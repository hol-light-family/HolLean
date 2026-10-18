/- ========================================================================= -/
/- Elementary real analysis, with some supporting HOL88 compatibility stuff. -/
/- ========================================================================= -/
/- File: HolLibrary/Analysis.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/analysis.ml`, by hand, in file order,
  in the style of HolLibrary/Words.lean (see there and HolMath/Base.lean for
  the conventions).  Each section of analysis.ml is a bundle (a `structure`)
  built by a `setup` function; SessionLibrary/Analysis.lean builds the
  bundles in order and exports every name under its HOL Light name.

  NAMES.  analysis.ml rebinds about a hundred names the core library already
  has (REAL_LE_TRANS, SUM_LE, sum, sup, EXPAND_TAC, ...).  Inside this file a
  use before the rebinding is the core one and a use after it is
  analysis.ml's, as OCaml's shadowing gives; SessionLibrary.Analysis exports
  analysis.ml's versions, so opening it together with Session makes those
  names ambiguous (qualify them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print
  (MESON, REAL_ARITH, ...) they are bound first, in OCaml's order.

  PARSER STATE.  analysis.ml changes the parser as it goes (prioritize_num,
  prioritize_real, infixes, `sum` overloading, `-->` interfaces).  Each
  change is made by the setup of the bundle where it occurs, through
  `AnalysisDeps`, so the quotations after it parse as they do in HOL Light.
-/

import HolMath

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolLibrary.Analysis

set_option maxHeartbeats 4000000

/- ------------------------------------------------------------------------- -/
/- What analysis.ml uses from the core library (supplied by Session).        -/
/- (Three structures, each under 128 fields: see HolLibrary/Words.lean.)     -/
/- ------------------------------------------------------------------------- -/

/-- Theorems analysis.ml uses from the core library, ADD to REAL_ADD_SYM. -/
structure CoreThms1 where
  (ADD ADD1 ADD_AC ADD_ASSOC ADD_CLAUSES ADD_SUB ADD_SYM AND_FORALL_THM ARITH
   ARITH_EQ BETA_THM CONJ_ASSOC CONJ_SYM CONTRAPOS_THM DE_MORGAN_THM EQ_IMP
   EQ_IMP_LE EQ_TRANS EXISTS_UNIQUE_THM EXTENSION FACT_LT FINITE_NUMSEG
   FINITE_SUBSET FUN_EQ_THM GE GT IMP_CLAUSES IMP_IMP IN IN_ELIM_THM
   IN_INSERT IN_NUMSEG LE LEFT_AND_EXISTS_THM LEFT_EXISTS_AND_THM
   LEFT_FORALL_IMP_THM LEFT_IMP_EXISTS_THM LE_0 LE_ADD LE_ADD_LCANCEL
   LE_ANTISYM LE_CASES LE_EXISTS LE_LT LE_MULT_RCANCEL LE_REFL LE_SUC
   LE_SUC_LT LE_TRANS LT LTE_CASES LTE_TRANS LT_0 LT_ADD_RCANCEL LT_EXISTS
   LT_IMP_LE LT_REFL LT_SUC_LE LT_TRANS MONO_EXISTS MONO_FORALL MULT_CLAUSES
   MULT_SYM NOT_CLAUSES NOT_EXISTS_THM NOT_FORALL_THM NOT_IMP NOT_IN_EMPTY
   NOT_LT NOT_SUC PRE REAL_ABS_0 REAL_ABS_DIV REAL_ABS_NUM REAL_ABS_POS
   REAL_ABS_REFL REAL_ABS_SUB REAL_ABS_TRIANGLE REAL_ADD2_SUB2 REAL_ADD_AC
   REAL_ADD_ASSOC REAL_ADD_LDISTRIB REAL_ADD_LID REAL_ADD_LINV
   REAL_ADD_RDISTRIB REAL_ADD_RID REAL_ADD_RINV REAL_ADD_SUB REAL_ADD_SUB2
   REAL_ADD_SYM : thm)

/-- Theorems analysis.ml uses from the core library, REAL_ARCH to REAL_MUL_RINV. -/
structure CoreThms2 where
  (REAL_ARCH REAL_ARCH_POW REAL_ARCH_POW2 REAL_ARCH_SIMPLE REAL_COMPLETE
   REAL_DIV_LMUL REAL_DIV_REFL REAL_DIV_RMUL REAL_DOWN REAL_DOWN2 REAL_ENTIRE
   REAL_EQ_ADD_LCANCEL REAL_EQ_IMP_LE REAL_EQ_NEG2 REAL_EQ_SUB_LADD
   REAL_EQ_SUB_RADD REAL_INV_MUL REAL_LET_ADD REAL_LET_ADD2 REAL_LET_TOTAL
   REAL_LET_TRANS REAL_LE_01 REAL_LE_ADD REAL_LE_ADD2 REAL_LE_ADDL
   REAL_LE_ADDR REAL_LE_ANTISYM REAL_LE_DOUBLE REAL_LE_LADD REAL_LE_LDIV_EQ
   REAL_LE_LMUL REAL_LE_LT REAL_LE_MUL REAL_LE_NEG2 REAL_LE_NEGL REAL_LE_NEGR
   REAL_LE_NEGTOTAL REAL_LE_RADD REAL_LE_REFL REAL_LE_RMUL REAL_LE_RMUL_EQ
   REAL_LE_SQUARE REAL_LE_SUB_LADD REAL_LE_SUB_RADD REAL_LE_TOTAL
   REAL_LE_TRANS REAL_LNEG_UNIQ REAL_LTE_ADD REAL_LTE_ADD2 REAL_LTE_TRANS
   REAL_LT_01 REAL_LT_ADD REAL_LT_ADD1 REAL_LT_ADD2 REAL_LT_ADDL
   REAL_LT_ADDNEG REAL_LT_ADDNEG2 REAL_LT_ADDR REAL_LT_ADD_SUB
   REAL_LT_ANTISYM REAL_LT_DIV REAL_LT_GT REAL_LT_IMP_LE REAL_LT_IMP_NE
   REAL_LT_IMP_NZ REAL_LT_INV2 REAL_LT_LADD REAL_LT_LDIV_EQ REAL_LT_LE
   REAL_LT_LMUL_EQ REAL_LT_MUL REAL_LT_NEG2 REAL_LT_NEGTOTAL REAL_LT_NZ
   REAL_LT_RADD REAL_LT_RDIV_EQ REAL_LT_REFL REAL_LT_RMUL_EQ REAL_LT_SUB_LADD
   REAL_LT_SUB_RADD REAL_LT_TOTAL REAL_LT_TRANS REAL_MUL_AC REAL_MUL_ASSOC
   REAL_MUL_LID REAL_MUL_LINV REAL_MUL_LZERO REAL_MUL_RID REAL_MUL_RINV : thm)

/-- Theorems analysis.ml uses from the core library, REAL_MUL_RZERO to sup. -/
structure CoreThms3 where
  (REAL_MUL_RZERO REAL_MUL_SYM REAL_NEG_0 REAL_NEG_ADD REAL_NEG_EQ
   REAL_NEG_GE0 REAL_NEG_GT0 REAL_NEG_LE0 REAL_NEG_LMUL REAL_NEG_LT0
   REAL_NEG_MINUS1 REAL_NEG_MUL2 REAL_NEG_NEG REAL_NEG_RMUL REAL_NEG_SUB
   REAL_NOT_LE REAL_NOT_LT REAL_OF_NUM_ADD REAL_OF_NUM_EQ REAL_OF_NUM_LE
   REAL_OF_NUM_LT REAL_OF_NUM_SUC REAL_POS REAL_POW_LBOUND REAL_RNEG_UNIQ
   REAL_SUB_0 REAL_SUB_ABS REAL_SUB_ADD REAL_SUB_ADD2 REAL_SUB_LDISTRIB
   REAL_SUB_LE REAL_SUB_LNEG REAL_SUB_LT REAL_SUB_LZERO REAL_SUB_NEG2
   REAL_SUB_RDISTRIB REAL_SUB_REFL REAL_SUB_RNEG REAL_SUB_RZERO REAL_SUB_SUB
   REAL_SUB_SUB2 REAL_SUB_TRIANGLE REAL_SUP_LE REAL_WLOG_LE
   RIGHT_AND_EXISTS_THM RIGHT_AND_FORALL_THM RIGHT_EXISTS_AND_THM
   RIGHT_FORALL_IMP_THM RIGHT_IMP_EXISTS_THM RIGHT_IMP_FORALL_THM SELECT_AX
   SKOLEM_THM SUBSET SUB_ADD SUC_SUB1 SUM_0 SUM_ABS SUM_ABS_LE SUM_ADD
   SUM_BOUND SUM_CLAUSES SUM_CONST SUM_DIFF SUM_EQ SUM_EQ_0 SUM_GROUP SUM_LE
   SUM_NEG SUM_OFFSET SUM_SUB SUM_SWAP SWAP_EXISTS_THM SWAP_FORALL_THM
   TRIV_EXISTS_AND_THM TRIV_FORALL_IMP_THM num_Axiom num_CASES num_RECURSION
   num_WOP real_abs real_div real_ge real_gt real_le real_pow real_sub sum
   sup : thm)

/-- The definitional principles, parser-state functions, decision procedures
    and conversions analysis.ml uses.  Rules that can fail are in `ExceptT`. -/
structure AnalysisDeps where
  -- definitions
  new_definition : String → ExceptT String IO thm
  new_specification : List String → thm → ExceptT String IO thm
  new_type_definition : String → String × String → thm → ExceptT String IO thm
  prove_recursive_functions_exist : thm → term → ExceptT String IO thm
  -- parser state
  prioritize_num : IO Unit
  prioritize_real : IO Unit
  parse_as_infix : String × (Int × String) → IO Unit
  make_overloadable : String → hol_type → ExceptT String IO Unit
  overload_interface : String → term → ExceptT String IO Unit
  override_interface : String → term → ExceptT String IO Unit
  remove_interface : String → IO Unit
  -- decision procedures and tactics
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_MESON_TAC : List thm → tactic
  INDUCT_TAC : tactic
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  REAL_ARITH : term → ExceptT String IO thm
  REAL_ARITH_TAC : tactic
  -- conversions
  GEN_BETA_CONV : ioconv
  num_CONV : ioconv
  core1 : CoreThms1
  core2 : CoreThms2
  core3 : CoreThms3

/- Kernel and HolCore conversions not in HolMath/Base, as `ioconv`s and
   `ExceptT` rules. -/

/-- equal.ml's `ALPHA_CONV`. -/
def ALPHA_CONV (v : term) : ioconv := fun t => pure (HolCore.Equal.ALPHA_CONV v t)
/-- equal.ml's `GEN_ALPHA_CONV`. -/
def GEN_ALPHA_CONV (v : term) : ioconv := fun t => pure (HolCore.Equal.GEN_ALPHA_CONV v t)
/-- class.ml's `ETA_CONV`. -/
def ETA_CONV [HolBase] : ioconv := fun t =>
  pure (HolCore.Classic.ETA_CONV HolBase.C.etaPth
    (mk_var "t" (.Tyapp "fun" [mk_vartype "A", mk_vartype "B"])) t)
/-- class.ml's `SELECT_CONV`. -/
def SELECT_CONV [HolBase] : ioconv := fun t =>
  pure (HolCore.Classic.SELECT_CONV HolBase.C.selectConvPth
    (mk_var "P" (.Tyapp "fun" [mk_vartype "A", bool_ty])) t)
/-- fusion.ml's `ABS`. -/
def ABS (v : term) (th : thm) : ExceptT String IO thm := liftExcept (HolCore.Kernel.ABS v th)
/-- tactics.ml's `NO_TAC`. -/
def NO_TAC : tactic := HolCore.Tactics.NO_TAC

/- ------------------------------------------------------------------------- -/
/- HOL88 compatibility: the quantifier movement conversions, named           -/
/- tautologies, derived rules, half abstractions, old substitution.          -/
/- (analysis.ml 1-156)                                                       -/
/- ------------------------------------------------------------------------- -/

/-- `get_bv` of `CONV_OF_RCONV` (analysis.ml 15-19). -/
partial def getBv (tm : term) : Except String term :=
  if is_abs tm then bndvar tm
  else if is_comb tm then
    match (do getBv (← rand tm)) with
    | .ok v => .ok v
    | .error _ => do getBv (← rator tm)
  else .error ""

/-- The recursive `SINGLE_DEPTH_CONV` (analysis.ml 44-48). -/
partial def singleDepthConv [HolBase] (conv : ioconv) : ioconv := fun tm => do
  match ← conv tm with
  | .ok th => pure (.ok th)
  | .error _ => (SUB_CONV (singleDepthConv conv) THENC TRY_CONV conv) tm

structure Compat where
  -- @@FIELDS
  dest_neg_imp : term → ExceptT String IO (term × term)
  CONV_OF_RCONV : ioconv → ioconv
  CONV_OF_THM : thm → ioconv
  X_FUN_EQ_CONV : term → ioconv
  FUN_EQ_CONV : ioconv
  SINGLE_DEPTH_CONV : ioconv → ioconv
  OLD_SKOLEM_CONV : ioconv
  X_SKOLEM_CONV : term → ioconv
  EXISTS_UNIQUE_CONV : ioconv
  NOT_FORALL_CONV : ioconv
  NOT_EXISTS_CONV : ioconv
  RIGHT_IMP_EXISTS_CONV : ioconv
  FORALL_IMP_CONV : ioconv
  EXISTS_AND_CONV : ioconv
  LEFT_IMP_EXISTS_CONV : ioconv
  LEFT_AND_EXISTS_CONV : ioconv
  RIGHT_AND_EXISTS_CONV : ioconv
  AND_FORALL_CONV : ioconv
  F_IMP : thm
  LEFT_AND_OVER_OR : thm
  RIGHT_AND_OVER_OR : thm
  INST_TY_TERM : List (term × term) × List (hol_type × hol_type) → thm → ExceptT String IO thm
  NOT_MP : thm → thm → ExceptT String IO thm
  MK_ABS : thm → ExceptT String IO thm
  HALF_MK_ABS : thm → ExceptT String IO thm
  SUBST : List (thm × term) → term → thm → ExceptT String IO thm
  deriving Inhabited

@[nospecialize]
def setupCompat [HolBase] (D : AnalysisDeps) :
    ExceptT String IO Compat := do
  -- @@SCOPE BEGIN
  let { AND_FORALL_THM, EXISTS_UNIQUE_THM, FUN_EQ_THM, LEFT_AND_EXISTS_THM,
        LEFT_EXISTS_AND_THM, LEFT_FORALL_IMP_THM, LEFT_IMP_EXISTS_THM, NOT_EXISTS_THM,
        NOT_FORALL_THM, .. } := D.core1
  let { RIGHT_AND_EXISTS_THM, RIGHT_EXISTS_AND_THM, RIGHT_FORALL_IMP_THM,
        RIGHT_IMP_EXISTS_THM, SKOLEM_THM, TRIV_EXISTS_AND_THM, TRIV_FORALL_IMP_THM, .. } := D.core3
  -- @@SCOPE END
  let dest_neg_imp : term → ExceptT String IO (term × term) ← pure (fun tm => do
    match dest_imp tm with
    | .ok p => pure p
    | .error _ =>
      -- `(dest_neg tm,mk_const("F",[]))`: the tuple is built right to left.
      tryWith (do
        let f ← ExceptT.mk (mk_const "F" [])
        let n ← liftExcept (dest_neg tm)
        pure (n, f))
        (throw "dest_neg_imp"))

  let CONV_OF_RCONV : ioconv → ioconv ← pure (fun conv tm => ExceptT.run do
    let v ← liftExcept (getBv tm)
    let th1 ← ExceptT.mk (conv tm)
    let th2 ← ExceptT.mk (ONCE_DEPTH_CONV (GEN_ALPHA_CONV v) (← liftExcept (rhs (concl th1))))
    TRANS th1 th2)

  let CONV_OF_THM : thm → ioconv ← pure (fun th => CONV_OF_RCONV (REWR_CONV th))

  let X_FUN_EQ_CONV : term → ioconv ← pure (fun v =>
    REWR_CONV FUN_EQ_THM THENC GEN_ALPHA_CONV v)

  let FUN_EQ_CONV : ioconv ← pure (fun tm => ExceptT.run do
    let vars := frees tm
    let (op, tys) ← liftExcept (do dest_type (type_of (← lhs tm)))
    let (ty1, _ty2) ← match tys with
      | [a, b] => pure (a, b)
      | _ => throw "Match_failure"
    if op == "fun" then
      let varnm ← if is_vartype ty1 then pure "x" else do
        let (c, _) ← liftExcept (dest_type ty1)
        match explode c with
        | h :: _ => pure h
        | [] => throw "hd"
      let x ← liftExcept (variant vars (mk_var varnm ty1))
      ExceptT.mk (X_FUN_EQ_CONV x tm)
    else throw "FUN_EQ_CONV")

  let SINGLE_DEPTH_CONV : ioconv → ioconv ← pure singleDepthConv

  let OLD_SKOLEM_CONV : ioconv ← pure (SINGLE_DEPTH_CONV (REWR_CONV SKOLEM_THM))

  let X_SKOLEM_CONV : term → ioconv ← pure (fun v =>
    OLD_SKOLEM_CONV THENC GEN_ALPHA_CONV v)

  let EXISTS_UNIQUE_CONV : ioconv ← pure (fun tm => ExceptT.run do
    let v ← liftExcept (do bndvar (← rand tm))
    let th1 ← ExceptT.mk (REWR_CONV EXISTS_UNIQUE_THM tm)
    let tm1 ← liftExcept (rhs (concl th1))
    let vars := frees tm1
    let v ← liftExcept (variant vars v)
    let v' ← liftExcept (variant (v :: vars) v)
    let th2 ← ExceptT.mk ((LAND_CONV (GEN_ALPHA_CONV v) THENC
       RAND_CONV (BINDER_CONV (GEN_ALPHA_CONV v') THENC
                  GEN_ALPHA_CONV v)) tm1)
    TRANS th1 th2)

  let NOT_FORALL_CONV : ioconv ← pure (CONV_OF_THM NOT_FORALL_THM)

  let NOT_EXISTS_CONV : ioconv ← pure (CONV_OF_THM NOT_EXISTS_THM)

  let RIGHT_IMP_EXISTS_CONV : ioconv ← pure (CONV_OF_THM RIGHT_IMP_EXISTS_THM)

  let FORALL_IMP_CONV : ioconv ← pure (CONV_OF_RCONV
    (REWR_CONV TRIV_FORALL_IMP_THM ORELSEC
     REWR_CONV RIGHT_FORALL_IMP_THM ORELSEC
     REWR_CONV LEFT_FORALL_IMP_THM))

  let EXISTS_AND_CONV : ioconv ← pure (CONV_OF_RCONV
    (REWR_CONV TRIV_EXISTS_AND_THM ORELSEC
     REWR_CONV LEFT_EXISTS_AND_THM ORELSEC
     REWR_CONV RIGHT_EXISTS_AND_THM))

  let LEFT_IMP_EXISTS_CONV : ioconv ← pure (CONV_OF_THM LEFT_IMP_EXISTS_THM)

  let LEFT_AND_EXISTS_CONV : ioconv ← pure (fun tm => ExceptT.run do
    let v ← liftExcept (do bndvar (← rand (← rand (← rator tm))))
    ExceptT.mk ((REWR_CONV LEFT_AND_EXISTS_THM THENC TRY_CONV (GEN_ALPHA_CONV v)) tm))

  let RIGHT_AND_EXISTS_CONV : ioconv ← pure (CONV_OF_THM RIGHT_AND_EXISTS_THM)

  let AND_FORALL_CONV : ioconv ← pure (CONV_OF_THM AND_FORALL_THM)

  let F_IMP ← TAUT (← q r"!t. ~t ==> t ==> F")

  let LEFT_AND_OVER_OR ← TAUT
    (← q r"!t1 t2 t3. t1 /\ (t2 \/ t3) <=> t1 /\ t2 \/ t1 /\ t3")

  let RIGHT_AND_OVER_OR ← TAUT
    (← q r"!t1 t2 t3. (t2 \/ t3) /\ t1 <=> t2 /\ t1 \/ t3 /\ t1")

  let INST_TY_TERM : List (term × term) × List (hol_type × hol_type) → thm → ExceptT String IO thm ← pure (fun (substl, insttyl) th => do
    INST substl (← HolLight.INST_TYPE insttyl th))

  let NOT_MP : thm → thm → ExceptT String IO thm ← pure (fun thi th =>
    tryWith (MP thi th)
      (tryWith (do
        let t ← liftExcept (dest_neg (concl thi))
        MP (← MP (← SPEC t F_IMP) thi) th)
        (throw "NOT_MP")))

  let MK_ABS : thm → ExceptT String IO thm ← pure (fun qth =>
    tryWith (do
      let ov ← liftExcept (do bndvar (← rand (concl qth)))
      let (bv, rth) ← SPEC_VAR qth
      let sth ← ABS bv rth
      let cnv := ALPHA_CONV ov
      CONV_RULE (BINOP_CONV cnv) sth)
      (throw "MK_ABS"))

  let HALF_MK_ABS : thm → ExceptT String IO thm ← pure (fun th =>
    tryWith (do
      let th1 ← MK_ABS th
      CONV_RULE (LAND_CONV ETA_CONV) th1)
      (throw "HALF_MK_ABS"))

  let SUBST : List (thm × term) → term → thm → ExceptT String IO thm ← pure (fun thl pat th => do
    let (eqs, vs) := unzip thl
    let mut gvs : List term := []
    for v in vs do gvs := gvs ++ [← (genvar (type_of v) : IO term)]
    let sb ← ExceptT.mk (subst (← liftExcept (zip gvs vs)))
    let gpat ← ExceptT.mk (sb pat)
    let (ls, rs) := unzip (← liftExcept (eqs.mapM (fun e => dest_eq (concl e))))
    let mkEq ← ExceptT.mk (mk_eq : IO _)
    let ths ← (← liftExcept (zip gvs rs)).mapM (fun p => do ASSUME (← liftExcept (mkEq p)))
    let th1 ← ASSUME gpat
    let th2 ← SUBS ths th1
    let th3 ← (ths.map concl).foldrM (fun t acc => DISCH t acc) (← DISCH gpat th2)
    let th4 ← INST (← liftExcept (zip ls gvs)) th3
    -- `rev_itlist (C MP) eqs th4`
    let th5 ← eqs.foldlM (fun acc e => MP acc e) th4
    MP th5 th)

  -- @@RETURN BEGIN
  return { dest_neg_imp, CONV_OF_RCONV, CONV_OF_THM, X_FUN_EQ_CONV, FUN_EQ_CONV,
           SINGLE_DEPTH_CONV, OLD_SKOLEM_CONV, X_SKOLEM_CONV, EXISTS_UNIQUE_CONV,
           NOT_FORALL_CONV, NOT_EXISTS_CONV, RIGHT_IMP_EXISTS_CONV, FORALL_IMP_CONV,
           EXISTS_AND_CONV, LEFT_IMP_EXISTS_CONV, LEFT_AND_EXISTS_CONV,
           RIGHT_AND_EXISTS_CONV, AND_FORALL_CONV, F_IMP, LEFT_AND_OVER_OR,
           RIGHT_AND_OVER_OR, INST_TY_TERM, NOT_MP, MK_ABS, HALF_MK_ABS, SUBST }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Various theorems have different names.  (analysis.ml 158-196)             -/
/- ------------------------------------------------------------------------- -/

structure Names where
  -- @@FIELDS
  LESS_EQUAL_ANTISYM : thm
  NOT_LESS_0 : thm
  LESS_LEMMA1 : thm
  LESS_SUC_REFL : thm
  LESS_EQ_SUC_REFL : thm
  LESS_EQUAL_ADD : thm
  LESS_EQ_IMP_LESS_SUC : thm
  LESS_MONO_ADD : thm
  LESS_SUC : thm
  LESS_ADD_1 : thm
  SUC_SUB1 : thm
  LESS_ADD_SUC : thm
  OR_LESS : thm
  NOT_SUC_LESS_EQ : thm
  LESS_LESS_CASES : thm
  SUB_SUB : thm
  LESS_CASES_IMP : thm
  SUB_LESS_EQ : thm
  SUB_EQ_EQ_0 : thm
  SUB_LEFT_LESS_EQ : thm
  SUB_LEFT_GREATER_EQ : thm
  LESS_0_CASES : thm
  LESS_OR : thm
  SUB_OLD : thm
  deriving Inhabited

@[nospecialize]
def setupNames [HolBase] (D : AnalysisDeps) :
    ExceptT String IO Names := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, prioritize_num, .. } := D
  let { ADD1, LE_ANTISYM, LE_EXISTS, LE_SUC_LT, LT, LT_ADD_RCANCEL, LT_EXISTS,
        LT_SUC_LE, .. } := D.core1
  let { RIGHT_IMP_FORALL_THM, .. } := D.core3
  -- @@SCOPE END
  prioritize_num

  let LESS_EQUAL_ANTISYM ← GEN_ALL (← EQ_IMP_RULE (← SPEC_ALL LE_ANTISYM)).1
  let NOT_LESS_0 ← GEN_ALL (← EQF_ELIM (← SPEC_ALL (← CONJUNCT1 LT)))
  let LESS_LEMMA1 ← GEN_ALL (← EQ_IMP_RULE (← SPEC_ALL (← CONJUNCT2 LT))).1
  let LESS_SUC_REFL ← ARITH_RULE (← q r"!n. n < SUC n")
  let LESS_EQ_SUC_REFL ← ARITH_RULE (← q r"!n. n <= SUC n")
  let LESS_EQUAL_ADD ← GEN_ALL (← EQ_IMP_RULE (← SPEC_ALL LE_EXISTS)).1
  let LESS_EQ_IMP_LESS_SUC ← GEN_ALL (← EQ_IMP_RULE (← SPEC_ALL LT_SUC_LE)).2
  let LESS_MONO_ADD ← GEN_ALL (← EQ_IMP_RULE (← SPEC_ALL LT_ADD_RCANCEL)).2
  let LESS_SUC ← ARITH_RULE (← q r"!m n. m < n ==> m < (SUC n)")
  let LESS_ADD_1 ← GEN_ALL (← EQ_IMP_RULE (← SPEC_ALL
    (← REWRITE_RULE [ADD1] LT_EXISTS))).1
  let SUC_SUB1 ← ARITH_RULE (← q r"!m. SUC m - 1 = m")
  let LESS_ADD_SUC ← ARITH_RULE (← q r"!m n. m < m + SUC n")
  let OR_LESS ← GEN_ALL (← EQ_IMP_RULE (← SPEC_ALL LE_SUC_LT)).1
  let NOT_SUC_LESS_EQ ← ARITH_RULE (← q r"!n m. ~(SUC n <= m) <=> m <= n")
  let LESS_LESS_CASES ← ARITH_RULE (← q r"!m n. (m = n) \/ m < n \/ n < m")
  let SUB_SUB ← prove
   r"!b c. c <= b ==> (!a. a - (b - c) = (a + c) - b)"
   (REWRITE_TAC [RIGHT_IMP_FORALL_THM] THEN ARITH_TAC)
  let LESS_CASES_IMP ← ARITH_RULE (← q r"!m n. ~(m < n) /\ ~(m = n) ==> n < m")
  let SUB_LESS_EQ ← ARITH_RULE (← q r"!n m. (n - m) <= n")
  let SUB_EQ_EQ_0 ← ARITH_RULE (← q r"!m n. (m - n = m) <=> (m = 0) \/ (n = 0)")
  let SUB_LEFT_LESS_EQ ←
    ARITH_RULE (← q r"!m n p. m <= (n - p) <=> (m + p) <= n \/ m <= 0")
  let SUB_LEFT_GREATER_EQ ← ARITH_RULE (← q r"!m n p. m >= (n - p) <=> (m + p) >= n")
  let LESS_0_CASES ← ARITH_RULE (← q r"!m. (0 = m) \/ 0 < m")
  let LESS_OR ← ARITH_RULE (← q r"!m n. m < n ==> (SUC m) <= n")
  let SUB_OLD ← prove
   r"(!m. 0 - m = 0) /\
                 (!m n. (SUC m) - n = (if m < n then 0 else SUC(m - n)))"
   (REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN
    ASM_REWRITE_TAC [] THEN TRY (POP_ASSUM MP_TAC) THEN
    ARITH_TAC)

  -- @@RETURN BEGIN
  return { LESS_EQUAL_ANTISYM, NOT_LESS_0, LESS_LEMMA1, LESS_SUC_REFL, LESS_EQ_SUC_REFL,
           LESS_EQUAL_ADD, LESS_EQ_IMP_LESS_SUC, LESS_MONO_ADD, LESS_SUC, LESS_ADD_1,
           SUC_SUB1, LESS_ADD_SUC, OR_LESS, NOT_SUC_LESS_EQ, LESS_LESS_CASES, SUB_SUB,
           LESS_CASES_IMP, SUB_LESS_EQ, SUB_EQ_EQ_0, SUB_LEFT_LESS_EQ,
           SUB_LEFT_GREATER_EQ, LESS_0_CASES, LESS_OR, SUB_OLD }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Various useful tactics, conversions etc.  (analysis.ml 198-269)           -/
/- ------------------------------------------------------------------------- -/

structure Tactics where
  -- @@FIELDS
  SYM_CANON_CONV : thm → (term × term → Bool) → ioconv
  IMP_SUBST_TAC : thm_tactic
  EXT_CONV : term → ExceptT String IO thm
  EQUAL_TAC : tactic
  X_BETA_CONV : term → ioconv
  EXACT_CONV : List thm → ExceptT String IO ioconv
  HABS_CONV : ioconv
  EXPAND_TAC : String → tactic
  deriving Inhabited

@[nospecialize]
def setupTactics [HolBase] (D : AnalysisDeps) (BCompat : Compat) :
    ExceptT String IO Tactics := do
  -- @@SCOPE BEGIN
  let { SUBST, X_FUN_EQ_CONV, .. } := BCompat
  let _ := D
  -- @@SCOPE END
  -- SYM_CANON_CONV - Canonicalizes single application of symmetric operator.
  let SYM_CANON_CONV : thm → (term × term → Bool) → ioconv ← pure (fun sym fn tm => ExceptT.run do
    -- `check (not o fn o ((snd o dest_comb) F_F I) o dest_comb)`
    let (f, x) ← liftExcept (dest_comb tm)
    let (_, fx) ← liftExcept (dest_comb f)
    if !(fn (fx, x)) then ExceptT.mk (REWR_CONV sym tm) else throw "check")

  -- IMP_SUBST_TAC - Implicational substitution for deepest matchable term.
  let IMP_SUBST_TAC : thm_tactic ← pure (fun th (asl, w) => ExceptT.run do
    let pf : term → Except String term := fun t => do lhs (← dest_imp t).2
    -- `find_terms (can (PART_MATCH ...)) w`: the same subterms, in the same
    -- order, as filtering all of `find_terms (K true) w`.
    let tms ← (find_terms (fun _ => true) w).filterM (fun t => do
      let r : Except String thm ← (PART_MATCH pf th t).run
      pure (match r with | .ok _ => true | .error _ => false))
    let tm1 ← liftExcept (hd (sort free_in tms))
    let th1 ← PART_MATCH pf th tm1
    let (a, eqn) ← liftExcept (dest_imp (concl th1))
    let (l, r) ← liftExcept (dest_eq eqn)
    let gv ← (genvar (type_of l) : IO term)
    let pat ← ExceptT.mk ((← ExceptT.mk (subst [(gv, l)])) w)
    let g2 ← ExceptT.mk ((← ExceptT.mk (subst [(r, gv)])) pat)
    let just : justification := fun _ ths => ExceptT.run do
      match ths with
      | [t1, t2] => SUBST [(← SYM (← MP th1 t1), gv)] pat t2
      | _ => throw "Match_failure"
    pure (HolCore.Tactics.null_meta, [(asl, a), (asl, g2)], just))

  -- EXT_CONV `!x. f x = g x` = |- (!x. f x = g x) = (f = g)
  let EXT_CONV : term → ExceptT String IO thm ← pure (fun tm => do
    let (v, bod) ← liftExcept (dest_forall tm)
    let (l, r) ← liftExcept (dest_eq bod)
    -- `(rator F_F rator)`: the pair is built right to left.
    let rr ← liftExcept (rator r)
    let rl ← liftExcept (rator l)
    let mkEq ← ExceptT.mk (mk_eq : IO _)
    SYM (← ExceptT.mk (X_FUN_EQ_CONV v (← liftExcept (mkEq (rl, rr))))))

  -- EQUAL_TAC - Strip down to unequal core (usually too enthusiastic).
  let EQUAL_TAC : tactic ← pure (REPEAT (FIRST [AP_TERM_TAC, AP_THM_TAC, ABS_TAC]))

  -- X_BETA_CONV `v` `tm[v]` = |- tm[v] = (\v. tm[v]) v
  let X_BETA_CONV : term → ioconv ← pure (fun v tm => ExceptT.run do
    SYM (← ExceptT.mk (BETA_CONV (← liftExcept (do mk_comb (← mk_abs v tm) v)))))

  -- EXACT_CONV - Rewrite with theorem matching exactly one in a list.  The
  -- left-hand sides are taken when `EXACT_CONV thl` is applied to the list,
  -- as OCaml's partial application `check((=)(lhs(concl t)))` does.
  let EXACT_CONV : List thm → ExceptT String IO ioconv ← pure (fun thl => do
    let cs ← thl.mapM (fun t => do
      let l ← liftExcept (lhs (concl t))
      pure (fun tm => pure (if tm == l then .ok t else .error "check") : ioconv))
    pure (ONCE_DEPTH_CONV (FIRST_CONV cs)))

  -- Rather ad-hoc higher-order fiddling conversion.
  let HABS_CONV : ioconv ← pure (fun tm => ExceptT.run do
    let (v, bod) ← liftExcept (dest_abs tm)
    let (hop, pl) := strip_comb bod
    let eql := HolCore.Lib.rev (← pl.mapM (fun p => ExceptT.mk (X_BETA_CONV v p)))
    -- `itlist (C(curry MK_COMB)) eql (REFL hop)`
    let th ← eql.foldrM (fun e acc => MK_COMB (acc, e)) (REFL hop)
    ABS v th)

  -- Expand an abbreviation.
  let EXPAND_TAC : String → tactic ← pure (fun s =>
    FIRST_ASSUM (fun th => tactic_of do
      -- `check((=) s o fst o dest_var o rhs o concl)`: a failure of
      -- `dest_var` propagates out of `check`.
      let (n, _) ← liftExcept (do dest_var (← rhs (concl th)))
      if n == s then pure (SUBST1_TAC (← SYM th)) else throw "check")
    THEN BETA_TAC)

  -- @@RETURN BEGIN
  return { SYM_CANON_CONV, IMP_SUBST_TAC, EXT_CONV, EQUAL_TAC, X_BETA_CONV, EXACT_CONV,
           HABS_CONV, EXPAND_TAC }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Set up the reals; link a few theorems; prove lots of boring field         -/
/- theorems.  (analysis.ml 271-560)                                          -/
/- ------------------------------------------------------------------------- -/

structure Reals1 where
  -- @@FIELDS
  real_le : thm
  REAL_10 : thm
  REAL_LDISTRIB : thm
  REAL_LT_IADD : thm
  REAL_MUL_RID : thm
  REAL_MUL_RINV : thm
  REAL_RDISTRIB : thm
  REAL_EQ_LADD : thm
  REAL_EQ_RADD : thm
  REAL_ADD_LID_UNIQ : thm
  REAL_ADD_RID_UNIQ : thm
  REAL_LNEG_UNIQ : thm
  REAL_RNEG_UNIQ : thm
  REAL_NEG_ADD : thm
  REAL_MUL_LZERO : thm
  REAL_MUL_RZERO : thm
  REAL_NEG_LMUL : thm
  REAL_NEG_RMUL : thm
  REAL_NEG_NEG : thm
  REAL_NEG_MUL2 : thm
  REAL_LT_LADD : thm
  REAL_LT_RADD : thm
  REAL_NOT_LT : thm
  REAL_LT_ANTISYM : thm
  REAL_LT_GT : thm
  REAL_NOT_LE : thm
  REAL_LE_TOTAL : thm
  REAL_LE_REFL : thm
  REAL_LE_LT : thm
  REAL_LT_LE : thm
  REAL_LT_IMP_LE : thm
  REAL_LTE_TRANS : thm
  REAL_LE_TRANS : thm
  REAL_NEG_LT0 : thm
  REAL_NEG_GT0 : thm
  REAL_NEG_LE0 : thm
  REAL_NEG_GE0 : thm
  REAL_LT_NEGTOTAL : thm
  REAL_LE_NEGTOTAL : thm
  REAL_LE_MUL : thm
  REAL_LE_SQUARE : thm
  REAL_LT_01 : thm
  REAL_LE_LADD : thm
  REAL_LE_RADD : thm
  REAL_LT_ADD2 : thm
  REAL_LT_ADD : thm
  REAL_LT_ADDNEG : thm
  REAL_LT_ADDNEG2 : thm
  REAL_LT_ADD1 : thm
  REAL_SUB_ADD : thm
  REAL_SUB_ADD2 : thm
  deriving Inhabited

@[nospecialize]
def setupReals1 [HolBase] (D : AnalysisDeps) (BCompat : Compat) :
    ExceptT String IO Reals1 := do
  -- @@SCOPE BEGIN
  let { REAL_ARITH, prioritize_real, .. } := D
  let { DE_MORGAN_THM, REAL_ADD_AC, REAL_ADD_ASSOC, REAL_ADD_LDISTRIB, REAL_ADD_LID,
        REAL_ADD_LINV, REAL_ADD_RID, REAL_ADD_RINV, REAL_ADD_SYM, .. } := D.core1
  let { REAL_LET_TRANS, REAL_LE_01, REAL_LT_MUL, REAL_LT_REFL, REAL_LT_TOTAL,
        REAL_LT_TRANS, REAL_MUL_LID, REAL_MUL_LINV, .. } := D.core2
  let { REAL_MUL_SYM, REAL_NOT_LT, real_sub, .. } := D.core3
  let { LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, .. } := BCompat
  -- @@SCOPE END
  prioritize_real

  let real_le ← prove
   r"!x y. x <= y <=> ~(y < x)"
   (REWRITE_TAC [REAL_NOT_LT])

  let REAL_10 ← REAL_ARITH (← q r"~(&1 = &0)")

  let REAL_LDISTRIB ← pure REAL_ADD_LDISTRIB

  let REAL_LT_IADD ← REAL_ARITH (← q r"!x y z. y < z ==> x + y < x + z")

  let REAL_MUL_RID ← prove
   r"!x. x * &1 = x"
   (GEN_TAC THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    MATCH_ACCEPT_TAC REAL_MUL_LID)

  let REAL_MUL_RINV ← prove
   r"!x. ~(x = &0) ==> (x * (inv x) = &1)"
   (GEN_TAC THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    MATCH_ACCEPT_TAC REAL_MUL_LINV)

  let REAL_RDISTRIB ← prove
   r"!x y z. (x + y) * z = (x * z) + (y * z)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    MATCH_ACCEPT_TAC REAL_LDISTRIB)

  let REAL_EQ_LADD ← prove
   r"!x y z. (x + y = x + z) <=> (y = z)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN (MP_TAC o AP_TERM (← q r"(+) (-- x)")) THEN
      REWRITE_TAC [REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_LID],
      DISCH_THEN SUBST1_TAC THEN REFL_TAC])

  let REAL_EQ_RADD ← prove
   r"!x y z. (x + z = y + z) <=> (x = y)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
    MATCH_ACCEPT_TAC REAL_EQ_LADD)

  let REAL_ADD_LID_UNIQ ← prove
   r"!x y. (x + y = y) <=> (x = &0)"
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← GSYM REAL_ADD_LID]
    THEN MATCH_ACCEPT_TAC REAL_EQ_RADD)

  let REAL_ADD_RID_UNIQ ← prove
   r"!x y. (x + y = x) <=> (y = &0)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
    MATCH_ACCEPT_TAC REAL_ADD_LID_UNIQ)

  let REAL_LNEG_UNIQ ← prove
   r"!x y. (x + y = &0) <=> (x = --y)"
   (REPEAT GEN_TAC THEN SUBST1_TAC (← SYM (← SPEC (← q "y:real") REAL_ADD_LINV)) THEN
    MATCH_ACCEPT_TAC REAL_EQ_RADD)

  let REAL_RNEG_UNIQ ← prove
   r"!x y. (x + y = &0) <=> (y = --x)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
    MATCH_ACCEPT_TAC REAL_LNEG_UNIQ)

  let REAL_NEG_ADD ← prove
   r"!x y. --(x + y) = (--x) + (--y)"
   (REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC [← GSYM REAL_LNEG_UNIQ] THEN
    ONCE_REWRITE_TAC [← AC REAL_ADD_AC
      (← q r"(a + b) + (c + d) = (a + c) + (b + d)")] THEN
    REWRITE_TAC [REAL_ADD_LINV, REAL_ADD_LID])

  let REAL_MUL_LZERO ← prove
   r"!x. &0 * x = &0"
   (GEN_TAC THEN SUBST1_TAC (← SYM (← SPECL [← q r"&0 * x", ← q r"&0 * x"] REAL_ADD_LID_UNIQ))
    THEN REWRITE_TAC [← GSYM REAL_RDISTRIB, REAL_ADD_LID])

  let REAL_MUL_RZERO ← prove
   r"!x. x * &0 = &0"
   (GEN_TAC THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    MATCH_ACCEPT_TAC REAL_MUL_LZERO)

  let REAL_NEG_LMUL ← prove
   r"!x y. --(x * y) = (--x) * y"
   (REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC [← GSYM REAL_LNEG_UNIQ, ← GSYM REAL_RDISTRIB,
                 REAL_ADD_LINV, REAL_MUL_LZERO])

  let REAL_NEG_RMUL ← prove
   r"!x y. --(x * y) = x * (--y)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    MATCH_ACCEPT_TAC REAL_NEG_LMUL)

  let REAL_NEG_NEG ← prove
   r"!x. --(--x) = x"
   (GEN_TAC THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC [← GSYM REAL_LNEG_UNIQ, REAL_ADD_RINV])

  let REAL_NEG_MUL2 ← prove
   r"!x y. (--x) * (--y) = x * y"
   (REWRITE_TAC [← GSYM REAL_NEG_LMUL, ← GSYM REAL_NEG_RMUL, REAL_NEG_NEG])

  let REAL_LT_LADD ← prove
   r"!x y z. (x + y) < (x + z) <=> y < z"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN (MP_TAC o SPEC (← q r"--x") o MATCH_MP REAL_LT_IADD) THEN
      REWRITE_TAC [REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_LID],
      MATCH_ACCEPT_TAC REAL_LT_IADD])

  let REAL_LT_RADD ← prove
   r"!x y z. (x + z) < (y + z) <=> x < y"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
    MATCH_ACCEPT_TAC REAL_LT_LADD)

  let REAL_NOT_LT ← prove
   r"!x y. ~(x < y) <=> y <= x"
   (REPEAT GEN_TAC THEN REWRITE_TAC [real_le])

  let REAL_LT_ANTISYM ← prove
   r"!x y. ~(x < y /\ y < x)"
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP REAL_LT_TRANS) THEN
    REWRITE_TAC [REAL_LT_REFL])

  let REAL_LT_GT ← prove
   r"!x y. x < y ==> ~(y < x)"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (fun th => DISCH_THEN (MP_TAC o (fun th' => CONJ th th'))) THEN
    REWRITE_TAC [REAL_LT_ANTISYM])

  let REAL_NOT_LE ← prove
   r"!x y. ~(x <= y) <=> y < x"
   (REPEAT GEN_TAC THEN REWRITE_TAC [real_le])

  let REAL_LE_TOTAL ← prove
   r"!x y. x <= y \/ y <= x"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [real_le, ← GSYM DE_MORGAN_THM, REAL_LT_ANTISYM])

  let REAL_LE_REFL ← prove
   r"!x. x <= x"
   (GEN_TAC THEN REWRITE_TAC [real_le, REAL_LT_REFL])

  let REAL_LE_LT ← prove
   r"!x y. x <= y <=> x < y \/ (x = y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [real_le] THEN EQ_TAC THENL
     [REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
       (← SPECL [← q "x:real", ← q "y:real"] REAL_LT_TOTAL) THEN ASM_REWRITE_TAC [],
      DISCH_THEN (DISJ_CASES_THEN2
       (fun th => MATCH_MP_TAC REAL_LT_GT THEN ACCEPT_TAC th) SUBST1_TAC) THEN
      MATCH_ACCEPT_TAC REAL_LT_REFL])

  let REAL_LT_LE ← prove
   r"!x y. x < y <=> x <= y /\ ~(x = y)"
   (← do
    let lemma ← TAUT (← q r"~(a /\ ~a)")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [REAL_LE_LT, RIGHT_AND_OVER_OR, lemma]
      THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
      POP_ASSUM MP_TAC THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC [] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [REAL_LT_REFL]))

  let REAL_LT_IMP_LE ← prove
   r"!x y. x < y ==> x <= y"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    ASM_REWRITE_TAC [REAL_LE_LT])

  let REAL_LTE_TRANS ← prove
   r"!x y z. x < y /\ y <= z ==> x < z"
   (REPEAT GEN_TAC THEN REWRITE_TAC [REAL_LE_LT, LEFT_AND_OVER_OR] THEN
    DISCH_THEN (DISJ_CASES_THEN2 (ACCEPT_TAC o MATCH_MP REAL_LT_TRANS)
      (CONJUNCTS_THEN2 MP_TAC SUBST1_TAC)) THEN REWRITE_TAC [])

  let REAL_LE_TRANS ← prove
   r"!x y z. x <= y /\ y <= z ==> x <= z"
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_LE_LT] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC (DISJ_CASES_THEN2 ASSUME_TAC SUBST1_TAC))
    THEN REWRITE_TAC [] THEN
    (← do let a ← ASSUME (← q r"y < z"); pure (DISCH_THEN (MP_TAC o (fun th => CONJ th a))))
    THEN DISCH_THEN (ACCEPT_TAC o MATCH_MP REAL_LT_IMP_LE o MATCH_MP REAL_LET_TRANS))

  let REAL_NEG_LT0 ← prove
   r"!x. (--x) < &0 <=> &0 < x"
   (GEN_TAC THEN SUBST1_TAC (← SYM (← SPECL [← q r"--x", ← q r"&0", ← q "x:real"] REAL_LT_RADD)) THEN
    REWRITE_TAC [REAL_ADD_LINV, REAL_ADD_LID])

  let REAL_NEG_GT0 ← prove
   r"!x. &0 < (--x) <=> x < &0"
   (GEN_TAC THEN REWRITE_TAC [← GSYM REAL_NEG_LT0, REAL_NEG_NEG])

  let REAL_NEG_LE0 ← prove
   r"!x. (--x) <= &0 <=> &0 <= x"
   (GEN_TAC THEN REWRITE_TAC [real_le] THEN
    REWRITE_TAC [REAL_NEG_GT0])

  let REAL_NEG_GE0 ← prove
   r"!x. &0 <= (--x) <=> x <= &0"
   (GEN_TAC THEN REWRITE_TAC [real_le] THEN
    REWRITE_TAC [REAL_NEG_LT0])

  let REAL_LT_NEGTOTAL ← prove
   r"!x. (x = &0) \/ (&0 < x) \/ (&0 < --x)"
   (GEN_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (← SPECL [← q "x:real", ← q r"&0"] REAL_LT_TOTAL) THEN
    ASM_REWRITE_TAC [← SYM (← REWRITE_RULE [REAL_NEG_NEG] (← SPEC (← q r"--x") REAL_NEG_LT0))])

  let REAL_LE_NEGTOTAL ← prove
   r"!x. &0 <= x \/ &0 <= --x"
   (GEN_TAC THEN REWRITE_TAC [REAL_LE_LT] THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (← SPEC (← q "x:real") REAL_LT_NEGTOTAL) THEN
    ASM_REWRITE_TAC [])

  let REAL_LE_MUL ← prove
   r"!x y. &0 <= x /\ &0 <= y ==> &0 <= (x * y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [REAL_LE_LT] THEN
    MAP_EVERY ASM_CASES_TAC [← q r"&0 = x", ← q r"&0 = y"] THEN
    ASM_REWRITE_TAC [] THEN TRY (FIRST_ASSUM (SUBST1_TAC o SYM)) THEN
    REWRITE_TAC [REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
    DISCH_TAC THEN DISJ1_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC [])

  let REAL_LE_SQUARE ← prove
   r"!x. &0 <= x * x"
   (GEN_TAC THEN DISJ_CASES_TAC (← SPEC (← q "x:real") REAL_LE_NEGTOTAL) THEN
    POP_ASSUM (MP_TAC o MATCH_MP REAL_LE_MUL o (fun th => CONJ th th)) THEN
    REWRITE_TAC [← GSYM REAL_NEG_RMUL, ← GSYM REAL_NEG_LMUL, REAL_NEG_NEG])

  let REAL_LT_01 ← prove
   r"&0 < &1"
   (REWRITE_TAC [REAL_LT_LE, REAL_LE_01] THEN
    CONV_TAC (RAND_CONV SYM_CONV) THEN
    REWRITE_TAC [REAL_10])

  let REAL_LE_LADD ← prove
   r"!x y z. (x + y) <= (x + z) <=> y <= z"
   (REPEAT GEN_TAC THEN REWRITE_TAC [real_le] THEN
    AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_LT_LADD)

  let REAL_LE_RADD ← prove
   r"!x y z. (x + z) <= (y + z) <=> x <= y"
   (REPEAT GEN_TAC THEN REWRITE_TAC [real_le] THEN
    AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_LT_RADD)

  let REAL_LT_ADD2 ← prove
   r"!w x y z. w < x /\ y < z ==> (w + y) < (x + z)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (← q r"w + z") THEN
    ASM_REWRITE_TAC [REAL_LT_LADD, REAL_LT_RADD])

  let REAL_LT_ADD ← prove
   r"!x y. &0 < x /\ &0 < y ==> &0 < (x + y)"
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP REAL_LT_ADD2) THEN
    REWRITE_TAC [REAL_ADD_LID])

  let REAL_LT_ADDNEG ← prove
   r"!x y z. y < (x + (--z)) <=> (y + z) < x"
   (REPEAT GEN_TAC THEN
    SUBST1_TAC (← SYM (← SPECL [← q "y:real", ← q r"x + (--z)", ← q "z:real"] REAL_LT_RADD)) THEN
    REWRITE_TAC [← GSYM REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_RID])

  let REAL_LT_ADDNEG2 ← prove
   r"!x y z. (x + (--y)) < z <=> x < (z + y)"
   (REPEAT GEN_TAC THEN
    SUBST1_TAC (← SYM (← SPECL [← q r"x + (-- y)", ← q "z:real", ← q "y:real"] REAL_LT_RADD)) THEN
    REWRITE_TAC [← GSYM REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_RID])

  let REAL_LT_ADD1 ← prove
   r"!x y. x <= y ==> x < (y + &1)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [REAL_LE_LT] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [POP_ASSUM (MP_TAC o MATCH_MP REAL_LT_ADD2 o (fun th => CONJ th REAL_LT_01)) THEN
      REWRITE_TAC [REAL_ADD_RID],
      POP_ASSUM SUBST1_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_ADD_RID] THEN
      REWRITE_TAC [REAL_LT_LADD, REAL_LT_01]])

  let REAL_SUB_ADD ← prove
   r"!x y. (x - y) + y = x"
   (REPEAT GEN_TAC THEN REWRITE_TAC [real_sub, ← GSYM REAL_ADD_ASSOC,
      REAL_ADD_LINV, REAL_ADD_RID])

  let REAL_SUB_ADD2 ← prove
   r"!x y. y + (x - y) = x"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
    MATCH_ACCEPT_TAC REAL_SUB_ADD)

  -- @@RETURN BEGIN
  return { real_le, REAL_10, REAL_LDISTRIB, REAL_LT_IADD, REAL_MUL_RID, REAL_MUL_RINV,
           REAL_RDISTRIB, REAL_EQ_LADD, REAL_EQ_RADD, REAL_ADD_LID_UNIQ,
           REAL_ADD_RID_UNIQ, REAL_LNEG_UNIQ, REAL_RNEG_UNIQ, REAL_NEG_ADD,
           REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_NEG_LMUL, REAL_NEG_RMUL, REAL_NEG_NEG,
           REAL_NEG_MUL2, REAL_LT_LADD, REAL_LT_RADD, REAL_NOT_LT, REAL_LT_ANTISYM,
           REAL_LT_GT, REAL_NOT_LE, REAL_LE_TOTAL, REAL_LE_REFL, REAL_LE_LT, REAL_LT_LE,
           REAL_LT_IMP_LE, REAL_LTE_TRANS, REAL_LE_TRANS, REAL_NEG_LT0, REAL_NEG_GT0,
           REAL_NEG_LE0, REAL_NEG_GE0, REAL_LT_NEGTOTAL, REAL_LE_NEGTOTAL, REAL_LE_MUL,
           REAL_LE_SQUARE, REAL_LT_01, REAL_LE_LADD, REAL_LE_RADD, REAL_LT_ADD2,
           REAL_LT_ADD, REAL_LT_ADDNEG, REAL_LT_ADDNEG2, REAL_LT_ADD1, REAL_SUB_ADD,
           REAL_SUB_ADD2 }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- More field theorems; homomorphisms for the inclusion map; now more        -/
/- theorems.  (analysis.ml 561-900)                                          -/
/- ------------------------------------------------------------------------- -/

structure Reals2 where
  -- @@FIELDS
  REAL_SUB_REFL : thm
  REAL_SUB_0 : thm
  REAL_LE_DOUBLE : thm
  REAL_LE_NEGL : thm
  REAL_LE_NEGR : thm
  REAL_NEG_EQ0 : thm
  REAL_NEG_0 : thm
  REAL_NEG_SUB : thm
  REAL_SUB_LT : thm
  REAL_SUB_LE : thm
  REAL_EQ_LMUL : thm
  REAL_EQ_RMUL : thm
  REAL_SUB_LDISTRIB : thm
  REAL_SUB_RDISTRIB : thm
  REAL_NEG_EQ : thm
  REAL_NEG_MINUS1 : thm
  REAL_INV_NZ : thm
  REAL_INVINV : thm
  REAL_LT_IMP_NE : thm
  REAL_INV_POS : thm
  REAL_LT_LMUL_0 : thm
  REAL_LT_RMUL_0 : thm
  REAL_LT_LMUL_EQ : thm
  REAL_LT_RMUL_EQ : thm
  REAL_LT_RMUL_IMP : thm
  REAL_LT_LMUL_IMP : thm
  REAL_LINV_UNIQ : thm
  REAL_RINV_UNIQ : thm
  REAL_NEG_INV : thm
  REAL_INV_1OVER : thm
  REAL : thm
  REAL_POS : thm
  REAL_LE : thm
  REAL_LT : thm
  REAL_INJ : thm
  REAL_ADD : thm
  REAL_MUL : thm
  REAL_INV1 : thm
  REAL_DIV_LZERO : thm
  REAL_LT_NZ : thm
  REAL_NZ_IMP_LT : thm
  REAL_LT_RDIV_0 : thm
  REAL_LT_RDIV : thm
  REAL_LT_FRACTION_0 : thm
  REAL_LT_MULTIPLE : thm
  REAL_LT_FRACTION : thm
  REAL_LT_HALF1 : thm
  REAL_LT_HALF2 : thm
  REAL_DOUBLE : thm
  deriving Inhabited

@[nospecialize]
def setupReals2 [HolBase] (D : AnalysisDeps) (BNames : Names) (BReals1 : Reals1) :
    ExceptT String IO Reals2 := do
  -- @@SCOPE BEGIN
  let { INDUCT_TAC, num_CONV, .. } := D
  let { ADD, ADD1, LE_0, LE_REFL, LE_SUC, LT_0, LT_TRANS, MULT_CLAUSES, NOT_LT,
        NOT_SUC, REAL_ADD_AC, REAL_ADD_LID, REAL_ADD_LINV, REAL_ADD_RID, REAL_ADD_RINV,
        REAL_ADD_SYM, .. } := D.core1
  let { REAL_LE_01, REAL_LE_ADD2, REAL_LE_ADDR, REAL_LE_ANTISYM, REAL_LT_ADDL,
        REAL_LT_ADDR, REAL_LT_MUL, REAL_LT_REFL, REAL_LT_TOTAL, REAL_MUL_ASSOC,
        REAL_MUL_LID, REAL_MUL_LINV, .. } := D.core2
  let { REAL_MUL_SYM, REAL_OF_NUM_ADD, real_div, real_sub, .. } := D.core3
  let { LESS_EQUAL_ANTISYM, LESS_LEMMA1, LESS_SUC_REFL, NOT_LESS_0, .. } := BNames
  let { REAL_10, REAL_LDISTRIB, REAL_LE_LADD, REAL_LE_RADD, REAL_LE_REFL,
        REAL_LE_TRANS, REAL_LT_01, REAL_LT_ADD2, REAL_LT_ANTISYM, REAL_LT_LE,
        REAL_LT_RADD, REAL_MUL_LZERO, REAL_MUL_RID, REAL_MUL_RINV, REAL_MUL_RZERO,
        REAL_NEG_ADD, REAL_NEG_GE0, REAL_NEG_GT0, REAL_NEG_LMUL, REAL_NEG_NEG,
        REAL_NEG_RMUL, REAL_NOT_LE, REAL_NOT_LT, REAL_RDISTRIB, REAL_SUB_ADD, .. } := BReals1
  -- @@SCOPE END
  let numc (s : String) : ExceptT String IO thm := do ExceptT.mk (num_CONV (← q s))

  let REAL_SUB_REFL ← prove
   r"!x. x - x = &0"
   (GEN_TAC THEN REWRITE_TAC [real_sub, REAL_ADD_RINV])

  let REAL_SUB_0 ← prove
   r"!x y. (x - y = &0) <=> (x = y)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN (MP_TAC o (flip AP_THM (← q "y:real")) o AP_TERM (← q r"(+)")) THEN
      REWRITE_TAC [REAL_SUB_ADD, REAL_ADD_LID],
      DISCH_THEN SUBST1_TAC THEN MATCH_ACCEPT_TAC REAL_SUB_REFL])

  let REAL_LE_DOUBLE ← prove
   r"!x. &0 <= x + x <=> &0 <= x"
   (GEN_TAC THEN EQ_TAC THENL
     [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC [REAL_NOT_LE] THEN
      DISCH_THEN (MP_TAC o MATCH_MP REAL_LT_ADD2 o (fun th => CONJ th th)),
      DISCH_THEN (MP_TAC o MATCH_MP REAL_LE_ADD2 o (fun th => CONJ th th))] THEN
    REWRITE_TAC [REAL_ADD_LID])

  let REAL_LE_NEGL ← prove
   r"!x. (--x <= x) <=> (&0 <= x)"
   (GEN_TAC THEN SUBST1_TAC (← SYM (← SPECL [← q "x:real", ← q r"--x", ← q "x:real"] REAL_LE_LADD))
    THEN REWRITE_TAC [REAL_ADD_RINV, REAL_LE_DOUBLE])

  let REAL_LE_NEGR ← prove
   r"!x. (x <= --x) <=> (x <= &0)"
   (GEN_TAC THEN SUBST1_TAC (← SYM (← SPEC (← q "x:real") REAL_NEG_NEG)) THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_NEG_NEG] THEN
    REWRITE_TAC [REAL_LE_NEGL] THEN REWRITE_TAC [REAL_NEG_GE0] THEN
    REWRITE_TAC [REAL_NEG_NEG])

  let REAL_NEG_EQ0 ← prove
   r"!x. (--x = &0) <=> (x = &0)"
   (GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN (MP_TAC o AP_TERM (← q r"(+) x")),
      DISCH_THEN (MP_TAC o AP_TERM (← q r"(+) (--x)"))] THEN
    REWRITE_TAC [REAL_ADD_RINV, REAL_ADD_LINV, REAL_ADD_RID] THEN
    DISCH_THEN SUBST1_TAC THEN REFL_TAC)

  let REAL_NEG_0 ← prove
   r"--(&0) = &0"
   (REWRITE_TAC [REAL_NEG_EQ0])

  let REAL_NEG_SUB ← prove
   r"!x y. --(x - y) = y - x"
   (REPEAT GEN_TAC THEN REWRITE_TAC [real_sub, REAL_NEG_ADD, REAL_NEG_NEG] THEN
    MATCH_ACCEPT_TAC REAL_ADD_SYM)

  let REAL_SUB_LT ← prove
   r"!x y. &0 < x - y <=> y < x"
   (REPEAT GEN_TAC THEN
    SUBST1_TAC (← SYM (← SPECL [← q r"&0", ← q r"x - y", ← q "y:real"] REAL_LT_RADD)) THEN
    REWRITE_TAC [REAL_SUB_ADD, REAL_ADD_LID])

  let REAL_SUB_LE ← prove
   r"!x y. &0 <= (x - y) <=> y <= x"
   (REPEAT GEN_TAC THEN
    SUBST1_TAC (← SYM (← SPECL [← q r"&0", ← q r"x - y", ← q "y:real"] REAL_LE_RADD)) THEN
    REWRITE_TAC [REAL_SUB_ADD, REAL_ADD_LID])

  let REAL_EQ_LMUL ← prove
   r"!x y z. (x * y = x * z) <=> (x = &0) \/ (y = z)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN (MP_TAC o AP_TERM (← q r"(*) (inv x)")) THEN
      ASM_CASES_TAC (← q r"x = &0") THEN ASM_REWRITE_TAC [] THEN
      POP_ASSUM (fun th => tactic_of do pure (REWRITE_TAC
        [REAL_MUL_ASSOC, ← MATCH_MP REAL_MUL_LINV th])) THEN
      REWRITE_TAC [REAL_MUL_LID],
      DISCH_THEN (DISJ_CASES_THEN SUBST1_TAC) THEN
      REWRITE_TAC [REAL_MUL_LZERO]])

  let REAL_EQ_RMUL ← prove
   r"!x y z. (x * z = y * z) <=> (z = &0) \/ (x = y)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    MATCH_ACCEPT_TAC REAL_EQ_LMUL)

  let REAL_SUB_LDISTRIB ← prove
   r"!x y z. x * (y - z) = (x * y) - (x * z)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [real_sub, REAL_LDISTRIB, REAL_NEG_RMUL])

  let REAL_SUB_RDISTRIB ← prove
   r"!x y z. (x - y) * z = (x * z) - (y * z)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    MATCH_ACCEPT_TAC REAL_SUB_LDISTRIB)

  let REAL_NEG_EQ ← prove
   r"!x y. (--x = y) <=> (x = --y)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN (SUBST1_TAC o SYM), DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC [REAL_NEG_NEG])

  let REAL_NEG_MINUS1 ← prove
   r"!x. --x = (--(&1)) * x"
   (GEN_TAC THEN REWRITE_TAC [← GSYM REAL_NEG_LMUL] THEN
    REWRITE_TAC [REAL_MUL_LID])

  let REAL_INV_NZ ← prove
   r"!x. ~(x = &0) ==> ~(inv x = &0)"
   (GEN_TAC THEN DISCH_TAC THEN
    DISCH_THEN (MP_TAC o (flip AP_THM (← q "x:real")) o AP_TERM (← q r"(*)")) THEN
    FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP REAL_MUL_LINV th])) THEN
    REWRITE_TAC [REAL_MUL_LZERO, REAL_10])

  let REAL_INVINV ← prove
   r"!x. ~(x = &0) ==> (inv (inv x) = x)"
   (GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP REAL_MUL_RINV) THEN
    ASM_CASES_TAC (← q r"inv x = &0") THEN
    ASM_REWRITE_TAC [REAL_MUL_RZERO, ← GSYM REAL_10] THEN
    MP_TAC (← SPECL [← q r"inv(inv x)", ← q "x:real", ← q r"inv x"] REAL_EQ_RMUL)
    THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC REAL_MUL_LINV THEN
    FIRST_ASSUM ACCEPT_TAC)

  let REAL_LT_IMP_NE ← prove
   r"!x y. x < y ==> ~(x = y)"
   (REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
    REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [REAL_LT_REFL])

  let REAL_INV_POS ← prove
   r"!x. &0 < x ==> &0 < inv x"
   (← do
    let a ← ASSUME (← q r"&0 < x")
    pure (GEN_TAC THEN DISCH_TAC THEN REPEAT_TCL DISJ_CASES_THEN
       MP_TAC (← SPECL [← q r"inv x", ← q r"&0"] REAL_LT_TOTAL) THENL
       [POP_ASSUM (ASSUME_TAC o MATCH_MP REAL_INV_NZ o
                  GSYM o MATCH_MP REAL_LT_IMP_NE) THEN ASM_REWRITE_TAC [],
        ONCE_REWRITE_TAC [← GSYM REAL_NEG_GT0] THEN
        DISCH_THEN (MP_TAC o MATCH_MP REAL_LT_MUL o (fun th => CONJ th a)) THEN
        REWRITE_TAC [← GSYM REAL_NEG_LMUL] THEN
        POP_ASSUM (fun th => tactic_of do pure (REWRITE_TAC
         [← MATCH_MP REAL_MUL_LINV (← GSYM (← MATCH_MP REAL_LT_IMP_NE th))])) THEN
        REWRITE_TAC [REAL_NEG_GT0] THEN DISCH_THEN (MP_TAC o CONJ REAL_LT_01) THEN
        REWRITE_TAC [REAL_LT_ANTISYM],
        REWRITE_TAC []]))

  let REAL_LT_LMUL_0 ← prove
   r"!x y. &0 < x ==> (&0 < (x * y) <=> &0 < y)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
     [FIRST_ASSUM (fun th => tactic_of do
        let c ← MATCH_MP REAL_INV_POS th
        pure (DISCH_THEN (MP_TAC o CONJ c))) THEN
      DISCH_THEN (MP_TAC o MATCH_MP REAL_LT_MUL) THEN
      REWRITE_TAC [REAL_MUL_ASSOC] THEN
      FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC
        [← MATCH_MP REAL_MUL_LINV (← GSYM (← MATCH_MP REAL_LT_IMP_NE th))])) THEN
      REWRITE_TAC [REAL_MUL_LID],
      DISCH_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC []])

  let REAL_LT_RMUL_0 ← prove
   r"!x y. &0 < y ==> (&0 < (x * y) <=> &0 < x)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    MATCH_ACCEPT_TAC REAL_LT_LMUL_0)

  let REAL_LT_LMUL_EQ ← prove
   r"!x y z. &0 < x ==> ((x * y) < (x * z) <=> y < z)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC [← GSYM REAL_SUB_LT] THEN
    REWRITE_TAC [← GSYM REAL_SUB_LDISTRIB] THEN
    POP_ASSUM MP_TAC THEN MATCH_ACCEPT_TAC REAL_LT_LMUL_0)

  let REAL_LT_RMUL_EQ ← prove
   r"!x y z. &0 < z ==> ((x * z) < (y * z) <=> x < y)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    MATCH_ACCEPT_TAC REAL_LT_LMUL_EQ)

  let REAL_LT_RMUL_IMP ← prove
   r"!x y z. x < y /\ &0 < z ==> (x * z) < (y * z)"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    POP_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← GEN_ALL (← MATCH_MP REAL_LT_RMUL_EQ th)])))

  let REAL_LT_LMUL_IMP ← prove
   r"!x y z. y < z  /\ &0 < x ==> (x * y) < (x * z)"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    POP_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← GEN_ALL (← MATCH_MP REAL_LT_LMUL_EQ th)])))

  let REAL_LINV_UNIQ ← prove
   r"!x y. (x * y = &1) ==> (x = inv y)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"x = &0") THEN
    ASM_REWRITE_TAC [REAL_MUL_LZERO, ← GSYM REAL_10] THEN
    DISCH_THEN (MP_TAC o AP_TERM (← q r"(*) (inv x)")) THEN
    REWRITE_TAC [REAL_MUL_ASSOC] THEN
    FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP REAL_MUL_LINV th])) THEN
    REWRITE_TAC [REAL_MUL_LID, REAL_MUL_RID] THEN
    DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN
    POP_ASSUM MP_TAC THEN MATCH_ACCEPT_TAC REAL_INVINV)

  let REAL_RINV_UNIQ ← prove
   r"!x y. (x * y = &1) ==> (y = inv x)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    MATCH_ACCEPT_TAC REAL_LINV_UNIQ)

  let REAL_NEG_INV ← prove
   r"!x. ~(x = &0) ==> (--(inv x) = inv(--x))"
   (GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LINV_UNIQ THEN
    REWRITE_TAC [← GSYM REAL_NEG_LMUL, ← GSYM REAL_NEG_RMUL] THEN
    POP_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP REAL_MUL_LINV th])) THEN
    REWRITE_TAC [REAL_NEG_NEG])

  let REAL_INV_1OVER ← prove
   r"!x. inv x = &1 / x"
   (GEN_TAC THEN REWRITE_TAC [real_div, REAL_MUL_LID])

  let REAL ← prove
   r"!n. &(SUC n) = &n + &1"
   (REWRITE_TAC [ADD1, REAL_OF_NUM_ADD])

  let REAL_POS ← prove
   r"!n. &0 <= &n"
   (INDUCT_TAC THEN REWRITE_TAC [REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"&n") THEN ASM_REWRITE_TAC [REAL] THEN
    REWRITE_TAC [REAL_LE_ADDR, REAL_LE_01])

  let REAL_LE ← prove
   r"!m n. &m <= &n <=> m <= n"
   (REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC
     [REAL, REAL_LE_RADD, LE_0, LE_SUC, REAL_LE_REFL] THEN
    REWRITE_TAC [← GSYM NOT_LT, LT_0] THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"&n") THEN
      ASM_REWRITE_TAC [LE_0, REAL_LE_ADDR, REAL_LE_01],
      (← do let p ← SPEC (← q "m:num") REAL_POS
            pure (DISCH_THEN (MP_TAC o (fun th => CONJ th p)))) THEN
      DISCH_THEN (MP_TAC o MATCH_MP REAL_LE_TRANS) THEN
      REWRITE_TAC [REAL_NOT_LE, REAL_LT_ADDR, REAL_LT_01]])

  let REAL_LT ← prove
   r"!m n. &m < &n <=> m < n"
   (REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC (← do
      let th ← REWRITE_RULE [← GSYM NOT_LT, ← GSYM REAL_NOT_LT] (← SPEC_ALL REAL_LE)
      REWRITE_RULE [] (← AP_TERM (← q r"(~)") th)))

  let REAL_INJ ← prove
   r"!m n. (&m = &n) <=> (m = n)"
   (← do
    let th ← prove r"(m = n) <=> m:num <= n /\ n <= m"
                (EQ_TAC THENL
                  [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [LE_REFL],
                   MATCH_ACCEPT_TAC LESS_EQUAL_ANTISYM])
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [th, ← GSYM REAL_LE_ANTISYM, REAL_LE]))

  let REAL_ADD ← prove
   r"!m n. &m + &n = &(m + n)"
   (INDUCT_TAC THEN REWRITE_TAC [REAL, ADD, REAL_ADD_LID] THEN
    RULE_ASSUM_TAC GSYM THEN GEN_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [REAL_ADD_AC])

  let REAL_MUL ← prove
   r"!m n. &m * &n = &(m * n)"
   (INDUCT_TAC THEN REWRITE_TAC [REAL_MUL_LZERO, MULT_CLAUSES, REAL,
      ← GSYM REAL_ADD, REAL_RDISTRIB] THEN
    FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← GSYM th])) THEN
    REWRITE_TAC [REAL_MUL_LID])

  let REAL_INV1 ← prove
   r"inv(&1) = &1"
   (CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_LINV_UNIQ THEN
    REWRITE_TAC [REAL_MUL_LID])

  let REAL_DIV_LZERO ← prove
   r"!x. &0 / x = &0"
   (REPEAT GEN_TAC THEN REWRITE_TAC [real_div, REAL_MUL_LZERO])

  let REAL_LT_NZ ← prove
   r"!n. ~(&n = &0) <=> (&0 < &n)"
   (GEN_TAC THEN REWRITE_TAC [REAL_LT_LE] THEN
    CONV_TAC (RAND_CONV (ONCE_DEPTH_CONV SYM_CONV)) THEN
    ASM_CASES_TAC (← q r"&n = &0") THEN ASM_REWRITE_TAC [REAL_LE_REFL, REAL_POS])

  let REAL_NZ_IMP_LT ← prove
   r"!n. ~(n = 0) ==> &0 < &n"
   (GEN_TAC THEN REWRITE_TAC [← GSYM REAL_INJ, REAL_LT_NZ])

  let REAL_LT_RDIV_0 ← prove
   r"!y z. &0 < z ==> (&0 < (y / z) <=> &0 < y)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [real_div] THEN MATCH_MP_TAC REAL_LT_RMUL_0 THEN
    MATCH_MP_TAC REAL_INV_POS THEN POP_ASSUM ACCEPT_TAC)

  let REAL_LT_RDIV ← prove
   r"!x y z. &0 < z ==> ((x / z) < (y / z) <=> x < y)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [real_div] THEN MATCH_MP_TAC REAL_LT_RMUL_EQ THEN
    MATCH_MP_TAC REAL_INV_POS THEN POP_ASSUM ACCEPT_TAC)

  let REAL_LT_FRACTION_0 ← prove
   r"!n d. ~(n = 0) ==> (&0 < (d / &n) <=> &0 < d)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LT_RDIV_0 THEN
    ASM_REWRITE_TAC [← GSYM REAL_LT_NZ, REAL_INJ])

  let REAL_LT_MULTIPLE ← prove
   r"!n d. 1 < n ==> (d < (&n * d) <=> &0 < d)"
   (ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN INDUCT_TAC THENL
     [REWRITE_TAC [← numc "1", NOT_LESS_0],
      POP_ASSUM MP_TAC THEN ASM_CASES_TAC (← q "1 < n") THEN
      ASM_REWRITE_TAC [] THENL
       [DISCH_TAC THEN GEN_TAC THEN DISCH_THEN (fun _ => ALL_TAC) THEN
        REWRITE_TAC [REAL, REAL_LDISTRIB, REAL_MUL_RID, REAL_LT_ADDL] THEN
        MATCH_MP_TAC REAL_LT_RMUL_0 THEN REWRITE_TAC [REAL_LT] THEN
        MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC (← q "1") THEN
        ASM_REWRITE_TAC [] THEN REWRITE_TAC [← numc "1", LT_0],
        GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP LESS_LEMMA1) THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
        REWRITE_TAC [REAL, REAL_LDISTRIB, REAL_MUL_RID] THEN
        REWRITE_TAC [REAL_LT_ADDL]]])

  let REAL_LT_FRACTION ← prove
   r"!n d. (1 < n) ==> ((d / &n) < d <=> &0 < d)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "n = 0") THEN
    ASM_REWRITE_TAC [NOT_LESS_0] THEN DISCH_TAC THEN
    UNDISCH_TAC (← q "1 < n") THEN
    FIRST_ASSUM (fun th => tactic_of do
      let th1 ← REWRITE_RULE [← GSYM REAL_INJ] th
      -- `[th1; REWRITE_RULE[REAL_LT_NZ] th1]`: right to left.
      let th2 ← REWRITE_RULE [REAL_LT_NZ] th1
      pure (MAP_EVERY ASSUME_TAC [th1, th2])) THEN
    FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC (RAND_CONV o LAND_CONV)
                       [← GSYM (← MATCH_MP REAL_LT_RMUL_EQ th)])) THEN
    REWRITE_TAC [real_div, ← GSYM REAL_MUL_ASSOC] THEN
    FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP REAL_MUL_LINV th])) THEN
    REWRITE_TAC [REAL_MUL_RID] THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    MATCH_ACCEPT_TAC REAL_LT_MULTIPLE)

  let REAL_LT_HALF1 ← prove
   r"!d. &0 < (d / &2) <=> &0 < d"
   (GEN_TAC THEN MATCH_MP_TAC REAL_LT_FRACTION_0 THEN
    REWRITE_TAC [← numc "2", NOT_SUC])

  let REAL_LT_HALF2 ← prove
   r"!d. (d / &2) < d <=> &0 < d"
   (GEN_TAC THEN MATCH_MP_TAC REAL_LT_FRACTION THEN
    CONV_TAC (RAND_CONV num_CONV) THEN
    REWRITE_TAC [LESS_SUC_REFL])

  let REAL_DOUBLE ← prove
   r"!x. x + x = &2 * x"
   (GEN_TAC THEN REWRITE_TAC [← numc "2", REAL] THEN
    REWRITE_TAC [REAL_RDISTRIB, REAL_MUL_LID])

  -- @@RETURN BEGIN
  return { REAL_SUB_REFL, REAL_SUB_0, REAL_LE_DOUBLE, REAL_LE_NEGL, REAL_LE_NEGR,
           REAL_NEG_EQ0, REAL_NEG_0, REAL_NEG_SUB, REAL_SUB_LT, REAL_SUB_LE,
           REAL_EQ_LMUL, REAL_EQ_RMUL, REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB, REAL_NEG_EQ,
           REAL_NEG_MINUS1, REAL_INV_NZ, REAL_INVINV, REAL_LT_IMP_NE, REAL_INV_POS,
           REAL_LT_LMUL_0, REAL_LT_RMUL_0, REAL_LT_LMUL_EQ, REAL_LT_RMUL_EQ,
           REAL_LT_RMUL_IMP, REAL_LT_LMUL_IMP, REAL_LINV_UNIQ, REAL_RINV_UNIQ,
           REAL_NEG_INV, REAL_INV_1OVER, REAL, REAL_POS, REAL_LE, REAL_LT, REAL_INJ,
           REAL_ADD, REAL_MUL, REAL_INV1, REAL_DIV_LZERO, REAL_LT_NZ, REAL_NZ_IMP_LT,
           REAL_LT_RDIV_0, REAL_LT_RDIV, REAL_LT_FRACTION_0, REAL_LT_MULTIPLE,
           REAL_LT_FRACTION, REAL_LT_HALF1, REAL_LT_HALF2, REAL_DOUBLE }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Yet more real theorems.  (analysis.ml 900-1183)                           -/
/- ------------------------------------------------------------------------- -/

structure Reals3 where
  -- @@FIELDS
  REAL_HALF_DOUBLE : thm
  REAL_SUB_SUB : thm
  REAL_LT_ADD_SUB : thm
  REAL_LT_SUB_RADD : thm
  REAL_LT_SUB_LADD : thm
  REAL_LE_SUB_LADD : thm
  REAL_LE_SUB_RADD : thm
  REAL_LT_NEG2 : thm
  REAL_LE_NEG2 : thm
  REAL_SUB_LZERO : thm
  REAL_SUB_RZERO : thm
  REAL_LTE_ADD2 : thm
  REAL_LTE_ADD : thm
  REAL_LT_MUL2_ALT : thm
  REAL_SUB_LNEG : thm
  REAL_SUB_RNEG : thm
  REAL_SUB_NEG2 : thm
  REAL_SUB_TRIANGLE : thm
  REAL_INV_MUL_WEAK : thm
  REAL_LE_LMUL_LOCAL : thm
  REAL_LE_RMUL_EQ : thm
  REAL_SUB_INV2 : thm
  REAL_SUB_SUB2 : thm
  REAL_MEAN : thm
  REAL_EQ_LMUL2 : thm
  REAL_LE_MUL2V : thm
  REAL_LE_LDIV : thm
  REAL_LE_RDIV : thm
  REAL_LT_1 : thm
  REAL_LE_LMUL_IMP : thm
  REAL_LE_RMUL_IMP : thm
  REAL_INV_LT1 : thm
  REAL_LT_IMP_NZ : thm
  REAL_EQ_RMUL_IMP : thm
  REAL_EQ_LMUL_IMP : thm
  REAL_FACT_NZ : thm
  REAL_POSSQ : thm
  REAL_SUMSQ : thm
  REAL_EQ_NEG : thm
  REAL_DIV_MUL2 : thm
  REAL_MIDDLE1 : thm
  REAL_MIDDLE2 : thm
  deriving Inhabited

@[nospecialize]
def setupReals3 [HolBase] (D : AnalysisDeps) (BTactics : Tactics) (BReals1 : Reals1) (BReals2 : Reals2) :
    ExceptT String IO Reals3 := do
  -- @@SCOPE BEGIN
  let { num_CONV, .. } := D
  let { CONJ_SYM, DE_MORGAN_THM, EQ_IMP, FACT_LT, LT_0, NOT_IMP, NOT_SUC, REAL_ADD_AC,
        REAL_ADD_ASSOC, REAL_ADD_LID, REAL_ADD_LINV, REAL_ADD_RID, REAL_ADD_RINV,
        REAL_ADD_SYM, .. } := D.core1
  let { REAL_DIV_LMUL, REAL_DIV_RMUL, REAL_DOWN, REAL_ENTIRE, REAL_INV_MUL,
        REAL_LET_ADD, REAL_LET_ADD2, REAL_LET_TRANS, REAL_LE_ANTISYM, REAL_LT_ADDR,
        REAL_LT_MUL, REAL_LT_REFL, REAL_MUL_AC, REAL_MUL_ASSOC, REAL_MUL_LID,
        REAL_MUL_LINV, .. } := D.core2
  let { REAL_MUL_SYM, real_div, real_sub, .. } := D.core3
  let { IMP_SUBST_TAC, .. } := BTactics
  let { REAL_LE_LADD, REAL_LE_LT, REAL_LE_MUL, REAL_LE_RADD, REAL_LE_REFL,
        REAL_LE_SQUARE, REAL_LT_IMP_LE, REAL_LT_RADD, REAL_MUL_LZERO, REAL_MUL_RINV,
        REAL_MUL_RZERO, REAL_NEG_ADD, REAL_NEG_NEG, REAL_NOT_LE, REAL_NOT_LT,
        REAL_SUB_ADD, .. } := BReals1
  let { REAL_DOUBLE, REAL_EQ_LMUL, REAL_EQ_RMUL, REAL_INJ, REAL_INV1, REAL_INVINV,
        REAL_INV_POS, REAL_LT, REAL_LT_IMP_NE, REAL_LT_LMUL_EQ, REAL_LT_RMUL_EQ,
        REAL_NEG_0, REAL_NEG_SUB, REAL_SUB_LDISTRIB, REAL_SUB_LT, REAL_SUB_RDISTRIB, .. } := BReals2
  -- @@SCOPE END
  let numc (s : String) : ExceptT String IO thm := do ExceptT.mk (num_CONV (← q s))

  let REAL_HALF_DOUBLE ← prove
   r"!x. (x / &2) + (x / &2) = x"
   (GEN_TAC THEN REWRITE_TAC [REAL_DOUBLE] THEN
    MATCH_MP_TAC REAL_DIV_LMUL THEN REWRITE_TAC [REAL_INJ] THEN
    REWRITE_TAC [← numc "2", NOT_SUC])

  let REAL_SUB_SUB ← prove
   r"!x y. (x - y) - x = --y"
   (REPEAT GEN_TAC THEN REWRITE_TAC [real_sub] THEN
    ONCE_REWRITE_TAC [← AC REAL_ADD_AC
      (← q r"(a + b) + c = (c + a) + b")] THEN
    REWRITE_TAC [REAL_ADD_LINV, REAL_ADD_LID])

  let REAL_LT_ADD_SUB ← prove
   r"!x y z. (x + y) < z <=> x < (z - y)"
   (REPEAT GEN_TAC THEN
    SUBST1_TAC (← SYM (← SPECL [← q "x:real", ← q r"z - y", ← q "y:real"] REAL_LT_RADD)) THEN
    REWRITE_TAC [REAL_SUB_ADD])

  let REAL_LT_SUB_RADD ← prove
   r"!x y z. (x - y) < z <=> x < z + y"
   (REPEAT GEN_TAC THEN
    SUBST1_TAC (← SYM (← SPECL [← q r"x - y", ← q "z:real", ← q "y:real"] REAL_LT_RADD)) THEN
    REWRITE_TAC [REAL_SUB_ADD])

  let REAL_LT_SUB_LADD ← prove
   r"!x y z. x < (y - z) <=> (x + z) < y"
   (REPEAT GEN_TAC THEN
    SUBST1_TAC (← SYM (← SPECL [← q r"x + z", ← q "y:real", ← q r"--z"] REAL_LT_RADD)) THEN
    REWRITE_TAC [real_sub, ← GSYM REAL_ADD_ASSOC, REAL_ADD_RINV, REAL_ADD_RID])

  let REAL_LE_SUB_LADD ← prove
   r"!x y z. x <= (y - z) <=> (x + z) <= y"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM REAL_NOT_LT, REAL_LT_SUB_RADD])

  let REAL_LE_SUB_RADD ← prove
   r"!x y z. (x - y) <= z <=> x <= z + y"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM REAL_NOT_LT, REAL_LT_SUB_LADD])

  let REAL_LT_NEG2 ← prove
   r"!x y. --x < --y <=> y < x"
   (REPEAT GEN_TAC THEN
    SUBST1_TAC (← SYM (← SPECL [← q r"--x", ← q r"--y", ← q r"x + y"] REAL_LT_RADD)) THEN
    REWRITE_TAC [REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_LID] THEN
    ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
    REWRITE_TAC [REAL_ADD_ASSOC, REAL_ADD_RINV, REAL_ADD_LID])

  let REAL_LE_NEG2 ← prove
   r"!x y. --x <= --y <=> y <= x"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM REAL_NOT_LT] THEN
    REWRITE_TAC [REAL_LT_NEG2])

  let REAL_SUB_LZERO ← prove
   r"!x. &0 - x = --x"
   (GEN_TAC THEN REWRITE_TAC [real_sub, REAL_ADD_LID])

  let REAL_SUB_RZERO ← prove
   r"!x. x - &0 = x"
   (GEN_TAC THEN REWRITE_TAC [real_sub, REAL_NEG_0, REAL_ADD_RID])

  let REAL_LTE_ADD2 ← prove
   r"!w x y z. w < x /\ y <= z ==> (w + y) < (x + z)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [CONJ_SYM] THEN
    ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
    MATCH_ACCEPT_TAC REAL_LET_ADD2)

  let REAL_LTE_ADD ← prove
   r"!x y. &0 < x /\ &0 <= y ==> &0 < (x + y)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBST1_TAC (← SYM (← SPEC (← q r"&0") REAL_ADD_LID)) THEN
    MATCH_MP_TAC REAL_LTE_ADD2 THEN
    ASM_REWRITE_TAC [])

  let REAL_LT_MUL2_ALT ← prove
   r"!x1 x2 y1 y2. &0 <= x1 /\ &0 <= y1 /\ x1 < x2 /\ y1 < y2 ==>
        (x1 * y1) < (x2 * y2)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_SUB_LT] THEN
    REWRITE_TAC [REAL_SUB_RZERO] THEN
    SUBGOAL_THEN (← q r"!a b c d.
    (a * b) - (c * d) = ((a * b) - (a * d)) + ((a * d) - (c * d))")
    MP_TAC THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC [real_sub] THEN
      ONCE_REWRITE_TAC [← AC REAL_ADD_AC
        (← q r"(a + b) + (c + d) = (b + c) + (a + d)")] THEN
      REWRITE_TAC [REAL_ADD_LINV, REAL_ADD_LID],
      DISCH_THEN (fun th => ONCE_REWRITE_TAC [th]) THEN
      REWRITE_TAC [← GSYM REAL_SUB_LDISTRIB, ← GSYM REAL_SUB_RDISTRIB] THEN
      DISCH_THEN STRIP_ASSUME_TAC THEN
      MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q "x1:real") THEN
        ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [← GSYM REAL_SUB_LT] THEN
        ASM_REWRITE_TAC [],
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC []]])

  let REAL_SUB_LNEG ← prove
   r"!x y. (--x) - y = --(x + y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [real_sub, REAL_NEG_ADD])

  let REAL_SUB_RNEG ← prove
   r"!x y. x - (--y) = x + y"
   (REPEAT GEN_TAC THEN REWRITE_TAC [real_sub, REAL_NEG_NEG])

  let REAL_SUB_NEG2 ← prove
   r"!x y. (--x) - (--y) = y - x"
   (REPEAT GEN_TAC THEN REWRITE_TAC [REAL_SUB_LNEG] THEN
    REWRITE_TAC [real_sub, REAL_NEG_ADD, REAL_NEG_NEG] THEN
    MATCH_ACCEPT_TAC REAL_ADD_SYM)

  let REAL_SUB_TRIANGLE ← prove
   r"!a b c. (a - b) + (b - c) = a - c"
   (REPEAT GEN_TAC THEN REWRITE_TAC [real_sub] THEN
    ONCE_REWRITE_TAC [← AC REAL_ADD_AC
      (← q r"(a + b) + (c + d) = (b + c) + (a + d)")] THEN
    REWRITE_TAC [REAL_ADD_LINV, REAL_ADD_LID])

  let REAL_INV_MUL_WEAK ← prove
   r"!x y. ~(x = &0) /\ ~(y = &0) ==>
             (inv(x * y) = inv(x) * inv(y))"
   (REWRITE_TAC [REAL_INV_MUL])

  let REAL_LE_LMUL_LOCAL ← prove
   r"!x y z. &0 < x ==> ((x * y) <= (x * z) <=> y <= z)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_NOT_LT] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC REAL_LT_LMUL_EQ THEN ASM_REWRITE_TAC [])

  let REAL_LE_RMUL_EQ ← prove
   r"!x y z. &0 < z ==> ((x * z) <= (y * z) <=> x <= y)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    MATCH_ACCEPT_TAC REAL_LE_LMUL_LOCAL)

  let REAL_SUB_INV2 ← prove
   r"!x y. ~(x = &0) /\ ~(y = &0) ==>
                (inv(x) - inv(y) = (y - x) / (x * y))"
   (REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
    REWRITE_TAC [real_div, REAL_SUB_RDISTRIB] THEN
    SUBGOAL_THEN (← q r"inv(x * y) = inv(x) * inv(y)") SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_INV_MUL_WEAK THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    REWRITE_TAC [REAL_MUL_ASSOC] THEN
    EVERY_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP REAL_MUL_RINV th])) THEN
    REWRITE_TAC [REAL_MUL_LID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REWRITE_TAC [REAL_MUL_ASSOC] THEN
    EVERY_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP REAL_MUL_LINV th])) THEN
    REWRITE_TAC [REAL_MUL_LID])

  let REAL_SUB_SUB2 ← prove
   r"!x y. x - (x - y) = y"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_NEG_NEG] THEN
    AP_TERM_TAC THEN REWRITE_TAC [REAL_NEG_SUB, REAL_SUB_SUB])

  let REAL_MEAN ← prove
   r"!x y. x < y ==> ?z. x < z /\ z < y"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (MP_TAC o MATCH_MP REAL_DOWN o ONCE_REWRITE_RULE [← GSYM REAL_SUB_LT])
    THEN DISCH_THEN (X_CHOOSE_THEN (← q "d:real") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"x + d") THEN ASM_REWRITE_TAC [REAL_LT_ADDR] THEN
    ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
    ASM_REWRITE_TAC [← GSYM REAL_LT_SUB_LADD])

  let REAL_EQ_LMUL2 ← prove
   r"!x y z. ~(x = &0) ==> ((y = z) <=> (x * y = x * z))"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC (← SPECL [← q "x:real", ← q "y:real", ← q "z:real"] REAL_EQ_LMUL) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST_ALL_TAC THEN REFL_TAC)

  let REAL_LE_MUL2V ← prove
   r"!x1 x2 y1 y2.
    (& 0) <= x1 /\ (& 0) <= y1 /\ x1 <= x2 /\ y1 <= y2 ==>
    (x1 * y1) <= (x2 * y2)"
   (REPEAT GEN_TAC THEN
    SUBST1_TAC (← SPECL [← q "x1:real", ← q "x2:real"] REAL_LE_LT) THEN
    ASM_CASES_TAC (← q r"x1:real = x2") THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THENL
     [UNDISCH_TAC (← q r"&0 <= x2") THEN
      DISCH_THEN (DISJ_CASES_TAC o REWRITE_RULE [REAL_LE_LT]) THENL
       [FIRST_ASSUM (fun th => tactic_of do pure (ASM_REWRITE_TAC [← MATCH_MP REAL_LE_LMUL_LOCAL th])),
        SUBST1_TAC (← SYM (← ASSUME (← q r"&0 = x2"))) THEN
        REWRITE_TAC [REAL_MUL_LZERO, REAL_LE_REFL]], ALL_TAC] THEN
    UNDISCH_TAC (← q r"y1 <= y2") THEN
    DISCH_THEN (DISJ_CASES_TAC o REWRITE_RULE [REAL_LE_LT]) THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_MUL2_ALT THEN
      ASM_REWRITE_TAC [],
      ASM_REWRITE_TAC []] THEN
    UNDISCH_TAC (← q r"&0 <= y1") THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (DISJ_CASES_TAC o REWRITE_RULE [REAL_LE_LT]) THENL
     [FIRST_ASSUM (fun th => tactic_of do pure (ASM_REWRITE_TAC [← MATCH_MP REAL_LE_RMUL_EQ th])) THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC [],
      SUBST1_TAC (← SYM (← ASSUME (← q r"&0 = y2"))) THEN
      REWRITE_TAC [REAL_MUL_RZERO, REAL_LE_REFL]])

  let REAL_LE_LDIV ← prove
   r"!x y z. &0 < x /\ y <= (z * x) ==> (y / x) <= z"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MATCH_MP_TAC (← TAUT (← q r"(a = b) ==> a ==> b")) THEN
    SUBGOAL_THEN (← q r"y = (y / x) * x") MP_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
      CONV_TAC (RAND_CONV SYM_CONV) THEN
      MATCH_MP_TAC REAL_LT_IMP_NE THEN POP_ASSUM ACCEPT_TAC,
      DISCH_THEN (fun t => GEN_REWRITE_TAC (funpow 2 LAND_CONV) [t])
      THEN MATCH_MP_TAC REAL_LE_RMUL_EQ THEN POP_ASSUM ACCEPT_TAC])

  let REAL_LE_RDIV ← prove
   r"!x y z. &0 < x /\ (y * x) <= z ==> y <= (z / x)"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MATCH_MP_TAC EQ_IMP THEN
    SUBGOAL_THEN (← q r"z = (z / x) * x") MP_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
      CONV_TAC (RAND_CONV SYM_CONV) THEN
      MATCH_MP_TAC REAL_LT_IMP_NE THEN POP_ASSUM ACCEPT_TAC,
      DISCH_THEN (fun t => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [t])
      THEN MATCH_MP_TAC REAL_LE_RMUL_EQ THEN POP_ASSUM ACCEPT_TAC])

  let REAL_LT_1 ← prove
   r"!x y. &0 <= x /\ x < y ==> (x / y) < &1"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"(x / y) < &1 <=> ((x / y) * y) < (&1 * y)") SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_LT_RMUL_EQ THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q "x:real") THEN
      ASM_REWRITE_TAC [],
      SUBGOAL_THEN (← q r"(x / y) * y = x") SUBST1_TAC THENL
       [MATCH_MP_TAC REAL_DIV_RMUL THEN CONV_TAC (RAND_CONV SYM_CONV) THEN
        MATCH_MP_TAC REAL_LT_IMP_NE THEN MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC (← q "x:real") THEN ASM_REWRITE_TAC [],
        ASM_REWRITE_TAC [REAL_MUL_LID]]])

  let REAL_LE_LMUL_IMP ← prove
   r"!x y z. &0 <= x /\ y <= z ==> (x * y) <= (x * z)"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN (DISJ_CASES_TAC o REWRITE_RULE [REAL_LE_LT]) THENL
     [FIRST_ASSUM (fun th => tactic_of do pure (ASM_REWRITE_TAC [← MATCH_MP REAL_LE_LMUL_LOCAL th])),
      FIRST_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC [REAL_MUL_LZERO] THEN
      MATCH_ACCEPT_TAC REAL_LE_REFL])

  let REAL_LE_RMUL_IMP ← prove
   r"!x y z. &0 <= x /\ y <= z ==> (y * x) <= (z * x)"
   (ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN MATCH_ACCEPT_TAC REAL_LE_LMUL_IMP)

  let REAL_INV_LT1 ← prove
   r"!x. &0 < x /\ x < &1 ==> &1 < inv(x)"
   (GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP REAL_INV_POS) THEN
    GEN_REWRITE_TAC id [← TAUT (← q r"a <=> ~ ~a")] THEN
    PURE_REWRITE_TAC [REAL_NOT_LT] THEN REWRITE_TAC [REAL_LE_LT] THEN
    DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL
     [DISCH_TAC THEN
      MP_TAC (← SPECL [← q r"inv(x)", ← q r"&1", ← q "x:real", ← q r"&1"] REAL_LT_MUL2_ALT) THEN
      ASM_REWRITE_TAC [NOT_IMP] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC [],
        MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC [],
        DISCH_THEN (MP_TAC o MATCH_MP REAL_LT_IMP_NE) THEN
        REWRITE_TAC [REAL_MUL_LID] THEN MATCH_MP_TAC REAL_MUL_LINV THEN
        DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"&0 < &0") THEN
        REWRITE_TAC [REAL_LT_REFL]],
      DISCH_THEN (MP_TAC o AP_TERM (← q "inv")) THEN REWRITE_TAC [REAL_INV1] THEN
      SUBGOAL_THEN (← q r"inv(inv x) = x") SUBST1_TAC THENL
       [MATCH_MP_TAC REAL_INVINV THEN CONV_TAC (RAND_CONV SYM_CONV) THEN
        MATCH_MP_TAC REAL_LT_IMP_NE THEN FIRST_ASSUM ACCEPT_TAC,
        DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"&1 < &1") THEN
        REWRITE_TAC [REAL_LT_REFL]]])

  let REAL_LT_IMP_NZ ← prove
   r"!x. &0 < x ==> ~(x = &0)"
   (GEN_TAC THEN DISCH_THEN (ASSUME_TAC o MATCH_MP REAL_LT_IMP_NE) THEN
    CONV_TAC (RAND_CONV SYM_CONV) THEN POP_ASSUM ACCEPT_TAC)

  let REAL_EQ_RMUL_IMP ← prove
   r"!x y z. ~(z = &0) /\ (x * z = y * z) ==> (x = y)"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC [REAL_EQ_RMUL])

  let REAL_EQ_LMUL_IMP ← prove
   r"!x y z. ~(x = &0) /\ (x * y = x * z) ==> (y = z)"
   (ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN MATCH_ACCEPT_TAC REAL_EQ_RMUL_IMP)

  let REAL_FACT_NZ ← prove
   r"!n. ~(&(FACT n) = &0)"
   (GEN_TAC THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
    REWRITE_TAC [REAL_LT, FACT_LT])

  let REAL_POSSQ ← prove
   r"!x. &0 < (x * x) <=> ~(x = &0)"
   (GEN_TAC THEN REWRITE_TAC [← GSYM REAL_NOT_LE] THEN AP_TERM_TAC THEN EQ_TAC THENL
     [(← do let p ← SPEC (← q "x:real") REAL_LE_SQUARE
            pure (DISCH_THEN (MP_TAC o (fun th => CONJ th p)))) THEN
      REWRITE_TAC [REAL_LE_ANTISYM, REAL_ENTIRE],
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [REAL_MUL_LZERO, REAL_LE_REFL]])

  let REAL_SUMSQ ← prove
   r"!x y. ((x * x) + (y * y) = &0) <=> (x = &0) /\ (y = &0)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC [DE_MORGAN_THM] THEN
      DISCH_THEN DISJ_CASES_TAC THEN MATCH_MP_TAC REAL_LT_IMP_NZ THENL
       [MATCH_MP_TAC REAL_LTE_ADD, MATCH_MP_TAC REAL_LET_ADD] THEN
      ASM_REWRITE_TAC [REAL_POSSQ, REAL_LE_SQUARE],
      DISCH_TAC THEN ASM_REWRITE_TAC [REAL_MUL_LZERO, REAL_ADD_LID]])

  let REAL_EQ_NEG ← prove
   r"!x y. (--x = --y) <=> (x = y)"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [← GSYM REAL_LE_ANTISYM, REAL_LE_NEG2] THEN
    MATCH_ACCEPT_TAC CONJ_SYM)

  let REAL_DIV_MUL2 ← prove
   r"!x z. ~(x = &0) /\ ~(z = &0) ==> !y. y / z = (x * y) / (x * z)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    REWRITE_TAC [real_div] THEN IMP_SUBST_TAC REAL_INV_MUL_WEAK THEN
    ASM_REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [← AC REAL_MUL_AC
      (← q r"(a * b) * (c * d) = (c * a) * (b * d)")] THEN
    IMP_SUBST_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [REAL_MUL_LID])

  let REAL_MIDDLE1 ← prove
   r"!a b. a <= b ==> a <= (a + b) / &2"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_RDIV THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    REWRITE_TAC [← GSYM REAL_DOUBLE] THEN
    ASM_REWRITE_TAC [← GSYM REAL_DOUBLE, REAL_LE_LADD] THEN
    REWRITE_TAC [← numc "2", REAL_LT, LT_0])

  let REAL_MIDDLE2 ← prove
   r"!a b. a <= b ==> ((a + b) / &2) <= b"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_LDIV THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    REWRITE_TAC [← GSYM REAL_DOUBLE] THEN
    ASM_REWRITE_TAC [← GSYM REAL_DOUBLE, REAL_LE_RADD] THEN
    REWRITE_TAC [← numc "2", REAL_LT, LT_0])

  -- @@RETURN BEGIN
  return { REAL_HALF_DOUBLE, REAL_SUB_SUB, REAL_LT_ADD_SUB, REAL_LT_SUB_RADD,
           REAL_LT_SUB_LADD, REAL_LE_SUB_LADD, REAL_LE_SUB_RADD, REAL_LT_NEG2,
           REAL_LE_NEG2, REAL_SUB_LZERO, REAL_SUB_RZERO, REAL_LTE_ADD2, REAL_LTE_ADD,
           REAL_LT_MUL2_ALT, REAL_SUB_LNEG, REAL_SUB_RNEG, REAL_SUB_NEG2,
           REAL_SUB_TRIANGLE, REAL_INV_MUL_WEAK, REAL_LE_LMUL_LOCAL, REAL_LE_RMUL_EQ,
           REAL_SUB_INV2, REAL_SUB_SUB2, REAL_MEAN, REAL_EQ_LMUL2, REAL_LE_MUL2V,
           REAL_LE_LDIV, REAL_LE_RDIV, REAL_LT_1, REAL_LE_LMUL_IMP, REAL_LE_RMUL_IMP,
           REAL_INV_LT1, REAL_LT_IMP_NZ, REAL_EQ_RMUL_IMP, REAL_EQ_LMUL_IMP,
           REAL_FACT_NZ, REAL_POSSQ, REAL_SUMSQ, REAL_EQ_NEG, REAL_DIV_MUL2,
           REAL_MIDDLE1, REAL_MIDDLE2 }
  -- @@RETURN END

/-- lib.ml's `end_itlist` for a rule that can fail: `f h (end_itlist f t)`. -/
def endItlistM {α : Type} (f : α → α → ExceptT String IO α) : List α → ExceptT String IO α
  | [] => throw "end_itlist"
  | [x] => pure x
  | h :: t => do f h (← endItlistM f t)

/- ------------------------------------------------------------------------- -/
/- Define usual norm (absolute distance) on the real line.                   -/
/- (analysis.ml 1230-1527)                                                   -/
/- ------------------------------------------------------------------------- -/

structure Abs where
  -- @@FIELDS
  ABS_ZERO : thm
  ABS_0 : thm
  ABS_1 : thm
  ABS_NEG : thm
  ABS_TRIANGLE : thm
  ABS_POS : thm
  ABS_MUL : thm
  ABS_LT_MUL2 : thm
  ABS_SUB : thm
  ABS_NZ : thm
  ABS_INV : thm
  ABS_ABS : thm
  ABS_LE : thm
  ABS_REFL : thm
  ABS_N : thm
  ABS_BETWEEN : thm
  ABS_BOUND : thm
  ABS_STILLNZ : thm
  ABS_CASES : thm
  ABS_BETWEEN1 : thm
  ABS_SIGN : thm
  ABS_SIGN2 : thm
  ABS_DIV : thm
  ABS_CIRCLE : thm
  REAL_SUB_ABS : thm
  ABS_SUB_ABS : thm
  ABS_BETWEEN2 : thm
  ABS_BOUNDS : thm
  deriving Inhabited

@[nospecialize]
def setupAbs [HolBase] (D : AnalysisDeps) (BNames : Names) (BReals1 : Reals1) (BReals2 : Reals2) (BReals3 : Reals3) :
    ExceptT String IO Abs := do
  -- @@SCOPE BEGIN
  let { num_CONV, .. } := D
  let { LE_0, NOT_LT, NOT_SUC, REAL_ADD_AC, REAL_ADD_LID, REAL_ADD_LINV, REAL_ADD_SUB,
        REAL_ADD_SYM, .. } := D.core1
  let { REAL_ENTIRE, REAL_LET_ADD2, REAL_LET_TOTAL, REAL_LET_TRANS, REAL_LE_ADD2,
        REAL_LE_ADDR, REAL_LE_ANTISYM, REAL_LT_ADDL, REAL_LT_ADDR, REAL_LT_REFL,
        REAL_LT_TRANS, REAL_MUL_LINV, .. } := D.core2
  let { real_abs, real_div, real_sub, .. } := D.core3
  let { NOT_LESS_0, .. } := BNames
  let { REAL_LE_LADD, REAL_LE_LT, REAL_LE_MUL, REAL_LE_NEGTOTAL, REAL_LE_RADD,
        REAL_LE_REFL, REAL_LE_TRANS, REAL_LTE_TRANS, REAL_LT_ADD2, REAL_LT_ANTISYM,
        REAL_LT_IMP_LE, REAL_LT_RADD, REAL_NEG_ADD, REAL_NEG_GE0, REAL_NEG_LMUL,
        REAL_NEG_LT0, REAL_NEG_NEG, REAL_NEG_RMUL, REAL_NOT_LE, REAL_NOT_LT,
        REAL_RNEG_UNIQ, REAL_SUB_ADD, REAL_SUB_ADD2, .. } := BReals1
  let { REAL_DOUBLE, REAL_INJ, REAL_LE, REAL_LE_NEGL, REAL_LE_NEGR, REAL_LINV_UNIQ,
        REAL_LT_HALF2, REAL_NEG_0, REAL_NEG_EQ0, REAL_NEG_SUB, REAL_SUB_LE,
        REAL_SUB_LT, .. } := BReals2
  let { REAL_HALF_DOUBLE, REAL_LE_NEG2, REAL_LT_MUL2_ALT, REAL_LT_SUB_RADD,
        REAL_SUB_LZERO, REAL_SUB_NEG2, .. } := BReals3
  -- @@SCOPE END
  let numc (s : String) : ExceptT String IO thm := do ExceptT.mk (num_CONV (← q s))

  let ABS_ZERO ← prove
   r"!x. (abs(x) = &0) <=> (x = &0)"
   (GEN_TAC THEN REWRITE_TAC [real_abs] THEN
    COND_CASES_TAC THEN REWRITE_TAC [REAL_NEG_EQ0])

  let ABS_0 ← prove
   r"abs(&0) = &0"
   (REWRITE_TAC [ABS_ZERO])

  let ABS_1 ← prove
   r"abs(&1) = &1"
   (REWRITE_TAC [real_abs, REAL_LE, LE_0])

  let ABS_NEG ← prove
   r"!x. abs(--x) = abs(x)"
   (GEN_TAC THEN REWRITE_TAC [real_abs, REAL_NEG_NEG, REAL_NEG_GE0] THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC [] THENL
     [MP_TAC (← CONJ (← ASSUME (← q r"&0 <= x")) (← ASSUME (← q r"x <= &0"))) THEN
      REWRITE_TAC [REAL_LE_ANTISYM] THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [REAL_NEG_0],
      RULE_ASSUM_TAC (REWRITE_RULE [REAL_NOT_LE]) THEN
      (fun gl => tactic_of (do
        pure (MP_TAC (← endItlistM CONJ (gl.1.map Prod.snd)))) gl) THEN
      REWRITE_TAC [REAL_LT_ANTISYM]])

  let ABS_TRIANGLE ← prove
   r"!x y. abs(x + y) <= abs(x) + abs(y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [real_abs] THEN
    REPEAT COND_CASES_TAC THEN
    REWRITE_TAC [REAL_NEG_ADD, REAL_LE_REFL, REAL_LE_LADD, REAL_LE_RADD] THEN
    ASM_REWRITE_TAC [← GSYM REAL_NEG_ADD, REAL_LE_NEGL, REAL_LE_NEGR] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [REAL_NOT_LE]) THEN
    TRY (MATCH_MP_TAC REAL_LT_IMP_LE) THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
    TRY (UNDISCH_TAC (← q r"(x + y) < &0")) THEN SUBST1_TAC (← SYM (← SPEC (← q r"&0") REAL_ADD_LID))
    THEN REWRITE_TAC [REAL_NOT_LT] THEN
    MAP_FIRST MATCH_MP_TAC [REAL_LT_ADD2, REAL_LE_ADD2] THEN
    ASM_REWRITE_TAC [])

  let ABS_POS ← prove
   r"!x. &0 <= abs(x)"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"&0 <= x") THENL
     [ALL_TAC,
      MP_TAC (← SPEC (← q "x:real") REAL_LE_NEGTOTAL) THEN ASM_REWRITE_TAC [] THEN
      DISCH_TAC] THEN
    ASM_REWRITE_TAC [real_abs])

  let ABS_MUL ← prove
   r"!x y. abs(x * y) = abs(x) * abs(y)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"&0 <= x") THENL
     [ALL_TAC,
      MP_TAC (← SPEC (← q "x:real") REAL_LE_NEGTOTAL) THEN ASM_REWRITE_TAC [] THEN
      POP_ASSUM (fun _ => ALL_TAC) THEN DISCH_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [← GSYM ABS_NEG] THEN
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [← GSYM ABS_NEG]
      THEN REWRITE_TAC [REAL_NEG_LMUL]] THEN
    (ASM_CASES_TAC (← q r"&0 <= y") THENL
      [ALL_TAC,
       MP_TAC (← SPEC (← q "y:real") REAL_LE_NEGTOTAL) THEN ASM_REWRITE_TAC [] THEN
       POP_ASSUM (fun _ => ALL_TAC) THEN DISCH_TAC THEN
       GEN_REWRITE_TAC LAND_CONV [← GSYM ABS_NEG] THEN
       GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [← GSYM ABS_NEG] THEN
       REWRITE_TAC [REAL_NEG_RMUL]]) THEN
    ASSUM_LIST (fun ths => tactic_of do
      pure (ASSUME_TAC (← MATCH_MP REAL_LE_MUL (← endItlistM CONJ ths.reverse)))) THEN
    ASM_REWRITE_TAC [real_abs])

  let ABS_LT_MUL2 ← prove
   r"!w x y z. abs(w) < y /\ abs(x) < z ==> abs(w * x) < (y * z)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [ABS_MUL] THEN MATCH_MP_TAC REAL_LT_MUL2_ALT THEN
    ASM_REWRITE_TAC [ABS_POS])

  let ABS_SUB ← prove
   r"!x y. abs(x - y) = abs(y - x)"
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [← GSYM REAL_NEG_SUB] THEN
    REWRITE_TAC [ABS_NEG])

  let ABS_NZ ← prove
   r"!x. ~(x = &0) <=> &0 < abs(x)"
   (GEN_TAC THEN EQ_TAC THENL
     [ONCE_REWRITE_TAC [← GSYM ABS_ZERO] THEN
      REWRITE_TAC [← TAUT (← q r"~a ==> b <=> b \/ a")] THEN
      CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
      REWRITE_TAC [← GSYM REAL_LE_LT, ABS_POS],
      CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC [] THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [real_abs, REAL_LT_REFL, REAL_LE_REFL]])

  let ABS_INV ← prove
   r"!x. ~(x = &0) ==> (abs(inv x) = inv(abs(x)))"
   (GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LINV_UNIQ THEN
    REWRITE_TAC [← GSYM ABS_MUL] THEN
    FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP REAL_MUL_LINV th])) THEN
    REWRITE_TAC [real_abs, REAL_LE] THEN
    REWRITE_TAC [← numc "1", ← GSYM NOT_LT, NOT_LESS_0])

  let ABS_ABS ← prove
   r"!x. abs(abs(x)) = abs(x)"
   (GEN_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [real_abs] THEN
    REWRITE_TAC [ABS_POS])

  let ABS_LE ← prove
   r"!x. x <= abs(x)"
   (GEN_TAC THEN REWRITE_TAC [real_abs] THEN
    COND_CASES_TAC THEN REWRITE_TAC [REAL_LE_REFL] THEN
    REWRITE_TAC [REAL_LE_NEGR] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [REAL_NOT_LE])

  let ABS_REFL ← prove
   r"!x. (abs(x) = x) <=> &0 <= x"
   (GEN_TAC THEN REWRITE_TAC [real_abs] THEN
    ASM_CASES_TAC (← q r"&0 <= x") THEN ASM_REWRITE_TAC [] THEN
    CONV_TAC (RAND_CONV SYM_CONV) THEN
    ONCE_REWRITE_TAC [← GSYM REAL_RNEG_UNIQ] THEN
    REWRITE_TAC [REAL_DOUBLE, REAL_ENTIRE, REAL_INJ] THEN
    REWRITE_TAC [← numc "2", NOT_SUC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC [REAL_LE_REFL])

  let ABS_N ← prove
   r"!n. abs(&n) = &n"
   (GEN_TAC THEN REWRITE_TAC [ABS_REFL, REAL_LE, LE_0])

  let ABS_BETWEEN ← prove
   r"!x y d. &0 < d /\ ((x - d) < y) /\ (y < (x + d)) <=> abs(y - x) < d"
   (REPEAT GEN_TAC THEN REWRITE_TAC [real_abs] THEN
    REWRITE_TAC [REAL_SUB_LE] THEN REWRITE_TAC [REAL_NEG_SUB] THEN
    COND_CASES_TAC THEN REWRITE_TAC [REAL_LT_SUB_RADD] THEN
    GEN_REWRITE_TAC (funpow 2 RAND_CONV) [REAL_ADD_SYM] THEN
    EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THENL
     [SUBGOAL_THEN (← q r"x < (x + d)") MP_TAC THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q "y:real") THEN
        ASM_REWRITE_TAC [], ALL_TAC] THEN
      REWRITE_TAC [REAL_LT_ADDR] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q "y:real") THEN
      ASM_REWRITE_TAC [REAL_LT_ADDR],
      RULE_ASSUM_TAC (REWRITE_RULE [REAL_NOT_LE]) THEN
      SUBGOAL_THEN (← q r"y < (y + d)") MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (← q "x:real") THEN
        ASM_REWRITE_TAC [], ALL_TAC] THEN
      REWRITE_TAC [REAL_LT_ADDR] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (← q "x:real") THEN
      ASM_REWRITE_TAC [REAL_LT_ADDR]])

  let ABS_BOUND ← prove
   r"!x y d. abs(x - y) < d ==> y < (x + d)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [ABS_SUB] THEN
    ONCE_REWRITE_TAC [← GSYM ABS_BETWEEN] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC [])

  let ABS_STILLNZ ← prove
   r"!x y. abs(x - y) < abs(y) ==> ~(x = &0)"
   (REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
    REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [REAL_SUB_LZERO, ABS_NEG, REAL_LT_REFL])

  let ABS_CASES ← prove
   r"!x. (x = &0) \/ &0 < abs(x)"
   (GEN_TAC THEN REWRITE_TAC [← GSYM ABS_NZ] THEN
    BOOL_CASES_TAC (← q r"x = &0") THEN ASM_REWRITE_TAC [])

  let ABS_BETWEEN1 ← prove
   r"!x y z. x < z /\ (abs(y - x)) < (z - x) ==> y < z"
   (REPEAT GEN_TAC THEN
    DISJ_CASES_TAC (← SPECL [← q "x:real", ← q "y:real"] REAL_LET_TOTAL) THENL
     [ASM_REWRITE_TAC [real_abs, REAL_SUB_LE] THEN
      REWRITE_TAC [real_sub, REAL_LT_RADD] THEN
      DISCH_THEN (ACCEPT_TAC o CONJUNCT2),
      DISCH_TAC THEN MATCH_MP_TAC REAL_LT_TRANS THEN
      EXISTS_TAC (← q "x:real") THEN ASM_REWRITE_TAC []])

  let ABS_SIGN ← prove
   r"!x y. abs(x - y) < y ==> &0 < x"
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP ABS_BOUND) THEN
    REWRITE_TAC [REAL_LT_ADDL])

  let ABS_SIGN2 ← prove
   r"!x y. abs(x - y) < --y ==> x < &0"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC (← SPECL [← q r"--x", ← q r"--y"] ABS_SIGN) THEN
    REWRITE_TAC [REAL_SUB_NEG2] THEN
    ONCE_REWRITE_TAC [ABS_SUB] THEN
    DISCH_THEN (fun th => FIRST_ASSUM (MP_TAC o MATCH_MP th)) THEN
    REWRITE_TAC [← GSYM REAL_NEG_LT0, REAL_NEG_NEG])

  let ABS_DIV ← prove
   r"!y. ~(y = &0) ==> !x. abs(x / y) = abs(x) / abs(y)"
   (GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN REWRITE_TAC [real_div] THEN
    REWRITE_TAC [ABS_MUL] THEN
    POP_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP ABS_INV th])))

  let ABS_CIRCLE ← prove
   r"!x y h. abs(h) < (abs(y) - abs(x)) ==> abs(x + h) < abs(y)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q r"abs(x) + abs(h)") THEN
    REWRITE_TAC [ABS_TRIANGLE] THEN
    POP_ASSUM (MP_TAC o CONJ (← SPEC (← q r"abs(x)") REAL_LE_REFL)) THEN
    DISCH_THEN (MP_TAC o MATCH_MP REAL_LET_ADD2) THEN
    REWRITE_TAC [REAL_SUB_ADD2])

  let REAL_SUB_ABS ← prove
   r"!x y. (abs(x) - abs(y)) <= abs(x - y)"
   (REPEAT GEN_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"(abs(x - y) + abs(y)) - abs(y)") THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC [real_sub] THEN REWRITE_TAC [REAL_LE_RADD] THEN
      SUBST1_TAC (← SYM (← SPECL [← q "x:real", ← q "y:real"] REAL_SUB_ADD)) THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REAL_SUB_ADD] THEN
      MATCH_ACCEPT_TAC ABS_TRIANGLE,
      ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
      REWRITE_TAC [REAL_ADD_SUB, REAL_LE_REFL]])

  let ABS_SUB_ABS ← prove
   r"!x y. abs(abs(x) - abs(y)) <= abs(x - y)"
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [real_abs] THEN
    COND_CASES_TAC THEN REWRITE_TAC [REAL_SUB_ABS] THEN
    REWRITE_TAC [REAL_NEG_SUB] THEN
    ONCE_REWRITE_TAC [ABS_SUB] THEN
    REWRITE_TAC [REAL_SUB_ABS])

  let ABS_BETWEEN2 ← prove
   r"!x0 x y0 y. x0 < y0 /\ abs(x - x0) < (y0 - x0) / &2 /\
                          abs(y - y0) < (y0 - x0) / &2
        ==> x < y"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"x < y0 /\ x0 < y") STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC (← SPECL [← q "x0:real", ← q "x:real", ← q r"y0 - x0"] ABS_BOUND) THEN
        REWRITE_TAC [REAL_SUB_ADD2] THEN DISCH_THEN MATCH_MP_TAC THEN
        ONCE_REWRITE_TAC [ABS_SUB] THEN
        MATCH_MP_TAC REAL_LT_TRANS THEN
        EXISTS_TAC (← q r"(y0 - x0) / &2") THEN ASM_REWRITE_TAC [REAL_LT_HALF2] THEN
        ASM_REWRITE_TAC [REAL_SUB_LT],
        GEN_REWRITE_TAC id [← TAUT (← q r"a = ~ ~a")] THEN
        PURE_REWRITE_TAC [REAL_NOT_LT] THEN DISCH_TAC THEN
        MP_TAC (← AC REAL_ADD_AC
         (← q r"(y0 + --x0) + (x0 + --y) = (--x0 + x0) + (y0 + --y)")) THEN
        REWRITE_TAC [← GSYM real_sub, REAL_ADD_LINV, REAL_ADD_LID] THEN
        DISCH_TAC THEN
        MP_TAC (← SPECL [← q r"y0 - x0", ← q r"x0 - y"] REAL_LE_ADDR) THEN
        ASM_REWRITE_TAC [REAL_SUB_LE] THEN DISCH_TAC THEN
        SUBGOAL_THEN (← q r"~(y0 <= y)") ASSUME_TAC THENL
         [REWRITE_TAC [REAL_NOT_LE] THEN ONCE_REWRITE_TAC [← GSYM REAL_SUB_LT] THEN
          MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q r"y0 - x0") THEN
          ASM_REWRITE_TAC [] THEN ASM_REWRITE_TAC [REAL_SUB_LT], ALL_TAC] THEN
        UNDISCH_TAC (← q r"abs(y - y0) < (y0 - x0) / &2") THEN
        ASM_REWRITE_TAC [real_abs, REAL_SUB_LE] THEN
        REWRITE_TAC [REAL_NEG_SUB] THEN DISCH_TAC THEN
        SUBGOAL_THEN (← q r"(y0 - x0) < (y0 - x0) / &2") MP_TAC THENL
         [MATCH_MP_TAC REAL_LET_TRANS THEN
          EXISTS_TAC (← q r"y0 - y") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
        REWRITE_TAC [REAL_NOT_LT] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
        REWRITE_TAC [REAL_LT_HALF2] THEN ASM_REWRITE_TAC [REAL_SUB_LT]],
      ALL_TAC] THEN
    GEN_REWRITE_TAC id [← TAUT (← q r"a <=> ~ ~a")] THEN
    PURE_REWRITE_TAC [REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"abs(x0 - y) < (y0 - x0) / &2") ASSUME_TAC THENL
     [REWRITE_TAC [real_abs, REAL_SUB_LE] THEN ASM_REWRITE_TAC [← GSYM REAL_NOT_LT] THEN
      REWRITE_TAC [REAL_NEG_SUB] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC (← q r"x - x0") THEN REWRITE_TAC [real_sub, REAL_LE_RADD] THEN
      ASM_REWRITE_TAC [← GSYM real_sub] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC (← q r"abs(x - x0)") THEN ASM_REWRITE_TAC [ABS_LE], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"abs(y0 - x0) < ((y0 - x0) / &2) + ((y0 - x0) / &2)")
    MP_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [REAL_HALF_DOUBLE, REAL_NOT_LT, ABS_LE]] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC (← q r"abs(y0 - y) + abs(y - x0)") THEN CONJ_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC REAL_LT_ADD2 THEN ONCE_REWRITE_TAC [ABS_SUB] THEN
      ASM_REWRITE_TAC []] THEN
    SUBGOAL_THEN (← q r"y0 - x0 = (y0 - y) + (y - x0)") SUBST1_TAC THEN
    REWRITE_TAC [ABS_TRIANGLE] THEN
    REWRITE_TAC [real_sub] THEN
    ONCE_REWRITE_TAC [← AC REAL_ADD_AC
      (← q r"(a + b) + (c + d) = (b + c) + (a + d)")] THEN
    REWRITE_TAC [REAL_ADD_LINV, REAL_ADD_LID])

  let ABS_BOUNDS ← prove
   r"!x k. abs(x) <= k <=> --k <= x /\ x <= k"
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [← GSYM REAL_LE_NEG2] THEN
    REWRITE_TAC [REAL_NEG_NEG] THEN REWRITE_TAC [real_abs] THEN
    COND_CASES_TAC THENL
     [REWRITE_TAC [← TAUT (← q r"(a <=> b /\ a) <=> a ==> b")] THEN
      DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q "x:real") THEN ASM_REWRITE_TAC [REAL_LE_NEGL],
      REWRITE_TAC [← TAUT (← q r"(a <=> a /\ b) <=> a ==> b")] THEN
      DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"--x") THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [REAL_LE_NEGR] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      ASM_REWRITE_TAC [← GSYM REAL_NOT_LE]])

  -- @@RETURN BEGIN
  return { ABS_ZERO, ABS_0, ABS_1, ABS_NEG, ABS_TRIANGLE, ABS_POS, ABS_MUL, ABS_LT_MUL2,
           ABS_SUB, ABS_NZ, ABS_INV, ABS_ABS, ABS_LE, ABS_REFL, ABS_N, ABS_BETWEEN,
           ABS_BOUND, ABS_STILLNZ, ABS_CASES, ABS_BETWEEN1, ABS_SIGN, ABS_SIGN2, ABS_DIV,
           ABS_CIRCLE, REAL_SUB_ABS, ABS_SUB_ABS, ABS_BETWEEN2, ABS_BOUNDS }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Define integer powers; derive the supremum property for an arbitrary      -/
/- bounded nonempty set; prove the Archimedean property.                     -/
/- (analysis.ml 1529-1804)                                                   -/
/- ------------------------------------------------------------------------- -/

structure Pow where
  -- @@FIELDS
  pow : thm
  POW_0 : thm
  POW_NZ : thm
  POW_INV : thm
  POW_ABS : thm
  POW_PLUS1 : thm
  POW_ADD : thm
  POW_1 : thm
  POW_2 : thm
  POW_POS : thm
  POW_LE : thm
  POW_M1 : thm
  POW_MUL : thm
  REAL_LE_SQUARE_POW : thm
  ABS_POW2 : thm
  REAL_LE1_POW2 : thm
  REAL_LT1_POW2 : thm
  POW_POS_LT : thm
  POW_2_LE1 : thm
  POW_2_LT : thm
  POW_MINUS1 : thm
  REAL_SUP_EXISTS : thm
  sup_def : thm
  sup : thm
  REAL_SUP : thm
  REAL_SUP_UBOUND : thm
  SETOK_LE_LT : thm
  REAL_SUP_LE : thm
  REAL_SUP_UBOUND_LE : thm
  REAL_ARCH_SIMPLE : thm
  REAL_ARCH : thm
  REAL_ARCH_LEAST : thm
  REAL_POW_LBOUND : thm
  REAL_ARCH_POW : thm
  REAL_ARCH_POW2 : thm
  deriving Inhabited

@[nospecialize]
def setupPow [HolBase] (D : AnalysisDeps) (BCompat : Compat) (BNames : Names) (BReals1 : Reals1) (BReals2 : Reals2) (BReals3 : Reals3) (BAbs : Abs) :
    ExceptT String IO Pow := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, REAL_ARITH, new_definition, num_CONV, .. } := D
  let { ADD1, ADD_CLAUSES, ARITH, FUN_EQ_THM, IN, LE_0, LT_0, MONO_EXISTS,
        MULT_CLAUSES, PRE, REAL_ADD_ASSOC, REAL_ADD_LID, REAL_ADD_RID, .. } := D.core1
  let { REAL_COMPLETE, REAL_ENTIRE, REAL_LE_01, REAL_LE_ADDR, REAL_LE_LMUL,
        REAL_LT_ADDR, REAL_LT_REFL, REAL_MUL_AC, REAL_MUL_ASSOC, REAL_MUL_LID, .. } := D.core2
  let { REAL_MUL_SYM, REAL_OF_NUM_ADD, REAL_OF_NUM_LT, REAL_OF_NUM_SUC,
        RIGHT_FORALL_IMP_THM, num_CASES, num_WOP, real_pow, .. } := D.core3
  let { NOT_EXISTS_CONV, .. } := BCompat
  let { LESS_EQ_SUC_REFL, LESS_SUC_REFL, .. } := BNames
  let { REAL_10, REAL_LDISTRIB, REAL_LE_MUL, REAL_LE_REFL, REAL_LE_SQUARE,
        REAL_LE_TOTAL, REAL_LE_TRANS, REAL_LTE_TRANS, REAL_LT_01, REAL_LT_ADD1,
        REAL_LT_ADD2, REAL_LT_IMP_LE, REAL_LT_LE, REAL_MUL_LZERO, REAL_MUL_RID,
        REAL_NEG_LMUL, REAL_NEG_NEG, REAL_NEG_RMUL, REAL_NOT_LE, REAL_NOT_LT,
        REAL_RDISTRIB, REAL_SUB_ADD2, .. } := BReals1
  let { REAL, REAL_ADD, REAL_DOUBLE, REAL_INV1, REAL_LE, REAL_LT, REAL_POS,
        REAL_SUB_LT, .. } := BReals2
  let { REAL_INV_MUL_WEAK, REAL_LE_LMUL_LOCAL, REAL_LE_MUL2V, REAL_LE_SUB_LADD,
        REAL_LTE_ADD2, REAL_LT_MUL2_ALT, REAL_LT_SUB_RADD, .. } := BReals3
  let { ABS_1, ABS_MUL, ABS_NEG, ABS_REFL, .. } := BAbs
  -- @@SCOPE END
  let numc (s : String) : ExceptT String IO thm := do ExceptT.mk (num_CONV (← q s))

  let pow ← pure real_pow

  let POW_0 ← prove
   r"!n. &0 pow (SUC n) = &0"
   (INDUCT_TAC THEN REWRITE_TAC [pow, REAL_MUL_LZERO])

  let POW_NZ ← prove
   r"!c n. ~(c = &0) ==> ~(c pow n = &0)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC (← q "n:num", ← q "n:num") THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC [pow, REAL_10, REAL_ENTIRE])

  let POW_INV ← prove
   r"!c n. ~(c = &0) ==> (inv(c pow n) = (inv c) pow n)"
   (GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC [pow, REAL_INV1] THEN
    MP_TAC (← SPECL [← q "c:real", ← q r"c pow n"] REAL_INV_MUL_WEAK) THEN
    ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"~(c pow n = &0)") ASSUME_TAC THENL
     [MATCH_MP_TAC POW_NZ THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    ASM_REWRITE_TAC [])

  let POW_ABS ← prove
   r"!c n. abs(c) pow n = abs(c pow n)"
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [pow, ABS_1, ABS_MUL])

  let POW_PLUS1 ← prove
   r"!e n. &0 < e ==> (&1 + (&n * e)) <= (&1 + e) pow n"
   (GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    DISCH_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC [pow, REAL_MUL_LZERO, REAL_ADD_RID, REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"(&1 + e) * (&1 + (&n * e))") THEN CONJ_TAC THENL
     [REWRITE_TAC [REAL_RDISTRIB, REAL, REAL_MUL_LID] THEN
      REWRITE_TAC [REAL_LDISTRIB, REAL_MUL_RID, REAL_ADD_ASSOC, REAL_LE_ADDR] THEN
      ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
      REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC [REAL_LE_SQUARE, REAL_LE, LE_0],
      SUBGOAL_THEN (← q r"&0 < (&1 + e)")
        (fun th => tactic_of do pure (ASM_REWRITE_TAC [← MATCH_MP REAL_LE_LMUL_LOCAL th])) THEN
      GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_ADD_LID] THEN
      MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [REAL_LT] THEN REWRITE_TAC [← numc "1", LT_0]])

  let POW_ADD ← prove
   r"!c m n. c pow (m + n) = (c pow m) * (c pow n)"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [pow, ADD_CLAUSES, REAL_MUL_RID] THEN
    REWRITE_TAC [REAL_MUL_AC])

  let POW_1 ← prove
   r"!x. x pow 1 = x"
   (GEN_TAC THEN REWRITE_TAC [← numc "1"] THEN
    REWRITE_TAC [pow, REAL_MUL_RID])

  let POW_2 ← prove
   r"!x. x pow 2 = x * x"
   (GEN_TAC THEN REWRITE_TAC [← numc "2"] THEN
    REWRITE_TAC [pow, POW_1])

  let POW_POS ← prove
   r"!x n. &0 <= x ==> &0 <= (x pow n)"
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC [pow, REAL_LE_01] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC [])

  let POW_LE ← prove
   r"!n x y. &0 <= x /\ x <= y ==> (x pow n) <= (y pow n)"
   (INDUCT_TAC THEN REWRITE_TAC [pow, REAL_LE_REFL] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL2V THEN ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [POW_POS])

  let POW_M1 ← prove
   r"!n. abs((--(&1)) pow n) = &1"
   (INDUCT_TAC THEN REWRITE_TAC [pow, ABS_NEG, ABS_1] THEN
    ASM_REWRITE_TAC [ABS_MUL, ABS_NEG, ABS_1, REAL_MUL_LID])

  let POW_MUL ← prove
   r"!n x y. (x * y) pow n = (x pow n) * (y pow n)"
   (INDUCT_TAC THEN REWRITE_TAC [pow, REAL_MUL_LID] THEN
    REPEAT GEN_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [REAL_MUL_AC])

  let REAL_LE_SQUARE_POW ← prove
   r"!x. &0 <= x pow 2"
   (GEN_TAC THEN REWRITE_TAC [POW_2, REAL_LE_SQUARE])

  let ABS_POW2 ← prove
   r"!x. abs(x pow 2) = x pow 2"
   (GEN_TAC THEN REWRITE_TAC [ABS_REFL, REAL_LE_SQUARE_POW])

  let REAL_LE1_POW2 ← prove
   r"!x. &1 <= x ==> &1 <= (x pow 2)"
   (GEN_TAC THEN REWRITE_TAC [POW_2] THEN DISCH_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2V THEN ASM_REWRITE_TAC [REAL_LE_01])

  let REAL_LT1_POW2 ← prove
   r"!x. &1 < x ==> &1 < (x pow 2)"
   (GEN_TAC THEN REWRITE_TAC [POW_2] THEN DISCH_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LT_MUL2_ALT THEN ASM_REWRITE_TAC [REAL_LE_01])

  let POW_POS_LT ← prove
   r"!x n. &0 < x ==> &0 < (x pow (SUC n))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [REAL_LT_LE] THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC POW_POS THEN ASM_REWRITE_TAC [],
      CONV_TAC (RAND_CONV SYM_CONV) THEN
      MATCH_MP_TAC POW_NZ THEN
      CONV_TAC (RAND_CONV SYM_CONV) THEN ASM_REWRITE_TAC []])

  let POW_2_LE1 ← prove
   r"!n. &1 <= &2 pow n"
   (INDUCT_TAC THEN REWRITE_TAC [pow, REAL_LE_REFL] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2V THEN ASM_REWRITE_TAC [REAL_LE] THEN
    REWRITE_TAC [LE_0, ← numc "2", LESS_EQ_SUC_REFL])

  let POW_2_LT ← prove
   r"!n. &n < &2 pow n"
   (INDUCT_TAC THEN REWRITE_TAC [pow, REAL_LT_01] THEN
    REWRITE_TAC [ADD1, ← GSYM REAL_ADD, ← GSYM REAL_DOUBLE] THEN
    MATCH_MP_TAC REAL_LTE_ADD2 THEN ASM_REWRITE_TAC [POW_2_LE1])

  let POW_MINUS1 ← prove
   r"!n. (--(&1)) pow (2 * n) = &1"
   (INDUCT_TAC THEN REWRITE_TAC [MULT_CLAUSES, pow] THEN
    REWRITE_TAC [← numc "2", ← numc "1", ADD_CLAUSES] THEN
    REWRITE_TAC [pow] THEN
    REWRITE_TAC [← SYM (← numc "2"), ← SYM (← numc "1")] THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [← GSYM REAL_NEG_LMUL, ← GSYM REAL_NEG_RMUL] THEN
    REWRITE_TAC [REAL_MUL_LID, REAL_NEG_NEG])

  let REAL_SUP_EXISTS ← prove
   r"!P. (?x. P x) /\ (?z. !x. P x ==> x < z) ==>
     (?s. !y. (?x. P x /\ y < x) <=> y < s)"
   (GEN_TAC THEN MP_TAC (← SPEC (← q r"P:real->bool") REAL_COMPLETE) THEN
    MESON_TAC [REAL_LT_IMP_LE, REAL_LTE_TRANS, REAL_NOT_LT])

  let sup_def ← new_definition
   r"sup s = @a. (!x. x IN s ==> x <= a) /\
              (!b. (!x. x IN s ==> x <= b) ==> a <= b)"

  let sup ← prove
   r"sup P = @s. !y. (?x. P x /\ y < x) <=> y < s"
   (REWRITE_TAC [sup_def, IN] THEN AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN
    ASM_MESON_TAC [REAL_LTE_TRANS, REAL_NOT_LT, REAL_LE_REFL])

  let REAL_SUP ← prove
   r"!P. (?x. P x) /\ (?z. !x. P x ==> x < z) ==>
          (!y. (?x. P x /\ y < x) <=> y < sup P)"
   (GEN_TAC THEN DISCH_THEN (MP_TAC o SELECT_RULE o MATCH_MP REAL_SUP_EXISTS)
    THEN REWRITE_TAC [← GSYM sup])

  let REAL_SUP_UBOUND ← prove
   r"!P. (?x. P x) /\ (?z. !x. P x ==> x < z) ==>
          (!y. P y ==> y <= sup P)"
   (GEN_TAC THEN DISCH_THEN (MP_TAC o SPEC (← q r"sup P") o MATCH_MP REAL_SUP) THEN
    REWRITE_TAC [REAL_LT_REFL] THEN
    DISCH_THEN (ASSUME_TAC o CONV_RULE NOT_EXISTS_CONV) THEN
    X_GEN_TAC (← q "x:real") THEN RULE_ASSUM_TAC (SPEC (← q "x:real")) THEN
    DISCH_THEN (SUBST_ALL_TAC o EQT_INTRO) THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC [REAL_NOT_LT])

  let SETOK_LE_LT ← prove
   r"!P. (?x. P x) /\ (?z. !x. P x ==> x <= z) <=>
       (?x. P x) /\ (?z. !x. P x ==> x < z)"
   (← do
    -- `map EXISTS_TAC [`z + &1`; `z:real`]`: the list literal is built
    -- right to left.
    let t2 ← q "z:real"
    let t1 ← q r"z + &1"
    pure (GEN_TAC THEN AP_TERM_TAC THEN EQ_TAC THEN DISCH_THEN (X_CHOOSE_TAC (← q "z:real"))
      THENL ([t1, t2].map EXISTS_TAC) THEN GEN_TAC THEN
      DISCH_THEN (fun th => FIRST_ASSUM (MP_TAC o (fun a => MATCH_MP a th))) THEN
      REWRITE_TAC [REAL_LT_ADD1, REAL_LT_IMP_LE]))

  let REAL_SUP_LE ← prove
   r"!P. (?x. P x) /\ (?z. !x. P x ==> x <= z) ==>
           (!y. (?x. P x /\ y < x) <=> y < sup P)"
   (GEN_TAC THEN REWRITE_TAC [SETOK_LE_LT, REAL_SUP])

  let REAL_SUP_UBOUND_LE ← prove
   r"!P. (?x. P x) /\ (?z. !x. P x ==> x <= z) ==>
          (!y. P y ==> y <= sup P)"
   (GEN_TAC THEN REWRITE_TAC [SETOK_LE_LT, REAL_SUP_UBOUND])

  let REAL_ARCH_SIMPLE ← prove
   r"!x. ?n. x <= &n"
   (← do
    let lemma ← prove r"(!x. (?n. x = &n) ==> P x) <=> !n. P(&n)" (MESON_TAC [])
    let ra ← REAL_ARITH (← q r"~(M <= M - &1)")
    pure (MP_TAC (← SPEC (← q r"\y. ?n. y = &n") REAL_COMPLETE) THEN REWRITE_TAC [lemma] THEN
      MESON_TAC [REAL_LE_SUB_LADD, REAL_OF_NUM_ADD, REAL_LE_TOTAL, ra]))

  let REAL_ARCH ← prove
   r"!x. &0 < x ==> !y. ?n. y < &n * x"
   (GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    ONCE_REWRITE_TAC [← TAUT (← q r"a <=> ~(~a)")] THEN
    CONV_TAC (ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
    REWRITE_TAC [REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC (← SPEC (← q r"\z. ?n. z = &n * x") REAL_SUP_LE) THEN BETA_TAC THEN
    (fun gl => ExceptT.run do
      let t ← liftExcept (do
        let (a, _) ← dest_imp gl.2
        pure (← dest_imp a).1)
      ExceptT.mk (SUBGOAL_THEN t (fun th => REWRITE_TAC [th]) gl))
    THENL [CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [← q r"&n * x", ← q "n:num"] THEN REFL_TAC,
      EXISTS_TAC (← q "y:real") THEN GEN_TAC THEN
      DISCH_THEN (CHOOSE_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC []], ALL_TAC] THEN
    DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q r"sup(\z. ?n. z = &n * x) - x")) THEN
    REWRITE_TAC [REAL_LT_SUB_RADD, REAL_LT_ADDR] THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "z:real") MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q "n:num")) MP_TAC) THEN
    ASM_REWRITE_TAC [] THEN
    GEN_REWRITE_TAC (funpow 3 RAND_CONV) [← GSYM REAL_MUL_LID] THEN
    REWRITE_TAC [← GSYM REAL_RDISTRIB] THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q r"sup(\z. ?n. z = &n * x)")) THEN
    REWRITE_TAC [REAL_LT_REFL] THEN EXISTS_TAC (← q r"(&n + &1) * x") THEN
    ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q "n + 1") THEN
    REWRITE_TAC [REAL_ADD])

  let REAL_ARCH_LEAST ← prove
   r"!y. &0 < y ==> !x. &0 <= x ==>
                        ?n. (&n * y) <= x /\ x < (&(SUC n) * y)"
   (GEN_TAC THEN DISCH_THEN (ASSUME_TAC o MATCH_MP REAL_ARCH) THEN
    GEN_TAC THEN POP_ASSUM (ASSUME_TAC o SPEC (← q "x:real")) THEN
    POP_ASSUM (X_CHOOSE_THEN (← q "n:num") MP_TAC o
          ONCE_REWRITE_RULE [num_WOP]) THEN
    REWRITE_TAC [REAL_NOT_LT] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SPEC (← q "PRE n"))) THEN
    DISCH_TAC THEN EXISTS_TAC (← q "PRE n") THEN
    SUBGOAL_THEN (← q "SUC(PRE n) = n") ASSUME_TAC THENL
     [DISJ_CASES_THEN2 SUBST_ALL_TAC (CHOOSE_THEN SUBST_ALL_TAC)
          (← SPEC (← q "n:num") num_CASES) THENL
       [UNDISCH_TAC (← q r"x < &0 * y") THEN
        ASM_REWRITE_TAC [REAL_MUL_LZERO, ← GSYM REAL_NOT_LE],
        REWRITE_TAC [PRE]],
      ASM_REWRITE_TAC [] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      FIRST_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC [PRE, LESS_SUC_REFL]])

  let REAL_POW_LBOUND ← prove
   r"!x n. &0 <= x ==> &1 + &n * x <= (&1 + x) pow n"
   (← do
    -- Two REAL_ARITHs in one THEN chain: the later one is evaluated first.
    let ra2 ← REAL_ARITH
      (← q r"&1 + (n + &1) * x <= (&1 + x) * (&1 + n * x) <=> &0 <= n * x * x")
    let ra1 ← REAL_ARITH (← q r"&0 <= x ==> &0 <= &1 + x")
    pure (GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
      INDUCT_TAC THEN
      REWRITE_TAC [real_pow, REAL_MUL_LZERO, REAL_ADD_RID, REAL_LE_REFL] THEN
      REWRITE_TAC [← GSYM REAL_OF_NUM_SUC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"(&1 + x) * (&1 + &n * x)") THEN
      ASM_SIMP_TAC [REAL_LE_LMUL, ra1] THEN
      ASM_SIMP_TAC [REAL_LE_MUL, REAL_POS, ra2]))

  let REAL_ARCH_POW ← prove
   r"!x y. &1 < x ==> ?n. y < x pow n"
   (← do
    let ra2 ← REAL_ARITH (← q r"&1 < x ==> &0 <= x - &1")
    let ra1 ← REAL_ARITH (← q r"x < y ==> x < &1 + y")
    pure (REPEAT STRIP_TAC THEN
      MP_TAC (← SPEC (← q r"x - &1") REAL_ARCH) THEN ASM_REWRITE_TAC [REAL_SUB_LT] THEN
      DISCH_THEN (MP_TAC o SPEC (← q "y:real")) THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC (← q "n:num") THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC (← q r"&1 + &n * (x - &1)") THEN
      ASM_SIMP_TAC [ra1] THEN
      ASM_MESON_TAC [REAL_POW_LBOUND, REAL_SUB_ADD2, ra2]))

  let REAL_ARCH_POW2 ← prove
   r"!x. ?n. x < &2 pow n"
   (SIMP_TAC [REAL_ARCH_POW, REAL_OF_NUM_LT, ARITH])

  -- @@RETURN BEGIN
  return { pow, POW_0, POW_NZ, POW_INV, POW_ABS, POW_PLUS1, POW_ADD, POW_1, POW_2,
           POW_POS, POW_LE, POW_M1, POW_MUL, REAL_LE_SQUARE_POW, ABS_POW2, REAL_LE1_POW2,
           REAL_LT1_POW2, POW_POS_LT, POW_2_LE1, POW_2_LT, POW_MINUS1, REAL_SUP_EXISTS,
           sup_def, sup, REAL_SUP, REAL_SUP_UBOUND, SETOK_LE_LT, REAL_SUP_LE,
           REAL_SUP_UBOUND_LE, REAL_ARCH_SIMPLE, REAL_ARCH, REAL_ARCH_LEAST,
           REAL_POW_LBOUND, REAL_ARCH_POW, REAL_ARCH_POW2 }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Finite sums. NB: sum(m,n) f = f(m) + f(m+1) + ... + f(m+n-1); relation    -/
/- to the standard notion; stuff about sums.  (analysis.ml 1806-2108)        -/
/- ------------------------------------------------------------------------- -/

structure Sums where
  -- @@FIELDS
  sum_EXISTS : thm
  sum_DEF : thm
  sum : thm
  PSUM_SUM : thm
  PSUM_SUM_NUMSEG : thm
  SUM_TWO : thm
  SUM_DIFF : thm
  ABS_SUM : thm
  SUM_LE : thm
  SUM_EQ : thm
  SUM_POS : thm
  SUM_POS_GEN : thm
  SUM_ABS : thm
  SUM_ABS_LE : thm
  SUM_ZERO : thm
  SUM_ADD : thm
  SUM_CMUL : thm
  SUM_NEG : thm
  SUM_SUB : thm
  SUM_SUBST : thm
  SUM_NSUB : thm
  SUM_BOUND : thm
  SUM_GROUP : thm
  SUM_1 : thm
  SUM_2 : thm
  SUM_OFFSET : thm
  SUM_REINDEX : thm
  SUM_0 : thm
  SUM_CANCEL : thm
  SUM_HORNER : thm
  SUM_CONST : thm
  SUM_SPLIT : thm
  SUM_SWAP : thm
  SUM_EQ_0 : thm
  SUM_MORETERMS_EQ : thm
  SUM_DIFFERENCES_EQ : thm
  deriving Inhabited

@[nospecialize]
def setupSums [HolBase] (D : AnalysisDeps) (BReals1 : Reals1) (BReals2 : Reals2) :
    ExceptT String IO Sums := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, GEN_BETA_CONV, INDUCT_TAC, REAL_ARITH, REAL_ARITH_TAC,
        make_overloadable, new_specification, num_CONV, overload_interface,
        prioritize_real, prove_recursive_functions_exist, .. } := D
  let { ADD1, ADD_AC, ADD_ASSOC, ADD_CLAUSES, ADD_SYM, EQ_IMP_LE, EQ_TRANS, EXTENSION,
        FINITE_NUMSEG, FINITE_SUBSET, GE, IN_ELIM_THM, IN_INSERT, IN_NUMSEG, LE_ADD,
        LE_ADD_LCANCEL, LE_EXISTS, LE_REFL, LT, LTE_TRANS, LT_IMP_LE, LT_REFL,
        LT_SUC_LE, LT_TRANS, MULT_CLAUSES, NOT_IN_EMPTY, REAL_ABS_0, REAL_ABS_POS,
        REAL_ABS_REFL, REAL_ABS_TRIANGLE, REAL_ADD_AC, REAL_ADD_ASSOC,
        REAL_ADD_LDISTRIB, REAL_ADD_LID, REAL_ADD_LINV, REAL_ADD_RDISTRIB,
        REAL_ADD_RID, REAL_ADD_SUB, REAL_ADD_SYM, .. } := D.core1
  let { REAL_EQ_ADD_LCANCEL, REAL_EQ_IMP_LE, REAL_EQ_SUB_LADD, REAL_LE_ADD,
        REAL_LE_ADD2, REAL_LE_ANTISYM, REAL_MUL_LID, .. } := D.core2
  let { REAL_OF_NUM_SUC, SUBSET, SUB_ADD, SUM_CLAUSES, num_RECURSION, real_pow,
        real_sub, .. } := D.core3
  let { REAL_LE_RADD, REAL_LE_REFL, REAL_LE_TRANS, REAL_MUL_LZERO, REAL_MUL_RID,
        REAL_MUL_RZERO, REAL_NEG_ADD, REAL_SUB_ADD, .. } := BReals1
  let { REAL_NEG_0, REAL_SUB_0, REAL_SUB_REFL, .. } := BReals2
  -- @@SCOPE END
  let numc (s : String) : ExceptT String IO thm := do ExceptT.mk (num_CONV (← q s))

  prioritize_real

  make_overloadable "sum" (← qty "A->(B->real)->real")

  overload_interface "sum" (← q "sum:(A->bool)->(A->real)->real")
  overload_interface "sum" (← q "psum:(num#num)->(num->real)->real")

  let sum_EXISTS ← prove
   r"?sum. (!f n. sum(n,0) f = &0) /\
         (!f m n. sum(n,SUC m) f = sum(n,m) f + f(n + m))"
   (← do
    let pt ← q r"(!f n. sm n 0 f = &0) /\
     (!f m n. sm  n (SUC m) f = sm n m f + f(n + m))"
    let ex ← q r"\(n,m) f. (sm:num->num->(num->real)->real) n m f"
    pure ((fun g => tactic_of (do
        pure (CHOOSE_TAC (← prove_recursive_functions_exist num_RECURSION pt))) g) THEN
      EXISTS_TAC ex THEN
      CONV_TAC (DEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC []))

  let sum_DEF ← new_specification ["psum"] sum_EXISTS

  let sum ← prove
   r"(sum(n,0) f = &0) /\
   (sum(n,SUC m) f = sum(n,m) f + f(n + m))"
   (REWRITE_TAC [sum_DEF])

  let PSUM_SUM ← prove
   r"!f m n. sum(m,n) f = sum {i | m <= i /\ i < m + n} f"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [sum] THENL
     [SUBGOAL_THEN (← q r"{i | m <= i /\ i < m + 0} = {}")
       (fun th => SIMP_TAC [th, SUM_CLAUSES]) THEN
      REWRITE_TAC [EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY] THEN ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN
      (← q r"FINITE {i | m <= i /\ i < m + n} /\
     {i | m <= i /\ i < m + SUC n} =
                (m + n) INSERT {i | m <= i /\ i < m + n}")
      (fun th => ASM_SIMP_TAC [th, SUM_CLAUSES, IN_ELIM_THM,
                               LT_REFL, REAL_ADD_AC]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q "m..m+n") THEN
      REWRITE_TAC [FINITE_NUMSEG, SUBSET, IN_NUMSEG, IN_ELIM_THM],
      REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_INSERT]] THEN
    ARITH_TAC)

  let PSUM_SUM_NUMSEG ← prove
   r"!f m n. ~(m = 0 /\ n = 0) ==> sum(m,n) f = sum(m..(m+n)-1) f"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [PSUM_SUM] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, IN_NUMSEG, IN_ELIM_THM] THEN
    POP_ASSUM MP_TAC THEN ARITH_TAC)

  let SUM_TWO ← prove
   r"!f n p. sum(0,n) f + sum(n,p) f = sum(0,n + p) f"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC [sum, REAL_ADD_RID, ADD_CLAUSES] THEN
    ASM_REWRITE_TAC [REAL_ADD_ASSOC])

  let SUM_DIFF ← prove
   r"!f m n. sum(m,n) f = sum(0,m + n) f - sum(0,m) f"
   (REPEAT GEN_TAC THEN REWRITE_TAC [REAL_EQ_SUB_LADD] THEN
    ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN MATCH_ACCEPT_TAC SUM_TWO)

  let ABS_SUM ← prove
   r"!f m n. abs(sum(m,n) f) <= sum(m,n) (\n. abs(f n))"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC [sum, REAL_ABS_0, REAL_LE_REFL] THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"abs(sum(m,n) f) + abs(f(m + n))") THEN
    ASM_REWRITE_TAC [REAL_ABS_TRIANGLE, REAL_LE_RADD])

  let SUM_LE ← prove
   r"!f g m n. (!r. m <= r /\ r < n + m ==> f(r) <= g(r))
        ==> (sum(m,n) f <= sum(m,n) g)"
   (EVERY (replicate GEN_TAC 3) THEN
    INDUCT_TAC THEN REWRITE_TAC [sum, REAL_LE_REFL] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [ADD_CLAUSES] THEN
      MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC (← q r"(n:num) + m"),
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [ADD_SYM]] THEN
    ASM_REWRITE_TAC [ADD_CLAUSES, LE_ADD, LT])

  let SUM_EQ ← prove
   r"!f g m n. (!r. m <= r /\ r < (n + m) ==> (f(r) = g(r)))
        ==> (sum(m,n) f = sum(m,n) g)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [← GSYM REAL_LE_ANTISYM] THEN
    CONJ_TAC THEN MATCH_MP_TAC SUM_LE THEN GEN_TAC THEN
    DISCH_THEN (fun th => MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      FIRST_ASSUM (SUBST1_TAC o (fun a => MATCH_MP a th))) THEN REFL_TAC)

  let SUM_POS ← prove
   r"!f. (!n. &0 <= f(n)) ==> !m n. &0 <= sum(m,n) f"
   (GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC [sum, REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC [])

  let SUM_POS_GEN ← prove
   r"!f m n.
     (!n. m <= n ==> &0 <= f(n))
     ==> &0 <= sum(m,n) f"
   (REPEAT STRIP_TAC THEN SPEC_TAC (← q "n:num", ← q "n:num") THEN INDUCT_TAC THEN
    REWRITE_TAC [sum, REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN
    ASM_REWRITE_TAC [] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_ACCEPT_TAC LE_ADD)

  let SUM_ABS ← prove
   r"!f m n. abs(sum(m,n) (\m. abs(f m))) = sum(m,n) (\m. abs(f m))"
   (GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [REAL_ABS_REFL] THEN
    SPEC_TAC (← q "m:num", ← q "m:num") THEN MATCH_MP_TAC SUM_POS THEN BETA_TAC THEN
    REWRITE_TAC [REAL_ABS_POS])

  let SUM_ABS_LE ← prove
   r"!f m n. abs(sum(m,n) f) <= sum(m,n)(\n. abs(f n))"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC [sum, REAL_ABS_0, REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"abs(sum(m,n) f) + abs(f(m + n))") THEN
    REWRITE_TAC [REAL_ABS_TRIANGLE] THEN BETA_TAC THEN
    ASM_REWRITE_TAC [REAL_LE_RADD])

  let SUM_ZERO ← prove
   r"!f N. (!n. n >= N ==> (f(n) = &0)) ==>
         (!m n. m >= N ==> (sum(m,n) f = &0))"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [← q "m:num", ← q "n:num"] THEN REWRITE_TAC [GE] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "d:num") SUBST1_TAC o REWRITE_RULE [LE_EXISTS]) THEN
    SPEC_TAC (← q "n:num", ← q "n:num") THEN INDUCT_TAC THEN REWRITE_TAC [sum] THEN
    ASM_REWRITE_TAC [REAL_ADD_LID] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC [GE, ← GSYM ADD_ASSOC, LE_ADD])

  let SUM_ADD ← prove
   r"!f g m n. sum(m,n) (\n. f(n) + g(n)) = sum(m,n) f + sum(m,n) g"
   (EVERY (replicate GEN_TAC 3) THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [sum, REAL_ADD_LID, REAL_ADD_AC])

  let SUM_CMUL ← prove
   r"!f c m n. sum(m,n) (\n. c * f(n)) = c * sum(m,n) f"
   (EVERY (replicate GEN_TAC 3) THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [sum, REAL_MUL_RZERO] THEN BETA_TAC THEN
    REWRITE_TAC [REAL_ADD_LDISTRIB])

  let SUM_NEG ← prove
   r"!f n d. sum(n,d) (\n. --(f n)) = --(sum(n,d) f)"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [sum, REAL_NEG_0] THEN
    BETA_TAC THEN REWRITE_TAC [REAL_NEG_ADD])

  let SUM_SUB ← prove
   r"!f g m n. sum(m,n)(\n. (f n) - (g n)) = sum(m,n) f - sum(m,n) g"
   (REPEAT GEN_TAC THEN REWRITE_TAC [real_sub, ← GSYM SUM_NEG, ← GSYM SUM_ADD])

  let SUM_SUBST ← prove
   r"!f g m n. (!p. m <= p /\ p < (m + n) ==> (f p = g p))
        ==> (sum(m,n) f = sum(m,n) g)"
   (EVERY (replicate GEN_TAC 3) THEN INDUCT_TAC THEN REWRITE_TAC [sum] THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN BINOP_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [ADD_CLAUSES, LT_SUC_LE] THEN
      MATCH_MP_TAC LT_IMP_LE THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [LE_ADD] THEN ONCE_REWRITE_TAC [ADD_SYM] THEN
      REWRITE_TAC [LT_SUC_LE, LE_REFL, ADD_CLAUSES]])

  let SUM_NSUB ← prove
   r"!n f c. sum(0,n) f - (&n * c) = sum(0,n)(\p. f(p) - c)"
   (INDUCT_TAC THEN REWRITE_TAC [sum, REAL_MUL_LZERO, REAL_SUB_REFL] THEN
    REWRITE_TAC [ADD_CLAUSES, ← GSYM REAL_OF_NUM_SUC, REAL_ADD_RDISTRIB] THEN
    REPEAT GEN_TAC THEN POP_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← GSYM th])) THEN
    REWRITE_TAC [real_sub, REAL_NEG_ADD, REAL_MUL_LID, REAL_ADD_AC])

  let SUM_BOUND ← prove
   r"!f K m n. (!p. m <= p /\ p < (m + n) ==> (f(p) <= K))
        ==> (sum(m,n) f <= (&n * K))"
   (EVERY (replicate GEN_TAC 3) THEN INDUCT_TAC THEN
    REWRITE_TAC [sum, REAL_MUL_LZERO, REAL_LE_REFL] THEN
    DISCH_TAC THEN REWRITE_TAC [← GSYM REAL_OF_NUM_SUC, REAL_ADD_RDISTRIB] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [ADD_CLAUSES, LT_SUC_LE, LE_REFL] THEN
      MATCH_MP_TAC LT_IMP_LE THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [REAL_MUL_LID] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC [ADD_CLAUSES, LE_ADD, LT_SUC_LE, LE_REFL]])

  let SUM_GROUP ← prove
   r"!n k f. sum(0,n)(\m. sum(m * k,k) f) = sum(0,n * k) f"
   (INDUCT_TAC THEN REWRITE_TAC [sum, MULT_CLAUSES] THEN
    REPEAT GEN_TAC THEN BETA_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [ADD_CLAUSES, SUM_TWO])

  let SUM_1 ← prove
   r"!f n. sum(n,1) f = f(n)"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [← numc "1", sum, ADD_CLAUSES, REAL_ADD_LID])

  let SUM_2 ← prove
   r"!f n. sum(n,2) f = f(n) + f(n + 1)"
   (REPEAT GEN_TAC THEN CONV_TAC (REDEPTH_CONV num_CONV) THEN
    REWRITE_TAC [sum, ADD_CLAUSES, REAL_ADD_LID])

  let SUM_OFFSET ← prove
   r"!f n k. sum(0,n)(\m. f(m + k)) = sum(0,n + k) f - sum(0,k) f"
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ADD_SYM] THEN
    REWRITE_TAC [← GSYM SUM_TWO, REAL_ADD_SUB] THEN
    SPEC_TAC (← q "n:num", ← q "n:num") THEN INDUCT_TAC THEN REWRITE_TAC [sum] THEN
    BETA_TAC THEN ASM_REWRITE_TAC [ADD_CLAUSES] THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN MATCH_ACCEPT_TAC ADD_SYM)

  let SUM_REINDEX ← prove
   r"!f m k n. sum(m + k,n) f = sum(m,n)(\r. f(r + k))"
   (EVERY (replicate GEN_TAC 3) THEN INDUCT_TAC THEN REWRITE_TAC [sum] THEN
    ASM_REWRITE_TAC [REAL_EQ_ADD_LCANCEL] THEN REWRITE_TAC [ADD_AC])

  let SUM_0 ← prove
   r"!m n. sum(m,n)(\r. &0) = &0"
   (GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [sum] THEN
    BETA_TAC THEN ASM_REWRITE_TAC [REAL_ADD_LID])

  let SUM_CANCEL ← prove
   r"!f n d. sum(n,d) (\n. f(SUC n) - f(n)) = f(n + d) - f(n)"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [sum, ADD_CLAUSES, REAL_SUB_REFL] THEN
    BETA_TAC THEN ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
    REWRITE_TAC [real_sub, REAL_NEG_ADD, REAL_ADD_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [← GSYM REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_RID])

  let SUM_HORNER ← prove
   r"!f n x. sum(0,SUC n)(\i. f(i) * x pow i) =
           f(0) + x * sum(0,n)(\i. f(SUC i) * x pow i)"
   (← do
    let ra ← REAL_ARITH (← q r"a * b * c = b * (a * c)")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM SUM_CMUL] THEN
      ONCE_REWRITE_TAC [ra] THEN
      REWRITE_TAC [← GSYM real_pow] THEN
      MP_TAC (← GEN (← q r"f:num->real")
       (← SPECL [← q r"f:num->real", ← q "n:num", ← q "1"] SUM_OFFSET)) THEN
      REWRITE_TAC [← GSYM ADD1] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN
      REWRITE_TAC [SUM_1] THEN REWRITE_TAC [real_pow, REAL_MUL_RID] THEN
      ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN REWRITE_TAC [REAL_SUB_ADD]))

  let SUM_CONST ← prove
   r"!c n. sum(0,n) (\m. c) = &n * c"
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [sum, ← GSYM REAL_OF_NUM_SUC, REAL_MUL_LZERO] THEN
    REWRITE_TAC [REAL_ADD_RDISTRIB, REAL_MUL_LID])

  let SUM_SPLIT ← prove
   r"!f n p. sum(m,n) f + sum(m + n,p) f = sum(m,n + p) f"
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SUM_DIFF] THEN
    GEN_REWRITE_TAC RAND_CONV [SUM_DIFF] THEN
    REWRITE_TAC [ADD_ASSOC] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [← GSYM SUM_TWO] THEN
    REAL_ARITH_TAC)

  let SUM_SWAP ← prove
   r"!f m1 n1 m2 n2.
        sum(m1,n1) (\a. sum(m2,n2) (\b. f a b)) =
        sum(m2,n2) (\b. sum(m1,n1) (\a. f a b))"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC [sum, SUM_0] THEN ASM_REWRITE_TAC [SUM_ADD])

  let SUM_EQ_0 ← prove
   r"(!r. m <= r /\ r < m + n ==> (f(r) = &0)) ==> (sum(m,n) f = &0)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"sum(m,n) (\r. &0)") THEN
    CONJ_TAC THENL [ALL_TAC, REWRITE_TAC [SUM_0]] THEN
    MATCH_MP_TAC SUM_EQ THEN ASM_REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN ASM_REWRITE_TAC [])

  let SUM_MORETERMS_EQ ← prove
   r"!m n p.
      n <= p /\ (!r. m + n <= r /\ r < m + p ==> (f(r) = &0))
      ==> (sum(m,p) f = sum(m,n) f)"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (SUBST1_TAC o GSYM o MATCH_MP SUB_ADD) THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN REWRITE_TAC [← GSYM SUM_SPLIT] THEN
    SUBGOAL_THEN (← q r"sum (m + n,p - n) f = &0")
     (fun th => REWRITE_TAC [REAL_ADD_RID, th]) THEN MATCH_MP_TAC SUM_EQ_0 THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC (← q r"(m + n) + p - n:num") THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [← GSYM ADD_ASSOC, LE_ADD_LCANCEL] THEN MATCH_MP_TAC EQ_IMP_LE THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN ASM_SIMP_TAC [SUB_ADD])

  let SUM_DIFFERENCES_EQ ← prove
   r"!m n p.
      n <= p /\ (!r. m + n <= r /\ r < m + p ==> (f(r) = g(r)))
      ==> (sum(m,p) f - sum(m,n) f = sum(m,p) g - sum(m,n) g)"
   (ONCE_REWRITE_TAC [← REAL_ARITH (← q r"(a - b = c - d) <=> (a - c = b - d)")] THEN
    SIMP_TAC [← GSYM SUM_SUB, SUM_MORETERMS_EQ, REAL_SUB_0])

  -- @@RETURN BEGIN
  return { sum_EXISTS, sum_DEF, sum, PSUM_SUM, PSUM_SUM_NUMSEG, SUM_TWO, SUM_DIFF,
           ABS_SUM, SUM_LE, SUM_EQ, SUM_POS, SUM_POS_GEN, SUM_ABS, SUM_ABS_LE, SUM_ZERO,
           SUM_ADD, SUM_CMUL, SUM_NEG, SUM_SUB, SUM_SUBST, SUM_NSUB, SUM_BOUND,
           SUM_GROUP, SUM_1, SUM_2, SUM_OFFSET, SUM_REINDEX, SUM_0, SUM_CANCEL,
           SUM_HORNER, SUM_CONST, SUM_SPLIT, SUM_SWAP, SUM_EQ_0, SUM_MORETERMS_EQ,
           SUM_DIFFERENCES_EQ }
  -- @@RETURN END

/-- tactics.ml's `FREEZE_THEN`. -/
def FREEZE_THEN [HolBase] (ttac : thm_tactic) (th : thm) : tactic :=
  HolCore.Tactics.FREEZE_THEN HolBase.B ttac th

/-- The recursive `sum_conv` of `REAL_SUM_CONV` (analysis.ml 2119-2123). -/
partial def realSumGo [HolBase] (conv0 conv1 num_CONV : ioconv) : ioconv := fun tm => do
  match ← conv0 tm with
  | .ok th => pure (.ok th)
  | .error _ =>
    (LAND_CONV (RAND_CONV num_CONV) THENC
     conv1 THENC LAND_CONV (realSumGo conv0 conv1 num_CONV)) tm

/-- The recursive `sum_conv` of `REAL_HORNER_SUM_CONV` (analysis.ml 2141-2145). -/
partial def realHornerSumGo [HolBase] (conv0 conv1 num_CONV : ioconv) : ioconv := fun tm => do
  match ← conv0 tm with
  | .ok th => pure (.ok th)
  | .error _ =>
    (LAND_CONV (RAND_CONV num_CONV) THENC
     conv1 THENC RAND_CONV (RAND_CONV (realHornerSumGo conv0 conv1 num_CONV))) tm

/- ------------------------------------------------------------------------- -/
/- A conversion to evaluate summations.  (analysis.ml 2111-2152)             -/
/- ------------------------------------------------------------------------- -/

structure SumConv where
  -- @@FIELDS
  REAL_SUM_CONV : ioconv
  REAL_HORNER_SUM_CONV : ioconv
  deriving Inhabited

@[nospecialize]
def setupSumConv [HolBase] (D : AnalysisDeps) (BSums : Sums) :
    ExceptT String IO SumConv := do
  -- @@SCOPE BEGIN
  let { num_CONV, .. } := D
  let { ADD_CLAUSES, REAL_ADD_LID, .. } := D.core1
  let { SUM_HORNER, sum, .. } := BSums
  -- @@SCOPE END
  let numc (s : String) : ExceptT String IO thm := do ExceptT.mk (num_CONV (← q s))
  -- The guard of both conversions (analysis.ml 2125-2130).
  let guarded (sum_tm : term) (go : ioconv) (err : String) : ioconv := fun tm => ExceptT.run do
    let (sn, _bod) ← liftExcept (dest_comb tm)
    let (s, ntm) ← liftExcept (dest_comb sn)
    let (_, htm) ← liftExcept (HolMath.Pair.dest_pair ntm)
    if s == sum_tm && HolMath.Nums.is_numeral htm then ExceptT.mk (go tm)
    else throw err

  let REAL_SUM_CONV : ioconv ← do
    let sum_tm ← q "sum"
    let pth ← prove
     r"sum(0,1) f = f 0"
     (REWRITE_TAC [← numc "1", sum, REAL_ADD_LID, ADD_CLAUSES])
    -- `let conv0 = ... and conv1 = ...`: left to right.
    let conv0 ← GEN_REWRITE_CONV_NET id [← CONJUNCT1 sum, pth]
    let conv1 := REWR_CONV (← CONJUNCT2 sum)
    pure (guarded sum_tm (realSumGo conv0 conv1 num_CONV) "REAL_SUM_CONV")

  let REAL_HORNER_SUM_CONV : ioconv ← do
    let sum_tm ← q "sum"
    let pth ← prove
     r"sum(0,1) f = f 0"
     (REWRITE_TAC [← numc "1", sum, REAL_ADD_LID, ADD_CLAUSES])
    let conv0 ← GEN_REWRITE_CONV_NET id [← CONJUNCT1 sum, pth]
    let conv1 := REWR_CONV SUM_HORNER
    pure (guarded sum_tm (realHornerSumGo conv0 conv1 num_CONV) "REAL_HORNER_SUM_CONV")

  -- @@RETURN BEGIN
  return { REAL_SUM_CONV, REAL_HORNER_SUM_CONV }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Topologies and metric spaces, including metric on real line.             -/
/- (analysis.ml 2154-2414)                                                   -/
/- ------------------------------------------------------------------------- -/

structure Topology where
  -- @@FIELDS
  re_Union : thm
  re_union : thm
  re_intersect : thm
  re_null : thm
  re_universe : thm
  re_subset : thm
  re_compl : thm
  SUBSETA_REFL : thm
  COMPL_MEM : thm
  SUBSETA_ANTISYM : thm
  SUBSETA_TRANS : thm
  istopology : thm
  topology_tybij : thm
  TOPOLOGY : thm
  TOPOLOGY_UNION : thm
  neigh : thm
  OPEN_OWN_NEIGH : thm
  OPEN_UNOPEN : thm
  OPEN_SUBOPEN : thm
  OPEN_NEIGH : thm
  closed : thm
  limpt : thm
  CLOSED_LIMPT : thm
  ismet : thm
  metric_tybij : thm
  METRIC_ISMET : thm
  METRIC_ZERO : thm
  METRIC_SAME : thm
  METRIC_POS : thm
  METRIC_SYM : thm
  METRIC_TRIANGLE : thm
  METRIC_NZ : thm
  deriving Inhabited

@[nospecialize]
def setupTopology [HolBase] (D : AnalysisDeps) (BCompat : Compat) (BTactics : Tactics) (BReals1 : Reals1) :
    ExceptT String IO Topology := do
  -- @@SCOPE BEGIN
  let { GEN_BETA_CONV, new_definition, new_type_definition, parse_as_infix, .. } := D
  let { DE_MORGAN_THM, NOT_IMP, REAL_ADD_LID, REAL_ADD_RID, .. } := D.core1
  let { REAL_LE_01, REAL_LE_ADD2, REAL_LE_ANTISYM, .. } := D.core2
  let { AND_FORALL_CONV, FUN_EQ_CONV, NOT_EXISTS_CONV, NOT_FORALL_CONV, .. } := BCompat
  let { EQUAL_TAC, .. } := BTactics
  let { REAL_10, REAL_LE_LT, REAL_LE_REFL, REAL_LT_ADD2, REAL_NOT_LE, .. } := BReals1
  -- @@SCOPE END
  parse_as_infix ("re_union", (15, "right"))
  parse_as_infix ("re_intersect", (17, "right"))
  parse_as_infix ("re_subset", (12, "right"))

  let re_Union ← new_definition
   r"re_Union S = \x:A. ?s. S s /\ s x"

  let re_union ← new_definition
   r"P re_union Q = \x:A. P x \/ Q x"

  let re_intersect ← new_definition
   r"P re_intersect Q = \x:A. P x /\ Q x"

  let re_null ← new_definition
   r"re_null = \x:A. F"

  let re_universe ← new_definition
   r"re_universe = \x:A. T"

  let re_subset ← new_definition
   r"P re_subset Q <=> !x:A. P x ==> Q x"

  let re_compl ← new_definition
   r"re_compl S = \x:A. ~(S x)"

  let SUBSETA_REFL ← prove
   r"!S:A->bool. S re_subset S"
   (GEN_TAC THEN REWRITE_TAC [re_subset])

  let COMPL_MEM ← prove
   r"!S:A->bool. !x. S x <=> ~(re_compl S x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [re_compl] THEN
    BETA_TAC THEN REWRITE_TAC [])

  let SUBSETA_ANTISYM ← prove
   r"!P:A->bool. !Q. P re_subset Q /\ Q re_subset P <=> (P = Q)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [re_subset] THEN
    CONV_TAC (ONCE_DEPTH_CONV AND_FORALL_CONV) THEN
    REWRITE_TAC [← TAUT (← q r"(a ==> b) /\ (b ==> a) <=> (a <=> b)")] THEN
    CONV_TAC (RAND_CONV FUN_EQ_CONV) THEN REFL_TAC)

  let SUBSETA_TRANS ← prove
   r"!P:A->bool. !Q R. P re_subset Q /\ Q re_subset R ==> P re_subset R"
   (REPEAT GEN_TAC THEN REWRITE_TAC [re_subset] THEN
    CONV_TAC (ONCE_DEPTH_CONV AND_FORALL_CONV) THEN
    (← do
      let xA ← q "x:A"
      pure (DISCH_THEN (fun th => tactic_of do
        pure (MATCH_ACCEPT_TAC (← GEN xA (← endItlistM IMP_TRANS
          (CONJUNCTS (← SPEC xA th)))))))))

  let istopology ← new_definition
   r"!L:(A->bool)->bool. istopology L <=>
            L re_null /\
            L re_universe /\
     (!a b. L a /\ L b ==> L (a re_intersect b)) /\
       (!P. P re_subset L ==> L (re_Union P))"

  let topology_tybij ← new_type_definition "topology" ("topology", "open")
   (← prove r"?t:(A->bool)->bool. istopology t"
        (EXISTS_TAC (← q r"re_universe:(A->bool)->bool") THEN
         REWRITE_TAC [istopology, re_universe]))

  let TOPOLOGY ← prove
   r"!L:(A)topology. open(L) re_null /\
                   open(L) re_universe /\
            (!x y. open(L) x /\ open(L) y ==> open(L) (x re_intersect y)) /\
              (!P. P re_subset (open L) ==> open(L) (re_Union P))"
   (GEN_TAC THEN REWRITE_TAC [← GSYM istopology] THEN
    REWRITE_TAC [topology_tybij])

  let TOPOLOGY_UNION ← prove
   r"!L:(A)topology. !P. P re_subset (open L) ==> open(L) (re_Union P)"
   (REWRITE_TAC [TOPOLOGY])

  let neigh ← new_definition
   r"neigh(top)(N,(x:A)) = ?P. open(top) P /\ P re_subset N /\ P x"

  let OPEN_OWN_NEIGH ← prove
   r"!S top. !x:A. open(top) S /\ S x ==> neigh(top)(S,x)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [neigh] THEN
    EXISTS_TAC (← q "S:A->bool") THEN ASM_REWRITE_TAC [SUBSETA_REFL])

  let OPEN_UNOPEN ← prove
   r"!S top. open(top) S <=>
           (re_Union (\P:A->bool. open(top) P /\ P re_subset S) = S)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN ONCE_REWRITE_TAC [← GSYM SUBSETA_ANTISYM] THEN
      REWRITE_TAC [re_Union, re_subset] THEN
      BETA_TAC THEN CONJ_TAC THEN GEN_TAC THENL
       [DISCH_THEN (X_CHOOSE_THEN (← q "s:A->bool") STRIP_ASSUME_TAC) THEN
        FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC,
        DISCH_TAC THEN EXISTS_TAC (← q "S:A->bool") THEN ASM_REWRITE_TAC []],
      DISCH_THEN (SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC TOPOLOGY_UNION THEN
      REWRITE_TAC [re_subset] THEN BETA_TAC THEN
      GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC []])

  let OPEN_SUBOPEN ← prove
   r"!S top. open(top) S <=>
           !x:A. S x ==> ?P. P x /\ open(top) P /\ P re_subset S"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
      EXISTS_TAC (← q "S:A->bool") THEN ASM_REWRITE_TAC [SUBSETA_REFL],
      DISCH_TAC THEN SUBGOAL_THEN
       (← q r"S = re_Union (\P:A->bool. open(top) P /\ P re_subset S)") SUBST1_TAC THENL
       [ONCE_REWRITE_TAC [← GSYM SUBSETA_ANTISYM] THEN CONJ_TAC THENL
         [ONCE_REWRITE_TAC [re_subset] THEN REWRITE_TAC [re_Union] THEN
          BETA_TAC THEN GEN_TAC THEN
          DISCH_THEN (fun th => FIRST_ASSUM (MP_TAC o (fun a => MATCH_MP a th))) THEN
          DISCH_THEN (X_CHOOSE_TAC (← q "P:A->bool")) THEN EXISTS_TAC (← q "P:A->bool") THEN
          ASM_REWRITE_TAC [],
          REWRITE_TAC [re_subset, re_Union] THEN BETA_TAC THEN GEN_TAC THEN
          DISCH_THEN (CHOOSE_THEN STRIP_ASSUME_TAC) THEN
          FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC],
        MATCH_MP_TAC TOPOLOGY_UNION THEN ONCE_REWRITE_TAC [re_subset] THEN
        GEN_TAC THEN BETA_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC []]])

  let OPEN_NEIGH ← prove
   r"!S top. open(top) S = !x:A. S x ==> ?N. neigh(top)(N,x) /\ N re_subset S"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC (← q "S:A->bool") THEN
      REWRITE_TAC [SUBSETA_REFL, neigh] THEN
      EXISTS_TAC (← q "S:A->bool") THEN ASM_REWRITE_TAC [SUBSETA_REFL],
      DISCH_TAC THEN ONCE_REWRITE_TAC [OPEN_SUBOPEN] THEN
      GEN_TAC THEN DISCH_THEN (fun th => FIRST_ASSUM (MP_TAC o (fun a => MATCH_MP a th))) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "N:A->bool") (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC))
      THEN REWRITE_TAC [neigh] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "P:A->bool") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q "P:A->bool") THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC SUBSETA_TRANS THEN EXISTS_TAC (← q "N:A->bool") THEN
      ASM_REWRITE_TAC []])

  let closed ← new_definition
   r"closed(L:(A)topology) S = open(L)(re_compl S)"

  let limpt ← new_definition
   r"limpt(top) x S <=>
      !N:A->bool. neigh(top)(N,x) ==> ?y. ~(x = y) /\ S y /\ N y"

  let CLOSED_LIMPT ← prove
   r"!top S. closed(top) S <=> (!x:A. limpt(top) x S ==> S x)"
   (← do
    -- The THEN chain is built right to left: the later TAUTs first.
    let t2 ← TAUT (← q r"(a <=> b \/ a) <=> b ==> a")
    let t1 ← TAUT (← q r"a \/ b \/ ~c <=> c ==> a \/ b")
    pure (REPEAT GEN_TAC THEN CONV_TAC (ONCE_DEPTH_CONV CONTRAPOS_CONV) THEN
      REWRITE_TAC [closed, limpt] THEN
      CONV_TAC (ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
      FREEZE_THEN (fun th => ONCE_REWRITE_TAC [th])
        (← SPEC (← q "S:A->bool") COMPL_MEM) THEN
      REWRITE_TAC [] THEN
      SPEC_TAC (← q r"re_compl(S:A->bool)", ← q "S:A->bool") THEN
      GEN_TAC THEN REWRITE_TAC [NOT_IMP] THEN
      CONV_TAC (ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
      REWRITE_TAC [DE_MORGAN_THM] THEN
      REWRITE_TAC [OPEN_NEIGH, re_subset] THEN
      AP_TERM_TAC THEN ABS_TAC THEN
      ASM_CASES_TAC (← q r"(S:A->bool) x") THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [t1] THEN
      EQUAL_TAC THEN
      REWRITE_TAC [t2] THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN
      POP_ASSUM ACCEPT_TAC))

  let ismet ← new_definition
   r"ismet (m:A#A->real) <=> (!x y. (m(x,y) = &0) <=> (x = y)) /\
                           (!x y z. m(y,z) <= m(x,y) + m(x,z))"

  let metric_tybij ← new_type_definition "metric" ("metric", "mdist")
   (← prove r"?m:(A#A->real). ismet m"
        (EXISTS_TAC (← q r"\((x:A),(y:A)). if x = y then &0 else &1") THEN
         REWRITE_TAC [ismet] THEN
         CONV_TAC (ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
         CONJ_TAC THEN REPEAT GEN_TAC THENL
          [BOOL_CASES_TAC (← q r"x:A = y") THEN REWRITE_TAC [REAL_10],
           REPEAT COND_CASES_TAC THEN
           ASM_REWRITE_TAC [REAL_ADD_LID, REAL_ADD_RID, REAL_LE_REFL, REAL_LE_01]
           THEN GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_ADD_LID] THEN
           TRY (MATCH_MP_TAC REAL_LE_ADD2) THEN
           REWRITE_TAC [REAL_LE_01, REAL_LE_REFL] THEN
           FIRST_ASSUM (fun th => tactic_of do
             let th' ← liftExcept (check is_neg (concl th))
             pure (UNDISCH_TAC th')) THEN
           EVERY_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC []]))

  let METRIC_ISMET ← prove
   r"!m:(A)metric. ismet (mdist m)"
   (GEN_TAC THEN REWRITE_TAC [metric_tybij])

  let METRIC_ZERO ← prove
   r"!m:(A)metric. !x y. ((mdist m)(x,y) = &0) <=> (x = y)"
   (REPEAT GEN_TAC THEN ASSUME_TAC (← SPEC (← q r"m:(A)metric") METRIC_ISMET) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [ismet]) THEN ASM_REWRITE_TAC [])

  let METRIC_SAME ← prove
   r"!m:(A)metric. !x. (mdist m)(x,x) = &0"
   (REPEAT GEN_TAC THEN REWRITE_TAC [METRIC_ZERO])

  let METRIC_POS ← prove
   r"!m:(A)metric. !x y. &0 <= (mdist m)(x,y)"
   (REPEAT GEN_TAC THEN ASSUME_TAC (← SPEC (← q r"m:(A)metric") METRIC_ISMET) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [ismet]) THEN
    FIRST_ASSUM (MP_TAC o SPECL [← q "x:A", ← q "y:A", ← q "y:A"] o CONJUNCT2) THEN
    REWRITE_TAC [← REWRITE_RULE [] (← SPECL [← q r"m:(A)metric", ← q "y:A", ← q "y:A"] METRIC_ZERO)]
    THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC [REAL_NOT_LE] THEN
    DISCH_THEN (MP_TAC o MATCH_MP REAL_LT_ADD2 o (fun th => CONJ th th)) THEN
    REWRITE_TAC [REAL_ADD_LID])

  let METRIC_SYM ← prove
   r"!m:(A)metric. !x y. (mdist m)(x,y) = (mdist m)(y,x)"
   (REPEAT GEN_TAC THEN ASSUME_TAC (← SPEC (← q r"m:(A)metric") METRIC_ISMET) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [ismet]) THEN FIRST_ASSUM
     (MP_TAC o GENL [← q "y:A", ← q "z:A"] o SPECL [← q "z:A", ← q "y:A", ← q "z:A"] o CONJUNCT2)
    THEN REWRITE_TAC [METRIC_SAME, REAL_ADD_RID] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC [← GSYM REAL_LE_ANTISYM])

  let METRIC_TRIANGLE ← prove
   r"!m:(A)metric. !x y z. (mdist m)(x,z) <= (mdist m)(x,y) + (mdist m)(y,z)"
   (REPEAT GEN_TAC THEN ASSUME_TAC (← SPEC (← q r"m:(A)metric") METRIC_ISMET) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [ismet]) THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [METRIC_SYM] THEN
    ASM_REWRITE_TAC [])

  let METRIC_NZ ← prove
   r"!m:(A)metric. !x y. ~(x = y) ==> &0 < (mdist m)(x,y)"
   (REPEAT GEN_TAC THEN
    SUBST1_TAC (← SYM (← SPECL [← q r"m:(A)metric", ← q "x:A", ← q "y:A"] METRIC_ZERO)) THEN
    ONCE_REWRITE_TAC [← TAUT (← q r"~a ==> b <=> b \/ a")] THEN
    CONV_TAC (RAND_CONV SYM_CONV) THEN
    REWRITE_TAC [← GSYM REAL_LE_LT, METRIC_POS])

  -- @@RETURN BEGIN
  return { re_Union, re_union, re_intersect, re_null, re_universe, re_subset, re_compl,
           SUBSETA_REFL, COMPL_MEM, SUBSETA_ANTISYM, SUBSETA_TRANS, istopology,
           topology_tybij, TOPOLOGY, TOPOLOGY_UNION, neigh, OPEN_OWN_NEIGH, OPEN_UNOPEN,
           OPEN_SUBOPEN, OPEN_NEIGH, closed, limpt, CLOSED_LIMPT, ismet, metric_tybij,
           METRIC_ISMET, METRIC_ZERO, METRIC_SAME, METRIC_POS, METRIC_SYM,
           METRIC_TRIANGLE, METRIC_NZ }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Metric topology; open balls; limit points in a metric topology; the usual -/
/- metric on the real line.  (analysis.ml 2417-2597)                         -/
/- ------------------------------------------------------------------------- -/

structure MetricTop where
  -- @@FIELDS
  mtop : thm
  mtop_istopology : thm
  MTOP_OPEN : thm
  ball : thm
  BALL_OPEN : thm
  BALL_NEIGH : thm
  MTOP_LIMPT : thm
  ISMET_R1 : thm
  mr1 : thm
  MR1_DEF : thm
  MR1_ADD : thm
  MR1_SUB : thm
  MR1_ADD_LE : thm
  MR1_SUB_LE : thm
  MR1_ADD_LT : thm
  MR1_SUB_LT : thm
  MR1_BETWEEN1 : thm
  MR1_LIMPT : thm
  deriving Inhabited

@[nospecialize]
def setupMetricTop [HolBase] (D : AnalysisDeps) (BReals1 : Reals1) (BReals2 : Reals2) (BReals3 : Reals3) (BAbs : Abs) (BTopology : Topology) :
    ExceptT String IO MetricTop := do
  -- @@SCOPE BEGIN
  let { GEN_BETA_CONV, new_definition, .. } := D
  let { REAL_ADD_AC, REAL_ADD_LID, REAL_ADD_LINV, REAL_ADD_SUB, REAL_ADD_SYM, .. } := D.core1
  let { REAL_LET_TRANS, REAL_LT_TOTAL, REAL_LT_TRANS, .. } := D.core2
  let { real_abs, real_sub, .. } := D.core3
  let { REAL_ADD_RID_UNIQ, REAL_LT_01, REAL_LT_IMP_LE, .. } := BReals1
  let { REAL_LT_HALF1, REAL_LT_HALF2, REAL_LT_IMP_NE, REAL_NEG_SUB, REAL_SUB_0,
        REAL_SUB_LT, .. } := BReals2
  let { REAL_LT_SUB_LADD, REAL_SUB_SUB, .. } := BReals3
  let { ABS_BETWEEN1, ABS_NEG, ABS_TRIANGLE, ABS_ZERO, .. } := BAbs
  let { METRIC_SAME, METRIC_TRIANGLE, SUBSETA_REFL, ismet, istopology, limpt,
        metric_tybij, neigh, re_Union, re_intersect, re_null, re_subset, re_universe,
        topology_tybij, .. } := BTopology
  -- @@SCOPE END
  let mtop ← new_definition
   r"!m:(A)metric. mtop m =
    topology(\S. !x. S x ==> ?e. &0 < e /\ (!y. (mdist m)(x,y) < e ==> S y))"

  let mtop_istopology ← prove
   r"!m:(A)metric. istopology
    (\S. !x. S x ==> ?e. &0 < e /\ (!y. (mdist m)(x,y) < e ==> S y))"
   (← do
    let xA ← q "x:A"
    let e1 ← q "e1:real"
    let e2 ← q "e2:real"
    let eR ← q "e:real"
    pure (GEN_TAC THEN
      REWRITE_TAC [istopology, re_null, re_universe, re_Union,
                   re_intersect, re_subset] THEN
      CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
       [EXISTS_TAC (← q r"&1") THEN MATCH_ACCEPT_TAC REAL_LT_01,
        REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
        DISCH_THEN (fun th => POP_ASSUM (CONJUNCTS_THEN (MP_TAC o SPEC xA))
                        THEN REWRITE_TAC [th]) THEN
        DISCH_THEN (X_CHOOSE_TAC e1) THEN
        DISCH_THEN (X_CHOOSE_TAC e2) THEN
        REPEAT_TCL DISJ_CASES_THEN MP_TAC
            (← SPECL [e1, e2] REAL_LT_TOTAL) THENL
         [DISCH_THEN SUBST_ALL_TAC THEN EXISTS_TAC e2 THEN
          ASM_REWRITE_TAC [] THEN GEN_TAC THEN
          DISCH_THEN (fun th => EVERY_ASSUM (ASSUME_TAC o (fun a => MATCH_MP a th) o CONJUNCT2))
          THEN ASM_REWRITE_TAC [],
          DISCH_THEN (fun th => EXISTS_TAC e1 THEN MP_TAC th),
          DISCH_THEN (fun th => EXISTS_TAC e2 THEN MP_TAC th)] THEN
        ASM_REWRITE_TAC [] THEN
        DISCH_THEN (fun th2 => GEN_TAC THEN DISCH_THEN (fun th1 => tactic_of do
          pure (ASSUME_TAC th1 THEN ASSUME_TAC (← MATCH_MP REAL_LT_TRANS (← CONJ th1 th2)))))
        THEN CONJ_TAC THEN FIRST_ASSUM (MATCH_MP_TAC o CONJUNCT2)
        THEN FIRST_ASSUM ACCEPT_TAC,
        GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"y:A->bool")
         (fun th => tactic_of do
           let c1 ← CONJUNCT1 th
           let c2 ← CONJUNCT2 th
           pure (POP_ASSUM (X_CHOOSE_TAC eR o (fun a => MATCH_MP a c2) o (fun a => MATCH_MP a c1))
             THEN ASSUME_TAC th))) THEN
        EXISTS_TAC eR THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q "z:A") THEN
        DISCH_THEN
          (fun th => FIRST_ASSUM (ASSUME_TAC o (fun a => MATCH_MP a th) o CONJUNCT2)) THEN
        EXISTS_TAC (← q r"y:A->bool") THEN ASM_REWRITE_TAC []]))

  let MTOP_OPEN ← prove
   r"!m:(A)metric. open(mtop m) S <=>
      (!x. S x ==> ?e. &0 < e /\ (!y. (mdist m(x,y)) < e ==> S y))"
   (GEN_TAC THEN REWRITE_TAC [mtop] THEN
    REWRITE_TAC [← REWRITE_RULE [topology_tybij] mtop_istopology] THEN
    BETA_TAC THEN REFL_TAC)

  let ball ← new_definition
   r"!m:(A)metric. !x e. ball(m)(x,e) = \y. (mdist m)(x,y) < e"

  let BALL_OPEN ← prove
   r"!m:(A)metric. !x e. &0 < e ==> open(mtop(m))(ball(m)(x,e))"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [MTOP_OPEN] THEN
    X_GEN_TAC (← q "z:A") THEN REWRITE_TAC [ball] THEN BETA_TAC THEN
    DISCH_THEN (ASSUME_TAC o ONCE_REWRITE_RULE [← GSYM REAL_SUB_LT]) THEN
    EXISTS_TAC (← q r"e - mdist(m:(A)metric)(x,z)") THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q "y:A") THEN REWRITE_TAC [REAL_LT_SUB_LADD] THEN
    ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC (← q r"mdist(m)((x:A),z) + mdist(m)(z,y)") THEN
    ASM_REWRITE_TAC [METRIC_TRIANGLE])

  let BALL_NEIGH ← prove
   r"!m:(A)metric. !x e. &0 < e ==> neigh(mtop(m))(ball(m)(x,e),x)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [neigh] THEN EXISTS_TAC (← q r"ball(m)((x:A),e)") THEN
    REWRITE_TAC [SUBSETA_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BALL_OPEN,
      REWRITE_TAC [ball] THEN BETA_TAC THEN REWRITE_TAC [METRIC_SAME]] THEN
    POP_ASSUM ACCEPT_TAC)

  let MTOP_LIMPT ← prove
   r"!m:(A)metric. !x S. limpt(mtop m) x S <=>
      !e. &0 < e ==> ?y. ~(x = y) /\ S y /\ (mdist m)(x,y) < e"
   (REPEAT GEN_TAC THEN REWRITE_TAC [limpt] THEN EQ_TAC THENL
     [(← do
        let bt ← q r"ball(m)((x:A),e)"
        pure (DISCH_THEN (fun th => tactic_of do
          pure (GEN_TAC THEN DISCH_TAC THEN MP_TAC (← SPEC bt th))))) THEN
      FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP BALL_NEIGH th])) THEN
      REWRITE_TAC [ball] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC,
      DISCH_TAC THEN GEN_TAC THEN REWRITE_TAC [neigh] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"P:A->bool")
        (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
      REWRITE_TAC [MTOP_OPEN] THEN
      DISCH_THEN (MP_TAC o SPEC (← q "x:A")) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "e:real") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      FIRST_ASSUM (fun th => tactic_of do
        let t ← liftExcept (check is_forall (concl th))
        pure (UNDISCH_TAC t)) THEN
      DISCH_THEN (MP_TAC o SPEC (← q "e:real")) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "y:A") STRIP_ASSUME_TAC) THEN
      DISCH_THEN (MP_TAC o SPEC (← q "y:A")) THEN ASM_REWRITE_TAC [] THEN
      DISCH_TAC THEN EXISTS_TAC (← q "y:A") THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC (← q r"(P:A->bool) re_subset N") THEN
      REWRITE_TAC [re_subset] THEN DISCH_THEN MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC])

  let ISMET_R1 ← prove
   r"ismet (\(x,y). abs(y - x))"
   (REWRITE_TAC [ismet] THEN CONV_TAC (ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    CONJ_TAC THEN REPEAT GEN_TAC THENL
     [REWRITE_TAC [ABS_ZERO, REAL_SUB_0] THEN
      CONV_TAC (RAND_CONV SYM_CONV) THEN REFL_TAC,
      SUBST1_TAC (← SYM (← SPECL [← q "x:real", ← q "y:real"] REAL_NEG_SUB)) THEN
      REWRITE_TAC [ABS_NEG] THEN SUBGOAL_THEN (← q r"z - y = (x - y) + (z - x)")
        (fun th => SUBST1_TAC th THEN MATCH_ACCEPT_TAC ABS_TRIANGLE) THEN
      REWRITE_TAC [real_sub] THEN
      ONCE_REWRITE_TAC [← AC REAL_ADD_AC
        (← q r"(a + b) + (c + d) = (d + a) + (c + b)")] THEN
      REWRITE_TAC [REAL_ADD_LINV, REAL_ADD_LID]])

  let mr1 ← new_definition
   r"mr1 = metric(\(x,y). abs(y - x))"

  let MR1_DEF ← prove
   r"!x y. (mdist mr1)(x,y) = abs(y - x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [mr1, ← REWRITE_RULE [metric_tybij] ISMET_R1]
    THEN CONV_TAC (ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REFL_TAC)

  let MR1_ADD ← prove
   r"!x d. (mdist mr1)(x,x+d) = abs(d)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [MR1_DEF, REAL_ADD_SUB])

  let MR1_SUB ← prove
   r"!x d. (mdist mr1)(x,x-d) = abs(d)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [MR1_DEF, REAL_SUB_SUB, ABS_NEG])

  let MR1_ADD_LE ← prove
   r"!x d. &0 <= d ==> ((mdist mr1)(x,x+d) = d)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [MR1_ADD, real_abs])

  let MR1_SUB_LE ← prove
   r"!x d. &0 <= d ==> ((mdist mr1)(x,x-d) = d)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [MR1_SUB, real_abs])

  let MR1_ADD_LT ← prove
   r"!x d. &0 < d ==> ((mdist mr1)(x,x+d) = d)"
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
    MATCH_ACCEPT_TAC MR1_ADD_LE)

  let MR1_SUB_LT ← prove
   r"!x d. &0 < d ==> ((mdist mr1)(x,x-d) = d)"
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
    MATCH_ACCEPT_TAC MR1_SUB_LE)

  let MR1_BETWEEN1 ← prove
   r"!x y z. x < z /\ (mdist mr1)(x,y) < (z - x) ==> y < z"
   (REPEAT GEN_TAC THEN REWRITE_TAC [MR1_DEF, ABS_BETWEEN1])

  let MR1_LIMPT ← prove
   r"!x. limpt(mtop mr1) x re_universe"
   (GEN_TAC THEN REWRITE_TAC [MTOP_LIMPT, re_universe] THEN
    X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN
    EXISTS_TAC (← q r"x + (e / &2)") THEN
    REWRITE_TAC [MR1_ADD] THEN
    SUBGOAL_THEN (← q r"&0 <= (e / &2)") ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN
      ASM_REWRITE_TAC [REAL_LT_HALF1], ALL_TAC] THEN
    ASM_REWRITE_TAC [real_abs, REAL_LT_HALF2] THEN
    CONV_TAC (RAND_CONV SYM_CONV) THEN
    REWRITE_TAC [REAL_ADD_RID_UNIQ] THEN
    CONV_TAC (RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN
    ASM_REWRITE_TAC [REAL_LT_HALF1])

  -- @@RETURN BEGIN
  return { mtop, mtop_istopology, MTOP_OPEN, ball, BALL_OPEN, BALL_NEIGH, MTOP_LIMPT,
           ISMET_R1, mr1, MR1_DEF, MR1_ADD, MR1_SUB, MR1_ADD_LE, MR1_SUB_LE, MR1_ADD_LT,
           MR1_SUB_LT, MR1_BETWEEN1, MR1_LIMPT }
  -- @@RETURN END

/-- `FIRST_ASSUM(UNDISCH_TAC o check p o concl)`'s theorem tactic: a failure
    of `p` (as of a `dest_*` inside it) is a failure of `check`. -/
def undischCheck [HolBase] (p : term → Except String Bool) : thm_tactic := fun th =>
  tactic_of do
    if (← liftExcept (p (concl th))) then pure (UNDISCH_TAC (concl th))
    else throw "check"

/- ------------------------------------------------------------------------- -/
/- Theory of Moore-Smith convergence nets: definitions, DORDER_THEN, simpler -/
/- characterizations of limits.  (analysis.ml 2599-2918)                     -/
/- ------------------------------------------------------------------------- -/

structure Nets where
  -- @@FIELDS
  dorder : thm
  tends : thm
  bounded : thm
  tendsto : thm
  DORDER_LEMMA : thm
  DORDER_THEN : thm_tactic → thm_tactic
  DORDER_NGE : thm
  DORDER_TENDSTO : thm
  MTOP_TENDS : thm
  MTOP_TENDS_UNIQ : thm
  SEQ_TENDS : thm
  LIM_TENDS : thm
  LIM_TENDS2 : thm
  MR1_BOUNDED : thm
  NET_NULL : thm
  NET_CONV_BOUNDED : thm
  NET_CONV_NZ : thm
  NET_CONV_IBOUNDED : thm
  deriving Inhabited

@[nospecialize]
def setupNets [HolBase] (D : AnalysisDeps) (BCompat : Compat) (BTactics : Tactics) (BReals1 : Reals1) (BReals2 : Reals2) (BReals3 : Reals3) (BAbs : Abs) (BTopology : Topology) (BMetricTop : MetricTop) :
    ExceptT String IO Nets := do
  -- @@SCOPE BEGIN
  let { new_definition, num_CONV, override_interface, parse_as_infix, .. } := D
  let { GE, LE_CASES, LE_REFL, LE_TRANS, LT_0, NOT_SUC, REAL_ADD_SYM, .. } := D.core1
  let { REAL_LET_TRANS, REAL_LT_INV2, REAL_LT_REFL, REAL_LT_TRANS, REAL_MUL_AC,
        REAL_MUL_LID, REAL_MUL_LINV, .. } := D.core2
  let { SWAP_EXISTS_THM, real_div, .. } := D.core3
  let { AND_FORALL_CONV, EXISTS_AND_CONV, NOT_FORALL_CONV, .. } := BCompat
  let { EQUAL_TAC, EXACT_CONV, X_BETA_CONV, .. } := BTactics
  let { REAL_LE_REFL, REAL_LE_TOTAL, REAL_LE_TRANS, REAL_LT_ADD2, REAL_LT_IMP_LE,
        REAL_LT_LADD, REAL_LT_RADD, REAL_NOT_LT, REAL_SUB_ADD, .. } := BReals1
  let { REAL_INJ, REAL_LT, REAL_LT_HALF1, REAL_LT_HALF2, REAL_NEG_SUB, REAL_RINV_UNIQ, .. } := BReals2
  let { REAL_HALF_DOUBLE, REAL_SUB_LZERO, REAL_SUB_RZERO, .. } := BReals3
  let { ABS_ABS, ABS_INV, ABS_NEG, ABS_NZ, ABS_SUB, ABS_TRIANGLE, .. } := BAbs
  let { METRIC_NZ, METRIC_SYM, METRIC_TRIANGLE, neigh, re_subset, re_universe, .. } := BTopology
  let { BALL_NEIGH, MR1_DEF, MTOP_LIMPT, MTOP_OPEN, ball, .. } := BMetricTop
  -- @@SCOPE END
  let numc (s : String) : ExceptT String IO thm := do ExceptT.mk (num_CONV (← q s))
  parse_as_infix ("tends", (12, "right"))

  let dorder ← new_definition
   r"dorder (g:A->A->bool) <=>
     !x y. g x x /\ g y y ==> ?z. g z z /\ (!w. g w z ==> g w x /\ g w y)"

  let tends ← new_definition
   r"(s tends l)(top,g) <=>
      !N:A->bool. neigh(top)(N,l) ==>
            ?n:B. g n n /\ !m:B. g m n ==> N(s m)"

  let bounded ← new_definition
   r"bounded((m:(A)metric),(g:B->B->bool)) f <=>
      ?k x N. g N N /\ (!n. g n N ==> (mdist m)(f(n),x) < k)"

  let tendsto ← new_definition
   r"tendsto((m:(A)metric),x) y z <=>
      &0 < (mdist m)(x,y) /\ (mdist m)(x,y) <= (mdist m)(x,z)"

  parse_as_infix ("-->", (12, "right"))

  override_interface "-->" (← q "(tends)")

  let DORDER_LEMMA ← prove
   r"!g:A->A->bool.
      dorder g ==>
        !P Q. (?n. g n n /\ (!m. g m n ==> P m)) /\
              (?n. g n n /\ (!m. g m n ==> Q m))
                  ==> (?n. g n n /\ (!m. g m n ==> P m /\ Q m))"
   (GEN_TAC THEN REWRITE_TAC [dorder] THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q "N1:A") STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN (← q "N2:A") STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM (MP_TAC o SPECL [← q "N1:A", ← q "N2:A"]) THEN
    REWRITE_TAC [← ASSUME (← q r"(g:A->A->bool) N1 N1"),
                 ← ASSUME (← q r"(g:A->A->bool) N2 N2")] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "n:A") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q "n:A") THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q "m:A") THEN DISCH_TAC THEN
    CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM (undischCheck (fun c => do
      pure (is_conj (← dest_imp (← dest_forall c).2).2))) THEN
    DISCH_THEN (MP_TAC o SPEC (← q "m:A")) THEN ASM_REWRITE_TAC [] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC [])

  -- Following tactic is useful in the following proofs.
  let DORDER_THEN : thm_tactic → thm_tactic ← pure (fun tac th => tactic_of do
    let ts ← liftExcept ((conjuncts (concl th)).mapM
      (fun c => do rand (← rand (← body (← rand c)))))
    let (t1, t2) ← match ts with
      | [a, b] => pure (a, b)
      | _ => throw "DORDER_THEN"
    let dog ← liftExcept (do rator (← rator (← rand (← rator (← body t1)))))
    let thl ← [t1, t2].mapM (fun t => do
      let (v, b) ← liftExcept (dest_abs t)
      ExceptT.mk (X_BETA_CONV v (← liftExcept (rand b))))
    let th1 ← CONV_RULE (← EXACT_CONV thl) th
    let th2 ← MATCH_MP DORDER_LEMMA (← ASSUME (← ExceptT.mk (list_mk_icomb "dorder" [dog])))
    let th3 ← MATCH_MP th2 th1
    let th4 ← CONV_RULE (← EXACT_CONV (← thl.mapM SYM)) th3
    pure (tac th4))

  let DORDER_NGE ← prove
   r"dorder ((>=) :num->num->bool)"
   (REWRITE_TAC [dorder, GE, LE_REFL] THEN
    REPEAT GEN_TAC THEN
    DISJ_CASES_TAC (← SPECL [← q "x:num", ← q "y:num"] LE_CASES) THENL
      [EXISTS_TAC (← q "y:num"), EXISTS_TAC (← q "x:num")] THEN
    GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC LE_TRANS THENL
      [EXISTS_TAC (← q "y:num"), EXISTS_TAC (← q "x:num")] THEN
    ASM_REWRITE_TAC [])

  let DORDER_TENDSTO ← prove
   r"!m:(A)metric. !x. dorder(tendsto(m,x))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [dorder, tendsto] THEN
    MAP_EVERY X_GEN_TAC [← q "u:A", ← q "v:A"] THEN
    REWRITE_TAC [REAL_LE_REFL] THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC [] THEN
    DISJ_CASES_TAC (← SPECL [← q r"(mdist m)((x:A),v)", ← q r"(mdist m)((x:A),u)"]
      REAL_LE_TOTAL)
    THENL [EXISTS_TAC (← q "v:A"), EXISTS_TAC (← q "u:A")] THEN ASM_REWRITE_TAC [] THEN
    GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN FIRST_ASSUM (fun th => tactic_of do
      let r ← liftExcept (rand (concl th))
      pure (EXISTS_TAC r THEN ASM_REWRITE_TAC [] THEN NO_TAC)))

  let MTOP_TENDS ← prove
   r"!d g. !x:B->A. !x0. (x --> x0)(mtop(d),g) <=>
     !e. &0 < e ==> ?n. g n n /\ !m. g m n ==> mdist(d)(x(m),x0) < e"
   (REPEAT GEN_TAC THEN REWRITE_TAC [tends] THEN EQ_TAC THEN DISCH_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN
      FIRST_ASSUM (MP_TAC o SPEC (← q r"ball(d)((x0:A),e)")) THEN
      (fun gl => ExceptT.run do
        let t ← liftExcept (funpow 2 (fun (m : Except String term) => do rand (← rator (← m)))
          (pure gl.2))
        ExceptT.mk (SUBGOAL_THEN t MP_TAC gl)) THENL
       [MATCH_MP_TAC BALL_NEIGH THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
      DISCH_THEN (fun th => REWRITE_TAC [th]) THEN REWRITE_TAC [ball] THEN
      BETA_TAC THEN GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
       [METRIC_SYM] THEN REWRITE_TAC [],
      GEN_TAC THEN REWRITE_TAC [neigh] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"P:A->bool") STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC (← q r"open(mtop(d)) (P:A->bool)") THEN
      REWRITE_TAC [MTOP_OPEN] THEN DISCH_THEN (MP_TAC o SPEC (← q "x0:A")) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "d:real") STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM (MP_TAC o SPEC (← q "d:real")) THEN
      REWRITE_TAC [← ASSUME (← q r"&0 < d")] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "n:B") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q "n:B") THEN ASM_REWRITE_TAC [] THEN
      GEN_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC (← q r"(P:A->bool) re_subset N") THEN
      REWRITE_TAC [re_subset] THEN DISCH_TAC THEN
      REPEAT (FIRST_ASSUM MATCH_MP_TAC) THEN
      ONCE_REWRITE_TAC [METRIC_SYM] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC])

  let MTOP_TENDS_UNIQ ← prove
   r"!g d. dorder (g:B->B->bool) ==>
      (x --> x0)(mtop(d),g) /\ (x --> x1)(mtop(d),g) ==> (x0:A = x1)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [MTOP_TENDS] THEN
    CONV_TAC (ONCE_DEPTH_CONV AND_FORALL_CONV) THEN
    REWRITE_TAC [← TAUT (← q r"(a ==> b) /\ (a ==> c) <=> a ==> b /\ c")] THEN
    CONV_TAC CONTRAPOS_CONV THEN DISCH_TAC THEN
    CONV_TAC NOT_FORALL_CONV THEN
    EXISTS_TAC (← q r"mdist(d:(A)metric)(x0,x1) / &2") THEN
    (fun gl => ExceptT.run do
      let t ← liftExcept (do rand (← rator (← rand gl.2)))
      ExceptT.mk (SUBGOAL_THEN t ASSUME_TAC gl)) THENL
     [REWRITE_TAC [REAL_LT_HALF1] THEN MATCH_MP_TAC METRIC_NZ THEN
      FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (DORDER_THEN MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "N:B") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN (MP_TAC o SPEC (← q "N:B")) THEN ASM_REWRITE_TAC [] THEN
    BETA_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP REAL_LT_ADD2) THEN
    REWRITE_TAC [REAL_HALF_DOUBLE, REAL_NOT_LT] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [METRIC_SYM] THEN
    MATCH_ACCEPT_TAC METRIC_TRIANGLE)

  let SEQ_TENDS ← prove
   r"!d:(A)metric. !x x0. (x --> x0)(mtop(d), (>=) :num->num->bool) <=>
     !e. &0 < e ==> ?N. !n. n >= N ==> mdist(d)(x(n),x0) < e"
   (REPEAT GEN_TAC THEN REWRITE_TAC [MTOP_TENDS, GE, LE_REFL])

  let LIM_TENDS ← prove
   r"!m1:(A)metric. !m2:(B)metric. !f x0 y0.
      limpt(mtop m1) x0 re_universe ==>
        ((f --> y0)(mtop(m2),tendsto(m1,x0)) <=>
          !e. &0 < e ==>
            ?d. &0 < d /\ !x. &0 < (mdist m1)(x,x0) /\ (mdist m1)(x,x0) <= d
                ==> (mdist m2)(f(x),y0) < e)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [MTOP_TENDS, tendsto] THEN
    AP_TERM_TAC THEN ABS_TAC THEN
    ASM_CASES_TAC (← q r"&0 < e") THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [REAL_LE_REFL] THEN EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_THEN (← q "z:A") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"(mdist m1)((x0:A),z)") THEN ASM_REWRITE_TAC [] THEN
      GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [] THEN
      SUBST1_TAC (← ISPECL [← q r"m1:(A)metric", ← q "x0:A", ← q "x:A"] METRIC_SYM) THEN
      ASM_REWRITE_TAC [],
      DISCH_THEN (X_CHOOSE_THEN (← q "d:real") STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC (← q r"limpt(mtop m1) (x0:A) re_universe") THEN
      REWRITE_TAC [MTOP_LIMPT] THEN
      DISCH_THEN (MP_TAC o SPEC (← q "d:real")) THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [re_universe] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "y:A") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q "y:A") THEN CONJ_TAC THENL
       [MATCH_MP_TAC METRIC_NZ THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
      X_GEN_TAC (← q "x:A") THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC [METRIC_SYM] THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"(mdist m1)((x0:A),y)") THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      FIRST_ASSUM ACCEPT_TAC])

  let LIM_TENDS2 ← prove
   r"!m1:(A)metric. !m2:(B)metric. !f x0 y0.
      limpt(mtop m1) x0 re_universe ==>
        ((f --> y0)(mtop(m2),tendsto(m1,x0)) <=>
          !e. &0 < e ==>
            ?d. &0 < d /\ !x. &0 < (mdist m1)(x,x0) /\ (mdist m1)(x,x0) < d ==>
              (mdist m2)(f(x),y0) < e)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP LIM_TENDS th])) THEN
    AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
    EQ_TAC THEN DISCH_THEN (X_CHOOSE_THEN (← q "d:real") STRIP_ASSUME_TAC) THENL
     [EXISTS_TAC (← q "d:real") THEN ASM_REWRITE_TAC [] THEN
      GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC [],
      EXISTS_TAC (← q r"d / &2") THEN ASM_REWRITE_TAC [REAL_LT_HALF1] THEN
      GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC (← q r"d / &2") THEN ASM_REWRITE_TAC [REAL_LT_HALF2]])

  let MR1_BOUNDED ← prove
   r"!(g:A->A->bool) f. bounded(mr1,g) f <=>
        ?k N. g N N /\ (!n. g n N ==> abs(f n) < k)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [bounded, MR1_DEF] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ABS_CONV)
     [SWAP_EXISTS_THM] THEN
    ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
    AP_TERM_TAC THEN ABS_TAC THEN
    CONV_TAC (REDEPTH_CONV EXISTS_AND_CONV) THEN
    AP_TERM_TAC THEN EQ_TAC THEN DISCH_THEN (X_CHOOSE_THEN (← q "k:real") MP_TAC) THENL
     [DISCH_THEN (X_CHOOSE_TAC (← q "x:real")) THEN
      EXISTS_TAC (← q r"abs(x) + k") THEN GEN_TAC THEN DISCH_TAC THEN
      SUBST1_TAC (← SYM (← SPECL [← q r"(f:A->real) n", ← q "x:real"] REAL_SUB_ADD)) THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC (← q r"abs((f:A->real) n - x) + abs(x)") THEN
      REWRITE_TAC [ABS_TRIANGLE] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_ADD_SYM] THEN
      REWRITE_TAC [REAL_LT_RADD] THEN
      ONCE_REWRITE_TAC [ABS_SUB] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC,
      DISCH_TAC THEN MAP_EVERY EXISTS_TAC [← q "k:real", ← q r"&0"] THEN
      ASM_REWRITE_TAC [REAL_SUB_LZERO, ABS_NEG]])

  let NET_NULL ← prove
   r"!g:A->A->bool. !x x0.
      (x --> x0)(mtop(mr1),g) <=> ((\n. x(n) - x0) --> &0)(mtop(mr1),g)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [MTOP_TENDS] THEN BETA_TAC THEN
    REWRITE_TAC [MR1_DEF, REAL_SUB_LZERO] THEN EQUAL_TAC THEN
    REWRITE_TAC [REAL_NEG_SUB])

  let NET_CONV_BOUNDED ← prove
   r"!g:A->A->bool. !x x0.
      (x --> x0)(mtop(mr1),g) ==> bounded(mr1,g) x"
   (REPEAT GEN_TAC THEN REWRITE_TAC [MTOP_TENDS, bounded] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"&1")) THEN
    REWRITE_TAC [REAL_LT, ← numc "1", LT_0] THEN
    REWRITE_TAC [← GSYM (← numc "1")] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "N:A") STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [← q r"&1", ← q "x0:real", ← q "N:A"] THEN
    ASM_REWRITE_TAC [])

  let NET_CONV_NZ ← prove
   r"!g:A->A->bool. !x x0.
      (x --> x0)(mtop(mr1),g) /\ ~(x0 = &0) ==>
        ?N. g N N /\ (!n. g n N ==> ~(x n = &0))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [MTOP_TENDS, bounded] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (MP_TAC o SPEC (← q "abs(x0)")) ASSUME_TAC) THEN
    ASM_REWRITE_TAC [← GSYM ABS_NZ] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "N:A") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_TAC THEN EXISTS_TAC (← q "N:A") THEN ASM_REWRITE_TAC [] THEN
    GEN_TAC THEN DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [MR1_DEF, REAL_SUB_RZERO, REAL_LT_REFL])

  let NET_CONV_IBOUNDED ← prove
   r"!g:A->A->bool. !x x0.
      (x --> x0)(mtop(mr1),g) /\ ~(x0 = &0) ==>
        bounded(mr1,g) (\n. inv(x n))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [MTOP_TENDS, MR1_BOUNDED, MR1_DEF] THEN
    BETA_TAC THEN REWRITE_TAC [ABS_NZ] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"abs(x0) / &2")) THEN
    ASM_REWRITE_TAC [REAL_LT_HALF1] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "N:A") STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [← q r"&2 / abs(x0)", ← q "N:A"] THEN
    ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q "n:A") THEN
    DISCH_THEN (ANTE_RES_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"(abs(x0) / &2) < abs(x(n:A))") ASSUME_TAC THENL
     [SUBST1_TAC (← SYM (← SPECL [← q r"abs(x0) / &2", ← q r"abs(x0) / &2", ← q r"abs(x(n:A))"]
        REAL_LT_LADD)) THEN
      REWRITE_TAC [REAL_HALF_DOUBLE] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC (← q r"abs(x0 - x(n:A)) + abs(x(n))") THEN
      ASM_REWRITE_TAC [REAL_LT_RADD] THEN
      SUBST1_TAC (← SYM (← AP_TERM (← q "abs")
        (← SPECL [← q "x0:real", ← q r"x(n:A):real"] REAL_SUB_ADD))) THEN
      MATCH_ACCEPT_TAC ABS_TRIANGLE, ALL_TAC] THEN
    SUBGOAL_THEN (← q r"&0 < abs(x(n:A))") ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (← q r"abs(x0) / &2") THEN
      ASM_REWRITE_TAC [REAL_LT_HALF1], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"&2 / abs(x0) = inv(abs(x0) / &2)") SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_RINV_UNIQ THEN REWRITE_TAC [real_div] THEN
      ONCE_REWRITE_TAC [← AC REAL_MUL_AC
          (← q r"(a * b) * (c * d) = (d * a) * (b * c)")] THEN
      SUBGOAL_THEN (← q r"~(abs(x0) = &0) /\ ~(&2 = &0)")
        (fun th => CONJUNCTS_THEN (SUBST1_TAC o MATCH_MP REAL_MUL_LINV) th
              THEN REWRITE_TAC [REAL_MUL_LID]) THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC [ABS_NZ, ABS_ABS],
        REWRITE_TAC [REAL_INJ, ← numc "2", NOT_SUC]], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"~(x(n:A) = &0)") (SUBST1_TAC o MATCH_MP ABS_INV) THENL
     [ASM_REWRITE_TAC [ABS_NZ], ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC [REAL_LT_HALF1])

  -- @@RETURN BEGIN
  return { dorder, tends, bounded, tendsto, DORDER_LEMMA, DORDER_THEN, DORDER_NGE,
           DORDER_TENDSTO, MTOP_TENDS, MTOP_TENDS_UNIQ, SEQ_TENDS, LIM_TENDS, LIM_TENDS2,
           MR1_BOUNDED, NET_NULL, NET_CONV_BOUNDED, NET_CONV_NZ, NET_CONV_IBOUNDED }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Combining theorems for null nets; real arithmetic for convergent nets;    -/
/- comparison between limits.  (analysis.ml 2920-3209)                       -/
/- ------------------------------------------------------------------------- -/

structure NetArith where
  -- @@FIELDS
  NET_NULL_ADD : thm
  NET_NULL_MUL : thm
  NET_NULL_CMUL : thm
  NET_ADD : thm
  NET_NEG : thm
  NET_SUB : thm
  NET_MUL : thm
  NET_INV : thm
  NET_DIV : thm
  NET_ABS : thm
  NET_SUM : thm
  NET_LE : thm
  deriving Inhabited

@[nospecialize]
def setupNetArith [HolBase] (D : AnalysisDeps) (BCompat : Compat) (BNames : Names) (BTactics : Tactics) (BReals1 : Reals1) (BReals2 : Reals2) (BReals3 : Reals3) (BAbs : Abs) (BSums : Sums) (BMetricTop : MetricTop) (BNets : Nets) :
    ExceptT String IO NetArith := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, INDUCT_TAC, num_CONV, .. } := D
  let { CONJ_ASSOC, EQ_IMP, LE_LT, REAL_ADD_AC, REAL_ADD_ASSOC, REAL_ADD_LID,
        REAL_ADD_LINV, .. } := D.core1
  let { REAL_DIV_LMUL, REAL_LET_TRANS, REAL_LT_MUL, REAL_LT_REFL, REAL_MUL_AC,
        REAL_MUL_ASSOC, REAL_MUL_LINV, .. } := D.core2
  let { REAL_MUL_SYM, RIGHT_AND_FORALL_THM, SWAP_FORALL_THM, real_abs, real_div,
        real_sub, .. } := D.core3
  let { LEFT_AND_EXISTS_CONV, .. } := BCompat
  let { LESS_SUC_REFL, .. } := BNames
  let { EQUAL_TAC, EXACT_CONV, X_BETA_CONV, .. } := BTactics
  let { REAL_LDISTRIB, REAL_LE_REFL, REAL_LT_ADD2, REAL_MUL_LZERO, REAL_MUL_RID,
        REAL_MUL_RINV, REAL_NEG_ADD, REAL_NEG_LMUL, REAL_NEG_RMUL, REAL_NOT_LE,
        REAL_RDISTRIB, .. } := BReals1
  let { REAL_INV_NZ, REAL_INV_POS, REAL_LE, REAL_LT, REAL_LT_HALF1, REAL_LT_IMP_NE,
        REAL_LT_LMUL_EQ, REAL_LT_RDIV_0, REAL_SUB_LDISTRIB, REAL_SUB_LT, .. } := BReals2
  let { REAL_HALF_DOUBLE, REAL_LT_MUL2_ALT, REAL_SUB_LZERO, REAL_SUB_NEG2, .. } := BReals3
  let { ABS_BETWEEN2, ABS_LT_MUL2, ABS_MUL, ABS_NEG, ABS_NZ, ABS_POS, ABS_SUB,
        ABS_SUB_ABS, ABS_TRIANGLE, ABS_ZERO, .. } := BAbs
  let { sum, .. } := BSums
  let { MR1_DEF, .. } := BMetricTop
  let { DORDER_THEN, MR1_BOUNDED, MTOP_TENDS, NET_CONV_BOUNDED, NET_CONV_IBOUNDED,
        NET_CONV_NZ, NET_NULL, .. } := BNets
  -- @@SCOPE END
  let numc (s : String) : ExceptT String IO thm := do ExceptT.mk (num_CONV (← q s))
  -- `end_itlist CONJ o map (SPEC t) o CONJUNCTS`
  let specConj (t : term) (th : thm) : ExceptT String IO thm := do
    endItlistM CONJ (← (CONJUNCTS th).mapM (SPEC t))

  let NET_NULL_ADD ← prove
   r"!g:A->A->bool. dorder g ==>
        !x y. (x --> &0)(mtop(mr1),g) /\ (y --> &0)(mtop(mr1),g) ==>
                ((\n. x(n) + y(n)) --> &0)(mtop(mr1),g)"
   (← do
    let e2 ← q r"e / &2"
    let eR ← q "e:real"
    pure (GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
      REWRITE_TAC [MTOP_TENDS, MR1_DEF, REAL_SUB_LZERO, ABS_NEG] THEN
      DISCH_THEN (fun th => tactic_of do
        let th' ← specConj e2 th
        pure (X_GEN_TAC eR THEN DISCH_TAC THEN MP_TAC th')) THEN
      ASM_REWRITE_TAC [REAL_LT_HALF1] THEN
      DISCH_THEN (DORDER_THEN (X_CHOOSE_THEN (← q "N:A") STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC (← q "N:A") THEN ASM_REWRITE_TAC [] THEN
      GEN_TAC THEN DISCH_THEN (ANTE_RES_THEN ASSUME_TAC) THEN
      BETA_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC (← q r"abs(x(m:A)) + abs(y(m:A))") THEN
      REWRITE_TAC [ABS_TRIANGLE] THEN RULE_ASSUM_TAC BETA_RULE THEN
      GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_HALF_DOUBLE] THEN
      MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC []))

  let NET_NULL_MUL ← prove
   r"!g:A->A->bool. dorder g ==>
      !x y. bounded(mr1,g) x /\ (y --> &0)(mtop(mr1),g) ==>
              ((\n. x(n) * y(n)) --> &0)(mtop(mr1),g)"
   (← do
    let eR ← q "e:real"
    let ek ← q r"e / k"
    pure (GEN_TAC THEN DISCH_TAC THEN
      REPEAT GEN_TAC THEN REWRITE_TAC [MR1_BOUNDED] THEN
      REWRITE_TAC [MTOP_TENDS, MR1_DEF, REAL_SUB_LZERO, ABS_NEG] THEN
      DISCH_THEN (fun th => X_GEN_TAC eR THEN DISCH_TAC THEN MP_TAC th) THEN
      CONV_TAC (LAND_CONV LEFT_AND_EXISTS_CONV) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "k:real") MP_TAC) THEN
      DISCH_THEN (fun th => tactic_of do
        let (a, b) ← CONJ_PAIR th
        let b' ← SPEC ek b
        pure (ASSUME_TAC (← CONJ a b'))) THEN
      SUBGOAL_THEN (← q r"&0 < k") ASSUME_TAC THENL
       [FIRST_ASSUM (X_CHOOSE_THEN (← q "N:A")
          (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) o CONJUNCT1) THEN
        DISCH_THEN (MP_TAC o SPEC (← q "N:A")) THEN ASM_REWRITE_TAC [] THEN
        DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC (← q r"abs(x(N:A))") THEN ASM_REWRITE_TAC [ABS_POS], ALL_TAC] THEN
      FIRST_ASSUM (undischCheck (fun c => pure (is_conj c))) THEN
      SUBGOAL_THEN (← q r"&0 < e / k") ASSUME_TAC THENL
       [FIRST_ASSUM (fun th => tactic_of do
          pure (REWRITE_TAC [← MATCH_MP REAL_LT_RDIV_0 th] THEN
            ASM_REWRITE_TAC [] THEN NO_TAC)), ALL_TAC] THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (DORDER_THEN (X_CHOOSE_THEN (← q "N:A") STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC (← q "N:A") THEN ASM_REWRITE_TAC [] THEN
      GEN_TAC THEN DISCH_THEN (ANTE_RES_THEN (ASSUME_TAC o BETA_RULE)) THEN
      SUBGOAL_THEN (← q r"e = k * (e / k)") SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
        DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"&0 < &0") THEN
        REWRITE_TAC [REAL_LT_REFL], ALL_TAC] THEN BETA_TAC THEN
      REWRITE_TAC [ABS_MUL] THEN MATCH_MP_TAC REAL_LT_MUL2_ALT THEN
      ASM_REWRITE_TAC [ABS_POS]))

  let NET_NULL_CMUL ← prove
   r"!g:A->A->bool. !k x.
      (x --> &0)(mtop(mr1),g) ==> ((\n. k * x(n)) --> &0)(mtop(mr1),g)"
   (← do
    let eR ← q "e:real"
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [MTOP_TENDS, MR1_DEF] THEN
      BETA_TAC THEN REWRITE_TAC [REAL_SUB_LZERO, ABS_NEG] THEN
      DISCH_THEN (fun th => X_GEN_TAC eR THEN DISCH_TAC THEN MP_TAC th) THEN
      ASM_CASES_TAC (← q r"k = &0") THENL
       [DISCH_THEN (MP_TAC o SPEC (← q r"&1")) THEN
        REWRITE_TAC [REAL_LT, ← numc "1", LESS_SUC_REFL] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "N:A") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q "N:A") THEN
        ASM_REWRITE_TAC [REAL_MUL_LZERO, real_abs, REAL_LE_REFL],
        DISCH_THEN (MP_TAC o SPEC (← q r"e / abs(k)")) THEN
        SUBGOAL_THEN (← q r"&0 < e / abs(k)") ASSUME_TAC THENL
         [REWRITE_TAC [real_div] THEN MATCH_MP_TAC REAL_LT_MUL THEN
          ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_INV_POS THEN
          ASM_REWRITE_TAC [← GSYM ABS_NZ], ALL_TAC] THEN
        ASM_REWRITE_TAC [] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "N:A") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q "N:A") THEN ASM_REWRITE_TAC [] THEN
        GEN_TAC THEN DISCH_THEN (ANTE_RES_THEN ASSUME_TAC) THEN
        SUBGOAL_THEN (← q r"e = abs(k) * (e / abs(k))") SUBST1_TAC THENL
         [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
          ASM_REWRITE_TAC [ABS_ZERO], ALL_TAC] THEN
        REWRITE_TAC [ABS_MUL] THEN
        SUBGOAL_THEN (← q r"&0 < abs k")
          (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP REAL_LT_LMUL_EQ th]))
        THEN ASM_REWRITE_TAC [← GSYM ABS_NZ]]))

  let NET_ADD ← prove
   r"!g:A->A->bool x x0 y y0.
        dorder g
        ==> (x --> x0)(mtop(mr1),g) /\ (y --> y0)(mtop(mr1),g)
            ==> ((\n. x(n) + y(n)) --> (x0 + y0))(mtop(mr1),g)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC [NET_NULL] THEN
    DISCH_THEN (fun th => FIRST_ASSUM
      (MP_TAC o (fun a => MATCH_MP a th) o MATCH_MP NET_NULL_ADD))
    THEN MATCH_MP_TAC EQ_IMP THEN EQUAL_TAC THEN
    BETA_TAC THEN REWRITE_TAC [real_sub, REAL_NEG_ADD] THEN
    REWRITE_TAC [REAL_ADD_AC])

  let NET_NEG ← prove
   r"!g:A->A->bool x x0.
        dorder g
        ==> ((x --> x0)(mtop(mr1),g) <=>
            ((\n. --(x n)) --> --x0)(mtop(mr1),g))"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC [MTOP_TENDS, MR1_DEF] THEN BETA_TAC THEN
    REWRITE_TAC [REAL_SUB_NEG2] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ABS_SUB] THEN
    REFL_TAC)

  let NET_SUB ← prove
   r"!g:A->A->bool x x0 y y0.
      dorder g
      ==> (x --> x0)(mtop(mr1),g) /\ (y --> y0)(mtop(mr1),g)
          ==> ((\n. x(n) - y(n)) --> (x0 - y0))(mtop(mr1),g)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [real_sub] THEN
    CONV_TAC (← EXACT_CONV [← ExceptT.mk (X_BETA_CONV (← q "n:A") (← q r"--(y(n:A))"))]) THEN
    FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP NET_ADD) THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (ONCE_REWRITE_TAC [← GSYM (← MATCH_MP NET_NEG th)])) THEN
    ASM_REWRITE_TAC [])

  let NET_MUL ← prove
   r"!g:A->A->bool x y x0 y0.
        dorder g
        ==> (x --> x0)(mtop(mr1),g) /\ (y --> y0)(mtop(mr1),g)
            ==> ((\n. x(n) * y(n)) --> (x0 * y0))(mtop(mr1),g)"
   (← do
    let nA ← q "n:A"
    pure (REPEAT GEN_TAC THEN DISCH_TAC THEN
      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [NET_NULL] THEN
      DISCH_TAC THEN BETA_TAC THEN
      SUBGOAL_THEN (← q r"!a b c d. (a * b) - (c * d) = (a * (b - d)) + ((a - c) * d)")
      (fun th => ONCE_REWRITE_TAC [th]) THENL
       [REPEAT GEN_TAC THEN
        REWRITE_TAC [real_sub, REAL_LDISTRIB, REAL_RDISTRIB, ← GSYM REAL_ADD_ASSOC]
        THEN AP_TERM_TAC THEN
        REWRITE_TAC [← GSYM REAL_NEG_LMUL, ← GSYM REAL_NEG_RMUL] THEN
        REWRITE_TAC [REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_LID], ALL_TAC] THEN
      CONV_TAC (← EXACT_CONV [← ExceptT.mk (X_BETA_CONV nA (← q r"x(n:A) * (y(n) - y0)"))]) THEN
      CONV_TAC (← EXACT_CONV [← ExceptT.mk (X_BETA_CONV nA (← q r"(x(n:A) - x0) * y0"))]) THEN
      FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP NET_NULL_ADD) THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
      CONV_TAC (← EXACT_CONV (← [← q r"y(n:A) - y0", ← q r"x(n:A) - x0"].mapM
        (fun t => ExceptT.mk (X_BETA_CONV nA t)))) THEN
      CONJ_TAC THENL
       [FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP NET_NULL_MUL) THEN
        ASM_REWRITE_TAC [] THEN MATCH_MP_TAC NET_CONV_BOUNDED THEN
        EXISTS_TAC (← q "x0:real") THEN ONCE_REWRITE_TAC [NET_NULL] THEN
        ASM_REWRITE_TAC [],
        MATCH_MP_TAC NET_NULL_CMUL THEN ASM_REWRITE_TAC []]))

  let NET_INV ← prove
   r"!g:A->A->bool x x0.
        dorder g
        ==> (x --> x0)(mtop(mr1),g) /\ ~(x0 = &0)
            ==> ((\n. inv(x(n))) --> inv x0)(mtop(mr1),g)"
   (← do
    let eR ← q "e:real"
    let ax ← ASSUME (← q r"(x --> x0)(mtop mr1,(g:A->A->bool))")
    pure (REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
      DISCH_THEN (fun th => tactic_of do
        let a ← MATCH_MP NET_CONV_IBOUNDED th
        let b ← MATCH_MP NET_CONV_NZ th
        pure (STRIP_ASSUME_TAC th THEN MP_TAC (← CONJ a b))) THEN
      REWRITE_TAC [MR1_BOUNDED] THEN
      CONV_TAC (ONCE_DEPTH_CONV LEFT_AND_EXISTS_CONV) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "k:real") MP_TAC) THEN
      DISCH_THEN (DORDER_THEN MP_TAC) THEN BETA_TAC THEN
      DISCH_THEN (MP_TAC o (fun th => CONJ th ax)) THEN
      ONCE_REWRITE_TAC [NET_NULL] THEN
      REWRITE_TAC [MTOP_TENDS, MR1_DEF, REAL_SUB_LZERO, ABS_NEG] THEN BETA_TAC
      THEN DISCH_THEN (fun th => X_GEN_TAC eR THEN DISCH_TAC THEN MP_TAC th) THEN
      ONCE_REWRITE_TAC [RIGHT_AND_FORALL_THM] THEN
      DISCH_THEN (ASSUME_TAC o SPEC (← q r"e * abs(x0) * (inv k)")) THEN
      SUBGOAL_THEN (← q r"&0 < k") ASSUME_TAC THENL
       [FIRST_ASSUM (MP_TAC o CONJUNCT1) THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "N:A") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN (MP_TAC o SPEC (← q "N:A")) THEN ASM_REWRITE_TAC [] THEN
        DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q r"abs(inv(x(N:A)))") THEN
        ASM_REWRITE_TAC [ABS_POS], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"&0 < e * abs(x0) * inv k") ASSUME_TAC THENL
       [REPEAT (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
        ASM_REWRITE_TAC [← GSYM ABS_NZ] THEN
        MATCH_MP_TAC REAL_INV_POS THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
      FIRST_ASSUM (undischCheck (fun c => pure (is_conj c))) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (DORDER_THEN MP_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "N:A") (CONJUNCTS_THEN ASSUME_TAC)) THEN
      EXISTS_TAC (← q "N:A") THEN ASM_REWRITE_TAC [] THEN
      X_GEN_TAC (← q "n:A") THEN DISCH_THEN (ANTE_RES_THEN STRIP_ASSUME_TAC) THEN
      RULE_ASSUM_TAC BETA_RULE THEN POP_ASSUM_LIST (MAP_EVERY STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN (← q r"inv(x n) - inv x0 =
                  inv(x n) * inv x0 * (x0 - x(n:A))") SUBST1_TAC THENL
       [REWRITE_TAC [REAL_SUB_LDISTRIB] THEN
        REWRITE_TAC [← MATCH_MP REAL_MUL_LINV (← ASSUME (← q r"~(x0 = &0)"))] THEN
        REWRITE_TAC [REAL_MUL_RID] THEN REPEAT AP_TERM_TAC THEN
        ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN
        REWRITE_TAC [← MATCH_MP REAL_MUL_RINV (← ASSUME (← q r"~(x(n:A) = &0)"))] THEN
        REWRITE_TAC [REAL_MUL_RID], ALL_TAC] THEN
      REWRITE_TAC [ABS_MUL] THEN ONCE_REWRITE_TAC [ABS_SUB] THEN
      SUBGOAL_THEN (← q r"e = e * (abs(inv x0) * abs(x0)) * (inv k * k)")
      SUBST1_TAC THENL
       [REWRITE_TAC [← GSYM ABS_MUL] THEN
        REWRITE_TAC [← MATCH_MP REAL_MUL_LINV (← ASSUME (← q r"~(x0 = &0)"))] THEN
        REWRITE_TAC [← MATCH_MP REAL_MUL_LINV
          (← GSYM (← MATCH_MP REAL_LT_IMP_NE (← ASSUME (← q r"&0 < k"))))] THEN
        REWRITE_TAC [REAL_MUL_RID] THEN
        REWRITE_TAC [real_abs, REAL_LE, LE_LT, ← numc "1", LESS_SUC_REFL] THEN
        REWRITE_TAC [← SYM (← numc "1"), REAL_MUL_RID], ALL_TAC] THEN
      ONCE_REWRITE_TAC [← AC REAL_MUL_AC
        (← q r"a * (b * c) * (d * e) = e * b * (a * c * d)")] THEN
      REWRITE_TAC [← GSYM ABS_MUL] THEN
      MATCH_MP_TAC ABS_LT_MUL2 THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [ABS_MUL] THEN SUBGOAL_THEN (← q r"&0 < abs(inv x0)")
        (fun th => tactic_of do pure (ASM_REWRITE_TAC [← MATCH_MP REAL_LT_LMUL_EQ th])) THEN
      REWRITE_TAC [← GSYM ABS_NZ] THEN
      MATCH_MP_TAC REAL_INV_NZ THEN ASM_REWRITE_TAC []))

  let NET_DIV ← prove
   r"!g:A->A->bool x x0 y y0.
       dorder g
       ==> (x --> x0)(mtop(mr1),g) /\
           (y --> y0)(mtop(mr1),g) /\ ~(y0 = &0)
           ==> ((\n. x(n) / y(n)) --> (x0 / y0))(mtop(mr1),g)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [real_div] THEN
    CONV_TAC (← EXACT_CONV [← ExceptT.mk (X_BETA_CONV (← q "n:A") (← q r"inv(y(n:A))"))]) THEN
    FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP NET_MUL) THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP NET_INV) THEN
    ASM_REWRITE_TAC [])

  let NET_ABS ← prove
   r"!x x0. (x --> x0)(mtop(mr1),g) ==>
               ((\n:A. abs(x n)) --> abs(x0))(mtop(mr1),g)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [MTOP_TENDS] THEN
    DISCH_TAC THEN X_GEN_TAC (← q "e:real") THEN
    DISCH_THEN (fun th => POP_ASSUM (MP_TAC o (fun a => MATCH_MP a th))) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "N:A") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q "N:A") THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q "n:A") THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC (← q r"mdist(mr1)(x(n:A),x0)") THEN CONJ_TAC THENL
     [REWRITE_TAC [MR1_DEF, ABS_SUB_ABS],
      FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC])

  let NET_SUM ← prove
   r"!g. dorder g /\
       ((\x. &0) --> &0)(mtop(mr1),g)
       ==> !m n. (!r. m <= r /\ r < m + n ==> (f r --> l r)(mtop(mr1),g))
                 ==> ((\x. sum(m,n) (\r. f r x)) --> sum(m,n) l)
                     (mtop(mr1),g)"
   (GEN_TAC THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN INDUCT_TAC THEN
    ASM_SIMP_TAC [sum] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP NET_ADD) THEN CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN
      X_GEN_TAC (← q "r:num") THEN REPEAT STRIP_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC [← ARITH_RULE (← q r"a < b + c ==> a < b + SUC c")],
      CONV_TAC (ONCE_DEPTH_CONV ETA_CONV) THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ARITH_TAC])

  let NET_LE ← prove
   r"!g:A->A->bool x x0 y y0.
        dorder g
        ==> (x --> x0)(mtop(mr1),g) /\
            (y --> y0)(mtop(mr1),g) /\
            (?N. g N N /\ !n. g n N ==> x(n) <= y(n))
            ==> x0 <= y0"
   (← do
    let xy2 ← q r"(x0 - y0) / &2"
    pure (REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
      GEN_REWRITE_TAC id [← TAUT (← q r"a <=> ~ ~a")] THEN
      PURE_ONCE_REWRITE_TAC [REAL_NOT_LE] THEN
      ONCE_REWRITE_TAC [← GSYM REAL_SUB_LT] THEN DISCH_TAC THEN
      FIRST_ASSUM (undischCheck (fun c => pure (is_conj c))) THEN
      REWRITE_TAC [CONJ_ASSOC] THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      REWRITE_TAC [MTOP_TENDS] THEN
      DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← specConj xy2 th))) THEN
      ASM_REWRITE_TAC [REAL_LT_HALF1] THEN
      DISCH_THEN (DORDER_THEN MP_TAC) THEN
      FIRST_ASSUM (undischCheck (fun c => pure (is_exists c))) THEN
      DISCH_THEN (fun th1 => DISCH_THEN (fun th2 => tactic_of do
        pure (MP_TAC (← CONJ th1 th2)))) THEN
      DISCH_THEN (DORDER_THEN MP_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "N:A") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      BETA_TAC THEN DISCH_THEN (MP_TAC o SPEC (← q "N:A")) THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [MR1_DEF] THEN ONCE_REWRITE_TAC [ABS_SUB] THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      REWRITE_TAC [REAL_NOT_LE] THEN MATCH_MP_TAC ABS_BETWEEN2 THEN
      MAP_EVERY EXISTS_TAC [← q "y0:real", ← q "x0:real"] THEN
      ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [← GSYM REAL_SUB_LT] THEN
      FIRST_ASSUM ACCEPT_TAC))

  -- @@RETURN BEGIN
  return { NET_NULL_ADD, NET_NULL_MUL, NET_NULL_CMUL, NET_ADD, NET_NEG, NET_SUB, NET_MUL,
           NET_INV, NET_DIV, NET_ABS, NET_SUM, NET_LE }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Theory of sequences: net theorems specialized to sequences, convergence,  -/
/- Cauchy-ness, subsequences, monotonicity, bounded sequences.               -/
/- (analysis.ml 3215-3497)                                                   -/
/- ------------------------------------------------------------------------- -/

structure Seqs where
  -- @@FIELDS
  tends_num_real : thm
  SEQ : thm
  SEQ_CONST : thm
  SEQ_ADD : thm
  SEQ_MUL : thm
  SEQ_NEG : thm
  SEQ_INV : thm
  SEQ_SUB : thm
  SEQ_DIV : thm
  SEQ_UNIQ : thm
  SEQ_NULL : thm
  SEQ_SUM : thm
  SEQ_TRANSFORM : thm
  convergent : thm
  cauchy : thm
  lim : thm
  SEQ_LIM : thm
  subseq : thm
  SUBSEQ_SUC : thm
  mono : thm
  MONO_SUC : thm
  MAX_LEMMA : thm
  SEQ_BOUNDED : thm
  SEQ_BOUNDED_2 : thm
  SEQ_CBOUNDED : thm
  SEQ_ICONV : thm
  deriving Inhabited

@[nospecialize]
def setupSeqs [HolBase] (D : AnalysisDeps) (BCompat : Compat) (BNames : Names) (BReals1 : Reals1) (BReals2 : Reals2) (BReals3 : Reals3) (BAbs : Abs) (BPow : Pow) (BMetricTop : MetricTop) (BNets : Nets) (BNetArith : NetArith) :
    ExceptT String IO Seqs := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, INDUCT_TAC, MESON_TAC, new_definition, override_interface,
        parse_as_infix, .. } := D
  let { ADD1, ADD_CLAUSES, CONJ_SYM, GE, LE_REFL, LT, LTE_CASES, LT_TRANS,
        REAL_ADD_RINV, REAL_ADD_SYM, .. } := D.core1
  let { REAL_LET_TOTAL, REAL_LET_TRANS, REAL_LE_ADDL, REAL_LE_ADDR, REAL_LT_ADDR,
        REAL_LT_REFL, .. } := D.core2
  let { RIGHT_IMP_FORALL_THM, real_abs, real_ge, real_sub, .. } := D.core3
  let { LEFT_IMP_EXISTS_CONV, NOT_EXISTS_CONV, .. } := BCompat
  let { LESS_ADD_1, LESS_EQUAL_ADD, LESS_EQ_SUC_REFL, LESS_SUC_REFL, NOT_LESS_0, .. } := BNames
  let { REAL_LE_RADD, REAL_LE_REFL, REAL_LE_TOTAL, REAL_LE_TRANS, REAL_LTE_TRANS,
        REAL_LT_01, REAL_LT_ADD1, REAL_LT_IMP_LE, REAL_NOT_LT, .. } := BReals1
  let { REAL_NEG_SUB, REAL_SUB_REFL, .. } := BReals2
  let { REAL_LE_NEG2, REAL_LT_SUB_RADD, .. } := BReals3
  let { ABS_0, ABS_LE, ABS_POS, ABS_SUB, .. } := BAbs
  let { REAL_SUP, .. } := BPow
  let { MR1_DEF, .. } := BMetricTop
  let { DORDER_NGE, MR1_BOUNDED, MTOP_TENDS_UNIQ, NET_NULL, SEQ_TENDS, bounded, .. } := BNets
  let { NET_ADD, NET_DIV, NET_INV, NET_MUL, NET_NEG, NET_SUB, NET_SUM, .. } := BNetArith
  -- @@SCOPE END
  parse_as_infix ("tends_num_real", (12, "right"))

  parse_as_infix ("sums", (12, "right"))

  let tends_num_real ← new_definition
   r"x tends_num_real x0 <=> (x tends x0)(mtop(mr1), (>=) :num->num->bool)"

  override_interface "-->" (← q "(tends_num_real)")

  let SEQ ← prove
   r"!x x0. (x --> x0) <=>
          !e. &0 < e ==> ?N. !n. n >= N ==> abs(x(n) - x0) < e"
   (REPEAT GEN_TAC THEN REWRITE_TAC [tends_num_real, SEQ_TENDS, MR1_DEF] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ABS_SUB] THEN
    REFL_TAC)

  let SEQ_CONST ← prove
   r"!k. (\x. k) --> k"
   (REPEAT GEN_TAC THEN REWRITE_TAC [SEQ, REAL_SUB_REFL, ABS_0] THEN
    GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [])

  let SEQ_ADD ← prove
   r"!x x0 y y0. x --> x0 /\ y --> y0 ==> (\n. x(n) + y(n)) --> (x0 + y0)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [tends_num_real] THEN
    MATCH_MP_TAC NET_ADD THEN
    MATCH_ACCEPT_TAC DORDER_NGE)

  let SEQ_MUL ← prove
   r"!x x0 y y0. x --> x0 /\ y --> y0 ==> (\n. x(n) * y(n)) --> (x0 * y0)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [tends_num_real] THEN
    MATCH_MP_TAC NET_MUL THEN
    MATCH_ACCEPT_TAC DORDER_NGE)

  let SEQ_NEG ← prove
   r"!x x0. x --> x0 <=> (\n. --(x n)) --> --x0"
   (REPEAT GEN_TAC THEN REWRITE_TAC [tends_num_real] THEN
    MATCH_MP_TAC NET_NEG THEN
    MATCH_ACCEPT_TAC DORDER_NGE)

  let SEQ_INV ← prove
   r"!x x0. x --> x0 /\ ~(x0 = &0) ==> (\n. inv(x n)) --> inv x0"
   (REPEAT GEN_TAC THEN REWRITE_TAC [tends_num_real] THEN
    MATCH_MP_TAC NET_INV THEN
    MATCH_ACCEPT_TAC DORDER_NGE)

  let SEQ_SUB ← prove
   r"!x x0 y y0. x --> x0 /\ y --> y0 ==> (\n. x(n) - y(n)) --> (x0 - y0)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [tends_num_real] THEN
    MATCH_MP_TAC NET_SUB THEN
    MATCH_ACCEPT_TAC DORDER_NGE)

  let SEQ_DIV ← prove
   r"!x x0 y y0. x --> x0 /\ y --> y0 /\ ~(y0 = &0) ==>
                  (\n. x(n) / y(n)) --> (x0 / y0)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [tends_num_real] THEN
    MATCH_MP_TAC NET_DIV THEN
    MATCH_ACCEPT_TAC DORDER_NGE)

  let SEQ_UNIQ ← prove
   r"!x x1 x2. x --> x1 /\ x --> x2 ==> (x1 = x2)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [tends_num_real] THEN
    MATCH_MP_TAC MTOP_TENDS_UNIQ THEN
    MATCH_ACCEPT_TAC DORDER_NGE)

  let SEQ_NULL ← prove
   r"!s l. s --> l <=> (\n. s(n) - l) --> &0"
   (REPEAT GEN_TAC THEN REWRITE_TAC [tends_num_real] THEN
    MATCH_ACCEPT_TAC NET_NULL)

  let SEQ_SUM ← prove
   r"!f l m n.
      (!r. m <= r /\ r < m + n ==> f r --> l r)
      ==> (\k. sum(m,n) (\r. f r k)) --> sum(m,n) l"
   (REPEAT GEN_TAC THEN REWRITE_TAC [tends_num_real] THEN
    MATCH_MP_TAC (← REWRITE_RULE [RIGHT_IMP_FORALL_THM] NET_SUM) THEN
    REWRITE_TAC [SEQ_CONST, DORDER_NGE, ← GSYM tends_num_real])

  let SEQ_TRANSFORM ← prove
   r"!s t l N. (!n. N <= n ==> (s n = t n)) /\ s --> l ==> t --> l"
   (REWRITE_TAC [SEQ, GE] THEN
    MESON_TAC [← ARITH_RULE (← q r"M + N <= n:num ==> M <= n /\ N <= n")])

  let convergent ← new_definition
   r"convergent f <=> ?l. f --> l"

  let cauchy ← new_definition
   r"cauchy f <=> !e. &0 < e ==>
        ?N:num. !m n. m >= N /\ n >= N ==> abs(f(m) - f(n)) < e"

  let lim ← new_definition
   r"lim f = @l. f --> l"

  let SEQ_LIM ← prove
   r"!f. convergent f <=> (f --> lim f)"
   (GEN_TAC THEN REWRITE_TAC [convergent] THEN EQ_TAC THENL
     [DISCH_THEN (MP_TAC o SELECT_RULE) THEN REWRITE_TAC [lim],
      DISCH_TAC THEN EXISTS_TAC (← q "lim f") THEN POP_ASSUM ACCEPT_TAC])

  let subseq ← new_definition
   r"subseq (f:num->num) <=> !m n. m < n ==> (f m) < (f n)"

  let SUBSEQ_SUC ← prove
   r"!f. subseq f <=> !n. f(n) < f(SUC n)"
   (GEN_TAC THEN REWRITE_TAC [subseq] THEN EQ_TAC THEN DISCH_TAC THENL
     [X_GEN_TAC (← q "n:num") THEN POP_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC [LESS_SUC_REFL],
      REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP LESS_ADD_1) THEN
      REWRITE_TAC [← GSYM ADD1] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "p:num") SUBST1_TAC) THEN
      SPEC_TAC (← q "p:num", ← q "p:num") THEN INDUCT_TAC THENL
       [ALL_TAC,
        MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC (← q r"f(m + (SUC p)):num")] THEN
      ASM_REWRITE_TAC [ADD_CLAUSES]])

  let mono ← new_definition
   r"mono (f:num->real) <=>
            (!m n. m <= n ==> f(m) <= f(n)) \/
            (!m n. m <= n ==> f(m) >= f(n))"

  let MONO_SUC ← prove
   r"!f. mono f <=> (!n. f(SUC n) >= f(n)) \/ (!n. f(SUC n) <= f(n))"
   (← do
    let nN ← q "n:num"
    let sN ← q "SUC n"
    pure (GEN_TAC THEN REWRITE_TAC [mono, real_ge] THEN
      MATCH_MP_TAC (← TAUT (← q r"(a <=> c) /\ (b <=> d) ==> (a \/ b <=> c \/ d)")) THEN
      CONJ_TAC THEN (EQ_TAC THENL
        [DISCH_THEN (MP_TAC o GEN nN o SPECL [nN, sN]) THEN
         REWRITE_TAC [LESS_EQ_SUC_REFL],
         DISCH_TAC THEN REPEAT GEN_TAC THEN
         DISCH_THEN (X_CHOOSE_THEN (← q "p:num") SUBST1_TAC o MATCH_MP LESS_EQUAL_ADD) THEN
         SPEC_TAC (← q "p:num", ← q "p:num") THEN INDUCT_TAC THEN
         ASM_REWRITE_TAC [ADD_CLAUSES, REAL_LE_REFL] THEN
         MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"f(m + p:num):real") THEN
         ASM_REWRITE_TAC []])))

  let MAX_LEMMA ← prove
   r"!s N. ?k. !n:num. n < N ==> abs(s n) < k"
   (GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [NOT_LESS_0] THEN
    POP_ASSUM (X_CHOOSE_TAC (← q "k:real")) THEN
    DISJ_CASES_TAC (← SPECL [← q "k:real", ← q r"abs(s(N:num))"] REAL_LET_TOTAL) THENL
     [EXISTS_TAC (← q r"abs(s(N:num)) + &1"), EXISTS_TAC (← q "k:real")] THEN
    X_GEN_TAC (← q "n:num") THEN REWRITE_TAC [← CONJUNCT2 LT] THEN
    DISCH_THEN (DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THEN
    TRY (MATCH_MP_TAC REAL_LT_ADD1) THEN ASM_REWRITE_TAC [REAL_LE_REFL] THEN
    DISCH_THEN (ANTE_RES_THEN ASSUME_TAC) THEN
    MATCH_MP_TAC REAL_LT_ADD1 THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "k:real") THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    ASM_REWRITE_TAC [])

  let SEQ_BOUNDED ← prove
   r"!s. bounded(mr1, (>=)) s <=> ?k. !n:num. abs(s n) < k"
   (GEN_TAC THEN REWRITE_TAC [MR1_BOUNDED] THEN
    REWRITE_TAC [GE, LE_REFL] THEN EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_THEN (← q "k:real") (X_CHOOSE_TAC (← q "N:num"))) THEN
      MP_TAC (← SPECL [← q r"s:num->real", ← q "N:num"] MAX_LEMMA) THEN
      DISCH_THEN (X_CHOOSE_TAC (← q "l:real")) THEN
      DISJ_CASES_TAC (← SPECL [← q "k:real", ← q "l:real"] REAL_LE_TOTAL) THENL
       [EXISTS_TAC (← q "l:real"), EXISTS_TAC (← q "k:real")] THEN
      X_GEN_TAC (← q "n:num") THEN MP_TAC (← SPECL [← q "n:num", ← q "N:num"] LTE_CASES) THEN
      DISCH_THEN (DISJ_CASES_THEN (ANTE_RES_THEN ASSUME_TAC)) THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
      FIRST_ASSUM (fun th => tactic_of do
        let r ← liftExcept (rand (concl th))
        pure (EXISTS_TAC r THEN ASM_REWRITE_TAC [] THEN NO_TAC)),
      DISCH_THEN (X_CHOOSE_TAC (← q "k:real")) THEN
      MAP_EVERY EXISTS_TAC [← q "k:real", ← q "0"] THEN
      GEN_TAC THEN ASM_REWRITE_TAC []])

  let SEQ_BOUNDED_2 ← prove
   r"!f k K. (!n:num. k <= f(n) /\ f(n) <= K) ==> bounded(mr1, (>=)) f"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [SEQ_BOUNDED] THEN
    EXISTS_TAC (← q r"(abs(k) + abs(K)) + &1") THEN GEN_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q r"abs(k) + abs(K)") THEN
    REWRITE_TAC [REAL_LT_ADDR, REAL_LT_01] THEN
    GEN_REWRITE_TAC LAND_CONV [real_abs] THEN COND_CASES_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "abs(K)") THEN
      REWRITE_TAC [REAL_LE_ADDL, ABS_POS] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "K:real") THEN
      ASM_REWRITE_TAC [ABS_LE],
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "abs(k)") THEN
      REWRITE_TAC [REAL_LE_ADDR, ABS_POS] THEN
      REWRITE_TAC [real_abs] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_LE_NEG2] THEN
      SUBGOAL_THEN (← q r"&0 <= f(n:num)") MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC (← q "k:real") THEN ASM_REWRITE_TAC [],
        ASM_REWRITE_TAC []]])

  let SEQ_CBOUNDED ← prove
   r"!f. cauchy f ==> bounded(mr1, (>=)) f"
   (GEN_TAC THEN REWRITE_TAC [bounded, cauchy] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"&1")) THEN REWRITE_TAC [REAL_LT_01] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q "N:num")) THEN
    MAP_EVERY EXISTS_TAC [← q r"&1", ← q r"(f:num->real) N", ← q "N:num"] THEN
    REWRITE_TAC [GE, LE_REFL] THEN
    POP_ASSUM (MP_TAC o SPEC (← q "N:num")) THEN
    REWRITE_TAC [GE, LE_REFL, MR1_DEF])

  let SEQ_ICONV ← prove
   r"!f. bounded(mr1, (>=)) f /\ (!m n. m >= n ==> f(m) >= f(n))
           ==> convergent f"
   (← do
    let supE ← q r"sup(\x. ?n:num. x = f(n)) - e"
    let nN ← q "n:num"
    let fn ← q r"(f:num->real) n"
    pure (GEN_TAC THEN DISCH_TAC THEN
      MP_TAC (← SPEC (← q r"\x:real. ?n:num. x = f(n)") REAL_SUP) THEN BETA_TAC THEN
      (fun gl => ExceptT.run do
        let t ← liftExcept (funpow 2 (fun (m : Except String term) => do
          pure (← dest_imp (← m)).1) (pure gl.2))
        ExceptT.mk (SUBGOAL_THEN t MP_TAC gl)) THENL
       [CONJ_TAC THENL
         [MAP_EVERY EXISTS_TAC [← q r"f(0):real", ← q "0"] THEN REFL_TAC,
          POP_ASSUM (MP_TAC o REWRITE_RULE [SEQ_BOUNDED] o CONJUNCT1) THEN
          DISCH_THEN (X_CHOOSE_TAC (← q "k:real")) THEN EXISTS_TAC (← q "k:real") THEN
          GEN_TAC THEN DISCH_THEN (X_CHOOSE_THEN (← q "n:num") SUBST1_TAC) THEN
          MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q r"abs(f(n:num))") THEN
          ASM_REWRITE_TAC [ABS_LE]], ALL_TAC] THEN
      DISCH_THEN (fun th => REWRITE_TAC [th]) THEN DISCH_TAC THEN
      REWRITE_TAC [convergent] THEN EXISTS_TAC (← q r"sup(\x. ?n:num. x = f(n))") THEN
      REWRITE_TAC [SEQ] THEN X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN
      FIRST_ASSUM (fun th => tactic_of do
        pure (MP_TAC (← liftExcept (check (fun t => is_forall (concl t)) th)))) THEN
      DISCH_THEN (MP_TAC o SPEC supE) THEN
      REWRITE_TAC [REAL_LT_SUB_RADD, REAL_LT_ADDR] THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "x:real") MP_TAC) THEN
      ONCE_REWRITE_TAC [CONJ_SYM] THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_THEN (← q "n:num") SUBST1_TAC)) THEN
      ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN REWRITE_TAC [← GSYM REAL_LT_SUB_RADD] THEN
      DISCH_TAC THEN SUBGOAL_THEN (← q r"!n. f(n) <= sup(\x. ?n:num. x = f(n))")
      ASSUME_TAC THENL
       [FIRST_ASSUM (MP_TAC o SPEC (← q r"sup(\x. ?n:num. x = f(n))")) THEN
        REWRITE_TAC [REAL_LT_REFL] THEN
        CONV_TAC (ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
        REWRITE_TAC [← TAUT (← q r"~(a /\ b) <=> a ==> ~b")] THEN
        REWRITE_TAC [REAL_NOT_LT] THEN
        CONV_TAC (ONCE_DEPTH_CONV LEFT_IMP_EXISTS_CONV) THEN
        DISCH_THEN (MP_TAC o GEN nN o SPECL [fn, nN]) THEN
        REWRITE_TAC [], ALL_TAC] THEN
      EXISTS_TAC (← q "n:num") THEN X_GEN_TAC (← q "m:num") THEN
      FIRST_ASSUM (undischCheck (fun c => pure (is_conj c))) THEN
      DISCH_THEN (ASSUME_TAC o CONJUNCT2) THEN
      DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN
      RULE_ASSUM_TAC (REWRITE_RULE [REAL_LT_SUB_RADD]) THEN
      RULE_ASSUM_TAC (ONCE_REWRITE_RULE [REAL_ADD_SYM]) THEN
      RULE_ASSUM_TAC (REWRITE_RULE [← GSYM REAL_LT_SUB_RADD]) THEN
      REWRITE_TAC [real_ge] THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"(sup(\x. ?m:num. x = f(m)) - e) < f(m)") ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q r"(f:num->real) n") THEN
        ASM_REWRITE_TAC [], ALL_TAC] THEN
      REWRITE_TAC [real_abs] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC [REAL_NEG_SUB] THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q r"&0") THEN
        ASM_REWRITE_TAC [] THEN REWRITE_TAC [real_sub] THEN
        SUBST1_TAC (← REWRITE_RULE [REAL_ADD_RINV] (← SPECL
          [← q r"(f:num->real) m", ← q r"(sup(\x. ?n:num. x = f(n)))",
           ← q r"--(sup(\x. ?n:num. x = f(n)))"] REAL_LE_RADD)) THEN
        ASM_REWRITE_TAC [],
        REWRITE_TAC [REAL_LT_SUB_RADD] THEN ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
        REWRITE_TAC [← GSYM REAL_LT_SUB_RADD] THEN ASM_REWRITE_TAC []]))

  -- @@RETURN BEGIN
  return { tends_num_real, SEQ, SEQ_CONST, SEQ_ADD, SEQ_MUL, SEQ_NEG, SEQ_INV, SEQ_SUB,
           SEQ_DIV, SEQ_UNIQ, SEQ_NULL, SEQ_SUM, SEQ_TRANSFORM, convergent, cauchy, lim,
           SEQ_LIM, subseq, SUBSEQ_SUC, mono, MONO_SUC, MAX_LEMMA, SEQ_BOUNDED,
           SEQ_BOUNDED_2, SEQ_CBOUNDED, SEQ_ICONV }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Bounded monotonic sequences converge; monotonic subsequences; Cauchy      -/
/- sequences converge; limit comparison.  (analysis.ml 3499-3718)            -/
/- ------------------------------------------------------------------------- -/

structure Seqs2 where
  -- @@FIELDS
  SEQ_NEG_CONV : thm
  SEQ_NEG_BOUNDED : thm
  SEQ_BCONV : thm
  SEQ_MONOSUB : thm
  SEQ_SBOUNDED : thm
  SEQ_SUBLE : thm
  SEQ_DIRECT : thm
  SEQ_CAUCHY : thm
  SEQ_LE : thm
  SEQ_LE_0 : thm
  deriving Inhabited

@[nospecialize]
def setupSeqs2 [HolBase] (D : AnalysisDeps) (BCompat : Compat) (BNames : Names) (BReals1 : Reals1) (BReals2 : Reals2) (BReals3 : Reals3) (BAbs : Abs) (BNets : Nets) (BNetArith : NetArith) (BSeqs : Seqs) :
    ExceptT String IO Seqs2 := do
  -- @@SCOPE BEGIN
  let { INDUCT_TAC, MESON_TAC, .. } := D
  let { GE, GT, LE_CASES, LE_LT, LE_REFL, LE_SUC, LE_SUC_LT, LE_TRANS, LT_IMP_LE,
        NOT_IMP, NOT_LT, .. } := D.core1
  let { REAL_LET_TRANS, REAL_LT_REFL, .. } := D.core2
  let { RIGHT_FORALL_IMP_THM, num_Axiom, num_CASES, real_ge, .. } := D.core3
  let { NOT_EXISTS_CONV, NOT_FORALL_CONV, RIGHT_AND_OVER_OR, .. } := BCompat
  let { NOT_LESS_0, .. } := BNames
  let { REAL_LT_ADD2, REAL_LT_IMP_LE, REAL_NEG_NEG, REAL_NOT_LE, .. } := BReals1
  let { REAL_LT_HALF1, .. } := BReals2
  let { REAL_HALF_DOUBLE, REAL_LE_NEG2, REAL_SUB_RZERO, REAL_SUB_TRIANGLE, .. } := BReals3
  let { ABS_NEG, ABS_SUB, ABS_TRIANGLE, .. } := BAbs
  let { DORDER_NGE, .. } := BNets
  let { NET_LE, .. } := BNetArith
  let { MONO_SUC, SEQ, SEQ_BOUNDED, SEQ_CBOUNDED, SEQ_ICONV, SEQ_NEG, SUBSEQ_SUC,
        cauchy, convergent, mono, tends_num_real, .. } := BSeqs
  -- @@SCOPE END
  let SEQ_NEG_CONV ← prove
   r"!f. convergent f <=> convergent (\n. --(f n))"
   (GEN_TAC THEN REWRITE_TAC [convergent] THEN EQ_TAC THEN
    DISCH_THEN (X_CHOOSE_TAC (← q "l:real")) THEN
    EXISTS_TAC (← q "--l") THEN POP_ASSUM MP_TAC THEN
    SUBST1_TAC (← SYM (← SPEC (← q "l:real") REAL_NEG_NEG)) THEN
    REWRITE_TAC [← GSYM SEQ_NEG] THEN REWRITE_TAC [REAL_NEG_NEG])

  let SEQ_NEG_BOUNDED ← prove
   r"!f. bounded(mr1, (>=))(\n:num. --(f n)) <=> bounded(mr1, (>=)) f"
   (GEN_TAC THEN REWRITE_TAC [SEQ_BOUNDED] THEN BETA_TAC THEN
    REWRITE_TAC [ABS_NEG])

  let SEQ_BCONV ← prove
   r"!f. bounded(mr1, (>=)) f /\ mono f ==> convergent f"
   (GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC [mono] THEN DISCH_THEN DISJ_CASES_TAC THENL
     [MATCH_MP_TAC SEQ_ICONV THEN ASM_REWRITE_TAC [GE, real_ge],
      ONCE_REWRITE_TAC [SEQ_NEG_CONV] THEN MATCH_MP_TAC SEQ_ICONV THEN
      ASM_REWRITE_TAC [SEQ_NEG_BOUNDED] THEN BETA_TAC THEN
      REWRITE_TAC [GE, real_ge, REAL_LE_NEG2] THEN
      ONCE_REWRITE_TAC [← GSYM real_ge] THEN ASM_REWRITE_TAC []])

  let SEQ_MONOSUB ← prove
   r"!s:num->real. ?f. subseq f /\ mono(\n.s(f n))"
   (← do
    let nN ← q "n:num"
    let qN ← q "q:num"
    pure (GEN_TAC THEN
      ASM_CASES_TAC (← q r"!n:num. ?p. p > n /\ !m. m >= p ==> s(m) <= s(p)") THENL
       [X_CHOOSE_THEN (← q r"f:num->num") MP_TAC (← EXISTENCE (← ISPECL
         [← q r"@p. p > 0 /\ (!m. m >= p ==> (s m) <= (s p))",
          ← q r"\x. \n:num. @p:num. p > x /\
                         (!m. m >= p ==> (s m) <= (s p))"] num_Axiom)) THEN
        BETA_TAC THEN RULE_ASSUM_TAC (GEN nN o SELECT_RULE o SPEC nN) THEN
        (← do
          let z ← q "0"
          let fn ← q r"(f:num->num) n"
          pure (POP_ASSUM (fun th => tactic_of do
            pure (DISCH_THEN (ASSUME_TAC o GSYM) THEN
              MP_TAC (← SPEC z th) THEN
              MP_TAC (← GEN nN (← SPEC fn th)))))) THEN
        ASM_REWRITE_TAC [] THEN POP_ASSUM (fun _ => ALL_TAC) THEN REPEAT STRIP_TAC THEN
        EXISTS_TAC (← q r"f:num->num") THEN ASM_REWRITE_TAC [SUBSEQ_SUC, ← GSYM GT] THEN
        SUBGOAL_THEN (← q r"!p q. p:num >= (f q) ==> s(p) <= s(f(q:num))") MP_TAC THENL
         [REPEAT GEN_TAC THEN STRUCT_CASES_TAC (← SPEC qN num_CASES) THEN
          ASM_REWRITE_TAC [], ALL_TAC] THEN
        DISCH_THEN (MP_TAC o GEN qN o SPECL [← q r"f(SUC q):num", qN]) THEN
        SUBGOAL_THEN (← q r"!q. f(SUC q):num >= f(q)") (fun th => REWRITE_TAC [th]) THENL
         [GEN_TAC THEN REWRITE_TAC [GE] THEN
          MATCH_MP_TAC LT_IMP_LE
          THEN ASM_REWRITE_TAC [← GSYM GT], ALL_TAC] THEN
        DISCH_TAC THEN REWRITE_TAC [MONO_SUC] THEN DISJ2_TAC THEN
        BETA_TAC THEN ASM_REWRITE_TAC [],
        POP_ASSUM (X_CHOOSE_TAC (← q "N:num") o CONV_RULE NOT_FORALL_CONV) THEN
        POP_ASSUM (MP_TAC o CONV_RULE NOT_EXISTS_CONV) THEN
        REWRITE_TAC [← TAUT (← q r"~(a /\ b) <=> a ==> ~b")] THEN
        CONV_TAC (ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
        REWRITE_TAC [NOT_IMP, REAL_NOT_LE] THEN DISCH_TAC THEN
        SUBGOAL_THEN (← q r"!p. p >= SUC N ==> (?m. m > p /\ s(p) < s(m))")
        MP_TAC THENL
         [GEN_TAC THEN REWRITE_TAC [GE, LE_SUC_LT] THEN
          REWRITE_TAC [← GSYM GT] THEN DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN
          REWRITE_TAC [GE, LE_LT, RIGHT_AND_OVER_OR, GT] THEN
          DISCH_THEN (X_CHOOSE_THEN (← q "m:num") DISJ_CASES_TAC) THENL
           [EXISTS_TAC (← q "m:num") THEN ASM_REWRITE_TAC [],
            FIRST_ASSUM (undischCheck (fun c => pure (is_conj c))) THEN
            DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
            ASM_REWRITE_TAC [REAL_LT_REFL]], ALL_TAC] THEN
        POP_ASSUM (fun _ => ALL_TAC) THEN DISCH_TAC THEN
        X_CHOOSE_THEN (← q r"f:num->num") MP_TAC (← EXISTENCE (← ISPECL
         [← q r"@m. m > (SUC N) /\ s(SUC N) < s(m)",
          ← q r"\x. \n:num. @m:num. m > x /\ s(x) < s(m)"] num_Axiom)) THEN
        BETA_TAC THEN DISCH_THEN ASSUME_TAC THEN SUBGOAL_THEN
          (← q r"!n. f(n) >= (SUC N) /\
             f(SUC n) > f(n) /\ s(f n) < s(f(SUC n):num)") MP_TAC THENL
         [INDUCT_TAC THENL
           [SUBGOAL_THEN (← q r"f(0) >= (SUC N)") MP_TAC THENL
             [FIRST_ASSUM (MP_TAC o SPEC (← q "SUC N")) THEN
              REWRITE_TAC [GE, LE_REFL] THEN
              DISCH_THEN (MP_TAC o SELECT_RULE) THEN ASM_REWRITE_TAC [] THEN
              DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN
              MATCH_MP_TAC LT_IMP_LE THEN
              ASM_REWRITE_TAC [← GSYM GT], ALL_TAC] THEN
            DISCH_THEN (fun th => ASSUME_TAC th THEN REWRITE_TAC [th]) THEN
            FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← CONJUNCT2 th])) THEN
            CONV_TAC SELECT_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN
            FIRST_ASSUM ACCEPT_TAC,
            FIRST_ASSUM (undischCheck (fun c => pure ((conjuncts c).length == 3))) THEN
            DISCH_THEN STRIP_ASSUME_TAC THEN CONJ_TAC THENL
             [REWRITE_TAC [GE] THEN MATCH_MP_TAC LE_TRANS THEN
              EXISTS_TAC (← q r"(f:num->num) n") THEN REWRITE_TAC [← GSYM GE] THEN
              CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
              REWRITE_TAC [GE] THEN MATCH_MP_TAC LT_IMP_LE THEN
              REWRITE_TAC [← GSYM GT] THEN FIRST_ASSUM ACCEPT_TAC,
              FIRST_ASSUM (SUBST1_TAC o SPEC (← q "SUC n") o CONJUNCT2) THEN
              CONV_TAC SELECT_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN
              REWRITE_TAC [GE] THEN MATCH_MP_TAC LE_TRANS THEN
              EXISTS_TAC (← q r"(f:num->num) n") THEN
              REWRITE_TAC [← GSYM GE] THEN CONJ_TAC THEN
              TRY (FIRST_ASSUM ACCEPT_TAC) THEN
              REWRITE_TAC [GE] THEN MATCH_MP_TAC LT_IMP_LE THEN
              REWRITE_TAC [← GSYM GT] THEN
              FIRST_ASSUM ACCEPT_TAC]], ALL_TAC] THEN
        POP_ASSUM_LIST (fun _ => ALL_TAC) THEN DISCH_TAC THEN
        EXISTS_TAC (← q r"f:num->num") THEN REWRITE_TAC [SUBSEQ_SUC, MONO_SUC] THEN
        ASM_REWRITE_TAC [← GSYM GT] THEN DISJ1_TAC THEN BETA_TAC THEN
        GEN_TAC THEN REWRITE_TAC [real_ge] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC []]))

  let SEQ_SBOUNDED ← prove
   r"!s (f:num->num). bounded(mr1, (>=)) s ==> bounded(mr1, (>=)) (\n. s(f n))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [SEQ_BOUNDED] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q "k:real")) THEN EXISTS_TAC (← q "k:real") THEN
    GEN_TAC THEN BETA_TAC THEN ASM_REWRITE_TAC [])

  let SEQ_SUBLE ← prove
   r"!f n. subseq f ==> n <= f(n)"
   (GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    DISCH_TAC THEN INDUCT_TAC THENL
     [REWRITE_TAC [← GSYM NOT_LT, NOT_LESS_0],
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"SUC(f(n:num))") THEN
      ASM_REWRITE_TAC [LE_SUC] THEN
      REWRITE_TAC [LE_SUC_LT] THEN
      UNDISCH_TAC (← q "subseq f") THEN REWRITE_TAC [SUBSEQ_SUC] THEN
      DISCH_THEN MATCH_ACCEPT_TAC])

  let SEQ_DIRECT ← prove
   r"!f. subseq f ==> !N1 N2. ?n. n >= N1 /\ f(n) >= N2"
   (GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    DISJ_CASES_TAC (← SPECL [← q "N1:num", ← q "N2:num"] LE_CASES) THENL
     [EXISTS_TAC (← q "N2:num") THEN ASM_REWRITE_TAC [GE] THEN
      MATCH_MP_TAC SEQ_SUBLE THEN
      FIRST_ASSUM ACCEPT_TAC,
      EXISTS_TAC (← q "N1:num") THEN REWRITE_TAC [GE, LE_REFL] THEN
      REWRITE_TAC [GE] THEN MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC (← q "N1:num") THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC SEQ_SUBLE THEN
      FIRST_ASSUM ACCEPT_TAC])

  let SEQ_CAUCHY ← prove
   r"!f. cauchy f <=> convergent f"
   (GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o MATCH_MP SEQ_CBOUNDED) THEN
      MP_TAC (← SPEC (← q r"f:num->real") SEQ_MONOSUB) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"g:num->num") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN (← q r"bounded(mr1, (>=) :num->num->bool)(\n. f(g(n):num))")
      ASSUME_TAC THENL
       [MATCH_MP_TAC SEQ_SBOUNDED THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"convergent (\n. f(g(n):num))") MP_TAC THENL
       [MATCH_MP_TAC SEQ_BCONV THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
      REWRITE_TAC [convergent] THEN DISCH_THEN (X_CHOOSE_TAC (← q "l:real")) THEN
      EXISTS_TAC (← q "l:real") THEN REWRITE_TAC [SEQ] THEN
      X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN
      UNDISCH_TAC (← q r"(\n. f(g(n):num)) --> l") THEN REWRITE_TAC [SEQ] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"e / &2")) THEN ASM_REWRITE_TAC [REAL_LT_HALF1] THEN
      BETA_TAC THEN DISCH_THEN (X_CHOOSE_TAC (← q "N1:num")) THEN
      UNDISCH_TAC (← q "cauchy f") THEN REWRITE_TAC [cauchy] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"e / &2")) THEN ASM_REWRITE_TAC [REAL_LT_HALF1] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "N2:num") ASSUME_TAC) THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP SEQ_DIRECT) THEN
      DISCH_THEN (MP_TAC o SPECL [← q "N1:num", ← q "N2:num"]) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "n:num") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q "N2:num") THEN X_GEN_TAC (← q "m:num") THEN DISCH_TAC THEN
      UNDISCH_TAC (← q r"!n:num. n >= N1 ==> abs(f(g n:num) - l) < (e / &2)") THEN
      DISCH_THEN (MP_TAC o SPEC (← q "n:num")) THEN ASM_REWRITE_TAC [] THEN
      DISCH_TAC THEN FIRST_ASSUM (undischCheck (fun c => pure (is_forall c))) THEN
      DISCH_THEN (MP_TAC o SPECL [← q r"g(n:num):num", ← q "m:num"]) THEN
      ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      SUBGOAL_THEN (← q r"f(m:num) - l = (f(m) - f(g(n:num))) + (f(g n) - l)")
      SUBST1_TAC THENL [REWRITE_TAC [REAL_SUB_TRIANGLE], ALL_TAC] THEN
      EXISTS_TAC (← q r"abs(f(m:num) - f(g(n:num))) + abs(f(g n) - l)") THEN
      REWRITE_TAC [ABS_TRIANGLE] THEN
      SUBST1_TAC (← SYM (← SPEC (← q "e:real") REAL_HALF_DOUBLE)) THEN
      MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC [] THEN
      ONCE_REWRITE_TAC [ABS_SUB] THEN ASM_REWRITE_TAC [],

      REWRITE_TAC [convergent] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "l:real") MP_TAC) THEN
      REWRITE_TAC [SEQ, cauchy] THEN DISCH_TAC THEN
      X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN
      FIRST_ASSUM (undischCheck (fun c => pure (is_forall c))) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"e / &2")) THEN
      ASM_REWRITE_TAC [REAL_LT_HALF1] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q "N:num")) THEN
      EXISTS_TAC (← q "N:num") THEN REPEAT GEN_TAC THEN
      DISCH_THEN (CONJUNCTS_THEN (ANTE_RES_THEN ASSUME_TAC)) THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      SUBGOAL_THEN (← q r"f(m:num) - f(n) = (f(m) - l) + (l - f(n))")
      SUBST1_TAC THENL [REWRITE_TAC [REAL_SUB_TRIANGLE], ALL_TAC] THEN
      EXISTS_TAC (← q r"abs(f(m:num) - l) + abs(l - f(n))") THEN
      REWRITE_TAC [ABS_TRIANGLE] THEN
      SUBST1_TAC (← SYM (← SPEC (← q "e:real") REAL_HALF_DOUBLE)) THEN
      MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC [] THEN
      ONCE_REWRITE_TAC [ABS_SUB] THEN ASM_REWRITE_TAC []])

  let SEQ_LE ← prove
   r"!f g l m. f --> l /\ g --> m /\ (?N. !n. n >= N ==> f(n) <= g(n))
        ==> l <= m"
   (REPEAT GEN_TAC THEN
    MP_TAC (← ISPEC (← q r"(>=) :num->num->bool") NET_LE) THEN
    REWRITE_TAC [DORDER_NGE, tends_num_real, GE, LE_REFL] THEN
    DISCH_THEN MATCH_ACCEPT_TAC)

  let SEQ_LE_0 ← prove
   r"!f g. f --> &0 /\ (?N. !n. n >= N ==> abs(g n) <= abs(f n))
         ==> g --> &0"
   (REWRITE_TAC [SEQ, REAL_SUB_RZERO, GE] THEN
    MESON_TAC [LE_CASES, LE_TRANS, REAL_LET_TRANS])

  -- @@RETURN BEGIN
  return { SEQ_NEG_CONV, SEQ_NEG_BOUNDED, SEQ_BCONV, SEQ_MONOSUB, SEQ_SBOUNDED,
           SEQ_SUBLE, SEQ_DIRECT, SEQ_CAUCHY, SEQ_LE, SEQ_LE_0 }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Displacing sequences; abs; inverses of unbounded sequences; c^n; the      -/
/- harmonic sequence; nested intervals.  (analysis.ml 3729-3994)             -/
/- ------------------------------------------------------------------------- -/

structure SeqLim where
  -- @@FIELDS
  SEQ_SUC : thm
  SEQ_ABS : thm
  SEQ_ABS_IMP : thm
  SEQ_INV0 : thm
  SEQ_POWER_ABS : thm
  SEQ_POWER : thm
  SEQ_HARMONIC : thm
  SEQ_SUBSEQ : thm
  SEQ_POW : thm
  NEST_LEMMA : thm
  NEST_LEMMA_UNIQ : thm
  deriving Inhabited

@[nospecialize]
def setupSeqLim [HolBase] (D : AnalysisDeps) (BNames : Names) (BTactics : Tactics) (BReals1 : Reals1) (BReals2 : Reals2) (BReals3 : Reals3) (BAbs : Abs) (BPow : Pow) (BNetArith : NetArith) (BSeqs : Seqs) (BSeqs2 : Seqs2) :
    ExceptT String IO SeqLim := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, INDUCT_TAC, MESON_TAC, num_CONV, .. } := D
  let { ADD_CLAUSES, CONJ_ASSOC, GE, LE_ADD, LE_MULT_RCANCEL, LE_SUC, LE_TRANS, LT_0,
        NOT_LT, REAL_ABS_DIV, REAL_ABS_NUM, REAL_ADD_LID, REAL_ADD_SYM, .. } := D.core1
  let { REAL_LET_TRANS, REAL_LE_RMUL, REAL_LT_ADDL, REAL_LT_INV2, REAL_LT_LDIV_EQ,
        REAL_LT_TRANS, .. } := D.core2
  let { REAL_MUL_SYM, REAL_OF_NUM_LE, REAL_OF_NUM_LT, RIGHT_IMP_FORALL_THM, num_CASES,
        real_abs, real_ge, real_gt, real_pow, real_sub, .. } := D.core3
  let { LESS_EQ_SUC_REFL, .. } := BNames
  let { EXACT_CONV, X_BETA_CONV, .. } := BTactics
  let { REAL_LE_LADD, REAL_LE_LT, REAL_LE_RADD, REAL_LE_REFL, REAL_LE_TRANS,
        REAL_LTE_TRANS, REAL_LT_01, REAL_LT_IMP_LE, REAL_NOT_LE, REAL_NOT_LT,
        REAL_SUB_ADD, .. } := BReals1
  let { REAL_INV1, REAL_INVINV, REAL_INV_POS, REAL_LE, REAL_LT_IMP_NE, REAL_NEG_SUB,
        REAL_SUB_0, REAL_SUB_LE, REAL_SUB_LT, .. } := BReals2
  let { REAL_LE_NEG2, REAL_LE_RMUL_EQ, REAL_LT_SUB_LADD, REAL_SUB_RZERO, .. } := BReals3
  let { ABS_0, ABS_ABS, ABS_INV, ABS_LE, ABS_NZ, ABS_POS, .. } := BAbs
  let { POW_0, POW_ABS, POW_INV, POW_NZ, POW_PLUS1, REAL_ARCH, .. } := BPow
  let { NET_ABS, .. } := BNetArith
  let { MONO_SUC, SEQ, SEQ_BOUNDED_2, SEQ_CONST, SEQ_LIM, SEQ_MUL, SEQ_SUB, SEQ_UNIQ,
        tends_num_real, .. } := BSeqs
  let { SEQ_BCONV, SEQ_LE, .. } := BSeqs2
  -- @@SCOPE END
  let numc (s : String) : ExceptT String IO thm := do ExceptT.mk (num_CONV (← q s))

  let SEQ_SUC ← prove
   r"!f l. f --> l <=> (\n. f(SUC n)) --> l"
   (← do
    let eR ← q "e:real"
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [SEQ, GE] THEN EQ_TAC THEN
      DISCH_THEN (fun th => X_GEN_TAC eR THEN
        DISCH_THEN (MP_TAC o MATCH_MP th)) THEN BETA_TAC THEN
      DISCH_THEN (X_CHOOSE_TAC (← q "N:num")) THENL
       [EXISTS_TAC (← q "N:num") THEN X_GEN_TAC (← q "n:num") THEN DISCH_TAC THEN
        FIRST_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
        EXISTS_TAC (← q "SUC N") THEN ASM_REWRITE_TAC [LE_SUC, LESS_EQ_SUC_REFL],
        EXISTS_TAC (← q "SUC N") THEN X_GEN_TAC (← q "n:num") THEN
        STRUCT_CASES_TAC (← SPEC (← q "n:num") num_CASES) THENL
         [REWRITE_TAC [← GSYM NOT_LT, LT_0],
          REWRITE_TAC [LE_SUC] THEN DISCH_TAC THEN
          FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []]]))

  let SEQ_ABS ← prove
   r"!f. (\n. abs(f n)) --> &0 <=> f --> &0"
   (GEN_TAC THEN REWRITE_TAC [SEQ] THEN
    BETA_TAC THEN REWRITE_TAC [REAL_SUB_RZERO, ABS_ABS])

  let SEQ_ABS_IMP ← prove
   r"!f l. f --> l ==> (\n. abs(f n)) --> abs(l)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [tends_num_real] THEN
    MATCH_ACCEPT_TAC NET_ABS)

  let SEQ_INV0 ← prove
   r"!f. (!y. ?N. !n. n >= N ==> f(n) > y)
        ==> (\n. inv(f n)) --> &0"
   (GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [SEQ, REAL_SUB_RZERO] THEN
    X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN
    FIRST_ASSUM (X_CHOOSE_TAC (← q "N:num") o SPEC (← q "inv e")) THEN
    EXISTS_TAC (← q "N:num") THEN X_GEN_TAC (← q "n:num") THEN
    DISCH_THEN (fun th => ASSUME_TAC th THEN ANTE_RES_THEN MP_TAC th) THEN
    REWRITE_TAC [real_gt] THEN BETA_TAC THEN
    IMP_RES_THEN ASSUME_TAC REAL_INV_POS THEN
    SUBGOAL_THEN (← q r"&0 < f(n:num)") ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (← q "inv e") THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [← GSYM real_gt] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"&0 < inv(f(n:num))") ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_INV_POS THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"~(f(n:num) = &0)") ASSUME_TAC THENL
     [CONV_TAC (RAND_CONV SYM_CONV) THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
      ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP ABS_INV th])) THEN
    SUBGOAL_THEN (← q r"e = inv(inv e)") SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INVINV THEN
      CONV_TAC (RAND_CONV SYM_CONV) THEN
      MATCH_MP_TAC REAL_LT_IMP_NE THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q r"(f:num->real) n") THEN
    ASM_REWRITE_TAC [ABS_LE])

  let SEQ_POWER_ABS ← prove
   r"!c. abs(c) < &1 ==> (\n. abs(c) pow n) --> &0"
   (GEN_TAC THEN DISCH_TAC THEN MP_TAC (← SPEC (← q "c:real") ABS_POS) THEN
    REWRITE_TAC [REAL_LE_LT] THEN DISCH_THEN DISJ_CASES_TAC THENL
     [SUBGOAL_THEN (← q r"!n. abs(c) pow n = inv(inv(abs(c) pow n))")
        (fun th => ONCE_REWRITE_TAC [th]) THENL
       [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INVINV THEN
        MATCH_MP_TAC POW_NZ THEN
        ASM_REWRITE_TAC [ABS_NZ, ABS_ABS], ALL_TAC] THEN
      CONV_TAC (← EXACT_CONV [← ExceptT.mk (X_BETA_CONV (← q "n:num") (← q r"inv(abs(c) pow n)"))]) THEN
      MATCH_MP_TAC SEQ_INV0 THEN BETA_TAC THEN X_GEN_TAC (← q "y:real") THEN
      SUBGOAL_THEN (← q r"~(abs(c) = &0)")
           (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP POW_INV th])) THENL
       [CONV_TAC (RAND_CONV SYM_CONV) THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
        ASM_REWRITE_TAC [], ALL_TAC] THEN REWRITE_TAC [real_gt] THEN
      SUBGOAL_THEN (← q r"&0 < inv(abs c) - &1") ASSUME_TAC THENL
       [REWRITE_TAC [REAL_LT_SUB_LADD] THEN REWRITE_TAC [REAL_ADD_LID] THEN
        ONCE_REWRITE_TAC [← GSYM REAL_INV1] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
        ASM_REWRITE_TAC [], ALL_TAC] THEN
      MP_TAC (← SPEC (← q r"inv(abs c) - &1") REAL_ARCH) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q "N:num") o SPEC (← q "y:real")) THEN
      EXISTS_TAC (← q "N:num") THEN X_GEN_TAC (← q "n:num") THEN REWRITE_TAC [GE] THEN
      DISCH_TAC THEN SUBGOAL_THEN (← q r"y < (&n * (inv(abs c) - &1))")
      ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LTE_TRANS THEN
        EXISTS_TAC (← q r"&N * (inv(abs c) - &1)") THEN ASM_REWRITE_TAC [] THEN
        FIRST_ASSUM (fun th => tactic_of do
          pure (GEN_REWRITE_TAC id [← MATCH_MP REAL_LE_RMUL_EQ th])) THEN
        ASM_REWRITE_TAC [REAL_LE], ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_TRANS THEN
      EXISTS_TAC (← q r"&n * (inv(abs c) - &1)") THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC (← q r"&1 + (&n * (inv(abs c) - &1))") THEN
      REWRITE_TAC [REAL_LT_ADDL, REAL_LT_01] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"(&1 + (inv(abs c) - &1)) pow n") THEN CONJ_TAC THENL
       [MATCH_MP_TAC POW_PLUS1 THEN ASM_REWRITE_TAC [],
        ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN REWRITE_TAC [REAL_SUB_ADD] THEN
        REWRITE_TAC [REAL_LE_REFL]],
      FIRST_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC [SEQ] THEN
      GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC (← q "1") THEN
      X_GEN_TAC (← q "n:num") THEN REWRITE_TAC [GE] THEN BETA_TAC THEN
      STRUCT_CASES_TAC (← SPEC (← q "n:num") num_CASES) THENL
       [REWRITE_TAC [← GSYM NOT_LT, ← numc "1", LT_0],
        REWRITE_TAC [POW_0, REAL_SUB_RZERO, ABS_0] THEN
        REWRITE_TAC [← ASSUME (← q r"&0 < e")]]])

  let SEQ_POWER ← prove
   r"!c. abs(c) < &1 ==> (\n. c pow n) --> &0"
   (GEN_TAC THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC [← GSYM SEQ_ABS] THEN BETA_TAC THEN
    REWRITE_TAC [← GSYM POW_ABS] THEN
    POP_ASSUM (ACCEPT_TAC o MATCH_MP SEQ_POWER_ABS))

  let SEQ_HARMONIC ← prove
   r"!a. (\n. a / &n) --> &0"
   (GEN_TAC THEN REWRITE_TAC [SEQ] THEN X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q "abs a") o MATCH_MP REAL_ARCH) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q "N:num")) THEN EXISTS_TAC (← q "N + 1") THEN
    X_GEN_TAC (← q "n:num") THEN REWRITE_TAC [GE] THEN DISCH_TAC THEN
    REWRITE_TAC [REAL_SUB_RZERO, REAL_ABS_DIV, REAL_ABS_NUM] THEN
    SUBGOAL_THEN (← q r"&0 < &n") (fun th => SIMP_TAC [REAL_LT_LDIV_EQ, th]) THENL
     [REWRITE_TAC [REAL_OF_NUM_LT] THEN UNDISCH_TAC (← q "N + 1 <= n") THEN ARITH_TAC,
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q r"&N * e")] THEN
    ASM_REWRITE_TAC [] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC [REAL_LT_IMP_LE, REAL_OF_NUM_LE] THEN
    UNDISCH_TAC (← q "N + 1 <= n") THEN ARITH_TAC)

  let SEQ_SUBSEQ ← prove
   r"!f l. f --> l ==> !a b. ~(a = 0) ==> (\n. f(a * n + b)) --> l"
   (REWRITE_TAC [RIGHT_IMP_FORALL_THM, SEQ, GE] THEN REPEAT GEN_TAC THEN
    SUBGOAL_THEN (← q r"!a b n. ~(a = 0) ==> n <= a * n + b")
     (fun th => MESON_TAC [th, LE_TRANS]) THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC (← ARITH_RULE
     (← q r"1 * n <= a * n ==> n <= a * n + b")) THEN
    REWRITE_TAC [LE_MULT_RCANCEL] THEN POP_ASSUM MP_TAC THEN ARITH_TAC)

  let SEQ_POW ← prove
   r"!f l. (f --> l) ==> !n. (\i. f(i) pow n) --> l pow n"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC [real_pow, SEQ_CONST] THEN MATCH_MP_TAC SEQ_MUL THEN
    ASM_REWRITE_TAC [])

  let NEST_LEMMA ← prove
   r"!f g. (!n. f(SUC n) >= f(n)) /\
         (!n. g(SUC n) <= g(n)) /\
         (!n. f(n) <= g(n)) ==>
                ?l m. l <= m /\ ((!n. f(n) <= l) /\ f --> l) /\
                                ((!n. m <= g(n)) /\ g --> m)"
   (← do
    -- THENL branches are evaluated right to left; both TAUTs are the same.
    let tnn2 ← TAUT (← q r"a <=> ~ ~a")
    let tnn1 ← TAUT (← q r"a <=> ~ ~a")
    pure (REPEAT STRIP_TAC THEN MP_TAC (← SPEC (← q r"f:num->real") MONO_SUC) THEN
      ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
      MP_TAC (← SPEC (← q r"g:num->real") MONO_SUC) THEN ASM_REWRITE_TAC [] THEN
      DISCH_TAC THEN SUBGOAL_THEN (← q r"bounded((mr1), (>=) :num->num->bool) f")
      ASSUME_TAC THENL
       [MATCH_MP_TAC SEQ_BOUNDED_2 THEN
        MAP_EVERY EXISTS_TAC [← q r"(f:num->real) 0", ← q r"(g:num->real) 0"] THEN
        INDUCT_TAC THEN ASM_REWRITE_TAC [REAL_LE_REFL] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"(f:num->real) n") THEN
          RULE_ASSUM_TAC (REWRITE_RULE [real_ge]) THEN ASM_REWRITE_TAC [],
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"g(SUC n):real") THEN
          ASM_REWRITE_TAC [] THEN SPEC_TAC (← q "SUC n", ← q "m:num") THEN
          INDUCT_TAC THEN REWRITE_TAC [REAL_LE_REFL] THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"g(m:num):real") THEN
          ASM_REWRITE_TAC []], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"bounded((mr1), (>=) :num->num->bool) g") ASSUME_TAC THENL
       [MATCH_MP_TAC SEQ_BOUNDED_2 THEN
        MAP_EVERY EXISTS_TAC [← q r"(f:num->real) 0", ← q r"(g:num->real) 0"] THEN
        INDUCT_TAC THEN ASM_REWRITE_TAC [REAL_LE_REFL] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"(f:num->real) (SUC n)") THEN
          ASM_REWRITE_TAC [] THEN SPEC_TAC (← q "SUC n", ← q "m:num") THEN
          INDUCT_TAC THEN REWRITE_TAC [REAL_LE_REFL] THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"(f:num->real) m") THEN
          RULE_ASSUM_TAC (REWRITE_RULE [real_ge]) THEN ASM_REWRITE_TAC [],
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"(g:num->real) n") THEN
          ASM_REWRITE_TAC []], ALL_TAC] THEN
      MP_TAC (← SPEC (← q r"f:num->real") SEQ_BCONV) THEN ASM_REWRITE_TAC [SEQ_LIM] THEN
      DISCH_TAC THEN MP_TAC (← SPEC (← q r"g:num->real") SEQ_BCONV) THEN
      ASM_REWRITE_TAC [SEQ_LIM] THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [← q "lim f", ← q "lim g"] THEN ASM_REWRITE_TAC [] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SEQ_LE THEN
        MAP_EVERY EXISTS_TAC [← q r"f:num->real", ← q r"g:num->real"] THEN ASM_REWRITE_TAC [],
        X_GEN_TAC (← q "m:num") THEN GEN_REWRITE_TAC id [tnn1] THEN
        PURE_REWRITE_TAC [REAL_NOT_LE] THEN DISCH_TAC THEN
        UNDISCH_TAC (← q "f --> lim f") THEN REWRITE_TAC [SEQ] THEN
        DISCH_THEN (MP_TAC o SPEC (← q "f(m) - lim f")) THEN
        ASM_REWRITE_TAC [REAL_SUB_LT] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "p:num") MP_TAC) THEN
        DISCH_THEN (MP_TAC o SPEC (← q "p + m:num")) THEN
        REWRITE_TAC [GE, LE_ADD] THEN REWRITE_TAC [real_abs] THEN
        SUBGOAL_THEN (← q r"!p. lim f <= f(p + m:num)") ASSUME_TAC THENL
         [INDUCT_TAC THEN ASM_REWRITE_TAC [ADD_CLAUSES] THENL
           [MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC,
            MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"f(p + m:num):real") THEN
            RULE_ASSUM_TAC (REWRITE_RULE [real_ge]) THEN ASM_REWRITE_TAC []],
          ASM_REWRITE_TAC [REAL_SUB_LE] THEN
          REWRITE_TAC [REAL_NOT_LT, real_sub, REAL_LE_RADD] THEN
          SPEC_TAC (← q "p:num", ← q "p:num") THEN INDUCT_TAC THEN
          REWRITE_TAC [REAL_LE_REFL, ADD_CLAUSES] THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"f(p + m:num):real") THEN
          RULE_ASSUM_TAC (REWRITE_RULE [real_ge]) THEN ASM_REWRITE_TAC []],
        X_GEN_TAC (← q "m:num") THEN GEN_REWRITE_TAC id [tnn2] THEN
        PURE_REWRITE_TAC [REAL_NOT_LE] THEN DISCH_TAC THEN
        UNDISCH_TAC (← q "g --> lim g") THEN REWRITE_TAC [SEQ] THEN
        DISCH_THEN (MP_TAC o SPEC (← q "lim g - g(m)")) THEN
        ASM_REWRITE_TAC [REAL_SUB_LT] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "p:num") MP_TAC) THEN
        DISCH_THEN (MP_TAC o SPEC (← q "p + m:num")) THEN
        REWRITE_TAC [GE, LE_ADD] THEN REWRITE_TAC [real_abs] THEN
        SUBGOAL_THEN (← q r"!p. g(p + m:num) < lim g") ASSUME_TAC THENL
         [INDUCT_TAC THEN ASM_REWRITE_TAC [ADD_CLAUSES] THEN
          MATCH_MP_TAC REAL_LET_TRANS THEN
          EXISTS_TAC (← q r"g(p + m:num):real") THEN ASM_REWRITE_TAC [],
          REWRITE_TAC [REAL_SUB_LE] THEN ASM_REWRITE_TAC [← GSYM REAL_NOT_LT] THEN
          REWRITE_TAC [REAL_NOT_LT, REAL_NEG_SUB] THEN
          REWRITE_TAC [real_sub, REAL_LE_LADD, REAL_LE_NEG2] THEN
          SPEC_TAC (← q "p:num", ← q "p:num") THEN INDUCT_TAC THEN
          REWRITE_TAC [REAL_LE_REFL, ADD_CLAUSES] THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"g(p + m:num):real") THEN
          ASM_REWRITE_TAC []]]))

  let NEST_LEMMA_UNIQ ← prove
   r"!f g. (!n. f(SUC n) >= f(n)) /\
         (!n. g(SUC n) <= g(n)) /\
         (!n. f(n) <= g(n)) /\
         (\n. f(n) - g(n)) --> &0 ==>
                ?l. ((!n. f(n) <= l) /\ f --> l) /\
                    ((!n. l <= g(n)) /\ g --> l)"
   (← do
    let a ← ASSUME (← q r"(\n. f(n) - g(n)) --> &0")
    pure (REPEAT GEN_TAC THEN
      DISCH_THEN (fun th => STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
      REWRITE_TAC [CONJ_ASSOC] THEN DISCH_THEN (MP_TAC o CONJUNCT1) THEN
      REWRITE_TAC [← GSYM CONJ_ASSOC] THEN
      DISCH_THEN (MP_TAC o MATCH_MP NEST_LEMMA) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "l:real") MP_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "m:real") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q "l:real") THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q "l:real = m") (fun th => ASM_REWRITE_TAC [th]) THEN
      MP_TAC (← SPECL [← q r"f:num->real", ← q "l:real", ← q r"g:num->real", ← q "m:real"] SEQ_SUB) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (MP_TAC o CONJ a) THEN
      DISCH_THEN (MP_TAC o MATCH_MP SEQ_UNIQ) THEN
      CONV_TAC (LAND_CONV SYM_CONV) THEN
      REWRITE_TAC [REAL_SUB_0]))

  -- @@RETURN BEGIN
  return { SEQ_SUC, SEQ_ABS, SEQ_ABS_IMP, SEQ_INV0, SEQ_POWER_ABS, SEQ_POWER,
           SEQ_HARMONIC, SEQ_SUBSEQ, SEQ_POW, NEST_LEMMA, NEST_LEMMA_UNIQ }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Bolzano's lemma; infinite sums; grouping and offsetting terms.            -/
/- (analysis.ml 4002-4296)                                                   -/
/- ------------------------------------------------------------------------- -/

structure Series1 where
  -- @@FIELDS
  BOLZANO_LEMMA : thm
  BOLZANO_LEMMA_ALT : thm
  sums : thm
  summable : thm
  suminf : thm
  SUM_SUMMABLE : thm
  SUMMABLE_SUM : thm
  SUM_UNIQ : thm
  SER_UNIQ : thm
  SER_0 : thm
  SER_POS_LE : thm
  SER_POS_LT : thm
  SER_GROUP : thm
  SER_PAIR : thm
  SER_OFFSET : thm
  SER_OFFSET_REV : thm
  deriving Inhabited

@[nospecialize]
def setupSeries1 [HolBase] (D : AnalysisDeps) (BNames : Names) (BReals1 : Reals1) (BReals2 : Reals2) (BReals3 : Reals3) (BAbs : Abs) (BPow : Pow) (BSums : Sums) (BSeqs : Seqs) (BSeqs2 : Seqs2) (BSeqLim : SeqLim) :
    ExceptT String IO Series1 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, GEN_BETA_CONV, INDUCT_TAC, MESON_TAC, REAL_ARITH,
        new_definition, num_CONV, .. } := D
  let { ADD1, ADD_CLAUSES, ADD_SYM, GE, IMP_CLAUSES, IMP_IMP, LE, LE_ADD, LE_EXISTS,
        LE_REFL, LE_TRANS, LT_0, LT_REFL, MONO_FORALL, MULT_CLAUSES, MULT_SYM,
        NOT_CLAUSES, NOT_SUC, REAL_ADD_AC, REAL_ADD_ASSOC, REAL_ADD_LID, REAL_ADD_LINV,
        REAL_ADD_RID, REAL_ADD_SYM, .. } := D.core1
  let { REAL_DIV_LMUL, REAL_LET_TRANS, REAL_LE_ADDR, REAL_LT_ADDR, REAL_MUL_ASSOC,
        REAL_MUL_LID, REAL_MUL_LINV, .. } := D.core2
  let { REAL_MUL_SYM, SELECT_AX, num_Axiom, num_CASES, real_abs, real_div, real_ge,
        real_sub, .. } := D.core3
  let { LESS_EQUAL_ADD, LESS_EQ_SUC_REFL, LESS_SUC_REFL, .. } := BNames
  let { REAL_ADD_RID_UNIQ, REAL_LE_REFL, REAL_LTE_TRANS, REAL_LT_ADD2, REAL_LT_IMP_LE,
        REAL_MUL_RID, REAL_MUL_RINV, REAL_MUL_RZERO, REAL_NEG_ADD, REAL_NEG_NEG, .. } := BReals1
  let { REAL_DOUBLE, REAL_INJ, REAL_INV1, REAL_LT, REAL_LT_HALF1, REAL_LT_RMUL_EQ,
        REAL_NEG_0, REAL_NEG_SUB, REAL_SUB_0, REAL_SUB_LDISTRIB, REAL_SUB_LE, .. } := BReals2
  let { REAL_EQ_LMUL_IMP, REAL_HALF_DOUBLE, REAL_INV_MUL_WEAK, REAL_MIDDLE1,
        REAL_MIDDLE2, .. } := BReals3
  let { ABS_INV, ABS_N, ABS_SUB, ABS_ZERO, .. } := BAbs
  let { POW_ABS, POW_INV, POW_NZ, pow, .. } := BPow
  let { SUM_DIFF, SUM_GROUP, SUM_OFFSET, SUM_POS_GEN, SUM_TWO, SUM_ZERO, sum, .. } := BSums
  let { SEQ, SEQ_CONST, SEQ_MUL, SEQ_NEG, SEQ_UNIQ, .. } := BSeqs
  let { SEQ_LE, .. } := BSeqs2
  let { NEST_LEMMA_UNIQ, SEQ_ABS, SEQ_POWER_ABS, .. } := BSeqLim
  -- @@SCOPE END
  let numc (s : String) : ExceptT String IO thm := do ExceptT.mk (num_CONV (← q s))

  let BOLZANO_LEMMA ← prove
   r"!P. (!a b c. a <= b /\ b <= c /\ P(a,b) /\ P(b,c) ==> P(a,c)) /\
       (!x. ?d. &0 < d /\ !a b. a <= x /\ x <= b /\ (b - a) < d ==> P(a,b))
      ==> !a b. a <= b ==> P(a,b)"
   (← do
    let two ← q r"&2"
    -- `(... o C ISPECL num_Axiom) [t1; t2]`: the list is built right to left.
    let ax2 ← q r"\fn (n:num). if P(FST fn,(FST fn + SND fn)/ &2) then
                          ((FST fn + SND fn)/ &2,SND fn) else
                          (FST fn,(FST fn + SND fn)/ &2)"
    let ax1 ← q r"(a:real,(b:real))"
    let fax ← EXISTENCE (← BETA_RULE (← ISPECL [ax1, ax2] num_Axiom))
    let ac ← AC REAL_ADD_AC (← q r"a + b + c + d = (d + a) + (c + b)")
    let sm4 ← q r"&0"
    let sm3 ← q r"\n. (inv (&2 pow n))"
    let sm2 ← q r"b - a"
    let sm1 ← q r"\n:num. b - a"
    let seqMul ← SPECL [sm1, sm2, sm3, sm4] SEQ_MUL
    pure (REPEAT STRIP_TAC THEN
      GEN_REWRITE_TAC id [← TAUT (← q r"a <=> ~ ~a")] THEN DISCH_TAC THEN
      X_CHOOSE_THEN (← q r"f:num->real#real") STRIP_ASSUME_TAC fax THEN
      MP_TAC (← SPECL
        [← q r"\n:num. FST(f(n) :real#real)", ← q r"\n:num. SND(f(n) :real#real)"]
        NEST_LEMMA_UNIQ) THEN BETA_TAC THEN
      SUBGOAL_THEN (← q r"!n:num. FST(f n) <= SND(f n)") ASSUME_TAC THENL
       [INDUCT_TAC THEN ASM_REWRITE_TAC [] THEN
        COND_CASES_TAC THEN REWRITE_TAC [] THENL
         [MATCH_MP_TAC REAL_MIDDLE2, MATCH_MP_TAC REAL_MIDDLE1] THEN
        FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN REWRITE_TAC [real_ge] THEN
      SUBGOAL_THEN (← q r"!n. FST(f n :real#real) <= FST(f(SUC n))")
      ASSUME_TAC THENL
       [REWRITE_TAC [real_ge] THEN INDUCT_TAC THEN
        FIRST_ASSUM
         (fun th => GEN_REWRITE_TAC (funpow 2 RAND_CONV) [th]) THEN
        COND_CASES_TAC THEN REWRITE_TAC [REAL_LE_REFL] THEN
        MATCH_MP_TAC REAL_MIDDLE1 THEN FIRST_ASSUM MATCH_ACCEPT_TAC, ALL_TAC] THEN
      SUBGOAL_THEN (← q r"!n. ~P(FST((f:num->real#real) n),SND(f n))") ASSUME_TAC THENL
       [INDUCT_TAC THEN ASM_REWRITE_TAC [] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
        DISCH_TAC THEN UNDISCH_TAC (← q r"~P(FST((f:num->real#real) n),SND(f n))") THEN
        PURE_REWRITE_TAC [IMP_CLAUSES, NOT_CLAUSES] THEN
        FIRST_ASSUM MATCH_MP_TAC THEN
        EXISTS_TAC (← q r"(FST(f(n:num)) + SND(f(n))) / &2") THEN
        ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_MIDDLE1, MATCH_MP_TAC REAL_MIDDLE2] THEN
        FIRST_ASSUM MATCH_ACCEPT_TAC, ALL_TAC] THEN
      SUBGOAL_THEN (← q r"!n. SND(f(SUC n) :real#real) <= SND(f n)") ASSUME_TAC THENL
       [BETA_TAC THEN INDUCT_TAC THEN
        FIRST_ASSUM (fun th => GEN_REWRITE_TAC
          (LAND_CONV o RAND_CONV) [th]) THEN
        COND_CASES_TAC THEN REWRITE_TAC [REAL_LE_REFL] THEN
        MATCH_MP_TAC REAL_MIDDLE2 THEN FIRST_ASSUM MATCH_ACCEPT_TAC, ALL_TAC] THEN
      SUBGOAL_THEN (← q r"!n. SND(f n) - FST(f n) = (b - a) / (&2 pow n)")
      ASSUME_TAC THENL
       [INDUCT_TAC THENL
         [ASM_REWRITE_TAC [pow, real_div, REAL_INV1, REAL_MUL_RID], ALL_TAC] THEN
        ASM_REWRITE_TAC [] THEN COND_CASES_TAC THEN REWRITE_TAC [] THEN
        MATCH_MP_TAC REAL_EQ_LMUL_IMP THEN EXISTS_TAC two THEN
        REWRITE_TAC [REAL_SUB_LDISTRIB] THEN
        (SUBGOAL_THEN (← q r"~(&2 = &0)") (fun th => tactic_of do
           pure (REWRITE_TAC [th] THEN REWRITE_TAC [← MATCH_MP REAL_DIV_LMUL th])) THENL
          [REWRITE_TAC [REAL_INJ, ← numc "2", NOT_SUC], ALL_TAC]) THEN
        REWRITE_TAC [← GSYM REAL_DOUBLE] THEN
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_ADD_SYM] THEN
        (SUBGOAL_THEN (← q r"!x y z. (x + y) - (x + z) = y - z")
         (fun th => REWRITE_TAC [th])
         THENL
          [REPEAT GEN_TAC THEN REWRITE_TAC [real_sub, REAL_NEG_ADD] THEN
           GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_ADD_RID] THEN
           SUBST1_TAC (← SYM (← SPEC (← q "x:real") REAL_ADD_LINV)) THEN
           REWRITE_TAC [REAL_ADD_AC], ALL_TAC]) THEN
        ASM_REWRITE_TAC [REAL_DOUBLE] THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
        REWRITE_TAC [real_div, ← GSYM REAL_MUL_ASSOC] THEN
        AP_TERM_TAC THEN REWRITE_TAC [pow] THEN
        (SUBGOAL_THEN (← q r"~(&2 = &0) /\ ~(&2 pow n = &0)")
           (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP REAL_INV_MUL_WEAK th])) THENL
          [CONJ_TAC THENL [ALL_TAC, MATCH_MP_TAC POW_NZ] THEN
           REWRITE_TAC [REAL_INJ] THEN
           REWRITE_TAC [← numc "2", NOT_SUC],
           ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REWRITE_TAC [REAL_MUL_ASSOC] THEN
           GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV)
             [← GSYM REAL_MUL_LID] THEN
           AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
           MATCH_MP_TAC REAL_MUL_RINV THEN REWRITE_TAC [REAL_INJ] THEN
           REWRITE_TAC [← numc "2", NOT_SUC]]),
        ALL_TAC] THEN
      FIRST_ASSUM (undischCheck (fun c => pure (can (find_term HolCore.Classic.is_cond) c))) THEN
      DISCH_THEN (fun _ => ALL_TAC) THEN ASM_REWRITE_TAC [] THEN
      (fun gl => ExceptT.run do
        let t ← liftExcept (do pure (← dest_imp (← rand gl.2)).1)
        ExceptT.mk (SUBGOAL_THEN t (fun t => REWRITE_TAC [t]) gl)) THENL
       [ONCE_REWRITE_TAC [SEQ_NEG] THEN BETA_TAC THEN
        ASM_REWRITE_TAC [REAL_NEG_SUB, REAL_NEG_0] THEN
        REWRITE_TAC [real_div] THEN SUBGOAL_THEN (← q r"~(&2 = &0)") ASSUME_TAC THENL
         [REWRITE_TAC [REAL_INJ, ← numc "2", NOT_SUC], ALL_TAC] THEN
        MP_TAC seqMul THEN
        REWRITE_TAC [SEQ_CONST, REAL_MUL_RZERO] THEN BETA_TAC THEN
        DISCH_THEN MATCH_MP_TAC THEN
        FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP POW_INV th])) THEN
        ONCE_REWRITE_TAC [← GSYM SEQ_ABS] THEN BETA_TAC THEN
        REWRITE_TAC [← GSYM POW_ABS] THEN MATCH_MP_TAC SEQ_POWER_ABS THEN
        FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP ABS_INV th])) THEN
        REWRITE_TAC [ABS_N] THEN SUBGOAL_THEN (← q r"&0 < &2")
        (fun th => tactic_of do
          pure (ONCE_REWRITE_TAC [← GSYM (← MATCH_MP REAL_LT_RMUL_EQ th)])) THENL
         [REWRITE_TAC [REAL_LT, ← numc "2", LT_0], ALL_TAC] THEN
        FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP REAL_MUL_LINV th])) THEN
        REWRITE_TAC [REAL_MUL_LID] THEN REWRITE_TAC [REAL_LT] THEN
        REWRITE_TAC [← numc "2", LESS_SUC_REFL],
        DISCH_THEN (X_CHOOSE_THEN (← q "l:real") STRIP_ASSUME_TAC) THEN
        FIRST_ASSUM (X_CHOOSE_THEN (← q "d:real") MP_TAC o SPEC (← q "l:real")) THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        UNDISCH_TAC (← q r"(\n:num. SND(f n :real#real)) --> l") THEN
        UNDISCH_TAC (← q r"(\n:num. FST(f n :real#real)) --> l") THEN
        REWRITE_TAC [SEQ] THEN DISCH_THEN (MP_TAC o SPEC (← q r"d / &2")) THEN
        ASM_REWRITE_TAC [REAL_LT_HALF1] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "N1:num") (ASSUME_TAC o BETA_RULE)) THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"d / &2")) THEN ASM_REWRITE_TAC [REAL_LT_HALF1] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "N2:num") (ASSUME_TAC o BETA_RULE)) THEN
        DISCH_THEN (MP_TAC o
          SPECL [← q r"FST((f:num->real#real) (N1 + N2))",
                 ← q r"SND((f:num->real#real) (N1 + N2))"]) THEN
        UNDISCH_TAC (← q r"!n. (SND(f n)) - (FST(f n)) = (b - a) / ((& 2) pow n)") THEN
        DISCH_THEN (fun _ => ALL_TAC) THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC (← q r"abs(FST(f(N1 + N2:num)) - l) +
                    abs(SND(f(N1 + N2:num)) - l)") THEN
        GEN_REWRITE_TAC (funpow 2 RAND_CONV) [← GSYM REAL_HALF_DOUBLE] THEN
        CONJ_TAC THENL
         [GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [ABS_SUB] THEN
          ASM_REWRITE_TAC [real_abs, REAL_SUB_LE] THEN
          REWRITE_TAC [real_sub, ← GSYM REAL_ADD_ASSOC] THEN
          REWRITE_TAC [ac] THEN
          REWRITE_TAC [REAL_ADD_LINV, REAL_ADD_LID, REAL_LE_REFL],
          MATCH_MP_TAC REAL_LT_ADD2 THEN
          CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
          REWRITE_TAC [GE, LE_ADD] THEN
          ONCE_REWRITE_TAC [ADD_SYM] THEN REWRITE_TAC [LE_ADD]]]))

  let BOLZANO_LEMMA_ALT ← prove
   r"!P. (!a b c. a <= b /\ b <= c /\ P a b /\ P b c ==> P a c) /\
       (!x. ?d. &0 < d /\ (!a b. a <= x /\ x <= b /\ b - a < d ==> P a b))
       ==> !a b. a <= b ==> P a b"
   (GEN_TAC THEN MP_TAC (← SPEC (← q r"\(x:real,y:real). P x y :bool") BOLZANO_LEMMA) THEN
    REWRITE_TAC [] THEN
    CONV_TAC (ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC [])

  let sums ← new_definition
   r"f sums s <=> (\n. sum(0,n) f) --> s"

  let summable ← new_definition
   r"summable f <=> ?s. f sums s"

  let suminf ← new_definition
   r"suminf f = @s. f sums s"

  let SUM_SUMMABLE ← prove
   r"!f l. f sums l ==> summable f"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [summable] THEN
    EXISTS_TAC (← q "l:real") THEN POP_ASSUM ACCEPT_TAC)

  let SUMMABLE_SUM ← prove
   r"!f. summable f ==> f sums (suminf f)"
   (GEN_TAC THEN REWRITE_TAC [summable, suminf] THEN
    DISCH_THEN (CHOOSE_THEN MP_TAC) THEN
    CONV_TAC (ONCE_DEPTH_CONV ETA_CONV) THEN
    MATCH_ACCEPT_TAC SELECT_AX)

  let SUM_UNIQ ← prove
   r"!f x. f sums x ==> (x = suminf f)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q "summable f") MP_TAC THENL
     [REWRITE_TAC [summable] THEN EXISTS_TAC (← q "x:real") THEN ASM_REWRITE_TAC [],
      DISCH_THEN (ASSUME_TAC o MATCH_MP SUMMABLE_SUM) THEN
      MATCH_MP_TAC SEQ_UNIQ THEN
      EXISTS_TAC (← q r"\n. sum(0,n) f") THEN ASM_REWRITE_TAC [← GSYM sums]])

  let SER_UNIQ ← prove
   r"!f x y. f sums x /\ f sums y ==> (x = y)"
   (MESON_TAC [SUM_UNIQ])

  let SER_0 ← prove
   r"!f n. (!m. n <= m ==> (f(m) = &0)) ==>
        f sums (sum(0,n) f)"
   (← do
    let z ← q r"&0"
    pure (REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [sums, SEQ] THEN
      X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN EXISTS_TAC (← q "n:num") THEN
      X_GEN_TAC (← q "m:num") THEN REWRITE_TAC [GE] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "d:num") SUBST1_TAC o MATCH_MP LESS_EQUAL_ADD) THEN
      (fun gl => ExceptT.run do
        let mkEq ← ExceptT.mk (mk_eq : IO _)
        let t ← liftExcept (do mkEq ((← rand (← rator gl.2)), z))
        ExceptT.mk (SUBGOAL_THEN t SUBST1_TAC gl)) THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [ABS_ZERO, REAL_SUB_0] THEN
      BETA_TAC THEN REWRITE_TAC [← GSYM SUM_TWO, REAL_ADD_RID_UNIQ] THEN
      FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [GE] SUM_ZERO)) THEN
      MATCH_ACCEPT_TAC LE_REFL))

  let SER_POS_LE ← prove
   r"!f n. summable f /\ (!m. n <= m ==> &0 <= f(m))
        ==> sum(0,n) f <= suminf f"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP SUMMABLE_SUM) THEN REWRITE_TAC [sums] THEN
    MP_TAC (← SPEC (← q r"sum(0,n) f") SEQ_CONST) THEN
    GEN_REWRITE_TAC id [IMP_IMP] THEN
    MATCH_MP_TAC (← REWRITE_RULE [← TAUT (← q r"a /\ b /\ c ==> d <=> c ==> a /\ b ==> d")]
      SEQ_LE) THEN BETA_TAC THEN
    EXISTS_TAC (← q "n:num") THEN X_GEN_TAC (← q "m:num") THEN REWRITE_TAC [GE] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "d:num") SUBST1_TAC o MATCH_MP LESS_EQUAL_ADD) THEN
    REWRITE_TAC [← GSYM SUM_TWO, REAL_LE_ADDR] THEN
    MATCH_MP_TAC SUM_POS_GEN THEN FIRST_ASSUM MATCH_ACCEPT_TAC)

  let SER_POS_LT ← prove
   r"!f n. summable f /\ (!m. n <= m ==> &0 < f(m))
        ==> sum(0,n) f < suminf f"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q r"sum(0,n + 1) f") THEN
    CONJ_TAC THENL
     [REWRITE_TAC [← GSYM SUM_TWO, REAL_LT_ADDR] THEN
      REWRITE_TAC [← numc "1", sum, REAL_ADD_LID, ADD_CLAUSES] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN MATCH_ACCEPT_TAC LE_REFL,
      MATCH_MP_TAC SER_POS_LE THEN ASM_REWRITE_TAC [] THEN
      GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q "SUC n") THEN
      REWRITE_TAC [LESS_EQ_SUC_REFL] THEN ASM_REWRITE_TAC [ADD1]])

  let SER_GROUP ← prove
   r"!f k. summable f /\ 0 < k ==>
          (\n. sum(n * k,k) f) sums (suminf f)"
   (← do
    let eR ← q "e:real"
    pure (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      DISCH_THEN (MP_TAC o MATCH_MP SUMMABLE_SUM) THEN
      REWRITE_TAC [sums, SEQ] THEN BETA_TAC THEN
      DISCH_THEN (fun t => X_GEN_TAC eR THEN
        DISCH_THEN (MP_TAC o MATCH_MP t)) THEN
      REWRITE_TAC [GE] THEN DISCH_THEN (X_CHOOSE_TAC (← q "N:num")) THEN
      REWRITE_TAC [SUM_GROUP] THEN EXISTS_TAC (← q "N:num") THEN
      X_GEN_TAC (← q "n:num") THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q "n:num") THEN
      ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q "0 < k") THEN
      STRUCT_CASES_TAC (← SPEC (← q "k:num") num_CASES) THEN
      REWRITE_TAC [MULT_CLAUSES, LE_ADD, ← CONJUNCT1 LE] THEN
      REWRITE_TAC [LT_REFL]))

  let SER_PAIR ← prove
   r"!f. summable f ==> (\n. sum(2 * n,2) f) sums (suminf f)"
   (← do
    let lt01 ← SPEC (← q "1:num") LT_0
    pure (GEN_TAC THEN DISCH_THEN (MP_TAC o (fun th => CONJ th lt01)) THEN
      REWRITE_TAC [← SYM (← numc "2")] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN
      MATCH_ACCEPT_TAC SER_GROUP))

  let SER_OFFSET ← prove
   r"!f. summable f ==> !k. (\n. f(n + k)) sums (suminf f - sum(0,k) f)"
   (GEN_TAC THEN
    DISCH_THEN (fun th => tactic_of do
      pure (GEN_TAC THEN MP_TAC (← MATCH_MP SUMMABLE_SUM th))) THEN
    REWRITE_TAC [sums, SEQ] THEN
    DISCH_THEN (fun th => GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP th)) THEN
    BETA_TAC THEN REWRITE_TAC [GE] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q "N:num")) THEN
    EXISTS_TAC (← q "N:num") THEN X_GEN_TAC (← q "n:num") THEN DISCH_TAC THEN
    REWRITE_TAC [SUM_OFFSET] THEN
    REWRITE_TAC [real_sub, REAL_NEG_ADD, REAL_NEG_NEG] THEN
    ONCE_REWRITE_TAC [← AC REAL_ADD_AC
      (← q r"(a + b) + (c + d) = (b + d) + (a + c)")] THEN
    REWRITE_TAC [REAL_ADD_LINV, REAL_ADD_LID] THEN REWRITE_TAC [← GSYM real_sub] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC (← q "n:num") THEN ASM_REWRITE_TAC [LE_ADD])

  let SER_OFFSET_REV ← prove
   r"!f k. summable(\n. f(n + k)) ==>
         f sums (sum(0,k) f) + suminf (\n. f(n + k))"
   (← do
    -- The later rule in the THEN chain is evaluated first.
    let ra ← REAL_ARITH (← q r"a - (b + c) = a - b - c")
    let ar ← ARITH_RULE (← q r"(N + k) + d = k + N + d:num")
    pure (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP SUMMABLE_SUM) THEN
      REWRITE_TAC [sums, SEQ] THEN REWRITE_TAC [SUM_OFFSET] THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      MATCH_MP_TAC (← TAUT (← q r"(a ==> b ==> c) ==> (a ==> b) ==> (a ==> c)")) THEN
      DISCH_TAC THEN REWRITE_TAC [← GSYM (← ONCE_REWRITE_RULE [ADD_SYM] SUM_DIFF)] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "N:num") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q "N + k:num") THEN
      X_GEN_TAC (← q "n:num") THEN REWRITE_TAC [GE, LE_EXISTS] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "d:num") SUBST1_TAC) THEN
      ONCE_REWRITE_TAC [ar] THEN
      REWRITE_TAC [ra] THEN
      REWRITE_TAC [← GSYM SUM_DIFF] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC))

  -- @@RETURN BEGIN
  return { BOLZANO_LEMMA, BOLZANO_LEMMA_ALT, sums, summable, suminf, SUM_SUMMABLE,
           SUMMABLE_SUM, SUM_UNIQ, SER_UNIQ, SER_0, SER_POS_LE, SER_POS_LT, SER_GROUP,
           SER_PAIR, SER_OFFSET, SER_OFFSET_REV }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Pairing terms; composition formulas for series; Cauchy criterion;         -/
/- comparison test; geometric progressions; ratio test; truncation error.    -/
/- (analysis.ml 4300-4659)                                                   -/
/- ------------------------------------------------------------------------- -/

structure Series2 where
  -- @@FIELDS
  SER_POS_LT_PAIR : thm
  SER_ADD : thm
  SER_CMUL : thm
  SER_NEG : thm
  SER_SUB : thm
  SER_CDIV : thm
  SER_CAUCHY : thm
  SER_ZERO : thm
  SER_COMPAR : thm
  SER_COMPARA : thm
  SER_LE : thm
  SER_LE2 : thm
  SER_ACONV : thm
  SER_ABS : thm
  GP_FINITE : thm
  GP : thm
  ABS_NEG_LEMMA : thm
  SER_RATIO : thm
  SEQ_TRUNCATION : thm
  deriving Inhabited

@[nospecialize]
def setupSeries2 [HolBase] (D : AnalysisDeps) (BNames : Names) (BTactics : Tactics) (BReals1 : Reals1) (BReals2 : Reals2) (BReals3 : Reals3) (BAbs : Abs) (BPow : Pow) (BSums : Sums) (BSeqs : Seqs) (BSeqs2 : Seqs2) (BSeqLim : SeqLim) (BSeries1 : Series1) :
    ExceptT String IO Series2 := do
  -- @@SCOPE BEGIN
  let { INDUCT_TAC, num_CONV, .. } := D
  let { ADD1, ADD_AC, ADD_ASSOC, ADD_CLAUSES, ADD_SYM, BETA_THM, CONJ_ASSOC, GE, LE_0,
        LE_ADD, LE_CASES, LE_SUC, LE_TRANS, MULT_CLAUSES, REAL_ADD_AC, REAL_ADD_ASSOC,
        REAL_ADD_LID, REAL_ADD_LINV, REAL_ADD_RID, REAL_ADD_SYM, .. } := D.core1
  let { REAL_DIV_RMUL, REAL_EQ_IMP_LE, REAL_LET_TOTAL, REAL_LET_TRANS, REAL_LE_ADDR,
        REAL_LT_REFL, REAL_MUL_AC, REAL_MUL_LINV, .. } := D.core2
  let { REAL_MUL_SYM, RIGHT_EXISTS_AND_THM, num_CASES, real_abs, real_div, real_sub, .. } := D.core3
  let { LESS_EQUAL_ADD, NOT_LESS_0, OR_LESS, .. } := BNames
  let { EXACT_CONV, X_BETA_CONV, .. } := BTactics
  let { REAL_LE_MUL, REAL_LE_RADD, REAL_LE_REFL, REAL_LE_TRANS, REAL_LT_IMP_LE,
        REAL_MUL_RID, REAL_NEG_GE0, REAL_NEG_LMUL, REAL_NEG_MUL2, REAL_NOT_LE,
        REAL_NOT_LT, REAL_RDISTRIB, .. } := BReals1
  let { REAL_DIV_LZERO, REAL_EQ_RMUL, REAL_INV_1OVER, REAL_LT_IMP_NE, REAL_NEG_INV,
        REAL_NEG_MINUS1, REAL_NEG_SUB, REAL_SUB_0, REAL_SUB_LDISTRIB, REAL_SUB_LE,
        REAL_SUB_REFL, .. } := BReals2
  let { REAL_LE_LMUL_LOCAL, REAL_LT_SUB_RADD, REAL_SUB_RZERO, .. } := BReals3
  let { ABS_0, ABS_1, ABS_ABS, ABS_LE, ABS_NZ, ABS_POS, ABS_SUB, .. } := BAbs
  let { POW_ADD, POW_NZ, pow, .. } := BPow
  let { ABS_SUM, SUM_ABS, SUM_ABS_LE, SUM_ADD, SUM_CMUL, SUM_DIFF, SUM_LE, SUM_REINDEX,
        SUM_ZERO, sum, .. } := BSums
  let { SEQ, SEQ_ADD, SEQ_CONST, SEQ_DIV, SEQ_MUL, SEQ_SUB, cauchy, convergent, .. } := BSeqs
  let { SEQ_CAUCHY, SEQ_LE, .. } := BSeqs2
  let { SEQ_ABS_IMP, SEQ_POWER, .. } := BSeqLim
  let { SER_OFFSET, SUMMABLE_SUM, SUM_SUMMABLE, SUM_UNIQ, summable, sums, .. } := BSeries1
  -- @@SCOPE END
  let numc (s : String) : ExceptT String IO thm := do ExceptT.mk (num_CONV (← q s))

  let SER_POS_LT_PAIR ← prove
   r"!f n. summable f /\
         (!d. &0 < (f(n + (2 * d))) +
               f(n + ((2 * d) + 1)))
        ==> sum(0,n) f < suminf f"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN (MP_TAC o MATCH_MP SUMMABLE_SUM) THEN
    REWRITE_TAC [sums, SEQ] THEN BETA_TAC THEN
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC [REAL_NOT_LT] THEN DISCH_TAC THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"f(n) + f(n + 1)")) THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q "0")) THEN
    REWRITE_TAC [ADD_CLAUSES, MULT_CLAUSES] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "N:num") MP_TAC) THEN
    SUBGOAL_THEN (← q r"sum(0,n + 2) f <= sum(0,(2 * (SUC N)) + n) f")
    ASSUME_TAC THENL
     [SPEC_TAC (← q "N:num", ← q "N:num") THEN INDUCT_TAC THENL
       [REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES] THEN
        GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ADD_SYM] THEN
        MATCH_ACCEPT_TAC REAL_LE_REFL,
        ABBREV_TAC (← q "M = SUC N") THEN
        REWRITE_TAC [MULT_CLAUSES] THEN
        REWRITE_TAC [← numc "2", ADD_CLAUSES] THEN
        REWRITE_TAC [← GSYM (← ONCE_REWRITE_RULE [ADD_SYM] ADD1)] THEN
        REWRITE_TAC [← SYM (← numc "2")] THEN REWRITE_TAC [ADD_CLAUSES] THEN
        GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [ADD1] THEN
        REWRITE_TAC [← GSYM ADD_ASSOC] THEN
        REWRITE_TAC [← GSYM ADD1, ← SYM (← numc "2")] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC (← q r"sum(0,(2 * M) + n) f") THEN
        ASM_REWRITE_TAC [] THEN REWRITE_TAC [sum] THEN
        REWRITE_TAC [← GSYM REAL_ADD_ASSOC, REAL_LE_ADDR] THEN
        REWRITE_TAC [ADD_CLAUSES] THEN REWRITE_TAC [ADD1] THEN
        REWRITE_TAC [← GSYM ADD_ASSOC] THEN ONCE_REWRITE_TAC [ADD_SYM] THEN
        REWRITE_TAC [← GSYM ADD_ASSOC] THEN
        ONCE_REWRITE_TAC [← SPEC (← q "1") ADD_SYM] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC []],
      DISCH_THEN (MP_TAC o SPEC (← q r"(2 * (SUC N)) + n")) THEN
      (fun gl => ExceptT.run do
        let t ← liftExcept (funpow 2 (fun (m : Except String term) => do
          pure (← dest_imp (← m)).1) (pure gl.2))
        ExceptT.mk (SUBGOAL_THEN t (fun th => REWRITE_TAC [th]) gl)) THENL
       [REWRITE_TAC [← numc "2", MULT_CLAUSES] THEN
        ONCE_REWRITE_TAC [← AC ADD_AC
         (← q r"(a + (b + c)) + d:num = b + (a + (c + d))")] THEN
        REWRITE_TAC [GE, LE_ADD], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"(suminf f + (f(n) + f(n + 1))) <=
                                sum(0,(2 * (SUC N)) + n) f")
      ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC (← q r"sum(0,n + 2) f") THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC (← q r"sum(0,n) f + (f(n) + f(n + 1))") THEN
        ASM_REWRITE_TAC [REAL_LE_RADD] THEN
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        CONV_TAC (REDEPTH_CONV num_CONV) THEN
        REWRITE_TAC [ADD_CLAUSES, sum, REAL_ADD_ASSOC], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"suminf f <= sum(0,(2 * (SUC N)) + n) f")
      ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC (← q r"suminf f + (f(n) + f(n + 1))") THEN
        ASM_REWRITE_TAC [] THEN REWRITE_TAC [REAL_LE_ADDR] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
      ASM_REWRITE_TAC [real_abs, REAL_SUB_LE] THEN
      REWRITE_TAC [REAL_LT_SUB_RADD] THEN
      GEN_REWRITE_TAC (funpow 2 RAND_CONV) [REAL_ADD_SYM] THEN
      ASM_REWRITE_TAC [REAL_NOT_LT]])

  let SER_ADD ← prove
   r"!x x0 y y0. x sums x0 /\ y sums y0 ==> (\n. x(n) + y(n)) sums (x0 + y0)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [sums, SUM_ADD] THEN
    CONV_TAC (RAND_CONV (← EXACT_CONV [← ExceptT.mk (X_BETA_CONV (← q "n:num") (← q r"sum(0,n) x"))])) THEN
    CONV_TAC (RAND_CONV (← EXACT_CONV [← ExceptT.mk (X_BETA_CONV (← q "n:num") (← q r"sum(0,n) y"))])) THEN
    MATCH_ACCEPT_TAC SEQ_ADD)

  let SER_CMUL ← prove
   r"!x x0 c. x sums x0 ==> (\n. c * x(n)) sums (c * x0)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [sums, SUM_CMUL] THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"(\n. (\n. c) n * (\n. sum(0,n) x) n) --> c * x0") MP_TAC THENL
     [MATCH_MP_TAC SEQ_MUL THEN ASM_REWRITE_TAC [SEQ_CONST],
      REWRITE_TAC [BETA_THM]])

  let SER_NEG ← prove
   r"!x x0. x sums x0 ==> (\n. --(x n)) sums --x0"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [REAL_NEG_MINUS1] THEN
    MATCH_ACCEPT_TAC SER_CMUL)

  let SER_SUB ← prove
   r"!x x0 y y0. x sums x0 /\ y sums y0 ==> (\n. x(n) - y(n)) sums (x0 - y0)"
   (REPEAT GEN_TAC THEN DISCH_THEN (fun th => tactic_of do
      let b ← MATCH_MP SER_NEG (← CONJUNCT2 th)
      let a ← CONJUNCT1 th
      pure (MP_TAC (← MATCH_MP SER_ADD (← CONJ a b)))) THEN
    BETA_TAC THEN REWRITE_TAC [real_sub])

  let SER_CDIV ← prove
   r"!x x0 c. x sums x0 ==> (\n. x(n) / c) sums (x0 / c)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [real_div] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    MATCH_ACCEPT_TAC SER_CMUL)

  let SER_CAUCHY ← prove
   r"!f. summable f <=>
          !e. &0 < e ==> ?N. !m n. m >= N ==> abs(sum(m,n) f) < e"
   (GEN_TAC THEN REWRITE_TAC [summable, sums] THEN
    REWRITE_TAC [← GSYM convergent] THEN
    REWRITE_TAC [← GSYM SEQ_CAUCHY] THEN REWRITE_TAC [cauchy] THEN
    AP_TERM_TAC THEN ABS_TAC THEN REWRITE_TAC [GE] THEN BETA_TAC THEN
    REWRITE_TAC [← TAUT (← q r"((a ==> b) <=> (a ==> c)) <=> a ==> (b <=> c)")] THEN
    DISCH_TAC THEN EQ_TAC THEN DISCH_THEN (X_CHOOSE_TAC (← q "N:num")) THEN
    EXISTS_TAC (← q "N:num") THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
     [ONCE_REWRITE_TAC [SUM_DIFF] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q "m:num") THEN
      ASM_REWRITE_TAC [LE_ADD],
      DISJ_CASES_THEN MP_TAC (← SPECL [← q "m:num", ← q "n:num"] LE_CASES) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "p:num") SUBST1_TAC o
        MATCH_MP LESS_EQUAL_ADD) THENL
       [ONCE_REWRITE_TAC [ABS_SUB], ALL_TAC] THEN
      REWRITE_TAC [← GSYM SUM_DIFF] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC []])

  let SER_ZERO ← prove
   r"!f. summable f ==> f --> &0"
   (← do
    let nN ← q "n:num"
    let NN ← q "N:num"
    pure (GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [SEQ] THEN
      X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN
      UNDISCH_TAC (← q "summable f") THEN REWRITE_TAC [SER_CAUCHY] THEN
      DISCH_THEN (fun th => FIRST_ASSUM (MP_TAC o MATCH_MP th)) THEN
      DISCH_THEN (X_CHOOSE_THEN NN MP_TAC) THEN
      DISCH_THEN (fun th => EXISTS_TAC NN THEN X_GEN_TAC nN THEN
        DISCH_TAC THEN MP_TAC th) THEN
      DISCH_THEN (MP_TAC o SPECL [nN, ← q "SUC 0"]) THEN
      ASM_REWRITE_TAC [sum, REAL_SUB_RZERO, REAL_ADD_LID, ADD_CLAUSES]))

  let SER_COMPAR ← prove
   r"!f g. (?N. !n. n >= N ==> abs(f(n)) <= g(n)) /\ summable g ==>
            summable f"
   (REPEAT GEN_TAC THEN REWRITE_TAC [SER_CAUCHY, GE] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q "N1:num")) MP_TAC) THEN
    REWRITE_TAC [SER_CAUCHY, GE] THEN DISCH_TAC THEN
    X_GEN_TAC (← q "e:real") THEN DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q "N2:num")) THEN EXISTS_TAC (← q "N1 + N2:num") THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC (← q r"sum(m,n)(\k. abs(f k))") THEN REWRITE_TAC [ABS_SUM] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q r"sum(m,n) g") THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN BETA_TAC THEN
      X_GEN_TAC (← q "p:num") THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q "m:num") THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC (← q "N1 + N2:num") THEN ASM_REWRITE_TAC [LE_ADD], ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q r"abs(sum(m,n) g)") THEN
    REWRITE_TAC [ABS_LE] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q "N1 + N2:num") THEN
    ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [ADD_SYM] THEN
    REWRITE_TAC [LE_ADD])

  let SER_COMPARA ← prove
   r"!f g. (?N. !n. n >= N ==> abs(f(n)) <= g(n)) /\ summable g ==>
            summable (\k. abs(f k))"
   (REPEAT GEN_TAC THEN SUBGOAL_THEN (← q r"!n. abs(f(n)) = abs((\k:num. abs(f k)) n)")
    (fun th => GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [th])
    THENL
     [GEN_TAC THEN BETA_TAC THEN REWRITE_TAC [ABS_ABS],
      MATCH_ACCEPT_TAC SER_COMPAR])

  let SER_LE ← prove
   r"!f g. (!n. f(n) <= g(n)) /\ summable f /\ summable g
        ==> suminf f <= suminf g"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN (fun th => tactic_of do
      pure (ASSUME_TAC th THEN ASSUME_TAC
        (← REWRITE_RULE [sums] (← MATCH_MP SUMMABLE_SUM th))))) THEN
    MATCH_MP_TAC SEQ_LE THEN REWRITE_TAC [CONJ_ASSOC] THEN
    MAP_EVERY EXISTS_TAC [← q r"\n. sum(0,n) f", ← q r"\n. sum(0,n) g"] THEN CONJ_TAC THENL
     [REWRITE_TAC [← GSYM sums] THEN CONJ_TAC THEN
      MATCH_MP_TAC SUMMABLE_SUM THEN FIRST_ASSUM ACCEPT_TAC,
      EXISTS_TAC (← q "0") THEN REWRITE_TAC [GE, LE_0] THEN
      GEN_TAC THEN BETA_TAC THEN MATCH_MP_TAC SUM_LE THEN
      GEN_TAC THEN ASM_REWRITE_TAC [LE_0]])

  let SER_LE2 ← prove
   r"!f g. (!n. abs(f n) <= g(n)) /\ summable g ==>
                summable f /\ suminf f <= suminf g"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q "summable f") ASSUME_TAC THENL
     [MATCH_MP_TAC SER_COMPAR THEN EXISTS_TAC (← q r"g:num->real") THEN
      ASM_REWRITE_TAC [], ASM_REWRITE_TAC []] THEN
    MATCH_MP_TAC SER_LE THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q "n:num") THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"abs(f(n:num))") THEN ASM_REWRITE_TAC [ABS_LE])

  let SER_ACONV ← prove
   r"!f. summable (\n. abs(f n)) ==> summable f"
   (← do
    let eR ← q "e:real"
    pure (GEN_TAC THEN REWRITE_TAC [SER_CAUCHY] THEN REWRITE_TAC [SUM_ABS] THEN
      DISCH_THEN (fun th => X_GEN_TAC eR THEN DISCH_TAC THEN MP_TAC th) THEN
      DISCH_THEN (IMP_RES_THEN (X_CHOOSE_TAC (← q "N:num"))) THEN
      EXISTS_TAC (← q "N:num") THEN REPEAT GEN_TAC THEN
      DISCH_THEN (ANTE_RES_THEN ASSUME_TAC) THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC (← q r"sum(m,n)(\m. abs(f m))") THEN ASM_REWRITE_TAC [ABS_SUM]))

  let SER_ABS ← prove
   r"!f. summable(\n. abs(f n)) ==> abs(suminf f) <= suminf(\n. abs(f n))"
   (GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP SUMMABLE_SUM o MATCH_MP SER_ACONV) THEN
    POP_ASSUM (MP_TAC o MATCH_MP SUMMABLE_SUM) THEN
    REWRITE_TAC [sums] THEN DISCH_TAC THEN
    DISCH_THEN (ASSUME_TAC o BETA_RULE o MATCH_MP SEQ_ABS_IMP) THEN
    MATCH_MP_TAC SEQ_LE THEN MAP_EVERY EXISTS_TAC
     [← q r"\n. abs(sum(0,n)f)", ← q r"\n. sum(0,n)(\n. abs(f n))"] THEN
    ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q "0") THEN X_GEN_TAC (← q "n:num") THEN
    DISCH_THEN (fun _ => ALL_TAC) THEN BETA_TAC THEN MATCH_ACCEPT_TAC SUM_ABS_LE)

  let GP_FINITE ← prove
   r"!x. ~(x = &1) ==>
        !n. (sum(0,n) (\n. x pow n) = ((x pow n) - &1) / (x - &1))"
   (GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
     [REWRITE_TAC [sum, pow, REAL_SUB_REFL, REAL_DIV_LZERO],
      REWRITE_TAC [sum, pow] THEN BETA_TAC THEN
      ASM_REWRITE_TAC [ADD_CLAUSES] THEN
      SUBGOAL_THEN (← q r"~(x - &1 = &0)") ASSUME_TAC THEN
      ASM_REWRITE_TAC [REAL_SUB_0] THEN
      MP_TAC (← GENL [← q "p:real", ← q "q:real"]
       (← SPECL [← q "p:real", ← q "q:real", ← q r"x - &1"] REAL_EQ_RMUL)) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => tactic_of do pure (ONCE_REWRITE_TAC [← GSYM th])) THEN
      REWRITE_TAC [REAL_RDISTRIB] THEN SUBGOAL_THEN
        (← q r"!p. (p / (x - &1)) * (x - &1) = p") (fun th => REWRITE_TAC [th]) THENL
        [GEN_TAC THEN MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REWRITE_TAC [], ALL_TAC]
      THEN REWRITE_TAC [REAL_SUB_LDISTRIB] THEN REWRITE_TAC [real_sub] THEN
      ONCE_REWRITE_TAC [← AC REAL_ADD_AC
        (← q r"(a + b) + (c + d) = (c + b) + (d + a)")] THEN
      REWRITE_TAC [REAL_MUL_RID, REAL_ADD_LINV, REAL_ADD_RID] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_MUL_SYM])

  let GP ← prove
   r"!x. abs(x) < &1 ==> (\n. x pow n) sums inv(&1 - x)"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"x = &1") THEN
    ASM_REWRITE_TAC [ABS_1, REAL_LT_REFL] THEN DISCH_TAC THEN
    REWRITE_TAC [sums] THEN
    FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP GP_FINITE th])) THEN
    REWRITE_TAC [REAL_INV_1OVER] THEN REWRITE_TAC [real_div] THEN
    GEN_REWRITE_TAC (LAND_CONV o ABS_CONV) [← GSYM REAL_NEG_MUL2] THEN
    SUBGOAL_THEN (← q r"~(x - &1 = &0)")
      (fun t => tactic_of do pure (REWRITE_TAC [← MATCH_MP REAL_NEG_INV t])) THENL
      [ASM_REWRITE_TAC [REAL_SUB_0], ALL_TAC] THEN
    REWRITE_TAC [REAL_NEG_SUB, ← GSYM real_div] THEN
    SUBGOAL_THEN (← q r"(\n. (\n. &1 - x pow n) n / (\n. &1 - x) n) --> &1 / (&1 - x)")
    MP_TAC THENL [ALL_TAC, REWRITE_TAC [BETA_THM]] THEN
    MATCH_MP_TAC SEQ_DIV THEN BETA_TAC THEN REWRITE_TAC [SEQ_CONST] THEN
    REWRITE_TAC [REAL_SUB_0] THEN CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
    ASM_REWRITE_TAC [] THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_SUB_RZERO] THEN
    SUBGOAL_THEN (← q r"(\n. (\n. &1) n - (\n. x pow n) n) --> &1 - &0")
    MP_TAC THENL [ALL_TAC, REWRITE_TAC [BETA_THM]] THEN
    MATCH_MP_TAC SEQ_SUB THEN BETA_TAC THEN REWRITE_TAC [SEQ_CONST] THEN
    MATCH_MP_TAC SEQ_POWER THEN FIRST_ASSUM ACCEPT_TAC)

  let ABS_NEG_LEMMA ← prove
   r"!c x y. c <= &0 ==> abs(x) <= c * abs(y) ==> (x = &0)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM REAL_NEG_GE0] THEN DISCH_TAC THEN
    MP_TAC (← SPECL [← q "--c", ← q "abs(y)"] REAL_LE_MUL) THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [ABS_POS, ← GSYM REAL_NEG_LMUL, REAL_NEG_GE0] THEN
    DISCH_THEN (fun th => DISCH_THEN (MP_TAC o (fun a => CONJ a th))) THEN
    DISCH_THEN (MP_TAC o MATCH_MP REAL_LE_TRANS) THEN CONV_TAC CONTRAPOS_CONV THEN
    REWRITE_TAC [ABS_NZ, REAL_NOT_LE])

  let SER_RATIO ← prove
   r"!f c N. c < &1 /\
           (!n. n >= N ==> abs(f(SUC n)) <= c * abs(f(n))) ==>
       summable f"
   (← do
    let lec ← MATCH_MP REAL_LT_IMP_LE (← ASSUME (← q r"&0 < c"))
    pure (REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
      DISJ_CASES_TAC (← SPECL [← q "c:real", ← q r"&0"] REAL_LET_TOTAL) THENL
       [REWRITE_TAC [SER_CAUCHY] THEN X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN
        SUBGOAL_THEN (← q r"!n. n >= N ==> (f(SUC n) = &0)") ASSUME_TAC THENL
         [GEN_TAC THEN DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN
          MATCH_MP_TAC ABS_NEG_LEMMA THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
        SUBGOAL_THEN (← q r"!n. n >= (SUC N) ==> (f(n) = &0)") ASSUME_TAC THENL
         [GEN_TAC THEN STRUCT_CASES_TAC (← SPEC (← q "n:num") num_CASES) THENL
           [REWRITE_TAC [GE] THEN DISCH_THEN (MP_TAC o MATCH_MP OR_LESS) THEN
            REWRITE_TAC [NOT_LESS_0],
            REWRITE_TAC [GE, LE_SUC] THEN
            ASM_REWRITE_TAC [← GSYM GE]], ALL_TAC] THEN
        EXISTS_TAC (← q "SUC N") THEN FIRST_ASSUM (ASSUME_TAC o MATCH_MP SUM_ZERO) THEN
        REPEAT GEN_TAC THEN
        DISCH_THEN (ANTE_RES_THEN (fun th => REWRITE_TAC [th])) THEN
        ASM_REWRITE_TAC [ABS_0],

        MATCH_MP_TAC SER_COMPAR THEN
        EXISTS_TAC (← q r"\n. (abs(f N) / c pow N) * (c pow n)") THEN CONJ_TAC THENL
         [EXISTS_TAC (← q "N:num") THEN X_GEN_TAC (← q "n:num") THEN
          REWRITE_TAC [GE] THEN
          DISCH_THEN (X_CHOOSE_THEN (← q "d:num") SUBST1_TAC o MATCH_MP LESS_EQUAL_ADD)
          THEN BETA_TAC THEN REWRITE_TAC [POW_ADD] THEN REWRITE_TAC [real_div] THEN
          ONCE_REWRITE_TAC [← AC REAL_MUL_AC
            (← q r"(a * b) * (c * d) = (a * d) * (b * c)")] THEN
          SUBGOAL_THEN (← q r"~(c pow N = &0)")
            (fun th => tactic_of do
              pure (REWRITE_TAC [← MATCH_MP REAL_MUL_LINV th, REAL_MUL_RID])) THENL
           [MATCH_MP_TAC POW_NZ THEN CONV_TAC (RAND_CONV SYM_CONV) THEN
            MATCH_MP_TAC REAL_LT_IMP_NE THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
          SPEC_TAC (← q "d:num", ← q "d:num") THEN INDUCT_TAC THEN
          REWRITE_TAC [pow, ADD_CLAUSES, REAL_MUL_RID, REAL_LE_REFL] THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"c * abs(f(N + d:num))") THEN
          CONJ_TAC THENL
           [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [GE, LE_ADD],
            ONCE_REWRITE_TAC [← AC REAL_MUL_AC
              (← q r"a * (b * c) = b * (a * c)")] THEN
            FIRST_ASSUM (fun th => tactic_of do
              pure (ASM_REWRITE_TAC [← MATCH_MP REAL_LE_LMUL_LOCAL th]))],

          REWRITE_TAC [summable] THEN
          EXISTS_TAC (← q r"(abs(f(N:num)) / (c pow N)) * inv(&1 - c)") THEN
          MATCH_MP_TAC SER_CMUL THEN MATCH_MP_TAC GP THEN
          ASSUME_TAC lec THEN
          ASM_REWRITE_TAC [real_abs]]]))

  let SEQ_TRUNCATION ← prove
   r"!f l n b.
        f sums l /\ (!m. abs(sum(n,m) f) <= b)
        ==> abs(l - sum(0,n) f) <= b"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
    DISCH_THEN (MP_TAC o SPEC (← q "n:num") o MATCH_MP SER_OFFSET) THEN
    REWRITE_TAC [sums] THEN
    FIRST_ASSUM (SUBST1_TAC o SYM o MATCH_MP SUM_UNIQ) THEN
    DISCH_THEN (ASSUME_TAC o MATCH_MP SEQ_ABS_IMP) THEN
    MATCH_MP_TAC SEQ_LE THEN
    REWRITE_TAC [RIGHT_EXISTS_AND_THM] THEN
    FIRST_ASSUM (fun th => tactic_of do
      let l ← liftExcept (lhand (concl th))
      pure (EXISTS_TAC l THEN
            CONJ_TAC THENL [ACCEPT_TAC th, ALL_TAC])) THEN
    EXISTS_TAC (← q r"\r:num. b:real") THEN REWRITE_TAC [SEQ_CONST] THEN
    ASM_REWRITE_TAC [← GSYM SUM_REINDEX, ADD_CLAUSES])

  -- @@RETURN BEGIN
  return { SER_POS_LT_PAIR, SER_ADD, SER_CMUL, SER_NEG, SER_SUB, SER_CDIV, SER_CAUCHY,
           SER_ZERO, SER_COMPAR, SER_COMPARA, SER_LE, SER_LE2, SER_ACONV, SER_ABS,
           GP_FINITE, GP, ABS_NEG_LEMMA, SER_RATIO, SEQ_TRUNCATION }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Limits of real->real functions; differentiation and continuity defined;   -/
/- combining theorems for continuity.  (analysis.ml 4661-4925)               -/
/- ------------------------------------------------------------------------- -/

structure Lims where
  -- @@FIELDS
  tends_real_real : thm
  LIM : thm
  LIM_CONST : thm
  LIM_ADD : thm
  LIM_MUL : thm
  LIM_NEG : thm
  LIM_INV : thm
  LIM_SUB : thm
  LIM_DIV : thm
  LIM_NULL : thm
  LIM_SUM : thm
  LIM_X : thm
  LIM_UNIQ : thm
  LIM_EQUAL : thm
  LIM_TRANSFORM : thm
  diffl : thm
  contl : thm
  differentiable : thm
  DIFF_UNIQ : thm
  DIFF_CONT : thm
  CONTL_LIM : thm
  CONT_X : thm
  CONT_CONST : thm
  CONT_ADD : thm
  CONT_MUL : thm
  CONT_NEG : thm
  CONT_INV : thm
  CONT_SUB : thm
  CONT_DIV : thm
  CONT_ABS : thm
  CONT_COMPOSE : thm
  deriving Inhabited

@[nospecialize]
def setupLims [HolBase] (D : AnalysisDeps) (BTactics : Tactics) (BReals1 : Reals1) (BReals2 : Reals2) (BReals3 : Reals3) (BAbs : Abs) (BTopology : Topology) (BMetricTop : MetricTop) (BNets : Nets) (BNetArith : NetArith) :
    ExceptT String IO Lims := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, REAL_ARITH, new_definition, override_interface, parse_as_infix, .. } := D
  let { REAL_ADD_SUB, .. } := D.core1
  let { REAL_DIV_RMUL, REAL_DOWN2, REAL_LET_TRANS, REAL_LT_TRANS, .. } := D.core2
  let { RIGHT_IMP_FORALL_THM, .. } := D.core3
  let { EXACT_CONV, X_BETA_CONV, .. } := BTactics
  let { REAL_LE_REFL, REAL_LTE_TRANS, REAL_LT_ADD2, REAL_MUL_RZERO, REAL_SUB_ADD2, .. } := BReals1
  let { REAL_LT_HALF1, REAL_SUB_0, REAL_SUB_REFL, .. } := BReals2
  let { REAL_HALF_DOUBLE, REAL_SUB_RZERO, REAL_SUB_TRIANGLE, .. } := BReals3
  let { ABS_0, ABS_NZ, ABS_SUB, ABS_TRIANGLE, .. } := BAbs
  let { METRIC_SAME, .. } := BTopology
  let { MR1_DEF, MR1_LIMPT, MTOP_LIMPT, .. } := BMetricTop
  let { DORDER_TENDSTO, LIM_TENDS2, MTOP_TENDS, MTOP_TENDS_UNIQ, NET_NULL, tendsto, .. } := BNets
  let { NET_ADD, NET_DIV, NET_INV, NET_MUL, NET_NEG, NET_SUB, NET_SUM, .. } := BNetArith
  -- @@SCOPE END
  parse_as_infix ("tends_real_real", (12, "right"))

  parse_as_infix ("diffl", (12, "right"))
  parse_as_infix ("contl", (12, "right"))
  parse_as_infix ("differentiable", (12, "right"))

  let tends_real_real ← new_definition
   r"(f tends_real_real l)(x0) <=>
        (f tends l)(mtop(mr1),tendsto(mr1,x0))"

  override_interface "-->" (← q "(tends_real_real)")

  let LIM ← prove
   r"!f y0 x0. (f --> y0)(x0) <=>
        !e. &0 < e ==>
            ?d. &0 < d /\ !x. &0 < abs(x - x0) /\ abs(x - x0) < d ==>
                abs(f(x) - y0) < e"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [tends_real_real, ← MATCH_MP LIM_TENDS2 (← SPEC (← q "x0:real") MR1_LIMPT)]
    THEN REWRITE_TAC [MR1_DEF] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ABS_SUB] THEN
    REFL_TAC)

  let LIM_CONST ← prove
   r"!k x. ((\x. k) --> k)(x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [tends_real_real, MTOP_TENDS] THEN
    GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [METRIC_SAME] THEN
    REWRITE_TAC [tendsto, REAL_LE_REFL] THEN
    MP_TAC (← REWRITE_RULE [MTOP_LIMPT] (← SPEC (← q "x:real") MR1_LIMPT)) THEN
    DISCH_THEN (MP_TAC o SPEC (← q "e:real")) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "z:real") (ASSUME_TAC o CONJUNCT1)) THEN
    EXISTS_TAC (← q "z:real") THEN REWRITE_TAC [MR1_DEF, ← GSYM ABS_NZ] THEN
    REWRITE_TAC [REAL_SUB_0] THEN CONV_TAC (RAND_CONV SYM_CONV) THEN
    ASM_REWRITE_TAC [])

  let LIM_ADD ← prove
   r"!f g l m. (f --> l)(x) /\ (g --> m)(x) ==>
      ((\x. f(x) + g(x)) --> (l + m))(x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [tends_real_real] THEN
    MATCH_MP_TAC NET_ADD THEN MATCH_ACCEPT_TAC DORDER_TENDSTO)

  let LIM_MUL ← prove
   r"!f g l m. (f --> l)(x) /\ (g --> m)(x) ==>
      ((\x. f(x) * g(x)) --> (l * m))(x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [tends_real_real] THEN
    MATCH_MP_TAC NET_MUL THEN MATCH_ACCEPT_TAC DORDER_TENDSTO)

  let LIM_NEG ← prove
   r"!f l. (f --> l)(x) <=> ((\x. --(f(x))) --> --l)(x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [tends_real_real] THEN
    MATCH_MP_TAC NET_NEG THEN MATCH_ACCEPT_TAC DORDER_TENDSTO)

  let LIM_INV ← prove
   r"!f l. (f --> l)(x) /\ ~(l = &0) ==>
        ((\x. inv(f(x))) --> inv l)(x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [tends_real_real] THEN
    MATCH_MP_TAC NET_INV THEN MATCH_ACCEPT_TAC DORDER_TENDSTO)

  let LIM_SUB ← prove
   r"!f g l m. (f --> l)(x) /\ (g --> m)(x) ==>
      ((\x. f(x) - g(x)) --> (l - m))(x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [tends_real_real] THEN
    MATCH_MP_TAC NET_SUB THEN MATCH_ACCEPT_TAC DORDER_TENDSTO)

  let LIM_DIV ← prove
   r"!f g l m. (f --> l)(x) /\ (g --> m)(x) /\ ~(m = &0) ==>
      ((\x. f(x) / g(x)) --> (l / m))(x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [tends_real_real] THEN
    MATCH_MP_TAC NET_DIV THEN MATCH_ACCEPT_TAC DORDER_TENDSTO)

  let LIM_NULL ← prove
   r"!f l x. (f --> l)(x) <=> ((\x. f(x) - l) --> &0)(x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [tends_real_real] THEN
    MATCH_ACCEPT_TAC NET_NULL)

  let LIM_SUM ← prove
   r"!f l m n x.
      (!r. m <= r /\ r < m + n ==> (f r --> l r)(x))
      ==> ((\x. sum(m,n) (\r. f r x)) --> sum(m,n) l)(x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [tends_real_real] THEN
    MATCH_MP_TAC (← REWRITE_RULE [RIGHT_IMP_FORALL_THM] NET_SUM) THEN
    REWRITE_TAC [LIM_CONST, DORDER_TENDSTO, ← GSYM tends_real_real])

  let LIM_X ← prove
   r"!x0. ((\x. x) --> x0)(x0)"
   (GEN_TAC THEN REWRITE_TAC [LIM] THEN X_GEN_TAC (← q "e:real") THEN
    DISCH_TAC THEN EXISTS_TAC (← q "e:real") THEN ASM_REWRITE_TAC [] THEN
    BETA_TAC THEN GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [])

  let LIM_UNIQ ← prove
   r"!f l m x. (f --> l)(x) /\ (f --> m)(x) ==> (l = m)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [tends_real_real] THEN
    MATCH_MP_TAC MTOP_TENDS_UNIQ THEN
    MATCH_ACCEPT_TAC DORDER_TENDSTO)

  let LIM_EQUAL ← prove
   r"!f g l x0. (!x. ~(x = x0) ==> (f x = g x)) ==>
        ((f --> l)(x0) <=> (g --> l)(x0))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [LIM] THEN DISCH_TAC THEN
    AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN ABS_TAC THEN
    ONCE_REWRITE_TAC [← TAUT (← q r"(a ==> b <=> a ==> c) <=> a ==> (b <=> c)")] THEN
    DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC [← GSYM REAL_SUB_0] THEN
    ASM_REWRITE_TAC [ABS_NZ])

  let LIM_TRANSFORM ← prove
   r"!f g x0 l. ((\x. f(x) - g(x)) --> &0)(x0) /\ (g --> l)(x0)
        ==> (f --> l)(x0)"
   (← do
    let eR ← q "e:real"
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [LIM] THEN
      DISCH_THEN (fun th => X_GEN_TAC eR THEN DISCH_TAC THEN MP_TAC th) THEN
      DISCH_THEN (CONJUNCTS_THEN (MP_TAC o SPEC (← q r"e / &2"))) THEN
      ASM_REWRITE_TAC [REAL_LT_HALF1] THEN BETA_TAC THEN
      REWRITE_TAC [REAL_SUB_RZERO] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "d:real") STRIP_ASSUME_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "c:real") STRIP_ASSUME_TAC) THEN
      MP_TAC (← SPECL [← q "c:real", ← q "d:real"] REAL_DOWN2) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "b:real") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q "b:real") THEN ASM_REWRITE_TAC [] THEN
      X_GEN_TAC (← q "x:real") THEN DISCH_THEN STRIP_ASSUME_TAC THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q r"(e / &2) + (e / &2)") THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REAL_HALF_DOUBLE] THEN
      REWRITE_TAC [REAL_LE_REFL] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC (← q r"abs(f(x:real) - g(x)) + abs(g(x) - l)") THEN
      SUBST1_TAC (← SYM (← SPECL
        [← q r"(f:real->real) x", ← q r"(g:real->real) x", ← q "l:real"] REAL_SUB_TRIANGLE)) THEN
      REWRITE_TAC [ABS_TRIANGLE] THEN MATCH_MP_TAC REAL_LT_ADD2 THEN
      CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (← q "b:real") THEN
      ASM_REWRITE_TAC []))

  let diffl ← new_definition
   r"(f diffl l)(x) <=> ((\h. (f(x+h) - f(x)) / h) --> l)(&0)"

  let contl ← new_definition
   r"f contl x <=> ((\h. f(x + h)) --> f(x))(&0)"

  let differentiable ← new_definition
   r"f differentiable x <=> ?l. (f diffl l)(x)"

  let DIFF_UNIQ ← prove
   r"!f l m x. (f diffl l)(x) /\ (f diffl m)(x) ==> (l = m)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [diffl] THEN
    MATCH_ACCEPT_TAC LIM_UNIQ)

  let DIFF_CONT ← prove
   r"!f l x. (f diffl l)(x) ==> f contl x"
   (REPEAT GEN_TAC THEN REWRITE_TAC [diffl, contl] THEN DISCH_TAC THEN
    REWRITE_TAC [tends_real_real] THEN ONCE_REWRITE_TAC [NET_NULL] THEN
    REWRITE_TAC [← GSYM tends_real_real] THEN BETA_TAC THEN
    SUBGOAL_THEN (← q r"((\h. f(x + h) - f(x)) --> &0)(&0) <=>
                  ((\h. ((f(x + h) - f(x)) / h) * h) --> &0)(&0)") SUBST1_TAC
    THENL
     [MATCH_MP_TAC LIM_EQUAL THEN
      X_GEN_TAC (← q "z:real") THEN BETA_TAC THEN
      DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP REAL_DIV_RMUL th])),
      ALL_TAC] THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ABS_CONV o RAND_CONV)
      [← SYM (← ExceptT.mk (BETA_CONV (← q r"(\h:real. h) h")))] THEN
    CONV_TAC (← EXACT_CONV [← ExceptT.mk (X_BETA_CONV (← q "h:real") (← q r"(f(x + h) - f(x)) / h"))]) THEN
    SUBST1_TAC (← SYM (← SPEC (← q "l:real") REAL_MUL_RZERO)) THEN
    MATCH_MP_TAC LIM_MUL THEN BETA_TAC THEN REWRITE_TAC [REAL_MUL_RZERO] THEN
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [LIM] THEN BETA_TAC THEN
    REWRITE_TAC [REAL_SUB_RZERO] THEN
    X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN EXISTS_TAC (← q "e:real") THEN
    ASM_REWRITE_TAC [] THEN GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [])

  let CONTL_LIM ← prove
   r"!f x. f contl x <=> (f --> f(x))(x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [contl, LIM] THEN
    AP_TERM_TAC THEN ABS_TAC THEN
    ONCE_REWRITE_TAC [← TAUT (← q r"(a ==> b <=> a ==> c) <=> a ==> (b <=> c)")] THEN
    DISCH_TAC THEN BETA_TAC THEN REWRITE_TAC [REAL_SUB_RZERO] THEN
    EQ_TAC THEN DISCH_THEN (X_CHOOSE_THEN (← q "d:real") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q "d:real") THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q "k:real") THENL
     [DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN REWRITE_TAC [REAL_SUB_ADD2],
      DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [REAL_ADD_SUB]])

  let CONT_X ← prove
   r"!x. (\x. x) contl x"
   (REWRITE_TAC [CONTL_LIM, LIM_X])

  let CONT_CONST ← prove
   r"!x. (\x. k) contl x"
   (REPEAT GEN_TAC THEN REWRITE_TAC [CONTL_LIM] THEN
    MATCH_ACCEPT_TAC LIM_CONST)

  let CONT_ADD ← prove
   r"!x. f contl x /\ g contl x ==> (\x. f(x) + g(x)) contl x"
   (GEN_TAC THEN REWRITE_TAC [CONTL_LIM] THEN BETA_TAC THEN
    MATCH_ACCEPT_TAC LIM_ADD)

  let CONT_MUL ← prove
   r"!x. f contl x /\ g contl x ==> (\x. f(x) * g(x)) contl x"
   (GEN_TAC THEN REWRITE_TAC [CONTL_LIM] THEN BETA_TAC THEN
    MATCH_ACCEPT_TAC LIM_MUL)

  let CONT_NEG ← prove
   r"!x. f contl x ==> (\x. --(f(x))) contl x"
   (GEN_TAC THEN REWRITE_TAC [CONTL_LIM] THEN BETA_TAC THEN
    REWRITE_TAC [← GSYM LIM_NEG])

  let CONT_INV ← prove
   r"!x. f contl x /\ ~(f x = &0) ==> (\x. inv(f(x))) contl x"
   (GEN_TAC THEN REWRITE_TAC [CONTL_LIM] THEN BETA_TAC THEN
    MATCH_ACCEPT_TAC LIM_INV)

  let CONT_SUB ← prove
   r"!x. f contl x /\ g contl x ==> (\x. f(x) - g(x)) contl x"
   (GEN_TAC THEN REWRITE_TAC [CONTL_LIM] THEN BETA_TAC THEN
    MATCH_ACCEPT_TAC LIM_SUB)

  let CONT_DIV ← prove
   r"!x. f contl x /\ g contl x /\ ~(g x = &0) ==>
        (\x. f(x) / g(x)) contl x"
   (GEN_TAC THEN REWRITE_TAC [CONTL_LIM] THEN BETA_TAC THEN
    MATCH_ACCEPT_TAC LIM_DIV)

  let CONT_ABS ← prove
   r"!f x. f contl x ==> (\x. abs(f x)) contl x"
   (REWRITE_TAC [CONTL_LIM, LIM] THEN
    MESON_TAC [← REAL_ARITH (← q r"abs(a - b) < e ==> abs(abs a - abs b) < e")])

  let CONT_COMPOSE ← prove
   r"!f g x. f contl x /\ g contl (f x) ==> (\x. g(f x)) contl x"
   (REPEAT GEN_TAC THEN REWRITE_TAC [contl, LIM, REAL_SUB_RZERO] THEN
    BETA_TAC THEN DISCH_TAC THEN X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN
    FIRST_ASSUM (undischCheck (fun c => pure (is_conj c))) THEN
    DISCH_THEN (CONJUNCTS_THEN MP_TAC) THEN
    DISCH_THEN (fun th => FIRST_ASSUM (MP_TAC o MATCH_MP th)) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "d:real") STRIP_ASSUME_TAC) THEN
    DISCH_THEN (MP_TAC o SPEC (← q "d:real")) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "c:real") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q "c:real") THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q "h:real") THEN DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN
    ASM_CASES_TAC (← q r"&0 < abs(f(x + h) - f(x))") THENL
     [UNDISCH_TAC (← q r"&0 < abs(f(x + h) - f(x))") THEN
      DISCH_THEN (fun th => DISCH_THEN (MP_TAC o CONJ th)) THEN
      DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN REWRITE_TAC [REAL_SUB_ADD2],
      UNDISCH_TAC (← q r"~(&0 < abs(f(x + h) - f(x)))") THEN
      REWRITE_TAC [← GSYM ABS_NZ, REAL_SUB_0] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC [REAL_SUB_REFL, ABS_0]])

  -- @@RETURN BEGIN
  return { tends_real_real, LIM, LIM_CONST, LIM_ADD, LIM_MUL, LIM_NEG, LIM_INV, LIM_SUB,
           LIM_DIV, LIM_NULL, LIM_SUM, LIM_X, LIM_UNIQ, LIM_EQUAL, LIM_TRANSFORM, diffl,
           contl, differentiable, DIFF_UNIQ, DIFF_CONT, CONTL_LIM, CONT_X, CONT_CONST,
           CONT_ADD, CONT_MUL, CONT_NEG, CONT_INV, CONT_SUB, CONT_DIV, CONT_ABS,
           CONT_COMPOSE }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Intermediate value theorem; combining theorems for differentiation; the   -/
/- chain rule; powers, inverses, quotients, finite sums.                     -/
/- (analysis.ml 4971-5338)                                                   -/
/- ------------------------------------------------------------------------- -/

structure Diffs where
  -- @@FIELDS
  IVT : thm
  IVT2 : thm
  DIFF_CONST : thm
  DIFF_ADD : thm
  DIFF_MUL : thm
  DIFF_CMUL : thm
  DIFF_NEG : thm
  DIFF_SUB : thm
  DIFF_CARAT : thm
  DIFF_CHAIN : thm
  DIFF_X : thm
  DIFF_POW : thm
  DIFF_XM1 : thm
  DIFF_INV : thm
  DIFF_DIV : thm
  DIFF_SUM : thm
  deriving Inhabited

@[nospecialize]
def setupDiffs [HolBase] (D : AnalysisDeps) (BCompat : Compat) (BNames : Names) (BTactics : Tactics) (BReals1 : Reals1) (BReals2 : Reals2) (BReals3 : Reals3) (BAbs : Abs) (BPow : Pow) (BSums : Sums) (BSeries1 : Series1) (BLims : Lims) :
    ExceptT String IO Diffs := do
  -- @@SCOPE BEGIN
  let { GEN_BETA_CONV, INDUCT_TAC, num_CONV, .. } := D
  let { ADD1, ADD_CLAUSES, ADD_SUB, DE_MORGAN_THM, EQ_IMP, LE_ADD, LT_TRANS, NOT_IMP,
        REAL_ADD2_SUB2, REAL_ADD_AC, REAL_ADD_LID, REAL_ADD_LINV, REAL_ADD_RID,
        REAL_ADD_SUB, REAL_ADD_SYM, .. } := D.core1
  let { REAL_DIV_REFL, REAL_DIV_RMUL, REAL_ENTIRE, REAL_LET_TRANS, REAL_LT_REFL,
        REAL_LT_TOTAL, REAL_MUL_AC, REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LINV, .. } := D.core2
  let { REAL_MUL_SYM, num_CASES, real_abs, real_div, real_sub, .. } := D.core3
  let { NOT_EXISTS_CONV, .. } := BCompat
  let { LESS_SUC_REFL, .. } := BNames
  let { EXACT_CONV, HABS_CONV, X_BETA_CONV, .. } := BTactics
  let { REAL_ADD_RID_UNIQ, REAL_LDISTRIB, REAL_LE_LADD, REAL_LE_RADD, REAL_LE_REFL,
        REAL_LE_TOTAL, REAL_LE_TRANS, REAL_LNEG_UNIQ, REAL_LT_01, REAL_LT_IMP_LE,
        REAL_LT_LE, REAL_MUL_LZERO, REAL_MUL_RID, REAL_MUL_RINV, REAL_MUL_RZERO,
        REAL_NEG_LMUL, REAL_NEG_NEG, REAL_NEG_RMUL, REAL_NOT_LE, REAL_NOT_LT,
        REAL_RDISTRIB, REAL_SUB_ADD, .. } := BReals1
  let { REAL, REAL_EQ_LMUL, REAL_NEG_EQ, REAL_NEG_MINUS1, REAL_NEG_SUB, REAL_SUB_0,
        REAL_SUB_LDISTRIB, REAL_SUB_LE, REAL_SUB_LT, REAL_SUB_RDISTRIB, REAL_SUB_REFL, .. } := BReals2
  let { REAL_INV_MUL_WEAK, REAL_LE_NEG2, REAL_SUB_RZERO, .. } := BReals3
  let { ABS_0, ABS_NEG, ABS_NZ, ABS_SUB, ABS_ZERO, .. } := BAbs
  let { POW_2, POW_ADD, POW_INV, pow, .. } := BPow
  let { sum, .. } := BSums
  let { BOLZANO_LEMMA, .. } := BSeries1
  let { CONT_COMPOSE, CONT_MUL, CONT_NEG, DIFF_CONT, LIM, LIM_ADD, LIM_CONST,
        LIM_EQUAL, LIM_INV, LIM_MUL, LIM_NEG, LIM_TRANSFORM, LIM_X, contl, diffl, .. } := BLims
  -- @@SCOPE END
  let numc (s : String) : ExceptT String IO thm := do ExceptT.mk (num_CONV (← q s))
  let xbeta (v : term) (t : term) : ExceptT String IO thm := ExceptT.mk (X_BETA_CONV v t)
  -- `W(C SUBGOAL_THEN ttac o funpow 2 (fst o dest_imp) o snd)`
  let subgoalAnte2 (ttac : thm_tactic) : tactic := fun gl => ExceptT.run do
    let t ← liftExcept (funpow 2 (fun (m : Except String term) => do
      pure (← dest_imp (← m)).1) (pure gl.2))
    ExceptT.mk (SUBGOAL_THEN t ttac gl)

  let IVT ← prove
   r"!f a b y. a <= b /\
             (f(a) <= y /\ y <= f(b)) /\
             (!x. a <= x /\ x <= b ==> f contl x)
        ==> (?x. a <= x /\ x <= b /\ (f(x) = y))"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
    CONV_TAC CONTRAPOS_CONV THEN
    DISCH_THEN (ASSUME_TAC o CONV_RULE NOT_EXISTS_CONV) THEN
    MP_TAC (← SPEC
      (← q r"\(u,v). a <= u /\ u <= v /\ v <= b ==> ~(f(u) <= y /\ y <= f(v))")
      BOLZANO_LEMMA) THEN
    CONV_TAC (ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    subgoalAnte2 (fun t => REWRITE_TAC [t]) THENL
     [ALL_TAC,
      DISCH_THEN (MP_TAC o SPECL [← q "a:real", ← q "b:real"]) THEN
      ASM_REWRITE_TAC [REAL_LE_REFL]] THEN
    CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [← q "u:real", ← q "v:real", ← q "w:real"] THEN
      CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC [DE_MORGAN_THM, NOT_IMP] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      MAP_EVERY ASM_CASES_TAC [← q "u <= v", ← q "v <= w"] THEN ASM_REWRITE_TAC [] THEN
      DISJ_CASES_TAC (← SPECL [← q "y:real", ← q r"(f:real->real) v"] REAL_LE_TOTAL) THEN
      ASM_REWRITE_TAC [] THENL [DISJ1_TAC, DISJ2_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THENL
       [EXISTS_TAC (← q "w:real"), EXISTS_TAC (← q "u:real")] THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    X_GEN_TAC (← q "x:real") THEN ASM_CASES_TAC (← q r"a <= x /\ x <= b") THENL
     [ALL_TAC,
      EXISTS_TAC (← q r"&1") THEN REWRITE_TAC [REAL_LT_01] THEN
      MAP_EVERY X_GEN_TAC [← q "u:real", ← q "v:real"] THEN
      REPEAT STRIP_TAC THEN UNDISCH_TAC (← q r"~(a <= x /\ x <= b)") THEN
      REWRITE_TAC [] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
       [EXISTS_TAC (← q "u:real"), EXISTS_TAC (← q "v:real")] THEN
      ASM_REWRITE_TAC []] THEN
    UNDISCH_TAC (← q r"!x. ~(a <= x /\ x <= b /\ (f(x) = (y:real)))") THEN
    DISCH_THEN (MP_TAC o SPEC (← q "x:real")) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    UNDISCH_TAC (← q r"!x. a <= x /\ x <= b ==> f contl x") THEN
    DISCH_THEN (fun th => FIRST_ASSUM (MP_TAC o MATCH_MP th)) THEN
    REWRITE_TAC [contl, LIM] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"abs(y - f(x:real))")) THEN
    GEN_REWRITE_TAC (funpow 2 LAND_CONV) [← GSYM ABS_NZ] THEN
    REWRITE_TAC [REAL_SUB_0, REAL_SUB_RZERO] THEN BETA_TAC THEN
    ASSUM_LIST (fun thl => tactic_of do pure (REWRITE_TAC (← thl.mapM GSYM))) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "d:real") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q "d:real") THEN ASM_REWRITE_TAC [] THEN
    MAP_EVERY X_GEN_TAC [← q "u:real", ← q "v:real"] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"(f:real->real) x", ← q "y:real"] REAL_LT_TOTAL) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN DISJ_CASES_TAC THEN
    FIRST_ASSUM (undischCheck (fun c => pure (is_forall c))) THENL
     [DISCH_THEN (MP_TAC o SPEC (← q "v - x")) THEN REWRITE_TAC [NOT_IMP] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC [real_abs, REAL_SUB_LE, REAL_SUB_LT] THEN
        ASM_REWRITE_TAC [REAL_LT_LE] THEN DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC (← q r"f(v:real) < y") THEN ASM_REWRITE_TAC [← GSYM REAL_NOT_LE],
        ASM_REWRITE_TAC [real_abs, REAL_SUB_LE] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q "v - u") THEN
        ASM_REWRITE_TAC [real_sub, REAL_LE_LADD, REAL_LE_NEG2, REAL_LE_RADD],
        ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN REWRITE_TAC [REAL_SUB_ADD] THEN
        REWRITE_TAC [REAL_NOT_LT, real_abs, REAL_SUB_LE] THEN
        SUBGOAL_THEN (← q r"f(x:real) <= y") ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
        SUBGOAL_THEN (← q r"f(x:real) <= f(v)") ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "y:real"), ALL_TAC] THEN
        ASM_REWRITE_TAC [real_sub, REAL_LE_RADD]],
      DISCH_THEN (MP_TAC o SPEC (← q "u - x")) THEN REWRITE_TAC [NOT_IMP] THEN
      REPEAT CONJ_TAC THENL
       [ONCE_REWRITE_TAC [ABS_SUB] THEN
        ASM_REWRITE_TAC [real_abs, REAL_SUB_LE, REAL_SUB_LT] THEN
        ASM_REWRITE_TAC [REAL_LT_LE] THEN DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC (← q r"y < f(x:real)") THEN ASM_REWRITE_TAC [← GSYM REAL_NOT_LE],
        ONCE_REWRITE_TAC [ABS_SUB] THEN ASM_REWRITE_TAC [real_abs, REAL_SUB_LE] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q "v - u") THEN
        ASM_REWRITE_TAC [real_sub, REAL_LE_LADD, REAL_LE_NEG2, REAL_LE_RADD],
        ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN REWRITE_TAC [REAL_SUB_ADD] THEN
        REWRITE_TAC [REAL_NOT_LT, real_abs, REAL_SUB_LE] THEN
        SUBGOAL_THEN (← q r"f(u:real) < f(x)") ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q "y:real") THEN
          ASM_REWRITE_TAC [], ALL_TAC] THEN
        ASM_REWRITE_TAC [← GSYM REAL_NOT_LT] THEN
        ASM_REWRITE_TAC [REAL_NOT_LT, REAL_LE_NEG2, real_sub, REAL_LE_RADD]]])

  let IVT2 ← prove
   r"!f a b y. (a <= b) /\ (f(b) <= y /\ y <= f(a)) /\
             (!x. a <= x /\ x <= b ==> f contl x) ==>
        ?x. a <= x /\ x <= b /\ (f(x) = y)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"\x:real. --(f x)", ← q "a:real", ← q "b:real", ← q "--y"] IVT) THEN
    BETA_TAC THEN ASM_REWRITE_TAC [REAL_LE_NEG2, REAL_NEG_EQ, REAL_NEG_NEG] THEN
    DISCH_THEN MATCH_MP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC CONT_NEG THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [])

  let DIFF_CONST ← prove
   r"!k x. ((\x. k) diffl &0)(x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [diffl] THEN
    REWRITE_TAC [REAL_SUB_REFL, real_div, REAL_MUL_LZERO] THEN
    MATCH_ACCEPT_TAC LIM_CONST)

  let DIFF_ADD ← prove
   r"!f g l m x. (f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) + g(x)) diffl (l + m))(x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [diffl] THEN
    DISCH_TAC THEN BETA_TAC THEN
    REWRITE_TAC [REAL_ADD2_SUB2] THEN
    REWRITE_TAC [real_div, REAL_RDISTRIB] THEN
    REWRITE_TAC [← GSYM real_div] THEN
    CONV_TAC (← EXACT_CONV [← xbeta (← q "h:real") (← q r"(f(x + h) - f(x)) / h")]) THEN
    CONV_TAC (← EXACT_CONV [← xbeta (← q "h:real") (← q r"(g(x + h) - g(x)) / h")]) THEN
    MATCH_MP_TAC LIM_ADD THEN ASM_REWRITE_TAC [])

  let DIFF_MUL ← prove
   r"!f g l m x. (f diffl l)(x) /\ (g diffl m)(x) ==>
                  ((\x. f(x) * g(x)) diffl ((l * g(x)) + (m * f(x))))(x)"
   (← do
    let h ← q "h:real"
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [diffl] THEN
      DISCH_TAC THEN BETA_TAC THEN SUBGOAL_THEN
        (← q r"!a b c d. (a * b) - (c * d) = ((a * b) - (a * d)) + ((a * d) - (c * d))")
      (fun th => tactic_of do pure (ONCE_REWRITE_TAC [← GEN_ALL th])) THENL
       [REWRITE_TAC [real_sub] THEN
        ONCE_REWRITE_TAC [← AC REAL_ADD_AC
          (← q r"(a + b) + (c + d) = (b + c) + (a + d)")] THEN
        REWRITE_TAC [REAL_ADD_LINV, REAL_ADD_LID], ALL_TAC] THEN
      REWRITE_TAC [← GSYM REAL_SUB_LDISTRIB, ← GSYM REAL_SUB_RDISTRIB] THEN SUBGOAL_THEN
        (← q r"!a b c d e. ((a * b) + (c * d)) / e = ((b / e) * a) + ((c / e) * d)")
        (fun th => ONCE_REWRITE_TAC [th]) THENL
       [REPEAT GEN_TAC THEN REWRITE_TAC [real_div] THEN
        REWRITE_TAC [REAL_RDISTRIB] THEN BINOP_TAC THEN
        REWRITE_TAC [REAL_MUL_AC], ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [REAL_ADD_SYM] THEN
      CONV_TAC (← EXACT_CONV (← [← q r"((g(x + h) - g(x)) / h) * f(x + h)",
                                ← q r"((f(x + h) - f(x)) / h) * g(x)"].mapM (xbeta h))) THEN
      MATCH_MP_TAC LIM_ADD THEN
      CONV_TAC (← EXACT_CONV (← [← q r"(g(x + h) - g(x)) / h", ← q r"f(x + h):real",
                                ← q r"(f(x + h) - f(x)) / h", ← q r"g(x:real):real"].mapM (xbeta h))) THEN
      CONJ_TAC THEN MATCH_MP_TAC LIM_MUL THEN
      BETA_TAC THEN ASM_REWRITE_TAC [LIM_CONST] THEN
      REWRITE_TAC [← GSYM contl] THEN
      MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC (← q "l:real") THEN
      ASM_REWRITE_TAC [diffl]))

  let DIFF_CMUL ← prove
   r"!f c l x. (f diffl l)(x) ==> ((\x. c * f(x)) diffl (c * l))(x)"
   (← do
    let dc ← SPECL [← q "c:real", ← q "x:real"] DIFF_CONST
    pure (REPEAT GEN_TAC THEN
      DISCH_THEN (MP_TAC o CONJ dc) THEN
      DISCH_THEN (MP_TAC o MATCH_MP DIFF_MUL) THEN BETA_TAC THEN
      REWRITE_TAC [REAL_MUL_LZERO, REAL_ADD_LID] THEN
      MATCH_MP_TAC (← TAUT (← q r"(a <=> b) ==> a ==> b")) THEN AP_THM_TAC THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
      REWRITE_TAC []))

  let DIFF_NEG ← prove
   r"!f l x. (f diffl l)(x) ==> ((\x. --(f x)) diffl --l)(x)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [REAL_NEG_MINUS1] THEN
    MATCH_ACCEPT_TAC DIFF_CMUL)

  let DIFF_SUB ← prove
   r"!f g l m x. (f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) - g(x)) diffl (l - m))(x)"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (fun th => tactic_of do
      let (a, b) ← CONJ_PAIR th
      let b' ← MATCH_MP DIFF_NEG b
      pure (MP_TAC (← MATCH_MP DIFF_ADD (← CONJ a b')))) THEN
    BETA_TAC THEN REWRITE_TAC [real_sub])

  let DIFF_CARAT ← prove
   r"!f l x. (f diffl l)(x) <=>
      ?g. (!z. f(z) - f(x) = g(z) * (z - x)) /\ g contl x /\ (g(x) = l)"
   (REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [EXISTS_TAC (← q r"\z. if z = x then l else (f(z) - f(x)) / (z - x)") THEN
      BETA_TAC THEN REWRITE_TAC [] THEN CONJ_TAC THENL
       [X_GEN_TAC (← q "z:real") THEN COND_CASES_TAC THEN
        ASM_REWRITE_TAC [REAL_SUB_REFL, REAL_MUL_RZERO] THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
        ASM_REWRITE_TAC [REAL_SUB_0],
        POP_ASSUM MP_TAC THEN MATCH_MP_TAC EQ_IMP THEN
        REWRITE_TAC [diffl, contl] THEN BETA_TAC THEN REWRITE_TAC [] THEN
        MATCH_MP_TAC LIM_EQUAL THEN GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
        ASM_REWRITE_TAC [REAL_ADD_RID_UNIQ, REAL_ADD_SUB]],
      POP_ASSUM (X_CHOOSE_THEN (← q r"g:real->real") STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM (undischCheck (fun c => pure (is_eq c))) THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN UNDISCH_TAC (← q "g contl x") THEN
      ASM_REWRITE_TAC [contl, diffl, REAL_ADD_SUB] THEN
      MATCH_MP_TAC EQ_IMP THEN
      MATCH_MP_TAC LIM_EQUAL THEN GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
      REWRITE_TAC [real_div, ← GSYM REAL_MUL_ASSOC] THEN
      FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP REAL_MUL_RINV th])) THEN
      REWRITE_TAC [REAL_MUL_RID]])

  let DIFF_CHAIN ← prove
   r"!f g l m x.
     (f diffl l)(g x) /\ (g diffl m)(x) ==> ((\x. f(g x)) diffl (l * m))(x)"
   (← do
    let ag' ← ASSUME (← q "g' contl x")
    pure (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN MP_TAC) THEN
      DISCH_THEN (fun th => tactic_of do
        pure (MP_TAC th THEN ASSUME_TAC (← MATCH_MP DIFF_CONT th))) THEN
      REWRITE_TAC [DIFF_CARAT] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"g':real->real") STRIP_ASSUME_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"f':real->real") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC
       (← q r"\z. if z = x then l * m else (f(g(z):real) - f(g(x))) / (z - x)") THEN
      BETA_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [GEN_TAC THEN COND_CASES_TAC THEN
        ASM_REWRITE_TAC [REAL_SUB_REFL, REAL_MUL_RZERO] THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
        ASM_REWRITE_TAC [REAL_SUB_0],
        MP_TAC (← do
          let b ← ASSUME (← q r"f' contl (g(x:real))")
          let a ← ASSUME (← q "g contl x")
          CONJ a b) THEN
        DISCH_THEN (MP_TAC o MATCH_MP CONT_COMPOSE) THEN
        DISCH_THEN (MP_TAC o (fun th => CONJ th ag')) THEN
        DISCH_THEN (MP_TAC o MATCH_MP CONT_MUL) THEN BETA_TAC THEN
        ASM_REWRITE_TAC [contl] THEN BETA_TAC THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC EQ_IMP THEN
        MATCH_MP_TAC LIM_EQUAL THEN X_GEN_TAC (← q "z:real") THEN
        DISCH_TAC THEN BETA_TAC THEN ASM_REWRITE_TAC [REAL_ADD_RID_UNIQ] THEN
        REWRITE_TAC [real_div, ← GSYM REAL_MUL_ASSOC, REAL_ADD_SUB] THEN
        FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP REAL_MUL_RINV th])) THEN
        REWRITE_TAC [REAL_MUL_RID]]))

  let DIFF_X ← prove
   r"!x. ((\x. x) diffl &1)(x)"
   (GEN_TAC THEN REWRITE_TAC [diffl] THEN BETA_TAC THEN
    REWRITE_TAC [REAL_ADD_SUB] THEN REWRITE_TAC [LIM, REAL_SUB_RZERO] THEN
    BETA_TAC THEN X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN
    EXISTS_TAC (← q r"&1") THEN REWRITE_TAC [REAL_LT_01] THEN
    GEN_TAC THEN DISCH_THEN (MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC [← GSYM ABS_NZ] THEN
    DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP REAL_DIV_REFL th])) THEN
    ASM_REWRITE_TAC [REAL_SUB_REFL, ABS_0])

  let DIFF_POW ← prove
   r"!n x. ((\x. x pow n) diffl (&n * (x pow (n - 1))))(x)"
   (← do
    let xR ← q "x:real"
    let dx ← SPEC xR DIFF_X
    pure (INDUCT_TAC THEN REWRITE_TAC [pow, DIFF_CONST, REAL_MUL_LZERO] THEN
      X_GEN_TAC xR THEN
      POP_ASSUM (MP_TAC o CONJ dx o SPEC xR) THEN
      DISCH_THEN (MP_TAC o MATCH_MP DIFF_MUL) THEN BETA_TAC THEN
      MATCH_MP_TAC EQ_IMP THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [REAL_MUL_LID] THEN
      REWRITE_TAC [REAL, REAL_RDISTRIB, REAL_MUL_LID] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_ADD_SYM] THEN BINOP_TAC THENL
       [REWRITE_TAC [ADD1, ADD_SUB],
        STRUCT_CASES_TAC (← SPEC (← q "n:num") num_CASES) THEN
        REWRITE_TAC [REAL_MUL_LZERO] THEN
        REWRITE_TAC [ADD1, ADD_SUB, POW_ADD] THEN
        REWRITE_TAC [REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
        REWRITE_TAC [← numc "1", pow] THEN
        REWRITE_TAC [← SYM (← numc "1"), REAL_MUL_RID]]))

  let DIFF_XM1 ← prove
   r"!x. ~(x = &0) ==> ((\x. inv(x)) diffl (--(inv(x) pow 2)))(x)"
   (← do
    let z ← q r"&0"
    let xh ← q r"x * (x + h)"
    let h ← q "h:real"
    let linvs ← [← q r"~(x = &0)", ← q r"~(x + h = &0)"].mapM (fun t => do
      MATCH_MP REAL_MUL_LINV (← ASSUME t))
    let negAddSub ← REWRITE_RULE [REAL_NEG_SUB]
      (← AP_TERM (← q "(--)") (← SPEC_ALL REAL_ADD_SUB))
    pure (GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [diffl] THEN BETA_TAC THEN
      MATCH_MP_TAC LIM_TRANSFORM THEN
      EXISTS_TAC (← q r"\h. --(inv(x + h) * inv(x))") THEN
      BETA_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC [LIM] THEN X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN
        EXISTS_TAC (← q "abs(x)") THEN
        EVERY_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← REWRITE_RULE [ABS_NZ] th])) THEN
        X_GEN_TAC h THEN REWRITE_TAC [REAL_SUB_RZERO] THEN
        DISCH_THEN STRIP_ASSUME_TAC THEN BETA_TAC THEN
        (fun gl => ExceptT.run do
          let mkEq ← ExceptT.mk (mk_eq : IO _)
          let t ← liftExcept (do mkEq ((← rand (← rator gl.2)), z))
          ExceptT.mk (SUBGOAL_THEN t SUBST1_TAC gl)) THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [ABS_ZERO, REAL_SUB_0] THEN
        SUBGOAL_THEN (← q r"~(x + h = &0)") ASSUME_TAC THENL
         [REWRITE_TAC [REAL_LNEG_UNIQ] THEN DISCH_THEN SUBST_ALL_TAC THEN
          UNDISCH_TAC (← q r"abs(h) < abs(--h)") THEN
          REWRITE_TAC [ABS_NEG, REAL_LT_REFL], ALL_TAC] THEN
        (fun gl => ExceptT.run do
          let w := gl.2
          let r ← liftExcept (rhs w)
          let l ← liftExcept (lhs w)
          ExceptT.mk (MP_TAC (← SPECL [xh, l, r] REAL_EQ_LMUL) gl)) THEN
        ASM_REWRITE_TAC [REAL_ENTIRE] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
        REWRITE_TAC [← GSYM REAL_NEG_LMUL, ← GSYM REAL_NEG_RMUL] THEN
        REWRITE_TAC [real_div, REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB] THEN
        ONCE_REWRITE_TAC [← AC REAL_MUL_AC
          (← q r"(a * b) * (c * d) = (c * b) * (d * a)")] THEN
        REWRITE_TAC linvs THEN REWRITE_TAC [REAL_MUL_LID] THEN
        ONCE_REWRITE_TAC [← AC REAL_MUL_AC
          (← q r"(a * b) * (c * d) = (a * d) * (c * b)")] THEN
        REWRITE_TAC [← MATCH_MP REAL_MUL_LINV (← ASSUME (← q r"~(x = &0)"))] THEN
        REWRITE_TAC [REAL_MUL_LID, ← GSYM REAL_SUB_LDISTRIB] THEN
        REWRITE_TAC [negAddSub] THEN
        REWRITE_TAC [← GSYM REAL_NEG_RMUL] THEN AP_TERM_TAC THEN
        MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC [ABS_NZ],

        REWRITE_TAC [POW_2] THEN
        CONV_TAC (← EXACT_CONV [← xbeta h (← q r"inv(x + h) * inv(x)")]) THEN
        REWRITE_TAC [← GSYM LIM_NEG] THEN
        CONV_TAC (← EXACT_CONV (← [← q r"inv(x + h)", ← q "inv(x)"].mapM (xbeta h)))
        THEN MATCH_MP_TAC LIM_MUL THEN BETA_TAC THEN
        REWRITE_TAC [LIM_CONST] THEN
        CONV_TAC (← EXACT_CONV [← xbeta h (← q "x + h")]) THEN
        MATCH_MP_TAC LIM_INV THEN ASM_REWRITE_TAC [] THEN
        GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_ADD_RID] THEN
        CONV_TAC (← EXACT_CONV (← [← q "x:real", ← q "h:real"].mapM (xbeta h))) THEN
        MATCH_MP_TAC LIM_ADD THEN BETA_TAC THEN REWRITE_TAC [LIM_CONST] THEN
        MATCH_ACCEPT_TAC LIM_X]))

  let DIFF_INV ← prove
   r"!f l x. (f diffl l)(x) /\ ~(f(x) = &0) ==>
        ((\x. inv(f x)) diffl --(l / (f(x) pow 2)))(x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [real_div, REAL_NEG_RMUL] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN DISCH_TAC THEN
    MATCH_MP_TAC DIFF_CHAIN THEN ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (REWRITE_TAC [← MATCH_MP POW_INV (← CONJUNCT2 th)])) THEN
    MATCH_MP_TAC (← CONV_RULE (ONCE_DEPTH_CONV ETA_CONV) DIFF_XM1) THEN
    ASM_REWRITE_TAC [])

  let DIFF_DIV ← prove
   r"!f g l m. (f diffl l)(x) /\ (g diffl m)(x) /\ ~(g(x) = &0) ==>
    ((\x. f(x) / g(x)) diffl (((l * g(x)) - (m * f(x))) / (g(x) pow 2)))(x)"
   (REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
    REWRITE_TAC [real_div] THEN
    MP_TAC (← SPECL [← q r"g:real->real", ← q "m:real", ← q "x:real"] DIFF_INV) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o CONJ (← ASSUME (← q "(f diffl l)(x)"))) THEN
    DISCH_THEN (MP_TAC o MATCH_MP DIFF_MUL) THEN BETA_TAC THEN
    (fun gl => ExceptT.run do
      let mkEq ← ExceptT.mk (mk_eq : IO _)
      let t ← liftExcept (do
        let (a, b) ← dest_imp gl.2
        -- `(rand o rator) F_F (rand o rator)`: the pair is built right to left.
        let b' ← rand (← rator b)
        let a' ← rand (← rator a)
        mkEq (a', b'))
      ExceptT.mk (SUBGOAL_THEN t SUBST1_TAC gl)) THEN
    REWRITE_TAC [] THEN REWRITE_TAC [real_sub] THEN
    REWRITE_TAC [REAL_LDISTRIB, REAL_RDISTRIB] THEN BINOP_TAC THENL
     [REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
      REWRITE_TAC [POW_2] THEN
      FIRST_ASSUM (fun th => tactic_of do
        pure (REWRITE_TAC [← MATCH_MP REAL_INV_MUL_WEAK (← CONJ th th)])) THEN
      REWRITE_TAC [REAL_MUL_ASSOC] THEN
      FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP REAL_MUL_RINV th])) THEN
      REWRITE_TAC [REAL_MUL_LID],
      REWRITE_TAC [real_div, ← GSYM REAL_NEG_LMUL, ← GSYM REAL_NEG_RMUL] THEN
      AP_TERM_TAC THEN REWRITE_TAC [REAL_MUL_AC]])

  let DIFF_SUM ← prove
   r"!f f' m n x. (!r. m <= r /\ r < (m + n)
                 ==> ((\x. f r x) diffl (f' r x))(x))
     ==> ((\x. sum(m,n)(\n. f n x)) diffl (sum(m,n) (\r. f' r x)))(x)"
   (REPEAT GEN_TAC THEN SPEC_TAC (← q "n:num", ← q "n:num") THEN
    INDUCT_TAC THEN REWRITE_TAC [sum, DIFF_CONST] THEN DISCH_TAC THEN
    CONV_TAC (ONCE_DEPTH_CONV HABS_CONV) THEN MATCH_MP_TAC DIFF_ADD THEN
    BETA_TAC THEN CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC LT_TRANS THEN
      EXISTS_TAC (← q "m + n:num") THEN ASM_REWRITE_TAC [ADD_CLAUSES, LESS_SUC_REFL],
      REWRITE_TAC [LE_ADD, ADD_CLAUSES, LESS_SUC_REFL]])

  -- @@RETURN BEGIN
  return { IVT, IVT2, DIFF_CONST, DIFF_ADD, DIFF_MUL, DIFF_CMUL, DIFF_NEG, DIFF_SUB,
           DIFF_CARAT, DIFF_CHAIN, DIFF_X, DIFF_POW, DIFF_XM1, DIFF_INV, DIFF_DIV,
           DIFF_SUM }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- A function continuous on a closed interval is bounded and attains its     -/
/- bounds.  (analysis.ml 5340-5622)                                          -/
/- ------------------------------------------------------------------------- -/

structure Cont where
  -- @@FIELDS
  CONT_BOUNDED : thm
  CONT_BOUNDED_ABS : thm
  CONT_HASSUP : thm
  CONT_ATTAINS : thm
  CONT_ATTAINS2 : thm
  CONT_ATTAINS_ALL : thm
  deriving Inhabited

@[nospecialize]
def setupCont [HolBase] (D : AnalysisDeps) (BCompat : Compat) (BTactics : Tactics) (BReals1 : Reals1) (BReals2 : Reals2) (BReals3 : Reals3) (BAbs : Abs) (BPow : Pow) (BSeries1 : Series1) (BLims : Lims) (BDiffs : Diffs) :
    ExceptT String IO Cont := do
  -- @@SCOPE BEGIN
  let { GEN_BETA_CONV, REAL_ARITH, .. } := D
  let { CONJ_ASSOC, DE_MORGAN_THM, NOT_IMP, REAL_ADD_SYM, .. } := D.core1
  let { REAL_LET_TRANS, REAL_LT_ADDR, REAL_LT_INV2, REAL_LT_REFL, REAL_LT_TRANS, .. } := D.core2
  let { real_abs, real_sub, .. } := D.core3
  let { NOT_EXISTS_CONV, .. } := BCompat
  let { HABS_CONV, .. } := BTactics
  let { REAL_LE_LADD, REAL_LE_LT, REAL_LE_RADD, REAL_LE_REFL, REAL_LE_TOTAL,
        REAL_LE_TRANS, REAL_LTE_TRANS, REAL_LT_01, REAL_LT_IMP_LE, REAL_LT_LE,
        REAL_NEG_NEG, REAL_NOT_LT, REAL_SUB_ADD, .. } := BReals1
  let { REAL_INVINV, REAL_INV_POS, REAL_LT_IMP_NE, REAL_NEG_EQ, REAL_NEG_SUB,
        REAL_SUB_0, REAL_SUB_LE, REAL_SUB_LT, REAL_SUB_REFL, .. } := BReals2
  let { REAL_LE_NEG2, REAL_LT_SUB_LADD, REAL_LT_SUB_RADD, REAL_SUB_RZERO, .. } := BReals3
  let { ABS_0, ABS_LE, ABS_NZ, ABS_TRIANGLE, .. } := BAbs
  let { REAL_SUP_LE, .. } := BPow
  let { BOLZANO_LEMMA, .. } := BSeries1
  let { CONT_CONST, CONT_INV, CONT_NEG, CONT_SUB, LIM, contl, .. } := BLims
  let { IVT, IVT2, .. } := BDiffs
  -- @@SCOPE END
  -- `W(C SUBGOAL_THEN ttac o funpow 2 (fst o dest_imp) o snd)`
  let subgoalAnte2 (ttac : thm_tactic) : tactic := fun gl => ExceptT.run do
    let t ← liftExcept (funpow 2 (fun (m : Except String term) => do
      pure (← dest_imp (← m)).1) (pure gl.2))
    ExceptT.mk (SUBGOAL_THEN t ttac gl)

  let CONT_BOUNDED ← prove
   r"!f a b. (a <= b /\ !x. a <= x /\ x <= b ==> f contl x)
        ==> ?M. !x. a <= x /\ x <= b ==> f(x) <= M"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPEC
      (← q r"\(u,v). a <= u /\ u <= v /\ v <= b ==>
                 ?M. !x. u <= x /\ x <= v ==> f x <= M") BOLZANO_LEMMA) THEN
    CONV_TAC (ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    subgoalAnte2 (fun t => REWRITE_TAC [t]) THENL
     [ALL_TAC,
      DISCH_THEN (MP_TAC o SPECL [← q "a:real", ← q "b:real"]) THEN
      ASM_REWRITE_TAC [REAL_LE_REFL]] THEN
    CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [← q "u:real", ← q "v:real", ← q "w:real"] THEN
      DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
      DISCH_TAC THEN
      REPEAT (FIRST_ASSUM (undischCheck (fun c => pure (is_imp c)))) THEN
      ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q "v <= b") ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "w:real") THEN
        ASM_REWRITE_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN (← q "a <= v") ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "u:real") THEN
        ASM_REWRITE_TAC [], ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q "M1:real")) THEN
      DISCH_THEN (X_CHOOSE_TAC (← q "M2:real")) THEN
      DISJ_CASES_TAC (← SPECL [← q "M1:real", ← q "M2:real"] REAL_LE_TOTAL) THENL
       [EXISTS_TAC (← q "M2:real") THEN X_GEN_TAC (← q "x:real") THEN STRIP_TAC THEN
        DISJ_CASES_TAC (← SPECL [← q "x:real", ← q "v:real"] REAL_LE_TOTAL) THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "M1:real") THEN
          ASM_REWRITE_TAC [], ALL_TAC] THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
        EXISTS_TAC (← q "M1:real") THEN X_GEN_TAC (← q "x:real") THEN STRIP_TAC THEN
        DISJ_CASES_TAC (← SPECL [← q "x:real", ← q "v:real"] REAL_LE_TOTAL) THENL
         [ALL_TAC, MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC (← q "M2:real") THEN ASM_REWRITE_TAC []] THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []],
      ALL_TAC] THEN
    X_GEN_TAC (← q "x:real") THEN ASM_CASES_TAC (← q r"a <= x /\ x <= b") THENL
     [ALL_TAC,
      EXISTS_TAC (← q r"&1") THEN REWRITE_TAC [REAL_LT_01] THEN
      MAP_EVERY X_GEN_TAC [← q "u:real", ← q "v:real"] THEN
      REPEAT STRIP_TAC THEN UNDISCH_TAC (← q r"~(a <= x /\ x <= b)") THEN
      CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN (fun _ => ALL_TAC) THEN
      REWRITE_TAC [] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
       [EXISTS_TAC (← q "u:real"), EXISTS_TAC (← q "v:real")] THEN
      ASM_REWRITE_TAC []] THEN
    UNDISCH_TAC (← q r"!x. a <= x /\ x <= b ==> f contl x") THEN
    DISCH_THEN (MP_TAC o SPEC (← q "x:real")) THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [contl, LIM] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"&1")) THEN REWRITE_TAC [REAL_LT_01] THEN
    ASM_REWRITE_TAC [REAL_SUB_RZERO] THEN BETA_TAC THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "d:real") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q "d:real") THEN ASM_REWRITE_TAC [] THEN
    MAP_EVERY X_GEN_TAC [← q "u:real", ← q "v:real"] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC (← q r"abs(f(x:real)) + &1") THEN
    X_GEN_TAC (← q "z:real") THEN STRIP_TAC THEN
    FIRST_ASSUM (undischCheck (fun c => pure (is_forall c))) THEN
    DISCH_THEN (MP_TAC o SPEC (← q "z - x")) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_ADD_SYM] THEN
    REWRITE_TAC [REAL_SUB_ADD] THEN DISCH_TAC THEN
    MP_TAC (← SPECL [← q r"f(z:real) - f(x)", ← q r"(f:real->real) x"] ABS_TRIANGLE) THEN
    REWRITE_TAC [REAL_SUB_ADD] THEN
    DISCH_THEN (ASSUME_TAC o ONCE_REWRITE_RULE [REAL_ADD_SYM]) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"abs(f(z:real))") THEN
    REWRITE_TAC [ABS_LE] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"abs(f(x:real)) + (abs(f(z) - f(x)))") THEN
    ASM_REWRITE_TAC [REAL_LE_LADD] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    ASM_CASES_TAC (← q "z:real = x") THENL
     [ASM_REWRITE_TAC [REAL_SUB_REFL, ABS_0, REAL_LT_01],
      FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [← GSYM ABS_NZ] THEN
      ASM_REWRITE_TAC [REAL_SUB_0, real_abs, REAL_SUB_LE] THEN
      REWRITE_TAC [REAL_NEG_SUB] THEN COND_CASES_TAC THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q "v - u") THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LE_TRANS THENL
       [EXISTS_TAC (← q "v - x"), EXISTS_TAC (← q "v - z")] THEN
      ASM_REWRITE_TAC [real_sub, REAL_LE_RADD, REAL_LE_LADD, REAL_LE_NEG2]])

  let CONT_BOUNDED_ABS ← prove
   r"!f a b. (!x. a <= x /\ x <= b ==> f contl x)
           ==> ?M. !x. a <= x /\ x <= b ==> abs(f(x)) <= M"
   (← do
    -- The later rule in the THEN chain is evaluated first.
    let ra2 ← REAL_ARITH
     (← q r"x <= m1 /\ --x <= m2 ==> abs(x) <= abs(m2) + abs(m1)")
    let ra1 ← REAL_ARITH (← q r"~(a <= b) ==> ~(a <= x /\ x <= b)")
    pure (REPEAT STRIP_TAC THEN
      ASM_CASES_TAC (← q "a <= b") THENL
       [ALL_TAC,
        ASM_SIMP_TAC [ra1]] THEN
      MP_TAC (← SPECL [← q r"f:real->real", ← q "a:real", ← q "b:real"] CONT_BOUNDED) THEN
      MP_TAC (← SPECL [← q r"\x:real. --(f x)", ← q "a:real", ← q "b:real"] CONT_BOUNDED) THEN
      ASM_SIMP_TAC [CONT_NEG] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q "M1:real")) THEN
      DISCH_THEN (X_CHOOSE_TAC (← q "M2:real")) THEN
      EXISTS_TAC (← q "abs(M1) + abs(M2)") THEN
      ASM_SIMP_TAC [ra2]))

  let CONT_HASSUP ← prove
   r"!f a b. (a <= b /\ !x. a <= x /\ x <= b ==> f contl x)
        ==> ?M. (!x. a <= x /\ x <= b ==> f(x) <= M) /\
                (!N. N < M ==> ?x. a <= x /\ x <= b /\ N < f(x))"
   (← do
    let tm ← q r"\y:real. ?x. a <= x /\ x <= b /\ (y = f(x))"
    let supTm ← q "sup"
    let st ← liftExcept (mk_comb supTm tm)
    pure (REPEAT GEN_TAC THEN DISCH_TAC THEN MP_TAC (← SPEC tm REAL_SUP_LE) THEN
      BETA_TAC THEN
      subgoalAnte2 (fun t => REWRITE_TAC [t])
      THENL
       [CONJ_TAC THENL
         [MAP_EVERY EXISTS_TAC [← q r"(f:real->real) a", ← q "a:real"] THEN
          ASM_REWRITE_TAC [REAL_LE_REFL, REAL_LE_LT],
          POP_ASSUM (X_CHOOSE_TAC (← q "M:real") o MATCH_MP CONT_BOUNDED) THEN
          EXISTS_TAC (← q "M:real") THEN X_GEN_TAC (← q "y:real") THEN
          DISCH_THEN (X_CHOOSE_THEN (← q "x:real") MP_TAC) THEN
          REWRITE_TAC [CONJ_ASSOC] THEN
          DISCH_THEN (CONJUNCTS_THEN2 MP_TAC SUBST1_TAC) THEN
          POP_ASSUM MATCH_ACCEPT_TAC],
        DISCH_TAC THEN EXISTS_TAC st THEN CONJ_TAC THENL
         [X_GEN_TAC (← q "x:real") THEN DISCH_TAC THEN
          FIRST_ASSUM (MP_TAC o SPEC st) THEN
          REWRITE_TAC [REAL_LT_REFL] THEN
          CONV_TAC (ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
          DISCH_THEN (MP_TAC o SPEC (← q r"(f:real->real) x")) THEN
          REWRITE_TAC [DE_MORGAN_THM, REAL_NOT_LT] THEN
          CONV_TAC (ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
          DISCH_THEN (DISJ_CASES_THEN MP_TAC) THEN REWRITE_TAC [] THEN
          DISCH_THEN (MP_TAC o SPEC (← q "x:real")) THEN ASM_REWRITE_TAC [],
          GEN_TAC THEN FIRST_ASSUM (SUBST1_TAC o SYM o SPEC (← q "N:real")) THEN
          DISCH_THEN (X_CHOOSE_THEN (← q "y:real") MP_TAC) THEN
          DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
          DISCH_THEN (X_CHOOSE_THEN (← q "x:real") MP_TAC) THEN
          REWRITE_TAC [CONJ_ASSOC] THEN
          DISCH_THEN (CONJUNCTS_THEN2 MP_TAC SUBST_ALL_TAC) THEN
          DISCH_TAC THEN EXISTS_TAC (← q "x:real") THEN ASM_REWRITE_TAC []]]))

  let CONT_ATTAINS ← prove
   r"!f a b. (a <= b /\ !x. a <= x /\ x <= b ==> f contl x)
        ==> ?M. (!x. a <= x /\ x <= b ==> f(x) <= M) /\
                (?x. a <= x /\ x <= b /\ (f(x) = M))"
   (← do
    -- The later TAUT in the THEN chain is evaluated first.
    let t2 ← TAUT (← q r"~(a /\ b /\ c) <=> a /\ b ==> ~c")
    let t1 ← TAUT (← q r"a <=> ~ ~a")
    pure (REPEAT GEN_TAC THEN DISCH_TAC THEN
      FIRST_ASSUM (X_CHOOSE_THEN (← q "M:real") STRIP_ASSUME_TAC o MATCH_MP CONT_HASSUP)
      THEN EXISTS_TAC (← q "M:real") THEN ASM_REWRITE_TAC [] THEN
      GEN_REWRITE_TAC id [t1] THEN
      CONV_TAC (RAND_CONV NOT_EXISTS_CONV) THEN
      REWRITE_TAC [t2] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN (← q r"!x. a <= x /\ x <= b ==> f(x) < M") MP_TAC THENL
       [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [REAL_LT_LE] THEN
        CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
        FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
      PURE_ONCE_REWRITE_TAC [← GSYM REAL_SUB_LT] THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"!x. a <= x /\ x <= b ==> (\x. inv(M - f(x))) contl x")
      ASSUME_TAC THENL
       [GEN_TAC THEN DISCH_TAC THEN
        CONV_TAC (ONCE_DEPTH_CONV HABS_CONV) THEN
        MATCH_MP_TAC CONT_INV THEN BETA_TAC THEN
        REWRITE_TAC [REAL_SUB_0] THEN CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
        CONJ_TAC THENL
         [ALL_TAC,
          MATCH_MP_TAC REAL_LT_IMP_NE THEN
          ONCE_REWRITE_TAC [← GSYM REAL_SUB_LT] THEN
          FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []] THEN
        CONV_TAC (ONCE_DEPTH_CONV HABS_CONV) THEN
        MATCH_MP_TAC CONT_SUB THEN BETA_TAC THEN
        REWRITE_TAC [CONT_CONST] THEN
        CONV_TAC (ONCE_DEPTH_CONV ETA_CONV) THEN
        FIRST_ASSUM (MATCH_MP_TAC o CONJUNCT2) THEN
        ASM_REWRITE_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"?k. !x. a <= x /\ x <= b ==> (\x. inv(M - (f x))) x <= k")
      MP_TAC THENL
       [MATCH_MP_TAC CONT_BOUNDED THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
      BETA_TAC THEN DISCH_THEN (X_CHOOSE_TAC (← q "k:real")) THEN
      SUBGOAL_THEN (← q r"!x. a <= x /\ x <= b ==> &0 < inv(M - f(x))") ASSUME_TAC THENL
       [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_INV_POS THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"!x. a <= x /\ x <= b ==> (\x. inv(M - (f x))) x < (k + &1)")
      ASSUME_TAC THENL
       [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC (← q "k:real") THEN REWRITE_TAC [REAL_LT_ADDR, REAL_LT_01] THEN
        BETA_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"!x. a <= x /\ x <= b ==>
           inv(k + &1) < inv((\x. inv(M - (f x))) x)") MP_TAC THENL
       [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LT_INV2 THEN
        CONJ_TAC THENL
         [BETA_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
          FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []], ALL_TAC] THEN
      BETA_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"!x. a <= x /\ x <= b ==> inv(k + &1) < (M - (f x))")
      MP_TAC THENL
       [GEN_TAC THEN DISCH_TAC THEN
        SUBGOAL_THEN (← q r"~(M - f(x:real) = &0)")
          (SUBST1_TAC o SYM o MATCH_MP REAL_INVINV) THENL
         [CONV_TAC (RAND_CONV SYM_CONV) THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
          FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
          FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []], ALL_TAC] THEN
      REWRITE_TAC [REAL_LT_SUB_LADD] THEN ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
      ONCE_REWRITE_TAC [← GSYM REAL_LT_SUB_LADD] THEN DISCH_TAC THEN
      UNDISCH_TAC (← q r"!N. N < M ==> (?x. a <= x /\ x <= b /\ N < (f x))") THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"M - inv(k + &1)")) THEN
      REWRITE_TAC [REAL_LT_SUB_RADD, REAL_LT_ADDR] THEN
      REWRITE_TAC [NOT_IMP] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_INV_POS THEN MATCH_MP_TAC REAL_LT_TRANS THEN
        EXISTS_TAC (← q "k:real") THEN REWRITE_TAC [REAL_LT_ADDR, REAL_LT_01] THEN
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q r"inv(M - f(a:real))") THEN
        CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC [REAL_LE_REFL],
        DISCH_THEN (X_CHOOSE_THEN (← q "x:real") MP_TAC) THEN REWRITE_TAC [CONJ_ASSOC] THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        REWRITE_TAC [REAL_NOT_LT] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
        ONCE_REWRITE_TAC [← GSYM REAL_LT_SUB_LADD] THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []]))

  let CONT_ATTAINS2 ← prove
   r"!f a b. (a <= b /\ !x. a <= x /\ x <= b ==> f contl x)
        ==> ?M. (!x. a <= x /\ x <= b ==> M <= f(x)) /\
                (?x. a <= x /\ x <= b /\ (f(x) = M))"
   (REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
    SUBGOAL_THEN (← q r"!x. a <= x /\ x <= b ==> (\x. --(f x)) contl x") MP_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CONT_NEG THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o CONJ (← ASSUME (← q "a <= b"))) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "M:real") MP_TAC o MATCH_MP CONT_ATTAINS) THEN
    BETA_TAC THEN DISCH_TAC THEN EXISTS_TAC (← q "--M") THEN CONJ_TAC THENL
     [GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_LE_NEG2] THEN
      ASM_REWRITE_TAC [REAL_NEG_NEG],
      ASM_REWRITE_TAC [← GSYM REAL_NEG_EQ]])

  let CONT_ATTAINS_ALL ← prove
   r"!f a b. (a <= b /\ !x. a <= x /\ x <= b ==>  f contl x)
        ==> ?L M. (!x. a <= x /\ x <= b ==> L <= f(x) /\ f(x) <= M) /\
                  !y. L <= y /\ y <= M ==> ?x. a <= x /\ x <= b /\ (f(x) = y)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (X_CHOOSE_THEN (← q "L:real") MP_TAC o MATCH_MP CONT_ATTAINS2) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "x1:real") STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM (X_CHOOSE_THEN (← q "M:real") MP_TAC o MATCH_MP CONT_ATTAINS) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "x2:real") STRIP_ASSUME_TAC) THEN
     MAP_EVERY EXISTS_TAC [← q "L:real", ← q "M:real"] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    DISJ_CASES_TAC (← SPECL [← q "x1:real", ← q "x2:real"] REAL_LE_TOTAL) THEN
    REPEAT STRIP_TAC THENL
     [MP_TAC (← SPECL [← q r"f:real->real", ← q "x1:real", ← q "x2:real", ← q "y:real"] IVT) THEN
      ASM_REWRITE_TAC [] THEN subgoalAnte2 (fun t => REWRITE_TAC [t]) THENL
       [REPEAT STRIP_TAC THEN FIRST_ASSUM (MATCH_MP_TAC o CONJUNCT2),
        DISCH_THEN (X_CHOOSE_THEN (← q "x:real") STRIP_ASSUME_TAC) THEN

        ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q "x:real") THEN ASM_REWRITE_TAC []] THEN
      (CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
        [EXISTS_TAC (← q "x1:real"), EXISTS_TAC (← q "x2:real")] THEN
       ASM_REWRITE_TAC []),
      MP_TAC (← SPECL [← q r"f:real->real", ← q "x2:real", ← q "x1:real", ← q "y:real"] IVT2) THEN
      ASM_REWRITE_TAC [] THEN subgoalAnte2 (fun t => REWRITE_TAC [t]) THENL
       [REPEAT STRIP_TAC THEN FIRST_ASSUM (MATCH_MP_TAC o CONJUNCT2),
        DISCH_THEN (X_CHOOSE_THEN (← q "x:real") STRIP_ASSUME_TAC) THEN
       ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q "x:real") THEN ASM_REWRITE_TAC []] THEN
      (CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
        [EXISTS_TAC (← q "x2:real"), EXISTS_TAC (← q "x1:real")] THEN
       ASM_REWRITE_TAC [])])

  -- @@RETURN BEGIN
  return { CONT_BOUNDED, CONT_BOUNDED_ABS, CONT_HASSUP, CONT_ATTAINS, CONT_ATTAINS2,
           CONT_ATTAINS_ALL }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Local extrema; Rolle's theorem; mean value theorem; functions with zero   -/
/- derivative are constant.  (analysis.ml 5626-6060)                         -/
/- ------------------------------------------------------------------------- -/

structure Mvt where
  -- @@FIELDS
  DIFF_LINC : thm
  DIFF_LDEC : thm
  DIFF_LMAX : thm
  DIFF_LMIN : thm
  DIFF_LCONST : thm
  INTERVAL_LEMMA_LT : thm
  INTERVAL_LEMMA : thm
  ROLLE : thm
  MVT_LEMMA : thm
  MVT : thm
  MVT_ALT : thm
  DIFF_ISCONST_END : thm
  DIFF_ISCONST : thm
  DIFF_ISCONST_END_SIMPLE : thm
  DIFF_ISCONST_ALL : thm
  INTERVAL_ABS : thm
  deriving Inhabited

@[nospecialize]
def setupMvt [HolBase] (D : AnalysisDeps) (BCompat : Compat) (BTactics : Tactics) (BReals1 : Reals1) (BReals2 : Reals2) (BReals3 : Reals3) (BAbs : Abs) (BLims : Lims) (BDiffs : Diffs) (BCont : Cont) :
    ExceptT String IO Mvt := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, REAL_ARITH, .. } := D
  let { CONJ_ASSOC, DE_MORGAN_THM, EQ_IMP, REAL_ADD_AC, REAL_ADD_ASSOC, REAL_ADD_LID,
        REAL_ADD_LINV, REAL_ADD_RID, REAL_ADD_SUB2, REAL_ADD_SYM, .. } := D.core1
  let { REAL_DIV_LMUL, REAL_DIV_RMUL, REAL_DOWN2, REAL_LET_TRANS, REAL_LE_ANTISYM,
        REAL_LT_REFL, REAL_LT_TOTAL, REAL_MUL_ASSOC, .. } := D.core2
  let { REAL_MUL_SYM, RIGHT_FORALL_IMP_THM, real_abs, real_div, real_sub, .. } := D.core3
  let { EXISTS_AND_CONV, .. } := BCompat
  let { HABS_CONV, .. } := BTactics
  let { REAL_LDISTRIB, REAL_LE_LT, REAL_LE_REFL, REAL_LE_TOTAL, REAL_LE_TRANS,
        REAL_LTE_TRANS, REAL_LT_IMP_LE, REAL_LT_LE, REAL_LT_RADD, REAL_MUL_LZERO,
        REAL_MUL_RID, REAL_MUL_RZERO, REAL_NEG_ADD, REAL_NEG_LE0, REAL_NEG_LMUL,
        REAL_NEG_LT0, REAL_NEG_NEG, REAL_NEG_RMUL, REAL_NOT_LT, REAL_RDISTRIB,
        REAL_SUB_ADD, .. } := BReals1
  let { REAL_EQ_RMUL, REAL_INV_POS, REAL_LT_IMP_NE, REAL_LT_RMUL_EQ, REAL_NEG_EQ0,
        REAL_NEG_INV, REAL_SUB_0, REAL_SUB_LT, REAL_SUB_RDISTRIB, .. } := BReals2
  let { REAL_LE_NEG2, REAL_LE_SUB_LADD, REAL_LE_SUB_RADD, REAL_LT_SUB_LADD,
        REAL_LT_SUB_RADD, REAL_MEAN, REAL_SUB_RZERO, REAL_SUB_SUB2, .. } := BReals3
  let { ABS_BETWEEN, ABS_NEG, ABS_SIGN, ABS_SIGN2, .. } := BAbs
  let { CONT_CONST, CONT_MUL, CONT_SUB, DIFF_CONT, DIFF_UNIQ, LIM, differentiable,
        diffl, .. } := BLims
  let { DIFF_ADD, DIFF_CMUL, DIFF_NEG, DIFF_SUB, DIFF_X, .. } := BDiffs
  let { CONT_ATTAINS, CONT_ATTAINS2, .. } := BCont
  -- @@SCOPE END
  -- `W(C SUBGOAL_THEN ttac o funpow 2 (fst o dest_imp) o snd)`
  let subgoalAnte2 (ttac : thm_tactic) : tactic := fun gl => ExceptT.run do
    let t ← liftExcept (funpow 2 (fun (m : Except String term) => do
      pure (← dest_imp (← m)).1) (pure gl.2))
    ExceptT.mk (SUBGOAL_THEN t ttac gl)
  -- lib.ml's `el n`.
  let el (n : Nat) (l : List thm) : ExceptT String IO thm :=
    match l[n]? with
    | some x => pure x
    | none => throw "el"

  let DIFF_LINC ← prove
   r"!f x l. (f diffl l)(x) /\ &0 < l ==>
      ?d. &0 < d /\ !h. &0 < h /\ h < d ==> f(x) < f(x + h)"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    REWRITE_TAC [diffl, LIM, REAL_SUB_RZERO] THEN
    DISCH_THEN (MP_TAC o SPEC (← q "l:real")) THEN ASM_REWRITE_TAC [] THEN BETA_TAC THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "d:real") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q "d:real") THEN ASM_REWRITE_TAC [] THEN GEN_TAC THEN
    DISCH_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_SUB_LT] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP REAL_INV_POS o CONJUNCT1) THEN
    DISCH_THEN (fun th => tactic_of do
      pure (ONCE_REWRITE_TAC [← GSYM (← MATCH_MP REAL_LT_RMUL_EQ th)])) THEN
    REWRITE_TAC [REAL_MUL_LZERO] THEN REWRITE_TAC [← GSYM real_div] THEN
    MATCH_MP_TAC ABS_SIGN THEN EXISTS_TAC (← q "l:real") THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE o CONJUNCT1) THEN
    ASM_REWRITE_TAC [real_abs])

  let DIFF_LDEC ← prove
   r"!f x l. (f diffl l)(x) /\ l < &0 ==>
      ?d. &0 < d /\ !h. &0 < h /\ h < d ==> f(x) < f(x - h)"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    REWRITE_TAC [diffl, LIM, REAL_SUB_RZERO] THEN
    DISCH_THEN (MP_TAC o SPEC (← q "--l")) THEN
    ONCE_REWRITE_TAC [← GSYM REAL_NEG_LT0] THEN ASM_REWRITE_TAC [REAL_NEG_NEG] THEN
    REWRITE_TAC [REAL_NEG_LT0] THEN BETA_TAC THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "d:real") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q "d:real") THEN ASM_REWRITE_TAC [] THEN GEN_TAC THEN
    DISCH_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_SUB_LT] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP REAL_INV_POS o CONJUNCT1) THEN
    DISCH_THEN (fun th => tactic_of do
      pure (ONCE_REWRITE_TAC [← GSYM (← MATCH_MP REAL_LT_RMUL_EQ th)])) THEN
    REWRITE_TAC [REAL_MUL_LZERO] THEN
    REWRITE_TAC [← GSYM REAL_NEG_LT0, REAL_NEG_RMUL] THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (REWRITE_TAC [← MATCH_MP REAL_NEG_INV
        (← GSYM (← MATCH_MP REAL_LT_IMP_NE (← CONJUNCT1 th)))])) THEN
    MATCH_MP_TAC ABS_SIGN2 THEN EXISTS_TAC (← q "l:real") THEN
    REWRITE_TAC [← GSYM real_div] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o funpow 3 LAND_CONV o RAND_CONV)
      [real_sub] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE o CONJUNCT1) THEN
    REWRITE_TAC [real_abs, ← GSYM REAL_NEG_LE0, REAL_NEG_NEG] THEN
    ASM_REWRITE_TAC [← GSYM REAL_NOT_LT])

  let DIFF_LMAX ← prove
   r"!f x l. (f diffl l)(x) /\
           (?d. &0 < d /\ (!y. abs(x - y) < d ==> f(y) <= f(x))) ==> (l = &0)"
   (← do
    -- THENL branches are evaluated right to left.
    let alt0 ← ASSUME (← q r"&0 < l")
    let altl ← ASSUME (← q r"l < &0")
    pure (REPEAT GEN_TAC THEN DISCH_THEN
       (CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_THEN (← q "k:real") STRIP_ASSUME_TAC)) THEN
      REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
       (← SPECL [← q "l:real", ← q r"&0"] REAL_LT_TOTAL) THEN
      ASM_REWRITE_TAC [] THENL
       [DISCH_THEN (MP_TAC o (fun th => CONJ th altl)) THEN
        DISCH_THEN (MP_TAC o MATCH_MP DIFF_LDEC) THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "e:real") MP_TAC) THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        MP_TAC (← SPECL [← q "k:real", ← q "e:real"] REAL_DOWN2) THEN
        ASM_REWRITE_TAC [] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "d:real") STRIP_ASSUME_TAC) THEN
        DISCH_THEN (MP_TAC o SPEC (← q "d:real")) THEN ASM_REWRITE_TAC [] THEN
        DISCH_TAC THEN FIRST_ASSUM (undischCheck (fun c => pure (is_forall c))) THEN
        DISCH_THEN (MP_TAC o SPEC (← q "x - d")) THEN REWRITE_TAC [REAL_SUB_SUB2] THEN
        SUBGOAL_THEN (← q r"&0 <= d") ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
        ASM_REWRITE_TAC [real_abs] THEN ASM_REWRITE_TAC [← GSYM REAL_NOT_LT],
        DISCH_THEN (MP_TAC o (fun th => CONJ th alt0)) THEN
        DISCH_THEN (MP_TAC o MATCH_MP DIFF_LINC) THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "e:real") MP_TAC) THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        MP_TAC (← SPECL [← q "k:real", ← q "e:real"] REAL_DOWN2) THEN
        ASM_REWRITE_TAC [] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "d:real") STRIP_ASSUME_TAC) THEN
        DISCH_THEN (MP_TAC o SPEC (← q "d:real")) THEN ASM_REWRITE_TAC [] THEN
        DISCH_TAC THEN FIRST_ASSUM (undischCheck (fun c => pure (is_forall c))) THEN
        DISCH_THEN (MP_TAC o SPEC (← q "x + d")) THEN REWRITE_TAC [REAL_ADD_SUB2] THEN
        SUBGOAL_THEN (← q r"&0 <= d") ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
        REWRITE_TAC [ABS_NEG] THEN
        ASM_REWRITE_TAC [real_abs] THEN ASM_REWRITE_TAC [← GSYM REAL_NOT_LT]]))

  let DIFF_LMIN ← prove
   r"!f x l. (f diffl l)(x) /\
           (?d. &0 < d /\ (!y. abs(x - y) < d ==> f(x) <= f(y))) ==> (l = &0)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC (← SPECL [← q r"\x:real. --(f x)", ← q "x:real", ← q "--l"] DIFF_LMAX) THEN
    BETA_TAC THEN REWRITE_TAC [REAL_LE_NEG2, REAL_NEG_EQ0] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC DIFF_NEG THEN ASM_REWRITE_TAC [])

  let DIFF_LCONST ← prove
   r"!f x l. (f diffl l)(x) /\
         (?d. &0 < d /\ (!y. abs(x - y) < d ==> (f(y) = f(x)))) ==> (l = &0)"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "d:real") STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC DIFF_LMAX THEN
    MAP_EVERY EXISTS_TAC [← q r"f:real->real", ← q "x:real"] THEN ASM_REWRITE_TAC [] THEN
    EXISTS_TAC (← q "d:real") THEN ASM_REWRITE_TAC [] THEN GEN_TAC THEN
    DISCH_THEN (fun th => FIRST_ASSUM (SUBST1_TAC o (fun a => MATCH_MP a th))) THEN
    MATCH_ACCEPT_TAC REAL_LE_REFL)

  let INTERVAL_LEMMA_LT ← prove
   r"!a b x. a < x /\ x < b ==>
        ?d. &0 < d /\ !y. abs(x - y) < d ==> a < y /\ y < b"
   (← do
    let ltRadd ← do
      let (a, _) ← EQ_IMP_RULE (← SPEC_ALL REAL_LT_RADD)
      GEN_ALL a
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM ABS_BETWEEN] THEN
      DISJ_CASES_TAC (← SPECL [← q "x - a", ← q "b - x"] REAL_LE_TOTAL) THENL
       [EXISTS_TAC (← q "x - a"), EXISTS_TAC (← q "b - x")] THEN
      ASM_REWRITE_TAC [REAL_SUB_LT] THEN GEN_TAC THEN
      REWRITE_TAC [REAL_LT_SUB_LADD, REAL_LT_SUB_RADD] THEN
      REWRITE_TAC [real_sub, REAL_ADD_ASSOC] THEN
      REWRITE_TAC [← GSYM real_sub, REAL_LT_SUB_LADD, REAL_LT_SUB_RADD] THEN
      FREEZE_THEN (fun th => ONCE_REWRITE_TAC [th]) (← SPEC (← q "x:real") REAL_ADD_SYM) THEN
      REWRITE_TAC [REAL_LT_RADD] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC ltRadd THENL
       [EXISTS_TAC (← q "a:real") THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
        EXISTS_TAC (← q "x + x") THEN ASM_REWRITE_TAC [] THEN
        UNDISCH_TAC (← q "(x - a) <= (b - x)"),
         EXISTS_TAC (← q "b:real") THEN MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC (← q "x + x") THEN ASM_REWRITE_TAC [] THEN
        UNDISCH_TAC (← q "(b - x) <= (x - a)")] THEN
      REWRITE_TAC [REAL_LE_SUB_LADD, ← GSYM REAL_LE_SUB_RADD] THEN
      MATCH_MP_TAC EQ_IMP THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [real_sub] THEN
      REWRITE_TAC [REAL_ADD_AC]))

  let INTERVAL_LEMMA ← prove
   r"!a b x. a < x /\ x < b ==>
        ?d. &0 < d /\ !y. abs(x - y) < d ==> a <= y /\ y <= b"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (X_CHOOSE_TAC (← q "d:real") o MATCH_MP INTERVAL_LEMMA_LT) THEN
    EXISTS_TAC (← q "d:real") THEN ASM_REWRITE_TAC [] THEN GEN_TAC THEN
    DISCH_THEN (fun th => FIRST_ASSUM (MP_TAC o (fun a => MATCH_MP a th) o CONJUNCT2)) THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC [])

  let ROLLE ← prove
   r"!f a b. a < b /\
           (f(a) = f(b)) /\
           (!x. a <= x /\ x <= b ==> f contl x) /\
           (!x. a < x /\ x < b ==> f differentiable x)
        ==> ?z. a < z /\ z < b /\ (f diffl &0)(z)"
   (← do
    let fR ← q r"f:real->real"
    -- The THENL list and the THEN chain are evaluated right to left.
    let axab ← ASSUME (← q r"a < x /\ x < b")
    let mean ← MATCH_MP REAL_MEAN (← ASSUME (← q "a < b"))
    pure (REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
      MP_TAC (← SPECL [fR, ← q "a:real", ← q "b:real"] CONT_ATTAINS) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q "M:real") MP_TAC) THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC (← q "x1:real"))) THEN
      MP_TAC (← SPECL [fR, ← q "a:real", ← q "b:real"] CONT_ATTAINS2) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q "m:real") MP_TAC) THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC (← q "x2:real"))) THEN
      ASM_CASES_TAC (← q r"a < x1 /\ x1 < b") THENL
       [FIRST_ASSUM (X_CHOOSE_THEN (← q "d:real") MP_TAC o MATCH_MP INTERVAL_LEMMA) THEN
        DISCH_THEN STRIP_ASSUME_TAC THEN EXISTS_TAC (← q "x1:real") THEN
        ASM_REWRITE_TAC [] THEN SUBGOAL_THEN
         (← q r"?l. (f diffl l)(x1) /\
              ?d. &0 < d /\ (!y. abs(x1 - y) < d ==> f(y) <= f(x1))") MP_TAC THENL
         [CONV_TAC EXISTS_AND_CONV THEN CONJ_TAC THENL
           [REWRITE_TAC [← GSYM differentiable] THEN FIRST_ASSUM MATCH_MP_TAC THEN
            ASM_REWRITE_TAC [],
            EXISTS_TAC (← q "d:real") THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q "y:real") THEN
            DISCH_TAC THEN REPEAT (FIRST_ASSUM MATCH_MP_TAC) THEN
            ASM_REWRITE_TAC []], ALL_TAC] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "l:real") MP_TAC) THEN
        DISCH_THEN (fun th => tactic_of do
          pure (ASSUME_TAC th THEN SUBST_ALL_TAC (← MATCH_MP DIFF_LMAX th)))
        THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
      ASM_CASES_TAC (← q r"a < x2 /\ x2 < b") THENL
       [FIRST_ASSUM (X_CHOOSE_THEN (← q "d:real") MP_TAC o MATCH_MP INTERVAL_LEMMA) THEN
        DISCH_THEN STRIP_ASSUME_TAC THEN EXISTS_TAC (← q "x2:real") THEN
        ASM_REWRITE_TAC [] THEN SUBGOAL_THEN
         (← q r"?l. (f diffl l)(x2) /\
              ?d. &0 < d /\ (!y. abs(x2 - y) < d ==> f(x2) <= f(y))") MP_TAC THENL
         [CONV_TAC EXISTS_AND_CONV THEN CONJ_TAC THENL
           [REWRITE_TAC [← GSYM differentiable] THEN FIRST_ASSUM MATCH_MP_TAC THEN
            ASM_REWRITE_TAC [],
            EXISTS_TAC (← q "d:real") THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q "y:real") THEN
            DISCH_TAC THEN REPEAT (FIRST_ASSUM MATCH_MP_TAC) THEN
            ASM_REWRITE_TAC []], ALL_TAC] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "l:real") MP_TAC) THEN
        DISCH_THEN (fun th => tactic_of do
          pure (ASSUME_TAC th THEN SUBST_ALL_TAC (← MATCH_MP DIFF_LMIN th))) THEN
      ASM_REWRITE_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"!x. a <= x /\ x <= b ==> (f(x):real = f(b))") MP_TAC THENL
       [REPEAT (FIRST_ASSUM (undischCheck (fun c => pure (is_neg c)))) THEN
        ASM_REWRITE_TAC [REAL_LT_LE] THEN REWRITE_TAC [DE_MORGAN_THM] THEN
        REPEAT (DISCH_THEN (DISJ_CASES_THEN2 (MP_TAC o SYM) MP_TAC) THEN
                DISCH_THEN (SUBST_ALL_TAC o AP_TERM fR)) THEN
        UNDISCH_TAC (← q r"(f:real->real) a = f b") THEN
        DISCH_THEN (fun th => SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
        GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [← GSYM REAL_LE_ANTISYM] THEN
        (CONJ_TAC THENL
          [SUBGOAL_THEN (← q r"(f:real->real) b = M") SUBST1_TAC THENL
            [FIRST_ASSUM (ACCEPT_TAC o (fun th => el 2 (CONJUNCTS th))),
             FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []],
           SUBGOAL_THEN (← q r"(f:real->real) b = m") SUBST1_TAC THENL
            [FIRST_ASSUM (ACCEPT_TAC o (fun th => el 2 (CONJUNCTS th))),
             FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []]]),
        X_CHOOSE_TAC (← q "x:real") mean THEN
        DISCH_TAC THEN EXISTS_TAC (← q "x:real") THEN
        REWRITE_TAC [axab] THEN
        FIRST_ASSUM (MP_TAC o MATCH_MP INTERVAL_LEMMA) THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "d:real") STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN (← q r"?l. (f diffl l)(x) /\
            (?d. &0 < d /\ (!y. abs(x - y) < d ==> (f(y) = f(x))))") MP_TAC THENL
         [CONV_TAC (ONCE_DEPTH_CONV EXISTS_AND_CONV) THEN CONJ_TAC THENL
           [REWRITE_TAC [← GSYM differentiable] THEN FIRST_ASSUM MATCH_MP_TAC THEN
            ASM_REWRITE_TAC [],
            EXISTS_TAC (← q "d:real") THEN ASM_REWRITE_TAC [] THEN GEN_TAC THEN
            DISCH_THEN (fun th => FIRST_ASSUM (MP_TAC o (fun a => MATCH_MP a th))) THEN
            DISCH_THEN (fun th => FIRST_ASSUM (MP_TAC o (fun a => MATCH_MP a th))) THEN
            DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN
            FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THEN
            MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC []],
          DISCH_THEN (X_CHOOSE_THEN (← q "l:real") (fun th => tactic_of do
           pure (ASSUME_TAC th THEN SUBST_ALL_TAC (← MATCH_MP DIFF_LCONST th)))) THEN
          ASM_REWRITE_TAC []]]))

  let MVT_LEMMA ← prove
   r"!(f:real->real) a b.
        (\x. f(x) - (((f(b) - f(a)) / (b - a)) * x))(a) =
        (\x. f(x) - (((f(b) - f(a)) / (b - a)) * x))(b)"
   (REPEAT GEN_TAC THEN BETA_TAC THEN
    ASM_CASES_TAC (← q "b:real = a") THEN ASM_REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    RULE_ASSUM_TAC (ONCE_REWRITE_RULE [← GSYM REAL_SUB_0]) THEN
    MP_TAC (← GENL [← q "x:real", ← q "y:real"]
     (← SPECL [← q "x:real", ← q "y:real", ← q "b - a"] REAL_EQ_RMUL)) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC id [← GSYM th])) THEN
    REWRITE_TAC [REAL_SUB_RDISTRIB, ← GSYM REAL_MUL_ASSOC] THEN
    FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP REAL_DIV_RMUL th])) THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
    REWRITE_TAC [real_sub, REAL_LDISTRIB, REAL_RDISTRIB] THEN
    REWRITE_TAC [← GSYM REAL_NEG_LMUL, ← GSYM REAL_NEG_RMUL,
                REAL_NEG_ADD, REAL_NEG_NEG] THEN
    REWRITE_TAC [← GSYM REAL_ADD_ASSOC] THEN
    REWRITE_TAC [← AC REAL_ADD_AC
      (← q r"w + x + y + z = (y + w) + (x + z)"), REAL_ADD_LINV, REAL_ADD_LID] THEN
    REWRITE_TAC [REAL_ADD_RID])

  let MVT ← prove
   r"!f a b. a < b /\
           (!x. a <= x /\ x <= b ==> f contl x) /\
           (!x. a < x /\ x < b ==> f differentiable x)
        ==> ?l z. a < z /\ z < b /\ (f diffl l)(z) /\
            (f(b) - f(a) = (b - a) * l)"
   (← do
    let ez2 ← q "z:real"
    let ez1 ← q r"((f(b) - f(a)) / (b - a))"
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
      MP_TAC (← SPECL [← q r"\x. f(x) - (((f(b) - f(a)) / (b - a)) * x)",
                       ← q "a:real", ← q "b:real"] ROLLE) THEN
      subgoalAnte2 (fun t => REWRITE_TAC [t]) THENL
       [ASM_REWRITE_TAC [MVT_LEMMA] THEN BETA_TAC THEN
        CONJ_TAC THEN X_GEN_TAC (← q "x:real") THENL
         [DISCH_TAC THEN CONV_TAC (ONCE_DEPTH_CONV HABS_CONV) THEN
          MATCH_MP_TAC CONT_SUB THEN CONJ_TAC THENL
           [CONV_TAC (ONCE_DEPTH_CONV ETA_CONV) THEN
            FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
            CONV_TAC (ONCE_DEPTH_CONV HABS_CONV) THEN MATCH_MP_TAC CONT_MUL THEN
            REWRITE_TAC [CONT_CONST] THEN MATCH_MP_TAC DIFF_CONT THEN
            EXISTS_TAC (← q r"&1") THEN MATCH_ACCEPT_TAC DIFF_X],
          DISCH_THEN (fun th => FIRST_ASSUM (MP_TAC o (fun a => MATCH_MP a th))) THEN
          REWRITE_TAC [differentiable] THEN DISCH_THEN (X_CHOOSE_TAC (← q "l:real")) THEN
          EXISTS_TAC (← q r"l - ((f(b) - f(a)) / (b - a))") THEN
          CONV_TAC (ONCE_DEPTH_CONV HABS_CONV) THEN MATCH_MP_TAC DIFF_SUB THEN
          CONJ_TAC THENL
           [CONV_TAC (ONCE_DEPTH_CONV ETA_CONV) THEN FIRST_ASSUM ACCEPT_TAC,
            CONV_TAC (ONCE_DEPTH_CONV HABS_CONV) THEN REWRITE_TAC [] THEN
            GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_MUL_RID] THEN
            MATCH_MP_TAC DIFF_CMUL THEN MATCH_ACCEPT_TAC DIFF_X]],
        ALL_TAC] THEN
      REWRITE_TAC [CONJ_ASSOC] THEN DISCH_THEN (X_CHOOSE_THEN (← q "z:real") MP_TAC) THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN (fun th => MAP_EVERY EXISTS_TAC [ez1, ez2] THEN MP_TAC th) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => CONJ_TAC THEN MP_TAC th) THENL
       [ALL_TAC, DISCH_THEN (fun _ => ALL_TAC) THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC REAL_DIV_LMUL THEN REWRITE_TAC [REAL_SUB_0] THEN
        DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q "a < a") THEN
        REWRITE_TAC [REAL_LT_REFL]] THEN
      SUBGOAL_THEN (← q r"((\x. ((f(b) - f(a)) / (b - a)) * x ) diffl
                          ((f(b) - f(a)) / (b - a)))(z)")
      (fun th => DISCH_THEN (MP_TAC o (fun a => CONJ a th))) THENL
       [CONV_TAC (ONCE_DEPTH_CONV HABS_CONV) THEN REWRITE_TAC [] THEN
        GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC DIFF_CMUL THEN REWRITE_TAC [DIFF_X], ALL_TAC] THEN
      DISCH_THEN (MP_TAC o MATCH_MP DIFF_ADD) THEN BETA_TAC THEN
      REWRITE_TAC [REAL_SUB_ADD] THEN CONV_TAC (ONCE_DEPTH_CONV ETA_CONV) THEN
      REWRITE_TAC [REAL_ADD_LID]))

  let MVT_ALT ← prove
   r"!f f' a b.
        a < b /\ (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x))
        ==> ?z. a < z /\ z < b /\ (f b - f a = (b - a) * f'(z))"
   (REPEAT STRIP_TAC THEN SUBGOAL_THEN
     (← q r"?l z. a < z /\ z < b /\ (f diffl l) z /\ (f b - f a = (b - a) * l)")
    MP_TAC THENL
     [MATCH_MP_TAC MVT THEN REWRITE_TAC [differentiable] THEN
      ASM_MESON_TAC [DIFF_CONT, REAL_LT_IMP_LE],
      ASM_MESON_TAC [DIFF_UNIQ, REAL_LT_IMP_LE]])

  let DIFF_ISCONST_END ← prove
   r"!f a b. a < b /\
           (!x. a <= x /\ x <= b ==> f contl x) /\
           (!x. a < x /\ x < b ==> (f diffl &0)(x))
        ==> (f b = f a)"
   (← do
    let z ← q r"&0"
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
      MP_TAC (← SPECL [← q r"f:real->real", ← q "a:real", ← q "b:real"] MVT) THEN
      ASM_REWRITE_TAC [] THEN
      subgoalAnte2 MP_TAC THENL
       [GEN_TAC THEN REWRITE_TAC [differentiable] THEN
        DISCH_THEN (fun th => EXISTS_TAC z THEN MP_TAC th) THEN
        ASM_REWRITE_TAC [],
        DISCH_THEN (fun th => REWRITE_TAC [th])] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "l:real") (X_CHOOSE_THEN (← q "x:real") MP_TAC)) THEN
      ONCE_REWRITE_TAC [← TAUT (← q r"a /\ b /\ c /\ d <=> (a /\ b) /\ (c /\ d)")] THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
      DISCH_THEN (fun th => FIRST_ASSUM (MP_TAC o (fun a => MATCH_MP a th))) THEN
      DISCH_THEN (MP_TAC o CONJ (← ASSUME (← q "(f diffl l)(x)"))) THEN
      DISCH_THEN (SUBST_ALL_TAC o MATCH_MP DIFF_UNIQ) THEN
      RULE_ASSUM_TAC (REWRITE_RULE [REAL_MUL_RZERO, REAL_SUB_0]) THEN
      FIRST_ASSUM ACCEPT_TAC))

  let DIFF_ISCONST ← prove
   r"!f a b. a < b /\
           (!x. a <= x /\ x <= b ==> f contl x) /\
           (!x. a < x /\ x < b ==> (f diffl &0)(x))
        ==> !x. a <= x /\ x <= b ==> (f x = f a)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"f:real->real", ← q "a:real", ← q "x:real"] DIFF_ISCONST_END) THEN
    DISJ_CASES_THEN MP_TAC (← REWRITE_RULE [REAL_LE_LT] (← ASSUME (← q "a <= x"))) THENL
     [DISCH_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
      CONJ_TAC THEN X_GEN_TAC (← q "z:real") THEN STRIP_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "x:real"),
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q "x:real")] THEN
      ASM_REWRITE_TAC [],
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC []])

  let DIFF_ISCONST_END_SIMPLE ← prove
   r"!f a b. a < b /\
           (!x. a <= x /\ x <= b ==> (f diffl &0)(x))
        ==> (f b = f a)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC DIFF_ISCONST_END THEN
    ASM_MESON_TAC [DIFF_CONT, REAL_LT_IMP_LE])

  let DIFF_ISCONST_ALL ← prove
   r"!f x y. (!x. (f diffl &0)(x)) ==> (f(x) = f(y))"
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q "!x. f contl x") ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC DIFF_CONT THEN
      EXISTS_TAC (← q r"&0") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    REPEAT GEN_TAC THEN REPEAT_TCL DISJ_CASES_THEN MP_TAC
     (← SPECL [← q "x:real", ← q "y:real"] REAL_LT_TOTAL) THENL
     [DISCH_THEN SUBST1_TAC THEN REFL_TAC,
      CONV_TAC (RAND_CONV SYM_CONV),
      ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC DIFF_ISCONST_END THEN
    ASM_REWRITE_TAC [])

  let INTERVAL_ABS ← REAL_ARITH
   (← q r"!x z d. (x - d) <= z /\ z <= (x + d) <=> abs(z - x) <= d")

  -- @@RETURN BEGIN
  return { DIFF_LINC, DIFF_LDEC, DIFF_LMAX, DIFF_LMIN, DIFF_LCONST, INTERVAL_LEMMA_LT,
           INTERVAL_LEMMA, ROLLE, MVT_LEMMA, MVT, MVT_ALT, DIFF_ISCONST_END,
           DIFF_ISCONST, DIFF_ISCONST_END_SIMPLE, DIFF_ISCONST_ALL, INTERVAL_ABS }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Continuous injections; continuity and differentiability of inverse       -/
/- functions.  (analysis.ml 6062-6331)                                       -/
/- ------------------------------------------------------------------------- -/

structure Inverse where
  -- @@FIELDS
  CONT_INJ_LEMMA : thm
  CONT_INJ_LEMMA2 : thm
  CONT_INJ_RANGE : thm
  CONT_INVERSE : thm
  DIFF_INVERSE : thm
  DIFF_INVERSE_LT : thm
  deriving Inhabited

@[nospecialize]
def setupInverse [HolBase] (D : AnalysisDeps) (BReals1 : Reals1) (BReals2 : Reals2) (BReals3 : Reals3) (BAbs : Abs) (BLims : Lims) (BDiffs : Diffs) (BCont : Cont) (BMvt : Mvt) :
    ExceptT String IO Inverse := do
  -- @@SCOPE BEGIN
  let { CONJ_ASSOC, EQ_IMP, REAL_ADD_ASSOC, REAL_ADD_SUB, REAL_ADD_SYM, .. } := D.core1
  let { REAL_DIV_RMUL, REAL_DOWN2, REAL_LET_TRANS, REAL_LE_ADDR, REAL_LT_ADDR,
        REAL_LT_REFL, REAL_LT_TRANS, REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LINV, .. } := D.core2
  let { REAL_MUL_SYM, real_abs, real_div, .. } := D.core3
  let { REAL_LE_LADD, REAL_LE_REFL, REAL_LE_TOTAL, REAL_LE_TRANS, REAL_LTE_TRANS,
        REAL_LT_IMP_LE, REAL_LT_LE, REAL_MUL_RZERO, REAL_NEG_NEG, REAL_SUB_ADD2, .. } := BReals1
  let { REAL_LE_DOUBLE, REAL_LT_HALF1, REAL_LT_HALF2, REAL_LT_IMP_NE, REAL_NEG_SUB,
        REAL_SUB_0, REAL_SUB_LE, REAL_SUB_LT, REAL_SUB_REFL, .. } := BReals2
  let { REAL_INV_MUL_WEAK, REAL_LE_NEG2, REAL_LE_SUB_LADD, REAL_LE_SUB_RADD,
        REAL_LT_SUB_RADD, REAL_SUB_LZERO, REAL_SUB_RZERO, REAL_SUB_SUB, .. } := BReals3
  let { ABS_0, ABS_NEG, ABS_NZ, ABS_ZERO, .. } := BAbs
  let { CONTL_LIM, CONT_COMPOSE, CONT_NEG, DIFF_CONT, LIM, LIM_INV, LIM_TRANSFORM,
        contl, .. } := BLims
  let { DIFF_CARAT, IVT, IVT2, .. } := BDiffs
  let { CONT_ATTAINS_ALL, .. } := BCont
  let { INTERVAL_ABS, .. } := BMvt
  -- @@SCOPE END
  -- `W(C SUBGOAL_THEN MP_TAC o fst o dest_imp o dest_neg o snd)`
  let subgoalNegAnte : tactic := fun gl => ExceptT.run do
    let t ← liftExcept (do pure (← dest_imp (← dest_neg gl.2)).1)
    ExceptT.mk (SUBGOAL_THEN t MP_TAC gl)

  let CONT_INJ_LEMMA ← prove
   r"!f g x d. &0 < d /\
            (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
            (!z. abs(z - x) <= d ==> f contl z) ==>
     ~(!z. abs(z - x) <= d ==> f(z) <= f(x))"
   (← do
    let xmd ← q "x - d"
    let xpd ← q "x + d"
    let gR ← q r"g:real->real"
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
      IMP_RES_THEN ASSUME_TAC REAL_LT_IMP_LE THEN
      DISCH_THEN (fun th => MAP_EVERY (fun t => tactic_of do pure (MP_TAC (← SPEC t th)))
        [xmd, xpd]) THEN
      REWRITE_TAC [REAL_ADD_SUB, REAL_SUB_SUB, ABS_NEG] THEN
      ASM_REWRITE_TAC [real_abs, REAL_LE_REFL] THEN
      DISCH_TAC THEN DISCH_TAC THEN DISJ_CASES_TAC
        (← SPECL [← q r"f(x - d):real", ← q r"f(x + d):real"] REAL_LE_TOTAL) THENL
       [MP_TAC (← SPECL [← q r"f:real->real", xmd, ← q "x:real", ← q r"f(x + d):real"] IVT) THEN
        ASM_REWRITE_TAC [REAL_LE_SUB_RADD, REAL_LE_ADDR] THEN
        subgoalNegAnte THENL
         [X_GEN_TAC (← q "z:real") THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
          ONCE_REWRITE_TAC [← GSYM ABS_NEG] THEN
          REWRITE_TAC [real_abs, REAL_SUB_LE] THEN
          ASM_REWRITE_TAC [REAL_NEG_SUB, REAL_SUB_LE, REAL_LE_SUB_RADD] THEN
          ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN ASM_REWRITE_TAC [],
          DISCH_THEN (fun th => REWRITE_TAC [th]) THEN
          DISCH_THEN (X_CHOOSE_THEN (← q "z:real") STRIP_ASSUME_TAC) THEN
          FIRST_ASSUM (MP_TAC o AP_TERM gR) THEN
          SUBGOAL_THEN (← q r"g((f:real->real) z) = z") SUBST1_TAC THENL
           [FIRST_ASSUM MATCH_MP_TAC THEN
            ONCE_REWRITE_TAC [← GSYM ABS_NEG] THEN
            REWRITE_TAC [real_abs, REAL_SUB_LE] THEN
            ASM_REWRITE_TAC [REAL_NEG_SUB, REAL_SUB_LE, REAL_LE_SUB_RADD] THEN
            ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
          SUBGOAL_THEN (← q r"g(f(x + d):real) = x + d") SUBST1_TAC THENL
           [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [REAL_ADD_SUB] THEN
            ASM_REWRITE_TAC [real_abs, REAL_LE_REFL], ALL_TAC] THEN
          REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
          MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q "x:real") THEN
          ASM_REWRITE_TAC [REAL_LT_ADDR]],
        MP_TAC (← SPECL [← q r"f:real->real", ← q "x:real", xpd, ← q r"f(x - d):real"] IVT2) THEN
        ASM_REWRITE_TAC [REAL_LE_SUB_RADD, REAL_LE_ADDR] THEN
        subgoalNegAnte THENL
         [X_GEN_TAC (← q "z:real") THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
          ASM_REWRITE_TAC [real_abs, REAL_SUB_LE, REAL_LE_SUB_RADD] THEN
          ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN ASM_REWRITE_TAC [],
          DISCH_THEN (fun th => REWRITE_TAC [th]) THEN
          DISCH_THEN (X_CHOOSE_THEN (← q "z:real") STRIP_ASSUME_TAC) THEN
          FIRST_ASSUM (MP_TAC o AP_TERM gR) THEN
          SUBGOAL_THEN (← q r"g((f:real->real) z) = z") SUBST1_TAC THENL
           [FIRST_ASSUM MATCH_MP_TAC THEN
            ASM_REWRITE_TAC [real_abs, REAL_SUB_LE, REAL_LE_SUB_RADD] THEN
            ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
          SUBGOAL_THEN (← q r"g(f(x - d):real) = x - d") SUBST1_TAC THENL
           [FIRST_ASSUM MATCH_MP_TAC THEN
            REWRITE_TAC [REAL_SUB_SUB, ABS_NEG] THEN
            ASM_REWRITE_TAC [real_abs, REAL_LE_REFL], ALL_TAC] THEN
          REWRITE_TAC [] THEN CONV_TAC (RAND_CONV SYM_CONV) THEN
          MATCH_MP_TAC REAL_LT_IMP_NE THEN
          MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q "x:real") THEN
          ASM_REWRITE_TAC [REAL_LT_SUB_RADD, REAL_LT_ADDR]]]))

  let CONT_INJ_LEMMA2 ← prove
   r"!f g x d. &0 < d /\
            (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
            (!z. abs(z - x) <= d ==> f contl z) ==>
     ~(!z. abs(z - x) <= d ==> f(x) <= f(z))"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"\x:real. --(f x)", ← q r"\y. (g(--y):real)", ← q "x:real", ← q "d:real"]
      CONT_INJ_LEMMA) THEN
    BETA_TAC THEN ASM_REWRITE_TAC [REAL_NEG_NEG, REAL_LE_NEG2] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CONT_NEG THEN
    FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC)

  let CONT_INJ_RANGE ← prove
   r"!f g x d.  &0 < d /\
            (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
            (!z. abs(z - x) <= d ==> f contl z) ==>
        ?e. &0 < e /\
            (!y. abs(y - f(x)) <= e ==> ?z. abs(z - x) <= d /\ (f z = y))"
   (← do
    let fgxd ← [← q r"f:real->real", ← q r"g:real->real", ← q "x:real", ← q "d:real"].mapM pure
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
      IMP_RES_THEN ASSUME_TAC REAL_LT_IMP_LE THEN
      MP_TAC (← SPECL [← q r"f:real->real", ← q "x - d", ← q "x + d"] CONT_ATTAINS_ALL) THEN
      ASM_REWRITE_TAC [INTERVAL_ABS, REAL_LE_SUB_RADD] THEN
      ASM_REWRITE_TAC [← GSYM REAL_ADD_ASSOC, REAL_LE_ADDR, REAL_LE_DOUBLE] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "L:real") (X_CHOOSE_THEN (← q "M:real") MP_TAC)) THEN
      STRIP_TAC THEN
      SUBGOAL_THEN (← q r"L <= f(x:real) /\ f(x) <= M") STRIP_ASSUME_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC [REAL_SUB_REFL, ABS_0], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"L < f(x:real) /\ f(x:real) < M") STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN ASM_REWRITE_TAC [REAL_LT_LE] THENL
         [DISCH_THEN SUBST_ALL_TAC THEN MP_TAC (← SPECL fgxd CONT_INJ_LEMMA2),
          DISCH_THEN (SUBST_ALL_TAC o SYM) THEN MP_TAC (← SPECL fgxd CONT_INJ_LEMMA)] THEN
        ASM_REWRITE_TAC [] THEN GEN_TAC THEN
        DISCH_THEN (fun t => FIRST_ASSUM (fun th => tactic_of do
          pure (REWRITE_TAC [← MATCH_MP th t] THEN NO_TAC))),
        MP_TAC (← SPECL [← q r"f(x:real) - L", ← q r"M - f(x:real)"] REAL_DOWN2) THEN
        ASM_REWRITE_TAC [REAL_SUB_LT] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "e:real") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q "e:real") THEN ASM_REWRITE_TAC [] THEN
        GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [← GSYM INTERVAL_ABS] THEN
        REWRITE_TAC [REAL_LE_SUB_RADD] THEN ONCE_REWRITE_TAC [← GSYM CONJ_ASSOC] THEN
        FIRST_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC (← q r"abs(y - f(x:real)) <= e") THEN
        REWRITE_TAC [← GSYM INTERVAL_ABS] THEN STRIP_TAC THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"f(x:real) - e") THEN
          ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [REAL_LE_SUB_LADD] THEN
          ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
          REWRITE_TAC [← GSYM REAL_LE_SUB_LADD],
          MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC (← q r"f(x:real) + (M - f(x))") THEN CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"f(x:real) + e") THEN
            ASM_REWRITE_TAC [REAL_LE_LADD],
            REWRITE_TAC [REAL_SUB_ADD2, REAL_LE_REFL]]] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC []]))

  let CONT_INVERSE ← prove
   r"!f g x d. &0 < d /\
             (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
             (!z. abs(z - x) <= d ==> f contl z)
        ==> g contl (f x)"
   (← do
    let fxh ← q r"f(x:real) + h"
    let ahk ← q r"abs(h) <= k"
    let zR ← q "z:real"
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [contl, LIM] THEN
      X_GEN_TAC (← q "a:real") THEN DISCH_TAC THEN
      MP_TAC (← SPECL [← q "a:real", ← q "d:real"] REAL_DOWN2) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "e:real") STRIP_ASSUME_TAC) THEN
      IMP_RES_THEN ASSUME_TAC REAL_LT_IMP_LE THEN
      SUBGOAL_THEN (← q r"!z. abs(z - x) <= e ==> (g(f z :real) = z)") ASSUME_TAC THENL
       [X_GEN_TAC (← q "z:real") THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "e:real") THEN ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"!z. abs(z - x) <= e ==> (f contl z)") ASSUME_TAC THENL
       [X_GEN_TAC (← q "z:real") THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "e:real") THEN ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      UNDISCH_TAC (← q r"!z. abs(z - x) <= d ==> (g(f z :real) = z)") THEN
      UNDISCH_TAC (← q r"!z. abs(z - x) <= d ==> (f contl z)") THEN
      DISCH_THEN (fun _ => ALL_TAC) THEN DISCH_THEN (fun _ => ALL_TAC) THEN
      MP_TAC (← SPECL [← q r"f:real->real", ← q r"g:real->real", ← q "x:real", ← q "e:real"]
        CONT_INJ_RANGE) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "k:real") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q "k:real") THEN ASM_REWRITE_TAC [] THEN
      X_GEN_TAC (← q "h:real") THEN BETA_TAC THEN REWRITE_TAC [REAL_SUB_RZERO] THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC
        (ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE)) THEN
      REWRITE_TAC [← GSYM ABS_NZ] THEN DISCH_TAC THEN
      FIRST_ASSUM (fun th => tactic_of do
        pure (MP_TAC (← SPEC fxh th) THEN
          REWRITE_TAC [REAL_ADD_SUB, ← ASSUME ahk] THEN
          DISCH_THEN (X_CHOOSE_THEN zR STRIP_ASSUME_TAC))) THEN
      FIRST_ASSUM (undischCheck (fun c => pure (is_eq c))) THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q "e:real") THEN
      SUBGOAL_THEN (← q r"(g((f:real->real)(z)) = z) /\ (g(f(x)) = x)")
        (fun t => ASM_REWRITE_TAC [t]) THEN CONJ_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [REAL_SUB_REFL, ABS_0]))

  let DIFF_INVERSE ← prove
   r"!f g l x d. &0 < d /\
               (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
               (!z. abs(z - x) <= d ==> f contl z) /\
               (f diffl l)(x) /\
               ~(l = &0)
        ==> (g diffl (inv l))(f x)"
   (← do
    let fR ← q r"f:real->real"
    let afgy ← ASSUME (← q r"f((g:real->real)(y)) = y")
    pure (REPEAT STRIP_TAC THEN UNDISCH_TAC (← q "(f diffl l)(x)") THEN
      DISCH_THEN (fun th => tactic_of do
        pure (ASSUME_TAC (← MATCH_MP DIFF_CONT th) THEN MP_TAC th)) THEN
      REWRITE_TAC [DIFF_CARAT] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"h:real->real") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"\y. if y = f(x) then
        inv(h(g y)) else (g(y) - g(f(x:real))) / (y - f(x))") THEN BETA_TAC THEN
      ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC (← q "z:real") THEN COND_CASES_TAC THEN
        ASM_REWRITE_TAC [REAL_SUB_REFL, REAL_MUL_RZERO] THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
        ASM_REWRITE_TAC [REAL_SUB_0],
        ALL_TAC,
        FIRST_ASSUM (SUBST1_TAC o SYM) THEN REPEAT AP_TERM_TAC THEN
        FIRST_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC [REAL_SUB_REFL, ABS_0] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC []] THEN
      REWRITE_TAC [CONTL_LIM] THEN BETA_TAC THEN REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"g((f:real->real)(x)) = x") ASSUME_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [REAL_SUB_REFL, ABS_0] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE, ALL_TAC] THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC LIM_TRANSFORM THEN EXISTS_TAC (← q r"\y:real. inv(h(g(y):real))") THEN
      BETA_TAC THEN CONJ_TAC THENL
       [ALL_TAC,
        SUBST1_TAC (← SYM (← ExceptT.mk (ONCE_DEPTH_CONV BETA_CONV
          (← q r"\y. inv((\y:real. h(g(y):real)) y)")))) THEN
        MATCH_MP_TAC LIM_INV THEN ASM_REWRITE_TAC [] THEN
        SUBGOAL_THEN (← q r"(\y:real. h(g(y):real)) contl (f(x:real))") MP_TAC THENL
         [MATCH_MP_TAC CONT_COMPOSE THEN ASM_REWRITE_TAC [] THEN
          MATCH_MP_TAC CONT_INVERSE THEN EXISTS_TAC (← q "d:real"),
          REWRITE_TAC [CONTL_LIM] THEN BETA_TAC] THEN
        ASM_REWRITE_TAC []] THEN
      SUBGOAL_THEN (← q r"?e. &0 < e /\
                        !y. &0 < abs(y - f(x:real)) /\
                            abs(y - f(x:real)) < e ==>
                                (f(g(y)) = y) /\ ~(h(g(y)) = &0)")
      STRIP_ASSUME_TAC THENL
       [ALL_TAC,
        REWRITE_TAC [LIM] THEN X_GEN_TAC (← q "k:real") THEN DISCH_TAC THEN
        EXISTS_TAC (← q "e:real") THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q "y:real") THEN
        DISCH_THEN (fun th => tactic_of do
          pure (FIRST_ASSUM (STRIP_ASSUME_TAC o (fun a => MATCH_MP a th)) THEN
            ASSUME_TAC (← REWRITE_RULE [← GSYM ABS_NZ, REAL_SUB_0] (← CONJUNCT1 th)))) THEN
        BETA_TAC THEN ASM_REWRITE_TAC [REAL_SUB_RZERO] THEN
        SUBGOAL_THEN (← q r"y - f(x) = h(g(y)) * (g(y) - x)") SUBST1_TAC THENL
         [FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [← GSYM th])) THEN
          REWRITE_TAC [afgy],
          UNDISCH_TAC (← q r"&0 < k") THEN
          MATCH_MP_TAC EQ_IMP THEN
          AP_THM_TAC THEN AP_TERM_TAC THEN
          CONV_TAC SYM_CONV THEN REWRITE_TAC [ABS_ZERO, REAL_SUB_0]] THEN
        SUBGOAL_THEN (← q r"~(g(y:real) - x = &0)") ASSUME_TAC THENL
         [REWRITE_TAC [REAL_SUB_0] THEN
          DISCH_THEN (MP_TAC o AP_TERM fR) THEN
          ASM_REWRITE_TAC [], REWRITE_TAC [real_div]] THEN
        SUBGOAL_THEN (← q r"inv((h(g(y))) * (g(y:real) - x)) =
          inv(h(g(y))) * inv(g(y) - x)") SUBST1_TAC THENL
         [MATCH_MP_TAC REAL_INV_MUL_WEAK THEN ASM_REWRITE_TAC [],
          REWRITE_TAC [REAL_MUL_ASSOC] THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
          REWRITE_TAC [REAL_MUL_ASSOC] THEN
          GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_LID] THEN
          AP_THM_TAC THEN AP_TERM_TAC THEN
          MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC []]] THEN
      SUBGOAL_THEN
        (← q r"?e. &0 < e /\
             !y. &0 < abs(y - f(x:real)) /\ abs(y - f(x)) < e ==> (f(g(y)) = y)")
      (X_CHOOSE_THEN (← q "c:real") STRIP_ASSUME_TAC) THENL
       [MP_TAC (← SPECL [fR, ← q r"g:real->real", ← q "x:real", ← q "d:real"]
          CONT_INJ_RANGE) THEN ASM_REWRITE_TAC [] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "e:real") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q "e:real") THEN ASM_REWRITE_TAC [] THEN
        X_GEN_TAC (← q "y:real") THEN DISCH_THEN (MP_TAC o CONJUNCT2) THEN
        DISCH_THEN (MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
        DISCH_THEN (fun th => FIRST_ASSUM (MP_TAC o (fun a => MATCH_MP a th))) THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "z:real") STRIP_ASSUME_TAC) THEN
        UNDISCH_TAC (← q r"(f:real->real)(z) = y") THEN
        DISCH_THEN (SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN
        (← q r"?e. &0 < e /\
             !y. &0 < abs(y - f(x:real)) /\ abs(y - f(x)) < e
                        ==> ~((h:real->real)(g(y)) = &0)")
      (X_CHOOSE_THEN (← q "b:real") STRIP_ASSUME_TAC) THENL
       [ALL_TAC,
        MP_TAC (← SPECL [← q "b:real", ← q "c:real"] REAL_DOWN2) THEN
        ASM_REWRITE_TAC [] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "e:real") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q "e:real") THEN ASM_REWRITE_TAC [] THEN
        X_GEN_TAC (← q "y:real") THEN STRIP_TAC THEN CONJ_TAC THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (← q "e:real") THEN
        ASM_REWRITE_TAC []] THEN
      SUBGOAL_THEN (← q r"(\y. h(g(y:real):real)) contl (f(x:real))") MP_TAC THENL
       [MATCH_MP_TAC CONT_COMPOSE THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC CONT_INVERSE THEN EXISTS_TAC (← q "d:real") THEN
        ASM_REWRITE_TAC [], ALL_TAC] THEN
      REWRITE_TAC [CONTL_LIM, LIM] THEN DISCH_THEN (MP_TAC o SPEC (← q "abs(l)")) THEN
      ASM_REWRITE_TAC [← GSYM ABS_NZ] THEN BETA_TAC THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "e:real") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q "e:real") THEN ASM_REWRITE_TAC [ABS_NZ] THEN X_GEN_TAC (← q "y:real") THEN
      RULE_ASSUM_TAC (REWRITE_RULE [ABS_NZ]) THEN
      DISCH_THEN (fun th => FIRST_ASSUM (MP_TAC o (fun a => MATCH_MP a th))) THEN
      REWRITE_TAC [← GSYM ABS_NZ] THEN
      CONV_TAC CONTRAPOS_CONV THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [REAL_SUB_LZERO, ABS_NEG, REAL_LT_REFL]))

  let DIFF_INVERSE_LT ← prove
   r"!f g l x d. &0 < d /\
               (!z. abs(z - x) < d ==> (g(f(z)) = z)) /\
               (!z. abs(z - x) < d ==> f contl z) /\
               (f diffl l)(x) /\
               ~(l = &0)
        ==> (g diffl (inv l))(f x)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC DIFF_INVERSE THEN
    EXISTS_TAC (← q r"d / &2") THEN ASM_REWRITE_TAC [REAL_LT_HALF1] THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q r"d / &2") THEN
    ASM_REWRITE_TAC [REAL_LT_HALF2])

  -- @@RETURN BEGIN
  return { CONT_INJ_LEMMA, CONT_INJ_LEMMA2, CONT_INJ_RANGE, CONT_INVERSE, DIFF_INVERSE,
           DIFF_INVERSE_LT }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Darboux continuity of derivatives; uniform convergence; uniform           -/
/- continuity on closed intervals; `remove_interface "-->"`.                 -/
/- (analysis.ml 6333-6735)                                                   -/
/- ------------------------------------------------------------------------- -/

structure Uniform where
  -- @@FIELDS
  IVT_DERIVATIVE_0 : thm
  IVT_DERIVATIVE_POS : thm
  IVT_DERIVATIVE_NEG : thm
  SEQ_CONT_UNIFORM : thm
  SER_COMPARA_UNIFORM : thm
  SER_COMPARA_UNIFORM_WEAK : thm
  CONTL : thm
  CONTL_SEQ : thm
  SUP_INTERVAL : thm
  CONT_UNIFORM : thm
  CONT_UNIFORM_STRONG : thm
  deriving Inhabited

@[nospecialize]
def setupUniform [HolBase] (D : AnalysisDeps) (BReals1 : Reals1) (BReals2 : Reals2) (BReals3 : Reals3) (BPow : Pow) (BSums : Sums) (BSeqs : Seqs) (BSeries1 : Series1) (BSeries2 : Series2) (BLims : Lims) (BDiffs : Diffs) (BCont : Cont) (BMvt : Mvt) :
    ExceptT String IO Uniform := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC,
        remove_interface, .. } := D
  let { ADD_SYM, ARITH, ARITH_EQ, CONTRAPOS_THM, GE, LEFT_IMP_EXISTS_THM, LE_ADD,
        LE_TRANS, MONO_EXISTS, REAL_ABS_NUM, REAL_ABS_SUB, REAL_ADD_LID, REAL_ADD_SYM, .. } := D.core1
  let { REAL_DIV_LMUL, REAL_DOWN2, REAL_EQ_NEG2, REAL_EQ_SUB_RADD, REAL_LET_TRANS,
        REAL_LE_ADDL, REAL_LE_ANTISYM, REAL_LE_LDIV_EQ, REAL_LT_DIV, REAL_LT_LDIV_EQ,
        REAL_LT_RDIV_EQ, REAL_LT_REFL, REAL_LT_TRANS, .. } := D.core2
  let { REAL_MUL_SYM, REAL_OF_NUM_EQ, REAL_OF_NUM_LT, REAL_WLOG_LE,
        RIGHT_IMP_EXISTS_THM, SKOLEM_THM, real_gt, .. } := D.core3
  let { REAL_LE_LADD, REAL_LE_LT, REAL_LE_REFL, REAL_LE_TRANS, REAL_LTE_TRANS,
        REAL_LT_01, REAL_LT_ANTISYM, REAL_LT_IMP_LE, REAL_LT_LE, REAL_MUL_RID,
        REAL_NOT_LE, REAL_NOT_LT, .. } := BReals1
  let { REAL_SUB_REFL, .. } := BReals2
  let { REAL_LE_SUB_LADD, REAL_LE_SUB_RADD, REAL_LT_NEG2, REAL_LT_SUB_LADD,
        REAL_LT_SUB_RADD, .. } := BReals3
  let { REAL_SUP, .. } := BPow
  let { SUM_ABS_LE, SUM_LE, SUM_TWO, .. } := BSums
  let { SEQ, .. } := BSeqs
  let { summable, sums, .. } := BSeries1
  let { SER_CAUCHY, SER_COMPAR, .. } := BSeries2
  let { CONTL_LIM, DIFF_CONT, LIM, .. } := BLims
  let { DIFF_CMUL, DIFF_NEG, DIFF_SUB, DIFF_X, .. } := BDiffs
  let { CONT_ATTAINS, .. } := BCont
  let { DIFF_LDEC, DIFF_LINC, DIFF_LMAX, .. } := BMvt
  -- @@SCOPE END
  let IVT_DERIVATIVE_0 ← prove
   r"!f f' a b.
        a <= b /\
        (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x)) /\
        f'(a) > &0 /\ f'(b) < &0
        ==> ?z. a < z /\ z < b /\ (f'(z) = &0)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [real_gt] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [REAL_LE_LT] THEN
    STRIP_TAC THENL [ALL_TAC, ASM_MESON_TAC [REAL_LT_ANTISYM]] THEN
    SUBGOAL_THEN (← q r"?w. (!x. a <= x /\ x <= b ==> f x <= w) /\
                      (?x. a <= x /\ x <= b /\ (f x = w))")
    MP_TAC THENL
     [MATCH_MP_TAC CONT_ATTAINS THEN
      ASM_MESON_TAC [REAL_LT_IMP_LE, DIFF_CONT], ALL_TAC] THEN
    DISCH_THEN (CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "z:real") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q "z:real") THEN ASM_CASES_TAC (← q "z:real = a") THENL
     [UNDISCH_THEN (← q "z:real = a") SUBST_ALL_TAC THEN
      MP_TAC (← SPECL [← q r"f:real->real", ← q "a:real", ← q r"(f':real->real) a"] DIFF_LINC) THEN
      ASM_SIMP_TAC [REAL_LE_REFL, REAL_LT_IMP_LE] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "d:real") STRIP_ASSUME_TAC) THEN
      MP_TAC (← SPECL [← q "d:real", ← q "b - a"] REAL_DOWN2) THEN
      ASM_REWRITE_TAC [REAL_LT_SUB_LADD, REAL_ADD_LID] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "e:real") STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC (← q r"!h. &0 < h /\ h < d ==> w < f (a + h)") THEN
      DISCH_THEN (MP_TAC o SPEC (← q "e:real")) THEN ASM_REWRITE_TAC [] THEN
      CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN (fun _ => ALL_TAC) THEN
      REWRITE_TAC [REAL_NOT_LT] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
      ASM_SIMP_TAC [REAL_LE_ADDL, REAL_LT_IMP_LE], ALL_TAC] THEN
    ASM_CASES_TAC (← q "z:real = b") THENL
     [UNDISCH_THEN (← q "z:real = b") SUBST_ALL_TAC THEN
      MP_TAC (← SPECL [← q r"f:real->real", ← q "b:real", ← q r"(f':real->real) b"] DIFF_LDEC) THEN
      ASM_SIMP_TAC [REAL_LE_REFL, REAL_LT_IMP_LE] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "d:real") STRIP_ASSUME_TAC) THEN
      MP_TAC (← SPECL [← q "d:real", ← q "b - a"] REAL_DOWN2) THEN
      ASM_REWRITE_TAC [REAL_LT_SUB_LADD, REAL_ADD_LID] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "e:real") STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC (← q r"!h. &0 < h /\ h < d ==> w < f (b - h)") THEN
      DISCH_THEN (MP_TAC o SPEC (← q "e:real")) THEN ASM_REWRITE_TAC [] THEN
      CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN (fun _ => ALL_TAC) THEN
      REWRITE_TAC [REAL_NOT_LT] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC [REAL_LE_SUB_LADD, REAL_LE_SUB_RADD] THEN
      ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
      ASM_SIMP_TAC [REAL_LE_ADDL, REAL_LT_IMP_LE], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"a < z /\ z < b") STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC [REAL_LT_LE], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC DIFF_LMAX THEN
    MP_TAC (← SPECL [← q "z - a", ← q "b - z"] REAL_DOWN2) THEN
    ASM_REWRITE_TAC [REAL_LT_SUB_LADD, REAL_ADD_LID] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "e:real") STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [← q r"f:real->real", ← q "z:real"] THEN
    ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN
    EXISTS_TAC (← q "e:real") THEN ASM_REWRITE_TAC [] THEN GEN_TAC THEN
    DISCH_THEN (fun th => FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
    MAP_EVERY UNDISCH_TAC [← q "e + z < b", ← q "e + a < z"] THEN
    REAL_ARITH_TAC)

  let IVT_DERIVATIVE_POS ← prove
   r"!f f' a b y.
        a <= b /\
        (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x)) /\
        f'(a) > y /\ f'(b) < y
        ==> ?z. a < z /\ z < b /\ (f'(z) = y)"
   (REWRITE_TAC [real_gt] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"\x. f(x) - y * x", ← q r"\x:real. f'(x) - y",
                     ← q "a:real", ← q "b:real"] IVT_DERIVATIVE_0) THEN
    ASM_REWRITE_TAC [real_gt] THEN
    ASM_REWRITE_TAC [REAL_LT_SUB_LADD, REAL_LT_SUB_RADD] THEN
    ASM_REWRITE_TAC [REAL_EQ_SUB_RADD, REAL_ADD_LID] THEN
    GEN_REWRITE_TAC (funpow 2 LAND_CONV o BINDER_CONV o RAND_CONV o
                     LAND_CONV o RAND_CONV) [← GSYM REAL_MUL_RID] THEN
    ASM_SIMP_TAC [DIFF_SUB, DIFF_X, DIFF_CMUL])

  let IVT_DERIVATIVE_NEG ← prove
   r"!f f' a b y.
        a <= b /\
        (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x)) /\
        f'(a) < y /\ f'(b) > y
        ==> ?z. a < z /\ z < b /\ (f'(z) = y)"
   (REWRITE_TAC [real_gt] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"\x:real. --(f x)", ← q r"\x:real. --(f' x)",
                     ← q "a:real", ← q "b:real", ← q "--y"] IVT_DERIVATIVE_POS) THEN
    ASM_REWRITE_TAC [real_gt, REAL_LT_NEG2, REAL_EQ_NEG2] THEN
    ASM_SIMP_TAC [DIFF_NEG])

  let SEQ_CONT_UNIFORM ← prove
   r"!s f x0. (!e. &0 < e
                 ==> ?N d. &0 < d /\
                           !x n. abs(x - x0) < d /\ n >= N
                                 ==> abs(s n x - f(x)) < e) /\
            (?N:num. !n. n >= N ==> (s n) contl x0)
            ==> f contl x0"
   (← do
    -- The later rule in the THEN chain is evaluated first.
    let ar ← ARITH_RULE (← q "M + N >= N:num")
    let ra ← REAL_ARITH
     (← q r"!fx sx fx0 sx0 e3.
          abs(sx - fx) < e3 /\ abs(sx0 - fx0) < e3 /\ abs(sx - sx0) < e3 /\
          (&3 * e3 = e)
          ==> abs(fx - fx0) < e")
    pure (REPEAT GEN_TAC THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC (← q "M:num"))) THEN
      REWRITE_TAC [CONTL_LIM, LIM] THEN X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"e / &3")) THEN
      ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH, LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q "N:num", ← q "d1:real"] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q "M + N:num")) THEN REWRITE_TAC [GE, LE_ADD] THEN
      REWRITE_TAC [CONTL_LIM, LIM] THEN DISCH_THEN (MP_TAC o SPEC (← q r"e / &3")) THEN
      ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "d2:real") STRIP_ASSUME_TAC) THEN
      MP_TAC (← SPECL [← q "d1:real", ← q "d2:real"] REAL_DOWN2) THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q "d:real") THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q "x:real") THEN STRIP_TAC THEN
      MATCH_MP_TAC ra THEN
      MAP_EVERY EXISTS_TAC
       [← q r"(s:num->real->real) (M + N) x",
        ← q r"(s:num->real->real) (M + N) x0",
        ← q r"e / &3"] THEN
      ASM_SIMP_TAC [REAL_DIV_LMUL, REAL_OF_NUM_EQ, ARITH] THEN
      ASM_MESON_TAC [REAL_SUB_REFL, REAL_ABS_NUM, REAL_LT_TRANS, ar]))

  let SER_COMPARA_UNIFORM ← prove
   r"!s x0 g.
        (?N d. &0 < d /\
               !n x. abs(x - x0) < d /\ n >= N
                     ==> abs(s x n) <= g n) /\ summable g
        ==> ?f d. &0 < d /\
                  !e. &0 < e
                      ==> ?N. !x n. abs(x - x0) < d /\ n >= N
                                    ==> abs(sum(0,n) (s x) - f(x)) < e"
   (← do
    -- The later rules in the THEN chain are evaluated first.
    let ra2 ← REAL_ARITH (← q r"abs(x) < a ==> x < a")
    let ra1 ← REAL_ARITH
     (← q r"abs(snm) < e2 /\ (&2 * e2 = e)
      ==> abs((sn + snm) - fx) < e2 ==> abs(sn - fx) < e")
    let ar ← ARITH_RULE (← q r"n >= M + N ==> n >= M /\ n >= N:num")
    pure (REPEAT STRIP_TAC THEN
      SUBGOAL_THEN (← q r"!x. abs(x - x0) < d ==> ?y. (s x) sums y") MP_TAC THENL
       [ASM_MESON_TAC [summable, SER_COMPAR], ALL_TAC] THEN
      GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
          [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"f:real->real") THEN DISCH_TAC THEN
      EXISTS_TAC (← q "d:real") THEN ASM_REWRITE_TAC [] THEN
      X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [SER_CAUCHY]) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"e / &2")) THEN
      ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q "M:num")) THEN
      EXISTS_TAC (← q "M + N:num") THEN ASM_REWRITE_TAC [] THEN
      MAP_EVERY X_GEN_TAC [← q "x:real", ← q "n:num"] THEN STRIP_TAC THEN
      FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP ar) THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q "x:real")) THEN ASM_REWRITE_TAC [sums, SEQ] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"e / &2")) THEN
      ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "m:num") (MP_TAC o SPEC (← q "m + n:num"))) THEN
      REWRITE_TAC [GE, LE_ADD] THEN ONCE_REWRITE_TAC [ADD_SYM] THEN
      ONCE_REWRITE_TAC [← GSYM SUM_TWO] THEN
      MATCH_MP_TAC ra1 THEN
      SIMP_TAC [REAL_DIV_LMUL, REAL_OF_NUM_EQ, ARITH] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC (← q r"sum(n,m) (\n. abs(s (x:real) n))") THEN
      REWRITE_TAC [SUM_ABS_LE] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q r"sum(n,m) g") THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUM_LE THEN X_GEN_TAC (← q "r:num") THEN STRIP_TAC THEN
        REWRITE_TAC [] THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_MESON_TAC [GE, LE_TRANS], ALL_TAC] THEN
      MATCH_MP_TAC ra2 THEN ASM_SIMP_TAC []))

  let SER_COMPARA_UNIFORM_WEAK ← prove
   r"!s x0 g.
        (?N d. &0 < d /\
               !n x. abs(x - x0) < d /\ n >= N
                     ==> abs(s x n) <= g n) /\ summable g
        ==> ?f. !e. &0 < e
                    ==> ?N d. &0 < d /\
                              !x n. abs(x - x0) < d /\ n >= N
                                    ==> abs(sum(0,n) (s x) - f(x)) < e"
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP SER_COMPARA_UNIFORM) THEN
    MESON_TAC [])

  let CONTL ← prove
   r"!f x. f contl x <=>
         !e. &0 < e ==> ?d. &0 < d /\ !x'. abs(x' - x) < d
                            ==> abs(f(x') - f(x)) < e"
   (← do
    -- The later rules in the THEN chain are evaluated first.
    let ra2 ← REAL_ARITH (← q r"abs(x - x) = &0")
    let t ← TAUT (← q r"(a ==> (b <=> c)) ==> ((a ==> b) <=> (a ==> c))")
    let ra1 ← REAL_ARITH (← q r"&0 < abs(x - y) <=> ~(x = y)")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [CONTL_LIM, LIM] THEN
      REWRITE_TAC [ra1] THEN
      AP_TERM_TAC THEN ABS_TAC THEN
      MATCH_MP_TAC t THEN
      DISCH_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
      ASM_MESON_TAC [ra2]))

  let CONTL_SEQ ← prove
   r"!f x l. f contl l /\ x tends_num_real l

           ==> (\n. f(x n)) tends_num_real f(l)"
   (REWRITE_TAC [CONTL, SEQ] THEN MESON_TAC [])

  let SUP_INTERVAL ← prove
   r"!P a b.
        (?x. a <= x /\ x <= b /\ P x)
        ==> ?s. a <= s /\ s <= b /\
                !y. y < s <=> (?x. a <= x /\ x <= b /\ P x /\ y < x)"
   (← do
    let ar ← ARITH_RULE (← q r"x <= b ==> x < b + &1")
    pure (REPEAT STRIP_TAC THEN
      MP_TAC (← SPEC (← q r"\x. a <= x /\ x <= b /\ P x") REAL_SUP) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC [] THEN
        ASM_MESON_TAC [ar],
        ALL_TAC] THEN
      ABBREV_TAC (← q r"s = sup (\x. a <= x /\ x <= b /\ P x)") THEN
      REWRITE_TAC [] THEN DISCH_TAC THEN EXISTS_TAC (← q "s:real") THEN
      ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC [REAL_LTE_TRANS, REAL_NOT_LE, REAL_LT_ANTISYM]))

  let CONT_UNIFORM ← prove
   r"!f a b. a <= b /\ (!x. a <= x /\ x <= b ==> f contl x)
           ==> !e. &0 < e ==> ?d. &0 < d /\
                                  !x y. a <= x /\ x <= b /\
                                        a <= y /\ y <= b /\
                                        abs(x - y) < d
                                        ==> abs(f(x) - f(y)) < e"
   (← do
    -- The THEN chain and THENL lists are evaluated right to left, so the
    -- rules nearest the end of the proof come first.
    let ra9 ← REAL_ARITH (← q r"&0 < d ==> d <= d * &2")
    let ra8 ← REAL_ARITH
     (← q r"!r t d d12.
         ~(x <= r /\ y <= r) /\
        abs(x - y) < d /\
        s - d12 < r /\ t <= s + d /\
        x <= t /\ y <= t /\ &2 * d12 <= e /\
        &2 * d < e ==> abs(x - s) < e /\ abs(y - s) < e")
    let as7 ← ASSUME
     (← q r"!x y. abs(x - s) < d1 /\ abs(y - s) < d1 ==> abs(f x - f y) < e")
    let ra6 ← REAL_ARITH (← q r"s < s + d <=> &0 < d")
    let ra5 ← REAL_ARITH (← q r"x - y < x <=> &0 < y")
    let ra4 ← REAL_ARITH (← q r"&0 < abs(x - s) <=> ~(x = s)")
    let ra3 ← REAL_ARITH
     (← q r"!a. abs(x - a) < e / &2 /\ abs(y - a) < e / &2 /\ (&2 * e / &2 = e)
            ==> abs(x - y) < e")
    let ra2 ← REAL_ARITH (← q r"d < d * &2 <=> &0 < d")
    let ra1 ← REAL_ARITH (← q r"abs(x - x) = &0")
    let sR ← q "s:real"
    pure (REPEAT STRIP_TAC THEN
      MP_TAC (← SPEC (← q r"\c. ?d. &0 < d /\
                         !x y. a <= x /\ x <= c /\
                               a <= y /\ y <= c /\
                               abs(x - y) < d
                               ==> abs(f(x) - f(y)) < e")
           SUP_INTERVAL) THEN
      DISCH_THEN (MP_TAC o SPECL [← q "a:real", ← q "b:real"]) THEN ANTS_TAC THENL
       [EXISTS_TAC (← q "a:real") THEN ASM_REWRITE_TAC [REAL_LE_REFL] THEN
        REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"&1") THEN
        REWRITE_TAC [REAL_OF_NUM_LT, ARITH] THEN
        ASM_MESON_TAC [REAL_LE_ANTISYM, ra1],
        ALL_TAC] THEN
      REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN sR STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN (← q r"?t. s < t /\ ?d. &0 < d /\
                                   !x y. a <= x /\ x <= t /\ a <= y /\ y <= t /\
                                         abs(x - y) < d ==> abs(f(x) - f(y)) < e")
      MP_TAC THENL
       [UNDISCH_TAC (← q r"!x. a <= x /\ x <= b ==> f contl x") THEN
        DISCH_THEN (MP_TAC o SPEC sR) THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [CONTL_LIM, LIM] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"e / &2")) THEN
        ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "d1:real") STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN (← q r"&0 < d1 / &2 /\ d1 / &2 < d1") STRIP_ASSUME_TAC THENL
         [ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH, REAL_LT_LDIV_EQ,
                        ra2],
          ALL_TAC] THEN
        SUBGOAL_THEN (← q r"!x y. abs(x - s) < d1 /\ abs(y - s) < d1
                            ==> abs(f(x) - f(y)) < e")
        ASSUME_TAC THENL
         [REPEAT STRIP_TAC THEN
          MATCH_MP_TAC ra3 THEN
          EXISTS_TAC (← q r"(f:real->real) s") THEN
          SIMP_TAC [REAL_DIV_LMUL, REAL_OF_NUM_EQ, ARITH] THEN
          SUBGOAL_THEN (← q r"!x. abs(x - s) < d1 ==> abs(f x - f s) < e / &2")
           (fun th => ASM_MESON_TAC [th]) THEN
          X_GEN_TAC (← q "u:real") THEN
          REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q "u:real = s") THENL
           [ASM_SIMP_TAC [REAL_SUB_REFL, REAL_ABS_NUM, REAL_LT_DIV,
                          REAL_OF_NUM_LT, ARITH],
            ALL_TAC] THEN
          ASM_MESON_TAC [ra4],
          ALL_TAC] THEN
        SUBGOAL_THEN (← q r"s - d1 / &2 < s") MP_TAC THENL
         [ASM_REWRITE_TAC [ra5],
          ALL_TAC] THEN
        DISCH_THEN (fun th => FIRST_ASSUM (fun th' => tactic_of do
          pure (MP_TAC (← GEN_REWRITE_RULE id [th'] th)))) THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "r:real") MP_TAC) THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "d2:real") STRIP_ASSUME_TAC) THEN
        MP_TAC (← SPECL [← q "d2:real", ← q r"d1 / &2"] REAL_DOWN2) THEN
        ASM_REWRITE_TAC [] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "d:real") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q r"s + d / &2") THEN
        ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH, ra6] THEN
        EXISTS_TAC (← q "d:real") THEN ASM_REWRITE_TAC [] THEN
        MAP_EVERY X_GEN_TAC [← q "x:real", ← q "y:real"] THEN STRIP_TAC THEN
        ASM_CASES_TAC (← q r"x <= r /\ y <= r") THENL
         [ASM_MESON_TAC [REAL_LT_TRANS], ALL_TAC] THEN
        MATCH_MP_TAC as7 THEN
        MATCH_MP_TAC ra8 THEN
        MAP_EVERY EXISTS_TAC [← q "r:real", ← q r"s + d / &2", ← q "d:real", ← q r"d1 / &2"] THEN
        ASM_REWRITE_TAC [REAL_LE_LADD] THEN
        SIMP_TAC [REAL_DIV_LMUL, REAL_OF_NUM_EQ, ARITH] THEN
        ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
        SIMP_TAC [REAL_LE_LDIV_EQ, ← GSYM REAL_LT_RDIV_EQ, REAL_OF_NUM_LT, ARITH] THEN
        ASM_SIMP_TAC [ra9, REAL_LE_REFL],
        ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "t:real") (CONJUNCTS_THEN ASSUME_TAC)) THEN
      SUBGOAL_THEN (← q "b <= t") (fun th => ASM_MESON_TAC [REAL_LE_TRANS, th]) THEN
      FIRST_X_ASSUM (X_CHOOSE_THEN (← q "d:real") STRIP_ASSUME_TAC) THEN
      UNDISCH_THEN (← q r"!x. a <= x /\ x <= b ==> f contl x") (fun _ => ALL_TAC) THEN
      FIRST_X_ASSUM (fun th => tactic_of do
        let th1 ← SPEC sR th
        pure (MP_TAC (← liftExcept (check (fun t => is_eq (concl t)) th1)))) THEN
      REWRITE_TAC [REAL_LT_REFL] THEN
      ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN REWRITE_TAC [REAL_NOT_LE] THEN
      DISCH_TAC THEN EXISTS_TAC (← q "t:real") THEN
      ASM_MESON_TAC [REAL_LT_IMP_LE, REAL_LE_TRANS]))

  let CONT_UNIFORM_STRONG ← prove
   r"!f a b. (!x. a <= x /\ x <= b ==> f contl x)
           ==> !e. &0 < e
                   ==> ?d. &0 < d /\
                           !x y. (a <= x /\ x <= b \/ a <= y /\ y <= b) /\
                                 abs(x - y) < d
                                 ==> abs(f(x) - f(y)) < e"
   (← do
    -- The THENL list is evaluated right to left.
    let ra5 ← REAL_ARITH
     (← q r"~(a <= x) /\ a <= y /\ abs(x - y) < d /\ d < d1
        ==> abs(x - a) < d1 /\ abs(y - a) < d1")
    let ra4 ← REAL_ARITH
     (← q r"!a. abs(x - a) < e / &2 /\ abs(y - a) < e / &2 /\ (&2 * e / &2 = e)
            ==> abs(x - y) < e")
    let ra3 ← REAL_ARITH
     (← q r"x <= b /\ ~(y <= b) /\ abs(x - y) < d /\ d < d1
        ==> abs(x - b) < d1 /\ abs(y - b) < d1")
    let ra2 ← REAL_ARITH
     (← q r"!a. abs(x - a) < e / &2 /\ abs(y - a) < e / &2 /\ (&2 * e / &2 = e)
            ==> abs(x - y) < e")
    let aR ← q "a:real"
    let bR ← q "b:real"
    pure (REPEAT STRIP_TAC THEN
      ASM_CASES_TAC (← q "a <= b") THENL
       [ALL_TAC, ASM_MESON_TAC [REAL_LE_TRANS, REAL_LT_01]] THEN
      FIRST_ASSUM (fun th => tactic_of do
        let tb ← SPEC bR th
        let ta ← SPEC aR th
        pure (MP_TAC ta THEN MP_TAC tb)) THEN
      REWRITE_TAC [CONTL, REAL_LE_REFL] THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"e / &2")) THEN
      ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "d1:real") STRIP_ASSUME_TAC) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"e / &2")) THEN
      ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "d2:real") STRIP_ASSUME_TAC) THEN
      MP_TAC (← SPECL [← q "d1:real", ← q "d2:real"] REAL_DOWN2) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "d0:real") STRIP_ASSUME_TAC) THEN
      MP_TAC (← SPECL [← q r"f:real->real", aR, bR] CONT_UNIFORM) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (MP_TAC o SPEC (← q "e:real")) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "d3:real") STRIP_ASSUME_TAC) THEN
      MP_TAC (← SPECL [← q "d0:real", ← q "d3:real"] REAL_DOWN2) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "d:real") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q "d:real") THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC REAL_WLOG_LE THEN CONJ_TAC THENL
       [MESON_TAC [REAL_ABS_SUB], ALL_TAC] THEN
      REPEAT STRIP_TAC THENL
       [ASM_CASES_TAC (← q "y <= b") THENL
         [ASM_MESON_TAC [REAL_LT_TRANS, REAL_LE_TRANS], ALL_TAC] THEN
        MATCH_MP_TAC ra2 THEN
        EXISTS_TAC (← q r"(f:real->real) b") THEN
        SIMP_TAC [REAL_DIV_LMUL, REAL_OF_NUM_EQ, ARITH_EQ] THEN
        ASM_MESON_TAC [REAL_LT_TRANS, ra3],
        ASM_CASES_TAC (← q "a <= x") THENL
         [ASM_MESON_TAC [REAL_LT_TRANS, REAL_LE_TRANS], ALL_TAC] THEN
        MATCH_MP_TAC ra4 THEN
        EXISTS_TAC (← q r"(f:real->real) a") THEN
        SIMP_TAC [REAL_DIV_LMUL, REAL_OF_NUM_EQ, ARITH_EQ] THEN
        ASM_MESON_TAC [REAL_LT_TRANS, ra5]]))

  -- Get rid of special syntax status of '-->'.
  remove_interface "-->"

  -- @@RETURN BEGIN
  return { IVT_DERIVATIVE_0, IVT_DERIVATIVE_POS, IVT_DERIVATIVE_NEG, SEQ_CONT_UNIFORM,
           SER_COMPARA_UNIFORM, SER_COMPARA_UNIFORM_WEAK, CONTL, CONTL_SEQ, SUP_INTERVAL,
           CONT_UNIFORM, CONT_UNIFORM_STRONG }
  -- @@RETURN END

end HolLibrary.Analysis
