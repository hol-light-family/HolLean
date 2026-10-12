/- ========================================================================= -/
/- Properties of power series.                                               -/
/- ========================================================================= -/
/- File: HolLibrary/Transc.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/transc.ml`, by hand, in file order, in
  the style of HolLibrary/Analysis.lean (see there and HolMath/Base.lean for
  the conventions).  Each section of transc.ml is a bundle (a `structure`)
  built by a `setup` function; SessionLibrary/Transc.lean builds the bundles
  in order, after all of analysis.ml (transc.ml begins with
  `needs "Library/analysis.ml"`), and exports every name under its HOL Light
  name.

  NAMES.  A name is looked up as OCaml's scoping gives: transc.ml's own
  earlier bindings, then analysis.ml's (its bundles are passed to the setups
  that use them, as `(AX : HolLibrary.Analysis.X)`), then the core library's
  (CoreThms1..2).  transc.ml rebinds SYM_CANON_CONV and EXT_CONV (analysis.ml)
  and DIVISION_0, REAL_DIV_SQRT, SQRT_EVEN_POW2 and SUM_DIFFS (core).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules (REAL_ARITH,
  ARITH_RULE, TAUT) they are bound first, in OCaml's order.

  STATE.  transc.ml changes the parser (prioritize_num, prioritize_real) and
  the basic rewrites (without BETA_THM at 871, with it again at 3327), and
  keeps `diff_net`, the derivative theorems DIFF_CONV uses, in a ref.  Each
  change is made by the setup of the bundle where it occurs.
-/

import HolLibrary.Analysis

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolLibrary.Analysis (ALPHA_CONV ETA_CONV SELECT_CONV ABS NO_TAC undischCheck endItlistM
  FREEZE_THEN)

namespace HolLibrary.Transc

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

/- ------------------------------------------------------------------------- -/
/- What transc.ml uses from the core library (supplied by Session).          -/
/- (Two structures, each under 128 fields: see HolLibrary/Words.lean.)       -/
/- ------------------------------------------------------------------------- -/

/-- Theorems transc.ml uses from the core library, ADD1 to REAL_ADD_RID. -/
structure CoreThms1 where
  (ADD1 ADD_AC ADD_ASSOC ADD_CLAUSES ADD_EQ_0 ADD_SUB ADD_SYM AND_FORALL_THM
   ARITH ARITH_EQ ARITH_EVEN BETA_THM COND_ID CONJ_ACI CONJ_ASSOC CONJ_SYM
   CONTRAPOS_THM DE_MORGAN_THM DIVISION DIV_MULT DIV_UNIQ EQ_IMP EQ_TRANS
   ETA_AX EVEN EVEN_ADD EVEN_DOUBLE EVEN_EXISTS EVEN_MOD EVEN_MULT
   EXISTS_REFL FACT FACT_LT FINITE_INDUCT_STRONG FORALL_AND_THM FORALL_SIMP
   FUN_EQ_THM GE IMP_CONJ IMP_IMP IN_INSERT LE LEFT_ADD_DISTRIB
   LEFT_AND_EXISTS_THM LEFT_FORALL_IMP_THM LEFT_IMP_EXISTS_THM LET_CASES
   LET_TRANS LE_0 LE_ADD LE_ANTISYM LE_EXISTS LE_LT LE_REFL LE_SUC LE_SUC_LT
   LE_TRANS LT LTE_CASES LTE_TRANS LT_0 LT_ADD_RCANCEL LT_IMP_LE LT_LE LT_NZ
   LT_REFL LT_SUC LT_TRANS MOD_0 MOD_MULT_ADD MONO_AND MONO_EXISTS
   MONO_FORALL MONO_IMP MULT_CLAUSES MULT_SYM NOT_EVEN NOT_EXISTS_THM
   NOT_FORALL_THM NOT_IMP NOT_IN_EMPTY NOT_LE NOT_LT NOT_ODD NOT_SUC
   num_CASES num_MAX num_WOP ODD_DOUBLE ODD_EXISTS POW_2_SQRT POW_2_SQRT_ABS
   PRE real_abs REAL_ABS_0 REAL_ABS_ABS REAL_ABS_DIV REAL_ABS_INV
   REAL_ABS_MUL REAL_ABS_NEG REAL_ABS_NUM REAL_ABS_NZ REAL_ABS_POS
   REAL_ABS_POW REAL_ADD2_SUB2 REAL_ADD_AC REAL_ADD_ASSOC REAL_ADD_LDISTRIB
   REAL_ADD_LID REAL_ADD_LINV REAL_ADD_RDISTRIB REAL_ADD_RID : thm)
  deriving Inhabited

/-- Theorems transc.ml uses from the core library, REAL_ADD_RINV to UNWIND_THM2. -/
structure CoreThms2 where
  (REAL_ADD_RINV REAL_ADD_SUB REAL_ADD_SYM REAL_DIFFSQ real_div REAL_DIV_1
   REAL_DIV_LMUL REAL_DIV_REFL REAL_DIV_RMUL REAL_DOWN REAL_DOWN2 REAL_ENTIRE
   REAL_EQ_IMP_LE REAL_EQ_LDIV_EQ REAL_EQ_MUL_LCANCEL REAL_EQ_MUL_RCANCEL
   REAL_EQ_NEG2 REAL_EQ_RDIV_EQ REAL_EQ_SUB_LADD REAL_EQ_SUB_RADD REAL_INV_0
   REAL_INV_1 REAL_INV_1_LE REAL_INV_DIV REAL_INV_LE_1 REAL_INV_MUL
   REAL_INV_NEG REAL_LET_ADD REAL_LET_TOTAL REAL_LET_TRANS REAL_LE_01
   REAL_LE_ADD2 REAL_LE_ADDL REAL_LE_ADDR REAL_LE_ANTISYM REAL_LE_DIV
   REAL_LE_INV REAL_LE_INV2 REAL_LE_INV_EQ REAL_LE_LCANCEL_IMP
   REAL_LE_LDIV_EQ REAL_LE_LMUL REAL_LE_MUL2 REAL_LE_RDIV_EQ REAL_LE_RMUL
   REAL_LT_ADDL REAL_LT_ADDR REAL_LT_DIV REAL_LT_INV REAL_LT_INV2
   REAL_LT_INV_EQ REAL_LT_LDIV_EQ REAL_LT_MIN REAL_LT_MUL REAL_LT_MUL2
   REAL_LT_RDIV_EQ REAL_LT_REFL REAL_LT_TOTAL REAL_LT_TRANS REAL_MUL_2
   REAL_MUL_AC REAL_MUL_ASSOC REAL_MUL_LID REAL_MUL_LINV REAL_MUL_LNEG
   REAL_MUL_RNEG REAL_MUL_SYM REAL_OF_NUM_ADD REAL_OF_NUM_EQ REAL_OF_NUM_LE
   REAL_OF_NUM_LT REAL_OF_NUM_MUL REAL_OF_NUM_SUC real_pow REAL_POW2_ABS
   REAL_POW_1 REAL_POW_1_LE REAL_POW_2 REAL_POW_ADD REAL_POW_DIV
   REAL_POW_EQ_0 REAL_POW_INV REAL_POW_LE REAL_POW_LE2 REAL_POW_LT
   REAL_POW_MONO REAL_POW_MUL REAL_POW_NEG REAL_POW_ONE REAL_POW_POW real_sub
   RIGHT_AND_EXISTS_THM RIGHT_FORALL_IMP_THM RIGHT_IMP_EXISTS_THM
   RIGHT_IMP_FORALL_THM SELECT_AX SELECT_UNIQUE SKOLEM_THM SQRT_0 SQRT_POS_LE
   SQRT_POS_LT SQRT_POW_2 SQRT_UNIQUE SUB_0 SUB_ADD SUB_EQ_0 SUB_REFL SUB_SUC
   SUC_INJ SWAP_EXISTS_THM SWAP_FORALL_THM UNWIND_THM2 : thm)
  deriving Inhabited

/-- What transc.ml uses from Session besides theorems. -/
structure TranscDeps where
  -- definitions
  new_definition : String → ExceptT String IO thm
  -- parser state and basic rewrites
  prioritize_num : IO Unit
  prioritize_real : IO Unit
  basic_rewrites : IO (List thm)
  set_basic_rewrites : List thm → ExceptT String IO Unit
  extend_basic_rewrites : List thm → ExceptT String IO Unit
  -- decision procedures and tactics
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_MESON_TAC : List thm → tactic
  ASM_REAL_ARITH_TAC : tactic
  INDUCT_TAC : tactic
  MESON_TAC : List thm → tactic
  NUM_REDUCE_TAC : tactic
  REAL_ARITH : term → ExceptT String IO thm
  REAL_ARITH_TAC : tactic
  -- conversions
  EXPAND_CASES_CONV : ioconv
  GEN_BETA_CONV : ioconv
  NUM_REDUCE_CONV : ioconv
  REAL_RAT_REDUCE_CONV : ioconv
  num_CONV : ioconv
  core1 : CoreThms1
  core2 : CoreThms2

/-- tactics.ml's `CONTR_TAC`. -/
def CONTR_TAC [HolBase] : thm_tactic := HolCore.Tactics.CONTR_TAC HolBase.B

/- ------------------------------------------------------------------------- -/
/- Properties of power series: rearranging finite sums, the circle of        -/
/- convergence, formal differentiation.  (transc.ml 1-182)                   -/
/- ------------------------------------------------------------------------- -/

structure PowSer where
  -- @@FIELDS
  POWDIFF_LEMMA : thm
  POWDIFF : thm
  POWREV : thm
  POWSER_INSIDEA : thm
  POWSER_INSIDE : thm
  diffs : thm
  DIFFS_NEG : thm
  DIFFS_LEMMA : thm
  DIFFS_LEMMA2 : thm
  DIFFS_EQUIV : thm
  deriving Inhabited

@[nospecialize]
def setupPowSer [HolBase] (D : TranscDeps) (ACompat : HolLibrary.Analysis.Compat) (ANames : HolLibrary.Analysis.Names) (ATactics : HolLibrary.Analysis.Tactics) (AReals1 : HolLibrary.Analysis.Reals1) (AReals2 : HolLibrary.Analysis.Reals2) (AReals3 : HolLibrary.Analysis.Reals3) (AAbs : HolLibrary.Analysis.Abs) (APow : HolLibrary.Analysis.Pow) (ASums : HolLibrary.Analysis.Sums) (ASeqs : HolLibrary.Analysis.Seqs) (ASeqs2 : HolLibrary.Analysis.Seqs2) (ASeqLim : HolLibrary.Analysis.SeqLim) (ASeries1 : HolLibrary.Analysis.Series1) (ASeries2 : HolLibrary.Analysis.Series2) :
    ExceptT String IO PowSer := do
  -- @@SCOPE BEGIN
  let { INDUCT_TAC, new_definition, .. } := D
  let { ADD_CLAUSES, ADD_SYM, LE_REFL, LT, LT_IMP_LE, NOT_LT, REAL_ADD_AC,
        REAL_ADD_ASSOC, REAL_ADD_LID, REAL_ADD_LINV, .. } := D.core1
  let { REAL_EQ_SUB_LADD, REAL_LET_TRANS, REAL_MUL_AC, REAL_MUL_ASSOC, REAL_MUL_SYM,
        SUB_0, SUB_REFL, real_div, real_sub, .. } := D.core2
  let { FORALL_IMP_CONV, LEFT_IMP_EXISTS_CONV, .. } := ACompat
  let { SUB_OLD, SUC_SUB1, .. } := ANames
  let { HABS_CONV, .. } := ATactics
  let { REAL_ADD_LID_UNIQ, REAL_LDISTRIB, REAL_LE_REFL, REAL_LT_IMP_LE, REAL_MUL_LZERO,
        REAL_MUL_RID, REAL_MUL_RZERO, REAL_NEG_LMUL, REAL_NEG_NEG, REAL_NEG_RMUL,
        REAL_NOT_LT, .. } := AReals1
  let { REAL_LT_IMP_NE, REAL_NEG_SUB, REAL_SUB_0, REAL_SUB_LDISTRIB, .. } := AReals2
  let { REAL_EQ_LMUL2, REAL_LE_RDIV, REAL_LE_RMUL_EQ, REAL_LT_1, REAL_SUB_RZERO, .. } := AReals3
  let { ABS_0, ABS_ABS, ABS_CASES, ABS_INV, ABS_MUL, ABS_NZ, ABS_POS, .. } := AAbs
  let { POW_ABS, POW_ADD, POW_INV, POW_MUL, POW_NZ, pow, .. } := APow
  let { SUM_CMUL, SUM_SUBST, sum, .. } := ASums
  let { SEQ_BOUNDED, SEQ_CBOUNDED, SEQ_SUB, convergent, .. } := ASeqs
  let { SEQ_CAUCHY, .. } := ASeqs2
  let { SEQ_SUC, .. } := ASeqLim
  let { SUMMABLE_SUM, summable, sums, .. } := ASeries1
  let { GP, SER_ACONV, SER_CMUL, SER_COMPAR, SER_ZERO, .. } := ASeries2
  -- @@SCOPE END
  -- More theorems about rearranging finite sums

  let POWDIFF_LEMMA ← prove
   r"!n x y. sum(0,SUC n)(\p. (x pow p) * y pow ((SUC n) - p)) =
                y * sum(0,SUC n)(\p. (x pow p) * (y pow (n - p)))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM SUM_CMUL] THEN
    MATCH_MP_TAC SUM_SUBST THEN X_GEN_TAC (← q "p:num") THEN DISCH_TAC THEN
    BETA_TAC THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN (← q r"~(n < p:num)") ASSUME_TAC THENL
     [POP_ASSUM (MP_TAC o CONJUNCT2) THEN REWRITE_TAC [ADD_CLAUSES] THEN
      REWRITE_TAC [NOT_LT, ← CONJUNCT2 LT] THEN
      DISCH_THEN (DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THEN
      REWRITE_TAC [LE_REFL, LT_IMP_LE],
      ASM_REWRITE_TAC [SUB_OLD] THEN REWRITE_TAC [pow] THEN
      MATCH_ACCEPT_TAC REAL_MUL_SYM])

  let POWDIFF ← prove
   r"!n x y. (x pow (SUC n)) - (y pow (SUC n)) =
                (x - y) * sum(0,SUC n)(\p. (x pow p) * (y pow (n - p)))"
   (INDUCT_TAC THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC [sum] THEN
      REWRITE_TAC [REAL_ADD_LID, ADD_CLAUSES, SUB_0] THEN
      BETA_TAC THEN REWRITE_TAC [pow] THEN
      REWRITE_TAC [REAL_MUL_RID],
      REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [sum] THEN
      REWRITE_TAC [ADD_CLAUSES] THEN BETA_TAC THEN
      REWRITE_TAC [POWDIFF_LEMMA] THEN REWRITE_TAC [REAL_LDISTRIB] THEN
      ONCE_REWRITE_TAC [← AC REAL_MUL_AC
        (← q r"a * (b * c) = b * (a * c)")] THEN
      POP_ASSUM (fun th => tactic_of do pure (ONCE_REWRITE_TAC [← GSYM th])) THEN
      REWRITE_TAC [SUB_REFL] THEN
      SPEC_TAC (← q "SUC n", ← q "n:num") THEN GEN_TAC THEN
      REWRITE_TAC [pow, REAL_MUL_RID] THEN
      REWRITE_TAC [REAL_LDISTRIB, REAL_SUB_LDISTRIB] THEN
      REWRITE_TAC [real_sub] THEN
      ONCE_REWRITE_TAC [← AC REAL_ADD_AC
        (← q r"(a + b) + (c + d) = (d + a) + (c + b)")] THEN
      GEN_REWRITE_TAC (funpow 2 LAND_CONV) [REAL_MUL_SYM] THEN
      CONV_TAC SYM_CONV THEN REWRITE_TAC [REAL_ADD_LID_UNIQ] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
      REWRITE_TAC [REAL_ADD_LINV]])

  let POWREV ← prove
   r"!n x y. sum(0,SUC n)(\p. (x pow p) * (y pow (n - p))) =
                sum(0,SUC n)(\p. (x pow (n - p)) * (y pow p))"
   (← do
    let REAL_EQ_LMUL2' ← CONV_RULE (REDEPTH_CONV FORALL_IMP_CONV) REAL_EQ_LMUL2
    pure (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "x:real = y") THENL
     [ASM_REWRITE_TAC [← GSYM POW_ADD] THEN
      MATCH_MP_TAC SUM_SUBST THEN X_GEN_TAC (← q "p:num") THEN
      BETA_TAC THEN DISCH_TAC THEN AP_TERM_TAC THEN
      MATCH_ACCEPT_TAC ADD_SYM,
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
      RULE_ASSUM_TAC (ONCE_REWRITE_RULE [← GSYM REAL_SUB_0]) THEN
      FIRST_ASSUM (fun th => tactic_of do
        pure (GEN_REWRITE_TAC id [← MATCH_MP REAL_EQ_LMUL2' th])) THEN
      GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_NEG_NEG] THEN
      ONCE_REWRITE_TAC [REAL_NEG_LMUL] THEN
      ONCE_REWRITE_TAC [REAL_NEG_SUB] THEN
      REWRITE_TAC [← GSYM POWDIFF] THEN REWRITE_TAC [REAL_NEG_SUB]]))

  -- Show (essentially) that a power series has a "circle" of convergence,
  -- i.e. if it sums for x, then it sums absolutely for z with |z| < |x|.

  let POWSER_INSIDEA ← prove
   r"!f x z. summable (\n. f(n) * (x pow n)) /\ abs(z) < abs(x)
        ==> summable (\n. abs(f(n)) * (z pow n))"
   (← do
    let th ← do
      let (_, b) ← EQ_IMP_RULE (← SPEC_ALL convergent)
      GEN_ALL (← CONV_RULE LEFT_IMP_EXISTS_CONV b)
    pure (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      DISCH_THEN (MP_TAC o MATCH_MP SER_ZERO) THEN
      DISCH_THEN (MP_TAC o MATCH_MP th) THEN REWRITE_TAC [← GSYM SEQ_CAUCHY] THEN
      DISCH_THEN (MP_TAC o MATCH_MP SEQ_CBOUNDED) THEN
      REWRITE_TAC [SEQ_BOUNDED] THEN BETA_TAC THEN
      DISCH_THEN (X_CHOOSE_TAC (← q "K:real")) THEN MATCH_MP_TAC SER_COMPAR THEN
      EXISTS_TAC (← q r"\n. (K * abs(z pow n)) / abs(x pow n)") THEN CONJ_TAC THENL
       [EXISTS_TAC (← q "0") THEN X_GEN_TAC (← q "n:num") THEN DISCH_THEN (fun _ => ALL_TAC) THEN
        BETA_TAC THEN MATCH_MP_TAC REAL_LE_RDIV THEN CONJ_TAC THENL
         [REWRITE_TAC [← GSYM ABS_NZ] THEN MATCH_MP_TAC POW_NZ THEN
          REWRITE_TAC [ABS_NZ] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
          EXISTS_TAC (← q "abs(z)") THEN ASM_REWRITE_TAC [ABS_POS],
          REWRITE_TAC [ABS_MUL, ABS_ABS, ← GSYM REAL_MUL_ASSOC] THEN
          ONCE_REWRITE_TAC [← AC REAL_MUL_AC
           (← q r"a * b * c = (a * c) * b")] THEN
          DISJ_CASES_TAC (← SPEC (← q "z pow n") ABS_CASES) THEN
          ASM_REWRITE_TAC [ABS_0, REAL_MUL_RZERO, REAL_LE_REFL] THEN
          FIRST_ASSUM (fun th => tactic_of do
            pure (REWRITE_TAC [← MATCH_MP REAL_LE_RMUL_EQ th])) THEN
          MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC [← GSYM ABS_MUL]],
        REWRITE_TAC [summable] THEN
        EXISTS_TAC (← q r"K * inv(&1 - (abs(z) / abs(x)))") THEN
        REWRITE_TAC [real_div, ← GSYM REAL_MUL_ASSOC] THEN
        CONV_TAC (ONCE_DEPTH_CONV HABS_CONV) THEN REWRITE_TAC [] THEN
        MATCH_MP_TAC SER_CMUL THEN
        GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [← GSYM real_div] THEN
        SUBGOAL_THEN (← q r"!n. abs(z pow n) / abs(x pow n) =
                            (abs(z) / abs(x)) pow n")
        (fun th => ONCE_REWRITE_TAC [th]) THENL
         [ALL_TAC, REWRITE_TAC [← GSYM real_div] THEN
          MATCH_MP_TAC GP THEN REWRITE_TAC [real_div, ABS_MUL] THEN
          SUBGOAL_THEN (← q r"~(abs(x) = &0)") (SUBST1_TAC o MATCH_MP ABS_INV) THENL
           [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"abs(z) < &0") THEN
            REWRITE_TAC [REAL_NOT_LT, ABS_POS],
            REWRITE_TAC [ABS_ABS, ← GSYM real_div] THEN
            MATCH_MP_TAC REAL_LT_1 THEN ASM_REWRITE_TAC [ABS_POS]]] THEN
        REWRITE_TAC [← GSYM POW_ABS] THEN X_GEN_TAC (← q "n:num") THEN
        REWRITE_TAC [real_div, POW_MUL] THEN AP_TERM_TAC THEN
        MATCH_MP_TAC POW_INV THEN CONV_TAC (RAND_CONV SYM_CONV) THEN
        MATCH_MP_TAC REAL_LT_IMP_NE THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q "abs(z)") THEN
        ASM_REWRITE_TAC [ABS_POS]]))

  -- Weaker but more commonly useful form for non-absolute convergence

  let POWSER_INSIDE ← prove
   r"!f x z. summable (\n. f(n) * (x pow n)) /\ abs(z) < abs(x)
        ==> summable (\n. f(n) * (z pow n))"
   (REPEAT GEN_TAC THEN
    SUBST1_TAC (← SYM (← SPEC (← q "z:real") ABS_ABS)) THEN
    DISCH_THEN (MP_TAC o MATCH_MP POWSER_INSIDEA) THEN
    REWRITE_TAC [POW_ABS, ← GSYM ABS_MUL] THEN
    DISCH_THEN (fun th => MATCH_MP_TAC SER_ACONV THEN MP_TAC th) THEN
    BETA_TAC THEN DISCH_THEN ACCEPT_TAC)

  -- Define formal differentiation of power series

  let diffs ← new_definition
   r"diffs c = (\n. &(SUC n) * c(SUC n))"

  -- Lemma about distributing negation over it

  let DIFFS_NEG ← prove
   r"!c. diffs(\n. --(c n)) = \n. --((diffs c) n)"
   (GEN_TAC THEN REWRITE_TAC [diffs] THEN BETA_TAC THEN
    REWRITE_TAC [REAL_NEG_RMUL])

  -- Show that we can shift the terms down one

  let DIFFS_LEMMA ← prove
   r"!n c x. sum(0,n) (\n. (diffs c)(n) * (x pow n)) =
           sum(0,n) (\n. &n * c(n) * (x pow (n - 1))) +
             (&n * c(n) * x pow (n - 1))"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [sum, REAL_MUL_LZERO, REAL_ADD_LID] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM REAL_ADD_ASSOC] THEN
    AP_TERM_TAC THEN BETA_TAC THEN REWRITE_TAC [ADD_CLAUSES] THEN
    AP_TERM_TAC THEN REWRITE_TAC [diffs] THEN BETA_TAC THEN
    REWRITE_TAC [SUC_SUB1, REAL_MUL_ASSOC])

  let DIFFS_LEMMA2 ← prove
   r"!n c x. sum(0,n) (\n. &n * c(n) * (x pow (n - 1))) =
           sum(0,n) (\n. (diffs c)(n) * (x pow n)) -
                (&n * c(n) * x pow (n - 1))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [REAL_EQ_SUB_LADD, DIFFS_LEMMA])

  let DIFFS_EQUIV ← prove
   r"!c x. summable(\n. (diffs c)(n) * (x pow n)) ==>
      (\n. &n * c(n) * (x pow (n - 1))) sums
         (suminf(\n. (diffs c)(n) * (x pow n)))"
   (← do
    let sm ← MATCH_MP SUMMABLE_SUM
      (← ASSUME (← q r"summable(\n. (diffs c)(n) * (x pow n))"))
    pure (REPEAT GEN_TAC THEN DISCH_TAC THEN
      FIRST_ASSUM (MP_TAC o REWRITE_RULE [diffs] o MATCH_MP SER_ZERO) THEN
      BETA_TAC THEN REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"(\n. &n * c(n) * (x pow (n - 1))) tends_num_real &0")
      MP_TAC THENL
       [ONCE_REWRITE_TAC [SEQ_SUC] THEN BETA_TAC THEN
        ASM_REWRITE_TAC [SUC_SUB1], ALL_TAC] THEN
      DISCH_THEN (MP_TAC o CONJ sm) THEN
      REWRITE_TAC [sums] THEN DISCH_THEN (MP_TAC o MATCH_MP SEQ_SUB) THEN
      BETA_TAC THEN REWRITE_TAC [← GSYM DIFFS_LEMMA2] THEN
      REWRITE_TAC [REAL_SUB_RZERO]))

  -- @@RETURN BEGIN
  return { POWDIFF_LEMMA, POWDIFF, POWREV, POWSER_INSIDEA, POWSER_INSIDE, diffs,
           DIFFS_NEG, DIFFS_LEMMA, DIFFS_LEMMA2, DIFFS_EQUIV }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Show term-by-term differentiability of power series.                      -/
/- (NB we hypothesize convergence of first two derivatives; we could prove   -/
/-  they all have the same radius of convergence, but we don't need to.)     -/
/- (transc.ml 184-560)                                                       -/
/- ------------------------------------------------------------------------- -/

structure TermDiff where
  -- @@FIELDS
  TERMDIFF_LEMMA1 : thm
  TERMDIFF_LEMMA2 : thm
  TERMDIFF_LEMMA3 : thm
  TERMDIFF_LEMMA4 : thm
  TERMDIFF_LEMMA5 : thm
  TERMDIFF : thm
  deriving Inhabited

@[nospecialize]
def setupTermDiff [HolBase] (D : TranscDeps) (BPowSer : PowSer) (ACompat : HolLibrary.Analysis.Compat) (ANames : HolLibrary.Analysis.Names) (AReals1 : HolLibrary.Analysis.Reals1) (AReals2 : HolLibrary.Analysis.Reals2) (AReals3 : HolLibrary.Analysis.Reals3) (AAbs : HolLibrary.Analysis.Abs) (APow : HolLibrary.Analysis.Pow) (ASums : HolLibrary.Analysis.Sums) (ASeries1 : HolLibrary.Analysis.Series1) (ASeries2 : HolLibrary.Analysis.Series2) (ALims : HolLibrary.Analysis.Lims) :
    ExceptT String IO TermDiff := do
  -- @@SCOPE BEGIN
  let { num_CONV, .. } := D
  let { ADD1, ADD_CLAUSES, ADD_SUB, ADD_SYM, CONJ_SYM, EQ_IMP, LE_ADD, LE_SUC,
        LE_TRANS, LT_0, LT_IMP_LE, REAL_ADD2_SUB2, REAL_ADD_RID, num_CASES, real_abs, .. } := D.core1
  let { REAL_ADD_SUB, REAL_ADD_SYM, REAL_DIV_LMUL, REAL_DOWN2, REAL_LET_TRANS,
        REAL_LE_ANTISYM, REAL_LT_MUL, REAL_LT_TRANS, REAL_MUL_AC, REAL_MUL_ASSOC,
        REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_SYM, RIGHT_IMP_FORALL_THM, SUB_0,
        SUB_ADD, SUB_REFL, SUB_SUC, SUC_INJ, real_div, .. } := D.core2
  let { DIFFS_EQUIV, POWDIFF, POWREV, POWSER_INSIDE, POWSER_INSIDEA, diffs, .. } := BPowSer
  let { X_FUN_EQ_CONV, .. } := ACompat
  let { LESS_ADD_1, LESS_SUC_REFL, SUC_SUB1, .. } := ANames
  let { REAL_LE_LT, REAL_LE_REFL, REAL_LE_TRANS, REAL_LTE_TRANS, REAL_LT_IMP_LE,
        REAL_MUL_LZERO, REAL_MUL_RID, REAL_MUL_RINV, REAL_MUL_RZERO, REAL_RDISTRIB, .. } := AReals1
  let { REAL, REAL_EQ_LMUL, REAL_INV_POS, REAL_LE, REAL_LT, REAL_LT_HALF1,
        REAL_LT_HALF2, REAL_LT_IMP_NE, REAL_LT_LMUL_EQ, REAL_LT_RDIV, REAL_SUB_0,
        REAL_SUB_LDISTRIB, REAL_SUB_LT, REAL_SUB_RDISTRIB, REAL_SUB_REFL, .. } := AReals2
  let { REAL_EQ_LMUL2, REAL_LE_LMUL_IMP, REAL_LE_LMUL_LOCAL, REAL_LE_MUL2V,
        REAL_LE_RMUL_EQ, REAL_LT_SUB_LADD, REAL_MEAN, REAL_SUB_RZERO, .. } := AReals3
  let { ABS_0, ABS_ABS, ABS_CIRCLE, ABS_LE, ABS_MUL, ABS_N, ABS_NZ, ABS_POS, ABS_REFL,
        ABS_TRIANGLE, ABS_ZERO, .. } := AAbs
  let { POW_1, POW_ABS, POW_ADD, POW_LE, POW_POS, pow, .. } := APow
  let { ABS_SUM, SUM_BOUND, SUM_CMUL, SUM_NSUB, SUM_SUBST, sum, .. } := ASums
  let { SUMMABLE_SUM, SUM_SUMMABLE, SUM_UNIQ, .. } := ASeries1
  let { SER_ABS, SER_CDIV, SER_CMUL, SER_COMPAR, SER_LE, SER_SUB, .. } := ASeries2
  let { LIM, LIM_NULL, LIM_TRANSFORM, diffl, .. } := ALims
  -- @@SCOPE END
  let numc (s : String) : ExceptT String IO thm := do ExceptT.mk (num_CONV (← q s))

  let TERMDIFF_LEMMA1 ← prove
   r"!m z h.
     sum(0,m)(\p. (((z + h) pow (m - p)) * (z pow p)) - (z pow m)) =
       sum(0,m)(\p. (z pow p) *
       (((z + h) pow (m - p)) - (z pow (m - p))))"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_SUBST THEN
    X_GEN_TAC (← q "p:num") THEN DISCH_TAC THEN BETA_TAC THEN
    REWRITE_TAC [REAL_SUB_LDISTRIB, ← GSYM POW_ADD] THEN BINOP_TAC THENL
     [MATCH_ACCEPT_TAC REAL_MUL_SYM,
      AP_TERM_TAC THEN ONCE_REWRITE_TAC [ADD_SYM] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUB_ADD THEN
      MATCH_MP_TAC LT_IMP_LE THEN
      POP_ASSUM (MP_TAC o CONJUNCT2) THEN REWRITE_TAC [ADD_CLAUSES]])

  let TERMDIFF_LEMMA2 ← prove
   r"!z h. ~(h = &0) ==>
       (((((z + h) pow n) - (z pow n)) / h) - (&n * (z pow (n - 1))) =
        h * sum(0,n - 1)(\p. (z pow p) *
              sum(0,(n - 1) - p)
                (\q. ((z + h) pow q) *
                       (z pow (((n - 2) - p) - q)))))"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (GEN_REWRITE_TAC id [← MATCH_MP REAL_EQ_LMUL2 th])) THEN
    REWRITE_TAC [REAL_SUB_LDISTRIB] THEN
    FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP REAL_DIV_LMUL th])) THEN
    DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN (← q "m:num") SUBST1_TAC)
    (← SPEC (← q "n:num") num_CASES) THENL
     [REWRITE_TAC [pow, REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_SUB_REFL] THEN
      REWRITE_TAC [SUB_0, sum, REAL_MUL_RZERO], ALL_TAC] THEN
    REWRITE_TAC [POWDIFF, REAL_ADD_SUB] THEN
    ASM_REWRITE_TAC [← GSYM REAL_SUB_LDISTRIB, REAL_EQ_LMUL] THEN
    REWRITE_TAC [SUC_SUB1] THEN
    GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [POWREV] THEN
    REWRITE_TAC [sum] THEN REWRITE_TAC [ADD_CLAUSES] THEN BETA_TAC THEN
    REWRITE_TAC [SUB_REFL] THEN REWRITE_TAC [REAL, pow] THEN
    REWRITE_TAC [REAL_MUL_LID, REAL_MUL_RID, REAL_RDISTRIB] THEN
    REWRITE_TAC [REAL_ADD2_SUB2, REAL_SUB_REFL, REAL_ADD_RID] THEN
    REWRITE_TAC [SUM_NSUB] THEN BETA_TAC THEN
    REWRITE_TAC [TERMDIFF_LEMMA1] THEN
    ONCE_REWRITE_TAC [← GSYM SUM_CMUL] THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_SUBST THEN X_GEN_TAC (← q "p:num") THEN
    REWRITE_TAC [ADD_CLAUSES] THEN DISCH_TAC THEN BETA_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
    FIRST_ASSUM (MP_TAC o CONJUNCT2) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "d:num") SUBST_ALL_TAC o MATCH_MP LESS_ADD_1) THEN
    REWRITE_TAC [← GSYM ADD1] THEN ONCE_REWRITE_TAC [ADD_SYM] THEN
    REWRITE_TAC [ADD_SUB] THEN REWRITE_TAC [POWDIFF, REAL_ADD_SUB] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC SUM_SUBST THEN X_GEN_TAC (← q "q:num") THEN
    REWRITE_TAC [ADD_CLAUSES] THEN STRIP_TAC THEN BETA_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC (TOP_DEPTH_CONV num_CONV) THEN
    REWRITE_TAC [SUB_SUC, SUB_0, ADD_SUB])

  let TERMDIFF_LEMMA3 ← prove
   r"!z h n K. ~(h = &0) /\ abs(z) <= K /\ abs(z + h) <= K ==>
    abs(((((z + h) pow n) - (z pow n)) / h) - (&n * (z pow (n - 1))))
        <= &n * &(n - 1) * (K pow (n - 2)) * abs(h)"
   (← do
    -- `W((then_) (MATCH_MP_TAC REAL_LE_TRANS) o EXISTS_TAC o rand o concl o
    --   PART_MATCH (rand o rator) ABS_SUM o rand o rator o snd)`
    let tac : tactic := (fun gl => ExceptT.run do
      let t ← liftExcept (do rand (← rator gl.2))
      let th ← PART_MATCH (fun t => do rand (← rator t)) ABS_SUM t
      let r ← liftExcept (rand (concl th))
      ExceptT.mk ((MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC r) gl)) THEN
      REWRITE_TAC [ABS_SUM]
    pure (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC) THEN
      FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP TERMDIFF_LEMMA2 th])) THEN
      REWRITE_TAC [ABS_MUL] THEN REWRITE_TAC [REAL_MUL_ASSOC] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN
      FIRST_ASSUM (ASSUME_TAC o CONV_RULE (REWR_CONV ABS_NZ)) THEN
      FIRST_ASSUM (fun th => tactic_of do
        pure (GEN_REWRITE_TAC id [← MATCH_MP REAL_LE_LMUL_LOCAL th])) THEN
      tac THEN REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC SUM_BOUND THEN X_GEN_TAC (← q "p:num") THEN
      REWRITE_TAC [ADD_CLAUSES] THEN DISCH_THEN STRIP_ASSUME_TAC THEN
      BETA_TAC THEN REWRITE_TAC [ABS_MUL] THEN
      DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN (← q "r:num") SUBST_ALL_TAC)
      (← SPEC (← q "n:num") num_CASES) THENL
       [REWRITE_TAC [SUB_0, sum, ABS_0, REAL_MUL_RZERO, REAL_LE_REFL],
        ALL_TAC] THEN
      REWRITE_TAC [SUC_SUB1, ← numc "2", SUB_SUC] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [SUC_SUB1]) THEN
      SUBGOAL_THEN (← q "p < r:num") MP_TAC THENL
       [FIRST_ASSUM MATCH_ACCEPT_TAC, ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "d:num") SUBST_ALL_TAC o MATCH_MP LESS_ADD_1) THEN
      REWRITE_TAC [← GSYM ADD1] THEN ONCE_REWRITE_TAC [ADD_SYM] THEN
      REWRITE_TAC [ADD_SUB] THEN REWRITE_TAC [ADD_CLAUSES, SUC_SUB1, ADD_SUB] THEN
      REWRITE_TAC [POW_ADD] THEN GEN_REWRITE_TAC RAND_CONV
       [← AC REAL_MUL_AC
            (← q r"(a * b) * c = b * (c * a)")] THEN
      MATCH_MP_TAC REAL_LE_MUL2V THEN REWRITE_TAC [ABS_POS] THEN CONJ_TAC THENL
       [REWRITE_TAC [← GSYM POW_ABS] THEN MATCH_MP_TAC POW_LE THEN
        ASM_REWRITE_TAC [ABS_POS], ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"&(SUC d) * (K pow d)") THEN
      CONJ_TAC THENL
       [ALL_TAC, SUBGOAL_THEN (← q r"&0 <= K") MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "abs z") THEN
          ASM_REWRITE_TAC [ABS_POS],
          DISCH_THEN (MP_TAC o SPEC (← q "d:num") o MATCH_MP POW_POS) THEN
          DISCH_THEN (DISJ_CASES_THEN MP_TAC o REWRITE_RULE [REAL_LE_LT]) THENL
           [DISCH_THEN (fun th => tactic_of do
              pure (REWRITE_TAC [← MATCH_MP REAL_LE_RMUL_EQ th])) THEN
            REWRITE_TAC [REAL_LE, LE_SUC] THEN
            MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q "SUC d") THEN
            REWRITE_TAC [LE_SUC, LE_ADD] THEN
            MATCH_MP_TAC LT_IMP_LE THEN REWRITE_TAC [LESS_SUC_REFL],
            DISCH_THEN (SUBST1_TAC o SYM) THEN
            REWRITE_TAC [REAL_MUL_RZERO, REAL_LE_REFL]]]] THEN
      tac THEN MATCH_MP_TAC SUM_BOUND THEN X_GEN_TAC (← q "q:num") THEN
      REWRITE_TAC [ADD_CLAUSES] THEN STRIP_TAC THEN BETA_TAC THEN
      UNDISCH_TAC (← q "q < (SUC d)") THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "e:num") MP_TAC o MATCH_MP LESS_ADD_1) THEN
      REWRITE_TAC [← GSYM ADD1, ADD_CLAUSES, SUC_INJ] THEN
      DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC [POW_ADD] THEN
      ONCE_REWRITE_TAC [ADD_SYM] THEN REWRITE_TAC [ADD_SUB] THEN
      REWRITE_TAC [ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2V THEN
      REWRITE_TAC [ABS_POS, ← GSYM POW_ABS] THEN
      CONJ_TAC THEN MATCH_MP_TAC POW_LE THEN ASM_REWRITE_TAC [ABS_POS]))

  let TERMDIFF_LEMMA4 ← prove
   r"!f K k. &0 < k /\
           (!h. &0 < abs(h) /\ abs(h) < k ==> abs(f h) <= K * abs(h))
        ==> (f tends_real_real &0)(&0)"
   (← do
    let ak ← ASSUME (← q r"&0 < k")
    let ak2 ← ASSUME (← q r"&0 < k / &2")
    let aK ← ASSUME (← q r"&0 < K")
    let aKnz ← ASSUME (← q r"~(K = &0)")
    let fx ← SPEC (← q r"(f:real->real) x") ABS_POS
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
      REWRITE_TAC [LIM, REAL_SUB_RZERO] THEN
      SUBGOAL_THEN (← q r"&0 <= K") MP_TAC THENL
       [FIRST_ASSUM (MP_TAC o SPEC (← q r"k / &2")) THEN
        MP_TAC (← ONCE_REWRITE_RULE [← GSYM REAL_LT_HALF1] ak) THEN
        DISCH_THEN (fun th => ASSUME_TAC th THEN MP_TAC th) THEN
        DISCH_THEN (MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
        DISCH_THEN (fun th => REWRITE_TAC [th, real_abs]) THEN
        REWRITE_TAC [← GSYM real_abs] THEN
        ASM_REWRITE_TAC [REAL_LT_HALF1, REAL_LT_HALF2] THEN DISCH_TAC THEN
        MP_TAC (← GEN_ALL (← MATCH_MP REAL_LE_RMUL_EQ ak2)) THEN
        DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC id [← GSYM th])) THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"abs(f(k / &2))") THEN
        ASM_REWRITE_TAC [REAL_MUL_LZERO, ABS_POS], ALL_TAC] THEN
      DISCH_THEN (DISJ_CASES_TAC o REWRITE_RULE [REAL_LE_LT]) THEN
      X_GEN_TAC (← q "e:real") THEN DISCH_TAC THENL
       [ALL_TAC, EXISTS_TAC (← q "k:real") THEN REWRITE_TAC [ak] THEN
        GEN_TAC THEN DISCH_THEN (fun th => FIRST_ASSUM (MP_TAC o (fun a => MATCH_MP a th))) THEN
        FIRST_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC [REAL_MUL_LZERO] THEN
        DISCH_THEN (MP_TAC o (fun th => CONJ th fx)) THEN
        REWRITE_TAC [REAL_LE_ANTISYM] THEN DISCH_THEN SUBST1_TAC THEN
        FIRST_ASSUM ACCEPT_TAC] THEN
      SUBGOAL_THEN (← q r"&0 < (e / K) / &2") ASSUME_TAC THENL
       [REWRITE_TAC [real_div] THEN
        REPEAT (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
        TRY (MATCH_MP_TAC REAL_INV_POS) THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [REAL_LT, ← numc "2", LT_0], ALL_TAC] THEN
      MP_TAC (← SPECL [← q r"(e / K) / &2", ← q "k:real"] REAL_DOWN2) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "d:real") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q "d:real") THEN ASM_REWRITE_TAC [] THEN
      X_GEN_TAC (← q "h:real") THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q "K * abs(h)") THEN CONJ_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (← q "d:real") THEN
        ASM_REWRITE_TAC [],
        MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (← q "K * d") THEN
        ASM_REWRITE_TAC [← MATCH_MP REAL_LT_LMUL_EQ aK] THEN
        ONCE_REWRITE_TAC [← GSYM (← MATCH_MP REAL_LT_RDIV aK)] THEN
        REWRITE_TAC [real_div] THEN
        ONCE_REWRITE_TAC [← AC REAL_MUL_AC
          (← q r"(a * b) * c = (c * a) * b")] THEN
        ASSUME_TAC (← GSYM (← MATCH_MP REAL_LT_IMP_NE aK)) THEN
        REWRITE_TAC [← MATCH_MP REAL_MUL_LINV aKnz] THEN
        REWRITE_TAC [REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (← q r"(e / K) / &2") THEN
        ASM_REWRITE_TAC [← GSYM real_div] THEN REWRITE_TAC [REAL_LT_HALF2] THEN
        ONCE_REWRITE_TAC [← GSYM REAL_LT_HALF1] THEN ASM_REWRITE_TAC []]))

  let TERMDIFF_LEMMA5 ← prove
   r"!f g k. &0 < k /\
         summable(f) /\
         (!h. &0 < abs(h) /\ abs(h) < k ==> !n. abs(g(h) n) <= (f(n) * abs(h)))
             ==> ((\h. suminf(g h)) tends_real_real &0)(&0)"
   (← do
    let hR ← q "h:real"
    let cm ← GEN hR (← SPEC (← q "abs(h)")
      (← MATCH_MP SER_CMUL (← ASSUME (← q "f sums (suminf f)"))))
    pure (REPEAT GEN_TAC THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN (CONJUNCTS_THEN2 (ASSUME_TAC o MATCH_MP SUMMABLE_SUM) MP_TAC) THEN
      ASSUME_TAC cm THEN
      RULE_ASSUM_TAC (ONCE_REWRITE_RULE [REAL_MUL_SYM]) THEN
      FIRST_ASSUM (ASSUME_TAC o GEN hR o MATCH_MP SUM_UNIQ o SPEC hR) THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"!h. &0 < abs(h) /\ abs(h) < k ==>
        abs(suminf(g h)) <= (suminf(f) * abs(h))") ASSUME_TAC THENL
       [GEN_TAC THEN DISCH_THEN (fun th => ASSUME_TAC th THEN
          FIRST_ASSUM (MP_TAC o (fun a => MATCH_MP a th))) THEN DISCH_TAC THEN
        SUBGOAL_THEN (← q r"summable(\n. f(n) * abs(h))") ASSUME_TAC THENL
         [MATCH_MP_TAC SUM_SUMMABLE THEN
          EXISTS_TAC (← q r"suminf(f) * abs(h)") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
        SUBGOAL_THEN (← q r"summable(\n. abs(g(h:real)(n:num)))") ASSUME_TAC THENL
         [MATCH_MP_TAC SER_COMPAR THEN
          EXISTS_TAC (← q r"\n:num. f(n) * abs(h)") THEN ASM_REWRITE_TAC [] THEN
          EXISTS_TAC (← q "0") THEN X_GEN_TAC (← q "n:num") THEN
          DISCH_THEN (fun _ => ALL_TAC) THEN BETA_TAC THEN REWRITE_TAC [ABS_ABS] THEN
          FIRST_ASSUM (MATCH_MP_TAC o REWRITE_RULE [RIGHT_IMP_FORALL_THM]) THEN
          ASM_REWRITE_TAC [], ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC (← q r"suminf(\n. abs(g(h:real)(n:num)))") THEN CONJ_TAC THENL
         [MATCH_MP_TAC SER_ABS THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
        ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SER_LE THEN
        REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
        GEN_TAC THEN BETA_TAC THEN
        FIRST_ASSUM (MATCH_MP_TAC o REWRITE_RULE [RIGHT_IMP_FORALL_THM]) THEN
        ASM_REWRITE_TAC [], ALL_TAC] THEN
      MATCH_MP_TAC TERMDIFF_LEMMA4 THEN
      MAP_EVERY EXISTS_TAC [← q "suminf(f)", ← q "k:real"] THEN
      BETA_TAC THEN ASM_REWRITE_TAC []))

  let TERMDIFF ← prove
   r"!c K. summable(\n. c(n) * (K pow n)) /\
         summable(\n. (diffs c)(n) * (K pow n)) /\
         summable(\n. (diffs(diffs c))(n) * (K pow n)) /\
         abs(x) < abs(K)
        ==> ((\x. suminf (\n. c(n) * (x pow n))) diffl
             (suminf (\n. (diffs c)(n) * (x pow n))))(x)"
   (← do
    -- `W(fun (asl,w) -> SUBGOAL_THEN (mk_eq(rand(rator w),`&0`)) SUBST1_TAC)`
    let eqZero : tactic := fun gl => ExceptT.run do
      let mkEq ← ExceptT.mk (mk_eq : IO _)
      let z ← q r"&0"
      let t ← liftExcept (do mkEq ((← rand (← rator gl.2)), z))
      ExceptT.mk (SUBGOAL_THEN t SUBST1_TAC gl)
    let sumsxh ← q r"(\n. (c n) * (x pow n)) sums
             (suminf(\n. (c n) * (x pow n))) /\
         (\n. (c n) * ((x + h) pow n)) sums
             (suminf(\n. (c n) * ((x + h) pow n)))"
    let hR ← q "h:real"
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
      REWRITE_TAC [diffl] THEN BETA_TAC THEN
      MATCH_MP_TAC LIM_TRANSFORM THEN
      EXISTS_TAC (← q r"\h. suminf(\n. ((c(n) * ((x + h) pow n)) -
                               (c(n) * (x pow n))) / h)") THEN CONJ_TAC THENL
       [BETA_TAC THEN REWRITE_TAC [LIM] THEN BETA_TAC THEN
        REWRITE_TAC [REAL_SUB_RZERO] THEN X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN
        EXISTS_TAC (← q "abs(K) - abs(x)") THEN REWRITE_TAC [REAL_SUB_LT] THEN
        ASM_REWRITE_TAC [] THEN X_GEN_TAC hR THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        DISCH_THEN (ASSUME_TAC o MATCH_MP ABS_CIRCLE) THEN
        eqZero THEN
        ASM_REWRITE_TAC [] THEN REWRITE_TAC [ABS_ZERO] THEN
        REWRITE_TAC [REAL_SUB_0] THEN SUBGOAL_THEN sumsxh MP_TAC THENL
         [CONJ_TAC THEN MATCH_MP_TAC SUMMABLE_SUM THEN
          MATCH_MP_TAC POWSER_INSIDE THEN EXISTS_TAC (← q "K:real") THEN
          ASM_REWRITE_TAC [], ALL_TAC] THEN
        ONCE_REWRITE_TAC [CONJ_SYM] THEN
        DISCH_THEN (MP_TAC o MATCH_MP SER_SUB) THEN BETA_TAC THEN
        DISCH_THEN (MP_TAC o SPEC hR o MATCH_MP SER_CDIV) THEN
        BETA_TAC THEN DISCH_THEN (ACCEPT_TAC o MATCH_MP SUM_UNIQ), ALL_TAC] THEN
      ONCE_REWRITE_TAC [LIM_NULL] THEN BETA_TAC THEN
      MATCH_MP_TAC LIM_TRANSFORM THEN EXISTS_TAC
       (← q r"\h. suminf (\n. c(n) *
        (((((x + h) pow n) - (x pow n)) / h) - (&n * (x pow (n - 1)))))") THEN
      BETA_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC [LIM] THEN X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN
        EXISTS_TAC (← q "abs(K) - abs(x)") THEN REWRITE_TAC [REAL_SUB_LT] THEN
        ASM_REWRITE_TAC [] THEN X_GEN_TAC hR THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        DISCH_THEN (ASSUME_TAC o MATCH_MP ABS_CIRCLE) THEN
        eqZero THEN
        ASM_REWRITE_TAC [] THEN REWRITE_TAC [REAL_SUB_RZERO, ABS_ZERO] THEN
        BETA_TAC THEN REWRITE_TAC [REAL_SUB_0] THEN
        SUBGOAL_THEN (← q r"summable(\n. (diffs c)(n) * (x pow n))") MP_TAC THENL
         [MATCH_MP_TAC POWSER_INSIDE THEN EXISTS_TAC (← q "K:real") THEN
          ASM_REWRITE_TAC [], ALL_TAC] THEN
        DISCH_THEN (fun th => tactic_of do
          pure (ASSUME_TAC th THEN MP_TAC (← MATCH_MP DIFFS_EQUIV th))) THEN
        DISCH_THEN (fun th => tactic_of do
          pure (SUBST1_TAC (← MATCH_MP SUM_UNIQ th) THEN MP_TAC th)) THEN
        RULE_ASSUM_TAC (REWRITE_RULE [REAL_SUB_RZERO]) THEN SUBGOAL_THEN sumsxh MP_TAC THENL
         [CONJ_TAC THEN MATCH_MP_TAC SUMMABLE_SUM THEN
          MATCH_MP_TAC POWSER_INSIDE THEN EXISTS_TAC (← q "K:real") THEN
          ASM_REWRITE_TAC [], ALL_TAC] THEN
        ONCE_REWRITE_TAC [CONJ_SYM] THEN
        DISCH_THEN (MP_TAC o MATCH_MP SER_SUB) THEN BETA_TAC THEN
        DISCH_THEN (MP_TAC o SPEC hR o MATCH_MP SER_CDIV) THEN
        DISCH_THEN (MP_TAC o MATCH_MP SUMMABLE_SUM o MATCH_MP SUM_SUMMABLE) THEN
        BETA_TAC THEN DISCH_THEN (fun th => DISCH_THEN (MP_TAC o
          MATCH_MP SUMMABLE_SUM o MATCH_MP SUM_SUMMABLE) THEN MP_TAC th) THEN
        DISCH_THEN (fun th1 => DISCH_THEN (fun th2 => tactic_of do
          pure (MP_TAC (← CONJ th1 th2)))) THEN
        DISCH_THEN (MP_TAC o MATCH_MP SER_SUB) THEN BETA_TAC THEN
        DISCH_THEN (SUBST1_TAC o MATCH_MP SUM_UNIQ) THEN AP_TERM_TAC THEN
        ABS_TAC THEN REWRITE_TAC [real_div] THEN
        REWRITE_TAC [REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB] THEN
        REWRITE_TAC [REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_MUL_SYM,
        ALL_TAC] THEN
      MP_TAC (← SPECL [← q "abs(x)", ← q "abs(K)"] REAL_MEAN) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "R:real") STRIP_ASSUME_TAC) THEN
      MP_TAC (← SPECL
       [← q r"\n. abs(c n) * &n * &(n - 1) * (R pow (n - 2))",
        ← q r"\h n. c(n) * (((((x + h) pow n) - (x pow n)) / h) -
                         (&n * (x pow (n - 1))))",
        ← q "R - abs(x)"] TERMDIFF_LEMMA5) THEN
      BETA_TAC THEN REWRITE_TAC [REAL_MUL_ASSOC] THEN
      DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC [REAL_SUB_LT],

        SUBGOAL_THEN (← q r"summable(\n. abs(diffs(diffs c) n) * (R pow n))") MP_TAC THENL
         [MATCH_MP_TAC POWSER_INSIDEA THEN
          EXISTS_TAC (← q "K:real") THEN ASM_REWRITE_TAC [] THEN
          SUBGOAL_THEN (← q "abs(R) = R") (fun th => ASM_REWRITE_TAC [th]) THEN
          REWRITE_TAC [ABS_REFL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC (← q "abs(x)") THEN REWRITE_TAC [ABS_POS] THEN
          MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
        REWRITE_TAC [diffs] THEN BETA_TAC THEN REWRITE_TAC [ABS_MUL] THEN
        REWRITE_TAC [ABS_N] THEN REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN
        SUBGOAL_THEN
          (← q r"!n. diffs(diffs (\n. abs(c n))) n * (R pow n) =
               &(SUC n) * &(SUC(SUC n)) * abs(c(SUC(SUC n))) * (R pow n)")
          (fun th => tactic_of do pure (ONCE_REWRITE_TAC [← GSYM th])) THENL
         [GEN_TAC THEN REWRITE_TAC [diffs] THEN BETA_TAC THEN
          REWRITE_TAC [REAL_MUL_ASSOC], ALL_TAC] THEN
        DISCH_THEN (MP_TAC o MATCH_MP DIFFS_EQUIV) THEN
        DISCH_THEN (MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
        REWRITE_TAC [diffs] THEN BETA_TAC THEN REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN
        SUBGOAL_THEN (← q r"(\n. &n * &(SUC n) * abs(c(SUC n)) * (R pow (n - 1))) =
               \n. diffs(\m. &(m - 1) * abs(c m) / R) n * (R pow n)")
        SUBST1_TAC THENL
         [REWRITE_TAC [diffs] THEN BETA_TAC THEN REWRITE_TAC [SUC_SUB1] THEN
          ABS_TAC THEN
          DISJ_CASES_THEN2 (SUBST1_TAC) (X_CHOOSE_THEN (← q "m:num") SUBST1_TAC)
           (← SPEC (← q "n:num") num_CASES) THEN
          REWRITE_TAC [REAL_MUL_LZERO, REAL_MUL_RZERO, SUC_SUB1] THEN
          REWRITE_TAC [ADD1, POW_ADD] THEN REWRITE_TAC [← GSYM ADD1, POW_1] THEN
          REWRITE_TAC [← GSYM REAL_MUL_ASSOC, real_div] THEN
          ONCE_REWRITE_TAC [← AC REAL_MUL_AC
            (← q r"a * b * c * d * e * f = b * a * c * e * d * f")] THEN
          REPEAT AP_TERM_TAC THEN SUBGOAL_THEN (← q r"inv(R) * R = &1") SUBST1_TAC THENL
           [MATCH_MP_TAC REAL_MUL_LINV THEN REWRITE_TAC [ABS_NZ] THEN
            MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q "abs(x)") THEN
            ASM_REWRITE_TAC [ABS_POS] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
            EXISTS_TAC (← q "R:real") THEN ASM_REWRITE_TAC [ABS_LE],
            REWRITE_TAC [REAL_MUL_RID]], ALL_TAC] THEN
        DISCH_THEN (MP_TAC o MATCH_MP DIFFS_EQUIV) THEN BETA_TAC THEN
        DISCH_THEN (MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
        MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
        CONV_TAC (X_FUN_EQ_CONV (← q "n:num")) THEN BETA_TAC THEN GEN_TAC THEN
        REWRITE_TAC [real_div, ← GSYM REAL_MUL_ASSOC] THEN
        GEN_REWRITE_TAC RAND_CONV
         [← AC REAL_MUL_AC
          (← q r"a * b * c * d = b * c * a * d")] THEN
        DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN (← q "m:num") SUBST1_TAC)
         (← SPEC (← q "n:num") num_CASES) THEN REWRITE_TAC [REAL_MUL_LZERO] THEN
        REWRITE_TAC [← numc "2", SUC_SUB1, SUB_SUC] THEN AP_TERM_TAC THEN
        DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN (← q "n:num") SUBST1_TAC)
         (← SPEC (← q "m:num") num_CASES) THEN REWRITE_TAC [REAL_MUL_LZERO] THEN
        REPEAT AP_TERM_TAC THEN REWRITE_TAC [SUC_SUB1] THEN
        REWRITE_TAC [ADD1, POW_ADD, POW_1] THEN
        ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN
        SUBGOAL_THEN (← q r"R * inv(R) = &1")
        (fun th => REWRITE_TAC [th, REAL_MUL_RID]) THEN
        MATCH_MP_TAC REAL_MUL_RINV THEN CONV_TAC (RAND_CONV SYM_CONV) THEN
        MATCH_MP_TAC REAL_LT_IMP_NE THEN MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC (← q "abs(x)") THEN ASM_REWRITE_TAC [ABS_POS],

        X_GEN_TAC hR THEN DISCH_TAC THEN X_GEN_TAC (← q "n:num") THEN
        REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN ONCE_REWRITE_TAC [ABS_MUL] THEN
        MATCH_MP_TAC REAL_LE_LMUL_IMP THEN REWRITE_TAC [ABS_POS] THEN
        MATCH_MP_TAC TERMDIFF_LEMMA3 THEN ASM_REWRITE_TAC [ABS_NZ] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC [],
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "abs(x) + abs(h)") THEN
          REWRITE_TAC [ABS_TRIANGLE] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
          ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
          ASM_REWRITE_TAC [← GSYM REAL_LT_SUB_LADD]]]))

  -- @@RETURN BEGIN
  return { TERMDIFF_LEMMA1, TERMDIFF_LEMMA2, TERMDIFF_LEMMA3, TERMDIFF_LEMMA4,
           TERMDIFF_LEMMA5, TERMDIFF }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Getting rid of the pointless side-conditions; term-by-term comparison of  -/
/- power series.  (transc.ml 562-858)                                        -/
/- ------------------------------------------------------------------------- -/

structure PowSerEq where
  -- @@FIELDS
  SEQ_NPOW : thm
  TERMDIFF_CONVERGES : thm
  TERMDIFF_STRONG : thm
  POWSER_0 : thm
  POWSER_LIMIT_0 : thm
  POWSER_LIMIT_0_STRONG : thm
  POWSER_EQUAL_0 : thm
  POWSER_EQUAL : thm
  deriving Inhabited

@[nospecialize]
def setupPowSerEq [HolBase] (D : TranscDeps) (BPowSer : PowSer) (BTermDiff : TermDiff) (ATactics : HolLibrary.Analysis.Tactics) (AReals1 : HolLibrary.Analysis.Reals1) (AReals2 : HolLibrary.Analysis.Reals2) (AReals3 : HolLibrary.Analysis.Reals3) (APow : HolLibrary.Analysis.Pow) (ASums : HolLibrary.Analysis.Sums) (ASumConv : HolLibrary.Analysis.SumConv) (ASeqs : HolLibrary.Analysis.Seqs) (ASeries1 : HolLibrary.Analysis.Series1) (ASeries2 : HolLibrary.Analysis.Series2) (ALims : HolLibrary.Analysis.Lims) :
    ExceptT String IO PowSerEq := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, REAL_ARITH, REAL_ARITH_TAC, .. } := D
  let { ADD1, ADD_CLAUSES, ARITH, ARITH_EQ, EQ_IMP, EQ_TRANS, FUN_EQ_THM, GE, IMP_CONJ,
        LEFT_AND_EXISTS_THM, LE_EXISTS, LT, LT_0, MONO_EXISTS, MONO_FORALL,
        MULT_CLAUSES, NOT_FORALL_THM, REAL_ABS_ABS, REAL_ABS_DIV, REAL_ABS_MUL,
        REAL_ABS_NUM, REAL_ABS_NZ, REAL_ABS_POS, REAL_ABS_POW, REAL_ADD_LID, num_WOP, .. } := D.core1
  let { REAL_DIV_LMUL, REAL_DOWN2, REAL_ENTIRE, REAL_EQ_SUB_LADD, REAL_LET_TRANS,
        REAL_LE_LMUL, REAL_LE_RDIV_EQ, REAL_LE_RMUL, REAL_LT_DIV, REAL_LT_LDIV_EQ,
        REAL_LT_RDIV_EQ, REAL_LT_REFL, REAL_LT_TRANS, REAL_MUL_2, REAL_MUL_AC,
        REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LINV, REAL_OF_NUM_EQ, REAL_OF_NUM_LE,
        REAL_OF_NUM_LT, REAL_OF_NUM_MUL, REAL_OF_NUM_SUC, REAL_POW_1, REAL_POW_ADD,
        REAL_POW_DIV, REAL_POW_EQ_0, REAL_POW_INV, REAL_POW_LT, RIGHT_AND_EXISTS_THM,
        RIGHT_IMP_EXISTS_THM, SKOLEM_THM, real_div, real_pow, .. } := D.core2
  let { POWSER_INSIDE, POWSER_INSIDEA, diffs, .. } := BPowSer
  let { TERMDIFF, .. } := BTermDiff
  let { EXPAND_TAC, .. } := ATactics
  let { REAL_LE_MUL, REAL_LE_REFL, REAL_LTE_TRANS, REAL_LT_01, REAL_LT_IMP_LE,
        REAL_MUL_LZERO, REAL_MUL_RID, REAL_MUL_RINV, REAL_MUL_RZERO, .. } := AReals1
  let { REAL_SUB_LT, REAL_SUB_REFL, .. } := AReals2
  let { REAL_SUB_RZERO, .. } := AReals3
  let { REAL_ARCH_SIMPLE, .. } := APow
  let { SUM_CONST, SUM_EQ, SUM_OFFSET, .. } := ASums
  let { REAL_SUM_CONV, .. } := ASumConv
  let { SEQ, .. } := ASeqs
  let { SER_0, SER_OFFSET, SUM_SUMMABLE, SUM_UNIQ, summable, sums, .. } := ASeries1
  let { SER_ACONV, SER_CMUL, SER_COMPAR, SER_RATIO, SER_ZERO, .. } := ASeries2
  let { DIFF_CONT, LIM, LIM_EQUAL, LIM_TRANSFORM, contl, .. } := ALims
  -- @@SCOPE END
  -- `W(C SUBGOAL_THEN ttac o funpow 2 lhand o snd)`
  let subgoalLhand2 (ttac : thm_tactic) : tactic := fun gl => ExceptT.run do
    let t ← liftExcept (do lhand (← lhand gl.2))
    ExceptT.mk (SUBGOAL_THEN t ttac gl)

  -- I eventually decided to get rid of the pointless side-conditions.

  let SEQ_NPOW ← prove
   r"!x. abs(x) < &1 ==> (\n. &n * x pow n) tends_num_real &0"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"!n. abs(x) / (&1 - abs(x)) < &n <=> &(SUC n) * abs(x) < &n")
    ASSUME_TAC THENL
     [ASM_SIMP_TAC [REAL_LT_LDIV_EQ, REAL_SUB_LT] THEN
      REWRITE_TAC [← GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC, ALL_TAC] THEN
    MP_TAC (← SPEC (← q r"abs(x) / (&1 - abs(x))") REAL_ARCH_SIMPLE) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "N:num") STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC SER_ZERO THEN MATCH_MP_TAC SER_RATIO THEN
    EXISTS_TAC (← q r"&(SUC(SUC N)) * abs(x) / &(SUC N)") THEN
    EXISTS_TAC (← q "SUC N") THEN CONJ_TAC THENL
     [REWRITE_TAC [real_div, REAL_MUL_ASSOC] THEN REWRITE_TAC [← GSYM real_div] THEN
      SIMP_TAC [REAL_MUL_LID, REAL_LT_LDIV_EQ, REAL_OF_NUM_LT, LT_0] THEN
      FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC id [← GSYM th])) THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q r"&N") THEN
      ASM_REWRITE_TAC [REAL_OF_NUM_LT, LT], ALL_TAC] THEN
    ABBREV_TAC (← q "m = SUC N") THEN GEN_TAC THEN REWRITE_TAC [GE] THEN DISCH_TAC THEN
    REWRITE_TAC [real_div, real_pow, REAL_ABS_MUL, ← GSYM REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV [← AC REAL_MUL_AC
     (← q r"a * b * c * d * e = ((a * d) * c) * (b * e)")] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    SIMP_TAC [REAL_ABS_POS, REAL_LE_MUL] THEN
    SUBGOAL_THEN (← q r"&0 < &m") ASSUME_TAC THENL
     [REWRITE_TAC [REAL_OF_NUM_LT] THEN UNDISCH_TAC (← q "m:num <= n") THEN
      EXPAND_TAC "m" THEN ARITH_TAC, ALL_TAC] THEN
    ASM_SIMP_TAC [← GSYM real_div, REAL_LE_RDIV_EQ] THEN
    UNDISCH_TAC (← q "m:num <= n") THEN GEN_REWRITE_TAC LAND_CONV [LE_EXISTS] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "d:num") SUBST1_TAC) THEN
    REWRITE_TAC [REAL_ABS_NUM, REAL_OF_NUM_MUL, REAL_OF_NUM_LE] THEN
    REWRITE_TAC [ADD_CLAUSES, MULT_CLAUSES] THEN ARITH_TAC)

  let TERMDIFF_CONVERGES ← prove
   r"!K. (!x. abs(x) < K ==> summable(\n. c(n) * x pow n))
       ==> !x. abs(x) < K ==> summable (\n. diffs c n * x pow n)"
   (← do
    -- The later rule in the THEN chain is evaluated first.
    let t ← TAUT (← q r"(b ==> c) ==> (a ==> b) ==> (a ==> c)")
    let ar ← ARITH_RULE (← q r"1 <= m <=> ~(m = 0)")
    pure (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"x = &0") THENL
     [REWRITE_TAC [summable] THEN
      EXISTS_TAC (← q r"sum(0,1) (\n. diffs c n * x pow n)") THEN
      MATCH_MP_TAC SER_0 THEN
      ASM_REWRITE_TAC [REAL_ENTIRE, REAL_POW_EQ_0] THEN
      SIMP_TAC [ar], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"?y. abs(x) < abs(y) /\ abs(y) < K") STRIP_ASSUME_TAC THENL
     [EXISTS_TAC (← q r"(abs(x) + K) / &2") THEN
      SIMP_TAC [REAL_ABS_DIV, REAL_ABS_NUM, REAL_LT_RDIV_EQ, REAL_LT_LDIV_EQ,
               REAL_OF_NUM_LT, ARITH] THEN
      UNDISCH_TAC (← q "abs(x) < K") THEN REAL_ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [diffs] THEN
    SUBGOAL_THEN (← q r"summable (\n. (&n * c(n)) * x pow n)") MP_TAC THENL
     [ALL_TAC,
      DISCH_THEN (MP_TAC o SPEC (← q "1") o MATCH_MP SER_OFFSET) THEN
      DISCH_THEN (MP_TAC o SPEC (← q "inv(x)") o MATCH_MP SER_CMUL) THEN
      REWRITE_TAC [← GSYM ADD1, real_pow] THEN
      ONCE_REWRITE_TAC [← AC REAL_MUL_AC
       (← q r"a * (b * c) * d * e = (a * d) * (b * c) * e")] THEN
      ASM_SIMP_TAC [REAL_MUL_LINV, REAL_MUL_LID] THEN
      REWRITE_TAC [SUM_SUMMABLE]] THEN
    MATCH_MP_TAC SER_COMPAR THEN EXISTS_TAC (← q r"\n:num. abs(c n * y pow n)") THEN
    CONJ_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_POW] THEN
      MATCH_MP_TAC POWSER_INSIDEA THEN
      EXISTS_TAC (← q r"(abs(y) + K) / &2") THEN
      SUBGOAL_THEN (← q r"abs(abs y) < abs((abs y + K) / &2) /\
                    abs((abs y + K) / &2) < K")
       (fun th => ASM_SIMP_TAC [th]) THEN
      SIMP_TAC [REAL_ABS_DIV, REAL_ABS_NUM, REAL_LT_RDIV_EQ, REAL_LT_LDIV_EQ,
               REAL_OF_NUM_LT, ARITH] THEN
      UNDISCH_TAC (← q "abs y < K") THEN REAL_ARITH_TAC] THEN
    SUBGOAL_THEN (← q r"&0 < abs(y)") ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [← q "abs x < abs y", ← q r"~(x = &0)"] THEN
      REAL_ARITH_TAC, ALL_TAC] THEN
    MP_TAC (← SPEC (← q "x / y") SEQ_NPOW) THEN
    ASM_SIMP_TAC [REAL_MUL_LID, REAL_LT_LDIV_EQ, REAL_ABS_DIV] THEN
    REWRITE_TAC [SEQ] THEN DISCH_THEN (MP_TAC o SPEC (← q r"&1")) THEN
    REWRITE_TAC [REAL_OF_NUM_LT, REAL_SUB_RZERO, ARITH] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN
    GEN_TAC THEN MATCH_MP_TAC t THEN
    REWRITE_TAC [REAL_ABS_DIV, REAL_ABS_MUL, REAL_ABS_POW, REAL_ABS_NUM] THEN
    REWRITE_TAC [REAL_POW_DIV] THEN
    REWRITE_TAC [real_div, REAL_MUL_ASSOC, REAL_POW_INV] THEN
    REWRITE_TAC [← GSYM real_div] THEN
    ASM_SIMP_TAC [REAL_LT_LDIV_EQ, REAL_POW_LT] THEN
    REWRITE_TAC [REAL_MUL_LID] THEN DISCH_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [← AC REAL_MUL_AC (← q r"(a * b) * c = b * a * c")] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC [REAL_ABS_POS, REAL_LT_IMP_LE]))

  let TERMDIFF_STRONG ← prove
   r"!c K x.
        summable(\n. c(n) * (K pow n)) /\ abs(x) < abs(K)
        ==> ((\x. suminf (\n. c(n) * (x pow n))) diffl
             (suminf (\n. (diffs c)(n) * (x pow n))))(x)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC TERMDIFF THEN
    EXISTS_TAC (← q r"(abs(x) + abs(K)) / &2") THEN
    SUBGOAL_THEN (← q r"abs(x) < abs((abs(x) + abs(K)) / &2) /\
                  abs((abs(x) + abs(K)) / &2) < abs(K)")
    STRIP_ASSUME_TAC THENL
     [SIMP_TAC [REAL_ABS_DIV, REAL_ABS_NUM, REAL_LT_RDIV_EQ,
               REAL_LT_LDIV_EQ, REAL_OF_NUM_LT, ARITH] THEN
      UNDISCH_TAC (← q "abs(x) < abs(K)") THEN REAL_ARITH_TAC, ALL_TAC] THEN
    ASM_REWRITE_TAC [REAL_ABS_ABS] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SER_ACONV THEN
      REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_POW] THEN
      MATCH_MP_TAC POWSER_INSIDEA THEN
      EXISTS_TAC (← q "K:real") THEN ASM_REWRITE_TAC [REAL_ABS_ABS],
      SUBGOAL_THEN
       (← q r"!x. abs(x) < abs(K) ==> summable (\n. diffs c n * x pow n)")
       (fun th => ASM_SIMP_TAC [th]),
      SUBGOAL_THEN
       (← q r"!x. abs(x) < abs(K) ==> summable (\n. diffs(diffs c) n * x pow n)")
       (fun th => ASM_SIMP_TAC [th]) THEN
      MATCH_MP_TAC TERMDIFF_CONVERGES] THEN
    MATCH_MP_TAC TERMDIFF_CONVERGES THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SER_ACONV THEN
    REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_POW] THEN
    MATCH_MP_TAC POWSER_INSIDEA THEN
    EXISTS_TAC (← q "K:real") THEN ASM_REWRITE_TAC [REAL_ABS_ABS])

  -- Term-by-term comparison of power series.

  let POWSER_0 ← prove
   r"!a. (\n. a n * (&0) pow n) sums a(0)"
   (GEN_TAC THEN
    SUBGOAL_THEN (← q r"a(0) = sum(0,1) (\n. a n * (&0) pow n)") SUBST1_TAC THENL
     [CONV_TAC (ONCE_DEPTH_CONV REAL_SUM_CONV) THEN
      REWRITE_TAC [real_pow, REAL_MUL_RID], ALL_TAC] THEN
    MATCH_MP_TAC SER_0 THEN INDUCT_TAC THEN
    REWRITE_TAC [real_pow, REAL_MUL_LZERO, REAL_MUL_RZERO, ARITH])

  let POWSER_LIMIT_0 ← prove
   r"!f a s. &0 < s /\
           (!x. abs(x) < s ==> (\n. a n * x pow n) sums (f x))
           ==> (f tends_real_real a(0))(&0)"
   (← do
    -- The later rule in the THEN chain is evaluated first.
    let ra2 ← REAL_ARITH (← q r"(a = b) /\ &0 < e ==> abs(a - b) < e")
    let ra1 ← REAL_ARITH (← q r"&0 < x ==> &0 < abs(x)")
    pure (REPEAT STRIP_TAC THEN
      MP_TAC (← SPECL [← q r"a:num->real", ← q r"s / &2", ← q r"&0"] TERMDIFF_STRONG) THEN
      subgoalLhand2 (fun th => REWRITE_TAC [th]) THENL
       [ASM_SIMP_TAC [REAL_ABS_NUM, REAL_ABS_DIV, REAL_LT_DIV, REAL_OF_NUM_LT,
                     ARITH, ra1] THEN
        MATCH_MP_TAC SUM_SUMMABLE THEN
        EXISTS_TAC (← q r"(f:real->real) (s / &2)") THEN
        FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_SIMP_TAC [REAL_ABS_DIV, REAL_ABS_NUM, REAL_LT_LDIV_EQ, REAL_OF_NUM_LT,
                     ARITH] THEN
        UNDISCH_TAC (← q r"&0 < s") THEN REAL_ARITH_TAC, ALL_TAC] THEN
      DISCH_THEN (MP_TAC o MATCH_MP DIFF_CONT) THEN REWRITE_TAC [contl] THEN
      SUBGOAL_THEN (← q r"suminf (\n. a n * &0 pow n) = a(0)") SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_UNIQ THEN
        REWRITE_TAC [POWSER_0], ALL_TAC] THEN
      MATCH_MP_TAC (← ONCE_REWRITE_RULE [IMP_CONJ]
                   LIM_TRANSFORM) THEN
      REWRITE_TAC [REAL_ADD_LID, LIM] THEN
      REPEAT STRIP_TAC THEN EXISTS_TAC (← q "s:real") THEN
      ASM_REWRITE_TAC [REAL_SUB_RZERO] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC ra2 THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SUM_UNIQ THEN ASM_SIMP_TAC []))

  let POWSER_LIMIT_0_STRONG ← prove
   r"!f a s.
        &0 < s /\
        (!x. &0 < abs(x) /\ abs(x) < s ==> (\n. a n * x pow n) sums (f x))
        ==> (f tends_real_real a(0))(&0)"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"((\x. if x = &0 then a(0):real else f x) tends_real_real a(0))(&0)")
    MP_TAC THENL
     [MATCH_MP_TAC POWSER_LIMIT_0 THEN
      EXISTS_TAC (← q "s:real") THEN ASM_REWRITE_TAC [] THEN
      X_GEN_TAC (← q "x:real") THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"x = &0") THEN
      ASM_SIMP_TAC [← GSYM REAL_ABS_NZ] THEN REWRITE_TAC [sums, SEQ] THEN
      X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN EXISTS_TAC (← q "1") THEN
      INDUCT_TAC THEN REWRITE_TAC [ARITH, ADD1] THEN DISCH_TAC THEN
      REWRITE_TAC [← GSYM (← ONCE_REWRITE_RULE [REAL_EQ_SUB_LADD] SUM_OFFSET)] THEN
      REWRITE_TAC [REAL_POW_ADD, REAL_POW_1, REAL_MUL_RZERO, SUM_CONST] THEN
      CONV_TAC (ONCE_DEPTH_CONV REAL_SUM_CONV) THEN
      REWRITE_TAC [real_pow, REAL_MUL_RID] THEN
      ASM_REWRITE_TAC [REAL_ADD_LID, REAL_SUB_REFL, REAL_ABS_NUM], ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN
    MATCH_MP_TAC LIM_EQUAL THEN SIMP_TAC [])

  let POWSER_EQUAL_0 ← prove
   r"!f a b P.
        (!e. &0 < e ==> ?x. P x /\ &0 < abs x /\ abs(x) < e) /\
        (!x. &0 < abs(x) /\ P x
             ==> (\n. a n * x pow n) sums (f x) /\
                 (\n. b n * x pow n) sums (f x))
        ==> (a(0) = b(0))"
   (← do
    -- The later rule in the THEN chain is evaluated first.
    let ra2 ← REAL_ARITH
     (← q r"!f g h. abs(g - a) < e2 /\ abs(h - b) < e2 /\ (g = f) /\ (h = f)
              ==> abs(a - b) < e2 + e2")
    let ra1 ← REAL_ARITH (← q r"~(&0 < abs(x - y)) ==> (x = y)")
    let sumUniq ← GSYM SUM_UNIQ
    pure (REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
       (← q r"?s. &0 < s /\
            !x. abs(x) < s
                ==> summable (\n. a n * x pow n) /\ summable (\n. b n * x pow n)")
      MP_TAC THENL
       [FIRST_ASSUM (MP_TAC o (fun th => MATCH_MP th REAL_LT_01)) THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "k:real") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q "abs(k)") THEN ASM_REWRITE_TAC [] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC POWSER_INSIDE THEN
        EXISTS_TAC (← q "k:real") THEN
        ASM_REWRITE_TAC [summable] THEN
        EXISTS_TAC (← q r"(f:real->real) k") THEN ASM_SIMP_TAC [], ALL_TAC] THEN
      REWRITE_TAC [summable, LEFT_AND_EXISTS_THM] THEN
      REWRITE_TAC [RIGHT_AND_EXISTS_THM, RIGHT_IMP_EXISTS_THM] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "s:real") MP_TAC) THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      REWRITE_TAC [SKOLEM_THM] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"g:real->real") MP_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"h:real->real") MP_TAC) THEN DISCH_TAC THEN
      MATCH_MP_TAC ra1 THEN
      ABBREV_TAC (← q "e = abs(a 0 - b 0)") THEN DISCH_TAC THEN
      MP_TAC (← SPECL [← q r"g:real->real", ← q r"a:num->real", ← q "s:real"]
        POWSER_LIMIT_0_STRONG) THEN
      ASM_SIMP_TAC [LIM] THEN DISCH_THEN (MP_TAC o SPEC (← q r"e / &2")) THEN
      ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH, REAL_SUB_RZERO] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "d1:real") STRIP_ASSUME_TAC) THEN
      MP_TAC (← SPECL [← q r"h:real->real", ← q r"b:num->real", ← q "s:real"]
        POWSER_LIMIT_0_STRONG) THEN
      ASM_SIMP_TAC [LIM] THEN DISCH_THEN (MP_TAC o SPEC (← q r"e / &2")) THEN
      ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH, REAL_SUB_RZERO] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "d2:real") STRIP_ASSUME_TAC) THEN
      MP_TAC (← SPECL [← q "d1:real", ← q "d2:real"] REAL_DOWN2) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "d0:real") STRIP_ASSUME_TAC) THEN
      MP_TAC (← SPECL [← q "d0:real", ← q "s:real"] REAL_DOWN2) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "d:real") STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC (← q r"!e. &0 < e ==> ?x. P x /\ &0 < abs x /\ abs x < e") THEN
      DISCH_THEN (MP_TAC o SPEC (← q "d:real")) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "x:real") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN (← q "abs(a 0 - b 0) < e") MP_TAC THENL
       [ALL_TAC, ASM_REWRITE_TAC [REAL_LT_REFL]] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC (← q r"e / &2 + e / &2") THEN CONJ_TAC THENL
       [ALL_TAC,
        SIMP_TAC [← GSYM REAL_MUL_2, REAL_DIV_LMUL, REAL_OF_NUM_EQ, ARITH_EQ] THEN
        REWRITE_TAC [REAL_LE_REFL]] THEN
      MATCH_MP_TAC ra2 THEN
      MAP_EVERY EXISTS_TAC
       [← q r"(f:real->real) x", ← q r"(g:real->real) x", ← q r"(h:real->real) x"] THEN
      CONJ_TAC THENL [ASM_MESON_TAC [REAL_LT_TRANS], ALL_TAC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC [REAL_LT_TRANS], ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (← q r"suminf(\n. a n * x pow n)") THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC SUM_UNIQ,
          MATCH_MP_TAC sumUniq] THEN
        ASM_SIMP_TAC [] THEN
        SUBGOAL_THEN (← q "abs(x) < s") (fun th => ASM_SIMP_TAC [th]) THEN
        ASM_MESON_TAC [REAL_LT_TRANS],
        MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (← q r"suminf(\n. b n * x pow n)") THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC SUM_UNIQ,
          MATCH_MP_TAC sumUniq] THEN
        ASM_SIMP_TAC [] THEN
        SUBGOAL_THEN (← q "abs(x) < s") (fun th => ASM_SIMP_TAC [th]) THEN
        ASM_MESON_TAC [REAL_LT_TRANS]]))

  let POWSER_EQUAL ← prove
   r"!f a b P.
        (!e. &0 < e ==> ?x. P x /\ &0 < abs x /\ abs(x) < e) /\
        (!x. P x ==> (\n. a n * x pow n) sums (f x) /\
                     (\n. b n * x pow n) sums (f x))
        ==> (a = b)"
   (← do
    -- The later rules in the THEN chain are evaluated first.
    let ra ← REAL_ARITH (← q r"(x = &0) <=> ~(&0 < abs x)")
    let t2 ← TAUT (← q r"~(~a /\ b) <=> b ==> a")
    let t1 ← TAUT (← q r"p <=> ~ ~ p")
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN
      GEN_REWRITE_TAC id [t1] THEN
      GEN_REWRITE_TAC RAND_CONV [NOT_FORALL_THM] THEN
      ONCE_REWRITE_TAC [num_WOP] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "n:num") MP_TAC) THEN REWRITE_TAC [] THEN
      REWRITE_TAC [t2] THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"(\m. a(m + n):real) 0 = (\m. b(m + n)) 0") MP_TAC THENL
       [ALL_TAC, REWRITE_TAC [ADD_CLAUSES]] THEN
      MATCH_MP_TAC POWSER_EQUAL_0 THEN
      EXISTS_TAC (← q r"\x. inv(x pow n) * (f(x) - sum(0,n) (\n. b n * x pow n))") THEN
      EXISTS_TAC (← q r"P:real->bool") THEN ASM_REWRITE_TAC [] THEN
      X_GEN_TAC (← q "x:real") THEN STRIP_TAC THEN
      SUBGOAL_THEN (← q r"!a m. a(m + n) * x pow m =
                          inv(x pow n) * a(m + n) * x pow (m + n)")
       (fun th => GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV o ONCE_DEPTH_CONV) [th])
      THENL
       [REPEAT GEN_TAC THEN REWRITE_TAC [REAL_POW_ADD] THEN
        ONCE_REWRITE_TAC [← AC REAL_MUL_AC (← q r"x' * a * b * x = (x * x') * a * b")] THEN
        ASM_SIMP_TAC [REAL_MUL_RINV, REAL_POW_EQ_0, ra] THEN
        REWRITE_TAC [REAL_MUL_LID], ALL_TAC] THEN
      CONJ_TAC THEN MATCH_MP_TAC SER_CMUL THENL
       [SUBGOAL_THEN (← q r"sum(0,n) (\n. b n * x pow n) = sum(0,n) (\n. a n * x pow n)")
        SUBST1_TAC THENL
         [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC [ADD_CLAUSES], ALL_TAC] THEN
        SUBGOAL_THEN (← q r"f x = suminf (\n. a n * x pow n)") SUBST1_TAC THENL
         [MATCH_MP_TAC SUM_UNIQ THEN ASM_SIMP_TAC [], ALL_TAC] THEN
        MP_TAC (← SPEC (← q r"\n. a n * x pow n") SER_OFFSET),
        SUBGOAL_THEN (← q r"f x = suminf (\n. b n * x pow n)") SUBST1_TAC THENL
         [MATCH_MP_TAC SUM_UNIQ THEN ASM_SIMP_TAC [], ALL_TAC] THEN
        MP_TAC (← SPEC (← q r"\n. b n * x pow n") SER_OFFSET)] THEN
      REWRITE_TAC [] THEN
      subgoalLhand2 (fun th => SIMP_TAC [th]) THEN
      MATCH_MP_TAC SUM_SUMMABLE THEN
      EXISTS_TAC (← q r"(f:real->real) x") THEN ASM_SIMP_TAC []))

  -- @@RETURN BEGIN
  return { SEQ_NPOW, TERMDIFF_CONVERGES, TERMDIFF_STRONG, POWSER_0, POWSER_LIMIT_0,
           POWSER_LIMIT_0_STRONG, POWSER_EQUAL_0, POWSER_EQUAL }
  -- @@RETURN END

/-- The element type of `diff_net`: `PART_MATCH (lhand o rator o rand) th`. -/
abbrev DiffRule := term → ExceptT String IO thm

/-- transc.ml's `diff_net : net ref`, as a read/write handle on an `IO.Ref`
    (`get` is `!diff_net`, `set` is `diff_net := ...`). -/
structure NetRef where
  get : IO (HolCore.Nets.net DiffRule)
  set : HolCore.Nets.net DiffRule → IO Unit

instance : Inhabited NetRef := ⟨⟨pure HolCore.Nets.empty_net, fun _ => pure ()⟩⟩

/- ------------------------------------------------------------------------- -/
/- Definitions of the transcendental functions etc.: miscellaneous lemmas;   -/
/- `diff_net`; exp, sin and cos as series, their convergence and their       -/
/- derivatives.  (transc.ml 860-1162)                                        -/
/- ------------------------------------------------------------------------- -/

structure Defs where
  -- @@FIELDS
  MULT_DIV_2 : thm
  EVEN_DIV2 : thm
  POW_ZERO : thm
  POW_ZERO_EQ : thm
  POW_LT : thm
  POW_EQ : thm
  diff_net : NetRef
  add_to_diff_net : thm → ExceptT String IO Unit
  exp : thm
  sin : thm
  cos : thm
  REAL_EXP_CONVERGES : thm
  SIN_CONVERGES : thm
  COS_CONVERGES : thm
  REAL_EXP_FDIFF : thm
  SIN_FDIFF : thm
  COS_FDIFF : thm
  SIN_NEGLEMMA : thm
  DIFF_EXP : thm
  DIFF_SIN : thm
  DIFF_COS : thm
  deriving Inhabited

@[nospecialize]
def setupDefs [HolBase] (D : TranscDeps) (BPowSer : PowSer) (BTermDiff : TermDiff) (ACompat : HolLibrary.Analysis.Compat) (ANames : HolLibrary.Analysis.Names) (AReals1 : HolLibrary.Analysis.Reals1) (AReals2 : HolLibrary.Analysis.Reals2) (AReals3 : HolLibrary.Analysis.Reals3) (AAbs : HolLibrary.Analysis.Abs) (APow : HolLibrary.Analysis.Pow) (ASeries1 : HolLibrary.Analysis.Series1) (ASeries2 : HolLibrary.Analysis.Series2) :
    ExceptT String IO Defs := do
  -- @@SCOPE BEGIN
  let { INDUCT_TAC, NUM_REDUCE_CONV, basic_rewrites, new_definition, num_CONV,
        prioritize_num, prioritize_real, set_basic_rewrites, .. } := D
  let { ADD1, ADD_ASSOC, ARITH, BETA_THM, DIV_MULT, EVEN, FACT, FACT_LT, GE,
        LEFT_ADD_DISTRIB, LE_0, LE_TRANS, LT_0, NOT_ODD, NOT_SUC, ODD_EXISTS, .. } := D.core1
  let { REAL_DOWN, REAL_ENTIRE, REAL_EQ_IMP_LE, REAL_LT_ADDR, REAL_LT_TOTAL,
        REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_SYM, real_div, .. } := D.core2
  let { DIFFS_NEG, diffs, .. } := BPowSer
  let { TERMDIFF, .. } := BTermDiff
  let { HALF_MK_ABS, X_FUN_EQ_CONV, .. } := ACompat
  let { LESS_EQ_SUC_REFL, SUC_SUB1, .. } := ANames
  let { REAL_10, REAL_LE_MUL, REAL_LE_TRANS, REAL_LTE_TRANS, REAL_LT_01,
        REAL_LT_IMP_LE, REAL_MUL_LZERO, REAL_MUL_RID, REAL_MUL_RINV, REAL_MUL_RZERO,
        REAL_NEG_LMUL, .. } := AReals1
  let { REAL_EQ_RMUL, REAL_INJ, REAL_INV_POS, REAL_LE, REAL_LT, REAL_LT_IMP_NE,
        REAL_MUL, REAL_NEG_0, REAL_NEG_MINUS1, .. } := AReals2
  let { REAL_INV_MUL_WEAK, REAL_LE_LDIV, REAL_LE_RMUL_EQ, REAL_LE_RMUL_IMP,
        REAL_LT_MUL2_ALT, .. } := AReals3
  let { ABS_0, ABS_INV, ABS_LE, ABS_MUL, ABS_NZ, ABS_POS, ABS_REFL, .. } := AAbs
  let { POW_0, POW_1, POW_ABS, POW_ADD, POW_M1, POW_POS, REAL_ARCH, pow, .. } := APow
  let { SUMMABLE_SUM, SUM_SUMMABLE, SUM_UNIQ, .. } := ASeries1
  let { SER_COMPAR, SER_NEG, SER_RATIO, .. } := ASeries2
  -- @@SCOPE END
  let numc (s : String) : ExceptT String IO thm := do ExceptT.mk (num_CONV (← q s))
  prioritize_num

  -- To avoid all those beta redexes vanishing without trace...

  set_basic_rewrites (subtract' equals_thm (← basic_rewrites)
     [← SPEC_ALL BETA_THM])

  -- Some miscellaneous lemmas

  let MULT_DIV_2 ← prove
   r"!n. (2 * n) DIV 2 = n"
   (GEN_TAC THEN MATCH_MP_TAC DIV_MULT THEN
    REWRITE_TAC [ARITH])

  let EVEN_DIV2 ← prove
   r"!n. ~(EVEN n) ==> ((SUC n) DIV 2 = SUC((n - 1) DIV 2))"
   (GEN_TAC THEN REWRITE_TAC [← GSYM NOT_ODD, ODD_EXISTS] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "m:num") SUBST1_TAC) THEN
    REWRITE_TAC [SUC_SUB1] THEN REWRITE_TAC [ADD1, ← GSYM ADD_ASSOC] THEN
    SUBST1_TAC (← EQT_ELIM (← ExceptT.mk (NUM_REDUCE_CONV (← q "1 + 1 = 2 * 1")))) THEN
    REWRITE_TAC [← GSYM LEFT_ADD_DISTRIB, MULT_DIV_2])

  -- Now set up real numbers interface

  prioritize_real

  -- Another lost lemma.

  let POW_ZERO ← prove
   r"!n x. (x pow n = &0) ==> (x = &0)"
   (INDUCT_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC [pow] THEN
    REWRITE_TAC [REAL_10, REAL_ENTIRE] THEN
    DISCH_THEN (DISJ_CASES_THEN2 ACCEPT_TAC ASSUME_TAC) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC)

  let POW_ZERO_EQ ← prove
   r"!n x. (x pow (SUC n) = &0) <=> (x = &0)"
   (REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC [POW_ZERO] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [POW_0])

  let POW_LT ← prove
   r"!n x y. &0 <= x /\ x < y ==> (x pow (SUC n)) < (y pow (SUC n))"
   (REPEAT STRIP_TAC THEN SPEC_TAC (← q "n:num", ← q "n:num") THEN INDUCT_TAC THENL
     [ASM_REWRITE_TAC [pow, REAL_MUL_RID],
      ONCE_REWRITE_TAC [pow] THEN MATCH_MP_TAC REAL_LT_MUL2_ALT THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC POW_POS THEN ASM_REWRITE_TAC []])

  let POW_EQ ← prove
   r"!n x y. &0 <= x /\ &0 <= y /\ (x pow (SUC n) = y pow (SUC n))
        ==> (x = y)"
   (REPEAT STRIP_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
      (← SPECL [← q "x:real", ← q "y:real"] REAL_LT_TOTAL) THEN
    ASM_REWRITE_TAC [] THEN
    UNDISCH_TAC (← q "x pow (SUC n) = y pow (SUC n)") THEN
    CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN (fun _ => ALL_TAC) THENL
     [ALL_TAC, CONV_TAC (RAND_CONV SYM_CONV)] THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN
    MATCH_MP_TAC POW_LT THEN ASM_REWRITE_TAC [])

  -- Basic differentiation theorems --- none yet.

  let diff_net : NetRef ← do
    let r ← IO.mkRef (HolCore.Nets.empty_net : HolCore.Nets.net DiffRule)
    pure ⟨r.get, r.set⟩

  let add_to_diff_net : thm → ExceptT String IO Unit ← pure (fun th => do
    let t ← liftExcept (do lhand (← rator (← rand (concl th))))
    let net ← diff_net.get
    -- nets.ml's `enter` (Nets.enter needs `Ord` on the elements, which are
    -- functions here; OCaml's `set_insert` is never reached with a
    -- non-empty tip, as each theorem has its own pattern).
    let net' ← ExceptT.mk (HolCore.Nets.enter' [] (t, PART_MATCH
      (fun t => do lhand (← rator (← rand t))) th) net)
    diff_net.set net')

  -- The three functions we define by series are exp, sin, cos

  let exp ← new_definition
   r"exp(x) = suminf(\n. ((\n. inv(&(FACT n)))) n * (x pow n))"

  let sin ← new_definition
   r"sin(x) = suminf(\n. ((\n. if EVEN n then &0 else
      ((--(&1)) pow ((n - 1) DIV 2)) / &(FACT n))) n * (x pow n))"

  let cos ← new_definition
   r"cos(x) = suminf(\n. ((\n. if EVEN n then ((--(&1)) pow (n DIV 2)) / &(FACT n)
       else &0)) n * (x pow n))"

  -- Show the series for exp converges, using the ratio test

  let REAL_EXP_CONVERGES ← prove
   r"!x. (\n. ((\n. inv(&(FACT n)))) n * (x pow n)) sums exp(x)"
   (← do
    let fnz (tm : term) : ExceptT String IO thm := do
      GSYM (← MATCH_MP REAL_LT_IMP_NE (← REWRITE_RULE [← GSYM REAL_LT] (← SPEC tm FACT_LT)))
    let nN ← q "n:num"
    pure (GEN_TAC THEN REWRITE_TAC [exp] THEN MATCH_MP_TAC SUMMABLE_SUM THEN
      MATCH_MP_TAC SER_RATIO THEN
      MP_TAC (← SPEC (← q r"&1") REAL_DOWN) THEN REWRITE_TAC [REAL_LT_01] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "c:real") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q "c:real") THEN ASM_REWRITE_TAC [] THEN
      MP_TAC (← SPEC (← q "c:real") REAL_ARCH) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (MP_TAC o SPEC (← q "abs(x)")) THEN
      DISCH_THEN (X_CHOOSE_TAC (← q "N:num")) THEN EXISTS_TAC (← q "N:num") THEN
      X_GEN_TAC nN THEN REWRITE_TAC [GE] THEN DISCH_TAC THEN
      BETA_TAC THEN
      REWRITE_TAC [ADD1, POW_ADD, ABS_MUL, REAL_MUL_ASSOC, POW_1] THEN
      GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
      REWRITE_TAC [REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL_IMP THEN
      REWRITE_TAC [ABS_POS] THEN REWRITE_TAC [← GSYM ADD1, FACT] THEN
      REWRITE_TAC [← GSYM REAL_MUL, ← MATCH_MP REAL_INV_MUL_WEAK (← CONJ
       (← REWRITE_RULE [← GSYM REAL_INJ] (← SPEC nN NOT_SUC)) (← fnz nN))] THEN
      REWRITE_TAC [ABS_MUL, REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL_IMP THEN REWRITE_TAC [ABS_POS] THEN
      MP_TAC (← SPEC nN LT_0) THEN REWRITE_TAC [← GSYM REAL_LT] THEN
      DISCH_THEN (ASSUME_TAC o GSYM o MATCH_MP REAL_LT_IMP_NE) THEN
      FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP ABS_INV th])) THEN
      REWRITE_TAC [← GSYM real_div] THEN MATCH_MP_TAC REAL_LE_LDIV THEN
      ASM_REWRITE_TAC [← GSYM ABS_NZ] THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
      REWRITE_TAC [← REWRITE_RULE [← GSYM ABS_REFL, ← GSYM REAL_LE] LE_0] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"&N * c") THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC,
        FIRST_ASSUM (fun th => tactic_of do
          pure (REWRITE_TAC [← MATCH_MP REAL_LE_RMUL_EQ th])) THEN
        REWRITE_TAC [REAL_LE] THEN MATCH_MP_TAC LE_TRANS THEN
        EXISTS_TAC nN THEN ASM_REWRITE_TAC [LESS_EQ_SUC_REFL]]))

  -- Show by the comparison test that sin and cos converge

  let SIN_CONVERGES ← prove
   r"!x. (\n. ((\n. if EVEN n then &0 else
  ((--(&1)) pow ((n - 1) DIV 2)) / &(FACT n))) n * (x pow n)) sums
  sin(x)"
   (GEN_TAC THEN REWRITE_TAC [sin] THEN MATCH_MP_TAC SUMMABLE_SUM THEN
    MATCH_MP_TAC SER_COMPAR THEN
    EXISTS_TAC (← q r"\n. ((\n. inv(&(FACT n)))) n * (abs(x) pow n)") THEN
    REWRITE_TAC [← MATCH_MP SUM_SUMMABLE (← SPEC_ALL REAL_EXP_CONVERGES)] THEN
    EXISTS_TAC (← q "0") THEN X_GEN_TAC (← q "n:num") THEN
    DISCH_THEN (fun _ => ALL_TAC) THEN BETA_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC [ABS_MUL, POW_ABS] THENL
     [REWRITE_TAC [ABS_0, REAL_MUL_LZERO] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC [ABS_POS],
      REWRITE_TAC [real_div, ABS_MUL, POW_M1, REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL_IMP THEN REWRITE_TAC [ABS_POS] THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC [ABS_REFL]] THEN
    MAP_EVERY MATCH_MP_TAC [REAL_LT_IMP_LE, REAL_INV_POS] THEN
    REWRITE_TAC [REAL_LT, FACT_LT])

  let COS_CONVERGES ← prove
   r"!x. (\n. ((\n. if EVEN n then ((--(&1)) pow (n DIV 2)) / &(FACT n) else &0)) n
    * (x pow n)) sums cos(x)"
   (GEN_TAC THEN REWRITE_TAC [cos] THEN MATCH_MP_TAC SUMMABLE_SUM THEN
    MATCH_MP_TAC SER_COMPAR THEN
    EXISTS_TAC (← q r"\n. ((\n. inv(&(FACT n)))) n * (abs(x) pow n)") THEN
    REWRITE_TAC [← MATCH_MP SUM_SUMMABLE (← SPEC_ALL REAL_EXP_CONVERGES)] THEN
    EXISTS_TAC (← q "0") THEN X_GEN_TAC (← q "n:num") THEN
    DISCH_THEN (fun _ => ALL_TAC) THEN BETA_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC [ABS_MUL, POW_ABS] THENL
     [REWRITE_TAC [real_div, ABS_MUL, POW_M1, REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL_IMP THEN REWRITE_TAC [ABS_POS] THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC [ABS_REFL],
      REWRITE_TAC [ABS_0, REAL_MUL_LZERO] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC [ABS_POS]] THEN
    MAP_EVERY MATCH_MP_TAC [REAL_LT_IMP_LE, REAL_INV_POS] THEN
    REWRITE_TAC [REAL_LT, FACT_LT])

  -- Show what the formal derivatives of these series are

  let REAL_EXP_FDIFF ← prove
   r"diffs (\n. inv(&(FACT n))) = (\n. inv(&(FACT n)))"
   (REWRITE_TAC [diffs] THEN BETA_TAC THEN
    CONV_TAC (X_FUN_EQ_CONV (← q "n:num")) THEN GEN_TAC THEN BETA_TAC THEN
    REWRITE_TAC [FACT, ← GSYM REAL_MUL] THEN
    SUBGOAL_THEN (← q r"~(&(SUC n) = &0) /\ ~(&(FACT n) = &0)") ASSUME_TAC THENL
     [CONJ_TAC THEN CONV_TAC (RAND_CONV SYM_CONV) THEN
      MATCH_MP_TAC REAL_LT_IMP_NE THEN
      REWRITE_TAC [REAL_LT, LT_0, FACT_LT],
      FIRST_ASSUM (fun th => tactic_of do
        pure (REWRITE_TAC [← MATCH_MP REAL_INV_MUL_WEAK th])) THEN
      GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_LID] THEN
      REWRITE_TAC [REAL_MUL_ASSOC, REAL_EQ_RMUL] THEN DISJ2_TAC THEN
      MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REWRITE_TAC []])

  let SIN_FDIFF ← prove
   r"diffs (\n. if EVEN n then &0 else ((--(&1)) pow ((n - 1) DIV 2)) / &(FACT n))
   = (\n. if EVEN n then ((--(&1)) pow (n DIV 2)) / &(FACT n) else &0)"
   (REWRITE_TAC [diffs] THEN BETA_TAC THEN
    CONV_TAC (X_FUN_EQ_CONV (← q "n:num")) THEN GEN_TAC THEN BETA_TAC THEN
    COND_CASES_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE [EVEN]) THEN
    ASM_REWRITE_TAC [REAL_MUL_RZERO] THEN REWRITE_TAC [SUC_SUB1] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    REWRITE_TAC [real_div, ← GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
    REWRITE_TAC [FACT, ← GSYM REAL_MUL] THEN
    SUBGOAL_THEN (← q r"~(&(SUC n) = &0) /\ ~(&(FACT n) = &0)") ASSUME_TAC THENL
     [CONJ_TAC THEN CONV_TAC (RAND_CONV SYM_CONV) THEN
      MATCH_MP_TAC REAL_LT_IMP_NE THEN
      REWRITE_TAC [REAL_LT, LT_0, FACT_LT],
      FIRST_ASSUM (fun th => tactic_of do
        pure (REWRITE_TAC [← MATCH_MP REAL_INV_MUL_WEAK th])) THEN
      REWRITE_TAC [REAL_MUL_ASSOC] THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
      GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_LID] THEN
      REWRITE_TAC [REAL_MUL_ASSOC, REAL_EQ_RMUL] THEN DISJ2_TAC THEN
      MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REWRITE_TAC []])

  let COS_FDIFF ← prove
   r"diffs (\n. if EVEN n then ((--(&1)) pow (n DIV 2)) / &(FACT n) else &0) =
  (\n. --(((\n. if EVEN n then &0 else ((--(&1)) pow ((n - 1) DIV 2)) /
   &(FACT n))) n))"
   (REWRITE_TAC [diffs] THEN BETA_TAC THEN
    CONV_TAC (X_FUN_EQ_CONV (← q "n:num")) THEN GEN_TAC THEN BETA_TAC THEN
    COND_CASES_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE [EVEN]) THEN
    ASM_REWRITE_TAC [REAL_MUL_RZERO, REAL_NEG_0] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    REWRITE_TAC [real_div, REAL_NEG_LMUL] THEN
    REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN BINOP_TAC THENL
     [POP_ASSUM (SUBST1_TAC o MATCH_MP EVEN_DIV2) THEN
      REWRITE_TAC [pow] THEN REWRITE_TAC [← GSYM REAL_NEG_MINUS1],
      REWRITE_TAC [FACT, ← GSYM REAL_MUL] THEN
      SUBGOAL_THEN (← q r"~(&(SUC n) = &0) /\ ~(&(FACT n) = &0)") ASSUME_TAC THENL
       [CONJ_TAC THEN CONV_TAC (RAND_CONV SYM_CONV) THEN
        MATCH_MP_TAC REAL_LT_IMP_NE THEN
        REWRITE_TAC [REAL_LT, LT_0, FACT_LT],
        FIRST_ASSUM (fun th => tactic_of do
          pure (REWRITE_TAC [← MATCH_MP REAL_INV_MUL_WEAK th])) THEN
        REWRITE_TAC [REAL_MUL_ASSOC] THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
        GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_LID] THEN
        REWRITE_TAC [REAL_MUL_ASSOC, REAL_EQ_RMUL] THEN DISJ2_TAC THEN
        MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REWRITE_TAC []]])

  -- Now at last we can get the derivatives of exp, sin and cos

  let SIN_NEGLEMMA ← prove
   r"!x. --(sin x) = suminf (\n. --(((\n. if EVEN n then &0 else ((--(&1))
        pow ((n - 1) DIV 2)) / &(FACT n))) n * (x pow n)))"
   (GEN_TAC THEN MATCH_MP_TAC SUM_UNIQ THEN
    MP_TAC (← MATCH_MP SER_NEG (← SPEC (← q "x:real") SIN_CONVERGES)) THEN
    BETA_TAC THEN DISCH_THEN ACCEPT_TAC)

  let DIFF_EXP ← prove
   r"!x. (exp diffl exp(x))(x)"
   (GEN_TAC THEN REWRITE_TAC [← HALF_MK_ABS exp] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [← GSYM REAL_EXP_FDIFF] THEN
    CONV_TAC (LAND_CONV BETA_CONV) THEN
    MATCH_MP_TAC TERMDIFF THEN EXISTS_TAC (← q r"abs(x) + &1") THEN
    REWRITE_TAC [REAL_EXP_FDIFF, ← MATCH_MP SUM_SUMMABLE (← SPEC_ALL REAL_EXP_CONVERGES)] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q r"abs(x) + &1") THEN
    REWRITE_TAC [ABS_LE, REAL_LT_ADDR] THEN
    REWRITE_TAC [REAL_LT, ← numc "1", LT_0])

  let DIFF_SIN ← prove
   r"!x. (sin diffl cos(x))(x)"
   (GEN_TAC THEN REWRITE_TAC [← HALF_MK_ABS sin, cos] THEN
    ONCE_REWRITE_TAC [← GSYM SIN_FDIFF] THEN
    MATCH_MP_TAC TERMDIFF THEN EXISTS_TAC (← q r"abs(x) + &1") THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC [← MATCH_MP SUM_SUMMABLE (← SPEC_ALL SIN_CONVERGES)],
      REWRITE_TAC [SIN_FDIFF, ← MATCH_MP SUM_SUMMABLE (← SPEC_ALL COS_CONVERGES)],
      REWRITE_TAC [SIN_FDIFF, COS_FDIFF] THEN BETA_TAC THEN
      MP_TAC (← SPEC (← q r"abs(x) + &1") SIN_CONVERGES) THEN
      DISCH_THEN (MP_TAC o MATCH_MP SER_NEG) THEN
      DISCH_THEN (MP_TAC o MATCH_MP SUM_SUMMABLE) THEN BETA_TAC THEN
      REWRITE_TAC [← GSYM REAL_NEG_LMUL],
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q r"abs(x) + &1") THEN
      REWRITE_TAC [ABS_LE, REAL_LT_ADDR] THEN
      REWRITE_TAC [REAL_LT, ← numc "1", LT_0]])

  let DIFF_COS ← prove
   r"!x. (cos diffl --(sin(x)))(x)"
   (GEN_TAC THEN REWRITE_TAC [← HALF_MK_ABS cos, SIN_NEGLEMMA] THEN
    ONCE_REWRITE_TAC [REAL_NEG_LMUL] THEN
    REWRITE_TAC [← GSYM (← CONV_RULE (RAND_CONV BETA_CONV)
      (← AP_THM COS_FDIFF (← q "n:num")))] THEN
    MATCH_MP_TAC TERMDIFF THEN EXISTS_TAC (← q r"abs(x) + &1") THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC [← MATCH_MP SUM_SUMMABLE (← SPEC_ALL COS_CONVERGES)],
      REWRITE_TAC [COS_FDIFF] THEN
      MP_TAC (← SPEC (← q r"abs(x) + &1") SIN_CONVERGES) THEN
      DISCH_THEN (MP_TAC o MATCH_MP SER_NEG) THEN
      DISCH_THEN (MP_TAC o MATCH_MP SUM_SUMMABLE) THEN BETA_TAC THEN
      REWRITE_TAC [← GSYM REAL_NEG_LMUL],
      REWRITE_TAC [COS_FDIFF, DIFFS_NEG] THEN
      MP_TAC SIN_FDIFF THEN BETA_TAC THEN
      DISCH_THEN (fun th => REWRITE_TAC [th]) THEN
      MP_TAC (← SPEC (← q r"abs(x) + &1") COS_CONVERGES) THEN
      DISCH_THEN (MP_TAC o MATCH_MP SER_NEG) THEN
      DISCH_THEN (MP_TAC o MATCH_MP SUM_SUMMABLE) THEN BETA_TAC THEN
      REWRITE_TAC [← GSYM REAL_NEG_LMUL],
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q r"abs(x) + &1") THEN
      REWRITE_TAC [ABS_LE, REAL_LT_ADDR] THEN
      REWRITE_TAC [REAL_LT, ← numc "1", LT_0]])

  -- @@RETURN BEGIN
  return { MULT_DIV_2, EVEN_DIV2, POW_ZERO, POW_ZERO_EQ, POW_LT, POW_EQ, diff_net,
           add_to_diff_net, exp, sin, cos, REAL_EXP_CONVERGES, SIN_CONVERGES,
           COS_CONVERGES, REAL_EXP_FDIFF, SIN_FDIFF, COS_FDIFF, SIN_NEGLEMMA, DIFF_EXP,
           DIFF_SIN, DIFF_COS }
  -- @@RETURN END

/-- The recursive `DIFF_CONV` inside transc.ml's `DIFF_CONV` (1173-1195). -/
partial def diffConvGo [HolBase] (diff_net : NetRef) (diffl_tm v k : term)
    (DIFF_var DIFF_const : thm) (uneta_CONV : ioconv) (tm : term) :
    ExceptT String IO thm := do
  let go := diffConvGo diff_net diffl_tm v k DIFF_var DIFF_const uneta_CONV
  -- `lookup_expr tm = tryfind (fun f -> f tm) (lookup tm (!diff_net))`
  let lookup_expr (tm : term) : ExceptT String IO thm := do
    let fs := HolCore.Nets.lookup tm (← diff_net.get)
    ExceptT.mk (tryfindM (fun (f : DiffRule) => (f tm).run) fs)
  if !(is_abs tm) then
    let th0 ← ExceptT.mk (uneta_CONV tm)
    let th1 ← go (← liftExcept (rand (concl th0)))
    let sth0 ← SYM th0
    CONV_RULE (RATOR_CONV (LAND_CONV (fun _ => pure (.ok sth0)))) th1
  else
  let (x, bod) ← liftExcept (dest_abs tm)
  if bod == x then INST [(x, v)] DIFF_var
  else if !(free_in x bod) then INST [(bod, k), (x, v)] DIFF_const else
  let th ← lookup_expr tm
  let hyp := (← liftExcept (dest_imp (concl th))).1
  let hyps := conjuncts hyp
  let (dhyps, sides) := partition
    (fun t => match funpow 3 (fun (m : Except String term) => do rator (← m)) (pure t) with
      | .ok r => r == diffl_tm
      | .error _ => false) hyps
  let mkEq ← ExceptT.mk (mk_eq : IO _)
  let tha ← CONJ_ACI_RULE (← liftExcept (do mkEq (hyp, ← HolCore.Bool.list_mk_conj (dhyps ++ sides))))
  let thb ← CONV_RULE (LAND_CONV (fun _ => pure (.ok tha))) th
  let dths ← dhyps.mapM (fun t => do go (← liftExcept (do lhand (← rator t))))
  MATCH_MP thb (← endItlistM CONJ (dths ++ (← sides.mapM ASSUME)))

/- ------------------------------------------------------------------------- -/
/- Differentiation conversion; processed versions of composition theorems;   -/
/- DIFF_TAC; proving differentiability and continuity.                       -/
/- (transc.ml 1164-1265)                                                     -/
/- ------------------------------------------------------------------------- -/

structure DiffConv where
  -- @@FIELDS
  DIFF_CONV : ioconv
  DIFF_COMPOSITE : thm
  DIFF_TAC : tactic
  DIFFERENTIABLE_RULE : term → ExceptT String IO thm
  DIFFERENTIABLE_CONV : ioconv
  CONTINUOUS_RULE : term → ExceptT String IO thm
  CONTINUOUS_CONV : ioconv
  deriving Inhabited

@[nospecialize]
def setupDiffConv [HolBase] (D : TranscDeps) (BDefs : Defs) (ALims : HolLibrary.Analysis.Lims) (ADiffs : HolLibrary.Analysis.Diffs) :
    ExceptT String IO DiffConv := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, .. } := D
  let { EQ_IMP, ETA_AX, .. } := D.core1
  let { DIFF_COS, DIFF_EXP, DIFF_SIN, add_to_diff_net, diff_net, .. } := BDefs
  let { DIFF_CONT, differentiable, .. } := ALims
  let { DIFF_ADD, DIFF_CHAIN, DIFF_CONST, DIFF_DIV, DIFF_INV, DIFF_MUL, DIFF_NEG,
        DIFF_POW, DIFF_SUB, DIFF_X, .. } := ADiffs
  -- @@SCOPE END
  -- Differentiation conversion.

  let DIFF_CONV : ioconv ← do
    let v ← q "x:real"
    let k ← q "k:real"
    let diffl_tm ← q "(diffl)"
    let DIFF_var ← SPEC v DIFF_X
    let DIFF_const ← SPECL [k, v] DIFF_CONST
    let uneta_CONV := REWR_CONV (← GSYM ETA_AX)
    pure (fun tm => ExceptT.run do
      let xv := match bndvar tm with | .ok b => b | .error _ => v
      GEN xv (← DISCH_ALL (← diffConvGo diff_net diffl_tm v k DIFF_var DIFF_const
        uneta_CONV tm)))

  -- Processed versions of composition theorems.

  let DIFF_COMPOSITE ← prove
   r"((f diffl l)(x) /\ ~(f(x) = &0) ==>
        ((\x. inv(f x)) diffl --(l / (f(x) pow 2)))(x)) /\
   ((f diffl l)(x) /\ (g diffl m)(x) /\ ~(g(x) = &0) ==>
    ((\x. f(x) / g(x)) diffl (((l * g(x)) - (m * f(x))) / (g(x) pow 2)))(x)) /\
   ((f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) + g(x)) diffl (l + m))(x)) /\
   ((f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) * g(x)) diffl ((l * g(x)) + (m * f(x))))(x)) /\
   ((f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) - g(x)) diffl (l - m))(x)) /\
   ((f diffl l)(x) ==> ((\x. --(f x)) diffl --l)(x)) /\
   ((g diffl m)(x) ==>
         ((\x. (g x) pow n) diffl ((&n * (g x) pow (n - 1)) * m))(x)) /\
   ((g diffl m)(x) ==> ((\x. exp(g x)) diffl (exp(g x) * m))(x)) /\
   ((g diffl m)(x) ==> ((\x. sin(g x)) diffl (cos(g x) * m))(x)) /\
   ((g diffl m)(x) ==> ((\x. cos(g x)) diffl (--(sin(g x)) * m))(x))"
   (REWRITE_TAC [DIFF_INV, DIFF_DIV, DIFF_ADD, DIFF_SUB, DIFF_MUL, DIFF_NEG] THEN
    REPEAT CONJ_TAC THEN DISCH_TAC THEN
    TRY (MATCH_MP_TAC DIFF_CHAIN THEN
    ASM_REWRITE_TAC [DIFF_SIN, DIFF_COS, DIFF_EXP]) THEN
    MATCH_MP_TAC (← BETA_RULE (← SPEC (← q r"\x. x pow n") DIFF_CHAIN)) THEN
    ASM_REWRITE_TAC [DIFF_POW])

  for th in CONJUNCTS DIFF_COMPOSITE do add_to_diff_net th

  -- Tactic for goals "(f diffl l) x"

  let DIFF_TAC : tactic ← pure (fun gl => ExceptT.run do
    let w := gl.2
    let th ← ExceptT.mk (DIFF_CONV (← liftExcept (do lhand (← rator w))))
    ExceptT.mk ((MP_TAC (← SPEC (← liftExcept (rand w)) th) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC) gl))

  -- Prove differentiability terms.

  let DIFFERENTIABLE_RULE : term → ExceptT String IO thm ← do
    let pth ← prove
     r"(f diffl l) x ==> f differentiable x" (MESON_TAC [differentiable])
    let match_pth := MATCH_MP pth
    pure (fun tm => do
      let (tb, y) ← liftExcept (dest_comb tm)
      let tm' ← liftExcept (rand tb)
      match_pth (← SPEC y (← ExceptT.mk (DIFF_CONV tm'))))

  let DIFFERENTIABLE_CONV : ioconv ← pure (fun tm => (EQT_INTRO o DIFFERENTIABLE_RULE) tm |>.run)

  -- Prove continuity via differentiability (weak but useful).

  let CONTINUOUS_RULE : term → ExceptT String IO thm ← do
    let pth ← prove
     r"!f x. f differentiable x ==> f contl x"
     (MESON_TAC [differentiable, DIFF_CONT])
    let match_pth := PART_MATCH rand pth
    pure (fun tm => do
      let th1 ← match_pth tm
      MP th1 (← DIFFERENTIABLE_RULE (← liftExcept (lhand (concl th1)))))

  let CONTINUOUS_CONV : ioconv ← pure (fun tm => (EQT_INTRO o CONTINUOUS_RULE) tm |>.run)

  -- @@RETURN BEGIN
  return { DIFF_CONV, DIFF_COMPOSITE, DIFF_TAC, DIFFERENTIABLE_RULE, DIFFERENTIABLE_CONV,
           CONTINUOUS_RULE, CONTINUOUS_CONV }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Properties of the exponential function.  (transc.ml 1266-1485)            -/
/- ------------------------------------------------------------------------- -/

structure Exp where
  -- @@FIELDS
  REAL_EXP_0 : thm
  REAL_EXP_LE_X : thm
  REAL_EXP_LT_1 : thm
  REAL_EXP_ADD_MUL : thm
  REAL_EXP_NEG_MUL : thm
  REAL_EXP_NEG_MUL2 : thm
  REAL_EXP_NEG : thm
  REAL_EXP_ADD : thm
  REAL_EXP_POS_LE : thm
  REAL_EXP_NZ : thm
  REAL_EXP_POS_LT : thm
  REAL_EXP_N : thm
  REAL_EXP_SUB : thm
  REAL_EXP_MONO_IMP : thm
  REAL_EXP_MONO_LT : thm
  REAL_EXP_MONO_LE : thm
  REAL_EXP_INJ : thm
  REAL_EXP_TOTAL_LEMMA : thm
  REAL_EXP_TOTAL : thm
  REAL_EXP_BOUND_LEMMA : thm
  deriving Inhabited

@[nospecialize]
def setupExp [HolBase] (D : TranscDeps) (BDefs : Defs) (BDiffConv : DiffConv) (ANames : HolLibrary.Analysis.Names) (ATactics : HolLibrary.Analysis.Tactics) (AReals1 : HolLibrary.Analysis.Reals1) (AReals2 : HolLibrary.Analysis.Reals2) (AReals3 : HolLibrary.Analysis.Reals3) (APow : HolLibrary.Analysis.Pow) (ASums : HolLibrary.Analysis.Sums) (ASeries1 : HolLibrary.Analysis.Series1) (ASeries2 : HolLibrary.Analysis.Series2) (ALims : HolLibrary.Analysis.Lims) (ADiffs : HolLibrary.Analysis.Diffs) (AMvt : HolLibrary.Analysis.Mvt) :
    ExceptT String IO Exp := do
  -- @@SCOPE BEGIN
  let { INDUCT_TAC, REAL_ARITH, REAL_RAT_REDUCE_CONV, num_CONV, .. } := D
  let { ADD1, ADD_CLAUSES, ADD_SYM, BETA_THM, EQ_IMP, FACT, FACT_LT, LE_SUC_LT,
        MULT_CLAUSES, REAL_ADD_LDISTRIB, REAL_ADD_LID, REAL_ADD_RID, real_abs, .. } := D.core1
  let { REAL_INV_LE_1, REAL_LET_TOTAL, REAL_LET_TRANS, REAL_LE_ANTISYM,
        REAL_LE_LCANCEL_IMP, REAL_LT_ADDR, REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_SYM,
        REAL_OF_NUM_LE, REAL_POW_LE, real_div, real_sub, .. } := D.core2
  let { DIFF_EXP, REAL_EXP_CONVERGES, exp, .. } := BDefs
  let { DIFF_CONV, .. } := BDiffConv
  let { LESS_ADD_1, .. } := ANames
  let { X_BETA_CONV, .. } := ATactics
  let { REAL_10, REAL_LE_LT, REAL_LE_MUL, REAL_LE_REFL, REAL_LE_SQUARE, REAL_LE_TRANS,
        REAL_LTE_TRANS, REAL_LT_IMP_LE, REAL_LT_LE, REAL_MUL_LZERO, REAL_MUL_RID,
        REAL_MUL_RINV, REAL_MUL_RZERO, REAL_NEG_LMUL, REAL_NEG_RMUL, REAL_NOT_LT,
        REAL_RDISTRIB, REAL_SUB_ADD2, .. } := AReals1
  let { REAL_ADD, REAL_INV1, REAL_INVINV, REAL_INV_POS, REAL_LT, REAL_LT_IMP_NE,
        REAL_LT_RMUL_EQ, REAL_NEG_0, REAL_RINV_UNIQ, REAL_SUB_0, REAL_SUB_LE,
        REAL_SUB_LT, REAL_SUB_RDISTRIB, .. } := AReals2
  let { REAL_HALF_DOUBLE, REAL_INV_LT1, REAL_LE_LMUL_IMP, REAL_LE_RMUL_IMP,
        REAL_LE_SUB_LADD, .. } := AReals3
  let { POW_0, POW_POS, pow, .. } := APow
  let { sum, .. } := ASums
  let { SER_0, SER_POS_LE, SUM_SUMMABLE, SUM_UNIQ, summable, .. } := ASeries1
  let { GP, SER_LE, .. } := ASeries2
  let { DIFF_CONT, .. } := ALims
  let { IVT, .. } := ADiffs
  let { DIFF_ISCONST_ALL, .. } := AMvt
  -- @@SCOPE END
  let numc (s : String) : ExceptT String IO thm := do ExceptT.mk (num_CONV (← q s))
  -- `W(C SUBGOAL_THEN ttac o funpow 2 (fst o dest_imp) o snd)`
  let subgoalAnte2 (ttac : thm_tactic) : tactic := fun gl => ExceptT.run do
    let t ← liftExcept (funpow 2 (fun (m : Except String term) => do
      pure (← dest_imp (← m)).1) (pure gl.2))
    ExceptT.mk (SUBGOAL_THEN t ttac gl)

  let REAL_EXP_0 ← prove
   r"exp(&0) = &1"
   (REWRITE_TAC [exp] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SUM_UNIQ THEN BETA_TAC THEN
    (fun gl => ExceptT.run do
      let t ← liftExcept (do rand (← rator gl.2))
      ExceptT.mk (MP_TAC (← SPEC t SER_0) gl)) THEN
    DISCH_THEN (MP_TAC o SPEC (← q "1")) THEN
    REWRITE_TAC [← numc "1", sum] THEN
    REWRITE_TAC [ADD_CLAUSES, REAL_ADD_LID] THEN BETA_TAC THEN
    REWRITE_TAC [FACT, pow, REAL_MUL_RID, REAL_INV1] THEN
    REWRITE_TAC [← SYM (← numc "1")] THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC (← q "n:num") THEN REWRITE_TAC [← numc "1", LE_SUC_LT] THEN
    DISCH_THEN (CHOOSE_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
    REWRITE_TAC [← GSYM ADD1, POW_0, REAL_MUL_RZERO, ADD_CLAUSES])

  let REAL_EXP_LE_X ← prove
   r"!x. &0 <= x ==> (&1 + x) <= exp(x)"
   (GEN_TAC THEN DISCH_THEN (DISJ_CASES_TAC o REWRITE_RULE [REAL_LE_LT]) THENL
     [MP_TAC (← SPECL [← q r"\n. ((\n. inv(&(FACT n)))) n * (x pow n)", ← q "2"]
       SER_POS_LE) THEN
      REWRITE_TAC [← MATCH_MP SUM_SUMMABLE (← SPEC_ALL REAL_EXP_CONVERGES)] THEN
      REWRITE_TAC [← GSYM exp] THEN BETA_TAC THEN
      subgoalAnte2 (fun t => REWRITE_TAC [t]) THENL
       [GEN_TAC THEN DISCH_THEN (fun _ => ALL_TAC) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_INV_POS THEN
          REWRITE_TAC [REAL_LT, FACT_LT],
          MATCH_MP_TAC POW_POS THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
          FIRST_ASSUM ACCEPT_TAC],
        CONV_TAC (TOP_DEPTH_CONV num_CONV) THEN REWRITE_TAC [sum] THEN
        BETA_TAC THEN REWRITE_TAC [ADD_CLAUSES, FACT, pow, REAL_ADD_LID] THEN
        REWRITE_TAC [MULT_CLAUSES, REAL_INV1, REAL_MUL_LID, ADD_CLAUSES] THEN
        REWRITE_TAC [REAL_MUL_RID, ← SYM (← numc "1")]],
      POP_ASSUM (SUBST1_TAC o SYM) THEN
      REWRITE_TAC [REAL_EXP_0, REAL_ADD_RID, REAL_LE_REFL]])

  let REAL_EXP_LT_1 ← prove
   r"!x. &0 < x ==> &1 < exp(x)"
   (GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC (← q r"&1 + x") THEN ASM_REWRITE_TAC [REAL_LT_ADDR] THEN
    MATCH_MP_TAC REAL_EXP_LE_X THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    POP_ASSUM ACCEPT_TAC)

  let REAL_EXP_ADD_MUL ← prove
   r"!x y. exp(x + y) * exp(--x) = exp(y)"
   (REPEAT GEN_TAC THEN
    CONV_TAC (LAND_CONV (X_BETA_CONV (← q "x:real"))) THEN
    SUBGOAL_THEN (← q r"exp(y) = (\x. exp(x + y) * exp(--x))(&0)") SUBST1_TAC THENL
     [BETA_TAC THEN REWRITE_TAC [REAL_ADD_LID, REAL_NEG_0] THEN
      REWRITE_TAC [REAL_EXP_0, REAL_MUL_RID],
      MATCH_MP_TAC DIFF_ISCONST_ALL THEN X_GEN_TAC (← q "x:real") THEN
      (fun gl => ExceptT.run do
        let t ← liftExcept (do rand (← funpow 2 (fun (m : Except String term) => do
          rator (← m)) (pure gl.2)))
        ExceptT.mk (MP_TAC (← ExceptT.mk (DIFF_CONV t)) gl)) THEN
      DISCH_THEN (MP_TAC o SPEC (← q "x:real")) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
      AP_TERM_TAC THEN REWRITE_TAC [← GSYM REAL_NEG_LMUL, ← GSYM REAL_NEG_RMUL] THEN
      REWRITE_TAC [← GSYM real_sub, REAL_SUB_0, REAL_MUL_RID, REAL_ADD_RID] THEN
      MATCH_ACCEPT_TAC REAL_MUL_SYM])

  let REAL_EXP_NEG_MUL ← prove
   r"!x. exp(x) * exp(--x) = &1"
   (GEN_TAC THEN MP_TAC (← SPECL [← q "x:real", ← q r"&0"] REAL_EXP_ADD_MUL) THEN
    REWRITE_TAC [REAL_ADD_RID, REAL_EXP_0])

  let REAL_EXP_NEG_MUL2 ← prove
   r"!x. exp(--x) * exp(x) = &1"
   (ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN MATCH_ACCEPT_TAC REAL_EXP_NEG_MUL)

  let REAL_EXP_NEG ← prove
   r"!x. exp(--x) = inv(exp(x))"
   (GEN_TAC THEN MATCH_MP_TAC REAL_RINV_UNIQ THEN
    MATCH_ACCEPT_TAC REAL_EXP_NEG_MUL)

  let REAL_EXP_ADD ← prove
   r"!x y. exp(x + y) = exp(x) * exp(y)"
   (← do
    let ex ← q "exp(x)"
    let mul ← q "(*)"
    pure (REPEAT GEN_TAC THEN
      MP_TAC (← SPECL [← q "x:real", ← q "y:real"] REAL_EXP_ADD_MUL) THEN
      DISCH_THEN (MP_TAC o (fun th => AP_THM th ex) o AP_TERM mul) THEN
      REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN
      REWRITE_TAC [← ONCE_REWRITE_RULE [REAL_MUL_SYM] REAL_EXP_NEG_MUL, REAL_MUL_RID] THEN
      DISCH_THEN SUBST1_TAC THEN MATCH_ACCEPT_TAC REAL_MUL_SYM))

  let REAL_EXP_POS_LE ← prove
   r"!x. &0 <= exp(x)"
   (GEN_TAC THEN
    GEN_REWRITE_TAC (funpow 2 RAND_CONV) [← GSYM REAL_HALF_DOUBLE] THEN
    REWRITE_TAC [REAL_EXP_ADD] THEN MATCH_ACCEPT_TAC REAL_LE_SQUARE)

  let REAL_EXP_NZ ← prove
   r"!x. ~(exp(x) = &0)"
   (GEN_TAC THEN DISCH_TAC THEN
    MP_TAC (← SPEC (← q "x:real") REAL_EXP_NEG_MUL) THEN
    ASM_REWRITE_TAC [REAL_MUL_LZERO] THEN
    CONV_TAC (RAND_CONV SYM_CONV) THEN
    MATCH_ACCEPT_TAC REAL_10)

  let REAL_EXP_POS_LT ← prove
   r"!x. &0 < exp(x)"
   (GEN_TAC THEN REWRITE_TAC [REAL_LT_LE] THEN
    CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
    REWRITE_TAC [REAL_EXP_POS_LE, REAL_EXP_NZ])

  let REAL_EXP_N ← prove
   r"!n x. exp(&n * x) = exp(x) pow n"
   (INDUCT_TAC THEN REWRITE_TAC [REAL_MUL_LZERO, REAL_EXP_0, pow] THEN
    REWRITE_TAC [ADD1] THEN ONCE_REWRITE_TAC [ADD_SYM] THEN
    REWRITE_TAC [← GSYM REAL_ADD, REAL_EXP_ADD, REAL_RDISTRIB] THEN
    GEN_TAC THEN ASM_REWRITE_TAC [REAL_MUL_LID])

  let REAL_EXP_SUB ← prove
   r"!x y. exp(x - y) = exp(x) / exp(y)"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [real_sub, real_div, REAL_EXP_ADD, REAL_EXP_NEG])

  let REAL_EXP_MONO_IMP ← prove
   r"!x y. x < y ==> exp(x) < exp(y)"
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o
      MATCH_MP REAL_EXP_LT_1 o ONCE_REWRITE_RULE [← GSYM REAL_SUB_LT]) THEN
    REWRITE_TAC [REAL_EXP_SUB] THEN
    SUBGOAL_THEN (← q r"&1 < exp(y) / exp(x) <=>
                   (&1 * exp(x)) < ((exp(y) / exp(x)) * exp(x))") SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_LT_RMUL_EQ THEN
      MATCH_ACCEPT_TAC REAL_EXP_POS_LT,
      REWRITE_TAC [real_div, ← GSYM REAL_MUL_ASSOC, REAL_EXP_NEG_MUL2,
                  ← GSYM REAL_EXP_NEG] THEN
      REWRITE_TAC [REAL_MUL_LID, REAL_MUL_RID]])

  let REAL_EXP_MONO_LT ← prove
   r"!x y. exp(x) < exp(y) <=> x < y"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC [REAL_NOT_LT] THEN
      REWRITE_TAC [REAL_LE_LT] THEN
      DISCH_THEN (DISJ_CASES_THEN2 ASSUME_TAC SUBST1_TAC) THEN
      REWRITE_TAC [] THEN DISJ1_TAC THEN MATCH_MP_TAC REAL_EXP_MONO_IMP THEN
      POP_ASSUM ACCEPT_TAC,
      MATCH_ACCEPT_TAC REAL_EXP_MONO_IMP])

  let REAL_EXP_MONO_LE ← prove
   r"!x y. exp(x) <= exp(y) <=> x <= y"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM REAL_NOT_LT] THEN
    REWRITE_TAC [REAL_EXP_MONO_LT])

  let REAL_EXP_INJ ← prove
   r"!x y. (exp(x) = exp(y)) <=> (x = y)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_LE_ANTISYM] THEN
    REWRITE_TAC [REAL_EXP_MONO_LE])

  let REAL_EXP_TOTAL_LEMMA ← prove
   r"!y. &1 <= y ==> ?x. &0 <= x /\ x <= y - &1 /\ (exp(x) = y)"
   (GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC IVT THEN
    ASM_REWRITE_TAC [REAL_EXP_0, REAL_LE_SUB_LADD, REAL_ADD_LID] THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC (ONCE_REWRITE_RULE [← GSYM REAL_SUB_LE]) THEN
      POP_ASSUM (MP_TAC o MATCH_MP REAL_EXP_LE_X) THEN REWRITE_TAC [REAL_SUB_ADD2],
      X_GEN_TAC (← q "x:real") THEN DISCH_THEN (fun _ => ALL_TAC) THEN
      MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC (← q "exp(x)") THEN
      MATCH_ACCEPT_TAC DIFF_EXP])

  let REAL_EXP_TOTAL ← prove
   r"!y. &0 < y ==> ?x. exp(x) = y"
   (GEN_TAC THEN DISCH_TAC THEN
    DISJ_CASES_TAC (← SPECL [← q r"&1", ← q "y:real"] REAL_LET_TOTAL) THENL
     [FIRST_ASSUM (X_CHOOSE_TAC (← q "x:real") o MATCH_MP REAL_EXP_TOTAL_LEMMA) THEN
      EXISTS_TAC (← q "x:real") THEN ASM_REWRITE_TAC [],
      MP_TAC (← SPEC (← q "y:real") REAL_INV_LT1) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
      DISCH_THEN (X_CHOOSE_TAC (← q "x:real") o MATCH_MP REAL_EXP_TOTAL_LEMMA) THEN
      EXISTS_TAC (← q "--x") THEN ASM_REWRITE_TAC [REAL_EXP_NEG] THEN
      MATCH_MP_TAC REAL_INVINV THEN CONV_TAC (RAND_CONV SYM_CONV) THEN
      MATCH_MP_TAC REAL_LT_IMP_NE THEN ASM_REWRITE_TAC []])

  let REAL_EXP_BOUND_LEMMA ← prove
   r"!x. &0 <= x /\ x <= inv(&2) ==> exp(x) <= &1 + &2 * x"
   (← do
    -- The REAL_ARITHs in OCaml's order: the THENL lists are built right to
    -- left and the later rule in a THEN chain first.
    let ra4 ← REAL_ARITH (← q r"&1 <= (&1 + &2 * x) - (x + x * &2 * x) <=>
                                    x * (&2 * x) <= x * &1")
    let ra3 ← REAL_ARITH (← q r"a - x < b - x <=> a < b")
    let ra2 ← REAL_ARITH (← q r"&0 <= x - y <=> y <= x")
    let ra1 ← REAL_ARITH (← q r"(&1 - x = &0) <=> (x = &1)")
    pure (GEN_TAC THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"suminf (\n. x pow n)") THEN CONJ_TAC THENL
       [REWRITE_TAC [exp, BETA_THM] THEN MATCH_MP_TAC SER_LE THEN
        REWRITE_TAC [summable, BETA_THM] THEN REPEAT CONJ_TAC THENL
         [GEN_TAC THEN
          GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_LID] THEN
          MATCH_MP_TAC REAL_LE_RMUL_IMP THEN CONJ_TAC THENL
           [MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC [],
            MATCH_MP_TAC REAL_INV_LE_1 THEN
            REWRITE_TAC [REAL_OF_NUM_LE, ← numc "1", LE_SUC_LT] THEN
            REWRITE_TAC [FACT_LT]],
          EXISTS_TAC (← q "exp x") THEN REWRITE_TAC [← BETA_RULE REAL_EXP_CONVERGES],
          EXISTS_TAC (← q r"inv(&1 - x)") THEN MATCH_MP_TAC GP THEN
          ASM_REWRITE_TAC [real_abs] THEN
          MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q r"inv(&2)") THEN
          ASM_REWRITE_TAC [] THEN CONV_TAC REAL_RAT_REDUCE_CONV],
        SUBGOAL_THEN (← q r"suminf (\n. x pow n) = inv (&1 - x)") SUBST1_TAC THENL
         [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_UNIQ THEN
          MATCH_MP_TAC GP THEN
          ASM_REWRITE_TAC [real_abs] THEN
          MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q r"inv(&2)") THEN
          ASM_REWRITE_TAC [] THEN CONV_TAC REAL_RAT_REDUCE_CONV,
          MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
          EXISTS_TAC (← q r"&1 - x") THEN
          SUBGOAL_THEN (← q r"(&1 - x) * inv (&1 - x) = &1") SUBST1_TAC THENL
           [MATCH_MP_TAC REAL_MUL_RINV THEN
            REWRITE_TAC [ra1] THEN
            DISCH_THEN SUBST_ALL_TAC THEN
            POP_ASSUM MP_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV,
            CONJ_TAC THENL
             [MATCH_MP_TAC REAL_LET_TRANS THEN
              EXISTS_TAC (← q r"inv(&2) - x") THEN
              ASM_REWRITE_TAC [ra2] THEN
              ASM_REWRITE_TAC [ra3] THEN
              CONV_TAC REAL_RAT_REDUCE_CONV,
              REWRITE_TAC [REAL_ADD_LDISTRIB, REAL_SUB_RDISTRIB] THEN
              REWRITE_TAC [REAL_MUL_RID, REAL_MUL_LID] THEN
              REWRITE_TAC [ra4] THEN
              MATCH_MP_TAC REAL_LE_LMUL_IMP THEN ASM_REWRITE_TAC [] THEN
              MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC (← q r"inv(&2)") THEN
              REWRITE_TAC [REAL_MUL_ASSOC] THEN
              CONV_TAC REAL_RAT_REDUCE_CONV THEN
              ASM_REWRITE_TAC [REAL_MUL_LID, real_div]]]]]))

  -- @@RETURN BEGIN
  return { REAL_EXP_0, REAL_EXP_LE_X, REAL_EXP_LT_1, REAL_EXP_ADD_MUL, REAL_EXP_NEG_MUL,
           REAL_EXP_NEG_MUL2, REAL_EXP_NEG, REAL_EXP_ADD, REAL_EXP_POS_LE, REAL_EXP_NZ,
           REAL_EXP_POS_LT, REAL_EXP_N, REAL_EXP_SUB, REAL_EXP_MONO_IMP,
           REAL_EXP_MONO_LT, REAL_EXP_MONO_LE, REAL_EXP_INJ, REAL_EXP_TOTAL_LEMMA,
           REAL_EXP_TOTAL, REAL_EXP_BOUND_LEMMA }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Properties of the logarithmic function; some properties of roots (easier  -/
/- via logarithms); square roots; the derivative of sqrt.                    -/
/- (transc.ml 1487-1806)                                                     -/
/- ------------------------------------------------------------------------- -/

structure LnRoot where
  -- @@FIELDS
  ln : thm
  LN_EXP : thm
  REAL_EXP_LN : thm
  EXP_LN : thm
  LN_MUL : thm
  LN_INJ : thm
  LN_1 : thm
  LN_INV : thm
  LN_DIV : thm
  LN_MONO_LT : thm
  LN_MONO_LE : thm
  LN_POW : thm
  LN_LE : thm
  LN_LT_X : thm
  LN_POS : thm
  LN_POS_LT : thm
  DIFF_LN : thm
  root : thm
  ROOT_LT_LEMMA : thm
  ROOT_LN : thm
  ROOT_0 : thm
  ROOT_1 : thm
  ROOT_POW_POS : thm
  POW_ROOT_POS : thm
  ROOT_POS_POSITIVE : thm
  ROOT_POS_UNIQ : thm
  ROOT_MUL : thm
  ROOT_INV : thm
  ROOT_DIV : thm
  ROOT_MONO_LT : thm
  ROOT_MONO_LE : thm
  ROOT_MONO_LT_EQ : thm
  ROOT_MONO_LE_EQ : thm
  ROOT_INJ : thm
  SQRT_EVEN_POW2 : thm
  REAL_DIV_SQRT : thm
  DIFF_SQRT : thm
  deriving Inhabited

@[nospecialize]
def setupLnRoot [HolBase] (D : TranscDeps) (BDefs : Defs) (BDiffConv : DiffConv) (BExp : Exp) (ATactics : HolLibrary.Analysis.Tactics) (AReals1 : HolLibrary.Analysis.Reals1) (AReals2 : HolLibrary.Analysis.Reals2) (AReals3 : HolLibrary.Analysis.Reals3) (APow : HolLibrary.Analysis.Pow) (ALims : HolLibrary.Analysis.Lims) (ADiffs : HolLibrary.Analysis.Diffs) (AInverse : HolLibrary.Analysis.Inverse) :
    ExceptT String IO LnRoot := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, REAL_ARITH, new_definition, .. } := D
  let { ADD_CLAUSES, ARITH, ARITH_EQ, BETA_THM, DIVISION, EVEN_MOD, NOT_SUC,
        POW_2_SQRT, .. } := D.core1
  let { REAL_ENTIRE, REAL_LET_TRANS, REAL_LE_ANTISYM, REAL_LE_DIV, REAL_LE_INV,
        REAL_LT_ADDL, REAL_LT_MUL, REAL_LT_REFL, REAL_MUL_ASSOC, REAL_MUL_LINV,
        REAL_MUL_SYM, REAL_OF_NUM_EQ, REAL_POW_1, REAL_POW_2, REAL_POW_INV,
        REAL_POW_LE, REAL_POW_LE2, REAL_POW_MUL, REAL_POW_POW, SELECT_AX,
        SELECT_UNIQUE, SQRT_0, SQRT_POS_LE, SQRT_POS_LT, SQRT_POW_2, SQRT_UNIQUE,
        real_div, real_sub, .. } := D.core2
  let { DIFF_EXP, POW_EQ, POW_ZERO, add_to_diff_net, .. } := BDefs
  let { CONTINUOUS_CONV, DIFF_TAC, .. } := BDiffConv
  let { REAL_EXP_0, REAL_EXP_ADD, REAL_EXP_INJ, REAL_EXP_LE_X, REAL_EXP_MONO_LE,
        REAL_EXP_MONO_LT, REAL_EXP_N, REAL_EXP_POS_LE, REAL_EXP_POS_LT, REAL_EXP_TOTAL, .. } := BExp
  let { IMP_SUBST_TAC, .. } := ATactics
  let { REAL_LE_LT, REAL_LE_MUL, REAL_LE_REFL, REAL_LE_TRANS, REAL_LTE_TRANS,
        REAL_LT_01, REAL_LT_ADD, REAL_LT_IMP_LE, REAL_LT_LE, REAL_MUL_LZERO,
        REAL_MUL_RID, REAL_MUL_RINV, REAL_NOT_LT, REAL_RNEG_UNIQ, .. } := AReals1
  let { REAL_DIV_LZERO, REAL_EQ_RMUL, REAL_INJ, REAL_INV_POS, REAL_POS, .. } := AReals2
  let { REAL_LT_IMP_NZ, .. } := AReals3
  let { POW_0, POW_POS_LT, pow, .. } := APow
  let { DIFF_CONT, .. } := ALims
  let { DIFF_CHAIN, .. } := ADiffs
  let { DIFF_INVERSE_LT, .. } := AInverse
  -- @@SCOPE END
  -- `W(C SUBGOAL_THEN ttac o funpow 2 (fst o dest_imp) o snd)`
  let subgoalAnte2 (ttac : thm_tactic) : tactic := fun gl => ExceptT.run do
    let t ← liftExcept (funpow 2 (fun (m : Except String term) => do
      pure (← dest_imp (← m)).1) (pure gl.2))
    ExceptT.mk (SUBGOAL_THEN t ttac gl)

  -- Properties of the logarithmic function

  let ln ← new_definition
   r"ln x = @u. exp(u) = x"

  let LN_EXP ← prove
   r"!x. ln(exp x) = x"
   (GEN_TAC THEN REWRITE_TAC [ln, REAL_EXP_INJ] THEN
    CONV_TAC SYM_CONV THEN CONV_TAC (RAND_CONV (ONCE_DEPTH_CONV SYM_CONV)) THEN
    CONV_TAC (ONCE_DEPTH_CONV ETA_CONV) THEN MATCH_MP_TAC SELECT_AX THEN
    EXISTS_TAC (← q "x:real") THEN REFL_TAC)

  let REAL_EXP_LN ← prove
   r"!x. (exp(ln x) = x) <=> &0 < x"
   (GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_ACCEPT_TAC REAL_EXP_POS_LT,
      DISCH_THEN (X_CHOOSE_THEN (← q "y:real") MP_TAC o MATCH_MP REAL_EXP_TOTAL) THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [REAL_EXP_INJ, LN_EXP]])

  let EXP_LN ← prove
   r"!x. &0 < x ==> exp(ln x) = x"
   (REWRITE_TAC [REAL_EXP_LN])

  let LN_MUL ← prove
   r"!x y. &0 < x /\ &0 < y ==> (ln(x * y) = ln(x) + ln(y))"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_EXP_INJ] THEN
    REWRITE_TAC [REAL_EXP_ADD] THEN SUBGOAL_THEN (← q r"&0 < x * y") ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC [],
      EVERY_ASSUM (fun th => tactic_of do
        pure (REWRITE_TAC [← ONCE_REWRITE_RULE [← GSYM REAL_EXP_LN] th]))])

  let LN_INJ ← prove
   r"!x y. &0 < x /\ &0 < y ==> ((ln(x) = ln(y)) <=> (x = y))"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    EVERY_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
      [← SYM (← REWRITE_RULE [← GSYM REAL_EXP_LN] th)])) THEN
    CONV_TAC SYM_CONV THEN MATCH_ACCEPT_TAC REAL_EXP_INJ)

  let LN_1 ← prove
   r"ln(&1) = &0"
   (ONCE_REWRITE_TAC [← GSYM REAL_EXP_INJ] THEN
    REWRITE_TAC [REAL_EXP_0, REAL_EXP_LN, REAL_LT_01])

  let LN_INV ← prove
   r"!x. &0 < x ==> (ln(inv x) = --(ln x))"
   (GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [← GSYM REAL_RNEG_UNIQ] THEN
    SUBGOAL_THEN (← q r"&0 < x /\ &0 < inv(x)") MP_TAC THENL
     [CONJ_TAC THEN TRY (MATCH_MP_TAC REAL_INV_POS) THEN ASM_REWRITE_TAC [],
      DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← GSYM (← MATCH_MP LN_MUL th)])) THEN
      SUBGOAL_THEN (← q r"x * (inv x) = &1") SUBST1_TAC THENL
       [MATCH_MP_TAC REAL_MUL_RINV THEN
        POP_ASSUM (ACCEPT_TAC o MATCH_MP REAL_LT_IMP_NZ),
        REWRITE_TAC [LN_1]]])

  let LN_DIV ← prove
   r"!x. &0 < x /\ &0 < y ==> (ln(x / y) = ln(x) - ln(y))"
   (← do
    let lninv ← MATCH_MP LN_INV (← ASSUME (← q r"&0 < y"))
    pure (GEN_TAC THEN STRIP_TAC THEN
      SUBGOAL_THEN (← q r"&0 < x /\ &0 < inv(y)") MP_TAC THENL
       [CONJ_TAC THEN TRY (MATCH_MP_TAC REAL_INV_POS) THEN ASM_REWRITE_TAC [],
        REWRITE_TAC [real_div] THEN
        DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP LN_MUL th])) THEN
        REWRITE_TAC [lninv] THEN
        REWRITE_TAC [real_sub]]))

  let LN_MONO_LT ← prove
   r"!x y. &0 < x /\ &0 < y ==> (ln(x) < ln(y) <=> x < y)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    EVERY_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
      [← SYM (← REWRITE_RULE [← GSYM REAL_EXP_LN] th)])) THEN
    CONV_TAC SYM_CONV THEN MATCH_ACCEPT_TAC REAL_EXP_MONO_LT)

  let LN_MONO_LE ← prove
   r"!x y. &0 < x /\ &0 < y ==> (ln(x) <= ln(y) <=> x <= y)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    EVERY_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
      [← SYM (← REWRITE_RULE [← GSYM REAL_EXP_LN] th)])) THEN
    CONV_TAC SYM_CONV THEN MATCH_ACCEPT_TAC REAL_EXP_MONO_LE)

  let LN_POW ← prove
   r"!n x. &0 < x ==> (ln(x pow n) = &n * ln(x))"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (CHOOSE_THEN (SUBST1_TAC o SYM) o MATCH_MP REAL_EXP_TOTAL) THEN
    REWRITE_TAC [← GSYM REAL_EXP_N, LN_EXP])

  let LN_LE ← prove
   r"!x. &0 <= x ==> ln(&1 + x) <= x"
   (GEN_TAC THEN DISCH_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM LN_EXP] THEN
    MP_TAC (← SPECL [← q r"&1 + x", ← q "exp(x)"] LN_MONO_LE) THEN
    subgoalAnte2 (fun t => REWRITE_TAC [t]) THENL
     [REWRITE_TAC [REAL_EXP_POS_LT] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC (← q "x:real") THEN ASM_REWRITE_TAC [REAL_LT_ADDL, REAL_LT_01],
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC REAL_EXP_LE_X THEN ASM_REWRITE_TAC []])

  let LN_LT_X ← prove
   r"!x. &0 < x ==> ln(x) < x"
   (GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC (← q r"ln(&1 + x)") THEN CONJ_TAC THENL
     [IMP_SUBST_TAC LN_MONO_LT THEN
      ASM_REWRITE_TAC [REAL_LT_ADDL, REAL_LT_01] THEN
      MATCH_MP_TAC REAL_LT_ADD THEN ASM_REWRITE_TAC [REAL_LT_01],
      MATCH_MP_TAC LN_LE THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      ASM_REWRITE_TAC []])

  let LN_POS ← prove
   r"!x. &1 <= x ==> &0 <= ln(x)"
   (← do
    let ar ← ARITH_RULE (← q r"&1 <= x ==> &0 < x")
    pure (REWRITE_TAC [← GSYM LN_1] THEN
      SIMP_TAC [LN_MONO_LE, ar, REAL_LT_01]))

  let LN_POS_LT ← prove
   r"!x. &1 < x ==> &0 < ln(x)"
   (← do
    let ar ← ARITH_RULE (← q r"&1 < x ==> &0 < x")
    pure (REWRITE_TAC [← GSYM LN_1] THEN
      SIMP_TAC [LN_MONO_LT, ar, REAL_LT_01]))

  let DIFF_LN ← prove
   r"!x. &0 < x ==> (ln diffl (inv x))(x)"
   (GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o REWRITE_RULE [← GSYM REAL_EXP_LN]) THEN
    FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [← GSYM th])) THEN
    MATCH_MP_TAC DIFF_INVERSE_LT THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP REAL_LT_IMP_NZ) THEN
    ASM_REWRITE_TAC [← MATCH_MP DIFF_CONT (← SPEC_ALL DIFF_EXP)] THEN
    MP_TAC (← SPEC (← q "ln(x)") DIFF_EXP) THEN ASM_REWRITE_TAC [] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC [LN_EXP] THEN
    EXISTS_TAC (← q r"&1") THEN MATCH_ACCEPT_TAC REAL_LT_01)

  -- Some properties of roots (easier via logarithms)

  let root ← new_definition
   r"root(n) x = @u. (&0 < x ==> &0 < u) /\ (u pow n = x)"

  let ROOT_LT_LEMMA ← prove
   r"!n x. &0 < x ==> (exp(ln(x) / &(SUC n)) pow (SUC n) = x)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [← GSYM REAL_EXP_N] THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    REWRITE_TAC [real_div, ← GSYM REAL_MUL_ASSOC] THEN
    SUBGOAL_THEN (← q r"inv(&(SUC n)) * &(SUC n) = &1") SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_LINV THEN REWRITE_TAC [REAL_INJ, NOT_SUC],
      ASM_REWRITE_TAC [REAL_MUL_RID, REAL_EXP_LN]])

  let ROOT_LN ← prove
   r"!x. &0 < x ==> !n. root(SUC n) x = exp(ln(x) / &(SUC n))"
   (GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN REWRITE_TAC [root] THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC (← q "y:real") THEN BETA_TAC THEN
    ASM_REWRITE_TAC [] THEN EQ_TAC THENL
     [DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
      SUBGOAL_THEN (← q r"!z. &0 < y /\ &0 < exp(z)") MP_TAC THENL
       [ASM_REWRITE_TAC [REAL_EXP_POS_LT], ALL_TAC] THEN
      DISCH_THEN (MP_TAC o GEN_ALL o SYM o MATCH_MP LN_INJ o SPEC_ALL) THEN
      DISCH_THEN (fun th => GEN_REWRITE_TAC id [th]) THEN
      REWRITE_TAC [LN_EXP] THEN
      SUBGOAL_THEN (← q r"ln(y) * &(SUC n) = (ln(y pow(SUC n)) / &(SUC n)) * &(SUC n)")
      MP_TAC THENL
       [REWRITE_TAC [real_div, ← GSYM REAL_MUL_ASSOC] THEN
        SUBGOAL_THEN (← q r"inv(&(SUC n)) * &(SUC n) = &1") SUBST1_TAC THENL
         [MATCH_MP_TAC REAL_MUL_LINV THEN REWRITE_TAC [REAL_INJ, NOT_SUC],
          REWRITE_TAC [REAL_MUL_RID] THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
          CONV_TAC SYM_CONV THEN MATCH_MP_TAC LN_POW THEN
          ASM_REWRITE_TAC []],
        REWRITE_TAC [REAL_EQ_RMUL, REAL_INJ, NOT_SUC]],
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [REAL_EXP_POS_LT] THEN
      MATCH_MP_TAC ROOT_LT_LEMMA THEN ASM_REWRITE_TAC []])

  let ROOT_0 ← prove
   r"!n. root(SUC n) (&0) = &0"
   (GEN_TAC THEN REWRITE_TAC [root] THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC (← q "y:real") THEN
    BETA_TAC THEN REWRITE_TAC [REAL_LT_REFL] THEN EQ_TAC THENL
     [SPEC_TAC (← q "n:num", ← q "n:num") THEN INDUCT_TAC THEN ONCE_REWRITE_TAC [pow] THENL
       [REWRITE_TAC [pow, REAL_MUL_RID],
        REWRITE_TAC [REAL_ENTIRE] THEN DISCH_THEN DISJ_CASES_TAC THEN
        ASM_REWRITE_TAC [] THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC []],
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [pow, REAL_MUL_LZERO]])

  let ROOT_1 ← prove
   r"!n. root(SUC n) (&1) = &1"
   (GEN_TAC THEN REWRITE_TAC [← MATCH_MP ROOT_LN REAL_LT_01] THEN
    REWRITE_TAC [LN_1, REAL_DIV_LZERO, REAL_EXP_0])

  let ROOT_POW_POS ← prove
   r"!n x. &0 <= x ==> ((root(SUC n) x) pow (SUC n) = x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [REAL_LE_LT] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [FIRST_ASSUM (fun th => tactic_of do
        let b ← MATCH_MP ROOT_LT_LEMMA th
        let a ← MATCH_MP ROOT_LN th
        pure (REWRITE_TAC [a, b])),
      FIRST_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC [ROOT_0] THEN
      MATCH_ACCEPT_TAC POW_0])

  let POW_ROOT_POS ← prove
   r"!n x. &0 <= x ==> (root(SUC n)(x pow (SUC n)) = x)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [root] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    X_GEN_TAC (← q "y:real") THEN BETA_TAC THEN EQ_TAC THEN
    DISCH_TAC THEN ASM_REWRITE_TAC [] THENL
     [DISJ_CASES_THEN MP_TAC (← REWRITE_RULE [REAL_LE_LT] (← ASSUME (← q r"&0 <= x"))) THENL
       [DISCH_TAC THEN FIRST_ASSUM (undischCheck (fun c => pure (is_conj c))) THEN
        FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP POW_POS_LT th])) THEN
        DISCH_TAC THEN MATCH_MP_TAC POW_EQ THEN EXISTS_TAC (← q "n:num") THEN
        ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
        ASM_REWRITE_TAC [],
        DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
        FIRST_ASSUM (undischCheck (fun c => pure (is_conj c))) THEN
        REWRITE_TAC [POW_0, REAL_LT_REFL, POW_ZERO]],
      ASM_REWRITE_TAC [REAL_LT_LE] THEN CONV_TAC CONTRAPOS_CONV THEN
      REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      REWRITE_TAC [POW_0]])

  let ROOT_POS_POSITIVE ← prove
   r"!x n. &0 <= x ==> &0 <= root(SUC n) x"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (DISJ_CASES_TAC o REWRITE_RULE [REAL_LE_LT]) THENL
     [POP_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP ROOT_LN th])) THEN
      REWRITE_TAC [REAL_EXP_POS_LE],
      POP_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC [ROOT_0] THEN
      REWRITE_TAC [REAL_LE_REFL]])

  let ROOT_POS_UNIQ ← prove
   r"!n x y. &0 <= x /\ &0 <= y /\ (y pow (SUC n) = x)
           ==> (root (SUC n) x = y)"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM)) THEN
    ASM_SIMP_TAC [POW_ROOT_POS])

  let ROOT_MUL ← prove
   r"!n x y. &0 <= x /\ &0 <= y
           ==> (root(SUC n) (x * y) = root(SUC n) x * root(SUC n) y)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC ROOT_POS_UNIQ THEN
    ASM_SIMP_TAC [REAL_POW_MUL, ROOT_POW_POS, REAL_LE_MUL,
                 ROOT_POS_POSITIVE])

  let ROOT_INV ← prove
   r"!n x. &0 <= x ==> (root(SUC n) (inv x) = inv(root(SUC n) x))"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC ROOT_POS_UNIQ THEN
    ASM_SIMP_TAC [REAL_LE_INV, ROOT_POS_POSITIVE, REAL_POW_INV,
                 ROOT_POW_POS])

  let ROOT_DIV ← prove
   r"!n x y. &0 <= x /\ &0 <= y
           ==> (root(SUC n) (x / y) = root(SUC n) x / root(SUC n) y)"
   (SIMP_TAC [real_div, ROOT_MUL, ROOT_INV, REAL_LE_INV])

  let ROOT_MONO_LT ← prove
   r"!x y. &0 <= x /\ x < y ==> root(SUC n) x < root(SUC n) y"
   (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"&0 <= y") ASSUME_TAC THENL
     [ASM_MESON_TAC [REAL_LE_TRANS, REAL_LT_IMP_LE], ALL_TAC] THEN
    UNDISCH_TAC (← q "x < y") THEN CONV_TAC CONTRAPOS_CONV THEN
    REWRITE_TAC [REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"(x = (root(SUC n) x) pow (SUC n)) /\
                  (y = (root(SUC n) y) pow (SUC n))")
     (CONJUNCTS_THEN SUBST1_TAC)
    THENL [ASM_SIMP_TAC [← GSYM ROOT_POW_POS], ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_SIMP_TAC [NOT_SUC, ROOT_POS_POSITIVE])

  let ROOT_MONO_LE ← prove
   r"!x y. &0 <= x /\ x <= y ==> root(SUC n) x <= root(SUC n) y"
   (MESON_TAC [ROOT_MONO_LT, REAL_LE_LT])

  let ROOT_MONO_LT_EQ ← prove
   r"!x y. &0 <= x /\ &0 <= y ==> (root(SUC n) x < root(SUC n) y <=> x < y)"
   (MESON_TAC [ROOT_MONO_LT, REAL_NOT_LT, ROOT_MONO_LE])

  let ROOT_MONO_LE_EQ ← prove
   r"!x y. &0 <= x /\ &0 <= y ==> (root(SUC n) x <= root(SUC n) y <=> x <= y)"
   (MESON_TAC [ROOT_MONO_LT, REAL_NOT_LT, ROOT_MONO_LE])

  let ROOT_INJ ← prove
   r"!x y. &0 <= x /\ &0 <= y ==> ((root(SUC n) x = root(SUC n) y) <=> (x = y))"
   (SIMP_TAC [← GSYM REAL_LE_ANTISYM, ROOT_MONO_LE_EQ])

  -- Special case of square roots, a few theorems not already present.

  let SQRT_EVEN_POW2 ← prove
   r"!n. EVEN n ==> (sqrt(&2 pow n) = &2 pow (n DIV 2))"
   (GEN_TAC THEN REWRITE_TAC [EVEN_MOD] THEN DISCH_TAC THEN
    MATCH_MP_TAC SQRT_UNIQUE THEN
    SIMP_TAC [REAL_POW_LE, REAL_POS, REAL_POW_POW] THEN
    AP_TERM_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [← MATCH_MP DIVISION (← ARITH_RULE (← q r"~(2 = 0)"))] THEN
    ASM_REWRITE_TAC [ADD_CLAUSES])

  let REAL_DIV_SQRT ← prove
   r"!x. &0 <= x ==> x / sqrt(x) = sqrt(x)"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"x = &0") THENL
     [ASM_REWRITE_TAC [SQRT_0, real_div, REAL_MUL_LZERO], ALL_TAC] THEN
    DISCH_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_UNIQUE THEN
    ASM_SIMP_TAC [SQRT_POS_LE, REAL_LE_DIV] THEN
    REWRITE_TAC [real_div, REAL_POW_MUL, REAL_POW_INV] THEN
    ASM_SIMP_TAC [SQRT_POW_2] THEN
    REWRITE_TAC [REAL_POW_2, ← GSYM REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC [REAL_MUL_RINV, REAL_MUL_RID])

  -- Derivative of sqrt (could do the other roots with a bit more care).

  let DIFF_SQRT ← prove
   r"!x. &0 < x ==> (sqrt diffl inv(&2 * sqrt(x))) x"
   (← do
    let ra ← REAL_ARITH (← q r"abs(x - y) < y ==> &0 <= x")
    pure (REPEAT STRIP_TAC THEN
      MP_TAC (← SPECL [← q r"\x. x pow 2", ← q "sqrt", ← q r"&2 * sqrt(x)",
                       ← q "sqrt(x)", ← q "sqrt(x)"]
            DIFF_INVERSE_LT) THEN
      ASM_SIMP_TAC [SQRT_POW_2, REAL_LT_IMP_LE, BETA_THM] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC [SQRT_POS_LT, REAL_LT_IMP_NZ, REAL_ENTIRE] THEN
      REWRITE_TAC [REAL_OF_NUM_EQ, ARITH_EQ] THEN REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC [POW_2_SQRT, ra],
        REPEAT STRIP_TAC THEN CONV_TAC CONTINUOUS_CONV,
        DIFF_TAC THEN REWRITE_TAC [ARITH, REAL_POW_1, REAL_MUL_RID]]))

  -- `let DIFF_SQRT_COMPOSITE = prove (...) in add_to_diff_net ...`: a local
  -- binding, not exported.
  let _DIFF_SQRT_COMPOSITE ← prove
   r"!g m x. (g diffl m)(x) /\ &0 < g x
           ==> ((\x. sqrt(g x)) diffl (inv(&2 * sqrt(g x)) * m))(x)"
   (SIMP_TAC [DIFF_CHAIN, DIFF_SQRT])
  add_to_diff_net (← SPEC_ALL _DIFF_SQRT_COMPOSITE)

  -- @@RETURN BEGIN
  return { ln, LN_EXP, REAL_EXP_LN, EXP_LN, LN_MUL, LN_INJ, LN_1, LN_INV, LN_DIV,
           LN_MONO_LT, LN_MONO_LE, LN_POW, LN_LE, LN_LT_X, LN_POS, LN_POS_LT, DIFF_LN,
           root, ROOT_LT_LEMMA, ROOT_LN, ROOT_0, ROOT_1, ROOT_POW_POS, POW_ROOT_POS,
           ROOT_POS_POSITIVE, ROOT_POS_UNIQ, ROOT_MUL, ROOT_INV, ROOT_DIV, ROOT_MONO_LT,
           ROOT_MONO_LE, ROOT_MONO_LT_EQ, ROOT_MONO_LE_EQ, ROOT_INJ, SQRT_EVEN_POW2,
           REAL_DIV_SQRT, DIFF_SQRT }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Basic properties of the trig functions; a least positive x with           -/
/- cos(x) = 0, hence pi.  (transc.ml 1808-2195)                              -/
/- ------------------------------------------------------------------------- -/

structure Trig1 where
  -- @@FIELDS
  SIN_0 : thm
  COS_0 : thm
  SIN_CIRCLE : thm
  SIN_BOUND : thm
  SIN_BOUNDS : thm
  COS_BOUND : thm
  COS_BOUNDS : thm
  SIN_COS_ADD : thm
  SIN_COS_NEG : thm
  SIN_ADD : thm
  COS_ADD : thm
  SIN_NEG : thm
  COS_NEG : thm
  SIN_DOUBLE : thm
  COS_DOUBLE : thm
  COS_ABS : thm
  SIN_PAIRED : thm
  SIN_POS : thm
  COS_PAIRED : thm
  COS_2 : thm
  COS_ISZERO : thm
  pi : thm
  deriving Inhabited

@[nospecialize]
def setupTrig1 [HolBase] (D : TranscDeps) (BDefs : Defs) (BDiffConv : DiffConv) (ANames : HolLibrary.Analysis.Names) (ATactics : HolLibrary.Analysis.Tactics) (AReals1 : HolLibrary.Analysis.Reals1) (AReals2 : HolLibrary.Analysis.Reals2) (AReals3 : HolLibrary.Analysis.Reals3) (AAbs : HolLibrary.Analysis.Abs) (APow : HolLibrary.Analysis.Pow) (ASums : HolLibrary.Analysis.Sums) (ASeries1 : HolLibrary.Analysis.Series1) (ASeries2 : HolLibrary.Analysis.Series2) (ALims : HolLibrary.Analysis.Lims) (ADiffs : HolLibrary.Analysis.Diffs) (AMvt : HolLibrary.Analysis.Mvt) :
    ExceptT String IO Trig1 := do
  -- @@SCOPE BEGIN
  let { NUM_REDUCE_TAC, new_definition, num_CONV, .. } := D
  let { ADD1, ADD_CLAUSES, CONJ_ASSOC, DIV_UNIQ, EQ_IMP, EVEN, EVEN_DOUBLE, FACT,
        FACT_LT, LE_0, LE_SUC, LE_SUC_LT, LT_0, LT_SUC, MULT_CLAUSES, NOT_EVEN,
        NOT_IMP, NOT_SUC, ODD_DOUBLE, ODD_EXISTS, REAL_ADD_AC, REAL_ADD_ASSOC,
        REAL_ADD_LID, REAL_ADD_LINV, REAL_ADD_RID, real_abs, .. } := D.core1
  let { REAL_ADD_RINV, REAL_DIV_REFL, REAL_ENTIRE, REAL_EQ_SUB_LADD, REAL_LET_ADD,
        REAL_LET_TRANS, REAL_LE_01, REAL_LT_MUL, REAL_LT_REFL, REAL_LT_TOTAL,
        REAL_LT_TRANS, REAL_MUL_AC, REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_SYM,
        REAL_POW2_ABS, real_div, real_sub, .. } := D.core2
  let { COS_CONVERGES, DIFF_COS, MULT_DIV_2, SIN_CONVERGES, cos, sin, .. } := BDefs
  let { DIFF_CONV, .. } := BDiffConv
  let { LESS_ADD_1, LESS_SUC_REFL, SUC_SUB1, .. } := ANames
  let { IMP_SUBST_TAC, X_BETA_CONV, .. } := ATactics
  let { REAL_10, REAL_LE_MUL, REAL_LE_SQUARE, REAL_LNEG_UNIQ, REAL_LTE_TRANS,
        REAL_LT_IMP_LE, REAL_MUL_LZERO, REAL_MUL_RID, REAL_MUL_RINV, REAL_MUL_RZERO,
        REAL_NEG_ADD, REAL_NEG_LMUL, REAL_NEG_LT0, REAL_NEG_NEG, REAL_NEG_RMUL,
        REAL_NOT_LE, .. } := AReals1
  let { REAL_ADD, REAL_DOUBLE, REAL_INJ, REAL_INV_POS, REAL_LE, REAL_LT,
        REAL_LT_RMUL_IMP, REAL_MUL, REAL_NEG_0, REAL_NEG_EQ0, REAL_NEG_MINUS1,
        REAL_SUB_0, REAL_SUB_LT, REAL_SUB_REFL, .. } := AReals2
  let { REAL_EQ_LMUL_IMP, REAL_INV_MUL_WEAK, REAL_LTE_ADD, REAL_LT_1, REAL_LT_IMP_NZ,
        REAL_LT_MUL2_ALT, REAL_SUB_LZERO, REAL_SUB_RZERO, REAL_SUMSQ, .. } := AReals3
  let { ABS_BOUNDS, .. } := AAbs
  let { POW_0, POW_1, POW_2, POW_ADD, POW_MINUS1, POW_POS_LT, REAL_LT1_POW2, pow, .. } := APow
  let { SUM_2, sum, .. } := ASums
  let { SER_0, SER_PAIR, SER_POS_LT, SUM_SUMMABLE, SUM_UNIQ, .. } := ASeries1
  let { SER_NEG, SER_POS_LT_PAIR, .. } := ASeries2
  let { DIFF_CONT, DIFF_UNIQ, differentiable, .. } := ALims
  let { IVT2, .. } := ADiffs
  let { DIFF_ISCONST_ALL, ROLLE, .. } := AMvt
  -- @@SCOPE END
  let numc (s : String) : ExceptT String IO thm := do ExceptT.mk (num_CONV (← q s))
  -- `W(MP_TAC o C SPEC SER_0 o rand o rator o snd)`
  let mpSer0 : tactic := fun gl => ExceptT.run do
    let t ← liftExcept (do rand (← rator gl.2))
    ExceptT.mk (MP_TAC (← SPEC t SER_0) gl)
  -- `W(MP_TAC o DIFF_CONV o rand o funpow 2 rator o snd)`
  let mpDiffConv : tactic := fun gl => ExceptT.run do
    let t ← liftExcept (do rand (← funpow 2 (fun (m : Except String term) => do
      rator (← m)) (pure gl.2)))
    ExceptT.mk (MP_TAC (← ExceptT.mk (DIFF_CONV t)) gl)
  -- `W(C SUBGOAL_THEN (SUBST1_TAC o SYM) o subst[`&0`,`x:real`] o snd)`
  let subgoalAt0 : tactic := fun gl => ExceptT.run do
    let sb ← ExceptT.mk (subst [(← q r"&0", ← q "x:real")])
    let t ← ExceptT.mk (sb gl.2)
    ExceptT.mk (SUBGOAL_THEN t (SUBST1_TAC o SYM) gl)
  let _invMulSym ← CONV_RULE (RAND_CONV SYM_CONV) (← SPEC_ALL REAL_INV_MUL_WEAK)

  let SIN_0 ← prove
   r"sin(&0) = &0"
   (REWRITE_TAC [sin] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SUM_UNIQ THEN BETA_TAC THEN
    mpSer0 THEN
    DISCH_THEN (MP_TAC o SPEC (← q "0")) THEN REWRITE_TAC [LE_0] THEN
    BETA_TAC THEN
    REWRITE_TAC [sum] THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC (← q "n:num") THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [REAL_MUL_LZERO] THEN
    MP_TAC (← SPEC (← q "n:num") ODD_EXISTS) THEN ASM_REWRITE_TAC [← GSYM NOT_EVEN] THEN
    DISCH_THEN (CHOOSE_THEN SUBST1_TAC) THEN
    REWRITE_TAC [← GSYM ADD1, POW_0, REAL_MUL_RZERO])

  let COS_0 ← prove
   r"cos(&0) = &1"
   (REWRITE_TAC [cos] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SUM_UNIQ THEN BETA_TAC THEN
    mpSer0 THEN
    DISCH_THEN (MP_TAC o SPEC (← q "1")) THEN
    REWRITE_TAC [← numc "1", sum, ADD_CLAUSES] THEN BETA_TAC THEN
    REWRITE_TAC [EVEN, pow, FACT] THEN
    REWRITE_TAC [REAL_ADD_LID, REAL_MUL_RID] THEN
    SUBGOAL_THEN (← q "0 DIV 2 = 0") SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC (← q "0") THEN
      REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES] THEN
      REWRITE_TAC [← numc "2", LT_0],
      REWRITE_TAC [pow]] THEN
    SUBGOAL_THEN (← q r"&1 / &1 = &(SUC 0)") SUBST1_TAC THENL
     [REWRITE_TAC [← SYM (← numc "1")] THEN MATCH_MP_TAC REAL_DIV_REFL THEN
      MATCH_ACCEPT_TAC REAL_10,
      DISCH_THEN MATCH_MP_TAC] THEN
    X_GEN_TAC (← q "n:num") THEN REWRITE_TAC [LE_SUC_LT] THEN
    DISCH_THEN (CHOOSE_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
    REWRITE_TAC [← GSYM ADD1, POW_0, REAL_MUL_RZERO, ADD_CLAUSES])

  let SIN_CIRCLE ← prove
   r"!x. (sin(x) pow 2) + (cos(x) pow 2) = &1"
   (GEN_TAC THEN CONV_TAC (LAND_CONV (X_BETA_CONV (← q "x:real"))) THEN
    SUBGOAL_THEN (← q r"&1 = (\x.(sin(x) pow 2) + (cos(x) pow 2))(&0)") SUBST1_TAC THENL
     [BETA_TAC THEN REWRITE_TAC [SIN_0, COS_0] THEN
      REWRITE_TAC [← numc "2", POW_0] THEN
      REWRITE_TAC [pow, POW_1] THEN REWRITE_TAC [REAL_ADD_LID, REAL_MUL_LID],
      MATCH_MP_TAC DIFF_ISCONST_ALL THEN X_GEN_TAC (← q "x:real") THEN
      mpDiffConv THEN
      DISCH_THEN (MP_TAC o SPEC (← q "x:real")) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
      AP_TERM_TAC THEN REWRITE_TAC [← GSYM REAL_NEG_LMUL, ← GSYM REAL_NEG_RMUL] THEN
      REWRITE_TAC [← GSYM real_sub, REAL_SUB_0] THEN
      REWRITE_TAC [← GSYM REAL_MUL_ASSOC, REAL_MUL_RID] THEN
      AP_TERM_TAC THEN REWRITE_TAC [← numc "2", SUC_SUB1] THEN
      REWRITE_TAC [POW_1] THEN MATCH_ACCEPT_TAC REAL_MUL_SYM])

  let SIN_BOUND ← prove
   r"!x. abs(sin x) <= &1"
   (← do
    let lsq ← SPEC (← q "cos(x)") REAL_LE_SQUARE
    pure (GEN_TAC THEN GEN_REWRITE_TAC id [← TAUT (← q r"a <=> ~ ~a")] THEN
      PURE_ONCE_REWRITE_TAC [REAL_NOT_LE] THEN
      DISCH_THEN (MP_TAC o MATCH_MP REAL_LT1_POW2) THEN
      REWRITE_TAC [REAL_POW2_ABS] THEN
      DISCH_THEN (MP_TAC o ONCE_REWRITE_RULE [← GSYM REAL_SUB_LT]) THEN
      DISCH_THEN (MP_TAC o (fun th => CONJ th lsq)) THEN
      REWRITE_TAC [← GSYM POW_2] THEN
      DISCH_THEN (MP_TAC o MATCH_MP REAL_LTE_ADD) THEN
      REWRITE_TAC [real_sub, ← GSYM REAL_ADD_ASSOC] THEN
      ONCE_REWRITE_TAC [← AC REAL_ADD_AC
        (← q r"a + b + c = (a + c) + b")] THEN
      REWRITE_TAC [SIN_CIRCLE, REAL_ADD_RINV, REAL_LT_REFL]))

  let SIN_BOUNDS ← prove
   r"!x. --(&1) <= sin(x) /\ sin(x) <= &1"
   (GEN_TAC THEN REWRITE_TAC [← GSYM ABS_BOUNDS, SIN_BOUND])

  let COS_BOUND ← prove
   r"!x. abs(cos x) <= &1"
   (GEN_TAC THEN GEN_REWRITE_TAC id [← TAUT (← q r"a <=> ~ ~a")] THEN
    PURE_ONCE_REWRITE_TAC [REAL_NOT_LE] THEN
    DISCH_THEN (MP_TAC o MATCH_MP REAL_LT1_POW2) THEN
    REWRITE_TAC [REAL_POW2_ABS] THEN
    DISCH_THEN (MP_TAC o ONCE_REWRITE_RULE [← GSYM REAL_SUB_LT]) THEN
    DISCH_THEN (MP_TAC o CONJ (← SPEC (← q "sin(x)") REAL_LE_SQUARE)) THEN
    REWRITE_TAC [← GSYM POW_2] THEN
    DISCH_THEN (MP_TAC o MATCH_MP REAL_LET_ADD) THEN
    REWRITE_TAC [real_sub, REAL_ADD_ASSOC, SIN_CIRCLE,
      REAL_ADD_ASSOC, SIN_CIRCLE, REAL_ADD_RINV, REAL_LT_REFL])

  let COS_BOUNDS ← prove
   r"!x. --(&1) <= cos(x) /\ cos(x) <= &1"
   (GEN_TAC THEN REWRITE_TAC [← GSYM ABS_BOUNDS, COS_BOUND])

  let SIN_COS_ADD ← prove
   r"!x y. ((sin(x + y) - ((sin(x) * cos(y)) + (cos(x) * sin(y)))) pow 2) +
         ((cos(x + y) - ((cos(x) * cos(y)) - (sin(x) * sin(y)))) pow 2) = &0"
   (REPEAT GEN_TAC THEN
    CONV_TAC (LAND_CONV (X_BETA_CONV (← q "x:real"))) THEN
    subgoalAt0 THENL
     [BETA_TAC THEN REWRITE_TAC [SIN_0, COS_0] THEN
      REWRITE_TAC [REAL_ADD_LID, REAL_MUL_LZERO, REAL_MUL_LID] THEN
      REWRITE_TAC [REAL_SUB_RZERO, REAL_SUB_REFL] THEN
      REWRITE_TAC [← numc "2", POW_0, REAL_ADD_LID],
      MATCH_MP_TAC DIFF_ISCONST_ALL THEN GEN_TAC THEN
      mpDiffConv THEN
      NUM_REDUCE_TAC THEN REWRITE_TAC [POW_1] THEN
      REWRITE_TAC [REAL_MUL_LZERO, REAL_ADD_RID, REAL_MUL_RID] THEN
      DISCH_THEN (MP_TAC o SPEC (← q "x:real")) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
      AP_TERM_TAC THEN REWRITE_TAC [← GSYM REAL_NEG_LMUL] THEN
      ONCE_REWRITE_TAC [← GSYM REAL_EQ_SUB_LADD] THEN
      REWRITE_TAC [REAL_SUB_LZERO, ← GSYM REAL_MUL_ASSOC] THEN
      REWRITE_TAC [REAL_NEG_RMUL] THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN BINOP_TAC THENL
       [REWRITE_TAC [real_sub, REAL_NEG_ADD, REAL_NEG_NEG, REAL_NEG_RMUL],
        REWRITE_TAC [← GSYM REAL_NEG_RMUL, ← GSYM real_sub]]])

  let SIN_COS_NEG ← prove
   r"!x. ((sin(--x) + (sin x)) pow 2) +
       ((cos(--x) - (cos x)) pow 2) = &0"
   (GEN_TAC THEN CONV_TAC (LAND_CONV (X_BETA_CONV (← q "x:real"))) THEN
    subgoalAt0 THENL
     [BETA_TAC THEN REWRITE_TAC [SIN_0, COS_0, REAL_NEG_0] THEN
      REWRITE_TAC [REAL_ADD_LID, REAL_SUB_REFL] THEN
      REWRITE_TAC [← numc "2", POW_0, REAL_ADD_LID],
      MATCH_MP_TAC DIFF_ISCONST_ALL THEN GEN_TAC THEN
      mpDiffConv THEN
      NUM_REDUCE_TAC THEN REWRITE_TAC [POW_1] THEN
      DISCH_THEN (MP_TAC o SPEC (← q "x:real")) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
      AP_TERM_TAC THEN REWRITE_TAC [← GSYM REAL_NEG_RMUL] THEN
      REWRITE_TAC [REAL_MUL_RID, real_sub, REAL_NEG_NEG, ← GSYM REAL_MUL_ASSOC] THEN
      ONCE_REWRITE_TAC [← GSYM REAL_EQ_SUB_LADD] THEN
      REWRITE_TAC [REAL_SUB_LZERO, REAL_NEG_RMUL] THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      REWRITE_TAC [← GSYM REAL_NEG_LMUL, REAL_NEG_RMUL] THEN AP_TERM_TAC THEN
      REWRITE_TAC [REAL_NEG_ADD, REAL_NEG_NEG]])

  let SIN_ADD ← prove
   r"!x y. sin(x + y) = (sin(x) * cos(y)) + (cos(x) * sin(y))"
   (REPEAT GEN_TAC THEN MP_TAC (← SPECL [← q "x:real", ← q "y:real"] SIN_COS_ADD) THEN
    REWRITE_TAC [POW_2, REAL_SUMSQ] THEN REWRITE_TAC [REAL_SUB_0] THEN
    DISCH_THEN (fun th => REWRITE_TAC [th]))

  let COS_ADD ← prove
   r"!x y. cos(x + y) = (cos(x) * cos(y)) - (sin(x) * sin(y))"
   (REPEAT GEN_TAC THEN MP_TAC (← SPECL [← q "x:real", ← q "y:real"] SIN_COS_ADD) THEN
    REWRITE_TAC [POW_2, REAL_SUMSQ] THEN REWRITE_TAC [REAL_SUB_0] THEN
    DISCH_THEN (fun th => REWRITE_TAC [th]))

  let SIN_NEG ← prove
   r"!x. sin(--x) = --(sin(x))"
   (GEN_TAC THEN MP_TAC (← SPEC (← q "x:real") SIN_COS_NEG) THEN
    REWRITE_TAC [POW_2, REAL_SUMSQ] THEN REWRITE_TAC [REAL_LNEG_UNIQ] THEN
    DISCH_THEN (fun th => REWRITE_TAC [th]))

  let COS_NEG ← prove
   r"!x. cos(--x) = cos(x)"
   (GEN_TAC THEN MP_TAC (← SPEC (← q "x:real") SIN_COS_NEG) THEN
    REWRITE_TAC [POW_2, REAL_SUMSQ] THEN REWRITE_TAC [REAL_SUB_0] THEN
    DISCH_THEN (fun th => REWRITE_TAC [th]))

  let SIN_DOUBLE ← prove
   r"!x. sin(&2 * x) = &2 * sin(x) * cos(x)"
   (GEN_TAC THEN REWRITE_TAC [← GSYM REAL_DOUBLE, SIN_ADD] THEN
    AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_MUL_SYM)

  let COS_DOUBLE ← prove
   r"!x. cos(&2 * x) = (cos(x) pow 2) - (sin(x) pow 2)"
   (GEN_TAC THEN REWRITE_TAC [← GSYM REAL_DOUBLE, COS_ADD, POW_2])

  let COS_ABS ← prove
   r"!x. cos(abs x) = cos(x)"
   (GEN_TAC THEN REWRITE_TAC [real_abs] THEN
    COND_CASES_TAC THEN REWRITE_TAC [COS_NEG])

  -- Show that there's a least positive x with cos(x) = 0; hence define pi

  let SIN_PAIRED ← prove
   r"!x. (\n. (((--(&1)) pow n) / &(FACT((2 * n) + 1)))
         * (x pow ((2 * n) + 1))) sums (sin x)"
   (GEN_TAC THEN MP_TAC (← SPEC (← q "x:real") SIN_CONVERGES) THEN
    DISCH_THEN (MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
    DISCH_THEN (MP_TAC o MATCH_MP SER_PAIR) THEN REWRITE_TAC [← GSYM sin] THEN
    BETA_TAC THEN REWRITE_TAC [SUM_2] THEN BETA_TAC THEN
    REWRITE_TAC [← GSYM ADD1, EVEN_DOUBLE,
                ← REWRITE_RULE [← GSYM NOT_EVEN] ODD_DOUBLE] THEN
    REWRITE_TAC [REAL_MUL_LZERO, REAL_ADD_LID, SUC_SUB1, MULT_DIV_2])

  let SIN_POS ← prove
   r"!x. &0 < x /\ x < &2 ==> &0 < sin(x)"
   (← do
    let sinsum ← SYM (← MATCH_MP SUM_UNIQ (← SPEC (← q "x:real") SIN_PAIRED))
    let z ← q r"&0"
    let s00 ← q "sum(0,0)"
    let amp ← q "&"
    pure (GEN_TAC THEN STRIP_TAC THEN MP_TAC (← SPEC (← q "x:real") SIN_PAIRED) THEN
      DISCH_THEN (MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
      DISCH_THEN (MP_TAC o MATCH_MP SER_PAIR) THEN
      REWRITE_TAC [sinsum] THEN
      REWRITE_TAC [SUM_2] THEN BETA_TAC THEN REWRITE_TAC [← GSYM ADD1] THEN
      REWRITE_TAC [pow, ← GSYM REAL_NEG_MINUS1, POW_MINUS1] THEN
      REWRITE_TAC [real_div, ← GSYM REAL_NEG_LMUL, ← GSYM real_sub] THEN
      REWRITE_TAC [REAL_MUL_LID] THEN REWRITE_TAC [ADD1] THEN DISCH_TAC THEN
      FIRST_ASSUM (SUBST1_TAC o MATCH_MP SUM_UNIQ) THEN
      (fun gl => ExceptT.run do
        let mkEq ← ExceptT.mk (mk_eq : IO _)
        let t ← liftExcept (do mkEq (z, ← mk_comb s00 (← rand (← rand gl.2))))
        ExceptT.mk (SUBGOAL_THEN t SUBST1_TAC gl)) THENL [REWRITE_TAC [sum], ALL_TAC] THEN
      MATCH_MP_TAC SER_POS_LT THEN
      FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP SUM_SUMMABLE th])) THEN
      X_GEN_TAC (← q "n:num") THEN DISCH_THEN (fun _ => ALL_TAC) THEN BETA_TAC THEN
      REWRITE_TAC [← GSYM ADD1, MULT_CLAUSES] THEN
      REWRITE_TAC [← numc "2", ADD_CLAUSES, pow, FACT, ← GSYM REAL_MUL] THEN
      REWRITE_TAC [← SYM (← numc "2")] THEN
      REWRITE_TAC [← numc "1", ADD_CLAUSES, pow, FACT, ← GSYM REAL_MUL] THEN
      REWRITE_TAC [REAL_SUB_LT] THEN ONCE_REWRITE_TAC [← GSYM pow] THEN
      REWRITE_TAC [REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LT_RMUL_IMP THEN CONJ_TAC THENL
       [ALL_TAC, MATCH_MP_TAC POW_POS_LT THEN ASM_REWRITE_TAC []] THEN
      REWRITE_TAC [← GSYM REAL_MUL_ASSOC, ← GSYM POW_2] THEN
      SUBGOAL_THEN (← q r"!n. &0 < &(SUC n)") ASSUME_TAC THENL
       [GEN_TAC THEN REWRITE_TAC [REAL_LT, LT_0], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"!n. &0 < &(FACT n)") ASSUME_TAC THENL
       [GEN_TAC THEN REWRITE_TAC [REAL_LT, FACT_LT], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"!n. ~(&(SUC n) = &0)") ASSUME_TAC THENL
       [GEN_TAC THEN REWRITE_TAC [REAL_INJ, NOT_SUC], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"!n. ~(&(FACT n) = &0)") ASSUME_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
        REWRITE_TAC [REAL_LT, FACT_LT], ALL_TAC] THEN
      REPEAT (IMP_SUBST_TAC REAL_INV_MUL_WEAK THEN ASM_REWRITE_TAC [REAL_ENTIRE]) THEN
      REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN
      ONCE_REWRITE_TAC [← AC REAL_MUL_AC
        (← q r"a * b * c * d * e = (a * b * e) * (c * d)")] THEN
      GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LT_RMUL_IMP THEN CONJ_TAC THENL
       [ALL_TAC, MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN
        MATCH_MP_TAC REAL_INV_POS THEN ASM_REWRITE_TAC []] THEN
      REWRITE_TAC [REAL_MUL_ASSOC] THEN
      IMP_SUBST_TAC _invMulSym THEN
      ASM_REWRITE_TAC [REAL_ENTIRE] THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
      REWRITE_TAC [← GSYM real_div] THEN MATCH_MP_TAC REAL_LT_1 THEN
      REWRITE_TAC [POW_2] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC,
        MATCH_MP_TAC REAL_LT_MUL2_ALT THEN REPEAT CONJ_TAC] THEN
      TRY (MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC [] THEN NO_TAC) THENL
       [(fun gl => ExceptT.run do
          let t ← liftExcept (do mk_comb amp (← funpow 3 (fun (m : Except String term) => do
            rand (← m)) (pure gl.2)))
          ExceptT.mk ((MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC t) gl)) THEN
        REWRITE_TAC [REAL_LT, LESS_SUC_REFL], ALL_TAC] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q r"&2") THEN
      ASM_REWRITE_TAC [] THEN CONV_TAC (REDEPTH_CONV num_CONV) THEN
      REWRITE_TAC [REAL_LE, LE_SUC, LE_0]))

  let COS_PAIRED ← prove
   r"!x. (\n. (((--(&1)) pow n) / &(FACT(2 * n)))
         * (x pow (2 * n))) sums (cos x)"
   (GEN_TAC THEN MP_TAC (← SPEC (← q "x:real") COS_CONVERGES) THEN
    DISCH_THEN (MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
    DISCH_THEN (MP_TAC o MATCH_MP SER_PAIR) THEN REWRITE_TAC [← GSYM cos] THEN
    BETA_TAC THEN REWRITE_TAC [SUM_2] THEN BETA_TAC THEN
    REWRITE_TAC [← GSYM ADD1, EVEN_DOUBLE,
                ← REWRITE_RULE [← GSYM NOT_EVEN] ODD_DOUBLE] THEN
    REWRITE_TAC [REAL_MUL_LZERO, REAL_ADD_RID, MULT_DIV_2])

  let COS_2 ← prove
   r"cos(&2) < &0"
   (GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_NEG_NEG] THEN
    REWRITE_TAC [REAL_NEG_LT0] THEN MP_TAC (← SPEC (← q r"&2") COS_PAIRED) THEN
    DISCH_THEN (MP_TAC o MATCH_MP SER_NEG) THEN BETA_TAC THEN
    DISCH_TAC THEN FIRST_ASSUM (SUBST1_TAC o MATCH_MP SUM_UNIQ) THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC (← q r"sum(0,3) (\n. --((((--(&1)) pow n) / &(FACT(2 * n)))
                  * (&2 pow (2 * n))))") THEN CONJ_TAC THENL
     [REWRITE_TAC [← numc "3", sum, SUM_2] THEN BETA_TAC THEN
      REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES, pow, FACT] THEN
      REWRITE_TAC [REAL_MUL_RID, POW_1, POW_2, ← GSYM REAL_NEG_RMUL] THEN
      IMP_SUBST_TAC REAL_DIV_REFL THEN REWRITE_TAC [REAL_NEG_NEG, REAL_10] THEN
      NUM_REDUCE_TAC THEN REWRITE_TAC [← numc "4", ← numc "3", FACT, pow] THEN
      REWRITE_TAC [← SYM (← numc "4"), ← SYM (← numc "3")] THEN
      REWRITE_TAC [← numc "2", ← numc "1", FACT, pow] THEN
      REWRITE_TAC [← SYM (← numc "1"), ← SYM (← numc "2")] THEN
      REWRITE_TAC [REAL_MUL] THEN NUM_REDUCE_TAC THEN
      REWRITE_TAC [real_div, REAL_NEG_LMUL, REAL_NEG_NEG, REAL_MUL_LID] THEN
      REWRITE_TAC [← GSYM REAL_NEG_LMUL, REAL_ADD_ASSOC] THEN
      REWRITE_TAC [← GSYM real_sub, REAL_SUB_LT] THEN
      SUBGOAL_THEN (← q r"inv(&2) * &4 = &1 + &1") SUBST1_TAC THENL
       [MATCH_MP_TAC REAL_EQ_LMUL_IMP THEN EXISTS_TAC (← q r"&2") THEN
        REWRITE_TAC [REAL_INJ] THEN NUM_REDUCE_TAC THEN
        REWRITE_TAC [REAL_ADD, REAL_MUL] THEN NUM_REDUCE_TAC THEN
        REWRITE_TAC [REAL_MUL_ASSOC] THEN
        SUBGOAL_THEN (← q r"&2 * inv(&2) = &1") SUBST1_TAC THEN
        REWRITE_TAC [REAL_MUL_LID] THEN MATCH_MP_TAC REAL_MUL_RINV THEN
        REWRITE_TAC [REAL_INJ] THEN NUM_REDUCE_TAC,
        REWRITE_TAC [REAL_MUL_LID, REAL_ADD_ASSOC] THEN
        REWRITE_TAC [REAL_ADD_LINV, REAL_ADD_LID] THEN
        ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REWRITE_TAC [← GSYM real_div] THEN
        MATCH_MP_TAC REAL_LT_1 THEN REWRITE_TAC [REAL_LE, REAL_LT] THEN
        NUM_REDUCE_TAC], ALL_TAC] THEN
    MATCH_MP_TAC SER_POS_LT_PAIR THEN
    FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP SUM_SUMMABLE th])) THEN
    X_GEN_TAC (← q "d:num") THEN BETA_TAC THEN
    REWRITE_TAC [POW_ADD, POW_MINUS1, REAL_MUL_RID] THEN
    REWRITE_TAC [← numc "3", pow] THEN REWRITE_TAC [← SYM (← numc "3")] THEN
    REWRITE_TAC [POW_2, POW_1] THEN
    REWRITE_TAC [← GSYM REAL_NEG_MINUS1, REAL_NEG_NEG] THEN
    REWRITE_TAC [real_div, ← GSYM REAL_NEG_LMUL, ← GSYM REAL_NEG_RMUL] THEN
    REWRITE_TAC [REAL_MUL_LID, REAL_NEG_NEG] THEN
    REWRITE_TAC [← GSYM real_sub, REAL_SUB_LT] THEN
    REWRITE_TAC [← GSYM ADD1, ADD_CLAUSES, MULT_CLAUSES] THEN
    REWRITE_TAC [POW_ADD, REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LT_RMUL_IMP THEN CONJ_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [← numc "2", MULT_CLAUSES] THEN
      REWRITE_TAC [← numc "3", ADD_CLAUSES] THEN
      MATCH_MP_TAC POW_POS_LT THEN REWRITE_TAC [REAL_LT] THEN
      NUM_REDUCE_TAC] THEN
    REWRITE_TAC [← numc "2", ADD_CLAUSES, FACT] THEN
    REWRITE_TAC [← SYM (← numc "2")] THEN
    REWRITE_TAC [← numc "1", ADD_CLAUSES, FACT] THEN
    REWRITE_TAC [← SYM (← numc "1")] THEN
    SUBGOAL_THEN (← q r"!n. &0 < &(SUC n)") ASSUME_TAC THENL
     [GEN_TAC THEN REWRITE_TAC [REAL_LT, LT_0], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!n. &0 < &(FACT n)") ASSUME_TAC THENL
     [GEN_TAC THEN REWRITE_TAC [REAL_LT, FACT_LT], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!n. ~(&(SUC n) = &0)") ASSUME_TAC THENL
     [GEN_TAC THEN REWRITE_TAC [REAL_INJ, NOT_SUC], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!n. ~(&(FACT n) = &0)") ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
      REWRITE_TAC [REAL_LT, FACT_LT], ALL_TAC] THEN
    REWRITE_TAC [← GSYM REAL_MUL] THEN
    REPEAT (IMP_SUBST_TAC REAL_INV_MUL_WEAK THEN ASM_REWRITE_TAC [REAL_ENTIRE]) THEN
    REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC [← AC REAL_MUL_AC
      (← q r"a * b * c * d = (a * b * d) * c")] THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LT_RMUL_IMP THEN CONJ_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC REAL_INV_POS THEN REWRITE_TAC [REAL_LT, FACT_LT]] THEN
    REWRITE_TAC [REAL_MUL_ASSOC] THEN
    IMP_SUBST_TAC _invMulSym THEN
    ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    REWRITE_TAC [← GSYM real_div] THEN MATCH_MP_TAC REAL_LT_1 THEN
    REWRITE_TAC [POW_2, REAL_MUL, REAL_LE, REAL_LT] THEN NUM_REDUCE_TAC THEN
    REWRITE_TAC [← numc "4", ← numc "3", MULT_CLAUSES, ADD_CLAUSES] THEN
    REWRITE_TAC [LT_SUC] THEN
    REWRITE_TAC [← numc "2", ADD_CLAUSES, MULT_CLAUSES] THEN
    REWRITE_TAC [← numc "1", LT_SUC, LT_0])

  let COS_ISZERO ← prove
   r"?!x. &0 <= x /\ x <= &2 /\ (cos x = &0)"
   (← do
    let dc ← SPEC (← q "x:real") DIFF_COS
    let _cosT ← q "cos"
    pure (REWRITE_TAC [HolBase.B.EXISTS_UNIQUE_DEF] THEN BETA_TAC THEN
      (fun gl => ExceptT.run do
        let t ← match conjuncts gl.2 with
          | t :: _ => pure t
          | [] => throw "hd"
        ExceptT.mk (SUBGOAL_THEN t ASSUME_TAC gl)) THENL
       [MATCH_MP_TAC IVT2 THEN REPEAT CONJ_TAC THENL
         [REWRITE_TAC [REAL_LE, LE_0],
          MATCH_MP_TAC REAL_LT_IMP_LE THEN ACCEPT_TAC COS_2,
          REWRITE_TAC [COS_0, REAL_LE_01],
          X_GEN_TAC (← q "x:real") THEN DISCH_THEN (fun _ => ALL_TAC) THEN
          MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC (← q "--(sin x)") THEN
          REWRITE_TAC [DIFF_COS]],
        ASM_REWRITE_TAC [] THEN BETA_TAC THEN
        MAP_EVERY X_GEN_TAC [← q "x1:real", ← q "x2:real"] THEN
        GEN_REWRITE_TAC id [← TAUT (← q r"a <=> ~ ~a")] THEN
        PURE_REWRITE_TAC [NOT_IMP] THEN REWRITE_TAC [] THEN STRIP_TAC THEN
        MP_TAC (← SPECL [← q "x1:real", ← q "x2:real"] REAL_LT_TOTAL) THEN
        SUBGOAL_THEN (← q r"(!x. cos differentiable x) /\
                      (!x. cos contl x)") STRIP_ASSUME_TAC THENL
         [CONJ_TAC THEN GEN_TAC THENL
           [REWRITE_TAC [differentiable], MATCH_MP_TAC DIFF_CONT] THEN
          EXISTS_TAC (← q "--(sin x)") THEN REWRITE_TAC [DIFF_COS], ALL_TAC] THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN DISJ_CASES_TAC THENL
         [MP_TAC (← SPECL [_cosT, ← q "x1:real", ← q "x2:real"] ROLLE),
          MP_TAC (← SPECL [_cosT, ← q "x2:real", ← q "x1:real"] ROLLE)] THEN
        ASM_REWRITE_TAC [] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "x:real") MP_TAC) THEN REWRITE_TAC [CONJ_ASSOC] THEN
        DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
        DISCH_THEN (MP_TAC o CONJ dc) THEN
        DISCH_THEN (MP_TAC o MATCH_MP DIFF_UNIQ) THEN
        REWRITE_TAC [REAL_NEG_EQ0] THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
        MATCH_MP_TAC SIN_POS THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q "x1:real") THEN
            ASM_REWRITE_TAC [],
            MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q "x2:real") THEN
            ASM_REWRITE_TAC []],
          CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q "x2:real") THEN
            ASM_REWRITE_TAC [],
            MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q "x1:real") THEN
            ASM_REWRITE_TAC []]]]))

  let pi ← new_definition
   r"pi = &2 * @x. &0 <= x /\ x <= &2 /\ (cos x = &0)"

  -- @@RETURN BEGIN
  return { SIN_0, COS_0, SIN_CIRCLE, SIN_BOUND, SIN_BOUNDS, COS_BOUND, COS_BOUNDS,
           SIN_COS_ADD, SIN_COS_NEG, SIN_ADD, COS_ADD, SIN_NEG, COS_NEG, SIN_DOUBLE,
           COS_DOUBLE, COS_ABS, SIN_PAIRED, SIN_POS, COS_PAIRED, COS_2, COS_ISZERO, pi }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Periodicity and related properties of the trig functions.                 -/
/- (transc.ml 2196-2564)                                                     -/
/- ------------------------------------------------------------------------- -/

structure Trig2 where
  -- @@FIELDS
  PI2 : thm
  COS_PI2 : thm
  PI2_BOUNDS : thm
  PI_POS : thm
  SIN_PI2 : thm
  COS_PI : thm
  SIN_PI : thm
  SIN_COS : thm
  COS_SIN : thm
  SIN_PERIODIC_PI : thm
  COS_PERIODIC_PI : thm
  SIN_PERIODIC : thm
  COS_PERIODIC : thm
  COS_NPI : thm
  SIN_NPI : thm
  SIN_POS_PI2 : thm
  COS_POS_PI2 : thm
  COS_POS_PI : thm
  SIN_POS_PI : thm
  SIN_POS_PI_LE : thm
  COS_TOTAL : thm
  SIN_TOTAL : thm
  COS_ZERO_LEMMA : thm
  SIN_ZERO_LEMMA : thm
  COS_ZERO : thm
  SIN_ZERO : thm
  SIN_ZERO_PI : thm
  COS_ONE_2PI : thm
  deriving Inhabited

@[nospecialize]
def setupTrig2 [HolBase] (D : TranscDeps) (BDefs : Defs) (BTrig1 : Trig1) (ACompat : HolLibrary.Analysis.Compat) (ATactics : HolLibrary.Analysis.Tactics) (AReals1 : HolLibrary.Analysis.Reals1) (AReals2 : HolLibrary.Analysis.Reals2) (AReals3 : HolLibrary.Analysis.Reals3) (APow : HolLibrary.Analysis.Pow) (ALims : HolLibrary.Analysis.Lims) (ADiffs : HolLibrary.Analysis.Diffs) (AMvt : HolLibrary.Analysis.Mvt) :
    ExceptT String IO Trig2 := do
  -- @@SCOPE BEGIN
  let { INDUCT_TAC, MESON_TAC, NUM_REDUCE_TAC, REAL_ARITH, REAL_RAT_REDUCE_CONV, .. } := D
  let { ADD1, ADD_ASSOC, ADD_CLAUSES, ADD_SYM, ARITH, ARITH_EVEN, EVEN_DOUBLE,
        EVEN_EXISTS, EVEN_MULT, LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM, MULT_CLAUSES,
        MULT_SYM, NOT_EVEN, NOT_IMP, NOT_ODD, ODD_DOUBLE, ODD_EXISTS, REAL_ADD_ASSOC,
        REAL_ADD_LID, REAL_ADD_LINV, REAL_ADD_RID, .. } := D.core1
  let { REAL_ADD_SUB, REAL_ADD_SYM, REAL_DIFFSQ, REAL_DIV_LMUL, REAL_DIV_RMUL,
        REAL_ENTIRE, REAL_EQ_MUL_RCANCEL, REAL_EQ_NEG2, REAL_EQ_SUB_LADD,
        REAL_EQ_SUB_RADD, REAL_LET_TRANS, REAL_LE_01, REAL_LE_ADDR, REAL_LT_REFL,
        REAL_LT_TOTAL, REAL_LT_TRANS, REAL_MUL_AC, REAL_MUL_ASSOC, REAL_MUL_LID,
        REAL_MUL_LINV, REAL_MUL_SYM, REAL_OF_NUM_EQ, REAL_OF_NUM_MUL, REAL_POW_2,
        REAL_POW_NEG, REAL_POW_ONE, SWAP_EXISTS_THM, UNWIND_THM2, real_div, real_sub, .. } := D.core2
  let { DIFF_COS, .. } := BDefs
  let { COS_0, COS_2, COS_ADD, COS_ISZERO, COS_NEG, SIN_0, SIN_ADD, SIN_CIRCLE,
        SIN_NEG, SIN_POS, pi, .. } := BTrig1
  let { EXISTS_UNIQUE_CONV, .. } := ACompat
  let { IMP_SUBST_TAC, .. } := ATactics
  let { REAL_10, REAL_EQ_RADD, REAL_LE_LT, REAL_LE_REFL, REAL_LE_TOTAL, REAL_LE_TRANS,
        REAL_LNEG_UNIQ, REAL_LTE_TRANS, REAL_LT_01, REAL_LT_ADD, REAL_LT_GT,
        REAL_LT_IMP_LE, REAL_LT_LE, REAL_MUL_LZERO, REAL_MUL_RID, REAL_MUL_RZERO,
        REAL_NEG_GE0, REAL_NEG_LE0, REAL_NEG_LT0, REAL_NEG_NEG, REAL_NEG_RMUL,
        REAL_NOT_LT, REAL_RDISTRIB, REAL_SUB_ADD, .. } := AReals1
  let { REAL_ADD, REAL_DOUBLE, REAL_INJ, REAL_LT_HALF1, REAL_LT_HALF2, REAL_LT_IMP_NE,
        REAL_MUL, REAL_NEG_0, REAL_NEG_EQ, REAL_NEG_EQ0, REAL_NEG_SUB, REAL_SUB_0,
        REAL_SUB_LE, REAL_SUB_REFL, .. } := AReals2
  let { REAL_EQ_NEG, REAL_HALF_DOUBLE, REAL_LE_NEG2, REAL_LE_SUB_LADD,
        REAL_LE_SUB_RADD, REAL_LT_IMP_NZ, REAL_LT_NEG2, REAL_LT_SUB_LADD,
        REAL_LT_SUB_RADD, REAL_SUB_LZERO, REAL_SUB_RZERO, .. } := AReals3
  let { POW_2, REAL_ARCH_LEAST, pow, .. } := APow
  let { DIFF_CONT, DIFF_UNIQ, differentiable, .. } := ALims
  let { IVT2, .. } := ADiffs
  let { ROLLE, .. } := AMvt
  -- @@SCOPE END
  -- `W(C SUBGOAL_THEN ttac o funpow 2 (fst o dest_imp) o snd)`
  let subgoalAnte2 (ttac : thm_tactic) : tactic := fun gl => ExceptT.run do
    let t ← liftExcept (funpow 2 (fun (m : Except String term) => do
      pure (← dest_imp (← m)).1) (pure gl.2))
    ExceptT.mk (SUBGOAL_THEN t ttac gl)
  let _cosT ← q "cos"

  let PI2 ← prove
   r"pi / &2 = @x. &0 <= x /\ x <= &2 /\ (cos(x) = &0)"
   (REWRITE_TAC [pi, real_div] THEN
    ONCE_REWRITE_TAC [← AC REAL_MUL_AC
      (← q r"(a * b) * c = (c * a) * b")] THEN
    IMP_SUBST_TAC REAL_MUL_LINV THEN REWRITE_TAC [REAL_INJ] THEN
    NUM_REDUCE_TAC THEN REWRITE_TAC [REAL_MUL_LID])

  let COS_PI2 ← prove
   r"cos(pi / &2) = &0"
   (MP_TAC (← SELECT_RULE (← EXISTENCE COS_ISZERO)) THEN
    REWRITE_TAC [← GSYM PI2] THEN
    DISCH_THEN (fun th => REWRITE_TAC [th]))

  let PI2_BOUNDS ← prove
   r"&0 < (pi / &2) /\ (pi / &2) < &2"
   (MP_TAC (← SELECT_RULE (← EXISTENCE COS_ISZERO)) THEN
    REWRITE_TAC [← GSYM PI2] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC [REAL_LT_LE] THEN CONJ_TAC THENL
     [DISCH_TAC THEN MP_TAC COS_0 THEN ASM_REWRITE_TAC [] THEN
      FIRST_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC [← GSYM REAL_10],
      DISCH_TAC THEN MP_TAC COS_PI2 THEN FIRST_ASSUM SUBST1_TAC THEN
      REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
      MATCH_ACCEPT_TAC COS_2])

  let PI_POS ← prove
   r"&0 < pi"
   (GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_HALF_DOUBLE] THEN
    MATCH_MP_TAC REAL_LT_ADD THEN REWRITE_TAC [PI2_BOUNDS])

  let SIN_PI2 ← prove
   r"sin(pi / &2) = &1"
   (MP_TAC (← SPEC (← q r"pi / &2") SIN_CIRCLE) THEN
    REWRITE_TAC [COS_PI2, POW_2, REAL_MUL_LZERO, REAL_ADD_RID] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← GSYM REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC [← GSYM REAL_SUB_0] THEN
    REWRITE_TAC [← GSYM REAL_DIFFSQ, REAL_ENTIRE] THEN
    DISCH_THEN DISJ_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    POP_ASSUM MP_TAC THEN CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN (fun _ => ALL_TAC) THEN
    REWRITE_TAC [REAL_LNEG_UNIQ] THEN DISCH_THEN (MP_TAC o AP_TERM (← q "(--)")) THEN
    REWRITE_TAC [REAL_NEG_NEG] THEN DISCH_TAC THEN
    MP_TAC REAL_LT_01 THEN POP_ASSUM (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LT_GT THEN
    REWRITE_TAC [REAL_NEG_LT0] THEN MATCH_MP_TAC SIN_POS THEN
    REWRITE_TAC [PI2_BOUNDS])

  let COS_PI ← prove
   r"cos(pi) = --(&1)"
   (MP_TAC (← SPECL [← q r"pi / &2", ← q r"pi / &2"] COS_ADD) THEN
    REWRITE_TAC [SIN_PI2, COS_PI2, REAL_MUL_LZERO, REAL_MUL_LID] THEN
    REWRITE_TAC [REAL_SUB_LZERO] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    AP_TERM_TAC THEN REWRITE_TAC [REAL_DOUBLE] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
    REWRITE_TAC [REAL_INJ] THEN NUM_REDUCE_TAC)

  let SIN_PI ← prove
   r"sin(pi) = &0"
   (MP_TAC (← SPECL [← q r"pi / &2", ← q r"pi / &2"] SIN_ADD) THEN
    REWRITE_TAC [COS_PI2, REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_ADD_LID] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
    REWRITE_TAC [REAL_DOUBLE] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC REAL_DIV_LMUL THEN
    REWRITE_TAC [REAL_INJ] THEN NUM_REDUCE_TAC)

  let SIN_COS ← prove
   r"!x. sin(x) = cos((pi / &2) - x)"
   (GEN_TAC THEN REWRITE_TAC [real_sub, COS_ADD] THEN
    REWRITE_TAC [SIN_PI2, COS_PI2, REAL_MUL_LZERO] THEN
    REWRITE_TAC [REAL_ADD_LID, REAL_MUL_LID] THEN
    REWRITE_TAC [SIN_NEG, REAL_NEG_NEG])

  let COS_SIN ← prove
   r"!x. cos(x) = sin((pi / &2) - x)"
   (GEN_TAC THEN REWRITE_TAC [real_sub, SIN_ADD] THEN
    REWRITE_TAC [SIN_PI2, COS_PI2, REAL_MUL_LZERO] THEN
    REWRITE_TAC [REAL_MUL_LID, REAL_ADD_RID] THEN
    REWRITE_TAC [COS_NEG])

  let SIN_PERIODIC_PI ← prove
   r"!x. sin(x + pi) = --(sin(x))"
   (GEN_TAC THEN REWRITE_TAC [SIN_ADD, SIN_PI, COS_PI] THEN
    REWRITE_TAC [REAL_MUL_RZERO, REAL_ADD_RID, ← GSYM REAL_NEG_RMUL] THEN
    REWRITE_TAC [REAL_MUL_RID])

  let COS_PERIODIC_PI ← prove
   r"!x. cos(x + pi) = --(cos(x))"
   (GEN_TAC THEN REWRITE_TAC [COS_ADD, SIN_PI, COS_PI] THEN
    REWRITE_TAC [REAL_MUL_RZERO, REAL_SUB_RZERO, ← GSYM REAL_NEG_RMUL] THEN
    REWRITE_TAC [REAL_MUL_RID])

  let SIN_PERIODIC ← prove
   r"!x. sin(x + (&2 * pi)) = sin(x)"
   (GEN_TAC THEN REWRITE_TAC [← GSYM REAL_DOUBLE, REAL_ADD_ASSOC] THEN
    REWRITE_TAC [SIN_PERIODIC_PI, REAL_NEG_NEG])

  let COS_PERIODIC ← prove
   r"!x. cos(x + (&2 * pi)) = cos(x)"
   (GEN_TAC THEN REWRITE_TAC [← GSYM REAL_DOUBLE, REAL_ADD_ASSOC] THEN
    REWRITE_TAC [COS_PERIODIC_PI, REAL_NEG_NEG])

  let COS_NPI ← prove
   r"!n. cos(&n * pi) = --(&1) pow n"
   (INDUCT_TAC THEN REWRITE_TAC [REAL_MUL_LZERO, COS_0, pow] THEN
    REWRITE_TAC [ADD1, ← GSYM REAL_ADD, REAL_RDISTRIB, COS_ADD] THEN
    REWRITE_TAC [REAL_MUL_LID, SIN_PI, REAL_MUL_RZERO, REAL_SUB_RZERO] THEN
    ASM_REWRITE_TAC [COS_PI] THEN
    MATCH_ACCEPT_TAC REAL_MUL_SYM)

  let SIN_NPI ← prove
   r"!n. sin(&n * pi) = &0"
   (INDUCT_TAC THEN REWRITE_TAC [REAL_MUL_LZERO, SIN_0, pow] THEN
    REWRITE_TAC [ADD1, ← GSYM REAL_ADD, REAL_RDISTRIB, SIN_ADD] THEN
    REWRITE_TAC [REAL_MUL_LID, SIN_PI, REAL_MUL_RZERO, REAL_ADD_RID] THEN
    ASM_REWRITE_TAC [REAL_MUL_LZERO])

  let SIN_POS_PI2 ← prove
   r"!x. &0 < x /\ x < pi / &2 ==> &0 < sin(x)"
   (GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SIN_POS THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC (← q r"pi / &2") THEN ASM_REWRITE_TAC [PI2_BOUNDS])

  let COS_POS_PI2 ← prove
   r"!x. &0 < x /\ x < pi / &2 ==> &0 < cos(x)"
   (GEN_TAC THEN STRIP_TAC THEN
    GEN_REWRITE_TAC id [← TAUT (← q r"a <=> ~ ~a")] THEN
    PURE_REWRITE_TAC [REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC (← SPECL [_cosT, ← q r"&0", ← q "x:real", ← q r"&0"] IVT2) THEN
    ASM_REWRITE_TAC [COS_0, REAL_LE_01, NOT_IMP] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC [],
      X_GEN_TAC (← q "z:real") THEN DISCH_THEN (fun _ => ALL_TAC) THEN
      MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC (← q "--(sin z)") THEN
      REWRITE_TAC [DIFF_COS],
      DISCH_THEN (X_CHOOSE_TAC (← q "z:real")) THEN
      MP_TAC (← CONJUNCT2 (← CONV_RULE EXISTS_UNIQUE_CONV COS_ISZERO)) THEN
      DISCH_THEN (MP_TAC o SPECL [← q "z:real", ← q r"pi / &2"]) THEN
      ASM_REWRITE_TAC [COS_PI2] THEN REWRITE_TAC [NOT_IMP] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "x:real") THEN
        ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC (← q r"pi / &2") THEN ASM_REWRITE_TAC [] THEN CONJ_TAC,
        ALL_TAC,
        ALL_TAC,
        DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"x < pi / &2") THEN
        ASM_REWRITE_TAC [REAL_NOT_LT]] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC [PI2_BOUNDS]])

  let COS_POS_PI ← prove
   r"!x. --(pi / &2) < x /\ x < pi / &2 ==> &0 < cos(x)"
   (GEN_TAC THEN STRIP_TAC THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
          (← SPECL [← q "x:real", ← q r"&0"] REAL_LT_TOTAL) THENL
     [ASM_REWRITE_TAC [COS_0, REAL_LT_01],
      ONCE_REWRITE_TAC [← GSYM COS_NEG] THEN MATCH_MP_TAC COS_POS_PI2 THEN
      ONCE_REWRITE_TAC [← GSYM REAL_NEG_LT0] THEN ASM_REWRITE_TAC [REAL_NEG_NEG] THEN
      ONCE_REWRITE_TAC [← GSYM REAL_LT_NEG2] THEN ASM_REWRITE_TAC [REAL_NEG_NEG],
      MATCH_MP_TAC COS_POS_PI2 THEN ASM_REWRITE_TAC []])

  let SIN_POS_PI ← prove
   r"!x. &0 < x /\ x < pi ==> &0 < sin(x)"
   (GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC [SIN_COS] THEN ONCE_REWRITE_TAC [← GSYM COS_NEG] THEN
    REWRITE_TAC [REAL_NEG_SUB] THEN
    MATCH_MP_TAC COS_POS_PI THEN
    REWRITE_TAC [REAL_LT_SUB_LADD, REAL_LT_SUB_RADD] THEN
    ASM_REWRITE_TAC [REAL_HALF_DOUBLE, REAL_ADD_LINV])

  let SIN_POS_PI_LE ← prove
   r"!x. &0 <= x /\ x <= pi ==> &0 <= sin(x)"
   (REWRITE_TAC [REAL_LE_LT] THEN
    MESON_TAC [SIN_POS_PI, SIN_PI, SIN_0, REAL_LE_REFL])

  let COS_TOTAL ← prove
   r"!y. --(&1) <= y /\ y <= &1 ==> ?!x. &0 <= x /\ x <= pi /\ (cos(x) = y)"
   (← do
    let ltPi ← MATCH_MP REAL_LT_IMP_LE PI_POS
    let dc ← SPEC (← q "x:real") DIFF_COS
    pure (GEN_TAC THEN STRIP_TAC THEN
      CONV_TAC EXISTS_UNIQUE_CONV THEN CONJ_TAC THENL
       [MATCH_MP_TAC IVT2 THEN ASM_REWRITE_TAC [COS_0, COS_PI] THEN
        REWRITE_TAC [ltPi] THEN
        GEN_TAC THEN DISCH_THEN (fun _ => ALL_TAC) THEN
        MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC (← q "--(sin x)") THEN
        REWRITE_TAC [DIFF_COS],
        MAP_EVERY X_GEN_TAC [← q "x1:real", ← q "x2:real"] THEN STRIP_TAC THEN
        REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
             (← SPECL [← q "x1:real", ← q "x2:real"] REAL_LT_TOTAL) THENL
         [FIRST_ASSUM ACCEPT_TAC,
          MP_TAC (← SPECL [_cosT, ← q "x1:real", ← q "x2:real"] ROLLE),
          MP_TAC (← SPECL [_cosT, ← q "x2:real", ← q "x1:real"] ROLLE)]] THEN
      ASM_REWRITE_TAC [] THEN
      (subgoalAnte2 (fun t => REWRITE_TAC [t]) THENL
        [CONJ_TAC THEN X_GEN_TAC (← q "x:real") THEN DISCH_THEN (fun _ => ALL_TAC) THEN
         TRY (MATCH_MP_TAC DIFF_CONT) THEN REWRITE_TAC [differentiable] THEN
         EXISTS_TAC (← q "--(sin x)") THEN REWRITE_TAC [DIFF_COS], ALL_TAC]) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "x:real") STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC (← q r"(cos diffl &0)(x)") THEN
      DISCH_THEN (MP_TAC o CONJ dc) THEN
      DISCH_THEN (MP_TAC o MATCH_MP DIFF_UNIQ) THEN
      REWRITE_TAC [REAL_NEG_EQ0] THEN DISCH_TAC THEN
      MP_TAC (← SPEC (← q "x:real") SIN_POS_PI) THEN
      ASM_REWRITE_TAC [REAL_LT_REFL] THEN
      CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN (fun _ => ALL_TAC) THEN
      REWRITE_TAC [] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q "x1:real"),
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q "x2:real"),
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q "x2:real"),
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q "x1:real")] THEN
      ASM_REWRITE_TAC []))

  let SIN_TOTAL ← prove
   r"!y. --(&1) <= y /\ y <= &1 ==>
        ?!x.  --(pi / &2) <= x /\ x <= pi / &2 /\ (sin(x) = y)"
   (GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"!x. --(pi / &2) <= x /\ x <= pi / &2 /\ (sin(x) = y) <=>
      &0 <= (x + pi / &2) /\ (x + pi / &2) <= pi /\ (cos(x + pi / &2) = --y)")
    (fun th => REWRITE_TAC [th]) THENL
     [GEN_TAC THEN REWRITE_TAC [COS_ADD, SIN_PI2, COS_PI2] THEN
      REWRITE_TAC [REAL_MUL_RZERO, REAL_MUL_RZERO, REAL_MUL_RID] THEN
      REWRITE_TAC [REAL_SUB_LZERO] THEN
      REWRITE_TAC [← GSYM REAL_LE_SUB_RADD, ← GSYM REAL_LE_SUB_LADD] THEN
      REWRITE_TAC [REAL_SUB_LZERO] THEN AP_TERM_TAC THEN
      REWRITE_TAC [REAL_EQ_NEG] THEN AP_THM_TAC THEN
      REPEAT AP_TERM_TAC THEN
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [← GSYM REAL_HALF_DOUBLE] THEN
      REWRITE_TAC [REAL_ADD_SUB], ALL_TAC] THEN
    MP_TAC (← SPEC (← q "--y") COS_TOTAL) THEN ASM_REWRITE_TAC [REAL_LE_NEG2] THEN
    ONCE_REWRITE_TAC [← GSYM REAL_LE_NEG2] THEN ASM_REWRITE_TAC [REAL_NEG_NEG] THEN
    REWRITE_TAC [REAL_LE_NEG2] THEN
    CONV_TAC (ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV) THEN
    DISCH_THEN (fun th => CONJ_TAC THEN MP_TAC th) THENL
     [DISCH_THEN (X_CHOOSE_TAC (← q "x:real") o CONJUNCT1) THEN
      EXISTS_TAC (← q r"x - pi / &2") THEN ASM_REWRITE_TAC [REAL_SUB_ADD],
      POP_ASSUM (fun _ => ALL_TAC) THEN DISCH_THEN (ASSUME_TAC o CONJUNCT2) THEN
      REPEAT GEN_TAC THEN
      DISCH_THEN (fun th => FIRST_ASSUM (MP_TAC o (fun a => MATCH_MP a th))) THEN
      REWRITE_TAC [REAL_EQ_RADD]])

  let COS_ZERO_LEMMA ← prove
   r"!x. &0 <= x /\ (cos(x) = &0) ==>
      ?n. ~EVEN n /\ (x = &n * (pi / &2))"
   (GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← SPEC (← q "x:real") (← MATCH_MP REAL_ARCH_LEAST PI_POS)) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "n:num") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"&0 <= x - &n * pi /\ (x - &n * pi) <= pi /\
                  (cos(x - &n * pi) = &0)") ASSUME_TAC THENL
     [ASM_REWRITE_TAC [REAL_SUB_LE] THEN
      REWRITE_TAC [REAL_LE_SUB_RADD] THEN
      REWRITE_TAC [real_sub, COS_ADD, SIN_NEG, COS_NEG, SIN_NPI, COS_NPI] THEN
      ASM_REWRITE_TAC [REAL_MUL_LZERO, REAL_ADD_LID] THEN
      REWRITE_TAC [REAL_NEG_RMUL, REAL_NEG_NEG, REAL_MUL_RZERO] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN UNDISCH_TAC (← q r"x < &(SUC n) * pi") THEN
      REWRITE_TAC [ADD1] THEN ONCE_REWRITE_TAC [ADD_SYM] THEN
      REWRITE_TAC [← GSYM REAL_ADD, REAL_RDISTRIB, REAL_MUL_LID],
      MP_TAC (← SPEC (← q r"&0") COS_TOTAL) THEN
      REWRITE_TAC [REAL_LE_01, REAL_NEG_LE0] THEN
      DISCH_THEN (MP_TAC o CONV_RULE EXISTS_UNIQUE_CONV) THEN
      DISCH_THEN (MP_TAC o SPECL [← q r"x - &n * pi", ← q r"pi / &2"] o CONJUNCT2) THEN
      ASM_REWRITE_TAC [COS_PI2] THEN
      subgoalAnte2 MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN MP_TAC PI2_BOUNDS THEN
        REWRITE_TAC [REAL_LT_HALF1, REAL_LT_HALF2] THEN DISCH_TAC THEN
        ASM_REWRITE_TAC [],
        DISCH_THEN (fun th => REWRITE_TAC [th])] THEN
      REWRITE_TAC [REAL_EQ_SUB_RADD] THEN DISCH_TAC THEN
      EXISTS_TAC (← q "SUC(2 * n)") THEN
      REWRITE_TAC [← GSYM NOT_ODD, ODD_DOUBLE] THEN
      REWRITE_TAC [ADD1, ← GSYM REAL_ADD, ← GSYM REAL_MUL] THEN
      REWRITE_TAC [REAL_RDISTRIB, REAL_MUL_LID] THEN
      ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN ASM_REWRITE_TAC [] THEN
      AP_TERM_TAC THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
      REWRITE_TAC [REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
      REWRITE_TAC [REAL_INJ] THEN NUM_REDUCE_TAC])

  let SIN_ZERO_LEMMA ← prove
   r"!x. &0 <= x /\ (sin(x) = &0) ==>
        ?n. EVEN n /\ (x = &n * (pi / &2))"
   (GEN_TAC THEN DISCH_TAC THEN
    MP_TAC (← SPEC (← q r"x + pi / &2") COS_ZERO_LEMMA) THEN
    subgoalAnte2 MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "x:real") THEN
        ASM_REWRITE_TAC [REAL_LE_ADDR] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
        REWRITE_TAC [PI2_BOUNDS],
        ASM_REWRITE_TAC [COS_ADD, COS_PI2, REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
        MATCH_ACCEPT_TAC REAL_SUB_REFL],
      DISCH_THEN (fun th => REWRITE_TAC [th])] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "n:num") STRIP_ASSUME_TAC) THEN
    MP_TAC (← SPEC (← q "n:num") ODD_EXISTS) THEN ASM_REWRITE_TAC [← GSYM NOT_EVEN] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "m:num") SUBST_ALL_TAC) THEN
    EXISTS_TAC (← q "2 * m") THEN REWRITE_TAC [EVEN_DOUBLE] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [← GSYM REAL_EQ_SUB_LADD]) THEN
    FIRST_ASSUM SUBST1_TAC THEN
    REWRITE_TAC [ADD1, ← GSYM REAL_ADD, REAL_RDISTRIB, REAL_MUL_LID] THEN
    REWRITE_TAC [← ONCE_REWRITE_RULE [REAL_ADD_SYM] REAL_ADD_SUB])

  let COS_ZERO ← prove
   r"!x. (cos(x) = &0) <=> (?n. ~EVEN n /\ (x = &n * (pi / &2))) \/
                         (?n. ~EVEN n /\ (x = --(&n * (pi / &2))))"
   (GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN DISJ_CASES_TAC (← SPECL [← q r"&0", ← q "x:real"] REAL_LE_TOTAL) THENL
       [DISJ1_TAC THEN MATCH_MP_TAC COS_ZERO_LEMMA THEN ASM_REWRITE_TAC [],
        DISJ2_TAC THEN REWRITE_TAC [← GSYM REAL_NEG_EQ] THEN
        MATCH_MP_TAC COS_ZERO_LEMMA THEN ASM_REWRITE_TAC [COS_NEG] THEN
        ONCE_REWRITE_TAC [← GSYM REAL_LE_NEG2] THEN
        ASM_REWRITE_TAC [REAL_NEG_NEG, REAL_NEG_0]],
      DISCH_THEN (DISJ_CASES_THEN (X_CHOOSE_TAC (← q "n:num"))) THEN
      ASM_REWRITE_TAC [COS_NEG] THEN MP_TAC (← SPEC (← q "n:num") ODD_EXISTS) THEN
      ASM_REWRITE_TAC [← GSYM NOT_EVEN] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "m:num") SUBST1_TAC) THEN
      REWRITE_TAC [ADD1] THEN SPEC_TAC (← q "m:num", ← q "m:num") THEN INDUCT_TAC THEN
      REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES, REAL_MUL_LID, COS_PI2] THEN
      REWRITE_TAC [← GSYM ADD_ASSOC] THEN ONCE_REWRITE_TAC [← GSYM REAL_ADD] THEN
      REWRITE_TAC [REAL_RDISTRIB] THEN REWRITE_TAC [COS_ADD] THEN
      REWRITE_TAC [← GSYM REAL_DOUBLE, REAL_HALF_DOUBLE] THEN
      ASM_REWRITE_TAC [COS_PI, SIN_PI, REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
      REWRITE_TAC [REAL_SUB_RZERO]])

  let SIN_ZERO ← prove
   r"!x. (sin(x) = &0) <=> (?n. EVEN n /\ (x = &n * (pi / &2))) \/
                         (?n. EVEN n /\ (x = --(&n * (pi / &2))))"
   (GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN DISJ_CASES_TAC (← SPECL [← q r"&0", ← q "x:real"] REAL_LE_TOTAL) THENL
       [DISJ1_TAC THEN MATCH_MP_TAC SIN_ZERO_LEMMA THEN ASM_REWRITE_TAC [],
        DISJ2_TAC THEN REWRITE_TAC [← GSYM REAL_NEG_EQ] THEN
        MATCH_MP_TAC SIN_ZERO_LEMMA THEN
        ASM_REWRITE_TAC [SIN_NEG, REAL_NEG_0, REAL_NEG_GE0]],
      DISCH_THEN (DISJ_CASES_THEN (X_CHOOSE_TAC (← q "n:num"))) THEN
      ASM_REWRITE_TAC [SIN_NEG, REAL_NEG_EQ0] THEN
      MP_TAC (← SPEC (← q "n:num") EVEN_EXISTS) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "m:num") SUBST1_TAC) THEN
      REWRITE_TAC [← GSYM REAL_MUL] THEN
      ONCE_REWRITE_TAC [← AC REAL_MUL_AC
        (← q r"(a * b) * c = b * (a * c)")] THEN
      REWRITE_TAC [← GSYM REAL_DOUBLE, REAL_HALF_DOUBLE, SIN_NPI]])

  let SIN_ZERO_PI ← prove
   r"!x. (sin(x) = &0) <=> (?n. x = &n * pi) \/ (?n. x = --(&n * pi))"
   (GEN_TAC THEN REWRITE_TAC [SIN_ZERO, EVEN_EXISTS] THEN
    REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
    REWRITE_TAC [UNWIND_THM2] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN
    REWRITE_TAC [← GSYM REAL_OF_NUM_MUL] THEN
    SIMP_TAC [← GSYM REAL_MUL_ASSOC, REAL_DIV_LMUL, REAL_OF_NUM_EQ, ARITH])

  let COS_ONE_2PI ← prove
   r"!x. (cos(x) = &1) <=> (?n. x = &n * &2 * pi) \/ (?n. x = --(&n * &2 * pi))"
   (← do
    -- The later rule in the THEN chain is evaluated first.
    let t ← TAUT (← q r"(a ==> a') /\ (b ==> b') ==> (a \/ b ==> a' \/ b')")
    let ra ← REAL_ARITH (← q r"(x + &1 * &1 = &1) <=> (x = &0)")
    pure (REPEAT GEN_TAC THEN EQ_TAC THENL
     [ALL_TAC,
      STRIP_TAC THEN ASM_REWRITE_TAC [COS_NEG] THEN
      REWRITE_TAC [REAL_MUL_ASSOC, REAL_OF_NUM_MUL, COS_NPI] THEN
      REWRITE_TAC [REAL_POW_NEG, EVEN_MULT, ARITH_EVEN, REAL_POW_ONE]] THEN
    DISCH_TAC THEN MP_TAC (← SPEC (← q "x:real") SIN_CIRCLE) THEN
    ASM_REWRITE_TAC [REAL_POW_2, REAL_MUL_LZERO] THEN
    REWRITE_TAC [ra] THEN
    REWRITE_TAC [REAL_ENTIRE] THEN REWRITE_TAC [SIN_ZERO_PI] THEN
    MATCH_MP_TAC t THEN
    SIMP_TAC [LEFT_IMP_EXISTS_THM] THEN
    CONJ_TAC THEN X_GEN_TAC (← q "m:num") THEN DISCH_THEN SUBST_ALL_TAC THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [REAL_EQ_NEG2, COS_NEG] THEN
    REWRITE_TAC [COS_NPI, REAL_POW_NEG, REAL_POW_ONE] THEN
    REWRITE_TAC [REAL_MUL_ASSOC, REAL_EQ_MUL_RCANCEL] THEN
    SIMP_TAC [PI_POS, REAL_LT_IMP_NZ] THEN
    REWRITE_TAC [REAL_OF_NUM_EQ, REAL_OF_NUM_MUL] THEN
    ONCE_REWRITE_TAC [MULT_SYM] THEN REWRITE_TAC [← GSYM EVEN_EXISTS] THEN
    COND_CASES_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC []))

  -- @@RETURN BEGIN
  return { PI2, COS_PI2, PI2_BOUNDS, PI_POS, SIN_PI2, COS_PI, SIN_PI, SIN_COS, COS_SIN,
           SIN_PERIODIC_PI, COS_PERIODIC_PI, SIN_PERIODIC, COS_PERIODIC, COS_NPI,
           SIN_NPI, SIN_POS_PI2, COS_POS_PI2, COS_POS_PI, SIN_POS_PI, SIN_POS_PI_LE,
           COS_TOTAL, SIN_TOTAL, COS_ZERO_LEMMA, SIN_ZERO_LEMMA, COS_ZERO, SIN_ZERO,
           SIN_ZERO_PI, COS_ONE_2PI }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Tangent.  (transc.ml 2566-2893)                                           -/
/- ------------------------------------------------------------------------- -/

structure Tan where
  -- @@FIELDS
  tan : thm
  TAN_0 : thm
  TAN_PI : thm
  TAN_NPI : thm
  TAN_NEG : thm
  TAN_PERIODIC : thm
  TAN_PERIODIC_PI : thm
  TAN_PERIODIC_NPI : thm
  TAN_ADD : thm
  TAN_DOUBLE : thm
  TAN_POS_PI2 : thm
  DIFF_TAN : thm
  TAN_TOTAL_LEMMA : thm
  TAN_TOTAL_POS : thm
  TAN_TOTAL : thm
  PI2_PI4 : thm
  TAN_PI4 : thm
  TAN_COT : thm
  TAN_BOUND_PI2 : thm
  TAN_ABS_GE_X : thm
  deriving Inhabited

@[nospecialize]
def setupTan [HolBase] (D : TranscDeps) (BDefs : Defs) (BDiffConv : DiffConv) (BTrig1 : Trig1) (BTrig2 : Trig2) (ACompat : HolLibrary.Analysis.Compat) (ATactics : HolLibrary.Analysis.Tactics) (AReals1 : HolLibrary.Analysis.Reals1) (AReals2 : HolLibrary.Analysis.Reals2) (AReals3 : HolLibrary.Analysis.Reals3) (AAbs : HolLibrary.Analysis.Abs) (APow : HolLibrary.Analysis.Pow) (ALims : HolLibrary.Analysis.Lims) (ADiffs : HolLibrary.Analysis.Diffs) (AMvt : HolLibrary.Analysis.Mvt) :
    ExceptT String IO Tan := do
  -- @@SCOPE BEGIN
  let { INDUCT_TAC, REAL_ARITH, REAL_ARITH_TAC, REAL_RAT_REDUCE_CONV, new_definition, .. } := D
  let { ARITH, ARITH_EVEN, BETA_THM, CONJ_ASSOC, CONJ_SYM, DE_MORGAN_THM, EQ_IMP,
        EVEN_MULT, IMP_IMP, LEFT_IMP_EXISTS_THM, NOT_IMP, REAL_ABS_0, REAL_ABS_NEG,
        REAL_ABS_NUM, REAL_ADD_ASSOC, REAL_ADD_RDISTRIB, REAL_ADD_RID, real_abs, .. } := D.core1
  let { REAL_ADD_SYM, REAL_DOWN2, REAL_ENTIRE, REAL_EQ_LDIV_EQ, REAL_EQ_MUL_LCANCEL,
        REAL_EQ_RDIV_EQ, REAL_INV_1_LE, REAL_INV_DIV, REAL_INV_NEG, REAL_LET_TRANS,
        REAL_LE_ADDR, REAL_LE_LMUL, REAL_LT_DIV, REAL_LT_INV2, REAL_LT_INV_EQ,
        REAL_LT_MUL, REAL_LT_TOTAL, REAL_MUL_AC, REAL_MUL_ASSOC, REAL_MUL_LID,
        REAL_MUL_LINV, REAL_MUL_LNEG, REAL_MUL_RNEG, REAL_MUL_SYM, REAL_OF_NUM_EQ,
        REAL_OF_NUM_LT, REAL_OF_NUM_MUL, REAL_OF_NUM_SUC, REAL_POW_1_LE, REAL_POW_LT,
        real_div, real_sub, .. } := D.core2
  let { DIFF_COS, DIFF_SIN, add_to_diff_net, .. } := BDefs
  let { DIFF_CONV, .. } := BDiffConv
  let { COS_0, COS_ADD, COS_BOUNDS, COS_NEG, SIN_0, SIN_ADD, SIN_CIRCLE, SIN_NEG, .. } := BTrig1
  let { COS_PERIODIC, COS_PERIODIC_PI, COS_PI2, COS_POS_PI, COS_POS_PI2, COS_SIN,
        PI2_BOUNDS, PI_POS, SIN_COS, SIN_NPI, SIN_PERIODIC, SIN_PERIODIC_PI, SIN_PI,
        SIN_PI2, SIN_POS_PI2, SIN_ZERO, .. } := BTrig2
  let { EXISTS_UNIQUE_CONV, .. } := ACompat
  let { HABS_CONV, IMP_SUBST_TAC, .. } := ATactics
  let { REAL_10, REAL_LDISTRIB, REAL_LE_LT, REAL_LE_NEGTOTAL, REAL_LE_REFL,
        REAL_LTE_TRANS, REAL_LT_01, REAL_LT_IMP_LE, REAL_LT_NEGTOTAL, REAL_MUL_LZERO,
        REAL_MUL_RID, REAL_MUL_RINV, REAL_MUL_RZERO, REAL_NEG_GE0, REAL_NEG_LMUL,
        REAL_NEG_NEG, REAL_NOT_LE, .. } := AReals1
  let { REAL_DIV_LZERO, REAL_DOUBLE, REAL_INVINV, REAL_INV_1OVER, REAL_INV_NZ,
        REAL_INV_POS, REAL_LE_NEGL, REAL_NEG_0, REAL_NEG_EQ, REAL_POS,
        REAL_SUB_LDISTRIB, REAL_SUB_LT, .. } := AReals2
  let { REAL_DIV_MUL2, REAL_INV_MUL_WEAK, REAL_LT_IMP_NZ, REAL_LT_NEG2, REAL_SUB_RZERO,
        REAL_SUB_SUB, .. } := AReals3
  let { ABS_NEG, ABS_NZ, ABS_REFL, .. } := AAbs
  let { POW_2, POW_NZ, .. } := APow
  let { CONTL_LIM, DIFF_CONT, DIFF_UNIQ, LIM, LIM_DIV, differentiable, .. } := ALims
  let { DIFF_CHAIN, IVT, .. } := ADiffs
  let { MVT_ALT, ROLLE, .. } := AMvt
  -- @@SCOPE END
  -- `W(C SUBGOAL_THEN ttac o funpow 2 (fst o dest_imp) o snd)`
  let subgoalAnte2 (ttac : thm_tactic) : tactic := fun gl => ExceptT.run do
    let t ← liftExcept (funpow 2 (fun (m : Except String term) => do
      pure (← dest_imp (← m)).1) (pure gl.2))
    ExceptT.mk (SUBGOAL_THEN t ttac gl)
  -- `W(C SUBGOAL_THEN ttac o funpow 2 lhand o snd)`
  let subgoalLhand2 (ttac : thm_tactic) : tactic := fun gl => ExceptT.run do
    let t ← liftExcept (do lhand (← lhand gl.2))
    ExceptT.mk (SUBGOAL_THEN t ttac gl)

  let tan ← new_definition
   r"tan(x) = sin(x) / cos(x)"

  let TAN_0 ← prove
   r"tan(&0) = &0"
   (REWRITE_TAC [tan, SIN_0, REAL_DIV_LZERO])

  let TAN_PI ← prove
   r"tan(pi) = &0"
   (REWRITE_TAC [tan, SIN_PI, REAL_DIV_LZERO])

  let TAN_NPI ← prove
   r"!n. tan(&n * pi) = &0"
   (GEN_TAC THEN REWRITE_TAC [tan, SIN_NPI, REAL_DIV_LZERO])

  let TAN_NEG ← prove
   r"!x. tan(--x) = --(tan x)"
   (GEN_TAC THEN REWRITE_TAC [tan, SIN_NEG, COS_NEG] THEN
    REWRITE_TAC [real_div, REAL_NEG_LMUL])

  let TAN_PERIODIC ← prove
   r"!x. tan(x + &2 * pi) = tan(x)"
   (GEN_TAC THEN REWRITE_TAC [tan, SIN_PERIODIC, COS_PERIODIC])

  let TAN_PERIODIC_PI ← prove
   r"!x. tan(x + pi) = tan(x)"
   (REWRITE_TAC [tan, SIN_PERIODIC_PI, COS_PERIODIC_PI,
        real_div, REAL_INV_NEG, REAL_MUL_LNEG, REAL_MUL_RNEG, REAL_NEG_NEG])

  let TAN_PERIODIC_NPI ← prove
   r"!x n. tan(x + &n * pi) = tan(x)"
   (GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [REAL_MUL_LZERO, REAL_ADD_RID] THEN
    REWRITE_TAC [← GSYM REAL_OF_NUM_SUC, REAL_ADD_RDISTRIB, REAL_MUL_LID] THEN
    ASM_REWRITE_TAC [REAL_ADD_ASSOC, TAN_PERIODIC_PI])

  let TAN_ADD ← prove
   r"!x y. ~(cos(x) = &0) /\ ~(cos(y) = &0) /\ ~(cos(x + y) = &0) ==>
           (tan(x + y) = (tan(x) + tan(y)) / (&1 - tan(x) * tan(y)))"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [tan] THEN
    MP_TAC (← SPECL [← q "cos(x) * cos(y)",
                     ← q r"&1 - (sin(x) / cos(x)) * (sin(y) / cos(y))"]
           REAL_DIV_MUL2) THEN ASM_REWRITE_TAC [REAL_ENTIRE] THEN
    subgoalAnte2 MP_TAC THENL
     [DISCH_THEN (MP_TAC o AP_TERM (← q "(*) (cos(x) * cos(y))")) THEN
      REWRITE_TAC [real_div, REAL_SUB_LDISTRIB, ← GSYM REAL_MUL_ASSOC] THEN
      REWRITE_TAC [REAL_MUL_RID, REAL_MUL_RZERO] THEN
      UNDISCH_TAC (← q r"~(cos(x + y) = &0)") THEN
      MATCH_MP_TAC EQ_IMP THEN
      AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC [COS_ADD] THEN AP_TERM_TAC,
      DISCH_THEN (fun th => DISCH_THEN (MP_TAC o (fun a => MATCH_MP a th))) THEN
      DISCH_THEN (fun th => ONCE_REWRITE_TAC [th]) THEN BINOP_TAC THENL
       [REWRITE_TAC [real_div, REAL_LDISTRIB, ← GSYM REAL_MUL_ASSOC] THEN
        REWRITE_TAC [SIN_ADD] THEN BINOP_TAC THENL
         [ONCE_REWRITE_TAC [← AC REAL_MUL_AC
            (← q r"a * b * c * d = (d * a) * (c * b)")] THEN
          IMP_SUBST_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC [REAL_MUL_LID],
          ONCE_REWRITE_TAC [← AC REAL_MUL_AC
            (← q r"a * b * c * d = (d * b) * (a * c)")] THEN
          IMP_SUBST_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC [REAL_MUL_LID]],
        REWRITE_TAC [COS_ADD, REAL_SUB_LDISTRIB, REAL_MUL_RID] THEN
        AP_TERM_TAC THEN REWRITE_TAC [real_div, ← GSYM REAL_MUL_ASSOC]]] THEN
    ONCE_REWRITE_TAC [← AC REAL_MUL_AC
      (← q r"a * b * c * d * e * f = (f * b) * (d * a) * (c * e)")] THEN
    REPEAT (IMP_SUBST_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC []) THEN
    REWRITE_TAC [REAL_MUL_LID])

  let TAN_DOUBLE ← prove
   r"!x. ~(cos(x) = &0) /\ ~(cos(&2 * x) = &0) ==>
            (tan(&2 * x) = (&2 * tan(x)) / (&1 - (tan(x) pow 2)))"
   (GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← SPECL [← q "x:real", ← q "x:real"] TAN_ADD) THEN
    ASM_REWRITE_TAC [REAL_DOUBLE, POW_2])

  let TAN_POS_PI2 ← prove
   r"!x. &0 < x /\ x < pi / &2 ==> &0 < tan(x)"
   (GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [tan, real_div] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SIN_POS_PI2,
      MATCH_MP_TAC REAL_INV_POS THEN MATCH_MP_TAC COS_POS_PI2] THEN
    ASM_REWRITE_TAC [])

  let DIFF_TAN ← prove
   r"!x. ~(cos(x) = &0) ==> (tan diffl inv(cos(x) pow 2))(x)"
   (GEN_TAC THEN DISCH_TAC THEN
    MP_TAC (← ExceptT.mk (DIFF_CONV (← q r"\x. sin(x) / cos(x)"))) THEN
    DISCH_THEN (MP_TAC o SPEC (← q "x:real")) THEN ASM_REWRITE_TAC [REAL_MUL_RID] THEN
    REWRITE_TAC [← GSYM tan, ← GSYM REAL_NEG_LMUL, REAL_NEG_NEG, real_sub] THEN
    CONV_TAC (ONCE_DEPTH_CONV ETA_CONV) THEN ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
    REWRITE_TAC [← GSYM POW_2, SIN_CIRCLE, ← GSYM REAL_INV_1OVER])

  -- `let DIFF_TAN_COMPOSITE = prove (...) in add_to_diff_net ...`: a local
  -- binding, not exported.
  let _DIFF_TAN_COMPOSITE ← prove
   r"(g diffl m)(x) /\ ~(cos(g x) = &0)
   ==> ((\x. tan(g x)) diffl (inv(cos(g x) pow 2) * m))(x)"
   (ASM_SIMP_TAC [DIFF_CHAIN, DIFF_TAN])
  add_to_diff_net _DIFF_TAN_COMPOSITE

  let TAN_TOTAL_LEMMA ← prove
   r"!y. &0 < y ==> ?x. &0 < x /\ x < pi / &2 /\ y < tan(x)"
   (← do
    let aPos ← ASSUME (← q r"&0 < cos((pi / &2) - e) / sin((pi / &2) - e)")
    pure (GEN_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"((\x. cos(x) / sin(x)) tends_real_real &0)(pi / &2)")
      MP_TAC THENL
       [SUBST1_TAC (← SYM (← SPEC (← q r"&1") REAL_DIV_LZERO)) THEN
        CONV_TAC (ONCE_DEPTH_CONV HABS_CONV) THEN MATCH_MP_TAC LIM_DIV THEN
        REWRITE_TAC [REAL_10] THEN CONV_TAC (ONCE_DEPTH_CONV ETA_CONV) THEN
        SUBST1_TAC (← SYM COS_PI2) THEN SUBST1_TAC (← SYM SIN_PI2) THEN
        REWRITE_TAC [← GSYM CONTL_LIM] THEN CONJ_TAC THEN MATCH_MP_TAC DIFF_CONT THENL
         [EXISTS_TAC (← q r"--(sin(pi / &2))"),
          EXISTS_TAC (← q r"cos(pi / &2)")] THEN
        REWRITE_TAC [DIFF_SIN, DIFF_COS], ALL_TAC] THEN
      REWRITE_TAC [LIM] THEN DISCH_THEN (MP_TAC o SPEC (← q "inv(y)")) THEN
      FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP REAL_INV_POS th])) THEN
      BETA_TAC THEN REWRITE_TAC [REAL_SUB_RZERO] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "d:real") STRIP_ASSUME_TAC) THEN
      MP_TAC (← SPECL [← q "d:real", ← q r"pi / &2"] REAL_DOWN2) THEN
      ASM_REWRITE_TAC [PI2_BOUNDS] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "e:real") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"(pi / &2) - e") THEN ASM_REWRITE_TAC [REAL_SUB_LT] THEN
      CONJ_TAC THENL
       [REWRITE_TAC [real_sub, ← GSYM REAL_NOT_LE, REAL_LE_ADDR, REAL_NEG_GE0] THEN
        ASM_REWRITE_TAC [REAL_NOT_LE], ALL_TAC] THEN
      FIRST_ASSUM (undischCheck (fun c => pure (is_forall c))) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"(pi / &2) - e")) THEN
      REWRITE_TAC [REAL_SUB_SUB, ABS_NEG] THEN
      SUBGOAL_THEN (← q "abs(e) = e") (fun th => ASM_REWRITE_TAC [th]) THENL
       [REWRITE_TAC [ABS_REFL] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
        FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
      SUBGOAL_THEN (← q r"&0 < cos((pi / &2) - e) / sin((pi / &2) - e)")
      MP_TAC THENL
       [ONCE_REWRITE_TAC [real_div] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC COS_POS_PI2,
          MATCH_MP_TAC REAL_INV_POS THEN MATCH_MP_TAC SIN_POS_PI2] THEN
        ASM_REWRITE_TAC [REAL_SUB_LT] THEN
        REWRITE_TAC [← GSYM REAL_NOT_LE, real_sub, REAL_LE_ADDR, REAL_NEG_GE0] THEN
        ASM_REWRITE_TAC [REAL_NOT_LE], ALL_TAC] THEN
      DISCH_THEN (fun th => tactic_of do
        pure (ASSUME_TAC th THEN MP_TAC (← MATCH_MP REAL_LT_IMP_NZ th))) THEN
      REWRITE_TAC [ABS_NZ, IMP_IMP] THEN
      DISCH_THEN (MP_TAC o MATCH_MP REAL_LT_INV2) THEN REWRITE_TAC [tan] THEN
      MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
       [MATCH_MP_TAC REAL_INVINV THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
        FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
      MP_TAC aPos THEN
      DISCH_THEN (MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
      REWRITE_TAC [← GSYM ABS_REFL] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [real_div] THEN IMP_SUBST_TAC REAL_INV_MUL_WEAK THENL
       [REWRITE_TAC [← GSYM DE_MORGAN_THM, ← GSYM REAL_ENTIRE, ← GSYM real_div] THEN
        MATCH_MP_TAC REAL_LT_IMP_NZ THEN FIRST_ASSUM ACCEPT_TAC,
        GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN AP_TERM_TAC THEN
        MATCH_MP_TAC REAL_INVINV THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
        MATCH_MP_TAC SIN_POS_PI2 THEN REWRITE_TAC [REAL_SUB_LT, ← GSYM real_div] THEN
        REWRITE_TAC [← GSYM REAL_NOT_LE, real_sub, REAL_LE_ADDR, REAL_NEG_GE0] THEN
        ASM_REWRITE_TAC [REAL_NOT_LE]]))

  let TAN_TOTAL_POS ← prove
   r"!y. &0 <= y ==> ?x. &0 <= x /\ x < pi / &2 /\ (tan(x) = y)"
   (GEN_TAC THEN DISCH_THEN (DISJ_CASES_TAC o REWRITE_RULE [REAL_LE_LT]) THENL
     [FIRST_ASSUM (MP_TAC o MATCH_MP TAN_TOTAL_LEMMA) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "x:real") STRIP_ASSUME_TAC) THEN
      MP_TAC (← SPECL [← q "tan", ← q r"&0", ← q "x:real", ← q "y:real"] IVT) THEN
      subgoalAnte2 (fun th => DISCH_THEN (MP_TAC o (fun a => MATCH_MP a th))) THENL
       [REPEAT CONJ_TAC THEN TRY (MATCH_MP_TAC REAL_LT_IMP_LE) THEN
        ASM_REWRITE_TAC [TAN_0] THEN X_GEN_TAC (← q "z:real") THEN STRIP_TAC THEN
        MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC (← q "inv(cos(z) pow 2)") THEN
        MATCH_MP_TAC DIFF_TAN THEN UNDISCH_TAC (← q r"&0 <= z") THEN
        REWRITE_TAC [REAL_LE_LT] THEN DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL
         [DISCH_TAC THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
          MATCH_MP_TAC COS_POS_PI2 THEN ASM_REWRITE_TAC [] THEN
          MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q "x:real") THEN
          ASM_REWRITE_TAC [],
          DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [COS_0, REAL_10]],
        DISCH_THEN (X_CHOOSE_THEN (← q "z:real") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q "z:real") THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q "x:real") THEN
        ASM_REWRITE_TAC []],
      POP_ASSUM (SUBST1_TAC o SYM) THEN EXISTS_TAC (← q r"&0") THEN
      REWRITE_TAC [TAN_0, REAL_LE_REFL, PI2_BOUNDS]])

  let TAN_TOTAL ← prove
   r"!y. ?!x. --(pi / &2) < x /\ x < (pi / &2) /\ (tan(x) = y)"
   (← do
    let aTan ← ASSUME (← q r"(tan diffl &0)(x)")
    pure (GEN_TAC THEN CONV_TAC EXISTS_UNIQUE_CONV THEN CONJ_TAC THENL
     [DISJ_CASES_TAC (← SPEC (← q "y:real") REAL_LE_NEGTOTAL) THEN
      POP_ASSUM (X_CHOOSE_TAC (← q "x:real") o MATCH_MP TAN_TOTAL_POS) THENL
       [EXISTS_TAC (← q "x:real") THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q r"&0") THEN
        ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [← GSYM REAL_LT_NEG2] THEN
        REWRITE_TAC [REAL_NEG_NEG, REAL_NEG_0, PI2_BOUNDS],
        EXISTS_TAC (← q "--x") THEN ASM_REWRITE_TAC [REAL_LT_NEG2] THEN
        ASM_REWRITE_TAC [TAN_NEG, REAL_NEG_EQ, REAL_NEG_NEG] THEN
        ONCE_REWRITE_TAC [← GSYM REAL_LT_NEG2] THEN
        REWRITE_TAC [REAL_LT_NEG2] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC (← q "x:real") THEN ASM_REWRITE_TAC [REAL_LE_NEGL]],
      MAP_EVERY X_GEN_TAC [← q "x1:real", ← q "x2:real"] THEN
      REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
           (← SPECL [← q "x1:real", ← q "x2:real"] REAL_LT_TOTAL) THENL
       [DISCH_THEN (fun _ => ALL_TAC) THEN POP_ASSUM ACCEPT_TAC,
        ALL_TAC,
        POP_ASSUM MP_TAC THEN SPEC_TAC (← q "x1:real", ← q "z1:real") THEN
        SPEC_TAC (← q "x2:real", ← q "z2:real") THEN
        MAP_EVERY X_GEN_TAC [← q "x1:real", ← q "x2:real"] THEN DISCH_TAC THEN
        CONV_TAC (RAND_CONV SYM_CONV) THEN ONCE_REWRITE_TAC [CONJ_SYM]] THEN
      (STRIP_TAC THEN MP_TAC (← SPECL [← q "tan", ← q "x1:real", ← q "x2:real"] ROLLE) THEN
       ASM_REWRITE_TAC [] THEN CONV_TAC CONTRAPOS_CONV THEN
       DISCH_THEN (fun _ => ALL_TAC) THEN REWRITE_TAC [NOT_IMP] THEN
       REPEAT CONJ_TAC THENL
        [X_GEN_TAC (← q "x:real") THEN STRIP_TAC THEN MATCH_MP_TAC DIFF_CONT THEN
         EXISTS_TAC (← q "inv(cos(x) pow 2)") THEN MATCH_MP_TAC DIFF_TAN,
         X_GEN_TAC (← q "x:real") THEN
         DISCH_THEN (CONJUNCTS_THEN (ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE)) THEN
         REWRITE_TAC [differentiable] THEN EXISTS_TAC (← q "inv(cos(x) pow 2)") THEN
         MATCH_MP_TAC DIFF_TAN,
         REWRITE_TAC [CONJ_ASSOC] THEN DISCH_THEN (X_CHOOSE_THEN (← q "x:real")
           (CONJUNCTS_THEN2 (CONJUNCTS_THEN (ASSUME_TAC o MATCH_MP
            REAL_LT_IMP_LE)) ASSUME_TAC)) THEN
         MP_TAC (← SPEC (← q "x:real") DIFF_TAN) THEN
         SUBGOAL_THEN (← q r"~(cos(x) = &0)") ASSUME_TAC THENL
          [ALL_TAC,
           ASM_REWRITE_TAC [] THEN
           DISCH_THEN (MP_TAC o (fun th => CONJ th aTan)) THEN
           DISCH_THEN (MP_TAC o MATCH_MP DIFF_UNIQ) THEN REWRITE_TAC [] THEN
           MATCH_MP_TAC REAL_INV_NZ THEN MATCH_MP_TAC POW_NZ THEN
           ASM_REWRITE_TAC []]] THEN
       (MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC COS_POS_PI THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q "x1:real"),
          MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q "x2:real")] THEN
       ASM_REWRITE_TAC []))]))

  let PI2_PI4 ← prove
   r"pi / &2 = &2 * pi / &4"
   (ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    REWRITE_TAC [real_div, ← GSYM REAL_MUL_ASSOC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV)

  let TAN_PI4 ← prove
   r"tan(pi / &4) = &1"
   (← do
    let ra ← REAL_ARITH (← q r"&0 <= x ==> ~(&1 = --x)")
    pure (REWRITE_TAC [tan, COS_SIN, real_div, ← GSYM REAL_SUB_LDISTRIB] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN MATCH_MP_TAC REAL_MUL_RINV THEN
      REWRITE_TAC [SIN_ZERO] THEN
      REWRITE_TAC [real_div, ← GSYM REAL_MUL_LNEG] THEN
      ONCE_REWRITE_TAC [← AC REAL_MUL_AC (← q r"a * b * c = b * a * c")] THEN
      SIMP_TAC [REAL_MUL_LID, REAL_EQ_MUL_LCANCEL, PI_POS, REAL_LT_IMP_NZ] THEN
      SIMP_TAC [← GSYM real_div, REAL_EQ_RDIV_EQ, REAL_OF_NUM_LT, ARITH] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      SIMP_TAC [REAL_EQ_LDIV_EQ, REAL_OF_NUM_LT, ARITH] THEN
      REWRITE_TAC [REAL_MUL_LNEG, REAL_OF_NUM_MUL, REAL_OF_NUM_EQ] THEN
      SIMP_TAC [ra, REAL_POS] THEN
      STRIP_TAC THEN FIRST_ASSUM (MP_TAC o AP_TERM (← q "EVEN")) THEN
      REWRITE_TAC [EVEN_MULT, ARITH_EVEN]))

  let TAN_COT ← prove
   r"!x. tan(pi / &2 - x) = inv(tan x)"
   (REWRITE_TAC [tan, ← GSYM SIN_COS, ← GSYM COS_SIN, REAL_INV_DIV])

  let TAN_BOUND_PI2 ← prove
   r"!x. abs(x) < pi / &4 ==> abs(tan x) < &1"
   (← do
    -- The REAL_ARITHs in OCaml's order: right to left.
    let r5 ← REAL_ARITH (← q r"~(x = &0) /\ ~(&0 < x) ==> &0 < --x")
    let r4 ← REAL_ARITH (← q r"&0 < x /\ x < &1 ==> abs(x) < &1")
    let r3 ← REAL_ARITH (← q r"&0 < x /\ x < &1 ==> abs(x) < &1")
    let r2 ← REAL_ARITH (← q r"x < &1 <=> &0 < &1 - x")
    let r1 ← REAL_ARITH (← q r"&0 < x /\ x < a ==> x < &2 * a")
    pure (REPEAT GEN_TAC THEN
      SUBGOAL_THEN
       (← q r"!x. &0 < x /\ x < pi / &4 ==> &0 < tan(x) /\ tan(x) < &1")
      ASSUME_TAC THENL
       [REPEAT STRIP_TAC THENL
         [ASM_SIMP_TAC [tan, REAL_LT_DIV, SIN_POS_PI2, COS_POS_PI2, PI2_PI4, r1],
          ALL_TAC] THEN
        MP_TAC (← SPECL [← q "tan", ← q r"\x. inv(cos(x) pow 2)",
                         ← q "x:real", ← q r"pi / &4"] MVT_ALT) THEN
        subgoalLhand2 (fun th => REWRITE_TAC [th]) THENL
         [ASM_REWRITE_TAC [BETA_THM] THEN X_GEN_TAC (← q "z:real") THEN STRIP_TAC THEN
          MATCH_MP_TAC DIFF_TAN THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
          MATCH_MP_TAC COS_POS_PI2 THEN REWRITE_TAC [PI2_PI4] THEN
          MAP_EVERY UNDISCH_TAC [← q "x <= z", ← q r"z <= pi / &4", ← q r"&0 < x"] THEN
          REAL_ARITH_TAC,
          ALL_TAC] THEN
        SIMP_TAC [TAN_PI4, r2,
                 LEFT_IMP_EXISTS_THM] THEN
        X_GEN_TAC (← q "z:real") THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC [REAL_SUB_LT] THEN
        REWRITE_TAC [REAL_LT_INV_EQ, BETA_THM] THEN
        MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC COS_POS_PI2 THEN
        REWRITE_TAC [PI2_PI4] THEN
        MAP_EVERY UNDISCH_TAC [← q "x < z", ← q r"z < pi / &4", ← q r"&0 < x"] THEN
        REAL_ARITH_TAC, ALL_TAC] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [real_abs] THEN
      REWRITE_TAC [REAL_LE_LT] THEN
      ASM_CASES_TAC (← q r"x = &0") THEN
      ASM_REWRITE_TAC [TAN_0, REAL_ABS_NUM, REAL_LT_01] THEN
      COND_CASES_TAC THEN
      ASM_SIMP_TAC [r3] THEN
      ONCE_REWRITE_TAC [← GSYM REAL_ABS_NEG] THEN REWRITE_TAC [← GSYM TAN_NEG] THEN
      ASM_SIMP_TAC [r4, r5]))

  let TAN_ABS_GE_X ← prove
   r"!x. abs(x) < pi / &2 ==> abs(x) <= abs(tan x)"
   (← do
    -- The later rule in the THEN chain is evaluated first.
    let t ← TAUT (← q r"a /\ (b ==> c) ==> (a ==> b) ==> c")
    let ra ← REAL_ARITH
     (← q r"&0 < x /\ (x < p ==> x <= tx)
        ==> abs(x) < p ==> abs(x) <= abs(tx)")
    pure (SUBGOAL_THEN (← q r"!y. &0 < y /\ y < pi / &2 ==> y <= tan(y)") ASSUME_TAC THENL
     [ALL_TAC,
      GEN_TAC THEN
      REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (← SPEC (← q "x:real") REAL_LT_NEGTOTAL) THEN
      ASM_REWRITE_TAC [TAN_0, REAL_ABS_0, REAL_LE_REFL] THENL
       [ALL_TAC,
        ONCE_REWRITE_TAC [← GSYM REAL_ABS_NEG] THEN REWRITE_TAC [← GSYM TAN_NEG]] THEN
      MATCH_MP_TAC ra THEN ASM_SIMP_TAC []] THEN
    GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← SPECL [← q "tan", ← q r"\x. inv(cos(x) pow 2)", ← q r"&0", ← q "y:real"] MVT_ALT) THEN
    ASM_REWRITE_TAC [TAN_0, REAL_SUB_RZERO] THEN
    MATCH_MP_TAC t THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC DIFF_TAN THEN
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC COS_POS_PI THEN
      POP_ASSUM_LIST (fun ths => tactic_of do pure (MP_TAC (← endItlistM CONJ ths))) THEN
      REAL_ARITH_TAC,
      DISCH_THEN (X_CHOOSE_THEN (← q "z:real") STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC [BETA_THM] THEN
      GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_INV_1_LE THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT,
        MATCH_MP_TAC REAL_POW_1_LE THEN REWRITE_TAC [COS_BOUNDS] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC COS_POS_PI THEN
      POP_ASSUM_LIST (fun ths => tactic_of do pure (MP_TAC (← endItlistM CONJ ths))) THEN
      REAL_ARITH_TAC]))

  -- @@RETURN BEGIN
  return { tan, TAN_0, TAN_PI, TAN_NPI, TAN_NEG, TAN_PERIODIC, TAN_PERIODIC_PI,
           TAN_PERIODIC_NPI, TAN_ADD, TAN_DOUBLE, TAN_POS_PI2, DIFF_TAN, TAN_TOTAL_LEMMA,
           TAN_TOTAL_POS, TAN_TOTAL, PI2_PI4, TAN_PI4, TAN_COT, TAN_BOUND_PI2,
           TAN_ABS_GE_X }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Inverse trig functions; differentiation of arctan; a few more lemmas      -/
/- about arctan.  (transc.ml 2893-3104)                                      -/
/- ------------------------------------------------------------------------- -/

structure InvTrig where
  -- @@FIELDS
  asn : thm
  acs : thm
  atn : thm
  ASN : thm
  ASN_SIN : thm
  ASN_BOUNDS : thm
  ASN_BOUNDS_LT : thm
  SIN_ASN : thm
  ACS : thm
  ACS_COS : thm
  ACS_BOUNDS : thm
  ACS_BOUNDS_LT : thm
  COS_ACS : thm
  ATN : thm
  ATN_TAN : thm
  ATN_BOUNDS : thm
  TAN_ATN : thm
  ATN_0 : thm
  ATN_1 : thm
  ATN_NEG : thm
  COS_ATN_NZ : thm
  TAN_SEC : thm
  DIFF_ATN : thm
  ATN_MONO_LT : thm
  ATN_MONO_LT_EQ : thm
  ATN_MONO_LE_EQ : thm
  ATN_INJ : thm
  ATN_POS_LT : thm
  ATN_POS_LE : thm
  ATN_LT_PI4_POS : thm
  ATN_LT_PI4_NEG : thm
  ATN_LT_PI4 : thm
  ATN_LE_PI4 : thm
  deriving Inhabited

@[nospecialize]
def setupInvTrig [HolBase] (D : TranscDeps) (BDefs : Defs) (BTrig1 : Trig1) (BTrig2 : Trig2) (BTan : Tan) (ACompat : HolLibrary.Analysis.Compat) (ATactics : HolLibrary.Analysis.Tactics) (AReals1 : HolLibrary.Analysis.Reals1) (AReals2 : HolLibrary.Analysis.Reals2) (AReals3 : HolLibrary.Analysis.Reals3) (AAbs : HolLibrary.Analysis.Abs) (APow : HolLibrary.Analysis.Pow) (ALims : HolLibrary.Analysis.Lims) (ADiffs : HolLibrary.Analysis.Diffs) (AMvt : HolLibrary.Analysis.Mvt) (AInverse : HolLibrary.Analysis.Inverse) :
    ExceptT String IO InvTrig := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, REAL_ARITH, REAL_RAT_REDUCE_CONV, new_definition, .. } := D
  let { ADD1, ARITH, DE_MORGAN_THM, EVEN, LE_0, REAL_ABS_DIV, REAL_ABS_NEG,
        REAL_ABS_NUM, REAL_ADD_LID, num_CASES, real_abs, .. } := D.core1
  let { REAL_ADD_SYM, REAL_DIV_REFL, REAL_LE_ADDR, REAL_LE_ANTISYM, REAL_LT_DIV,
        REAL_LT_INV_EQ, REAL_LT_MUL, REAL_LT_REFL, REAL_MUL_LID, REAL_OF_NUM_LT,
        REAL_POW_2, real_div, .. } := D.core2
  let { add_to_diff_net, .. } := BDefs
  let { COS_0, COS_BOUNDS, SIN_BOUNDS, SIN_CIRCLE, SIN_NEG, .. } := BTrig1
  let { COS_PI, COS_POS_PI, COS_TOTAL, COS_ZERO, PI2_BOUNDS, PI_POS, SIN_PI2,
        SIN_TOTAL, .. } := BTrig2
  let { DIFF_TAN, TAN_0, TAN_NEG, TAN_PI4, TAN_TOTAL, tan, .. } := BTan
  let { EXISTS_UNIQUE_CONV, NOT_EXISTS_CONV, .. } := ACompat
  let { IMP_SUBST_TAC, .. } := ATactics
  let { REAL_LE_LT, REAL_LE_SQUARE, REAL_LT_01, REAL_LT_IMP_LE, REAL_LT_LE,
        REAL_NOT_LE, REAL_NOT_LT, REAL_RDISTRIB, .. } := AReals1
  let { REAL_ADD, REAL_LE, REAL_LT_LMUL_EQ, REAL_LT_RMUL_EQ, .. } := AReals2
  let { REAL_LTE_ADD, REAL_LT_IMP_NZ, REAL_LT_NEG2, REAL_LT_SUB_LADD, .. } := AReals3
  let { ABS_SUB, .. } := AAbs
  let { POW_2, POW_INV, POW_MUL, POW_NZ, .. } := APow
  let { DIFF_CONT, .. } := ALims
  let { DIFF_CHAIN, .. } := ADiffs
  let { INTERVAL_LEMMA_LT, MVT_ALT, .. } := AMvt
  let { DIFF_INVERSE_LT, .. } := AInverse
  -- @@SCOPE END
  -- `DISCH_THEN((then_) (POP_ASSUM_LIST (MP_TAC o end_itlist CONJ)) o ASSUME_TAC)`
  let popAllThenAssume : tactic := DISCH_THEN (fun th =>
    POP_ASSUM_LIST (fun ths => tactic_of do pure (MP_TAC (← endItlistM CONJ ths))) THEN
    ASSUME_TAC th)

  let asn ← new_definition
   r"asn(y) = @x. --(pi / &2) <= x /\ x <= pi / &2 /\ (sin x = y)"

  let acs ← new_definition
   r"acs(y) = @x. &0 <= x /\ x <= pi /\ (cos x = y)"

  let atn ← new_definition
   r"atn(y) = @x. --(pi / &2) < x /\ x < pi / &2 /\ (tan x = y)"

  let ASN ← prove
   r"!y. --(&1) <= y /\ y <= &1 ==>
     --(pi / &2) <= asn(y) /\ asn(y) <= pi / &2 /\ (sin(asn y) = y)"
   (GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP SIN_TOTAL) THEN
    DISCH_THEN (MP_TAC o CONJUNCT1 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
    DISCH_THEN (MP_TAC o SELECT_RULE) THEN REWRITE_TAC [← GSYM asn])

  let ASN_SIN ← prove
   r"!y. --(&1) <= y /\ y <= &1 ==> (sin(asn(y)) = y)"
   (GEN_TAC THEN DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP ASN th])))

  let ASN_BOUNDS ← prove
   r"!y. --(&1) <= y /\ y <= &1 ==> --(pi / &2) <= asn(y) /\ asn(y) <= pi / &2"
   (GEN_TAC THEN DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP ASN th])))

  let ASN_BOUNDS_LT ← prove
   r"!y. --(&1) < y /\ y < &1 ==> --(pi / &2) < asn(y) /\ asn(y) < pi / &2"
   (GEN_TAC THEN STRIP_TAC THEN
    EVERY_ASSUM (ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
    MP_TAC (← SPEC (← q "y:real") ASN_BOUNDS) THEN ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [REAL_LT_LE] THEN
    CONJ_TAC THEN DISCH_THEN (MP_TAC o AP_TERM (← q "sin")) THEN
    IMP_SUBST_TAC ASN_SIN THEN ASM_REWRITE_TAC [SIN_NEG, SIN_PI2] THEN
    popAllThenAssume THEN ASM_REWRITE_TAC [REAL_LT_REFL])

  let SIN_ASN ← prove
   r"!x. --(pi / &2) <= x /\ x <= pi / &2 ==> (asn(sin(x)) = x)"
   (GEN_TAC THEN DISCH_TAC THEN
    MP_TAC (← MATCH_MP SIN_TOTAL (← SPEC (← q "x:real") SIN_BOUNDS)) THEN
    DISCH_THEN (MATCH_MP_TAC o CONJUNCT2 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC ASN THEN
    MATCH_ACCEPT_TAC SIN_BOUNDS)

  let ACS ← prove
   r"!y. --(&1) <= y /\ y <= &1 ==>
     &0 <= acs(y) /\ acs(y) <= pi  /\ (cos(acs y) = y)"
   (GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP COS_TOTAL) THEN
    DISCH_THEN (MP_TAC o CONJUNCT1 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
    DISCH_THEN (MP_TAC o SELECT_RULE) THEN REWRITE_TAC [← GSYM acs])

  let ACS_COS ← prove
   r"!y. --(&1) <= y /\ y <= &1 ==> (cos(acs(y)) = y)"
   (GEN_TAC THEN DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP ACS th])))

  let ACS_BOUNDS ← prove
   r"!y. --(&1) <= y /\ y <= &1 ==> &0 <= acs(y) /\ acs(y) <= pi"
   (GEN_TAC THEN DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP ACS th])))

  let ACS_BOUNDS_LT ← prove
   r"!y. --(&1) < y /\ y < &1 ==> &0 < acs(y) /\ acs(y) < pi"
   (GEN_TAC THEN STRIP_TAC THEN
    EVERY_ASSUM (ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
    MP_TAC (← SPEC (← q "y:real") ACS_BOUNDS) THEN ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [REAL_LT_LE] THEN
    CONJ_TAC THEN DISCH_THEN (MP_TAC o AP_TERM (← q "cos")) THEN
    IMP_SUBST_TAC ACS_COS THEN ASM_REWRITE_TAC [COS_0, COS_PI] THEN
    popAllThenAssume THEN ASM_REWRITE_TAC [REAL_LT_REFL])

  let COS_ACS ← prove
   r"!x. &0 <= x /\ x <= pi ==> (acs(cos(x)) = x)"
   (GEN_TAC THEN DISCH_TAC THEN
    MP_TAC (← MATCH_MP COS_TOTAL (← SPEC (← q "x:real") COS_BOUNDS)) THEN
    DISCH_THEN (MATCH_MP_TAC o CONJUNCT2 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC ACS THEN
    MATCH_ACCEPT_TAC COS_BOUNDS)

  let ATN ← prove
   r"!y. --(pi / &2) < atn(y) /\ atn(y) < (pi / &2) /\ (tan(atn y) = y)"
   (GEN_TAC THEN MP_TAC (← SPEC (← q "y:real") TAN_TOTAL) THEN
    DISCH_THEN (MP_TAC o CONJUNCT1 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
    DISCH_THEN (MP_TAC o SELECT_RULE) THEN REWRITE_TAC [← GSYM atn])

  let ATN_TAN ← prove
   r"!y. tan(atn y) = y"
   (REWRITE_TAC [ATN])

  let ATN_BOUNDS ← prove
   r"!y. --(pi / &2) < atn(y) /\ atn(y) < (pi / &2)"
   (REWRITE_TAC [ATN])

  let TAN_ATN ← prove
   r"!x. --(pi / &2) < x /\ x < (pi / &2) ==> (atn(tan(x)) = x)"
   (GEN_TAC THEN DISCH_TAC THEN MP_TAC (← SPEC (← q "tan(x)") TAN_TOTAL) THEN
    DISCH_THEN (MATCH_MP_TAC o CONJUNCT2 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
    ASM_REWRITE_TAC [ATN])

  let ATN_0 ← prove
   r"atn(&0) = &0"
   (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← SYM TAN_0] THEN
    MATCH_MP_TAC TAN_ATN THEN
    MATCH_MP_TAC (← REAL_ARITH (← q r"&0 < a ==> --a < &0 /\ &0 < a")) THEN
    SIMP_TAC [REAL_LT_DIV, PI_POS, REAL_OF_NUM_LT, ARITH])

  let ATN_1 ← prove
   r"atn(&1) = pi / &4"
   (MP_TAC (← AP_TERM (← q "atn") TAN_PI4) THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC TAN_ATN THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"&0 < a /\ a < b ==> --b < a /\ a < b")) THEN
    SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH, PI_POS] THEN
    SIMP_TAC [real_div, REAL_LT_LMUL_EQ, PI_POS] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV)

  let ATN_NEG ← prove
   r"!x. atn(--x) = --(atn x)"
   (GEN_TAC THEN MP_TAC (← SPEC (← q "atn(x)") TAN_NEG) THEN
    REWRITE_TAC [ATN_TAN] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC TAN_ATN THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"--a < x /\ x < a ==> --a < --x /\ --x < a")) THEN
    REWRITE_TAC [ATN_BOUNDS])

  -- Differentiation of arctan.

  let COS_ATN_NZ ← prove
   r"!x. ~(cos(atn(x)) = &0)"
   (GEN_TAC THEN REWRITE_TAC [COS_ZERO, DE_MORGAN_THM] THEN CONJ_TAC THEN
    CONV_TAC NOT_EXISTS_CONV THEN X_GEN_TAC (← q "n:num") THEN
    STRUCT_CASES_TAC (← SPEC (← q "n:num") num_CASES) THEN
    REWRITE_TAC [EVEN, DE_MORGAN_THM] THEN DISJ2_TAC THEN
    DISCH_TAC THEN MP_TAC (← SPEC (← q "x:real") ATN_BOUNDS) THEN
    ASM_REWRITE_TAC [DE_MORGAN_THM] THENL
     [DISJ2_TAC, DISJ1_TAC THEN REWRITE_TAC [REAL_LT_NEG2]] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [← GSYM REAL_MUL_LID] THEN
    REWRITE_TAC [← MATCH_MP REAL_LT_RMUL_EQ (← CONJUNCT1 PI2_BOUNDS)] THEN
    REWRITE_TAC [ADD1, ← GSYM REAL_ADD, REAL_NOT_LT] THEN
    ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
    REWRITE_TAC [REAL_LE_ADDR, REAL_LE, LE_0])

  let TAN_SEC ← prove
   r"!x. ~(cos(x) = &0) ==> (&1 + (tan(x) pow 2) = inv(cos x) pow 2)"
   (GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [tan] THEN
    FIRST_ASSUM (fun th => tactic_of do pure (ONCE_REWRITE_TAC [← GSYM
     (← MATCH_MP REAL_DIV_REFL (← SPEC (← q "2") (← MATCH_MP POW_NZ th)))])) THEN
    REWRITE_TAC [real_div, POW_MUL] THEN
    POP_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP POW_INV th])) THEN
    ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
    REWRITE_TAC [← GSYM REAL_RDISTRIB, SIN_CIRCLE, REAL_MUL_LID])

  let DIFF_ATN ← prove
   r"!x. (atn diffl (inv(&1 + (x pow 2))))(x)"
   (GEN_TAC THEN
    SUBGOAL_THEN (← q r"(atn diffl (inv(&1 + (x pow 2))))(tan(atn x))")
    MP_TAC THENL [MATCH_MP_TAC DIFF_INVERSE_LT, REWRITE_TAC [ATN_TAN]] THEN
    SUBGOAL_THEN
      (← q r"?d. &0 < d /\
           !z. abs(z - atn(x)) < d ==>  (--(pi / (& 2))) < z /\ z < (pi / (& 2))")
    (X_CHOOSE_THEN (← q "d:real") STRIP_ASSUME_TAC) THENL
     [ONCE_REWRITE_TAC [ABS_SUB] THEN MATCH_MP_TAC INTERVAL_LEMMA_LT THEN
      MATCH_ACCEPT_TAC ATN_BOUNDS,
      EXISTS_TAC (← q "d:real") THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THENL
       [MATCH_MP_TAC TAN_ATN THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC [],
        MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC (← q "inv(cos(z) pow 2)") THEN
        MATCH_MP_TAC DIFF_TAN THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
        MATCH_MP_TAC COS_POS_PI THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC [],
        ASSUME_TAC (← SPEC (← q "x:real") COS_ATN_NZ) THEN
        FIRST_ASSUM (MP_TAC o MATCH_MP DIFF_TAN) THEN
        FIRST_ASSUM (ASSUME_TAC o SYM o MATCH_MP TAN_SEC) THEN
        FIRST_ASSUM (ASSUME_TAC o MATCH_MP POW_INV) THEN
        ASM_REWRITE_TAC [ATN_TAN],
        UNDISCH_TAC (← q r"&1 + (x pow 2) = &0") THEN REWRITE_TAC [] THEN
        MATCH_MP_TAC REAL_LT_IMP_NZ THEN
        MATCH_MP_TAC REAL_LTE_ADD THEN
        REWRITE_TAC [REAL_LT_01, REAL_LE_SQUARE, POW_2]]])

  -- `let DIFF_ATN_COMPOSITE = prove (...) in add_to_diff_net ...`: a local
  -- binding, not exported.
  let _DIFF_ATN_COMPOSITE ← prove
   r"(g diffl m)(x) ==> ((\x. atn(g x)) diffl (inv(&1 + (g x) pow 2) * m))(x)"
   (ASM_SIMP_TAC [DIFF_CHAIN, DIFF_ATN])
  add_to_diff_net _DIFF_ATN_COMPOSITE

  -- A few more lemmas about arctan.

  let ATN_MONO_LT ← prove
   r"!x y. x < y ==> atn(x) < atn(y)"
   (← do
    -- The REAL_ARITHs in OCaml's order: right to left.
    let r3 ← REAL_ARITH (← q r"&0 <= x ==> &0 < &1 + x")
    let r2 ← REAL_ARITH (← q r"a < b + a <=> &0 < b")
    let r1 ← REAL_ARITH (← q r"(l - r = d) ==> l < d + e ==> r < e")
    pure (REPEAT STRIP_TAC THEN
      MP_TAC (← SPECL [← q "atn", ← q r"\x. inv(&1 + x pow 2)", ← q "x:real", ← q "y:real"]
                   MVT_ALT) THEN
      BETA_TAC THEN ASM_REWRITE_TAC [DIFF_ATN] THEN STRIP_TAC THEN
      FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP r1) THEN
      REWRITE_TAC [r2] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REWRITE_TAC [REAL_LT_SUB_LADD, REAL_ADD_LID] THEN
      REWRITE_TAC [REAL_LT_INV_EQ] THEN
      MATCH_MP_TAC r3 THEN
      REWRITE_TAC [REAL_POW_2, REAL_LE_SQUARE]))

  let ATN_MONO_LT_EQ ← prove
   r"!x y. atn(x) < atn(y) <=> x < y"
   (MESON_TAC [REAL_NOT_LE, REAL_LE_LT, ATN_MONO_LT])

  let ATN_MONO_LE_EQ ← prove
   r"!x y. atn(x) <= atn(y) <=> x <= y"
   (REWRITE_TAC [← GSYM REAL_NOT_LT, ATN_MONO_LT_EQ])

  let ATN_INJ ← prove
   r"!x y. (atn x = atn y) <=> (x = y)"
   (REWRITE_TAC [← GSYM REAL_LE_ANTISYM, ATN_MONO_LE_EQ])

  let ATN_POS_LT ← prove
   r"&0 < atn(x) <=> &0 < x"
   (MESON_TAC [ATN_0, ATN_MONO_LT_EQ])

  let ATN_POS_LE ← prove
   r"&0 <= atn(x) <=> &0 <= x"
   (MESON_TAC [ATN_0, ATN_MONO_LE_EQ])

  let ATN_LT_PI4_POS ← prove
   r"!x. x < &1 ==> atn(x) < pi / &4"
   (SIMP_TAC [← GSYM ATN_1, ATN_MONO_LT])

  let ATN_LT_PI4_NEG ← prove
   r"!x. --(&1) < x ==> --(pi / &4) < atn(x)"
   (SIMP_TAC [← GSYM ATN_1, ← GSYM ATN_NEG, ATN_MONO_LT])

  let ATN_LT_PI4 ← prove
   r"!x. abs(x) < &1 ==> abs(atn x) < pi / &4"
   (GEN_TAC THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"(&0 < x ==> &0 < y) /\
      (x < &0 ==> y < &0) /\
      ((x = &0) ==> (y = &0)) /\
      (x < a ==> y < b) /\
      (--a < x ==> --b < y)
      ==> abs(x) < a ==> abs(y) < b")) THEN
    SIMP_TAC [ATN_LT_PI4_POS, ATN_LT_PI4_NEG, ATN_0] THEN CONJ_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [← GSYM ATN_0] THEN
    SIMP_TAC [ATN_MONO_LT])

  let ATN_LE_PI4 ← prove
   r"!x. abs(x) <= &1 ==> abs(atn x) <= pi / &4"
   (← do
    let ra ← REAL_ARITH (← q r"(abs(x) = a) ==> (x = a) \/ (x = --a)")
    pure (REWRITE_TAC [REAL_LE_LT] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC [ATN_LT_PI4] THEN DISJ2_TAC THEN
      FIRST_ASSUM (DISJ_CASES_THEN SUBST1_TAC o MATCH_MP ra) THEN
      ASM_REWRITE_TAC [ATN_1, ATN_NEG] THEN
      REWRITE_TAC [REAL_ABS_DIV, REAL_ABS_NUM, REAL_ABS_NEG] THEN
      SIMP_TAC [real_abs, REAL_LT_IMP_LE, PI_POS]))

  -- @@RETURN BEGIN
  return { asn, acs, atn, ASN, ASN_SIN, ASN_BOUNDS, ASN_BOUNDS_LT, SIN_ASN, ACS, ACS_COS,
           ACS_BOUNDS, ACS_BOUNDS_LT, COS_ACS, ATN, ATN_TAN, ATN_BOUNDS, TAN_ATN, ATN_0,
           ATN_1, ATN_NEG, COS_ATN_NZ, TAN_SEC, DIFF_ATN, ATN_MONO_LT, ATN_MONO_LT_EQ,
           ATN_MONO_LE_EQ, ATN_INJ, ATN_POS_LT, ATN_POS_LE, ATN_LT_PI4_POS,
           ATN_LT_PI4_NEG, ATN_LT_PI4, ATN_LE_PI4 }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Differentiation of arcsin and arccos; back to normal service; a kind of   -/
/- inverse to SIN_CIRCLE; the gauge integral's definitions.                  -/
/- (transc.ml 3105-3466)                                                     -/
/- ------------------------------------------------------------------------- -/

structure ArcSinCos where
  -- @@FIELDS
  COS_SIN_SQRT : thm
  COS_ASN_NZ : thm
  DIFF_ASN_COS : thm
  DIFF_ASN : thm
  SIN_COS_SQRT : thm
  SIN_ACS_NZ : thm
  DIFF_ACS_SIN : thm
  DIFF_ACS : thm
  CIRCLE_SINCOS : thm
  ACS_MONO_LT : thm
  LE_MATCH_TAC : thm_tactic
  LESS_SUC_EQ : thm
  LESS_1 : thm
  division : thm
  dsize : thm
  tdiv : thm
  gauge : thm
  fine : thm
  rsum : thm
  defint : thm
  deriving Inhabited

@[nospecialize]
def setupArcSinCos [HolBase] (D : TranscDeps) (BDefs : Defs) (BTrig1 : Trig1) (BTrig2 : Trig2) (BInvTrig : InvTrig) (ACompat : HolLibrary.Analysis.Compat) (ATactics : HolLibrary.Analysis.Tactics) (AReals1 : HolLibrary.Analysis.Reals1) (AReals2 : HolLibrary.Analysis.Reals2) (AReals3 : HolLibrary.Analysis.Reals3) (AAbs : HolLibrary.Analysis.Abs) (ALims : HolLibrary.Analysis.Lims) (ADiffs : HolLibrary.Analysis.Diffs) (AMvt : HolLibrary.Analysis.Mvt) (AInverse : HolLibrary.Analysis.Inverse) :
    ExceptT String IO ArcSinCos := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, INDUCT_TAC, REAL_ARITH, REAL_ARITH_TAC, REAL_RAT_REDUCE_CONV,
        extend_basic_rewrites, new_definition, num_CONV, .. } := D
  let { ADD1, BETA_THM, DE_MORGAN_THM, EQ_IMP, EVEN, LE, LE_0, LE_LT, LT,
        POW_2_SQRT_ABS, REAL_ABS_POS, REAL_ADD_ASSOC, num_CASES, .. } := D.core1
  let { REAL_ADD_SYM, REAL_EQ_SUB_LADD, REAL_EQ_SUB_RADD, REAL_LET_TRANS, REAL_LE_ADDL,
        REAL_LT_INV, REAL_LT_MUL, REAL_LT_MUL2, REAL_LT_REFL, REAL_MUL_LID,
        REAL_POW2_ABS, REAL_POW_2, SQRT_POS_LT, SQRT_UNIQUE, .. } := D.core2
  let { DIFF_COS, DIFF_SIN, add_to_diff_net, .. } := BDefs
  let { COS_NEG, SIN_CIRCLE, SIN_NEG, .. } := BTrig1
  let { COS_POS_PI, COS_ZERO, PI2_BOUNDS, SIN_POS_PI, SIN_POS_PI_LE, SIN_ZERO, .. } := BTrig2
  let { ACS_BOUNDS, ACS_BOUNDS_LT, ACS_COS, ASN_BOUNDS_LT, ASN_SIN, COS_ACS, SIN_ASN, .. } := BInvTrig
  let { NOT_EXISTS_CONV, .. } := ACompat
  let { IMP_SUBST_TAC, .. } := ATactics
  let { REAL_LE_MUL, REAL_LE_REFL, REAL_LE_SQUARE, REAL_LE_TRANS, REAL_LTE_TRANS,
        REAL_LT_IMP_LE, REAL_MUL_LZERO, REAL_NEG_LMUL, REAL_NEG_NEG, REAL_NOT_LE,
        REAL_NOT_LT, REAL_RDISTRIB, .. } := AReals1
  let { REAL_ADD, REAL_LE, REAL_NEG_0, REAL_NEG_EQ0, REAL_NEG_INV, REAL_POS,
        REAL_SUB_LT, .. } := AReals2
  let { REAL_EQ_NEG, REAL_HALF_DOUBLE, REAL_LE_NEG2, REAL_LT_NEG2, .. } := AReals3
  let { ABS_SUB, .. } := AAbs
  let { DIFF_CONT, .. } := ALims
  let { DIFF_CHAIN, .. } := ADiffs
  let { INTERVAL_LEMMA_LT, MVT_ALT, .. } := AMvt
  let { DIFF_INVERSE_LT, .. } := AInverse
  -- @@SCOPE END
  let numc (s : String) : ExceptT String IO thm := do ExceptT.mk (num_CONV (← q s))

  -- Differentiation of arcsin.

  let COS_SIN_SQRT ← prove
   r"!x. &0 <= cos(x) ==> (cos(x) = sqrt(&1 - (sin(x) pow 2)))"
   (GEN_TAC THEN DISCH_TAC THEN
    MP_TAC (← ONCE_REWRITE_RULE [REAL_ADD_SYM] (← SPEC (← q "x:real") SIN_CIRCLE)) THEN
    REWRITE_TAC [← GSYM REAL_EQ_SUB_LADD] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_UNIQUE THEN
    ASM_REWRITE_TAC [])

  let COS_ASN_NZ ← prove
   r"!x. --(&1) < x /\ x < &1 ==> ~(cos(asn(x)) = &0)"
   (GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP ASN_BOUNDS_LT) THEN
    REWRITE_TAC [COS_ZERO, DE_MORGAN_THM] THEN
    CONJ_TAC THEN CONV_TAC NOT_EXISTS_CONV THEN
    X_GEN_TAC (← q "n:num") THEN STRUCT_CASES_TAC (← SPEC (← q "n:num") num_CASES) THEN
    REWRITE_TAC [EVEN] THEN STRIP_TAC THENL
     [UNDISCH_TAC (← q r"asn(x) < (pi / &2)") THEN ASM_REWRITE_TAC [],
      UNDISCH_TAC (← q r"--(pi / &2) < asn(x)") THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [REAL_LT_NEG2]] THEN
    REWRITE_TAC [ADD1, ← GSYM REAL_ADD, REAL_RDISTRIB, REAL_MUL_LID] THEN
    REWRITE_TAC [← GSYM REAL_NOT_LE, REAL_LE_ADDL] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC [REAL_LE, LE_0] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC [PI2_BOUNDS])

  let DIFF_ASN_COS ← prove
   r"!x. --(&1) < x /\ x < &1 ==> (asn diffl (inv(cos(asn x))))(x)"
   (REPEAT STRIP_TAC THEN
    EVERY_ASSUM (ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
    MP_TAC (← SPEC (← q "x:real") ASN_SIN) THEN ASM_REWRITE_TAC [] THEN
    DISCH_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [← GSYM th])) THEN
    MATCH_MP_TAC DIFF_INVERSE_LT THEN
    MP_TAC (← SPEC (← q "x:real") ASN_BOUNDS_LT) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (STRIP_ASSUME_TAC th THEN MP_TAC (← MATCH_MP INTERVAL_LEMMA_LT th))) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "d:real") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN (ASSUME_TAC o ONCE_REWRITE_RULE [ABS_SUB]) THEN
    EXISTS_TAC (← q "d:real") THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC SIN_ASN THEN
      FIRST_ASSUM (undischCheck (fun c => pure (is_forall c))) THEN
      DISCH_THEN (MP_TAC o SPEC (← q "z:real")) THEN ASM_REWRITE_TAC [] THEN
      DISCH_TAC THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC [],
      MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC (← q "cos(z)") THEN
      REWRITE_TAC [DIFF_SIN],
      REWRITE_TAC [DIFF_SIN],
      POP_ASSUM MP_TAC THEN REWRITE_TAC [] THEN MATCH_MP_TAC COS_ASN_NZ THEN
      ASM_REWRITE_TAC []])

  let DIFF_ASN ← prove
   r"!x. --(&1) < x /\ x < &1 ==> (asn diffl (inv(sqrt(&1 - (x pow 2)))))(x)"
   (GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP DIFF_ASN_COS) THEN
    MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN (← q "sin(asn x) = x") MP_TAC THENL
     [MATCH_MP_TAC ASN_SIN THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC [],
      DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC
        (RAND_CONV o ONCE_DEPTH_CONV) [← GSYM th])) THEN
      MATCH_MP_TAC COS_SIN_SQRT THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP ASN_BOUNDS_LT) THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC COS_POS_PI THEN
      ASM_REWRITE_TAC []])

  -- `let DIFF_ASN_COMPOSITE = prove (...) in add_to_diff_net ...`: a local
  -- binding, not exported.
  let _DIFF_ASN_COMPOSITE ← prove
   r"(g diffl m)(x) /\ -- &1 < g(x) /\ g(x) < &1
   ==> ((\x. asn(g x)) diffl (inv(sqrt (&1 - g(x) pow 2)) * m))(x)"
   (ASM_SIMP_TAC [DIFF_CHAIN, DIFF_ASN])
  add_to_diff_net _DIFF_ASN_COMPOSITE

  -- Differentiation of arccos.

  let SIN_COS_SQRT ← prove
   r"!x. &0 <= sin(x) ==> (sin(x) = sqrt(&1 - (cos(x) pow 2)))"
   (GEN_TAC THEN DISCH_TAC THEN
    MP_TAC (← SPEC (← q "x:real") SIN_CIRCLE) THEN
    REWRITE_TAC [← GSYM REAL_EQ_SUB_LADD] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_UNIQUE THEN
    ASM_REWRITE_TAC [])

  let SIN_ACS_NZ ← prove
   r"!x. --(&1) < x /\ x < &1 ==> ~(sin(acs(x)) = &0)"
   (GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP ACS_BOUNDS_LT) THEN
    REWRITE_TAC [SIN_ZERO, REAL_NEG_EQ0] THEN
    REWRITE_TAC [DE_MORGAN_THM] THEN
    CONJ_TAC THEN CONV_TAC NOT_EXISTS_CONV THEN
    (INDUCT_TAC THENL
      [REWRITE_TAC [REAL_MUL_LZERO, EVEN, REAL_NEG_0] THEN
       DISCH_THEN SUBST_ALL_TAC THEN
       RULE_ASSUM_TAC (REWRITE_RULE [REAL_LT_REFL]) THEN
       CONTR_TAC (← ASSUME (← q "F")), ALL_TAC] THEN
     SPEC_TAC (← q "n:num", ← q "n:num") THEN REWRITE_TAC [EVEN] THEN
     INDUCT_TAC THEN REWRITE_TAC [EVEN] THEN STRIP_TAC) THENL
      [UNDISCH_TAC (← q "acs(x) < pi") THEN
       ASM_REWRITE_TAC [ADD1, ← GSYM REAL_ADD, REAL_RDISTRIB] THEN
       REWRITE_TAC [REAL_MUL_LID, ← GSYM REAL_ADD_ASSOC] THEN
       REWRITE_TAC [REAL_HALF_DOUBLE] THEN
       REWRITE_TAC [← GSYM REAL_NOT_LE, REAL_LE_ADDL] THEN
       MATCH_MP_TAC REAL_LE_MUL THEN
       REWRITE_TAC [REAL_LE, LE_0] THEN
       MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC [PI2_BOUNDS],
       UNDISCH_TAC (← q r"&0 < acs(x)") THEN ASM_REWRITE_TAC [] THEN
       REWRITE_TAC [REAL_NOT_LT] THEN ONCE_REWRITE_TAC [← GSYM REAL_LE_NEG2] THEN
       REWRITE_TAC [REAL_NEG_NEG, REAL_NEG_LMUL, REAL_NEG_0] THEN
       MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC [REAL_LE, LE_0] THEN
       MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC [PI2_BOUNDS]])

  let DIFF_ACS_SIN ← prove
   r"!x. --(&1) < x /\ x < &1 ==> (acs diffl (inv(--(sin(acs x)))))(x)"
   (REPEAT STRIP_TAC THEN
    EVERY_ASSUM (ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
    MP_TAC (← SPEC (← q "x:real") ACS_COS) THEN ASM_REWRITE_TAC [] THEN
    DISCH_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [← GSYM th])) THEN
    MATCH_MP_TAC DIFF_INVERSE_LT THEN
    MP_TAC (← SPEC (← q "x:real") ACS_BOUNDS_LT) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (STRIP_ASSUME_TAC th THEN MP_TAC (← MATCH_MP INTERVAL_LEMMA_LT th))) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "d:real") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN (ASSUME_TAC o ONCE_REWRITE_RULE [ABS_SUB]) THEN
    EXISTS_TAC (← q "d:real") THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC COS_ACS THEN
      FIRST_ASSUM (undischCheck (fun c => pure (is_forall c))) THEN
      DISCH_THEN (MP_TAC o SPEC (← q "z:real")) THEN ASM_REWRITE_TAC [] THEN
      DISCH_TAC THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC [],
      MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC (← q "--(sin(z))") THEN
      REWRITE_TAC [DIFF_COS],
      REWRITE_TAC [DIFF_COS],
      POP_ASSUM MP_TAC THEN REWRITE_TAC [] THEN
      ONCE_REWRITE_TAC [← GSYM REAL_EQ_NEG] THEN
      REWRITE_TAC [REAL_NEG_NEG, REAL_NEG_0] THEN
      MATCH_MP_TAC SIN_ACS_NZ THEN ASM_REWRITE_TAC []])

  let DIFF_ACS ← prove
   r"!x. --(&1) < x /\ x < &1 ==> (acs diffl --(inv(sqrt(&1 - (x pow 2)))))(x)"
   (GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP DIFF_ACS_SIN) THEN
    MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    IMP_SUBST_TAC (← GSYM REAL_NEG_INV) THENL
     [CONV_TAC (RAND_CONV SYM_CONV) THEN
      MATCH_MP_TAC SIN_ACS_NZ THEN ASM_REWRITE_TAC [],
      REPEAT AP_TERM_TAC] THEN
    SUBGOAL_THEN (← q "cos(acs x) = x") MP_TAC THENL
     [MATCH_MP_TAC ACS_COS THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC [],
      DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC
        (RAND_CONV o ONCE_DEPTH_CONV) [← GSYM th])) THEN
      MATCH_MP_TAC SIN_COS_SQRT THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP ACS_BOUNDS_LT) THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC SIN_POS_PI THEN
      ASM_REWRITE_TAC []])

  -- `let DIFF_ACS_COMPOSITE = prove (...) in add_to_diff_net ...`: a local
  -- binding, not exported.
  let _DIFF_ACS_COMPOSITE ← prove
   r"(g diffl m)(x) /\ -- &1 < g(x) /\ g(x) < &1
   ==> ((\x. acs(g x)) diffl (--inv(sqrt(&1 - g(x) pow 2)) * m))(x)"
   (ASM_SIMP_TAC [DIFF_CHAIN, DIFF_ACS])
  add_to_diff_net _DIFF_ACS_COMPOSITE

  -- Back to normal service!

  extend_basic_rewrites [BETA_THM]

  -- A kind of inverse to SIN_CIRCLE

  let CIRCLE_SINCOS ← prove
   r"!x y. (x pow 2 + y pow 2 = &1) ==> ?t. (x = cos(t)) /\ (y = sin(t))"
   (← do
    -- The REAL_ARITHs in OCaml's order: the THEN chain and THENL lists are
    -- built right to left.
    let rb ← REAL_ARITH (← q r"~(&0 <= y) /\ (abs(y) = x) ==> (y = --x)")
    let ra ← REAL_ARITH (← q r"&0 <= y /\ (abs(y) = x) ==> (y = x)")
    let rs ← REAL_ARITH (← q r"abs(x) <= &1 ==> --(&1) <= x /\ x <= &1")
    let r1 ← REAL_ARITH
     (← q r"(&1 < x ==> &1 < x pow 2) /\ (&1 < y ==> &1 < y pow 2) /\
        &0 <= x pow 2 /\ &0 <= y pow 2 /\ x pow 2 + y pow 2 <= &1
        ==> x <= &1 /\ y <= &1")
    let one ← SYM (← ExceptT.mk (REAL_RAT_REDUCE_CONV (← q r"&1 * &1")))
    pure (REPEAT STRIP_TAC THEN
      SUBGOAL_THEN (← q r"abs(x) <= &1 /\ abs(y) <= &1") STRIP_ASSUME_TAC THENL
       [MATCH_MP_TAC r1 THEN
        ASM_REWRITE_TAC [REAL_POW2_ABS, REAL_LE_REFL] THEN
        REWRITE_TAC [REAL_POW_2, REAL_LE_SQUARE] THEN
        REWRITE_TAC [← GSYM REAL_POW_2] THEN
        ONCE_REWRITE_TAC [← GSYM REAL_POW2_ABS] THEN REWRITE_TAC [REAL_POW_2] THEN
        CONJ_TAC THEN DISCH_TAC THEN
        SUBST1_TAC one THEN
        MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REWRITE_TAC [REAL_POS],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"&0 <= sin(acs x)") MP_TAC THENL
       [MATCH_MP_TAC SIN_POS_PI_LE THEN
        MATCH_MP_TAC ACS_BOUNDS THEN
        POP_ASSUM_LIST (fun ths => tactic_of do pure (MP_TAC (← endItlistM CONJ ths))) THEN
        REAL_ARITH_TAC,
        ALL_TAC] THEN
      DISCH_THEN (ASSUME_TAC o MATCH_MP SIN_COS_SQRT) THEN
      SUBGOAL_THEN (← q r"abs(y) = sqrt(&1 - x pow 2)") ASSUME_TAC THENL
       [REWRITE_TAC [← GSYM POW_2_SQRT_ABS] THEN AP_TERM_TAC THEN
        UNDISCH_TAC (← q r"x pow 2 + y pow 2 = &1") THEN REAL_ARITH_TAC,
        ALL_TAC] THEN
      ASM_CASES_TAC (← q r"&0 <= y") THENL
       [EXISTS_TAC (← q "acs x"), EXISTS_TAC (← q "--(acs x)")] THEN
      ASM_SIMP_TAC [COS_NEG, SIN_NEG, ACS_COS, rs]
      THENL
       [MATCH_MP_TAC ra,
        MATCH_MP_TAC rb] THEN
      ASM_REWRITE_TAC []))

  -- More lemmas.

  let ACS_MONO_LT ← prove
   r"!x y. --(&1) < x /\ x < y /\ y < &1 ==> acs(y) < acs(x)"
   (← do
    -- The later rule in the THEN chain is evaluated first.
    let r2 ← REAL_ARITH (← q r"&0 < &1 - z * z <=> z * z < &1 * &1")
    let r1 ← REAL_ARITH (← q r"a * --c + x < x <=> &0 < a * c")
    pure (REPEAT STRIP_TAC THEN
      MP_TAC (← SPECL [← q "acs", ← q r"\x. --inv(sqrt(&1 - x pow 2))", ← q "x:real", ← q "y:real"]
                   MVT_ALT) THEN
      ANTS_TAC THENL
       [REPEAT STRIP_TAC THEN ASM_SIMP_TAC [] THEN
        MATCH_MP_TAC DIFF_ACS THEN
        ASM_MESON_TAC [REAL_LET_TRANS, REAL_LTE_TRANS],
        REWRITE_TAC [REAL_EQ_SUB_RADD]] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "z:real") STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC [r1] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC [REAL_SUB_LT] THEN
      MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
      ONCE_REWRITE_TAC [← GSYM REAL_POW2_ABS] THEN REWRITE_TAC [REAL_POW_2] THEN
      REWRITE_TAC [r2] THEN
      MATCH_MP_TAC REAL_LT_MUL2 THEN REWRITE_TAC [REAL_ABS_POS] THEN
      POP_ASSUM_LIST (fun ths => tactic_of do pure (MP_TAC (← endItlistM CONJ ths))) THEN
      REAL_ARITH_TAC))

  -- Formalization of Kurzweil-Henstock gauge integral

  let LE_MATCH_TAC : thm_tactic ← pure (fun th gl => ExceptT.run do
    let w := gl.2
    let thi ← PART_MATCH (fun t => do rand (← rator t)) th (← liftExcept (do rand (← rator w)))
    let tm ← liftExcept (rand (concl thi))
    ExceptT.mk ((MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC tm THEN CONJ_TAC THENL
      [MATCH_ACCEPT_TAC th, ALL_TAC]) gl))

  -- Some miscellaneous lemmas

  let LESS_SUC_EQ ← prove
   r"!m n. m < SUC n <=> m <= n"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← CONJUNCT2 LT, LE_LT] THEN
    EQ_TAC THEN DISCH_THEN (DISJ_CASES_THEN (fun th => REWRITE_TAC [th])))

  let LESS_1 ← prove
   r"!n. n < 1 <=> (n = 0)"
   (REWRITE_TAC [← numc "1", LESS_SUC_EQ, ← CONJUNCT1 LE])

  -- Divisions and tagged divisions etc.

  let division ← new_definition
   r"division(a,b) D <=>
     (D 0 = a) /\
     (?N. (!n. n < N ==> D(n) < D(SUC n)) /\
          (!n. n >= N ==> (D(n) = b)))"

  let dsize ← new_definition
   r"dsize D =
      @N. (!n. n < N ==> D(n) < D(SUC n)) /\
          (!n. n >= N ==> (D(n) = D(N)))"

  let tdiv ← new_definition
   r"tdiv(a,b) (D,p) <=>
     division(a,b) D /\
     (!n. D(n) <= p(n) /\ p(n) <= D(SUC n))"

  -- Gauges and gauge-fine divisions

  let gauge ← new_definition
   r"gauge(E) (g:real->real) <=> !x. E x ==> &0 < g(x)"

  let fine ← new_definition
   r"fine(g:real->real) (D,p) <=>
     !n. n < (dsize D) ==> (D(SUC n) - D(n)) < g(p(n))"

  -- Riemann sum

  let rsum ← new_definition
   r"rsum (D,(p:num->real)) f =
        sum(0,dsize(D))(\n. f(p n) * (D(SUC n) - D(n)))"

  -- Gauge integrability (definite)

  let defint ← new_definition
   r"defint(a,b) f k <=>
     !e. &0 < e ==>
        ?g. gauge(\x. a <= x /\ x <= b) g /\
            !D p. tdiv(a,b) (D,p) /\ fine(g)(D,p) ==>
                abs(rsum(D,p) f - k) < e"

  -- @@RETURN BEGIN
  return { COS_SIN_SQRT, COS_ASN_NZ, DIFF_ASN_COS, DIFF_ASN, SIN_COS_SQRT, SIN_ACS_NZ,
           DIFF_ACS_SIN, DIFF_ACS, CIRCLE_SINCOS, ACS_MONO_LT, LE_MATCH_TAC, LESS_SUC_EQ,
           LESS_1, division, dsize, tdiv, gauge, fine, rsum, defint }
  -- @@RETURN END

/-- lib.ml's `el n` on a list of theorems. -/
def elThm (n : Nat) (l : List thm) : ExceptT String IO thm :=
  match l[n]? with
  | some x => pure x
  | none => throw "el"

/-- lib.ml's `last` on a list of theorems. -/
def lastThm (l : List thm) : ExceptT String IO thm :=
  match l.getLast? with
  | some x => pure x
  | none => throw "last"

/- ------------------------------------------------------------------------- -/
/- Useful lemmas about the size of `trivial` divisions etc.                  -/
/- (transc.ml 3464-3745)                                                     -/
/- ------------------------------------------------------------------------- -/

structure Division where
  -- @@FIELDS
  DIVISION_0 : thm
  DIVISION_1 : thm
  DIVISION_SINGLE : thm
  DIVISION_LHS : thm
  DIVISION_THM : thm
  DIVISION_RHS : thm
  DIVISION_LT_GEN : thm
  DIVISION_LT : thm
  DIVISION_LE : thm
  DIVISION_GT : thm
  DIVISION_EQ : thm
  DIVISION_LBOUND : thm
  DIVISION_LBOUND_LT : thm
  DIVISION_UBOUND : thm
  DIVISION_UBOUND_LT : thm
  deriving Inhabited

@[nospecialize]
def setupDivision [HolBase] (D : TranscDeps) (BArcSinCos : ArcSinCos) (ANames : HolLibrary.Analysis.Names) (AReals1 : HolLibrary.Analysis.Reals1) (AReals2 : HolLibrary.Analysis.Reals2) :
    ExceptT String IO Division := do
  -- @@SCOPE BEGIN
  let { INDUCT_TAC, num_CONV, .. } := D
  let { ADD1, ADD_CLAUSES, ADD_SUB, ADD_SYM, ARITH, COND_ID, EQ_IMP, GE, LE, LE_0,
        LE_LT, LE_REFL, LE_SUC, LE_TRANS, LT, LTE_CASES, LT_IMP_LE, LT_TRANS, NOT_IMP,
        NOT_LE, NOT_LT, NOT_SUC, PRE, num_CASES, .. } := D.core1
  let { REAL_EQ_IMP_LE, REAL_LT_REFL, REAL_LT_TRANS, RIGHT_FORALL_IMP_THM,
        SELECT_UNIQUE, SUB_0, SUB_EQ_0, SUB_SUC, .. } := D.core2
  let { LESS_1, division, dsize, .. } := BArcSinCos
  let { LESS_ADD_1, LESS_CASES_IMP, LESS_EQUAL_ANTISYM, LESS_EQ_SUC_REFL,
        LESS_LESS_CASES, LESS_SUC_REFL, NOT_LESS_0, NOT_SUC_LESS_EQ, OR_LESS,
        SUB_EQ_EQ_0, SUB_LESS_EQ, SUB_OLD, SUB_SUB, .. } := ANames
  let { REAL_LE_LT, REAL_LE_REFL, REAL_LE_TRANS, REAL_LT_IMP_LE, .. } := AReals1
  let { REAL_LT_IMP_NE, .. } := AReals2
  -- @@SCOPE END
  let numc (s : String) : ExceptT String IO thm := do ExceptT.mk (num_CONV (← q s))

  let DIVISION_0 ← prove
   r"!a b. (a = b) ==> (dsize(\n. if (n = 0) then a else b) = 0)"
   (REPEAT GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC [COND_ID] THEN
    REWRITE_TAC [dsize] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    X_GEN_TAC (← q "n:num") THEN BETA_TAC THEN
    REWRITE_TAC [REAL_LT_REFL, NOT_LT] THEN EQ_TAC THENL
     [DISCH_THEN (MP_TAC o SPEC (← q "0")) THEN REWRITE_TAC [← CONJUNCT1 LE],
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [LE_0]])

  let DIVISION_1 ← prove
   r"!a b. a < b ==> (dsize(\n. if (n = 0) then a else b) = 1)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [dsize] THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC (← q "n:num") THEN BETA_TAC THEN
    REWRITE_TAC [NOT_SUC] THEN EQ_TAC THENL
     [DISCH_TAC THEN MATCH_MP_TAC LESS_EQUAL_ANTISYM THEN CONJ_TAC THENL
       [POP_ASSUM (MP_TAC o SPEC (← q "1") o CONJUNCT1) THEN
        REWRITE_TAC [ARITH] THEN
        REWRITE_TAC [REAL_LT_REFL, NOT_LT],
        POP_ASSUM (MP_TAC o SPEC (← q "2") o CONJUNCT2) THEN
        REWRITE_TAC [← numc "2", GE] THEN
        CONV_TAC CONTRAPOS_CONV THEN
        REWRITE_TAC [← numc "1", NOT_SUC_LESS_EQ, ← CONJUNCT1 LE] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [NOT_SUC, NOT_IMP] THEN
        REWRITE_TAC [LE_0] THEN CONV_TAC (RAND_CONV SYM_CONV) THEN
        MATCH_MP_TAC REAL_LT_IMP_NE THEN POP_ASSUM ACCEPT_TAC],
      DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC [← numc "1", ← CONJUNCT2 LT, NOT_LESS_0] THEN
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [],
        X_GEN_TAC (← q "n:num") THEN REWRITE_TAC [GE, ← numc "1"] THEN
        ASM_CASES_TAC (← q "n = 0") THEN
        ASM_REWRITE_TAC [← CONJUNCT1 LE, ← GSYM NOT_SUC, NOT_SUC]]])

  let DIVISION_SINGLE ← prove
   r"!a b. a <= b ==> division(a,b)(\n. if (n = 0) then a else b)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [division] THEN
    BETA_TAC THEN REWRITE_TAC [] THEN
    POP_ASSUM (DISJ_CASES_TAC o REWRITE_RULE [REAL_LE_LT]) THENL
     [EXISTS_TAC (← q "1") THEN CONJ_TAC THEN X_GEN_TAC (← q "n:num") THENL
       [REWRITE_TAC [LESS_1] THEN DISCH_THEN SUBST1_TAC THEN
        ASM_REWRITE_TAC [NOT_SUC],
        REWRITE_TAC [GE] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [← numc "1"] THEN
        REWRITE_TAC [← GSYM NOT_LT, LESS_SUC_REFL]],
      EXISTS_TAC (← q "0") THEN REWRITE_TAC [NOT_LESS_0] THEN
      ASM_REWRITE_TAC [COND_ID]])

  let DIVISION_LHS ← prove
   r"!D a b. division(a,b) D ==> (D(0) = a)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [division] THEN
    DISCH_THEN (fun th => REWRITE_TAC [th]))

  let DIVISION_THM ← prove
   r"!D a b. division(a,b) D <=>
        (D(0) = a) /\
        (!n. n < (dsize D) ==> D(n) < D(SUC n)) /\
        (!n. n >= (dsize D) ==> (D(n) = b))"
   (← do
    let aN ← ASSUME (← q r"!n:num. n >= N ==> (D n :real = b)")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [division] THEN
      EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THENL
       [ALL_TAC, EXISTS_TAC (← q "dsize D") THEN ASM_REWRITE_TAC []] THEN
      POP_ASSUM (X_CHOOSE_THEN (← q "N:num") STRIP_ASSUME_TAC o CONJUNCT2) THEN
      SUBGOAL_THEN (← q "dsize D = N") (fun th => ASM_REWRITE_TAC [th]) THEN
      REWRITE_TAC [dsize] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
      X_GEN_TAC (← q "M:num") THEN BETA_TAC THEN EQ_TAC THENL
       [ALL_TAC, DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [] THEN
        MP_TAC (← SPEC (← q "N:num") aN) THEN
        DISCH_THEN (MP_TAC o REWRITE_RULE [GE, LE_REFL]) THEN
        DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC] THEN
      REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
       (← SPECL [← q "M:num", ← q "N:num"] LESS_LESS_CASES) THEN
      ASM_REWRITE_TAC [] THENL
       [DISCH_THEN (MP_TAC o SPEC (← q "SUC M") o CONJUNCT2) THEN
        REWRITE_TAC [GE, LESS_EQ_SUC_REFL] THEN DISCH_TAC THEN
        UNDISCH_TAC (← q r"!n. n < N ==> (D n) < (D(SUC n))") THEN
        DISCH_THEN (MP_TAC o SPEC (← q "M:num")) THEN ASM_REWRITE_TAC [REAL_LT_REFL],
        DISCH_THEN (MP_TAC o SPEC (← q "N:num") o CONJUNCT1) THEN ASM_REWRITE_TAC [] THEN
        UNDISCH_TAC (← q r"!n:num. n >= N ==> (D n :real = b)") THEN
        DISCH_THEN (fun th => tactic_of do
          let b2 ← SPEC (← q "SUC N") th
          let b1 ← SPEC (← q "N:num") th
          pure (MP_TAC b1 THEN MP_TAC b2)) THEN
        REWRITE_TAC [GE, LESS_EQ_SUC_REFL, LE_REFL] THEN
        DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC [REAL_LT_REFL]]))

  let DIVISION_RHS ← prove
   r"!D a b. division(a,b) D ==> (D(dsize D) = b)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [DIVISION_THM] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (MP_TAC (← SPEC (← q "dsize D") (← lastThm (CONJUNCTS th))))) THEN
    REWRITE_TAC [GE, LE_REFL])

  let DIVISION_LT_GEN ← prove
   r"!D a b m n. division(a,b) D /\
               m < n /\
               n <= (dsize D) ==> D(m) < D(n)"
   (REPEAT STRIP_TAC THEN UNDISCH_TAC (← q "m:num < n") THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "d:num") MP_TAC o MATCH_MP LESS_ADD_1) THEN
    REWRITE_TAC [← GSYM ADD1] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC (← q "(m + (SUC d)) <= (dsize D)") THEN
    SPEC_TAC (← q "d:num", ← q "d:num") THEN INDUCT_TAC THENL
     [REWRITE_TAC [ADD_CLAUSES] THEN
      DISCH_THEN (MP_TAC o MATCH_MP OR_LESS) THEN
      RULE_ASSUM_TAC (REWRITE_RULE [DIVISION_THM]) THEN
      ASM_REWRITE_TAC [],
      REWRITE_TAC [ADD_CLAUSES] THEN
      DISCH_THEN (MP_TAC o MATCH_MP OR_LESS) THEN
      DISCH_TAC THEN MATCH_MP_TAC REAL_LT_TRANS THEN
      EXISTS_TAC (← q r"D(m + (SUC d)):real") THEN CONJ_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [ADD_CLAUSES] THEN
        MATCH_MP_TAC LT_IMP_LE THEN ASM_REWRITE_TAC [],
        REWRITE_TAC [ADD_CLAUSES] THEN
        FIRST_ASSUM (fun th => tactic_of do
          pure (MATCH_MP_TAC (← elThm 1 (CONJUNCTS (← REWRITE_RULE [DIVISION_THM] th))))) THEN
        ASM_REWRITE_TAC []]])

  let DIVISION_LT ← prove
   r"!D a b. division(a,b) D ==> !n. n < (dsize D) ==> D(0) < D(SUC n)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [DIVISION_THM] THEN STRIP_TAC THEN
    INDUCT_TAC THEN DISCH_THEN (fun th => ASSUME_TAC th THEN
        FIRST_ASSUM (MP_TAC o (fun a => MATCH_MP a th))) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (← q r"D(SUC n):real") THEN
    ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"D(0):real = a") THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC (← q "SUC n") THEN
    ASM_REWRITE_TAC [LESS_SUC_REFL])

  let DIVISION_LE ← prove
   r"!D a b. division(a,b) D ==> a <= b"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP DIVISION_LT) THEN
    POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [DIVISION_THM]) THEN
    UNDISCH_TAC (← q r"D(0):real = a") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    UNDISCH_TAC (← q r"!n. n >= (dsize D) ==> (D n = b)") THEN
    DISCH_THEN (MP_TAC o SPEC (← q "dsize D")) THEN
    REWRITE_TAC [GE, LE_REFL] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    DISCH_THEN (MP_TAC o SPEC (← q "PRE(dsize D)")) THEN
    STRUCT_CASES_TAC (← SPEC (← q "dsize D") num_CASES) THEN
    ASM_REWRITE_TAC [PRE, REAL_LE_REFL, LESS_SUC_REFL, REAL_LT_IMP_LE])

  let DIVISION_GT ← prove
   r"!D a b. division(a,b) D ==> !n. n < (dsize D) ==> D(n) < D(dsize D)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC DIVISION_LT_GEN THEN
    MAP_EVERY EXISTS_TAC [← q "a:real", ← q "b:real"] THEN
    ASM_REWRITE_TAC [LE_REFL])

  let DIVISION_EQ ← prove
   r"!D a b. division(a,b) D ==> ((a = b) <=> (dsize D = 0))"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP DIVISION_LT) THEN
    POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [DIVISION_THM]) THEN
    UNDISCH_TAC (← q r"D(0):real = a") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    UNDISCH_TAC (← q r"!n. n >= (dsize D) ==> (D n = b)") THEN
    DISCH_THEN (MP_TAC o SPEC (← q "dsize D")) THEN
    REWRITE_TAC [GE, LE_REFL] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    DISCH_THEN (MP_TAC o SPEC (← q "PRE(dsize D)")) THEN
    STRUCT_CASES_TAC (← SPEC (← q "dsize D") num_CASES) THEN
    ASM_REWRITE_TAC [PRE, NOT_SUC, LESS_SUC_REFL, REAL_LT_IMP_NE])

  let DIVISION_LBOUND ← prove
   r"!D a b r. division(a,b) D ==> a <= D(r)"
   (REWRITE_TAC [DIVISION_THM, RIGHT_FORALL_IMP_THM] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC [REAL_LE_REFL] THEN
    DISJ_CASES_TAC (← SPECL [← q "SUC r", ← q "dsize D"] LTE_CASES) THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"(D:num->real) r") THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC (← q "SUC r") THEN
      ASM_REWRITE_TAC [LESS_SUC_REFL],
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "b:real") THEN CONJ_TAC THENL
       [MATCH_MP_TAC DIVISION_LE THEN
        EXISTS_TAC (← q r"D:num->real") THEN ASM_REWRITE_TAC [DIVISION_THM],
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [GE]]])

  let DIVISION_LBOUND_LT ← prove
   r"!D a b n. division(a,b) D /\ ~(dsize D = 0) ==> a < D(SUC n)"
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM (SUBST1_TAC o SYM o MATCH_MP DIVISION_LHS) THEN
    DISJ_CASES_TAC (← SPECL [← q "dsize D", ← q "SUC n"] LTE_CASES) THENL
     [FIRST_ASSUM (fun th => tactic_of do
        pure (MP_TAC (← elThm 2 (CONJUNCTS (← REWRITE_RULE [DIVISION_THM] th))))) THEN
      DISCH_THEN (MP_TAC o SPEC (← q "SUC n")) THEN REWRITE_TAC [GE] THEN
      IMP_RES_THEN ASSUME_TAC LT_IMP_LE THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN SUBST1_TAC THEN
      FIRST_ASSUM (SUBST1_TAC o SYM o MATCH_MP DIVISION_RHS) THEN
      FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP DIVISION_GT) THEN
      ASM_REWRITE_TAC [← GSYM NOT_LE, ← CONJUNCT1 LE],
      FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP DIVISION_LT) THEN
      MATCH_MP_TAC OR_LESS THEN ASM_REWRITE_TAC []])

  let DIVISION_UBOUND ← prove
   r"!D a b r. division(a,b) D ==> D(r) <= b"
   (REWRITE_TAC [DIVISION_THM] THEN REPEAT STRIP_TAC THEN
    DISJ_CASES_TAC (← SPECL [← q "r:num", ← q "dsize D"] LTE_CASES) THENL
     [ALL_TAC,
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [GE]] THEN
    SUBGOAL_THEN (← q "!r. D((dsize D) - r) <= b") MP_TAC THENL
     [ALL_TAC,
      DISCH_THEN (MP_TAC o SPEC (← q "(dsize D) - r")) THEN
      MATCH_MP_TAC EQ_IMP THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP SUB_SUB
        (← MATCH_MP LT_IMP_LE th)])) THEN
      ONCE_REWRITE_TAC [ADD_SYM] THEN REWRITE_TAC [ADD_SUB]] THEN
    UNDISCH_TAC (← q "r < (dsize D)") THEN DISCH_THEN (fun _ => ALL_TAC) THEN
    INDUCT_TAC THENL
     [REWRITE_TAC [SUB_0] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [GE, LE_REFL],
      ALL_TAC] THEN
    DISJ_CASES_TAC (← SPECL [← q "r:num", ← q "dsize D"] LTE_CASES) THENL
     [ALL_TAC,
      SUBGOAL_THEN (← q "(dsize D) - (SUC r) = 0") SUBST1_TAC THENL
       [REWRITE_TAC [SUB_EQ_0] THEN MATCH_MP_TAC LE_TRANS THEN
        EXISTS_TAC (← q "r:num") THEN ASM_REWRITE_TAC [LESS_EQ_SUC_REFL],
        ASM_REWRITE_TAC [] THEN MATCH_MP_TAC DIVISION_LE THEN
        EXISTS_TAC (← q r"D:num->real") THEN ASM_REWRITE_TAC [DIVISION_THM]]] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"D((dsize D) - r):real") THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q "(dsize D) - r = SUC((dsize D) - (SUC r))")
    SUBST1_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC LESS_CASES_IMP THEN
      REWRITE_TAC [NOT_LT, LE_LT, SUB_LESS_EQ] THEN
      CONV_TAC (RAND_CONV SYM_CONV) THEN
      REWRITE_TAC [SUB_EQ_EQ_0, NOT_SUC] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC (← q "r < 0") THEN REWRITE_TAC [NOT_LESS_0]] THEN
    MP_TAC (← SPECL [← q "dsize D", ← q "SUC r"] (← CONJUNCT2 SUB_OLD)) THEN
    COND_CASES_TAC THENL
     [REWRITE_TAC [SUB_EQ_0, LE_SUC] THEN
      ASM_REWRITE_TAC [← GSYM NOT_LT],
      DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [SUB_SUC]])

  let DIVISION_UBOUND_LT ← prove
   r"!D a b n. division(a,b) D /\
             n < dsize D ==> D(n) < b"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (SUBST1_TAC o SYM o MATCH_MP DIVISION_RHS) THEN
    FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP DIVISION_GT) THEN
    ASM_REWRITE_TAC [])

  -- @@RETURN BEGIN
  return { DIVISION_0, DIVISION_1, DIVISION_SINGLE, DIVISION_LHS, DIVISION_THM,
           DIVISION_RHS, DIVISION_LT_GEN, DIVISION_LT, DIVISION_LE, DIVISION_GT,
           DIVISION_EQ, DIVISION_LBOUND, DIVISION_LBOUND_LT, DIVISION_UBOUND,
           DIVISION_UBOUND_LT }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Divisions of adjacent intervals can be combined into one; we can always   -/
/- find a division which is fine wrt any gauge.  (transc.ml 3747-4060)       -/
/- ------------------------------------------------------------------------- -/

structure DivAppend where
  -- @@FIELDS
  DIVISION_APPEND_LEMMA1 : thm
  DIVISION_APPEND_LEMMA2 : thm
  DIVISION_APPEND_EXPLICIT : thm
  DIVISION_APPEND_STRONG : thm
  DIVISION_APPEND : thm
  DIVISION_EXISTS : thm
  deriving Inhabited

@[nospecialize]
def setupDivAppend [HolBase] (D : TranscDeps) (BArcSinCos : ArcSinCos) (BDivision : Division) (ANames : HolLibrary.Analysis.Names) (AReals1 : HolLibrary.Analysis.Reals1) (ASums : HolLibrary.Analysis.Sums) (ASeries1 : HolLibrary.Analysis.Series1) :
    ExceptT String IO DivAppend := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, GEN_BETA_CONV, MESON_TAC, num_CONV, .. } := D
  let { ADD_ASSOC, ADD_CLAUSES, ADD_SUB, ADD_SYM, CONJ_ASSOC, DE_MORGAN_THM, GE,
        LET_TRANS, LE_0, LE_ADD, LE_EXISTS, LE_REFL, LE_SUC_LT, LE_TRANS, LT,
        LTE_TRANS, LT_ADD_RCANCEL, LT_IMP_LE, LT_TRANS, NOT_LE, NOT_LT, NOT_SUC, .. } := D.core1
  let { REAL_LET_TRANS, REAL_LT_REFL, SELECT_UNIQUE, SUB_0, SUB_REFL, .. } := D.core2
  let { dsize, fine, gauge, rsum, tdiv, .. } := BArcSinCos
  let { DIVISION_0, DIVISION_1, DIVISION_EQ, DIVISION_LBOUND, DIVISION_LHS,
        DIVISION_LT_GEN, DIVISION_RHS, DIVISION_SINGLE, DIVISION_THM,
        DIVISION_UBOUND_LT, .. } := BDivision
  let { LESS_0_CASES, LESS_EQUAL_ANTISYM, LESS_EQ_SUC_REFL, LESS_OR, LESS_SUC_REFL,
        NOT_LESS_0, SUB_LEFT_GREATER_EQ, SUB_LEFT_LESS_EQ, SUB_OLD, .. } := ANames
  let { REAL_LE_LT, REAL_LE_REFL, REAL_LE_TRANS, REAL_LTE_TRANS, REAL_LT_01,
        REAL_NOT_LE, .. } := AReals1
  let { SUM_EQ, SUM_REINDEX, SUM_SPLIT, .. } := ASums
  let { BOLZANO_LEMMA, .. } := ASeries1
  -- @@SCOPE END
  let numc (s : String) : ExceptT String IO thm := do ExceptT.mk (num_CONV (← q s))
  -- `W(C SUBGOAL_THEN ttac o funpow 2 (fst o dest_imp) o snd)`
  let subgoalAnte2 (ttac : thm_tactic) : tactic := fun gl => ExceptT.run do
    let t ← liftExcept (funpow 2 (fun (m : Except String term) => do
      pure (← dest_imp (← m)).1) (pure gl.2))
    ExceptT.mk (SUBGOAL_THEN t ttac gl)
  let el2DivThm (th : thm) : ExceptT String IO thm := do
    elThm 2 (CONJUNCTS (← REWRITE_RULE [DIVISION_THM] th))
  let el1DivThm (th : thm) : ExceptT String IO thm := do
    elThm 1 (CONJUNCTS (← REWRITE_RULE [DIVISION_THM] th))

  let DIVISION_APPEND_LEMMA1 ← prove
   r"!a b c D1 D2. division(a,b) D1 /\ division(b,c) D2 ==>
        (!n. n < ((dsize D1) + (dsize D2)) ==>
                (\n. if (n < (dsize D1)) then  D1(n) else
                     D2(n - (dsize D1)))(n) <
   (\n. if (n < (dsize D1)) then  D1(n) else D2(n - (dsize D1)))(SUC n)) /\
        (!n. n >= ((dsize D1) + (dsize D2)) ==>
               ((\n. if (n < (dsize D1)) then  D1(n) else
   D2(n - (dsize D1)))(n) = (\n. if (n < (dsize D1)) then  D1(n) else
   D2(n - (dsize D1)))((dsize D1) + (dsize D2))))"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN
    X_GEN_TAC (← q "n:num") THEN DISCH_TAC THEN BETA_TAC THENL
     [ASM_CASES_TAC (← q "(SUC n) < (dsize D1)") THEN ASM_REWRITE_TAC [] THENL
       [SUBGOAL_THEN (← q "n < (dsize D1)") ASSUME_TAC THEN
        ASM_REWRITE_TAC [] THENL
         [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC (← q "SUC n") THEN
          ASM_REWRITE_TAC [LESS_SUC_REFL],
          UNDISCH_TAC (← q "division(a,b) D1") THEN REWRITE_TAC [DIVISION_THM] THEN
          STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
          FIRST_ASSUM ACCEPT_TAC],
        ASM_CASES_TAC (← q "n < (dsize D1)") THEN ASM_REWRITE_TAC [] THENL
         [RULE_ASSUM_TAC (REWRITE_RULE [NOT_LT]) THEN
          MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q "b:real") THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC DIVISION_UBOUND_LT THEN
            EXISTS_TAC (← q "a:real") THEN ASM_REWRITE_TAC [],
            MATCH_MP_TAC DIVISION_LBOUND THEN
            EXISTS_TAC (← q "c:real") THEN ASM_REWRITE_TAC []],
          UNDISCH_TAC (← q "~(n < (dsize D1))") THEN
          REWRITE_TAC [NOT_LT] THEN
          DISCH_THEN (X_CHOOSE_THEN (← q "d:num") SUBST_ALL_TAC o
            REWRITE_RULE [LE_EXISTS]) THEN
          REWRITE_TAC [SUB_OLD, ← GSYM NOT_LE, LE_ADD] THEN
          ONCE_REWRITE_TAC [ADD_SYM] THEN REWRITE_TAC [ADD_SUB] THEN
          FIRST_ASSUM (fun th => tactic_of do pure (MATCH_MP_TAC (← el1DivThm th))) THEN
          UNDISCH_TAC (← q r"((dsize D1) + d) <
                       ((dsize D1) + (dsize D2))") THEN
          ONCE_REWRITE_TAC [ADD_SYM] THEN REWRITE_TAC [LT_ADD_RCANCEL]]],
      REWRITE_TAC [← GSYM NOT_LE, LE_ADD] THEN
      ONCE_REWRITE_TAC [ADD_SYM] THEN REWRITE_TAC [ADD_SUB] THEN
      REWRITE_TAC [NOT_LE] THEN COND_CASES_TAC THEN
      UNDISCH_TAC (← q "n >= ((dsize D1) + (dsize D2))") THENL
       [CONV_TAC CONTRAPOS_CONV THEN DISCH_TAC THEN
        REWRITE_TAC [GE, NOT_LE] THEN
        MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC (← q "dsize D1") THEN
        ASM_REWRITE_TAC [LE_ADD],
        REWRITE_TAC [GE, LE_EXISTS] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "d:num") SUBST_ALL_TAC) THEN
        REWRITE_TAC [← GSYM ADD_ASSOC] THEN ONCE_REWRITE_TAC [ADD_SYM] THEN
        REWRITE_TAC [ADD_SUB] THEN
        FIRST_ASSUM (CHANGED_TAC o
         (SUBST1_TAC o MATCH_MP DIVISION_RHS)) THEN
        FIRST_ASSUM (fun th => tactic_of do pure (MATCH_MP_TAC (← el2DivThm th))) THEN
        REWRITE_TAC [GE, LE_ADD]]])

  let DIVISION_APPEND_LEMMA2 ← prove
   r"!a b c D1 D2. division(a,b) D1 /\ division(b,c) D2 ==>
                   (dsize(\n. if (n < (dsize D1)) then  D1(n) else
       D2(n - (dsize D1))) = dsize(D1) + dsize(D2))"
   (← do
    let aD2 ← ASSUME (← q "division(b,c) D2")
    pure (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [dsize] THEN
      MATCH_MP_TAC SELECT_UNIQUE THEN
      X_GEN_TAC (← q "N:num") THEN BETA_TAC THEN EQ_TAC THENL
       [DISCH_THEN (fun th => MATCH_MP_TAC LESS_EQUAL_ANTISYM THEN MP_TAC th) THEN
        CONV_TAC CONTRAPOS_CONV THEN
        REWRITE_TAC [DE_MORGAN_THM, NOT_LE] THEN
        DISCH_THEN DISJ_CASES_TAC THENL
         [DISJ1_TAC THEN
          DISCH_THEN (MP_TAC o SPEC (← q "dsize(D1) + dsize(D2)")) THEN
          ASM_REWRITE_TAC [] THEN
          REWRITE_TAC [← GSYM NOT_LE, LE_ADD] THEN
          SUBGOAL_THEN (← q "!x y. x <= SUC(x + y)") ASSUME_TAC THENL
           [REPEAT GEN_TAC THEN MATCH_MP_TAC LE_TRANS THEN
            EXISTS_TAC (← q "x + y:num") THEN
            REWRITE_TAC [LE_ADD, LESS_EQ_SUC_REFL], ALL_TAC] THEN
          ASM_REWRITE_TAC [] THEN REWRITE_TAC [SUB_OLD, ← GSYM NOT_LE] THEN
          REWRITE_TAC [LE_ADD] THEN ONCE_REWRITE_TAC [ADD_SYM] THEN
          REWRITE_TAC [ADD_SUB] THEN
          MP_TAC aD2 THEN REWRITE_TAC [DIVISION_THM] THEN
          DISCH_THEN (fun th => tactic_of do
            pure (MP_TAC (← SPEC (← q "SUC(dsize D2)") (← elThm 2 (CONJUNCTS th))))) THEN
          REWRITE_TAC [GE, LESS_EQ_SUC_REFL] THEN
          DISCH_THEN SUBST1_TAC THEN
          FIRST_ASSUM (CHANGED_TAC o SUBST1_TAC o MATCH_MP DIVISION_RHS) THEN
          REWRITE_TAC [REAL_LT_REFL],
          DISJ2_TAC THEN
          DISCH_THEN (MP_TAC o SPEC (← q "dsize(D1) + dsize(D2)")) THEN
          FIRST_ASSUM (ASSUME_TAC o MATCH_MP LT_IMP_LE) THEN
          ASM_REWRITE_TAC [GE] THEN
          REWRITE_TAC [← GSYM NOT_LE, LE_ADD] THEN
          ONCE_REWRITE_TAC [ADD_SYM] THEN REWRITE_TAC [ADD_SUB] THEN
          COND_CASES_TAC THENL
           [SUBGOAL_THEN (← q r"D1(N:num) < D2(dsize D2)") MP_TAC THENL
             [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q "b:real") THEN
              CONJ_TAC THENL
               [MATCH_MP_TAC DIVISION_UBOUND_LT THEN EXISTS_TAC (← q "a:real") THEN
                ASM_REWRITE_TAC [← GSYM NOT_LE],
                MATCH_MP_TAC DIVISION_LBOUND THEN
                EXISTS_TAC (← q "c:real") THEN ASM_REWRITE_TAC []],
              CONV_TAC CONTRAPOS_CONV THEN ASM_REWRITE_TAC [] THEN
              DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [REAL_LT_REFL]],
            RULE_ASSUM_TAC (REWRITE_RULE []) THEN
            SUBGOAL_THEN (← q "D2(N - (dsize D1)) < D2(dsize D2)") MP_TAC THENL
             [MATCH_MP_TAC DIVISION_LT_GEN THEN
              MAP_EVERY EXISTS_TAC [← q "b:real", ← q "c:real"] THEN
              ASM_REWRITE_TAC [LE_REFL] THEN
              REWRITE_TAC [← GSYM NOT_LE] THEN
              REWRITE_TAC [SUB_LEFT_LESS_EQ, DE_MORGAN_THM] THEN
              ONCE_REWRITE_TAC [ADD_SYM] THEN ASM_REWRITE_TAC [NOT_LE] THEN
              UNDISCH_TAC (← q "dsize(D1) <= N") THEN
              REWRITE_TAC [LE_EXISTS] THEN
              DISCH_THEN (X_CHOOSE_THEN (← q "d:num") SUBST_ALL_TAC) THEN
              RULE_ASSUM_TAC (ONCE_REWRITE_RULE [ADD_SYM]) THEN
              RULE_ASSUM_TAC (REWRITE_RULE [LT_ADD_RCANCEL]) THEN
              MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC (← q "d:num") THEN
              ASM_REWRITE_TAC [LE_0],
              CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC [] THEN
              DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [REAL_LT_REFL]]]],
        DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
         [X_GEN_TAC (← q "n:num") THEN DISCH_TAC THEN
          ASM_CASES_TAC (← q "(SUC n) < (dsize(D1))") THEN
          ASM_REWRITE_TAC [] THENL
           [SUBGOAL_THEN (← q "n < (dsize(D1))") ASSUME_TAC THENL
             [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC (← q "SUC n") THEN
              ASM_REWRITE_TAC [LESS_SUC_REFL], ALL_TAC] THEN
            ASM_REWRITE_TAC [] THEN MATCH_MP_TAC DIVISION_LT_GEN THEN
            MAP_EVERY EXISTS_TAC [← q "a:real", ← q "b:real"] THEN
            ASM_REWRITE_TAC [LESS_SUC_REFL] THEN
            MATCH_MP_TAC LT_IMP_LE THEN ASM_REWRITE_TAC [],
            COND_CASES_TAC THENL
             [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q "b:real") THEN
              CONJ_TAC THENL
               [MATCH_MP_TAC DIVISION_UBOUND_LT THEN EXISTS_TAC (← q "a:real") THEN
                ASM_REWRITE_TAC [],
                FIRST_ASSUM (MATCH_ACCEPT_TAC o MATCH_MP DIVISION_LBOUND)],
              MATCH_MP_TAC DIVISION_LT_GEN THEN
              MAP_EVERY EXISTS_TAC [← q "b:real", ← q "c:real"] THEN
              ASM_REWRITE_TAC [] THEN
              CONJ_TAC THENL [ASM_REWRITE_TAC [SUB_OLD, LESS_SUC_REFL], ALL_TAC] THEN
              REWRITE_TAC [← REWRITE_RULE [GE] SUB_LEFT_GREATER_EQ] THEN
              ONCE_REWRITE_TAC [ADD_SYM] THEN ASM_REWRITE_TAC [LE_SUC_LT]]],
          X_GEN_TAC (← q "n:num") THEN REWRITE_TAC [GE] THEN DISCH_TAC THEN
          REWRITE_TAC [← GSYM NOT_LE, LE_ADD] THEN
          SUBGOAL_THEN (← q "(dsize D1) <= n") ASSUME_TAC THENL
           [MATCH_MP_TAC LE_TRANS THEN
            EXISTS_TAC (← q "dsize D1 + dsize D2") THEN
            ASM_REWRITE_TAC [LE_ADD],
            ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [ADD_SYM] THEN
            REWRITE_TAC [ADD_SUB] THEN
            FIRST_ASSUM (CHANGED_TAC o SUBST1_TAC o MATCH_MP DIVISION_RHS) THEN
            FIRST_ASSUM (fun th => tactic_of do pure (MATCH_MP_TAC (← el2DivThm th))) THEN
            REWRITE_TAC [GE, SUB_LEFT_LESS_EQ] THEN
            ONCE_REWRITE_TAC [ADD_SYM] THEN ASM_REWRITE_TAC []]]]))

  let DIVISION_APPEND_EXPLICIT ← prove
   r"!a b c g d1 p1 d2 p2.
        tdiv(a,b) (d1,p1) /\
        fine g (d1,p1) /\
        tdiv(b,c) (d2,p2) /\
        fine g (d2,p2)
        ==> tdiv(a,c)
              ((\n. if n < dsize d1 then  d1(n) else d2(n - (dsize d1))),
               (\n. if n < dsize d1
                    then p1(n) else p2(n - (dsize d1)))) /\
            fine g ((\n. if n < dsize d1 then  d1(n) else d2(n - (dsize d1))),
               (\n. if n < dsize d1
                    then p1(n) else p2(n - (dsize d1)))) /\
            !f. rsum((\n. if n < dsize d1 then  d1(n) else d2(n - (dsize d1))),
                     (\n. if n < dsize d1
                          then p1(n) else p2(n - (dsize d1)))) f =
                rsum(d1,p1) f + rsum(d2,p2) f"
   (← do
    -- The ARITH_RULEs in OCaml's order: the later one in the THEN chain
    -- first, and the SIMP_TAC list right to left.
    let ar4 ← ARITH_RULE (← q r"k < n ==> (SUC k < n <=> ~(n = SUC k))")
    let ar3 ← ARITH_RULE (← q r"SUC(r + d) - d = SUC r")
    let ar2 ← ARITH_RULE (← q r"~(SUC(r + d) < d)")
    let ar1 ← ARITH_RULE (← q r"~(r + d < d:num)")
    let aSuc ← ASSUME (← q "SUC n = dsize D1")
    let abcdd ← [← q "a:real", ← q "b:real", ← q "c:real",
                 ← q r"D1:num->real", ← q r"D2:num->real"].mapM pure
    pure (MAP_EVERY X_GEN_TAC
       [← q "a:real", ← q "b:real", ← q "c:real", ← q r"g:real->real",
        ← q r"D1:num->real", ← q r"p1:num->real", ← q r"D2:num->real", ← q r"p2:num->real"] THEN
      STRIP_TAC THEN REWRITE_TAC [CONJ_ASSOC] THEN CONJ_TAC THENL
       [ALL_TAC,
        GEN_TAC THEN REWRITE_TAC [rsum] THEN
        MP_TAC (← SPECL abcdd DIVISION_APPEND_LEMMA2) THEN
        ANTS_TAC THENL [ASM_MESON_TAC [tdiv], ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [← GSYM SUM_SPLIT] THEN
        REWRITE_TAC [SUM_REINDEX] THEN BINOP_TAC THEN MATCH_MP_TAC SUM_EQ THEN
        SIMP_TAC [ADD_CLAUSES, ar1, ar2, ADD_SUB, ar3] THEN
        X_GEN_TAC (← q "k:num") THEN STRIP_TAC THEN AP_TERM_TAC THEN
        ASM_SIMP_TAC [ar4] THEN
        ASM_CASES_TAC (← q "dsize D1 = SUC k") THEN ASM_REWRITE_TAC [SUB_REFL] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN
        ASM_MESON_TAC [tdiv, DIVISION_LHS, DIVISION_RHS]] THEN
      DISJ_CASES_TAC (← GSYM (← SPEC (← q "dsize(D1)") LESS_0_CASES)) THENL
       [ASM_REWRITE_TAC [NOT_LESS_0, SUB_0] THEN
        CONV_TAC (ONCE_DEPTH_CONV ETA_CONV) THEN
        SUBGOAL_THEN (← q "a:real = b") (fun th => ASM_REWRITE_TAC [th]) THEN
        MP_TAC (← SPECL [← q r"D1:num->real", ← q "a:real", ← q "b:real"] DIVISION_EQ) THEN
        RULE_ASSUM_TAC (REWRITE_RULE [tdiv]) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
      CONJ_TAC THENL
       [ALL_TAC,
        REWRITE_TAC [fine] THEN X_GEN_TAC (← q "n:num") THEN
        RULE_ASSUM_TAC (REWRITE_RULE [tdiv]) THEN
        MP_TAC (← SPECL abcdd DIVISION_APPEND_LEMMA2) THEN
        ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN BETA_TAC THEN
        DISCH_TAC THEN ASM_CASES_TAC (← q "(SUC n) < (dsize D1)") THEN
        ASM_REWRITE_TAC [] THENL
         [SUBGOAL_THEN (← q "n < (dsize D1)") ASSUME_TAC THENL
           [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC (← q "SUC n") THEN
            ASM_REWRITE_TAC [LESS_SUC_REFL], ALL_TAC] THEN
          ASM_REWRITE_TAC [] THEN
          FIRST_ASSUM (MATCH_MP_TAC o REWRITE_RULE [fine]) THEN
          ASM_REWRITE_TAC [], ALL_TAC] THEN
        ASM_CASES_TAC (← q "n < (dsize D1)") THEN ASM_REWRITE_TAC [] THENL
         [SUBGOAL_THEN (← q "SUC n = dsize D1") ASSUME_TAC THENL
           [MATCH_MP_TAC LESS_EQUAL_ANTISYM THEN
            ASM_REWRITE_TAC [← GSYM NOT_LT] THEN
            REWRITE_TAC [NOT_LT] THEN MATCH_MP_TAC LESS_OR THEN
            ASM_REWRITE_TAC [],
            ASM_REWRITE_TAC [SUB_REFL] THEN
            FIRST_ASSUM (CHANGED_TAC o SUBST1_TAC o MATCH_MP DIVISION_LHS o
              CONJUNCT1) THEN
            FIRST_ASSUM (CHANGED_TAC o SUBST1_TAC o SYM o
              MATCH_MP DIVISION_RHS o CONJUNCT1) THEN
            SUBST1_TAC (← SYM aSuc) THEN
            FIRST_ASSUM (MATCH_MP_TAC o REWRITE_RULE [fine]) THEN
            ASM_REWRITE_TAC []],
          ASM_REWRITE_TAC [SUB_OLD] THEN UNDISCH_TAC (← q "~(n < (dsize D1))") THEN
          REWRITE_TAC [LE_EXISTS, NOT_LT] THEN
          DISCH_THEN (X_CHOOSE_THEN (← q "d:num") SUBST_ALL_TAC) THEN
          ONCE_REWRITE_TAC [ADD_SYM] THEN REWRITE_TAC [ADD_SUB] THEN
          FIRST_ASSUM (MATCH_MP_TAC o REWRITE_RULE [fine]) THEN
          RULE_ASSUM_TAC (ONCE_REWRITE_RULE [ADD_SYM]) THEN
          RULE_ASSUM_TAC (REWRITE_RULE [LT_ADD_RCANCEL]) THEN
          FIRST_ASSUM ACCEPT_TAC]] THEN
      REWRITE_TAC [tdiv] THEN BETA_TAC THEN CONJ_TAC THENL
       [RULE_ASSUM_TAC (REWRITE_RULE [tdiv]) THEN
        REWRITE_TAC [DIVISION_THM] THEN CONJ_TAC THENL
         [BETA_TAC THEN ASM_REWRITE_TAC [] THEN
          MATCH_MP_TAC DIVISION_LHS THEN EXISTS_TAC (← q "b:real") THEN
          ASM_REWRITE_TAC [], ALL_TAC] THEN
        SUBGOAL_THEN (← q r"c = (\n. if (n < (dsize D1)) then  D1(n) else D2(n -
                    (dsize D1))) (dsize(D1) + dsize(D2))") SUBST1_TAC THENL
         [BETA_TAC THEN REWRITE_TAC [← GSYM NOT_LE, LE_ADD] THEN
          ONCE_REWRITE_TAC [ADD_SYM] THEN REWRITE_TAC [ADD_SUB] THEN
          CONV_TAC SYM_CONV THEN MATCH_MP_TAC DIVISION_RHS THEN
          EXISTS_TAC (← q "b:real") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
        MP_TAC (← SPECL abcdd DIVISION_APPEND_LEMMA2) THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN
        MATCH_MP_TAC (← BETA_RULE DIVISION_APPEND_LEMMA1) THEN
        MAP_EVERY EXISTS_TAC [← q "a:real", ← q "b:real", ← q "c:real"] THEN
        ASM_REWRITE_TAC [], ALL_TAC] THEN
      X_GEN_TAC (← q "n:num") THEN RULE_ASSUM_TAC (REWRITE_RULE [tdiv]) THEN
      ASM_CASES_TAC (← q "(SUC n) < (dsize D1)") THEN ASM_REWRITE_TAC [] THENL
       [SUBGOAL_THEN (← q "n < (dsize D1)") ASSUME_TAC THENL
         [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC (← q "SUC n") THEN
          ASM_REWRITE_TAC [LESS_SUC_REFL], ALL_TAC] THEN
        ASM_REWRITE_TAC [], ALL_TAC] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THENL
       [ASM_REWRITE_TAC [SUB_OLD] THEN
        FIRST_ASSUM (CHANGED_TAC o SUBST1_TAC o MATCH_MP DIVISION_LHS o
          CONJUNCT1) THEN
        FIRST_ASSUM (CHANGED_TAC o SUBST1_TAC o SYM o
          MATCH_MP DIVISION_RHS o CONJUNCT1) THEN
        SUBGOAL_THEN (← q "dsize D1 = SUC n") (fun th => ASM_REWRITE_TAC [th]) THEN
        MATCH_MP_TAC LESS_EQUAL_ANTISYM THEN
        ASM_REWRITE_TAC [← GSYM NOT_LT] THEN REWRITE_TAC [NOT_LT] THEN
        MATCH_MP_TAC LESS_OR THEN ASM_REWRITE_TAC [],
        ASM_REWRITE_TAC [SUB_OLD]]))

  let DIVISION_APPEND_STRONG ← prove
   r"!a b c D1 p1 D2 p2.
        tdiv(a,b) (D1,p1) /\ fine(g) (D1,p1) /\
        tdiv(b,c) (D2,p2) /\ fine(g) (D2,p2)
        ==> ?D p. tdiv(a,c) (D,p) /\ fine(g) (D,p) /\
                  !f. rsum(D,p) f = rsum(D1,p1) f + rsum(D2,p2) f"
   (REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [← q r"\n. if n < dsize D1 then D1(n):real else D2(n - (dsize D1))",
      ← q r"\n. if n < dsize D1 then p1(n):real else p2(n - (dsize D1))"] THEN
    MATCH_MP_TAC DIVISION_APPEND_EXPLICIT THEN ASM_MESON_TAC [])

  let DIVISION_APPEND ← prove
   r"!a b c.
      (?D1 p1. tdiv(a,b) (D1,p1) /\ fine(g) (D1,p1)) /\
      (?D2 p2. tdiv(b,c) (D2,p2) /\ fine(g) (D2,p2)) ==>
        ?D p. tdiv(a,c) (D,p) /\ fine(g) (D,p)"
   (MESON_TAC [DIVISION_APPEND_STRONG])

  -- We can always find a division which is fine wrt any gauge

  let DIVISION_EXISTS ← prove
   r"!a b g. a <= b /\ gauge(\x. a <= x /\ x <= b) g ==>
        ?D p. tdiv(a,b) (D,p) /\ fine(g) (D,p)"
   (← do
    let awy ← ASSUME (← q "w <= y")
    pure (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      MP_TAC (← SPEC
        (← q r"\(u,v). a <= u /\ v <= b ==> ?D p. tdiv(u,v) (D,p) /\ fine(g) (D,p)")
        BOLZANO_LEMMA) THEN
      CONV_TAC (ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      subgoalAnte2 (fun t => REWRITE_TAC [t]) THENL
       [CONJ_TAC,
        DISCH_THEN (MP_TAC o SPECL [← q "a:real", ← q "b:real"]) THEN
        REWRITE_TAC [REAL_LE_REFL]]
      THENL
       [MAP_EVERY X_GEN_TAC [← q "u:real", ← q "v:real", ← q "w:real"] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC DIVISION_APPEND THEN
        EXISTS_TAC (← q "v:real") THEN CONJ_TAC THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "w:real"),
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "u:real")] THEN
        ASM_REWRITE_TAC [], ALL_TAC] THEN
      X_GEN_TAC (← q "x:real") THEN ASM_CASES_TAC (← q r"a <= x /\ x <= b") THENL
       [ALL_TAC,
        EXISTS_TAC (← q r"&1") THEN REWRITE_TAC [REAL_LT_01] THEN
        MAP_EVERY X_GEN_TAC [← q "w:real", ← q "y:real"] THEN STRIP_TAC THEN
        CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN (fun _ => ALL_TAC) THEN
        FIRST_ASSUM (undischCheck (fun c => pure (is_neg c))) THEN
        REWRITE_TAC [DE_MORGAN_THM, REAL_NOT_LE] THEN
        DISCH_THEN DISJ_CASES_TAC THENL
         [DISJ1_TAC THEN MATCH_MP_TAC REAL_LET_TRANS,
          DISJ2_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS] THEN
        EXISTS_TAC (← q "x:real") THEN ASM_REWRITE_TAC []] THEN
      UNDISCH_TAC (← q r"gauge(\x. a <= x /\ x <= b) g") THEN
      REWRITE_TAC [gauge] THEN BETA_TAC THEN
      DISCH_THEN (fun th => FIRST_ASSUM (ASSUME_TAC o MATCH_MP th)) THEN
      EXISTS_TAC (← q r"(g:real->real) x") THEN ASM_REWRITE_TAC [] THEN
      MAP_EVERY X_GEN_TAC [← q "w:real", ← q "y:real"] THEN REPEAT STRIP_TAC THEN
      EXISTS_TAC (← q r"\n. if (n = 0) then (w:real) else y") THEN
      EXISTS_TAC (← q r"\n. if (n = 0) then (x:real) else y") THEN
      SUBGOAL_THEN (← q "w <= y") ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "x:real") THEN
        ASM_REWRITE_TAC [], ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC [tdiv] THEN CONJ_TAC THENL
         [MATCH_MP_TAC DIVISION_SINGLE THEN FIRST_ASSUM ACCEPT_TAC,
          X_GEN_TAC (← q "n:num") THEN BETA_TAC THEN REWRITE_TAC [NOT_SUC] THEN
          COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_LE_REFL]],
        REWRITE_TAC [fine] THEN BETA_TAC THEN REWRITE_TAC [NOT_SUC] THEN
        X_GEN_TAC (← q "n:num") THEN
        DISJ_CASES_THEN MP_TAC (← REWRITE_RULE [REAL_LE_LT] awy) THENL
         [DISCH_THEN (ASSUME_TAC o MATCH_MP DIVISION_1) THEN
          ASM_REWRITE_TAC [← numc "1", ← CONJUNCT2 LT, NOT_LESS_0] THEN
          DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [],
          DISCH_THEN (SUBST1_TAC o MATCH_MP DIVISION_0) THEN
          REWRITE_TAC [NOT_LESS_0]]]))

  -- @@RETURN BEGIN
  return { DIVISION_APPEND_LEMMA1, DIVISION_APPEND_LEMMA2, DIVISION_APPEND_EXPLICIT,
           DIVISION_APPEND_STRONG, DIVISION_APPEND, DIVISION_EXISTS }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Lemmas about combining gauges; uniqueness of the integral; integral over  -/
/- a null interval; fundamental theorem of calculus (Part I).                -/
/- (transc.ml 4062-4328)                                                     -/
/- ------------------------------------------------------------------------- -/

structure Gauge where
  -- @@FIELDS
  GAUGE_MIN : thm
  FINE_MIN : thm
  DINT_UNIQ : thm
  INTEGRAL_NULL : thm
  STRADDLE_LEMMA : thm
  FTC1 : thm
  deriving Inhabited

@[nospecialize]
def setupGauge [HolBase] (D : TranscDeps) (BArcSinCos : ArcSinCos) (BDivision : Division) (BDivAppend : DivAppend) (ACompat : HolLibrary.Analysis.Compat) (AReals1 : HolLibrary.Analysis.Reals1) (AReals2 : HolLibrary.Analysis.Reals2) (AReals3 : HolLibrary.Analysis.Reals3) (AAbs : HolLibrary.Analysis.Abs) (ASums : HolLibrary.Analysis.Sums) (ALims : HolLibrary.Analysis.Lims) :
    ExceptT String IO Gauge := do
  -- @@SCOPE BEGIN
  let { num_CONV, .. } := D
  let { ADD_CLAUSES, EQ_IMP, LT_0, REAL_ADD2_SUB2, REAL_ADD_AC, REAL_ADD_LID,
        REAL_ADD_LINV, real_abs, .. } := D.core1
  let { REAL_DIV_RMUL, REAL_LET_TRANS, REAL_LE_ADD2, REAL_LT_MUL, REAL_LT_REFL,
        REAL_LT_TRANS, REAL_MUL_AC, REAL_MUL_ASSOC, real_div, real_sub, .. } := D.core2
  let { LE_MATCH_TAC, defint, fine, gauge, rsum, tdiv, .. } := BArcSinCos
  let { DIVISION_EQ, DIVISION_LBOUND, DIVISION_LHS, DIVISION_RHS, DIVISION_UBOUND, .. } := BDivision
  let { DIVISION_EXISTS, .. } := BDivAppend
  let { OLD_SKOLEM_CONV, RIGHT_IMP_EXISTS_CONV, .. } := ACompat
  let { REAL_LE_LADD, REAL_LE_LT, REAL_LE_RADD, REAL_LE_REFL, REAL_LE_TRANS,
        REAL_LTE_TRANS, REAL_LT_01, REAL_LT_ADD2, REAL_LT_IMP_LE, REAL_MUL_RZERO,
        REAL_NEG_ADD, REAL_NEG_RMUL, REAL_NOT_LT, REAL_SUB_ADD2, .. } := AReals1
  let { REAL_INV_POS, REAL_LT, REAL_LT_HALF1, REAL_LT_HALF2, REAL_LT_IMP_NE,
        REAL_LT_RMUL_EQ, REAL_NEG_SUB, REAL_SUB_0, REAL_SUB_LDISTRIB, REAL_SUB_LE,
        REAL_SUB_LT, REAL_SUB_RDISTRIB, REAL_SUB_REFL, .. } := AReals2
  let { REAL_HALF_DOUBLE, REAL_LE_LMUL_LOCAL, REAL_LE_NEG2, REAL_LE_RMUL_EQ,
        REAL_SUB_RZERO, .. } := AReals3
  let { ABS_0, ABS_MUL, ABS_NEG, ABS_NZ, ABS_SUB, ABS_TRIANGLE, .. } := AAbs
  let { ABS_SUM, SUM_CANCEL, SUM_CMUL, SUM_LE, SUM_SUB, sum, .. } := ASums
  let { LIM, diffl, .. } := ALims
  -- @@SCOPE END
  let numc (s : String) : ExceptT String IO thm := do ExceptT.mk (num_CONV (← q s))

  let GAUGE_MIN ← prove
   r"!E g1 g2. gauge(E) g1 /\ gauge(E) g2 ==>
        gauge(E) (\x. if g1(x) < g2(x) then g1(x) else g2(x))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [gauge] THEN STRIP_TAC THEN
    X_GEN_TAC (← q "x:real") THEN BETA_TAC THEN DISCH_TAC THEN
    COND_CASES_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC)

  let FINE_MIN ← prove
   r"!g1 g2 D p. fine (\x. if g1(x) < g2(x) then g1(x) else g2(x)) (D,p) ==>
        fine(g1) (D,p) /\ fine(g2) (D,p)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [fine] THEN
    BETA_TAC THEN DISCH_TAC THEN CONJ_TAC THEN
    X_GEN_TAC (← q "n:num") THEN DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN
    COND_CASES_TAC THEN REWRITE_TAC [] THEN DISCH_TAC THENL
     [RULE_ASSUM_TAC (REWRITE_RULE [REAL_NOT_LT]) THEN
      MATCH_MP_TAC REAL_LTE_TRANS,
      MATCH_MP_TAC REAL_LT_TRANS] THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (EXISTS_TAC (← liftExcept (rand (concl th))) THEN
                     ASM_REWRITE_TAC [] THEN NO_TAC)))

  -- The integral is unique if it exists

  let DINT_UNIQ ← prove
   r"!a b f k1 k2. a <= b /\ defint(a,b) f k1 /\ defint(a,b) f k2 ==> (k1 = k2)"
   (← do
    let acth ← AC REAL_ADD_AC (← q r"(a + b) + (c + d) = (d + a) + (c + b)")
    pure (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_SUB_0] THEN
      CONV_TAC CONTRAPOS_CONV THEN ONCE_REWRITE_TAC [ABS_NZ] THEN DISCH_TAC THEN
      REWRITE_TAC [defint] THEN
      DISCH_THEN (CONJUNCTS_THEN (MP_TAC o SPEC (← q r"abs(k1 - k2) / &2"))) THEN
      ASM_REWRITE_TAC [REAL_LT_HALF1] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"g1:real->real") STRIP_ASSUME_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"g2:real->real") STRIP_ASSUME_TAC) THEN
      MP_TAC (← SPECL [← q r"\x. a <= x /\ x <= b",
                    ← q r"g1:real->real", ← q r"g2:real->real"] GAUGE_MIN) THEN
      ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
      MP_TAC (← SPECL [← q "a:real", ← q "b:real",
             ← q r"\x:real. if g1(x) < g2(x) then g1(x) else g2(x)"] DIVISION_EXISTS) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"D:num->real") (X_CHOOSE_THEN (← q r"p:num->real")
        STRIP_ASSUME_TAC)) THEN
      FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP FINE_MIN) THEN
      REPEAT (FIRST_ASSUM (undischCheck (fun c => pure (is_forall c))) THEN
        DISCH_THEN (MP_TAC o SPECL [← q r"D:num->real", ← q r"p:num->real"]) THEN
        ASM_REWRITE_TAC [] THEN DISCH_TAC) THEN
      SUBGOAL_THEN (← q r"abs((rsum(D,p) f - k2) - (rsum(D,p) f - k1)) < abs(k1 - k2)")
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC (← q r"abs(rsum(D,p) f - k2) + abs(rsum(D,p) f - k1)") THEN
        CONJ_TAC THENL
         [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [real_sub] THEN
          GEN_REWRITE_TAC (funpow 2 RAND_CONV) [← GSYM ABS_NEG] THEN
          MATCH_ACCEPT_TAC ABS_TRIANGLE,
          GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_HALF_DOUBLE] THEN
          MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC []],
        REWRITE_TAC [real_sub, REAL_NEG_ADD, REAL_NEG_SUB] THEN
        ONCE_REWRITE_TAC [acth] THEN
        REWRITE_TAC [REAL_ADD_LINV, REAL_ADD_LID, REAL_LT_REFL]]))

  -- Integral over a null interval is 0

  let INTEGRAL_NULL ← prove
   r"!f a. defint(a,a) f (&0)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [defint] THEN GEN_TAC THEN
    DISCH_TAC THEN EXISTS_TAC (← q r"\x:real. &1") THEN
    REWRITE_TAC [gauge, REAL_LT_01] THEN REPEAT GEN_TAC THEN
    REWRITE_TAC [tdiv] THEN STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP DIVISION_EQ) THEN
    REWRITE_TAC [rsum] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC [sum, REAL_SUB_REFL, ABS_0])

  -- Fundamental theorem of calculus (Part I)

  let STRADDLE_LEMMA ← prove
   r"!f f' a b e. (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x)) /\ &0 < e
    ==> ?g. gauge(\x. a <= x /\ x <= b) g /\
            !x u v. a <= u /\ u <= x /\ x <= v /\ v <= b /\ (v - u) < g(x)
                ==> abs((f(v) - f(u)) - (f'(x) * (v - u))) <= e * (v - u)"
   (← do
    -- Built at tactic-construction time, in OCaml's right-to-left order.
    let ae2 ← ASSUME (← q r"&0 < e")
    let lmul2 ← MATCH_MP REAL_LE_LMUL_LOCAL ae2
    let acm2 ← AC REAL_MUL_AC (← q r"(a * b) * c = (a * c) * b")
    let ae1 ← ASSUME (← q r"&0 < e")
    let lmul1 ← MATCH_MP REAL_LE_LMUL_LOCAL ae1
    let acm1 ← AC REAL_MUL_AC (← q r"(a * b) * c = (a * c) * b")
    let aca ← AC REAL_ADD_AC (← q r"(a + b) + (c + d) = (b + c) + (a + d)")
    let azx ← ASSUME (← q r"&0 < abs(z - x)")
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [gauge] THEN BETA_TAC THEN
      SUBGOAL_THEN
       (← q r"!x. a <= x /\ x <= b ==>
            ?d. &0 < d /\
              !u v. u <= x /\ x <= v /\ (v - u) < d ==>
                abs((f(v) - f(u)) - (f'(x) * (v - u))) <= e * (v - u)") MP_TAC THENL
       [ALL_TAC,
        FIRST_ASSUM (undischCheck (fun c => pure (is_forall c))) THEN
        DISCH_THEN (fun _ => ALL_TAC) THEN
        DISCH_THEN (MP_TAC o CONV_RULE
          ((ONCE_DEPTH_CONV RIGHT_IMP_EXISTS_CONV) THENC OLD_SKOLEM_CONV)) THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"g:real->real") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q r"g:real->real") THEN CONJ_TAC THENL
         [GEN_TAC THEN
          DISCH_THEN (fun th => FIRST_ASSUM (MP_TAC o (fun a => MATCH_MP a th))) THEN
          DISCH_THEN (fun th => REWRITE_TAC [th]),
          REPEAT STRIP_TAC THEN
          SUBGOAL_THEN (← q r"a <= x /\ x <= b")
            (fun th => FIRST_ASSUM (MP_TAC o (fun a => MATCH_MP a th))) THENL
           [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
             [EXISTS_TAC (← q "u:real"), EXISTS_TAC (← q "v:real")] THEN
            ASM_REWRITE_TAC [],
            DISCH_THEN (MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC []]]] THEN
      X_GEN_TAC (← q "x:real") THEN
      DISCH_THEN (fun th => STRIP_ASSUME_TAC th THEN
        FIRST_ASSUM (undischCheck (fun c => pure (is_forall c))) THEN
        DISCH_THEN (MP_TAC o (fun a => MATCH_MP a th))) THEN
      REWRITE_TAC [diffl, LIM] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"e / &2")) THEN
      ASM_REWRITE_TAC [REAL_LT_HALF1] THEN
      BETA_TAC THEN REWRITE_TAC [REAL_SUB_RZERO] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "d:real") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN (← q r"!z. abs(z - x) < d ==>
            abs((f(z) - f(x)) - (f'(x) * (z - x))) <= (e / &2) * abs(z - x)")
      ASSUME_TAC THENL
       [GEN_TAC THEN ASM_CASES_TAC (← q r"&0 < abs(z - x)") THENL
         [ALL_TAC,
          UNDISCH_TAC (← q r"~(&0 < abs(z - x))") THEN
          REWRITE_TAC [← GSYM ABS_NZ, REAL_SUB_0] THEN
          DISCH_THEN SUBST1_TAC THEN
          REWRITE_TAC [REAL_SUB_REFL, REAL_MUL_RZERO, ABS_0, REAL_LE_REFL]] THEN
        DISCH_THEN (MP_TAC o CONJ azx) THEN
        DISCH_THEN (fun th => MATCH_MP_TAC REAL_LT_IMP_LE THEN MP_TAC th) THEN
        DISCH_THEN (fun th => FIRST_ASSUM (MP_TAC o (fun a => MATCH_MP a th))) THEN
        FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC LAND_CONV
          [← GSYM (← MATCH_MP REAL_LT_RMUL_EQ th)])) THEN
        MATCH_MP_TAC EQ_IMP THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC [← GSYM ABS_MUL] THEN AP_TERM_TAC THEN
        REWRITE_TAC [REAL_SUB_RDISTRIB] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC [REAL_SUB_ADD2] THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
        ASM_REWRITE_TAC [ABS_NZ], ALL_TAC] THEN
      EXISTS_TAC (← q "d:real") THEN ASM_REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN (← q "u <= v") (DISJ_CASES_TAC o REWRITE_RULE [REAL_LE_LT]) THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "x:real") THEN
        ASM_REWRITE_TAC [],
        ALL_TAC,
        ASM_REWRITE_TAC [REAL_SUB_REFL, REAL_MUL_RZERO, ABS_0, REAL_LE_REFL]] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"abs((f(v) - f(x)) - (f'(x) * (v - x))) +
                  abs((f(x) - f(u)) - (f'(x) * (x - u)))") THEN
      CONJ_TAC THENL
       [MP_TAC (← SPECL [← q r"(f(v) - f(x)) - (f'(x) * (v - x))",
                     ← q r"(f(x) - f(u)) - (f'(x) * (x - u))"] ABS_TRIANGLE) THEN
        MATCH_MP_TAC EQ_IMP THEN
        AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN
        ONCE_REWRITE_TAC [← GSYM REAL_ADD2_SUB2] THEN
        REWRITE_TAC [REAL_SUB_LDISTRIB] THEN
        SUBGOAL_THEN (← q r"!a b c. (a - b) + (b - c) = (a - c)")
          (fun th => REWRITE_TAC [th]) THEN
        REPEAT GEN_TAC THEN REWRITE_TAC [real_sub] THEN
        ONCE_REWRITE_TAC [aca] THEN
        REWRITE_TAC [REAL_ADD_LINV, REAL_ADD_LID], ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_HALF_DOUBLE] THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC (← q r"(e / &2) * abs(v - x)") THEN CONJ_TAC THENL
         [FIRST_ASSUM MATCH_MP_TAC THEN
          ASM_REWRITE_TAC [real_abs, REAL_SUB_LE] THEN
          MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q "v - u") THEN
          ASM_REWRITE_TAC [] THEN REWRITE_TAC [real_sub, REAL_LE_LADD] THEN
          ASM_REWRITE_TAC [REAL_LE_NEG2],
          ASM_REWRITE_TAC [real_abs, REAL_SUB_LE] THEN REWRITE_TAC [real_div] THEN
          GEN_REWRITE_TAC LAND_CONV [acm1] THEN
          REWRITE_TAC [← GSYM REAL_MUL_ASSOC, lmul1] THEN
          SUBGOAL_THEN (← q r"!x y. (x * inv(&2)) <= (y * inv(&2)) <=> x <= y")
          (fun th => ASM_REWRITE_TAC [th, real_sub, REAL_LE_LADD, REAL_LE_NEG2]) THEN
          REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_RMUL_EQ THEN
          MATCH_MP_TAC REAL_INV_POS THEN
          REWRITE_TAC [REAL_LT, ← numc "2", LT_0]],
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC (← q r"(e / &2) * abs(x - u)") THEN CONJ_TAC THENL
         [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [real_sub] THEN
          ONCE_REWRITE_TAC [← GSYM ABS_NEG] THEN
          REWRITE_TAC [REAL_NEG_ADD, REAL_NEG_SUB] THEN
          ONCE_REWRITE_TAC [REAL_NEG_RMUL] THEN
          REWRITE_TAC [REAL_NEG_SUB] THEN REWRITE_TAC [← GSYM real_sub] THEN
          FIRST_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC [ABS_SUB] THEN
          ASM_REWRITE_TAC [real_abs, REAL_SUB_LE] THEN
          MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q "v - u") THEN
          ASM_REWRITE_TAC [] THEN ASM_REWRITE_TAC [real_sub, REAL_LE_RADD],
          ASM_REWRITE_TAC [real_abs, REAL_SUB_LE] THEN REWRITE_TAC [real_div] THEN
          GEN_REWRITE_TAC LAND_CONV [acm2] THEN
          REWRITE_TAC [← GSYM REAL_MUL_ASSOC, lmul2] THEN
          SUBGOAL_THEN (← q r"!x y. (x * inv(&2)) <= (y * inv(&2)) <=> x <= y")
          (fun th => ASM_REWRITE_TAC [th, real_sub, REAL_LE_RADD, REAL_LE_NEG2]) THEN
          REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_RMUL_EQ THEN
          MATCH_MP_TAC REAL_INV_POS THEN
          REWRITE_TAC [REAL_LT, ← numc "2", LT_0]]]))

  let FTC1 ← prove
   r"!f f' a b. a <= b /\ (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x))
        ==> defint(a,b) f' (f(b) - f(a))"
   (← do
    let bconv ← ExceptT.mk (BETA_CONV (← q r"(\n. (D(SUC n) - D(n))) n"))
    pure (REPEAT STRIP_TAC THEN
      UNDISCH_TAC (← q "a <= b") THEN REWRITE_TAC [REAL_LE_LT] THEN
      DISCH_THEN DISJ_CASES_TAC THENL
       [ALL_TAC, ASM_REWRITE_TAC [REAL_SUB_REFL, INTEGRAL_NULL]] THEN
      REWRITE_TAC [defint] THEN X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN
      SUBGOAL_THEN
        (← q r"!e. &0 < e ==>
          ?g. gauge(\x. a <= x /\ x <= b)g /\
              (!D p.
                tdiv(a,b)(D,p) /\ fine g(D,p) ==>
                (abs((rsum(D,p)f') - ((f b) - (f a)))) <= e)")
      MP_TAC THENL
       [ALL_TAC,
        DISCH_THEN (MP_TAC o SPEC (← q r"e / &2")) THEN ASM_REWRITE_TAC [REAL_LT_HALF1] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"g:real->real") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q r"g:real->real") THEN ASM_REWRITE_TAC [] THEN
        REPEAT GEN_TAC THEN
        DISCH_THEN (fun th => FIRST_ASSUM (ASSUME_TAC o (fun a => MATCH_MP a th))) THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q r"e / &2") THEN
        ASM_REWRITE_TAC [REAL_LT_HALF2]] THEN
      UNDISCH_TAC (← q r"&0 < e") THEN DISCH_THEN (fun _ => ALL_TAC) THEN
      X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN
      MP_TAC (← SPECL [← q r"f:real->real", ← q r"f':real->real",
        ← q "a:real", ← q "b:real", ← q "e / (b - a)"] STRADDLE_LEMMA) THEN
      ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"&0 < e / (b - a)") (fun th => REWRITE_TAC [th]) THENL
       [REWRITE_TAC [real_div] THEN MATCH_MP_TAC REAL_LT_MUL THEN
        ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_INV_POS THEN
        ASM_REWRITE_TAC [REAL_SUB_LT], ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"g:real->real") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"g:real->real") THEN ASM_REWRITE_TAC [] THEN
      MAP_EVERY X_GEN_TAC [← q r"D:num->real", ← q r"p:num->real"] THEN
      REWRITE_TAC [tdiv] THEN STRIP_TAC THEN REWRITE_TAC [rsum] THEN
      SUBGOAL_THEN (← q r"f(b) - f(a) = sum(0,dsize D)(\n. f(D(SUC n)) - f(D(n)))")
      SUBST1_TAC THENL
       [MP_TAC (← SPECL [← q r"\n:num. (f:real->real)(D(n))", ← q "0", ← q "dsize D"]
          SUM_CANCEL) THEN BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
        ASM_REWRITE_TAC [ADD_CLAUSES] THEN
        MAP_EVERY (IMP_RES_THEN SUBST1_TAC) [DIVISION_LHS, DIVISION_RHS] THEN
        REFL_TAC, ALL_TAC] THEN
      ONCE_REWRITE_TAC [ABS_SUB] THEN REWRITE_TAC [← GSYM SUM_SUB] THEN BETA_TAC THEN
      LE_MATCH_TAC ABS_SUM THEN BETA_TAC THEN
      SUBGOAL_THEN (← q r"e = sum(0,dsize D)(\n. (e / (b - a)) * (D(SUC n) - D(n)))")
      SUBST1_TAC THENL
       [ONCE_REWRITE_TAC [← SYM bconv] THEN
        ASM_REWRITE_TAC [SUM_CMUL, SUM_CANCEL, ADD_CLAUSES] THEN
        MAP_EVERY (IMP_RES_THEN SUBST1_TAC) [DIVISION_LHS, DIVISION_RHS] THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
        REWRITE_TAC [REAL_SUB_0] THEN CONV_TAC (RAND_CONV SYM_CONV) THEN
        MATCH_MP_TAC REAL_LT_IMP_NE THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
      MATCH_MP_TAC SUM_LE THEN X_GEN_TAC (← q "r:num") THEN
      REWRITE_TAC [ADD_CLAUSES] THEN STRIP_TAC THEN BETA_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
       [IMP_RES_THEN (fun th => REWRITE_TAC [th]) DIVISION_LBOUND,
        IMP_RES_THEN (fun th => REWRITE_TAC [th]) DIVISION_UBOUND,
        UNDISCH_TAC (← q "fine(g)(D,p)") THEN REWRITE_TAC [fine] THEN
        DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]))

  -- @@RETURN BEGIN
  return { GAUGE_MIN, FINE_MIN, DINT_UNIQ, INTEGRAL_NULL, STRADDLE_LEMMA, FTC1 }
  -- @@RETURN END

/-- lib.ml's `repeat CONJUNCT2`. -/
partial def repeatCONJUNCT2 [HolBase] (th : thm) : ExceptT String IO thm :=
  tryCatch (do let t ← CONJUNCT2 th; repeatCONJUNCT2 t) (fun _ => pure th)

/- ------------------------------------------------------------------------- -/
/- Definition of integral and integrability; linearity; ordering; parts;    -/
/- simple lemmas about divisions.  (transc.ml 4328-4598)                     -/
/- ------------------------------------------------------------------------- -/

structure Integral where
  -- @@FIELDS
  integrable : thm
  integral : thm
  INTEGRABLE_DEFINT : thm
  DIVISION_BOUNDS : thm
  TDIV_BOUNDS : thm
  TDIV_LE : thm
  DEFINT_WRONG : thm
  DEFINT_INTEGRAL : thm
  DEFINT_CONST : thm
  DEFINT_0 : thm
  DEFINT_NEG : thm
  DEFINT_CMUL : thm
  DEFINT_ADD : thm
  DEFINT_SUB : thm
  INTEGRAL_LE : thm
  DEFINT_LE : thm
  DEFINT_TRIANGLE : thm
  DEFINT_EQ : thm
  INTEGRAL_EQ : thm
  INTEGRATION_BY_PARTS : thm
  DIVISION_LE_SUC : thm
  DIVISION_MONO_LE : thm
  DIVISION_MONO_LE_SUC : thm
  DIVISION_INTERMEDIATE : thm
  DIVISION_DSIZE_LE : thm
  DIVISION_DSIZE_GE : thm
  DIVISION_DSIZE_EQ : thm
  DIVISION_DSIZE_EQ_ALT : thm
  deriving Inhabited

@[nospecialize]
def setupIntegral [HolBase] (D : TranscDeps) (BDiffConv : DiffConv) (BArcSinCos : ArcSinCos) (BDivision : Division) (BDivAppend : DivAppend) (BGauge : Gauge) (AReals1 : HolLibrary.Analysis.Reals1) (AReals2 : HolLibrary.Analysis.Reals2) (ASums : HolLibrary.Analysis.Sums) (ADiffs : HolLibrary.Analysis.Diffs) :
    ExceptT String IO Integral := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, INDUCT_TAC, MESON_TAC,
        REAL_ARITH, REAL_ARITH_TAC, new_definition, .. } := D
  let { ADD_CLAUSES, ARITH, CONTRAPOS_THM, EXISTS_REFL, GE, LE, LEFT_FORALL_IMP_THM,
        LEFT_IMP_EXISTS_THM, LET_CASES, LE_0, LE_ANTISYM, LE_EXISTS, LE_REFL,
        LE_SUC_LT, LT, LT_LE, MONO_EXISTS, MONO_FORALL, NOT_EXISTS_THM, NOT_LT,
        REAL_ABS_MUL, REAL_ABS_NZ, REAL_ADD_LID, REAL_ADD_RDISTRIB, num_MAX, .. } := D.core1
  let { REAL_LE_ANTISYM, REAL_LE_RMUL, REAL_LT_DIV, REAL_LT_RDIV_EQ, REAL_LT_REFL,
        REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LNEG, REAL_MUL_SYM, REAL_OF_NUM_LT,
        SELECT_UNIQUE, SWAP_FORALL_THM, real_sub, .. } := D.core2
  let { DIFF_CONV, .. } := BDiffConv
  let { defint, gauge, rsum, tdiv, .. } := BArcSinCos
  let { DIVISION_LBOUND, DIVISION_LE, DIVISION_THM, DIVISION_UBOUND, .. } := BDivision
  let { DIVISION_EXISTS, .. } := BDivAppend
  let { DINT_UNIQ, FINE_MIN, FTC1, GAUGE_MIN, .. } := BGauge
  let { REAL_LE_REFL, REAL_LE_TRANS, REAL_LT_IMP_LE, REAL_MUL_LZERO, REAL_NOT_LE, .. } := AReals1
  let { REAL_SUB_LDISTRIB, REAL_SUB_LE, .. } := AReals2
  let { SUM_ADD, SUM_CMUL, SUM_EQ, SUM_LE, SUM_NEG, .. } := ASums
  let { DIFF_MUL, .. } := ADiffs
  -- @@SCOPE END

  let integrable ← new_definition
   r"integrable(a,b) f = ?i. defint(a,b) f i"

  let integral ← new_definition
   r"integral(a,b) f = @i. defint(a,b) f i"

  let INTEGRABLE_DEFINT ← prove
   r"!f a b. integrable(a,b) f ==> defint(a,b) f (integral(a,b) f)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [integrable, integral] THEN
    CONV_TAC (RAND_CONV SELECT_CONV) THEN REWRITE_TAC [])

  -- Other more or less trivial lemmas.

  let DIVISION_BOUNDS ← prove
   r"!d a b. division(a,b) d ==> !n. a <= d(n) /\ d(n) <= b"
   (MESON_TAC [DIVISION_UBOUND, DIVISION_LBOUND])

  let TDIV_BOUNDS ← prove
   r"!d p a b. tdiv(a,b) (d,p)
             ==> !n. a <= d(n) /\ d(n) <= b /\ a <= p(n) /\ p(n) <= b"
   (REWRITE_TAC [tdiv] THEN ASM_MESON_TAC [DIVISION_BOUNDS, REAL_LE_TRANS])

  let TDIV_LE ← prove
   r"!d p a b. tdiv(a,b) (d,p) ==> a <= b"
   (MESON_TAC [tdiv, DIVISION_LE])

  let DEFINT_WRONG ← prove
   r"!a b f i. b < a ==> defint(a,b) f i"
   (← do
    let ra ← REAL_ARITH (← q r"b < a ==> (a <= x /\ x <= b <=> F)")
    pure (REWRITE_TAC [defint, gauge] THEN REPEAT STRIP_TAC THEN
      EXISTS_TAC (← q r"\x:real. &0") THEN
      ASM_SIMP_TAC [ra] THEN
      ASM_MESON_TAC [REAL_NOT_LE, TDIV_LE]))

  let DEFINT_INTEGRAL ← prove
   r"!f a b i. a <= b /\ defint(a,b) f i ==> integral(a,b) f = i"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [integral] THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC [DINT_UNIQ])

  -- Linearity.

  let DEFINT_CONST ← prove
   r"!a b c. defint(a,b) (\x. c) (c * (b - a))"
   (← do
    let dc ← ExceptT.mk (DIFF_CONV (← q r"\x. c * x"))
    let ra ← REAL_ARITH (← q r"b < a \/ a <= b")
    pure (REPEAT GEN_TAC THEN
      MP_TAC (← SPECL [← q r"\x. c * x", ← q r"\x:real. c:real", ← q "a:real", ← q "b:real"] FTC1) THEN
      DISJ_CASES_TAC ra THEN
      ASM_SIMP_TAC [DEFINT_WRONG, REAL_SUB_LDISTRIB] THEN
      DISCH_THEN MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
      MP_TAC (← SPEC (← q "x:real") dc) THEN
      REWRITE_TAC [REAL_MUL_LID, REAL_MUL_LZERO, REAL_ADD_LID]))

  let DEFINT_0 ← prove
   r"!a b. defint(a,b) (\x. &0) (&0)"
   (MP_TAC DEFINT_CONST THEN REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"&0")) THEN REWRITE_TAC [REAL_MUL_LZERO])

  let DEFINT_NEG ← prove
   r"!f a b i. defint(a,b) f i ==> defint(a,b) (\x. --f x) (--i)"
   (← do
    let ra ← REAL_ARITH (← q r"abs(--x - --y) = abs(x - y)")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [defint] THEN
      REWRITE_TAC [rsum, REAL_MUL_LNEG, SUM_NEG] THEN
      REWRITE_TAC [ra]))

  let DEFINT_CMUL ← prove
   r"!f a b c i. defint(a,b) f i ==> defint(a,b) (\x. c * f x) (c * i)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"c = &0") THENL
     [MP_TAC (← SPECL [← q "a:real", ← q "b:real", ← q "c:real"] DEFINT_CONST) THEN
      ASM_SIMP_TAC [REAL_MUL_LZERO],
      ALL_TAC] THEN
    REWRITE_TAC [defint] THEN DISCH_TAC THEN X_GEN_TAC (← q "e:real") THEN
    DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q "e / abs c")) THEN
    ASM_SIMP_TAC [REAL_LT_DIV, ← GSYM REAL_ABS_NZ] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    REWRITE_TAC [rsum, SUM_CMUL, ← GSYM REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC [← GSYM REAL_SUB_LDISTRIB, REAL_ABS_MUL] THEN
    ASM_SIMP_TAC [REAL_LT_RDIV_EQ, ← GSYM REAL_ABS_NZ, REAL_MUL_SYM])

  let DEFINT_ADD ← prove
   r"!f g a b i j.
        defint(a,b) f i /\ defint(a,b) g j
        ==> defint(a,b) (\x. f x + g x) (i + j)"
   (← do
    let ra ← REAL_ARITH
     (← q r"abs(x - i) < e / &2 /\ abs(y - j) < e / &2
      ==> abs((x + y) - (i + j)) < e")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [defint] THEN
      STRIP_TAC THEN X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC (← q r"e / &2"))) THEN
      ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"g1:real->real") STRIP_ASSUME_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"g2:real->real") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"\x:real. if g1(x) < g2(x) then g1(x) else g2(x)") THEN
      ASM_SIMP_TAC [GAUGE_MIN, rsum] THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC [REAL_ADD_RDISTRIB, SUM_ADD] THEN REWRITE_TAC [← GSYM rsum] THEN
      MATCH_MP_TAC ra THEN
      ASM_MESON_TAC [FINE_MIN]))

  let DEFINT_SUB ← prove
   r"!f g a b i j.
        defint(a,b) f i /\ defint(a,b) g j
        ==> defint(a,b) (\x. f x - g x) (i - j)"
   (SIMP_TAC [real_sub, DEFINT_ADD, DEFINT_NEG])

  -- Ordering properties of integral.

  let INTEGRAL_LE ← prove
   r"!f g a b i j.
        a <= b /\ integrable(a,b) f /\ integrable(a,b) g /\
        (!x. a <= x /\ x <= b ==> f(x) <= g(x))
        ==> integral(a,b) f <= integral(a,b) g"
   (← do
    let ra3 ← REAL_ARITH
     (← q r"ih - ig = e /\ &0 < e /\ sh <= sg
      ==> abs(sg - ig) < e / &2 ==> ~(abs(sh - ih) < e / &2)")
    let ra2 ← REAL_ARITH (← q r"&0 < e / &2 <=> &0 < e")
    let ra1 ← REAL_ARITH (← q r"~(&0 < x - y) ==> x <= y")
    pure (REPEAT STRIP_TAC THEN
      REPEAT (FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP INTEGRABLE_DEFINT)) THEN
      MATCH_MP_TAC ra1 THEN
      ABBREV_TAC (← q "e = integral(a,b) f - integral(a,b) g") THEN DISCH_TAC THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o
        SPEC (← q r"e / &2") o GEN_REWRITE_RULE id [defint])) THEN
      ASM_REWRITE_TAC [ra2] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"g1:real->real") STRIP_ASSUME_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"g2:real->real") STRIP_ASSUME_TAC) THEN
      MP_TAC (← SPECL [← q "a:real", ← q "b:real",
                    ← q r"\x:real. if g1(x) < g2(x) then g1(x) else g2(x)"]
                   DIVISION_EXISTS) THEN
      ASM_SIMP_TAC [GAUGE_MIN, NOT_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"D:num->real", ← q r"p:num->real"] THEN STRIP_TAC THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o SPECL [← q r"D:num->real", ← q r"p:num->real"])) THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o SPECL [← q r"D:num->real", ← q r"p:num->real"])) THEN
      FIRST_ASSUM (fun th => tactic_of do pure (ASM_REWRITE_TAC [← MATCH_MP FINE_MIN th])) THEN
      MATCH_MP_TAC ra3 THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [rsum] THEN MATCH_MP_TAC SUM_LE THEN
      X_GEN_TAC (← q "r:num") THEN REWRITE_TAC [ADD_CLAUSES] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [REAL_SUB_LE] THEN
      ASM_MESON_TAC [TDIV_BOUNDS, REAL_LT_IMP_LE, DIVISION_THM, tdiv]))

  let DEFINT_LE ← prove
   r"!f g a b i j. a <= b /\ defint(a,b) f i /\ defint(a,b) g j /\
                 (!x. a <= x /\ x <= b ==> f(x) <= g(x))
                 ==> i <= j"
   (REPEAT GEN_TAC THEN MP_TAC (← SPEC_ALL INTEGRAL_LE) THEN
    MESON_TAC [integrable, DEFINT_INTEGRAL])

  let DEFINT_TRIANGLE ← prove
   r"!f a b i j. a <= b /\ defint(a,b) f i /\ defint(a,b) (\x. abs(f x)) j
               ==> abs(i) <= j"
   (← do
    let ra ← REAL_ARITH (← q r"--a <= b /\ b <= a ==> abs(b) <= a")
    pure (REPEAT STRIP_TAC THEN MATCH_MP_TAC ra THEN
      CONJ_TAC THEN MATCH_MP_TAC DEFINT_LE THENL
       [MAP_EVERY EXISTS_TAC [← q r"\x:real. --abs(f x)", ← q r"f:real->real"],
        MAP_EVERY EXISTS_TAC [← q r"f:real->real", ← q r"\x:real. abs(f x)"]] THEN
      MAP_EVERY EXISTS_TAC [← q "a:real", ← q "b:real"] THEN
      ASM_SIMP_TAC [DEFINT_NEG] THEN REAL_ARITH_TAC))

  let DEFINT_EQ ← prove
   r"!f g a b i j. a <= b /\ defint(a,b) f i /\ defint(a,b) g j /\
                 (!x. a <= x /\ x <= b ==> f(x) = g(x))
                 ==> i = j"
   (REWRITE_TAC [← GSYM REAL_LE_ANTISYM] THEN MESON_TAC [DEFINT_LE])

  let INTEGRAL_EQ ← prove
   r"!f g a b i. defint(a,b) f i /\
               (!x. a <= x /\ x <= b ==> f(x) = g(x))
               ==> defint(a,b) g i"
   (← do
    let ra ← REAL_ARITH (← q r"x = y ==> abs(x - i) < e ==> abs(y - i) < e")
    pure (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q "a <= b") THENL
       [ALL_TAC, ASM_MESON_TAC [REAL_NOT_LE, DEFINT_WRONG]] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [defint]) THEN
      REWRITE_TAC [defint] THEN MATCH_MP_TAC MONO_FORALL THEN
      X_GEN_TAC (← q "e:real") THEN ASM_CASES_TAC (← q r"&0 < e") THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"d:real->real") THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q r"D:num->real") THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q r"p:num->real") THEN
      DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC ra THEN
      REWRITE_TAC [rsum] THEN MATCH_MP_TAC SUM_EQ THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC [] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC [tdiv, DIVISION_LBOUND, DIVISION_UBOUND, DIVISION_THM,
                    REAL_LE_TRANS]))

  -- Integration by parts.

  let INTEGRATION_BY_PARTS ← prove
   r"!f g f' g' a b.
        a <= b /\
        (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x)) /\
        (!x. a <= x /\ x <= b ==> (g diffl g'(x))(x))
        ==> defint(a,b) (\x. f'(x) * g(x) + f(x) * g'(x))
                        (f(b) * g(b) - f(a) * g(a))"
   (← do
    let ra ← REAL_ARITH (← q r"a + b * c = a + c * b")
    pure (REPEAT STRIP_TAC THEN MATCH_MP_TAC FTC1 THEN ASM_REWRITE_TAC [] THEN
      ONCE_REWRITE_TAC [ra] THEN
      ASM_SIMP_TAC [DIFF_MUL]))

  -- Various simple lemmas about divisions.

  let DIVISION_LE_SUC ← prove
   r"!d a b. division(a,b) d ==> !n. d(n) <= d(SUC n)"
   (REWRITE_TAC [DIVISION_THM, GE] THEN
    MESON_TAC [LET_CASES, LE, REAL_LE_REFL, REAL_LT_IMP_LE])

  let DIVISION_MONO_LE ← prove
   r"!d a b. division(a,b) d ==> !m n. m <= n ==> d(m) <= d(n)"
   (REPEAT GEN_TAC THEN DISCH_THEN (ASSUME_TAC o MATCH_MP DIVISION_LE_SUC) THEN
    SIMP_TAC [LE_EXISTS, LEFT_IMP_EXISTS_THM] THEN
    GEN_TAC THEN ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    REWRITE_TAC [LEFT_FORALL_IMP_THM, EXISTS_REFL] THEN
    INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES, REAL_LE_REFL] THEN
    ASM_MESON_TAC [REAL_LE_TRANS])

  let DIVISION_MONO_LE_SUC ← prove
   r"!d a b. division(a,b) d ==> !n. d(n) <= d(SUC n)"
   (MESON_TAC [DIVISION_MONO_LE, LE, LE_REFL])

  let DIVISION_INTERMEDIATE ← prove
   r"!d a b c. division(a,b) d /\ a <= c /\ c <= b
             ==> ?n. n <= dsize d /\ d(n) <= c /\ c <= d(SUC n)"
   (← do
    let ar ← ARITH_RULE (← q r"~(SUC n <= n)")
    pure (REPEAT STRIP_TAC THEN
      MP_TAC (← SPEC (← q r"\n. n <= dsize d /\ (d:num->real)(n) <= c") num_MAX) THEN
      DISCH_THEN (fun th => tactic_of do
        let (a, _) ← EQ_IMP_RULE th
        pure (MP_TAC a)) THEN ANTS_TAC THENL
       [ASM_MESON_TAC [LE_0, DIVISION_THM], ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q "n:num") THEN SIMP_TAC [] THEN
      STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q "SUC n")) THEN
      REWRITE_TAC [ar] THEN
      ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN REWRITE_TAC [REAL_NOT_LE] THEN
      DISCH_TAC THEN ASM_SIMP_TAC [REAL_LT_IMP_LE, LE_SUC_LT, LT_LE] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [DIVISION_THM]) THEN
      DISCH_THEN (MP_TAC o SPEC (← q "SUC(dsize d)") o repeatCONJUNCT2) THEN
      REWRITE_TAC [GE, LE, LE_REFL] THEN
      ASM_REAL_ARITH_TAC))

  let DIVISION_DSIZE_LE ← prove
   r"!a b d n. division(a,b) d /\ d(SUC n) = d(n) ==> dsize d <= n"
   (REWRITE_TAC [DIVISION_THM] THEN MESON_TAC [REAL_LT_REFL, NOT_LT])

  let DIVISION_DSIZE_GE ← prove
   r"!a b d n. division(a,b) d /\ d(n) < d(SUC n) ==> SUC n <= dsize d"
   (REWRITE_TAC [DIVISION_THM, LE_SUC_LT, GE] THEN
    MESON_TAC [REAL_LT_REFL, LE, NOT_LT])

  let DIVISION_DSIZE_EQ ← prove
   r"!a b d n. division(a,b) d /\ d(n) < d(SUC n) /\ d(SUC(SUC n)) = d(SUC n)
           ==> dsize d = SUC n"
   (REWRITE_TAC [← GSYM LE_ANTISYM] THEN
    MESON_TAC [DIVISION_DSIZE_LE, DIVISION_DSIZE_GE])

  let DIVISION_DSIZE_EQ_ALT ← prove
   r"!a b d n. division(a,b) d /\ d(SUC n) = d(n) /\
             (!i. i < n ==> d(i) < d(SUC i))
             ==> dsize d = n"
   (← do
    let ar ← ARITH_RULE (← q r"d <= 0 ==> d = 0")
    pure (REPLICATE_TAC 3 GEN_TAC THEN INDUCT_TAC THENL
       [MESON_TAC [ar, DIVISION_DSIZE_LE], ALL_TAC] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM LE_ANTISYM] THEN
      ASM_MESON_TAC [DIVISION_DSIZE_LE, DIVISION_DSIZE_GE, LT]))

  -- @@RETURN BEGIN
  return { integrable, integral, INTEGRABLE_DEFINT, DIVISION_BOUNDS, TDIV_BOUNDS,
           TDIV_LE, DEFINT_WRONG, DEFINT_INTEGRAL, DEFINT_CONST, DEFINT_0, DEFINT_NEG,
           DEFINT_CMUL, DEFINT_ADD, DEFINT_SUB, INTEGRAL_LE, DEFINT_LE, DEFINT_TRIANGLE,
           DEFINT_EQ, INTEGRAL_EQ, INTEGRATION_BY_PARTS, DIVISION_LE_SUC,
           DIVISION_MONO_LE, DIVISION_MONO_LE_SUC, DIVISION_INTERMEDIATE,
           DIVISION_DSIZE_LE, DIVISION_DSIZE_GE, DIVISION_DSIZE_EQ,
           DIVISION_DSIZE_EQ_ALT }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Combination of adjacent intervals (quite painful in the details).         -/
/- (transc.ml 4598-4925)                                                     -/
/- ------------------------------------------------------------------------- -/

structure Combine where
  -- @@FIELDS
  DEFINT_COMBINE : thm
  deriving Inhabited

@[nospecialize]
def setupCombine [HolBase] (D : TranscDeps) (BArcSinCos : ArcSinCos) (BDivision : Division) (BGauge : Gauge) (BIntegral : Integral) (AReals1 : HolLibrary.Analysis.Reals1) (AReals2 : HolLibrary.Analysis.Reals2) (ASums : HolLibrary.Analysis.Sums) :
    ExceptT String IO Combine := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON_TAC,
        REAL_ARITH, REAL_ARITH_TAC, .. } := D
  let { ADD_AC, ADD_CLAUSES, ADD_EQ_0, ADD_SYM, AND_FORALL_THM, ARITH, CONJ_SYM, GE,
        LE, LE_0, LE_EXISTS, LE_REFL, LE_SUC_LT, LT_IMP_LE, MONO_AND, MONO_IMP,
        NOT_SUC, REAL_ADD_LID, REAL_ADD_RID, .. } := D.core1
  let { REAL_LT_DIV, REAL_LT_MIN, REAL_LT_REFL, REAL_OF_NUM_LT, .. } := D.core2
  let { defint, division, fine, gauge, rsum, tdiv, .. } := BArcSinCos
  let { DIVISION_THM, .. } := BDivision
  let { DINT_UNIQ, INTEGRAL_NULL, .. } := BGauge
  let { DIVISION_DSIZE_EQ, DIVISION_DSIZE_EQ_ALT, DIVISION_DSIZE_LE,
        DIVISION_INTERMEDIATE, DIVISION_MONO_LE, .. } := BIntegral
  let { REAL_LE_LT, REAL_LE_REFL, REAL_LE_TRANS, REAL_LT_LE, REAL_MUL_RZERO,
        REAL_NOT_LT, .. } := AReals1
  let { REAL_SUB_LT, REAL_SUB_REFL, .. } := AReals2
  let { SUM_1, SUM_EQ, SUM_REINDEX, SUM_SPLIT, sum, .. } := ASums
  -- @@SCOPE END

  let DEFINT_COMBINE ← prove
   r"!f a b c i j. a <= b /\ b <= c /\ defint(a,b) f i /\ defint(b,c) f j
                 ==> defint(a,c) f (i + j)"
   (← do
    -- The rules are evaluated when OCaml builds the tactic, last first.
    let r39 ← ARITH_RULE (← q r"m + 0 + 1 = 0 + m + 1")
    let r38 ← ARITH_RULE (← q r"1 = 0 + 1")
    let r37 ← REAL_ARITH (← q r"a = b ==> x + a = b + x")
    let r36 ← REAL_ARITH (← q r"x = y ==> abs(x - i) < e ==> abs(y - i) < e")
    let r35 ← REAL_ARITH (← q r"b <= a ==> x < b ==> x < a")
    let r34 ← ARITH_RULE (← q r"k + m < m + n <=> k:num < n")
    let r33 ← ARITH_RULE (← q r"k + m:num < m + n <=> k < n")
    let r32 ← ARITH_RULE (← q r"k + m:num < m + n <=> k < n")
    let r31 ← TAUT (← q r"a /\ (a ==> b /\ (b /\ c ==> d))
                     ==> (a /\ b ==> c) ==> d")
    let r30 ← REAL_ARITH (← q r"x = y ==> abs(x - i) < e ==> abs(y - i) < e")
    let r29 ← ARITH_RULE (← q r"m + 1 = 0 + SUC m")
    let r28 ← REAL_ARITH (← q r"b <= a ==> x < b ==> x < a")
    let r27 ← ARITH_RULE (← q r"SUC(PRE n + m) >= m + n /\
                                  SUC(SUC(PRE n + m)) >= m + n")
    let r26 ← ARITH_RULE (← q r"~(n = 0) /\ k >= PRE n ==> SUC(k + m) >= m + n")
    let r25 ← ARITH_RULE (← q r"~(n = 0) /\ k < PRE n ==> SUC(k + m) < m + n")
    let r24 ← TAUT (← q r"a /\ (a ==> b /\ (b /\ c ==> d))
                       ==> (a /\ b ==> c) ==> d")
    let r23 ← ARITH_RULE (← q r"~(SUC(SUC m) <= m)")
    let r22 ← ARITH_RULE (← q r"~(SUC m <= m)")
    let r21 ← ARITH_RULE (← q r"~(SUC m <= m)")
    let r20 ← ARITH_RULE (← q r"i < m:num ==> i < m + n")
    let r19 ← ARITH_RULE (← q r"~(SUC m <= m)")
    let r18 ← REAL_ARITH (← q r"x = y ==> abs(x - i) < e ==> abs(y - i) < e")
    let r17 ← ARITH_RULE (← q r"d:num <= SUC m /\ ~(n = 0) ==> k < d ==> k < m + n")
    let r16 ← ARITH_RULE (← q r"k <= m /\ ~(k = m) ==> SUC k <= m")
    let r15 ← ARITH_RULE (← q r"k <= m /\ ~(n = 0) ==> k < m + n")
    let r14 ← ARITH_RULE (← q r"m < m + n <=> ~(n = 0)")
    let r13 ← ARITH_RULE (← q r"SUC n <= m <=> n <= m /\ ~(m = n)")
    let r12 ← ARITH_RULE (← q r"k < SUC m /\ ~(n = 0) ==> k < m + n")
    let r11 ← ARITH_RULE (← q r"n < SUC m ==> (SUC n <= m <=> ~(m = n))")
    let r10 ← ARITH_RULE (← q r"n < SUC m ==> n <= m")
    let r9 ← ARITH_RULE (← q r"n >= SUC m ==> ~(n <= m)")
    let r8 ← ARITH_RULE (← q r"i:num < m ==> i < m + n")
    let r7 ← ARITH_RULE (← q r"n >= m ==> (n <= m <=> m = n:num)")
    let r6 ← ARITH_RULE (← q r"n < m ==> n <= m /\ SUC n <= m")
    let r5 ← ARITH_RULE (← q r"SUC n <= m <=> n <= m /\ ~(m = n)")
    let r4 ← TAUT (← q r"a /\ (a ==> b) /\ (a /\ c ==> d)
                       ==> (a /\ b ==> c) ==> d")
    let r3 ← REAL_ARITH
     (← q r"!b. abs((s1 + x * (b - a)) - i) < e / &2 /\
        abs((s2 + x * (c - b)) - j) < e / &2
        ==> abs((s1 + x * (c - a) + s2) - (i + j)) < e")
    let r2 ← ARITH_RULE (← q r"m < m + n <=> ~(n = 0)")
    let r1 ← ARITH_RULE (← q r"~(n = 0) ==> n = 1 + PRE n")
    let aab ← ASSUME (← q "a <= b")
    let abc ← ASSUME (← q "b <= c")
    let tE ← q "e:real"
    let tK ← q "k:num"
    pure (REPEAT GEN_TAC THEN
      REPLICATE_TAC 2 (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      MP_TAC aab THEN REWRITE_TAC [REAL_LE_LT] THEN
      ASM_CASES_TAC (← q "a:real = b") THEN ASM_REWRITE_TAC [] THENL
       [ASM_MESON_TAC [INTEGRAL_NULL, DINT_UNIQ, REAL_LE_TRANS, REAL_ADD_LID],
        DISCH_TAC] THEN
      MP_TAC abc THEN REWRITE_TAC [REAL_LE_LT] THEN
      ASM_CASES_TAC (← q "b:real = c") THEN ASM_REWRITE_TAC [] THENL
       [ASM_MESON_TAC [INTEGRAL_NULL, DINT_UNIQ, REAL_LE_TRANS, REAL_ADD_RID],
        DISCH_TAC] THEN
      REWRITE_TAC [defint, AND_FORALL_THM] THEN
      DISCH_THEN (fun th => X_GEN_TAC tE THEN DISCH_TAC THEN MP_TAC th) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"e / &2")) THEN
      ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
      DISCH_THEN (CONJUNCTS_THEN2
       (X_CHOOSE_THEN (← q r"g1:real->real") STRIP_ASSUME_TAC)
       (X_CHOOSE_THEN (← q r"g2:real->real") STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC
       (← q r"\x. if x < b then min (g1 x) (b - x)
            else if b < x then min (g2 x) (x - b)
            else min (g1 x) (g2 x)") THEN
      CONJ_TAC THENL
       [REPEAT (FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [gauge])) THEN
        REWRITE_TAC [gauge] THEN REPEAT STRIP_TAC THEN
        REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC [REAL_LT_MIN, REAL_SUB_LT] THEN
        TRY CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC,
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [← q r"d:num->real", ← q r"p:num->real"] THEN
      REWRITE_TAC [tdiv, rsum] THEN STRIP_TAC THEN
      MP_TAC (← SPECL [← q r"d:num->real", ← q "a:real", ← q "c:real", ← q "b:real"]
                   DIVISION_INTERMEDIATE) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "m:num")
       (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN REWRITE_TAC [LE_EXISTS] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q "n:num")) THEN ASM_REWRITE_TAC [] THEN
      ASM_CASES_TAC (← q "n = 0") THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC (REWRITE_RULE [ADD_CLAUSES]) THEN
        FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN
        ASM_MESON_TAC [DIVISION_THM, GE, LE_REFL, REAL_NOT_LT],
        ALL_TAC] THEN
      REWRITE_TAC [← GSYM SUM_SPLIT, ADD_CLAUSES] THEN
      FIRST_ASSUM (SUBST1_TAC o MATCH_MP r1) THEN
      REWRITE_TAC [← GSYM SUM_SPLIT, SUM_1] THEN
      SUBGOAL_THEN (← q r"(p:num->real) m = b") ASSUME_TAC THENL
       [FIRST_X_ASSUM (MP_TAC o SPEC (← q "m:num") o GEN_REWRITE_RULE id [fine]) THEN
        ASM_REWRITE_TAC [r2] THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q "m:num")) THEN
        MAP_EVERY UNDISCH_TAC [← q r"(d:num->real) m <= b", ← q r"b:real <= d(SUC m)"] THEN
        REAL_ARITH_TAC,
        ALL_TAC] THEN
      MATCH_MP_TAC r3 THEN
      EXISTS_TAC (← q "b:real") THEN CONJ_TAC THENL
       [UNDISCH_TAC
         (← q r"!D p. tdiv(a,b) (D,p) /\ fine g1 (D,p)
                ==> abs(rsum(D,p) f - i) < e / &2") THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"\i. if i <= m then (d:num->real)(i) else b")) THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"\i. if i <= m then (p:num->real)(i) else b")) THEN
        MATCH_MP_TAC r4 THEN
        CONJ_TAC THENL
         [REWRITE_TAC [tdiv, division] THEN REPEAT CONJ_TAC THENL
           [ASM_MESON_TAC [division, LE_0],
            ALL_TAC,
            X_GEN_TAC (← q "k:num") THEN
            REWRITE_TAC [r5] THEN
            ASM_CASES_TAC (← q "k:num = m") THEN
            ASM_REWRITE_TAC [LE_REFL, REAL_LE_REFL] THEN
            COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_LE_REFL]] THEN
          ASM_CASES_TAC (← q r"(d:num->real) m = b") THENL
           [EXISTS_TAC (← q "m:num") THEN
            SIMP_TAC [r6] THEN
            SIMP_TAC [r7] THEN
            CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
            FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [DIVISION_THM]) THEN
            ASM_REWRITE_TAC [] THEN
            MESON_TAC [r8],
            ALL_TAC] THEN
          EXISTS_TAC (← q "SUC m") THEN
          SIMP_TAC [r9] THEN
          SIMP_TAC [r10] THEN
          SIMP_TAC [r11] THEN
          FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [DIVISION_THM]) THEN
          ASM_REWRITE_TAC [] THEN
          ASM_MESON_TAC [r12, REAL_LT_LE],
          ALL_TAC] THEN
        CONJ_TAC THENL
         [REWRITE_TAC [tdiv, fine] THEN STRIP_TAC THEN X_GEN_TAC (← q "k:num") THEN
          REWRITE_TAC [r13] THEN
          FIRST_X_ASSUM (MP_TAC o SPEC (← q "k:num") o GEN_REWRITE_RULE id [fine]) THEN
          MATCH_MP_TAC MONO_IMP THEN ASM_CASES_TAC (← q "k:num = m") THENL
           [ASM_REWRITE_TAC [LE_REFL, REAL_LT_REFL] THEN
            ASM_REWRITE_TAC [r14] THEN
            MAP_EVERY UNDISCH_TAC [← q r"d(m:num) <= b", ← q r"b <= d(SUC m)"] THEN
            REAL_ARITH_TAC,
            ALL_TAC] THEN
          ASM_CASES_TAC (← q "k:num <= m") THEN ASM_REWRITE_TAC [] THENL
           [ASM_SIMP_TAC [r15] THEN
            SUBGOAL_THEN (← q r"(p:num->real) k <= b") MP_TAC THENL
             [ALL_TAC, REAL_ARITH_TAC] THEN
            MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"(d:num->real) m") THEN
            ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
            EXISTS_TAC (← q r"(d:num->real) (SUC k)") THEN ASM_REWRITE_TAC [] THEN
            ASM_MESON_TAC [DIVISION_MONO_LE, r16],
            ALL_TAC] THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC r17 THEN
            ASM_REWRITE_TAC [] THEN MATCH_MP_TAC DIVISION_DSIZE_LE THEN
            MAP_EVERY EXISTS_TAC [← q "a:real", ← q "b:real"] THEN ASM_REWRITE_TAC [] THEN
            ARITH_TAC,
            ALL_TAC] THEN
          UNDISCH_TAC (← q r"gauge (\x. a <= x /\ x <= b) g1") THEN
          ASM_REWRITE_TAC [REAL_SUB_REFL, gauge, REAL_LE_REFL] THEN
          DISCH_THEN (fun th => DISCH_THEN (fun _ => ALL_TAC) THEN MP_TAC th) THEN
          ASM_MESON_TAC [REAL_LE_REFL],
          ALL_TAC] THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        MATCH_MP_TAC r18 THEN
        REWRITE_TAC [rsum] THEN ASM_CASES_TAC (← q r"(d:num->real) m = b") THENL
         [SUBGOAL_THEN (← q r"dsize (\i. if i <= m then d i else b) = m") ASSUME_TAC THENL
           [ALL_TAC,
            ASM_REWRITE_TAC [REAL_SUB_REFL, REAL_MUL_RZERO, REAL_ADD_RID] THEN
            MATCH_MP_TAC SUM_EQ THEN
            SIMP_TAC [ADD_CLAUSES, LT_IMP_LE, LE_SUC_LT]] THEN
          MATCH_MP_TAC DIVISION_DSIZE_EQ_ALT THEN
          MAP_EVERY EXISTS_TAC [← q "a:real", ← q "b:real"] THEN
          CONJ_TAC THENL [ASM_MESON_TAC [tdiv], ALL_TAC] THEN
          ASM_REWRITE_TAC [LE_REFL, r19] THEN
          SIMP_TAC [LT_IMP_LE, LE_SUC_LT] THEN
          FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [DIVISION_THM]) THEN
          ASM_REWRITE_TAC [] THEN MESON_TAC [r20],
          ALL_TAC] THEN
        SUBGOAL_THEN (← q r"dsize (\i. if i <= m then d i else b) = SUC m")
        ASSUME_TAC THENL
         [ALL_TAC,
          ASM_REWRITE_TAC [sum, ADD_CLAUSES, LE_REFL, r21] THEN
          AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ THEN
          SIMP_TAC [ADD_CLAUSES, LT_IMP_LE, LE_SUC_LT]] THEN
        MATCH_MP_TAC DIVISION_DSIZE_EQ THEN
        MAP_EVERY EXISTS_TAC [← q "a:real", ← q "b:real"] THEN
        CONJ_TAC THENL [ASM_MESON_TAC [tdiv], ALL_TAC] THEN
        ASM_REWRITE_TAC [LE_REFL, r22] THEN
        REWRITE_TAC [r23] THEN
        ASM_REWRITE_TAC [REAL_LT_LE],
        ALL_TAC] THEN
      ASM_CASES_TAC (← q r"d(SUC m):real = b") THEN ASM_REWRITE_TAC [] THENL
       [ASM_REWRITE_TAC [REAL_SUB_REFL, REAL_MUL_RZERO, REAL_ADD_RID] THEN
        UNDISCH_TAC
         (← q r"!D p. tdiv(b,c) (D,p) /\ fine g2 (D,p)
                ==> abs(rsum(D,p) f - j) < e / &2") THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"\i. (d:num->real) (i + SUC m)")) THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"\i. (p:num->real) (i + SUC m)")) THEN
        MATCH_MP_TAC r24 THEN
        CONJ_TAC THENL
         [ASM_REWRITE_TAC [tdiv, division, ADD_CLAUSES] THEN EXISTS_TAC (← q "PRE n") THEN
          FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE id [DIVISION_THM]) THEN
          ASM_MESON_TAC [r25, r26],
          DISCH_TAC] THEN
        SUBGOAL_THEN (← q r"dsize(\i. d (i + SUC m)) = PRE n") ASSUME_TAC THENL
         [MATCH_MP_TAC DIVISION_DSIZE_EQ_ALT THEN
          MAP_EVERY EXISTS_TAC [← q "b:real", ← q "c:real"] THEN
          CONJ_TAC THENL [ASM_MESON_TAC [tdiv], ALL_TAC] THEN
          FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [DIVISION_THM]) THEN
          DISCH_THEN (MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC [ADD_CLAUSES] THEN
          GEN_REWRITE_TAC RAND_CONV [CONJ_SYM] THEN
          MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
           [ALL_TAC,
            ASM_MESON_TAC [r27]] THEN
          DISCH_THEN (fun th => X_GEN_TAC tK THEN DISCH_TAC THEN
                               MATCH_MP_TAC th) THEN
          UNDISCH_TAC (← q "k < PRE n") THEN ARITH_TAC,
          ALL_TAC] THEN
        CONJ_TAC THENL
         [ASM_REWRITE_TAC [fine] THEN X_GEN_TAC (← q "k:num") THEN DISCH_TAC THEN
          FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [fine]) THEN
          DISCH_THEN (MP_TAC o SPEC (← q "k + SUC m")) THEN
          ASM_REWRITE_TAC [ADD_CLAUSES] THEN ANTS_TAC THENL
           [UNDISCH_TAC (← q "k < PRE n") THEN ARITH_TAC, ALL_TAC] THEN
          MATCH_MP_TAC r28 THEN
          SUBGOAL_THEN (← q r"~(p(SUC (k + m)) < b)")
            (fun th => REWRITE_TAC [th] THEN REAL_ARITH_TAC) THEN
          REWRITE_TAC [REAL_NOT_LT] THEN
          FIRST_ASSUM (MP_TAC o CONJUNCT1 o SPEC (← q "SUC(k + m)")) THEN
          UNDISCH_TAC (← q r"b <= d (SUC m)") THEN
          FIRST_X_ASSUM (MP_TAC o MATCH_MP DIVISION_MONO_LE) THEN
          DISCH_THEN (MP_TAC o SPECL [← q "SUC m", ← q "k + SUC m"]) THEN
          ANTS_TAC THENL [ARITH_TAC, ALL_TAC] THEN
          REWRITE_TAC [ADD_CLAUSES] THEN REAL_ARITH_TAC,
          ALL_TAC] THEN
         ASM_REWRITE_TAC [rsum] THEN
         DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
         SUBST1_TAC r29 THEN
         REWRITE_TAC [SUM_REINDEX] THEN
         MATCH_MP_TAC r30 THEN
         MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC [ADD_CLAUSES],
         ALL_TAC] THEN
      UNDISCH_TAC
       (← q r"!D p. tdiv(b,c) (D,p) /\ fine g2 (D,p)
              ==> abs(rsum(D,p) f - j) < e / &2") THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"\i. if i = 0 then b:real else d(i + m)")) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"\i. if i = 0 then b:real else p(i + m)")) THEN
      MATCH_MP_TAC r31 THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC [tdiv, division, ADD_CLAUSES] THEN CONJ_TAC THENL
         [ALL_TAC,
          GEN_TAC THEN REWRITE_TAC [NOT_SUC] THEN
          COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_LE_REFL] THEN
          FIRST_X_ASSUM (MP_TAC o CONJUNCT2 o SPEC (← q "m:num")) THEN
          ASM_REWRITE_TAC [ADD_CLAUSES]] THEN
        EXISTS_TAC (← q "n:num") THEN REWRITE_TAC [NOT_SUC] THEN
        FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE id [DIVISION_THM]) THEN
        DISCH_THEN (MP_TAC o CONJUNCT2) THEN MATCH_MP_TAC MONO_AND THEN
        ASM_REWRITE_TAC [] THEN CONJ_TAC THEN DISCH_THEN (fun th =>
          X_GEN_TAC tK THEN tactic_of do pure (MP_TAC (← SPEC (← q "k + m:num") th)))
        THENL [ALL_TAC, UNDISCH_TAC (← q "~(n = 0)") THEN ARITH_TAC] THEN
        ASM_CASES_TAC (← q "k:num < n") THEN
        ASM_REWRITE_TAC [r32] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [ADD_CLAUSES] THEN
        ASM_REWRITE_TAC [REAL_LT_LE],
        DISCH_TAC] THEN
      SUBGOAL_THEN (← q r"dsize(\i. if i = 0 then b else d (i + m)) = n") ASSUME_TAC
      THENL
       [MATCH_MP_TAC DIVISION_DSIZE_EQ_ALT THEN
        MAP_EVERY EXISTS_TAC [← q "b:real", ← q "c:real"] THEN
        CONJ_TAC THENL [ASM_MESON_TAC [tdiv], ALL_TAC] THEN
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [DIVISION_THM]) THEN
        DISCH_THEN (MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC [ADD_CLAUSES] THEN
        GEN_REWRITE_TAC RAND_CONV [CONJ_SYM] THEN REWRITE_TAC [NOT_SUC] THEN
        MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
         [ALL_TAC, MESON_TAC [GE, ADD_SYM, LE_REFL, LE]] THEN
        DISCH_THEN (fun th =>
          X_GEN_TAC tK THEN tactic_of do pure (MP_TAC (← SPEC (← q "k + m:num") th))) THEN
        ASM_CASES_TAC (← q "k:num < n") THEN
        ASM_REWRITE_TAC [r33] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [ADD_CLAUSES] THEN
        ASM_REWRITE_TAC [REAL_LT_LE],
        ALL_TAC] THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC [fine] THEN X_GEN_TAC (← q "k:num") THEN DISCH_TAC THEN
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [fine]) THEN
        DISCH_THEN (MP_TAC o SPEC (← q "k + m:num")) THEN
        ASM_REWRITE_TAC [ADD_CLAUSES, NOT_SUC, r34] THEN
        ASM_CASES_TAC (← q "k = 0") THEN ASM_REWRITE_TAC [] THENL
         [ASM_REWRITE_TAC [ADD_CLAUSES, REAL_LT_REFL] THEN
          MAP_EVERY UNDISCH_TAC [← q r"(d:num->real) m <= b", ← q r"b <= d (SUC m)"] THEN
          REAL_ARITH_TAC,
          ALL_TAC] THEN
        MATCH_MP_TAC r35 THEN
        SUBGOAL_THEN (← q r"~((p:num->real) (k + m) < b)")
         (fun th => REWRITE_TAC [th] THEN REAL_ARITH_TAC) THEN
        REWRITE_TAC [REAL_NOT_LT] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"d(SUC m):real") THEN
        ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"(d:num->real)(k + m)") THEN
        ASM_REWRITE_TAC [] THEN
        FIRST_X_ASSUM (MP_TAC o MATCH_MP DIVISION_MONO_LE) THEN
        DISCH_THEN MATCH_MP_TAC THEN UNDISCH_TAC (← q "~(k = 0)") THEN ARITH_TAC,
        ALL_TAC] THEN
      ASM_REWRITE_TAC [rsum] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      MATCH_MP_TAC r36 THEN
      SUBGOAL_THEN (← q "n = 1 + PRE n")
       (fun th => GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [th])
      THENL [UNDISCH_TAC (← q "~(n = 0)") THEN ARITH_TAC, ALL_TAC] THEN
      REWRITE_TAC [← GSYM SUM_SPLIT, SUM_1, NOT_SUC, ADD_CLAUSES] THEN
      MATCH_MP_TAC r37 THEN
      SUBST1_TAC r38 THEN
      SUBST1_TAC r39 THEN
      ONCE_REWRITE_TAC [SUM_REINDEX] THEN MATCH_MP_TAC SUM_EQ THEN
      REWRITE_TAC [ADD_CLAUSES, ADD_EQ_0, ARITH] THEN REWRITE_TAC [ADD_AC]))

  -- @@RETURN BEGIN
  return { DEFINT_COMBINE }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Pointwise perturbation and spike functions; Cauchy-type integrability    -/
/- criterion.  (transc.ml 4927-5098)                                         -/
/- ------------------------------------------------------------------------- -/

structure Spike where
  -- @@FIELDS
  DEFINT_DELTA_LEFT : thm
  DEFINT_DELTA_RIGHT : thm
  DEFINT_DELTA : thm
  DEFINT_POINT_SPIKE : thm
  DEFINT_FINITE_SPIKE : thm
  GAUGE_MIN_FINITE : thm
  INTEGRABLE_CAUCHY : thm
  deriving Inhabited

@[nospecialize]
def setupSpike [HolBase] (D : TranscDeps) (BArcSinCos : ArcSinCos) (BDivision : Division) (BDivAppend : DivAppend) (BGauge : Gauge) (BIntegral : Integral) (BCombine : Combine) (AReals1 : HolLibrary.Analysis.Reals1) (AReals2 : HolLibrary.Analysis.Reals2) (AReals3 : HolLibrary.Analysis.Reals3) (APow : HolLibrary.Analysis.Pow) (ASums : HolLibrary.Analysis.Sums) (ASeqs : HolLibrary.Analysis.Seqs) (ASeqs2 : HolLibrary.Analysis.Seqs2) :
    ExceptT String IO Spike := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, REAL_ARITH,
        REAL_ARITH_TAC, .. } := D
  let { ADD1, ADD_CLAUSES, ARITH, DE_MORGAN_THM, ETA_AX, EXISTS_REFL,
        FINITE_INDUCT_STRONG, FORALL_AND_THM, GE, IN_INSERT, LE, LEFT_FORALL_IMP_THM,
        LEFT_IMP_EXISTS_THM, LE_0, LE_ADD, LE_REFL, LE_SUC_LT, LT_NZ, MONO_EXISTS,
        NOT_IN_EMPTY, REAL_ABS_NUM, REAL_ADD_LID, REAL_ADD_RID, .. } := D.core1
  let { REAL_INV_DIV, REAL_LT_DIV, REAL_LT_INV2, REAL_LT_LDIV_EQ, REAL_MUL_LID,
        REAL_MUL_SYM, REAL_OF_NUM_LE, REAL_OF_NUM_LT, REAL_POW_LT, REAL_POW_MONO,
        RIGHT_FORALL_IMP_THM, SKOLEM_THM, real_div, .. } := D.core2
  let { defint, fine, gauge, rsum, tdiv, .. } := BArcSinCos
  let { DIVISION_THM, .. } := BDivision
  let { DIVISION_EXISTS, .. } := BDivAppend
  let { FINE_MIN, GAUGE_MIN, .. } := BGauge
  let { DEFINT_0, DEFINT_ADD, DEFINT_CMUL, DEFINT_WRONG, DIVISION_MONO_LE, INTEGRAL_EQ,
        integrable, .. } := BIntegral
  let { DEFINT_COMBINE, .. } := BCombine
  let { REAL_LE_REFL, REAL_LTE_TRANS, REAL_LT_IMP_LE, REAL_MUL_LZERO, REAL_MUL_RZERO,
        REAL_NOT_LE, .. } := AReals1
  let { REAL_SUB_LE, .. } := AReals2
  let { REAL_SUB_RZERO, .. } := AReals3
  let { REAL_ARCH_POW2, .. } := APow
  let { SUM_1, SUM_EQ_0, SUM_SPLIT, sum, .. } := ASums
  let { SEQ, cauchy, convergent, .. } := ASeqs
  let { SEQ_CAUCHY, .. } := ASeqs2
  -- @@SCOPE END

  let DEFINT_DELTA_LEFT ← prove
   r"!a b. defint(a,b) (\x. if x = a then &1 else &0) (&0)"
   (← do
    let r3 ← REAL_ARITH (← q r"(&0 <= x /\ x < e) /\ y = &0 ==> abs(x + y) < e")
    let r2 ← ARITH_RULE (← q r"~(n = 0) ==> n = 1 + PRE n")
    let r1 ← REAL_ARITH (← q r"b < a \/ a <= b")
    pure (REPEAT GEN_TAC THEN DISJ_CASES_TAC r1 THEN
      ASM_SIMP_TAC [DEFINT_WRONG] THEN REWRITE_TAC [defint] THEN
      X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN EXISTS_TAC (← q r"(\x. e):real->real") THEN
      ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH,
                   gauge, fine, rsum, tdiv, REAL_SUB_RZERO] THEN
      MAP_EVERY X_GEN_TAC [← q r"d:num->real", ← q r"p:num->real"] THEN STRIP_TAC THEN
      ASM_CASES_TAC (← q "dsize d = 0") THEN ASM_REWRITE_TAC [sum, REAL_ABS_NUM] THEN
      FIRST_ASSUM (SUBST1_TAC o MATCH_MP r2) THEN
      REWRITE_TAC [← GSYM SUM_SPLIT, SUM_1, ADD_CLAUSES] THEN
      MATCH_MP_TAC r3 THEN
      CONJ_TAC THENL
       [COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_MUL_LZERO, REAL_LE_REFL] THEN
        REWRITE_TAC [REAL_MUL_LID, REAL_SUB_LE] THEN
        ASM_MESON_TAC [DIVISION_THM, LE_0, LT_NZ],
        ALL_TAC] THEN
      MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC (← q "r:num") THEN
      STRIP_TAC THEN REWRITE_TAC [] THEN
      COND_CASES_TAC THEN REWRITE_TAC [REAL_MUL_LZERO] THEN
      FIRST_ASSUM (MP_TAC o SPECL [← q "1", ← q "r:num"] o MATCH_MP DIVISION_MONO_LE) THEN
      ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [DIVISION_THM]) THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o CONJUNCT1)) THEN
      DISCH_THEN (MP_TAC o SPEC (← q "0")) THEN ASM_REWRITE_TAC [ARITH, LT_NZ] THEN
      FIRST_X_ASSUM (MP_TAC o CONJUNCT1 o SPEC (← q "r:num")) THEN
      ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC))

  let DEFINT_DELTA_RIGHT ← prove
   r"!a b. defint(a,b) (\x. if x = b then &1 else &0) (&0)"
   (← do
    let r5 ← ARITH_RULE (← q r"x < x + 1")
    let r4 ← ARITH_RULE (← q r"m < m + 1")
    let r3 ← REAL_ARITH (← q r"(&0 <= x /\ x < e) /\ y = &0 ==> abs(y + x) < e")
    let r2 ← ARITH_RULE (← q r"~(n = 0) ==> n = PRE n + 1")
    let r1 ← REAL_ARITH (← q r"b < a \/ a <= b")
    pure (REPEAT GEN_TAC THEN DISJ_CASES_TAC r1 THEN
      ASM_SIMP_TAC [DEFINT_WRONG] THEN REWRITE_TAC [defint] THEN
      X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN EXISTS_TAC (← q r"(\x. e):real->real") THEN
      ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH,
                   gauge, fine, rsum, tdiv, REAL_SUB_RZERO] THEN
      MAP_EVERY X_GEN_TAC [← q r"d:num->real", ← q r"p:num->real"] THEN STRIP_TAC THEN
      ASM_CASES_TAC (← q "dsize d = 0") THEN ASM_REWRITE_TAC [sum, REAL_ABS_NUM] THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP r2) THEN
      ABBREV_TAC (← q "m = PRE(dsize d)") THEN
      ASM_REWRITE_TAC [← GSYM SUM_SPLIT, SUM_1, ADD_CLAUSES] THEN
      MATCH_MP_TAC r3 THEN
      CONJ_TAC THENL
       [COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_MUL_LZERO, REAL_LE_REFL] THEN
        REWRITE_TAC [REAL_MUL_LID, REAL_SUB_LE] THEN
        ASM_MESON_TAC [DIVISION_THM, r4, REAL_LT_IMP_LE],
        ALL_TAC] THEN
      MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC (← q "r:num") THEN
      REWRITE_TAC [ADD_CLAUSES] THEN STRIP_TAC THEN
      COND_CASES_TAC THEN REWRITE_TAC [REAL_MUL_LZERO] THEN
      FIRST_X_ASSUM (MP_TAC o CONJUNCT2 o SPEC (← q "r:num")) THEN
      FIRST_ASSUM (MP_TAC o SPECL [← q "SUC r", ← q "m:num"] o
        MATCH_MP DIVISION_MONO_LE) THEN
      ASM_REWRITE_TAC [LE_SUC_LT] THEN
      FIRST_X_ASSUM (MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE id [DIVISION_THM]) THEN
      DISCH_THEN (CONJUNCTS_THEN2
       (MP_TAC o SPEC (← q "m:num")) (MP_TAC o SPEC (← q "m + 1"))) THEN
      ASM_REWRITE_TAC [GE, LE_REFL, r5] THEN
      REWRITE_TAC [ADD1] THEN REAL_ARITH_TAC))

  let DEFINT_DELTA ← prove
   r"!a b c. defint(a,b) (\x. if x = c then &1 else &0) (&0)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "a <= b") THENL
     [ALL_TAC, ASM_MESON_TAC [REAL_NOT_LE, DEFINT_WRONG]] THEN
    ASM_CASES_TAC (← q r"a <= c /\ c <= b") THENL
     [ALL_TAC,
      MATCH_MP_TAC INTEGRAL_EQ THEN EXISTS_TAC (← q r"\x:real. &0") THEN
      ASM_REWRITE_TAC [DEFINT_0] THEN ASM_MESON_TAC []] THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_ADD_LID] THEN
    MATCH_MP_TAC DEFINT_COMBINE THEN EXISTS_TAC (← q "c:real") THEN
    ASM_REWRITE_TAC [DEFINT_DELTA_LEFT, DEFINT_DELTA_RIGHT])

  let DEFINT_POINT_SPIKE ← prove
   r"!f g a b c i.
        (!x. a <= x /\ x <= b /\ ~(x = c) ==> (f x = g x)) /\ defint(a,b) f i
        ==> defint(a,b) g i"
   (← do
    let ra ← REAL_ARITH (← q r"i = i + ((g:real->real) c - f c) * &0")
    pure (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q "a <= b") THENL
       [ALL_TAC, ASM_MESON_TAC [REAL_NOT_LE, DEFINT_WRONG]] THEN
      MATCH_MP_TAC INTEGRAL_EQ THEN
      EXISTS_TAC (← q r"\x:real. f(x) + (g c - f c) * (if x = c then &1 else &0)") THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [SUBST1_TAC ra THEN
        MATCH_MP_TAC DEFINT_ADD THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC DEFINT_CMUL THEN REWRITE_TAC [DEFINT_DELTA],
        REPEAT GEN_TAC THEN COND_CASES_TAC THEN
        ASM_SIMP_TAC [REAL_MUL_RZERO, REAL_ADD_RID] THEN
        REAL_ARITH_TAC]))

  let DEFINT_FINITE_SPIKE ← prove
   r"!f g a b s i.
        FINITE s /\
        (!x. a <= x /\ x <= b /\ ~(x IN s) ==> (f x = g x)) /\
        defint(a,b) f i
        ==> defint(a,b) g i"
   (← do
    let t ← TAUT (← q r"a /\ b /\ c ==> d <=> c ==> a ==> b ==> d")
    pure (REPEAT GEN_TAC THEN
      REWRITE_TAC [t] THEN
      DISCH_TAC THEN MAP_EVERY (fun t => SPEC_TAC (t, t))
       [← q r"g:real->real", ← q r"s:real->bool"] THEN
      REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
      REWRITE_TAC [NOT_IN_EMPTY] THEN
      CONJ_TAC THENL [ASM_MESON_TAC [INTEGRAL_EQ], ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [← q "c:real", ← q r"s:real->bool"] THEN STRIP_TAC THEN
      X_GEN_TAC (← q r"g:real->real") THEN REWRITE_TAC [IN_INSERT, DE_MORGAN_THM] THEN
      DISCH_TAC THEN MATCH_MP_TAC DEFINT_POINT_SPIKE THEN
      EXISTS_TAC (← q r"\x. if x = c then (f:real->real) x else g x") THEN
      EXISTS_TAC (← q "c:real") THEN SIMP_TAC [] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC []))

  -- Cauchy-type integrability criterion.

  let GAUGE_MIN_FINITE ← prove
   r"!s gs n. (!m:num. m <= n ==> gauge s (gs m))
            ==> ?g. gauge s g /\
                    !d p. fine g (d,p) ==> !m. m <= n ==> fine (gs m) (d,p)"
   (← do
    let t ← TAUT (← q r"a \/ b ==> c <=> (a ==> c) /\ (b ==> c)")
    pure (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [LE] THENL
       [MESON_TAC [], ALL_TAC] THEN
      REWRITE_TAC [t] THEN
      SIMP_TAC [FORALL_AND_THM, LEFT_FORALL_IMP_THM, EXISTS_REFL] THEN
      STRIP_TAC THEN FIRST_X_ASSUM (fun th => tactic_of do
        if is_imp (concl th) then pure (MP_TAC th) else throw "check") THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"gm:real->real") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"\x:real. if gm x < gs(SUC n) x then gm x else gs(SUC n) x") THEN
      ASM_SIMP_TAC [GAUGE_MIN, ETA_AX] THEN REPEAT GEN_TAC THEN
      DISCH_THEN (MP_TAC o MATCH_MP FINE_MIN) THEN ASM_SIMP_TAC [ETA_AX]))

  let INTEGRABLE_CAUCHY ← prove
   r"!f a b. integrable(a,b) f <=>
           !e. &0 < e
               ==> ?g. gauge (\x. a <= x /\ x <= b) g /\
                       !d1 p1 d2 p2.
                            tdiv (a,b) (d1,p1) /\ fine g (d1,p1) /\
                            tdiv (a,b) (d2,p2) /\ fine g (d2,p2)
                            ==> abs (rsum(d1,p1) f - rsum(d2,p2) f) < e"
   (← do
    let r3 ← REAL_ARITH
     (← q r"abs(s1 - i) < e / &2
      ==> d < e / &2
          ==> abs(s2 - s1) < d ==> abs(s2 - i) < e")
    let r2 ← REAL_ARITH (← q r"d < e ==> x < d ==> x < e")
    let r1 ← REAL_ARITH (← q r"b < a \/ a <= b")
    let d1 ← q r"d1:num->real"
    let p1 ← q r"p1:num->real"
    let d2 ← q r"d2:num->real"
    let p2 ← q r"p2:num->real"
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [integrable] THEN EQ_TAC THENL
       [REWRITE_TAC [defint] THEN DISCH_THEN (X_CHOOSE_TAC (← q "i:real")) THEN
        X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"e / &2")) THEN
        ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"g:real->real") THEN
        STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
        MAP_EVERY X_GEN_TAC [d1, p1, d2, p2] THEN
        STRIP_TAC THEN FIRST_X_ASSUM (fun th => tactic_of do
          let b2 ← SPECL [d2, p2] th
          let b1 ← SPECL [d1, p1] th
          pure (MP_TAC b1 THEN MP_TAC b2)) THEN
        ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC,
        ALL_TAC] THEN
      DISCH_TAC THEN DISJ_CASES_TAC r1 THENL
       [ASM_MESON_TAC [DEFINT_WRONG], ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o GEN (← q "n:num") o SPEC (← q r"&1 / &2 pow n")) THEN
      SIMP_TAC [REAL_LT_DIV, REAL_POW_LT, REAL_OF_NUM_LT, ARITH] THEN
      REWRITE_TAC [FORALL_AND_THM, SKOLEM_THM] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"g:num->real->real") STRIP_ASSUME_TAC) THEN
      MP_TAC (← GEN (← q "n:num")
       (← SPECL [← q r"\x. a <= x /\ x <= b", ← q r"g:num->real->real", ← q "n:num"]
              GAUGE_MIN_FINITE)) THEN
      ASM_REWRITE_TAC [SKOLEM_THM, FORALL_AND_THM] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"G:num->real->real") STRIP_ASSUME_TAC) THEN
      MP_TAC (← GEN (← q "n:num")
        (← SPECL [← q "a:real", ← q "b:real", ← q r"(G:num->real->real) n"] DIVISION_EXISTS)) THEN
      ASM_REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM, FORALL_AND_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"d:num->num->real", ← q r"p:num->num->real"] THEN
      STRIP_TAC THEN SUBGOAL_THEN (← q r"cauchy (\n. rsum(d n,p n) f)") MP_TAC THENL
       [REWRITE_TAC [cauchy] THEN X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN
        MP_TAC (← SPEC (← q r"&1 / e") REAL_ARCH_POW2) THEN MATCH_MP_TAC MONO_EXISTS THEN
        X_GEN_TAC (← q "N:num") THEN ASM_SIMP_TAC [REAL_LT_LDIV_EQ] THEN DISCH_TAC THEN
        REWRITE_TAC [GE] THEN MAP_EVERY X_GEN_TAC [← q "m:num", ← q "n:num"] THEN
        STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPECL
         [← q "N:num", ← q r"(d:num->num->real) m", ← q r"(p:num->num->real) m",
          ← q r"(d:num->num->real) n", ← q r"(p:num->num->real) n"]) THEN
        ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
        MATCH_MP_TAC r2 THEN
        ASM_SIMP_TAC [REAL_LT_LDIV_EQ, REAL_POW_LT, REAL_OF_NUM_LT, ARITH] THEN
        ASM_MESON_TAC [REAL_MUL_SYM],
        ALL_TAC] THEN
      REWRITE_TAC [SEQ_CAUCHY, convergent, SEQ, defint] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q "i:real") THEN STRIP_TAC THEN
      X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"e / &2")) THEN
      ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "N1:num") MP_TAC) THEN
      X_CHOOSE_TAC (← q "N2:num") (← SPEC (← q r"&2 / e") REAL_ARCH_POW2) THEN
      DISCH_THEN (MP_TAC o SPEC (← q "N1 + N2:num")) THEN REWRITE_TAC [GE, LE_ADD] THEN
      DISCH_TAC THEN EXISTS_TAC (← q r"(G:num->real->real)(N1 + N2)") THEN
      ASM_REWRITE_TAC [] THEN
      MAP_EVERY X_GEN_TAC [← q r"dx:num->real", ← q r"px:num->real"] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL
       [← q "N1 + N2:num", ← q r"dx:num->real", ← q r"px:num->real",
        ← q r"(d:num->num->real)(N1 + N2)", ← q r"(p:num->num->real)(N1 + N2)"]) THEN
      ANTS_TAC THENL [ASM_MESON_TAC [LE_REFL], ALL_TAC] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP r3) THEN
      REWRITE_TAC [real_div, REAL_MUL_LID] THEN REWRITE_TAC [← GSYM real_div] THEN
      GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_INV_DIV] THEN
      MATCH_MP_TAC REAL_LT_INV2 THEN
      ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q r"&2 pow N2") THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_POW_MONO THEN
      REWRITE_TAC [REAL_OF_NUM_LE] THEN ARITH_TAC))

  -- @@RETURN BEGIN
  return { DEFINT_DELTA_LEFT, DEFINT_DELTA_RIGHT, DEFINT_DELTA, DEFINT_POINT_SPIKE,
           DEFINT_FINITE_SPIKE, GAUGE_MIN_FINITE, INTEGRABLE_CAUCHY }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Limit theorem; continuous functions are integrable; integrability on a   -/
/- subinterval.  (transc.ml 5098-5369)                                       -/
/- ------------------------------------------------------------------------- -/

structure Limit where
  -- @@FIELDS
  SUM_DIFFS : thm
  RSUM_BOUND : thm
  RSUM_DIFF_BOUND : thm
  INTEGRABLE_LIMIT : thm
  INTEGRABLE_CONST : thm
  INTEGRABLE_COMBINE : thm
  INTEGRABLE_POINT_SPIKE : thm
  INTEGRABLE_CONTINUOUS : thm
  INTEGRABLE_SPLIT_SIDES : thm
  INTEGRABLE_SUBINTERVAL_LEFT : thm
  INTEGRABLE_SUBINTERVAL_RIGHT : thm
  INTEGRABLE_SUBINTERVAL : thm
  deriving Inhabited

@[nospecialize]
def setupLimit [HolBase] (D : TranscDeps) (BArcSinCos : ArcSinCos) (BDivision : Division) (BDivAppend : DivAppend) (BGauge : Gauge) (BIntegral : Integral) (BCombine : Combine) (BSpike : Spike) (AReals1 : HolLibrary.Analysis.Reals1) (AReals2 : HolLibrary.Analysis.Reals2) (APow : HolLibrary.Analysis.Pow) (ASums : HolLibrary.Analysis.Sums) (ASeqs : HolLibrary.Analysis.Seqs) (ASeqs2 : HolLibrary.Analysis.Seqs2) (ASeries1 : HolLibrary.Analysis.Series1) (AUniform : HolLibrary.Analysis.Uniform) :
    ExceptT String IO Limit := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, INDUCT_TAC, MESON_TAC,
        REAL_ARITH, REAL_ARITH_TAC, .. } := D
  let { ADD_CLAUSES, AND_FORALL_THM, ARITH, FORALL_AND_THM, GE, IMP_IMP,
        LEFT_IMP_EXISTS_THM, MONO_EXISTS, MONO_FORALL, REAL_ABS_MUL, REAL_ABS_POS,
        real_abs, .. } := D.core1
  let { REAL_LE_INV2, REAL_LE_LDIV_EQ, REAL_LE_LMUL, REAL_LE_RMUL, REAL_LT_DIV,
        REAL_MUL_LID, REAL_MUL_SYM, REAL_OF_NUM_LE, REAL_OF_NUM_LT, REAL_POW_LT,
        REAL_POW_MONO, SKOLEM_THM, SWAP_FORALL_THM, real_div, .. } := D.core2
  let { defint, gauge, rsum, tdiv, .. } := BArcSinCos
  let { DIVISION_LBOUND, DIVISION_LE, DIVISION_UBOUND, .. } := BDivision
  let { DIVISION_APPEND_STRONG, DIVISION_EXISTS, .. } := BDivAppend
  let { FINE_MIN, GAUGE_MIN, .. } := BGauge
  let { DEFINT_CONST, DEFINT_WRONG, DIVISION_MONO_LE_SUC, integrable, .. } := BIntegral
  let { DEFINT_COMBINE, .. } := BCombine
  let { DEFINT_POINT_SPIKE, INTEGRABLE_CAUCHY, .. } := BSpike
  let { REAL_LE_REFL, REAL_LE_TOTAL, REAL_LE_TRANS, REAL_LT_IMP_LE, REAL_NOT_LE, .. } := AReals1
  let { REAL_SUB_LE, REAL_SUB_RDISTRIB, REAL_SUB_REFL, .. } := AReals2
  let { REAL_ARCH_POW2, .. } := APow
  let { SUM_ABS_LE, SUM_CMUL, SUM_LE, SUM_SUB, sum, .. } := ASums
  let { SEQ, cauchy, convergent, .. } := ASeqs
  let { SEQ_CAUCHY, .. } := ASeqs2
  let { BOLZANO_LEMMA_ALT, .. } := ASeries1
  let { CONT_UNIFORM, .. } := AUniform
  -- @@SCOPE END

  -- Rebinds the core SUM_DIFFS.
  let SUM_DIFFS ← prove
   r"!m n. sum(m,n) (\i. d(SUC i) - d(i)) = d(m + n) - d m"
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [sum, ADD_CLAUSES, REAL_SUB_REFL] THEN REAL_ARITH_TAC)

  let RSUM_BOUND ← prove
   r"!a b d p e f.
        tdiv(a,b) (d,p) /\
        (!x. a <= x /\ x <= b ==> abs(f x) <= e)
        ==> abs(rsum(d,p) f) <= e * (b - a)"
   (← do
    let ra ← REAL_ARITH (← q r"a <= d0 /\ d1 <= b ==> d1 - d0 <= b - a")
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [rsum] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"sum(0,dsize d) (\i. abs(f(p i :real) * (d(SUC i) - d i)))") THEN
      REWRITE_TAC [SUM_ABS_LE] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"sum(0,dsize d) (\i. e * abs(d(SUC i) - d(i)))") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC [ADD_CLAUSES, REAL_ABS_MUL] THEN
        X_GEN_TAC (← q "r:num") THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        REWRITE_TAC [REAL_ABS_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_MESON_TAC [tdiv, DIVISION_UBOUND, DIVISION_LBOUND, REAL_LE_TRANS],
        ALL_TAC] THEN
      REWRITE_TAC [SUM_CMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [FIRST_X_ASSUM (MP_TAC o SPEC (← q "a:real")) THEN
        ASM_MESON_TAC [REAL_LE_REFL, REAL_ABS_POS, REAL_LE_TRANS, DIVISION_LE,
                      tdiv],
        ALL_TAC] THEN
      FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o REWRITE_RULE [tdiv]) THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP DIVISION_MONO_LE_SUC) THEN
      ASM_REWRITE_TAC [real_abs, REAL_SUB_LE, SUM_DIFFS, ADD_CLAUSES] THEN
      MATCH_MP_TAC ra THEN
      ASM_MESON_TAC [DIVISION_LBOUND, DIVISION_UBOUND]))

  let RSUM_DIFF_BOUND ← prove
   r"!a b d p e f g.
        tdiv(a,b) (d,p) /\
        (!x. a <= x /\ x <= b ==> abs(f x - g x) <= e)
        ==> abs(rsum (d,p) f - rsum (d,p) g) <= e * (b - a)"
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP RSUM_BOUND) THEN
    REWRITE_TAC [rsum, SUM_SUB, REAL_SUB_RDISTRIB])

  let INTEGRABLE_LIMIT ← prove
   r"!f a b. (!e. &0 < e
                ==> ?g. (!x. a <= x /\ x <= b ==> abs(f x - g x) <= e) /\
                        integrable(a,b) g)
           ==> integrable(a,b) f"
   (← do
    let r6 ← ARITH_RULE (← q r"N2 <= N1 + N2:num")
    let r5 ← REAL_ARITH (← q r"&1 / n * x <= e / &3 <=> (&3 * x) / n <= e")
    let r4 ← REAL_ARITH
     (← q r"abs(sf - sg) <= e / &3
      ==> abs(i - s) < e / &3 ==> abs(sg - i) < e / &3 ==> abs(sf - s) < e")
    let r3 ← ARITH_RULE (← q r"N1:num <= N1 + N2")
    let r2 ← REAL_ARITH (← q r"&2 / n * x <= e / &2 <=> (&4 * x) / n <= e")
    let r1 ← REAL_ARITH
     (← q r"!f. abs(f - gm) <= inv(k) /\ abs(f - gn) <= inv(k)
            ==> abs(gm - gn) <= &2 / k")
    let tm ← q "m:num"
    let tn ← q "n:num"
    pure (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q "a <= b") THENL
       [ALL_TAC, ASM_MESON_TAC [REAL_NOT_LE, DEFINT_WRONG, integrable]] THEN
      FIRST_X_ASSUM (MP_TAC o GEN (← q "n:num") o SPEC (← q r"&1 / &2 pow n")) THEN
      SIMP_TAC [REAL_LT_DIV, REAL_POW_LT, REAL_OF_NUM_LT, ARITH] THEN
      REWRITE_TAC [FORALL_AND_THM, SKOLEM_THM, integrable] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"g:num->real->real") (CONJUNCTS_THEN2
       ASSUME_TAC (X_CHOOSE_TAC (← q r"i:num->real")))) THEN
      SUBGOAL_THEN (← q "cauchy i") MP_TAC THENL
       [REWRITE_TAC [cauchy] THEN X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN
        MP_TAC (← SPEC (← q r"(&4 * (b - a)) / e") REAL_ARCH_POW2) THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q "N:num") THEN DISCH_TAC THEN
        MAP_EVERY X_GEN_TAC [← q "m:num", ← q "n:num"] THEN REWRITE_TAC [GE] THEN
        STRIP_TAC THEN
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE BINDER_CONV [defint]) THEN
        ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"e / &4")) THEN
        ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
        DISCH_THEN (fun th => tactic_of do
          let b2 ← SPEC tn th
          let b1 ← SPEC tm th
          pure (MP_TAC b1 THEN MP_TAC b2)) THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"gn:real->real") STRIP_ASSUME_TAC) THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"gm:real->real") STRIP_ASSUME_TAC) THEN
        MP_TAC (← SPECL [← q "a:real", ← q "b:real",
                      ← q r"\x:real. if gm x < gn x then gm x else gn x"]
                     DIVISION_EXISTS) THEN
        ASM_SIMP_TAC [GAUGE_MIN, LEFT_IMP_EXISTS_THM] THEN
        MAP_EVERY X_GEN_TAC [← q r"d:num->real", ← q r"p:num->real"] THEN
        STRIP_TAC THEN
        FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o MATCH_MP FINE_MIN) THEN
        REPEAT (FIRST_X_ASSUM (MP_TAC o SPECL [← q r"d:num->real", ← q r"p:num->real"])) THEN
        ASM_REWRITE_TAC [] THEN
        SUBGOAL_THEN (← q r"abs(rsum(d,p) (g(m:num)) - rsum(d,p) (g n)) <= e / &2")
         (fun th => MP_TAC th THEN REAL_ARITH_TAC) THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"&2 / &2 pow N * (b - a)") THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC RSUM_DIFF_BOUND THEN ASM_REWRITE_TAC [] THEN
          REPEAT STRIP_TAC THEN MATCH_MP_TAC r1 THEN
          EXISTS_TAC (← q r"(f:real->real) x") THEN CONJ_TAC THEN
          MATCH_MP_TAC REAL_LE_TRANS THENL
           [EXISTS_TAC (← q r"&1 / &2 pow m"), EXISTS_TAC (← q r"&1 / &2 pow n")] THEN
          ASM_SIMP_TAC [] THEN REWRITE_TAC [real_div, REAL_MUL_LID] THEN
          MATCH_MP_TAC REAL_LE_INV2 THEN
          ASM_SIMP_TAC [REAL_POW_LT, REAL_POW_MONO, REAL_OF_NUM_LE,
                       REAL_OF_NUM_LT, ARITH],
          ALL_TAC] THEN
        REWRITE_TAC [r2] THEN
        SIMP_TAC [REAL_LE_LDIV_EQ, REAL_POW_LT, REAL_OF_NUM_LT, ARITH] THEN
        GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
        ASM_SIMP_TAC [← GSYM REAL_LE_LDIV_EQ, REAL_LT_IMP_LE],
        ALL_TAC] THEN
      REWRITE_TAC [SEQ_CAUCHY, convergent] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q "s:real") THEN DISCH_TAC THEN
      REWRITE_TAC [defint] THEN X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"e / &3") o GEN_REWRITE_RULE id [SEQ]) THEN
      ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH, GE] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q "N1:num")) THEN
      MP_TAC (← SPEC (← q r"(&3 * (b - a)) / e") REAL_ARCH_POW2) THEN
      DISCH_THEN (X_CHOOSE_TAC (← q "N2:num")) THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE BINDER_CONV [defint]) THEN
      DISCH_THEN (MP_TAC o SPECL [← q "N1 + N2:num", ← q r"e / &3"]) THEN
      ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
      MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC (← q r"g:real->real") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      MAP_EVERY X_GEN_TAC [← q r"d:num->real", ← q r"p:num->real"] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [← q r"d:num->real", ← q r"p:num->real"]) THEN
      ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MP_TAC o (fun a => MATCH_MP a r3)) THEN
      MATCH_MP_TAC r4 THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"&1 / &2 pow (N1 + N2) * (b - a)") THEN CONJ_TAC THENL
       [MATCH_MP_TAC RSUM_DIFF_BOUND THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
      REWRITE_TAC [r5] THEN
      SIMP_TAC [REAL_LE_LDIV_EQ, REAL_POW_LT, REAL_OF_NUM_LT, ARITH] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      ASM_SIMP_TAC [← GSYM REAL_LE_LDIV_EQ, REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"&2 pow N2") THEN
      ASM_SIMP_TAC [REAL_LT_IMP_LE, REAL_POW_MONO, REAL_OF_NUM_LE, ARITH,
                   r6]))

  -- Hence continuous functions are integrable.

  let INTEGRABLE_CONST ← prove
   r"!a b c. integrable(a,b) (\x. c)"
   (REWRITE_TAC [integrable] THEN MESON_TAC [DEFINT_CONST])

  let INTEGRABLE_COMBINE ← prove
   r"!f a b c. a <= b /\ b <= c /\ integrable(a,b) f /\ integrable(b,c) f
         ==> integrable(a,c) f"
   (REWRITE_TAC [integrable] THEN MESON_TAC [DEFINT_COMBINE])

  let INTEGRABLE_POINT_SPIKE ← prove
   r"!f g a b c.
         (!x. a <= x /\ x <= b /\ ~(x = c) ==> f x = g x) /\ integrable(a,b) f
         ==> integrable(a,b) g"
   (REWRITE_TAC [integrable] THEN MESON_TAC [DEFINT_POINT_SPIKE])

  let INTEGRABLE_CONTINUOUS ← prove
   r"!f a b. (!x. a <= x /\ x <= b ==> f contl x) ==> integrable(a,b) f"
   (← do
    let r3 ← REAL_ARITH (← q r"b <= x /\ x <= c /\ ~(x = b) ==> ~(x <= b)")
    let r2 ← TAUT
     (← q r"(a /\ b) /\ (c /\ d ==> e) ==> (a ==> c) /\ (b ==> d) ==> e")
    let r1 ← REAL_ARITH (← q r"b < a \/ a <= b")
    pure (REPEAT STRIP_TAC THEN DISJ_CASES_TAC r1 THENL
       [ASM_MESON_TAC [integrable, DEFINT_WRONG], ALL_TAC] THEN
      MATCH_MP_TAC INTEGRABLE_LIMIT THEN X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN
      MP_TAC (← SPECL [← q r"f:real->real", ← q "a:real", ← q "b:real"] CONT_UNIFORM) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o SPEC (← q "e:real")) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "d:real") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      UNDISCH_TAC (← q "a <= b") THEN MAP_EVERY (fun t => SPEC_TAC (t, t))
       [← q "b:real", ← q "a:real"] THEN
      MATCH_MP_TAC BOLZANO_LEMMA_ALT THEN CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [← q "u:real", ← q "v:real", ← q "w:real"] THEN
        REPLICATE_TAC 2 (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN (fun th => DISCH_TAC THEN MP_TAC th) THEN
        MATCH_MP_TAC r2 THEN
        CONJ_TAC THENL [ASM_MESON_TAC [REAL_LE_TRANS], ALL_TAC] THEN
        DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"g:real->real"))
                                   (X_CHOOSE_TAC (← q r"h:real->real"))) THEN
        EXISTS_TAC (← q r"\x. if x <= v then g(x):real else h(x)") THEN
        REWRITE_TAC [] THEN CONJ_TAC THENL
         [ASM_MESON_TAC [REAL_LE_TOTAL], ALL_TAC] THEN
        MATCH_MP_TAC INTEGRABLE_COMBINE THEN EXISTS_TAC (← q "v:real") THEN
        ASM_REWRITE_TAC [] THEN CONJ_TAC THEN
        MATCH_MP_TAC INTEGRABLE_POINT_SPIKE THENL
         [EXISTS_TAC (← q r"g:real->real"), EXISTS_TAC (← q r"h:real->real")] THEN
        EXISTS_TAC (← q "v:real") THEN ASM_REWRITE_TAC [] THEN SIMP_TAC [] THEN
        ASM_MESON_TAC [r3],
        ALL_TAC] THEN
      X_GEN_TAC (← q "x:real") THEN EXISTS_TAC (← q "d:real") THEN ASM_REWRITE_TAC [] THEN
      MAP_EVERY X_GEN_TAC [← q "u:real", ← q "v:real"] THEN REPEAT STRIP_TAC THEN
      EXISTS_TAC (← q r"\x:real. (f:real->real) u") THEN
      ASM_REWRITE_TAC [INTEGRABLE_CONST] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC))

  -- Integrability on a subinterval.

  let INTEGRABLE_SPLIT_SIDES ← prove
   r"!f a b c.
        a <= c /\ c <= b /\ integrable(a,b) f
        ==> ?i. !e. &0 < e
                    ==> ?g. gauge(\x. a <= x /\ x <= b) g /\
                            !d1 p1 d2 p2. tdiv(a,c) (d1,p1) /\
                                          fine g (d1,p1) /\
                                          tdiv(c,b) (d2,p2) /\
                                          fine g (d2,p2)
                                          ==> abs((rsum(d1,p1) f +
                                                   rsum(d2,p2) f) - i) < e"
   (REPEAT GEN_TAC THEN REWRITE_TAC [integrable, defint] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q "i:real") THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q "e:real") THEN
    ASM_CASES_TAC (← q r"&0 < e") THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"g:real->real") THEN
    ASM_MESON_TAC [DIVISION_APPEND_STRONG])

  let INTEGRABLE_SUBINTERVAL_LEFT ← prove
   r"!f a b c. a <= c /\ c <= b /\ integrable(a,b) f ==> integrable(a,c) f"
   (← do
    let ae ← ASSUME (← q r"&0 < e")
    let d1 ← q r"d1:num->real"
    let p1 ← q r"p1:num->real"
    let d2 ← q r"d2:num->real"
    let p2 ← q r"p2:num->real"
    pure (REPEAT GEN_TAC THEN DISCH_TAC THEN
      FIRST_ASSUM (X_CHOOSE_TAC (← q "i:real") o MATCH_MP INTEGRABLE_SPLIT_SIDES) THEN
      REWRITE_TAC [INTEGRABLE_CAUCHY] THEN X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"e / &2")) THEN
      SIMP_TAC [ae, REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"g:real->real") THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [gauge]) THEN
        REWRITE_TAC [gauge] THEN ASM_MESON_TAC [REAL_LE_TRANS],
        ALL_TAC] THEN
      REPEAT STRIP_TAC THEN
      MP_TAC (← SPECL [← q "c:real", ← q "b:real", ← q r"g:real->real"] DIVISION_EXISTS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [] THEN
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [gauge]) THEN
        REWRITE_TAC [gauge] THEN ASM_MESON_TAC [REAL_LE_TRANS],
        ALL_TAC] THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"d:num->real", ← q r"p:num->real"] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (fun th => tactic_of do
        let b2 ← SPECL [d2, p2] th
        let b1 ← SPECL [d1, p1] th
        pure (MP_TAC b1 THEN MP_TAC b2)) THEN
      REWRITE_TAC [IMP_IMP, AND_FORALL_THM] THEN
      DISCH_THEN (MP_TAC o SPECL [← q r"d:num->real", ← q r"p:num->real"]) THEN
      ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC))

  let INTEGRABLE_SUBINTERVAL_RIGHT ← prove
   r"!f a b c. a <= c /\ c <= b /\ integrable(a,b) f ==> integrable(c,b) f"
   (← do
    let ae ← ASSUME (← q r"&0 < e")
    let d1 ← q r"d1:num->real"
    let p1 ← q r"p1:num->real"
    let d2 ← q r"d2:num->real"
    let p2 ← q r"p2:num->real"
    pure (REPEAT GEN_TAC THEN DISCH_TAC THEN
      FIRST_ASSUM (X_CHOOSE_TAC (← q "i:real") o MATCH_MP INTEGRABLE_SPLIT_SIDES) THEN
      REWRITE_TAC [INTEGRABLE_CAUCHY] THEN X_GEN_TAC (← q "e:real") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"e / &2")) THEN
      SIMP_TAC [ae, REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"g:real->real") THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [gauge]) THEN
        REWRITE_TAC [gauge] THEN ASM_MESON_TAC [REAL_LE_TRANS],
        ALL_TAC] THEN
      REPEAT STRIP_TAC THEN
      MP_TAC (← SPECL [← q "a:real", ← q "c:real", ← q r"g:real->real"] DIVISION_EXISTS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [] THEN
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [gauge]) THEN
        REWRITE_TAC [gauge] THEN ASM_MESON_TAC [REAL_LE_TRANS],
        ALL_TAC] THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"d:num->real", ← q r"p:num->real"] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [← q r"d:num->real", ← q r"p:num->real"]) THEN
      DISCH_THEN (fun th => tactic_of do
        let b2 ← SPECL [d2, p2] th
        let b1 ← SPECL [d1, p1] th
        pure (MP_TAC b1 THEN MP_TAC b2)) THEN
      ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC))

  let INTEGRABLE_SUBINTERVAL ← prove
   r"!f a b c d. a <= c /\ c <= d /\ d <= b /\ integrable(a,b) f
               ==> integrable(c,d) f"
   (MESON_TAC [INTEGRABLE_SUBINTERVAL_LEFT, INTEGRABLE_SUBINTERVAL_RIGHT,
              REAL_LE_TRANS])

  -- @@RETURN BEGIN
  return { SUM_DIFFS, RSUM_BOUND, RSUM_DIFF_BOUND, INTEGRABLE_LIMIT, INTEGRABLE_CONST,
           INTEGRABLE_COMBINE, INTEGRABLE_POINT_SPIKE, INTEGRABLE_CONTINUOUS,
           INTEGRABLE_SPLIT_SIDES, INTEGRABLE_SUBINTERVAL_LEFT,
           INTEGRABLE_SUBINTERVAL_RIGHT, INTEGRABLE_SUBINTERVAL }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Basic integrability rule for everywhere-differentiable function; more    -/
/- basic lemmas about integration; the SYM_CANON_CONV and EXT_CONV rebinds.  -/
/- (transc.ml 5371-5456)                                                     -/
/- ------------------------------------------------------------------------- -/

structure IntRule where
  -- @@FIELDS
  INTEGRABLE_RULE : term → ExceptT String IO thm
  INTEGRABLE_CONV : ioconv
  INTEGRAL_CONST : thm
  INTEGRAL_CMUL : thm
  INTEGRAL_ADD : thm
  INTEGRAL_SUB : thm
  INTEGRAL_BY_PARTS : thm
  SYM_CANON_CONV : thm → (term × term → Bool) → ioconv
  EXT_CONV : term → ExceptT String IO thm
  deriving Inhabited

@[nospecialize]
def setupIntRule [HolBase] (D : TranscDeps) (BDiffConv : DiffConv) (BIntegral : Integral) (BLimit : Limit) (ACompat : HolLibrary.Analysis.Compat) :
    ExceptT String IO IntRule := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, REAL_ARITH_TAC, .. } := D
  let { FORALL_SIMP, MONO_FORALL, .. } := D.core1
  let { CONTINUOUS_CONV, .. } := BDiffConv
  let { DEFINT_ADD, DEFINT_CMUL, DEFINT_CONST, DEFINT_INTEGRAL, DEFINT_SUB,
        INTEGRABLE_DEFINT, INTEGRATION_BY_PARTS, .. } := BIntegral
  let { INTEGRABLE_CONTINUOUS, .. } := BLimit
  let { X_FUN_EQ_CONV, .. } := ACompat
  -- @@SCOPE END

  let INTEGRABLE_RULE : term → ExceptT String IO thm ← do
    let pth ← prove
     r"(!x. f contl x) ==> integrable(a,b) f"
     (MESON_TAC [INTEGRABLE_CONTINUOUS])
    -- `let match_pth = ... and forsimp = ...`: left to right.
    let match_pth := PART_MATCH rand pth
    let forsimpConv ← GEN_REWRITE_CONV_NET LAND_CONV [FORALL_SIMP]
    let forsimp := CONV_RULE forsimpConv
    pure (fun tm => do
      let th1 ← match_pth tm
      let th2 ← CONV_RULE (LAND_CONV (BINDER_CONV CONTINUOUS_CONV)) th1
      MP (← forsimp th2) HolBase.B.TRUTH)

  let INTEGRABLE_CONV : ioconv ← pure (fun tm => (EQT_INTRO o INTEGRABLE_RULE) tm |>.run)

  -- More basic lemmas about integration.

  let INTEGRAL_CONST ← prove
   r"!a b c. a <= b ==> integral(a,b) (\x. c) = c * (b - a)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC DEFINT_INTEGRAL THEN
    ASM_SIMP_TAC [DEFINT_CONST])

  let INTEGRAL_CMUL ← prove
   r"!f c a b. a <= b /\ integrable(a,b) f
             ==> integral(a,b) (\x. c * f(x)) = c * integral(a,b) f"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC DEFINT_INTEGRAL THEN
    ASM_SIMP_TAC [DEFINT_CMUL, INTEGRABLE_DEFINT])

  let INTEGRAL_ADD ← prove
   r"!f g a b. a <= b /\ integrable(a,b) f /\ integrable(a,b) g
             ==> integral(a,b) (\x. f(x) + g(x)) =
                 integral(a,b) f + integral(a,b) g"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC DEFINT_INTEGRAL THEN
    ASM_SIMP_TAC [DEFINT_ADD, INTEGRABLE_DEFINT])

  let INTEGRAL_SUB ← prove
   r"!f g a b. a <= b /\ integrable(a,b) f /\ integrable(a,b) g
             ==> integral(a,b) (\x. f(x) - g(x)) =
                 integral(a,b) f - integral(a,b) g"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC DEFINT_INTEGRAL THEN
    ASM_SIMP_TAC [DEFINT_SUB, INTEGRABLE_DEFINT])

  let INTEGRAL_BY_PARTS ← prove
   r"!f g f' g' a b.
         a <= b /\
         (!x. a <= x /\ x <= b ==> (f diffl f' x) x) /\
         (!x. a <= x /\ x <= b ==> (g diffl g' x) x) /\
         integrable(a,b) (\x. f' x * g x) /\
         integrable(a,b) (\x. f x * g' x)
         ==> integral(a,b) (\x. f x * g' x) =
             (f b * g b - f a * g a) - integral(a,b) (\x. f' x * g x)"
   (← do
    let aab ← ASSUME (← q "a <= b")
    pure (MP_TAC INTEGRATION_BY_PARTS THEN
      REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
      DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o CONJ aab) THEN
      DISCH_THEN (SUBST1_TAC o SYM o MATCH_MP DEFINT_INTEGRAL) THEN
      ASM_SIMP_TAC [INTEGRAL_ADD] THEN REAL_ARITH_TAC))

  -- SYM_CANON_CONV - Canonicalizes single application of symmetric operator
  -- (rebinds analysis.ml's, with the same code).
  let SYM_CANON_CONV : thm → (term × term → Bool) → ioconv ← pure (fun sym fn tm => ExceptT.run do
    -- `check (not o fn o ((snd o dest_comb) F_F I) o dest_comb)`
    let (f, x) ← liftExcept (dest_comb tm)
    let (_, fx) ← liftExcept (dest_comb f)
    if !(fn (fx, x)) then ExceptT.mk (REWR_CONV sym tm) else throw "check")

  -- EXT_CONV `!x. f x = g x` = |- (!x. f x = g x) <=> (f = g)
  -- (rebinds analysis.ml's, with the same code).
  let EXT_CONV : term → ExceptT String IO thm ← pure (fun tm => do
    let (v, bod) ← liftExcept (dest_forall tm)
    let (l, r) ← liftExcept (dest_eq bod)
    -- `(rator F_F rator)`: the pair is built right to left.
    let rr ← liftExcept (rator r)
    let rl ← liftExcept (rator l)
    let mkEq ← ExceptT.mk (mk_eq : IO _)
    SYM (← ExceptT.mk (X_FUN_EQ_CONV v (← liftExcept (mkEq (rl, rr))))))

  -- @@RETURN BEGIN
  return { INTEGRABLE_RULE, INTEGRABLE_CONV, INTEGRAL_CONST, INTEGRAL_CMUL, INTEGRAL_ADD,
           INTEGRAL_SUB, INTEGRAL_BY_PARTS, SYM_CANON_CONV, EXT_CONV }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Mclaurin's theorem with Lagrange form of remainder; the "bidirectional"   -/
/- version.  (transc.ml 5452-5752)                                           -/
/- ------------------------------------------------------------------------- -/

structure Mclaurin where
  -- @@FIELDS
  MCLAURIN : thm
  MCLAURIN_NEG : thm
  MCLAURIN_BI_LE : thm
  deriving Inhabited

@[nospecialize]
def setupMclaurin [HolBase] (D : TranscDeps) (BDiffConv : DiffConv) (ACompat : HolLibrary.Analysis.Compat) (ANames : HolLibrary.Analysis.Names) (ATactics : HolLibrary.Analysis.Tactics) (AReals1 : HolLibrary.Analysis.Reals1) (AReals2 : HolLibrary.Analysis.Reals2) (AReals3 : HolLibrary.Analysis.Reals3) (APow : HolLibrary.Analysis.Pow) (ASums : HolLibrary.Analysis.Sums) (ASumConv : HolLibrary.Analysis.SumConv) (ALims : HolLibrary.Analysis.Lims) (ADiffs : HolLibrary.Analysis.Diffs) (AMvt : HolLibrary.Analysis.Mvt) :
    ExceptT String IO Mclaurin := do
  -- @@SCOPE BEGIN
  let { INDUCT_TAC, REAL_ARITH, .. } := D
  let { ADD1, ADD_ASSOC, ADD_CLAUSES, ADD_SUB, ADD_SYM, CONJ_ACI, EQ_IMP, FACT,
        FACT_LT, LT_0, LT_NZ, LT_REFL, LT_TRANS, MONO_EXISTS, NOT_SUC, REAL_ADD_LID,
        REAL_ADD_RID, num_CASES, .. } := D.core1
  let { REAL_ADD_SYM, REAL_DIV_1, REAL_EQ_SUB_LADD, REAL_EQ_SUB_RADD, REAL_LT_TRANS,
        REAL_MUL_AC, REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_SYM,
        REAL_POW_1, REAL_POW_ADD, SUB_0, SUB_REFL, real_div, real_pow, .. } := D.core2
  let { DIFF_CONV, .. } := BDiffConv
  let { FUN_EQ_CONV, .. } := ACompat
  let { LESS_ADD_1, LESS_SUC_REFL, SUC_SUB1, .. } := ANames
  let { EXPAND_TAC, HABS_CONV, IMP_SUBST_TAC, .. } := ATactics
  let { REAL_ADD_LID_UNIQ, REAL_LE_REFL, REAL_LE_TRANS, REAL_LT_IMP_LE, REAL_MUL_LZERO,
        REAL_MUL_RID, REAL_MUL_RZERO, REAL_NEG_GT0, REAL_NEG_NEG, .. } := AReals1
  let { REAL_DIV_LZERO, REAL_INJ, REAL_INV1, REAL_INVINV, REAL_INV_POS, REAL_LT,
        REAL_MUL, REAL_NEG_0, REAL_NEG_MINUS1, REAL_SUB_0, REAL_SUB_REFL, .. } := AReals2
  let { REAL_FACT_NZ, REAL_INV_MUL_WEAK, REAL_LE_NEG2, REAL_LT_IMP_NZ, REAL_LT_NEG2,
        REAL_SUB_RZERO, .. } := AReals3
  let { POW_0, POW_2, POW_MUL, POW_NZ, pow, .. } := APow
  let { SUM_0, SUM_1, SUM_EQ, SUM_OFFSET, sum, .. } := ASums
  let { REAL_SUM_CONV, .. } := ASumConv
  let { DIFF_CONT, DIFF_UNIQ, differentiable, .. } := ALims
  let { DIFF_ADD, DIFF_CHAIN, DIFF_CMUL, DIFF_CONST, DIFF_SUB, DIFF_SUM, .. } := ADiffs
  let { ROLLE, .. } := AMvt
  -- @@SCOPE END
  -- `W(MP_TAC o DIFF_CONV o rand o funpow 2 rator o snd)`
  let mpDiffConv : tactic := fun gl => ExceptT.run do
    let t ← liftExcept (do rand (← funpow 2 (fun (m : Except String term) => do
      rator (← m)) (pure gl.2)))
    ExceptT.mk (MP_TAC (← ExceptT.mk (DIFF_CONV t)) gl)
  -- `W(C SUBGOAL_THEN ttac o funpow 2 (fst o dest_imp) o snd)`
  let subgoalAnte2 (ttac : thm_tactic) : tactic := fun gl => ExceptT.run do
    let t ← liftExcept (funpow 2 (fun (m : Except String term) => do
      pure (← dest_imp (← m)).1) (pure gl.2))
    ExceptT.mk (SUBGOAL_THEN t ttac gl)

  let MCLAURIN ← prove
   r"!f diff h n.
    &0 < h /\
    0 < n /\
    (diff(0) = f) /\
    (!m t. m < n /\ &0 <= t /\ t <= h ==>
           (diff(m) diffl diff(SUC m)(t))(t)) ==>
   (?t. &0 < t /\ t < h /\
        (f(h) = sum(0,n)(\m. (diff(m)(&0) / &(FACT m)) * (h pow m)) +
                ((diff(n)(t) / &(FACT n)) * (h pow n))))"
   (← do
    -- Built when OCaml builds the tactic (none of these print).
    let ac6 ← AC REAL_MUL_AC (← q r"(a * b) * c = a * (c * b)")
    let ac5 ← AC REAL_MUL_AC (← q r"a * b * c * d = c * (a * d) * b")
    let ac4 ← AC REAL_MUL_AC
       (← q r"a * b * c * d * e * f * g = (b * a) * (d * f) * (c * g) * e")
    let ac3 ← AC REAL_MUL_AC (← q r"a * b * c * d = b * (a * (d * c))")
    let ac1 ← AC REAL_MUL_AC (← q r"a * b * c * d = (d * a) * (b * c)")
    let aDifg0 ← ASSUME (← q r"difg(0):real->real = g")
    let tj ← q r"j:num->real"
    let tt ← q "t:real"
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
      UNDISCH_TAC (← q "0 < n") THEN
      DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN (← q "r:num") MP_TAC)
       (← SPEC (← q "n:num") num_CASES) THEN REWRITE_TAC [LT_REFL] THEN
      DISCH_THEN (ASSUME_TAC o SYM) THEN DISCH_THEN (fun _ => ALL_TAC) THEN
      SUBGOAL_THEN (← q r"?B. f(h) = sum(0,n)(\m. (diff(m)(&0) / &(FACT m)) * (h pow m))
                    + (B * ((h pow n) / &(FACT n)))") MP_TAC THENL
       [ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
        ONCE_REWRITE_TAC [← GSYM REAL_EQ_SUB_RADD] THEN
        EXISTS_TAC (← q r"(f(h) - sum(0,n)(\m. (diff(m)(&0) / &(FACT m)) * (h pow m)))
            * &(FACT n) / (h pow n)") THEN REWRITE_TAC [real_div] THEN
        REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN
        GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [← GSYM REAL_MUL_RID] THEN
        AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
        ONCE_REWRITE_TAC [ac1] THEN
        GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_LID] THEN BINOP_TAC THEN
        MATCH_MP_TAC REAL_MUL_LINV THENL
         [MATCH_MP_TAC REAL_LT_IMP_NZ THEN REWRITE_TAC [REAL_LT, FACT_LT],
          MATCH_MP_TAC POW_NZ THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
          ASM_REWRITE_TAC []], ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "B:real") (ASSUME_TAC o SYM)) THEN
      ABBREV_TAC (← q r"g = \t. f(t) -
                          (sum(0,n)(\m. (diff(m)(&0) / &(FACT m)) * (t pow m)) +
                           (B * ((t pow n) / &(FACT n))))") THEN
      SUBGOAL_THEN (← q r"(g(&0) = &0) /\ (g(h) = &0)") ASSUME_TAC THENL
       [EXPAND_TAC "g" THEN BETA_TAC THEN ASM_REWRITE_TAC [REAL_SUB_REFL] THEN
        EXPAND_TAC "n" THEN REWRITE_TAC [POW_0, REAL_DIV_LZERO] THEN
        REWRITE_TAC [REAL_MUL_RZERO, REAL_ADD_RID] THEN REWRITE_TAC [REAL_SUB_0] THEN
        MP_TAC (← GEN tj
         (← SPECL [tj, ← q "r:num", ← q "1"] SUM_OFFSET)) THEN
        REWRITE_TAC [ADD1, REAL_EQ_SUB_LADD] THEN
        DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← GSYM th])) THEN BETA_TAC THEN
        REWRITE_TAC [SUM_1] THEN BETA_TAC THEN REWRITE_TAC [pow, FACT] THEN
        ASM_REWRITE_TAC [real_div, REAL_INV1, REAL_MUL_RID] THEN
        CONV_TAC SYM_CONV THEN REWRITE_TAC [REAL_ADD_LID_UNIQ] THEN
        REWRITE_TAC [← GSYM ADD1, POW_0, REAL_MUL_RZERO, SUM_0], ALL_TAC] THEN
      ABBREV_TAC (← q r"difg = \m t. diff(m) t -
          (sum(0,n - m)(\p. (diff(m + p)(&0) / &(FACT p)) * (t pow p))
           + (B * ((t pow (n - m)) / &(FACT(n - m)))))") THEN
      SUBGOAL_THEN (← q r"difg(0):real->real = g") ASSUME_TAC THENL
       [EXPAND_TAC "difg" THEN BETA_TAC THEN EXPAND_TAC "g" THEN
        CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC THEN
        ASM_REWRITE_TAC [ADD_CLAUSES, SUB_0], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"(!m t. m < n /\ (& 0) <= t /\ t <= h ==>
                       (difg(m) diffl difg(SUC m)(t))(t))") ASSUME_TAC THENL
       [REPEAT GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "difg" THEN BETA_TAC THEN
        CONV_TAC ((funpow 2 RATOR_CONV o RAND_CONV) HABS_CONV) THEN
        MATCH_MP_TAC DIFF_SUB THEN CONJ_TAC THENL
         [CONV_TAC (ONCE_DEPTH_CONV ETA_CONV) THEN
          FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
        CONV_TAC ((funpow 2 RATOR_CONV o RAND_CONV) HABS_CONV) THEN
        MATCH_MP_TAC DIFF_ADD THEN CONJ_TAC THENL
         [ALL_TAC,
          mpDiffConv THEN
          REWRITE_TAC [REAL_MUL_LZERO, REAL_MUL_RID, REAL_ADD_LID] THEN
          REWRITE_TAC [REAL_FACT_NZ, REAL_SUB_RZERO] THEN
          DISCH_THEN (MP_TAC o SPEC tt) THEN
          MATCH_MP_TAC EQ_IMP THEN
          AP_THM_TAC THEN CONV_TAC (ONCE_DEPTH_CONV (ALPHA_CONV tt)) THEN
          AP_TERM_TAC THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
          AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [real_div] THEN
          REWRITE_TAC [← GSYM REAL_MUL_ASSOC, POW_2] THEN
          ONCE_REWRITE_TAC [ac3] THEN
          FIRST_ASSUM (X_CHOOSE_THEN (← q "d:num") SUBST1_TAC o
            MATCH_MP LESS_ADD_1 o CONJUNCT1) THEN
          ONCE_REWRITE_TAC [ADD_SYM] THEN REWRITE_TAC [ADD_SUB] THEN
          REWRITE_TAC [← GSYM ADD_ASSOC] THEN
          REWRITE_TAC [← ONCE_REWRITE_RULE [ADD_SYM] (← GSYM ADD1)] THEN
          REWRITE_TAC [ADD_SUB] THEN AP_TERM_TAC THEN
          IMP_SUBST_TAC REAL_INV_MUL_WEAK THEN REWRITE_TAC [REAL_FACT_NZ] THEN
          REWRITE_TAC [← GSYM ADD1, FACT, ← GSYM REAL_MUL] THEN
          REPEAT (IMP_SUBST_TAC REAL_INV_MUL_WEAK THEN
                 REWRITE_TAC [REAL_FACT_NZ, REAL_INJ, NOT_SUC]) THEN
          REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN
          ONCE_REWRITE_TAC [ac4] THEN
          REPEAT (IMP_SUBST_TAC REAL_MUL_LINV THEN REWRITE_TAC [REAL_FACT_NZ] THEN
                 REWRITE_TAC [REAL_INJ, NOT_SUC]) THEN
          REWRITE_TAC [REAL_MUL_LID]] THEN
        FIRST_ASSUM (X_CHOOSE_THEN (← q "d:num") SUBST1_TAC o
            MATCH_MP LESS_ADD_1 o CONJUNCT1) THEN
        ONCE_REWRITE_TAC [ADD_SYM] THEN REWRITE_TAC [ADD_SUB] THEN
        REWRITE_TAC [← GSYM ADD_ASSOC] THEN
        REWRITE_TAC [← ONCE_REWRITE_RULE [ADD_SYM] (← GSYM ADD1)] THEN
        REWRITE_TAC [ADD_SUB] THEN
        REWRITE_TAC [← GSYM (← REWRITE_RULE [REAL_EQ_SUB_LADD] SUM_OFFSET)] THEN
        BETA_TAC THEN REWRITE_TAC [SUM_1] THEN BETA_TAC THEN
        CONV_TAC (funpow 2 RATOR_CONV (RAND_CONV HABS_CONV)) THEN
        GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [← GSYM REAL_ADD_RID] THEN
        MATCH_MP_TAC DIFF_ADD THEN REWRITE_TAC [pow, DIFF_CONST] THEN
        MP_TAC (← SPECL
         [← q r"\p x. (diff((p + 1) + m)(&0) / &(FACT(p + 1)))
                    * (x pow (p + 1))",
          ← q r"\p x. (diff(p + (SUC m))(&0) / &(FACT p)) * (x pow p)",
          ← q "0", ← q "d:num", tt] DIFF_SUM) THEN BETA_TAC THEN
        DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC [ADD_CLAUSES] THEN
        X_GEN_TAC (← q "k:num") THEN STRIP_TAC THEN
        mpDiffConv THEN
        DISCH_THEN (MP_TAC o SPEC tt) THEN
        MATCH_MP_TAC EQ_IMP THEN
        CONV_TAC (ONCE_DEPTH_CONV (ALPHA_CONV (← q "z:real"))) THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC [REAL_MUL_LZERO, REAL_ADD_LID, REAL_MUL_RID] THEN
        REWRITE_TAC [← GSYM ADD1, ADD_CLAUSES, real_div, ← GSYM REAL_MUL_ASSOC] THEN
        REWRITE_TAC [SUC_SUB1] THEN
        ONCE_REWRITE_TAC [ac5] THEN
        AP_TERM_TAC THEN REWRITE_TAC [REAL_MUL_ASSOC] THEN AP_THM_TAC THEN
        AP_TERM_TAC THEN
        SUBGOAL_THEN (← q r"&(SUC k) = inv(inv(&(SUC k)))") SUBST1_TAC THENL
         [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INVINV THEN
          REWRITE_TAC [REAL_INJ, NOT_SUC], ALL_TAC] THEN
        IMP_SUBST_TAC (← GSYM REAL_INV_MUL_WEAK) THENL
         [CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN REWRITE_TAC [REAL_FACT_NZ] THEN
          MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC REAL_INV_POS THEN
          REWRITE_TAC [REAL_LT, LT_0], ALL_TAC] THEN
        AP_TERM_TAC THEN REWRITE_TAC [FACT, ← GSYM REAL_MUL, REAL_MUL_ASSOC] THEN
        IMP_SUBST_TAC REAL_MUL_LINV THEN REWRITE_TAC [REAL_MUL_LID] THEN
        REWRITE_TAC [REAL_INJ, NOT_SUC], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"!m. m < n ==>
            ?t. &0 < t /\ t < h /\ (difg(SUC m)(t) = &0)") MP_TAC THENL
       [ALL_TAC,
        DISCH_THEN (MP_TAC o SPEC (← q "r:num")) THEN EXPAND_TAC "n" THEN
        REWRITE_TAC [LESS_SUC_REFL] THEN
        DISCH_THEN (X_CHOOSE_THEN tt STRIP_ASSUME_TAC) THEN
        EXISTS_TAC tt THEN ASM_REWRITE_TAC [] THEN
        UNDISCH_TAC (← q r"difg(SUC r)(t:real) = &0") THEN EXPAND_TAC "difg" THEN
        ASM_REWRITE_TAC [SUB_REFL, sum, pow, FACT] THEN
        REWRITE_TAC [REAL_SUB_0, REAL_ADD_LID, real_div] THEN
        REWRITE_TAC [REAL_INV1, REAL_MUL_RID] THEN DISCH_THEN SUBST1_TAC THEN
        GEN_REWRITE_TAC (funpow 2 RAND_CONV) [ac6] THEN
        ASM_REWRITE_TAC [← GSYM real_div]] THEN
      SUBGOAL_THEN (← q r"!m:num. m < n ==> (difg(m)(&0) = &0)") ASSUME_TAC THENL
       [X_GEN_TAC (← q "m:num") THEN EXPAND_TAC "difg" THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "d:num") SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
        ONCE_REWRITE_TAC [ADD_SYM] THEN REWRITE_TAC [ADD_SUB] THEN
        MP_TAC (← GEN tj
         (← SPECL [tj, ← q "d:num", ← q "1"] SUM_OFFSET)) THEN
        REWRITE_TAC [ADD1, REAL_EQ_SUB_LADD] THEN
        DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← GSYM th])) THEN BETA_TAC THEN
        REWRITE_TAC [SUM_1] THEN BETA_TAC THEN
        REWRITE_TAC [FACT, pow, REAL_INV1, ADD_CLAUSES, real_div, REAL_MUL_RID] THEN
        REWRITE_TAC [← GSYM ADD1, POW_0, REAL_MUL_RZERO, SUM_0, REAL_ADD_LID] THEN
        REWRITE_TAC [REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_ADD_RID] THEN
        REWRITE_TAC [REAL_SUB_REFL], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"!m:num. m < n ==> ?t. &0 < t /\ t < h /\
                            (difg(m) diffl &0)(t)") MP_TAC THENL
       [ALL_TAC,
        DISCH_THEN (fun th => GEN_TAC THEN
          DISCH_THEN (fun t => tactic_of do
            pure (ASSUME_TAC t THEN MP_TAC (← MATCH_MP th t)))) THEN
        DISCH_THEN (X_CHOOSE_THEN tt STRIP_ASSUME_TAC) THEN
        EXISTS_TAC tt THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC DIFF_UNIQ THEN EXISTS_TAC (← q r"difg(m:num):real->real") THEN
        EXISTS_TAC tt THEN ASM_REWRITE_TAC [] THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
        CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
        FIRST_ASSUM ACCEPT_TAC] THEN
      INDUCT_TAC THENL
       [DISCH_TAC THEN MATCH_MP_TAC ROLLE THEN ASM_REWRITE_TAC [] THEN
        SUBGOAL_THEN (← q r"!t. &0 <= t /\ t <= h ==> g differentiable t") MP_TAC THENL
         [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [differentiable] THEN
          EXISTS_TAC (← q r"difg(SUC 0)(t:real):real") THEN
          SUBST1_TAC (← SYM aDifg0) THEN
          FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
        DISCH_TAC THEN CONJ_TAC THENL
         [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC DIFF_CONT THEN
          REWRITE_TAC [← GSYM differentiable] THEN FIRST_ASSUM MATCH_MP_TAC THEN
          ASM_REWRITE_TAC [],
          GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
          CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC []],
        DISCH_TAC THEN
        SUBGOAL_THEN (← q "m < n:num")
        (fun th => FIRST_ASSUM (MP_TAC o (fun a => MATCH_MP a th))) THENL
         [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC (← q "SUC m") THEN
          ASM_REWRITE_TAC [LESS_SUC_REFL], ALL_TAC] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "t0:real") STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN (← q r"?t. (& 0) < t /\ t < t0 /\ ((difg(SUC m)) diffl (& 0))t")
        MP_TAC THENL
         [MATCH_MP_TAC ROLLE THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
           [SUBGOAL_THEN (← q r"difg(SUC m)(&0) = &0") SUBST1_TAC THENL
             [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC,
              MATCH_MP_TAC DIFF_UNIQ THEN EXISTS_TAC (← q r"difg(m:num):real->real") THEN
              EXISTS_TAC (← q "t0:real") THEN ASM_REWRITE_TAC [] THEN
              FIRST_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
               [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC (← q "SUC m") THEN
                ASM_REWRITE_TAC [LESS_SUC_REFL],
                MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC [],
                MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC []]], ALL_TAC] THEN
          SUBGOAL_THEN (← q r"!t. &0 <= t /\ t <= t0 ==>
                           difg(SUC m) differentiable t") ASSUME_TAC THENL
           [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [differentiable] THEN
            EXISTS_TAC (← q r"difg(SUC(SUC m))(t:real):real") THEN
            FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
            MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "t0:real") THEN
            ASM_REWRITE_TAC [] THEN
            MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
          CONJ_TAC THENL
           [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC DIFF_CONT THEN
            REWRITE_TAC [← GSYM differentiable] THEN FIRST_ASSUM MATCH_MP_TAC THEN
            ASM_REWRITE_TAC [],
            GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
            CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC []],
          DISCH_THEN (X_CHOOSE_THEN tt STRIP_ASSUME_TAC) THEN
          EXISTS_TAC tt THEN ASM_REWRITE_TAC [] THEN
          MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (← q "t0:real") THEN
          ASM_REWRITE_TAC []]]))

  let MCLAURIN_NEG ← prove
   r"!f diff h n.
    h < &0 /\
    0 < n /\
    (diff(0) = f) /\
    (!m t. m < n /\ h <= t /\ t <= &0 ==>
           (diff(m) diffl diff(SUC m)(t))(t)) ==>
   (?t. h < t /\ t < &0 /\
        (f(h) = sum(0,n)(\m. (diff(m)(&0) / &(FACT m)) * (h pow m)) +
                ((diff(n)(t) / &(FACT n)) * (h pow n))))"
   (← do
    -- In OCaml's order: the later parts of the THEN chain first.
    let acm2 ← AC REAL_MUL_AC (← q r"a * b * c * d = (b * c) * (a * d)")
    let dct ← SPEC (← q "t:real") (← ExceptT.mk (DIFF_CONV (← q r"\x. --x")))
    let acc ← AC CONJ_ACI (← q r"a /\ b /\ c <=> a /\ c /\ b")
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
      MP_TAC (← SPECL [← q r"\x. (f(--x):real)",
                    ← q r"\n x. ((--(&1)) pow n) * (diff:num->real->real)(n)(--x)",
                    ← q "--h", ← q "n:num"] MCLAURIN) THEN
      BETA_TAC THEN ASM_REWRITE_TAC [REAL_NEG_GT0, pow, REAL_MUL_LID] THEN
      ONCE_REWRITE_TAC [← GSYM REAL_LE_NEG2] THEN
      REWRITE_TAC [REAL_NEG_NEG, REAL_NEG_0] THEN
      ONCE_REWRITE_TAC [acc] THEN
      subgoalAnte2 (fun t => REWRITE_TAC [t]) THENL
       [REPEAT GEN_TAC THEN
        DISCH_THEN (fun th => FIRST_ASSUM (MP_TAC o (fun a => MATCH_MP a th))) THEN
        DISCH_THEN (MP_TAC o (fun th => CONJ th dct)) THEN
        CONV_TAC (ONCE_DEPTH_CONV ETA_CONV) THEN
        DISCH_THEN (MP_TAC o MATCH_MP DIFF_CHAIN) THEN
        DISCH_THEN (MP_TAC o GEN_ALL o MATCH_MP DIFF_CMUL) THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"(--(&1)) pow m")) THEN BETA_TAC THEN
        MATCH_MP_TAC EQ_IMP THEN
        CONV_TAC (ONCE_DEPTH_CONV (ALPHA_CONV (← q "z:real"))) THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN
        CONV_TAC (fun t => (AC REAL_MUL_AC t).run),
        DISCH_THEN (X_CHOOSE_THEN (← q "t:real") STRIP_ASSUME_TAC)] THEN
      EXISTS_TAC (← q "--t") THEN ONCE_REWRITE_TAC [← GSYM REAL_LT_NEG2] THEN
      ASM_REWRITE_TAC [REAL_NEG_NEG, REAL_NEG_0] THEN
      BINOP_TAC THENL
       [MATCH_MP_TAC SUM_EQ THEN
        X_GEN_TAC (← q "m:num") THEN REWRITE_TAC [ADD_CLAUSES] THEN
        DISCH_THEN (ASSUME_TAC o CONJUNCT2) THEN BETA_TAC, ALL_TAC] THEN
      REWRITE_TAC [real_div, ← GSYM REAL_MUL_ASSOC] THEN
      ONCE_REWRITE_TAC [acm2] THEN
      REWRITE_TAC [← GSYM POW_MUL, ← GSYM REAL_NEG_MINUS1, REAL_NEG_NEG] THEN
      REWRITE_TAC [REAL_MUL_ASSOC]))

  -- More convenient "bidirectional" version.

  let MCLAURIN_BI_LE ← prove
   r"!f diff x n.
        (diff 0 = f) /\
        (!m t. m < n /\ abs(t) <= abs(x) ==> (diff m diffl diff (SUC m) t) t)
        ==> ?t. abs(t) <= abs(x) /\
                (f x = sum (0,n) (\m. diff m (&0) / &(FACT m) * x pow m) +
                       diff n t / &(FACT n) * x pow n)"
   (← do
    let r5 ← REAL_ARITH (← q r"x < t /\ t < &0 ==> abs(t) <= abs(x)")
    let r4 ← REAL_ARITH (← q r"x <= t /\ t <= &0 ==> abs(t) <= abs(x)")
    let r3 ← REAL_ARITH (← q r"&0 < t /\ t < x ==> abs(t) <= abs(x)")
    let r2 ← REAL_ARITH (← q r"&0 <= t /\ t <= x ==> abs(t) <= abs(x)")
    let r1 ← REAL_ARITH (← q r"~(x = &0) ==> &0 < x \/ x < &0")
    pure (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q "n = 0") THENL
       [ASM_REWRITE_TAC [sum, real_pow, FACT, REAL_DIV_1, REAL_MUL_RID,
                        REAL_ADD_LID] THEN
        EXISTS_TAC (← q "x:real") THEN REWRITE_TAC [REAL_LE_REFL], ALL_TAC] THEN
      ASM_CASES_TAC (← q r"x = &0") THENL
       [EXISTS_TAC (← q r"&0") THEN ASM_REWRITE_TAC [REAL_LE_REFL] THEN
        UNDISCH_TAC (← q "~(n = 0)") THEN SPEC_TAC (← q "n:num", ← q "n:num") THEN
        INDUCT_TAC THEN ASM_REWRITE_TAC [NOT_SUC] THEN
        REWRITE_TAC [ADD1] THEN
        REWRITE_TAC [← REWRITE_RULE [REAL_EQ_SUB_RADD] (← GSYM SUM_OFFSET)] THEN
        REWRITE_TAC [REAL_POW_ADD, REAL_POW_1, REAL_MUL_RZERO, SUM_0] THEN
        REWRITE_TAC [REAL_ADD_RID, REAL_ADD_LID] THEN
        CONV_TAC (ONCE_DEPTH_CONV REAL_SUM_CONV) THEN
        ASM_REWRITE_TAC [real_pow, FACT, REAL_MUL_RID, REAL_DIV_1], ALL_TAC] THEN
      FIRST_ASSUM (DISJ_CASES_TAC o MATCH_MP r1)
      THENL
       [MP_TAC (← SPECL [← q r"f:real->real", ← q r"diff:num->real->real", ← q "x:real", ← q "n:num"]
                     MCLAURIN) THEN
        ASM_SIMP_TAC [r2] THEN
        ASM_REWRITE_TAC [LT_NZ] THEN MATCH_MP_TAC MONO_EXISTS THEN
        SIMP_TAC [r3],
        MP_TAC (← SPECL [← q r"f:real->real", ← q r"diff:num->real->real", ← q "x:real", ← q "n:num"]
                     MCLAURIN_NEG) THEN
        ASM_SIMP_TAC [r4] THEN
        ASM_REWRITE_TAC [LT_NZ] THEN MATCH_MP_TAC MONO_EXISTS THEN
        SIMP_TAC [r5]]))

  -- @@RETURN BEGIN
  return { MCLAURIN, MCLAURIN_NEG, MCLAURIN_BI_LE }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Simple strong form if a function is differentiable everywhere; versions   -/
/- for exp and ln(1 + x), ln(1 - x).  (transc.ml 5762-6056)                 -/
/- ------------------------------------------------------------------------- -/

structure McLnExp where
  -- @@FIELDS
  MCLAURIN_ALL_LT : thm
  MCLAURIN_ZERO : thm
  MCLAURIN_ALL_LE : thm
  MCLAURIN_EXP_LEMMA : thm
  MCLAURIN_EXP_LT : thm
  MCLAURIN_EXP_LE : thm
  MCLAURIN_LN_POS : thm
  MCLAURIN_LN_NEG : thm
  deriving Inhabited

@[nospecialize]
def setupMcLnExp [HolBase] (D : TranscDeps) (BDefs : Defs) (BDiffConv : DiffConv) (BExp : Exp) (BLnRoot : LnRoot) (BMclaurin : Mclaurin) (ANames : HolLibrary.Analysis.Names) (AReals1 : HolLibrary.Analysis.Reals1) (AReals2 : HolLibrary.Analysis.Reals2) (AReals3 : HolLibrary.Analysis.Reals3) (APow : HolLibrary.Analysis.Pow) (ASums : HolLibrary.Analysis.Sums) (ADiffs : HolLibrary.Analysis.Diffs) :
    ExceptT String IO McLnExp := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, INDUCT_TAC, REAL_ARITH_TAC, .. } := D
  let { ADD_CLAUSES, DE_MORGAN_THM, EQ_IMP, FACT, FACT_LT, LE, LET_CASES, LT, LT_REFL,
        NOT_LE, NOT_SUC, PRE, REAL_ADD_LID, REAL_ADD_RID, .. } := D.core1
  let { REAL_DIV_1, REAL_INV_0, REAL_INV_1, REAL_INV_MUL, REAL_LT_TOTAL, REAL_MUL_AC,
        REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_LNEG, REAL_MUL_RNEG,
        REAL_MUL_SYM, REAL_OF_NUM_EQ, REAL_OF_NUM_MUL, REAL_POW_2, REAL_POW_EQ_0,
        REAL_POW_ONE, real_div, real_pow, .. } := D.core2
  let { DIFF_EXP, add_to_diff_net, .. } := BDefs
  let { DIFF_CONV, .. } := BDiffConv
  let { REAL_EXP_0, .. } := BExp
  let { DIFF_LN, LN_1, .. } := BLnRoot
  let { MCLAURIN, MCLAURIN_NEG, .. } := BMclaurin
  let { SUC_SUB1, .. } := ANames
  let { REAL_LE_REFL, REAL_LT_IMP_LE, REAL_MUL_LZERO, REAL_MUL_RID, REAL_MUL_RZERO,
        REAL_NEG_NEG, .. } := AReals1
  let { REAL_NEG_0, .. } := AReals2
  let { REAL_SUB_LZERO, REAL_SUB_RZERO, .. } := AReals3
  let { pow, .. } := APow
  let { sum, .. } := ASums
  let { DIFF_CHAIN, .. } := ADiffs
  -- @@SCOPE END
  let _tu ← q "u:real"
  -- `W(MP_TAC o SPEC `u:real` o DIFF_CONV o lhand o rator o snd)`
  let mpSpecDiffU : tactic := fun gl => ExceptT.run do
    let t ← liftExcept (do lhand (← rator gl.2))
    ExceptT.mk (MP_TAC (← SPEC _tu (← ExceptT.mk (DIFF_CONV t))) gl)

  let MCLAURIN_ALL_LT ← prove
   r"!f diff.
      (diff 0 = f) /\
      (!m x. ((diff m) diffl (diff(SUC m) x)) x)
      ==> !x n. ~(x = &0) /\ 0 < n
            ==> ?t. &0 < abs(t) /\ abs(t) < abs(x) /\
                    (f(x) = sum(0,n)(\m. (diff m (&0) / &(FACT m)) * x pow m) +
                            (diff n t / &(FACT n)) * x pow n)"
   (REPEAT STRIP_TAC THEN
    REPEAT_TCL DISJ_CASES_THEN MP_TAC
     (← SPECL [← q "x:real", ← q r"&0"] REAL_LT_TOTAL) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THENL
     [MP_TAC (← SPECL [← q r"f:real->real", ← q r"diff:num->real->real",
                    ← q "x:real", ← q "n:num"] MCLAURIN_NEG) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "t:real") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q "t:real") THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC (← q r"t < &0") THEN UNDISCH_TAC (← q "x < t") THEN REAL_ARITH_TAC,
      MP_TAC (← SPECL [← q r"f:real->real", ← q r"diff:num->real->real",
                    ← q "x:real", ← q "n:num"] MCLAURIN) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "t:real") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q "t:real") THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC (← q r"&0 < t") THEN UNDISCH_TAC (← q "t < x") THEN REAL_ARITH_TAC])

  let MCLAURIN_ZERO ← prove
   r"!diff n x. (x = &0) /\ 0 < n ==>
       (sum(0,n)(\m. (diff m (&0) / &(FACT m)) * x pow m) = diff 0 (&0))"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
    SPEC_TAC (← q "n:num", ← q "n:num") THEN INDUCT_TAC THEN REWRITE_TAC [LT_REFL] THEN
    REWRITE_TAC [LT] THEN
    DISCH_THEN (DISJ_CASES_THEN2 (SUBST1_TAC o SYM) MP_TAC) THENL
     [REWRITE_TAC [sum, ADD_CLAUSES, FACT, real_pow, real_div, REAL_INV_1] THEN
      REWRITE_TAC [REAL_ADD_LID, REAL_MUL_RID],
      REWRITE_TAC [sum] THEN
      DISCH_THEN (fun th => ASSUME_TAC th THEN ANTE_RES_THEN SUBST1_TAC th) THEN
      UNDISCH_TAC (← q "0 < n") THEN SPEC_TAC (← q "n:num", ← q "n:num") THEN
      INDUCT_TAC THEN REWRITE_TAC [LT_REFL] THEN
      REWRITE_TAC [ADD_CLAUSES, real_pow, REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
      REWRITE_TAC [REAL_ADD_RID]])

  let MCLAURIN_ALL_LE ← prove
   r"!f diff.
      (diff 0 = f) /\
      (!m x. ((diff m) diffl (diff(SUC m) x)) x)
      ==> !x n. ?t. abs(t) <= abs(x) /\
                    (f(x) = sum(0,n)(\m. (diff m (&0) / &(FACT m)) * x pow m) +
                            (diff n t / &(FACT n)) * x pow n)"
   (REPEAT STRIP_TAC THEN
    DISJ_CASES_THEN MP_TAC (← SPECL [← q "n:num", ← q "0"] LET_CASES) THENL
     [REWRITE_TAC [LE] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC [sum, REAL_ADD_LID, FACT] THEN EXISTS_TAC (← q "x:real") THEN
      REWRITE_TAC [REAL_LE_REFL, real_pow, REAL_MUL_RID, REAL_DIV_1],
      DISCH_TAC THEN ASM_CASES_TAC (← q r"x = &0") THENL
       [MP_TAC (← SPEC_ALL MCLAURIN_ZERO) THEN ASM_REWRITE_TAC [] THEN
        DISCH_THEN SUBST1_TAC THEN EXISTS_TAC (← q r"&0") THEN
        REWRITE_TAC [REAL_LE_REFL] THEN
        SUBGOAL_THEN (← q r"&0 pow n = &0") SUBST1_TAC THENL
         [ASM_REWRITE_TAC [REAL_POW_EQ_0, ← GSYM (← CONJUNCT1 LE), NOT_LE],
          REWRITE_TAC [REAL_ADD_RID, REAL_MUL_RZERO]],
        MP_TAC (← SPEC_ALL MCLAURIN_ALL_LT) THEN ASM_REWRITE_TAC [] THEN
        DISCH_THEN (MP_TAC o SPEC_ALL) THEN ASM_REWRITE_TAC [] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "t:real") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q "t:real") THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC []]])

  -- Version for exp.

  let MCLAURIN_EXP_LEMMA ← prove
   r"((\n:num. exp) 0 = exp) /\
   (!m x. (((\n:num. exp) m) diffl ((\n:num. exp) (SUC m) x)) x)"
   (REWRITE_TAC [DIFF_EXP])

  let MCLAURIN_EXP_LT ← prove
   r"!x n. ~(x = &0) /\ 0 < n
         ==> ?t. &0 < abs(t) /\
                 abs(t) < abs(x) /\
                 (exp(x) = sum(0,n)(\m. x pow m / &(FACT m)) +
                           (exp(t) / &(FACT n)) * x pow n)"
   (MP_TAC (← MATCH_MP MCLAURIN_ALL_LT MCLAURIN_EXP_LEMMA) THEN
    REWRITE_TAC [REAL_EXP_0, real_div, REAL_MUL_AC, REAL_MUL_LID, REAL_MUL_RID])

  let MCLAURIN_EXP_LE ← prove
   r"!x n. ?t. abs(t) <= abs(x) /\
             (exp(x) = sum(0,n)(\m. x pow m / &(FACT m)) +
                       (exp(t) / &(FACT n)) * x pow n)"
   (MP_TAC (← MATCH_MP MCLAURIN_ALL_LE MCLAURIN_EXP_LEMMA) THEN
    REWRITE_TAC [REAL_EXP_0, real_div, REAL_MUL_AC, REAL_MUL_LID, REAL_MUL_RID])

  -- Version for ln(1 +/- x).

  -- `let DIFF_LN_COMPOSITE = prove (...) in add_to_diff_net ...`: a local
  -- binding, not exported.
  let _DIFF_LN_COMPOSITE ← prove
   r"!g m x. (g diffl m)(x) /\ &0 < g x
           ==> ((\x. ln(g x)) diffl (inv(g x) * m))(x)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC DIFF_CHAIN THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC DIFF_LN THEN
    ASM_REWRITE_TAC [])
  add_to_diff_net (← SPEC_ALL _DIFF_LN_COMPOSITE)

  let MCLAURIN_LN_POS ← prove
   r"!x n.
     &0 < x /\ 0 < n
     ==> ?t. &0 < t /\
             t < x /\
             (ln(&1 + x) = sum(0,n)
                           (\m. --(&1) pow (SUC m) * (x pow m) / &m) +
               --(&1) pow (SUC n) * x pow n / (&n * (&1 + t) pow n))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPEC (← q r"\x. ln(&1 + x)") MCLAURIN) THEN
    DISCH_THEN (MP_TAC o SPEC
      (← q r"\n x. if n = 0 then ln(&1 + x)
             else --(&1) pow (SUC n) *
                  &(FACT(PRE n)) * inv((&1 + x) pow n)")) THEN
    DISCH_THEN (MP_TAC o SPECL [← q "x:real", ← q "n:num"]) THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [NOT_SUC, REAL_ADD_RID, REAL_POW_ONE] THEN
    REWRITE_TAC [LN_1, REAL_INV_1, REAL_MUL_RID] THEN
    SUBGOAL_THEN (← q "~(n = 0)") ASSUME_TAC THENL
     [UNDISCH_TAC (← q "0 < n") THEN ARITH_TAC, ASM_REWRITE_TAC []] THEN
    SUBGOAL_THEN (← q r"!p. ~(p = 0) ==> (&(FACT(PRE p)) / &(FACT p) = inv(&p))")
    ASSUME_TAC THENL
     [INDUCT_TAC THEN REWRITE_TAC [NOT_SUC, PRE] THEN
      REWRITE_TAC [real_div, FACT, ← GSYM REAL_OF_NUM_MUL] THEN
      REWRITE_TAC [REAL_INV_MUL] THEN
      ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
      GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_RID] THEN
      REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC REAL_MUL_LINV THEN
      REWRITE_TAC [REAL_OF_NUM_EQ] THEN
      MP_TAC (← SPEC (← q "p:num") FACT_LT) THEN ARITH_TAC, ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!p. (if p = 0 then &0 else --(&1) pow (SUC p) * &(FACT (PRE p))) /
          &(FACT p) = --(&1) pow (SUC p) * inv(&p)")
    (fun th => REWRITE_TAC [th]) THENL
     [INDUCT_TAC THENL
       [REWRITE_TAC [REAL_INV_0, real_div, REAL_MUL_LZERO, REAL_MUL_RZERO],
        REWRITE_TAC [NOT_SUC] THEN
        REWRITE_TAC [real_div, ← GSYM REAL_MUL_ASSOC] THEN
        AP_TERM_TAC THEN REWRITE_TAC [← GSYM real_div] THEN
        FIRST_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC [NOT_SUC]], ALL_TAC] THEN
    SUBGOAL_THEN
      (← q r"!t. (--(&1) pow (SUC n) * &(FACT(PRE n)) * inv ((&1 + t) pow n)) /
           &(FACT n) * x pow n = --(&1) pow (SUC n) *
                                 x pow n / (&n * (&1 + t) pow n)")
    (fun th => REWRITE_TAC [th]) THENL
     [GEN_TAC THEN REWRITE_TAC [real_div, ← GSYM REAL_MUL_ASSOC] THEN
      AP_TERM_TAC THEN REWRITE_TAC [REAL_MUL_ASSOC] THEN
      GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN AP_TERM_TAC THEN
      REWRITE_TAC [REAL_INV_MUL] THEN
      GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
      REWRITE_TAC [REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REWRITE_TAC [← GSYM real_div] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    REWRITE_TAC [real_div, REAL_MUL_AC] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC (← q "m:num") THEN X_GEN_TAC _tu THEN STRIP_TAC THEN
    ASM_CASES_TAC (← q "m = 0") THEN ASM_REWRITE_TAC [] THENL
     [mpSpecDiffU THEN
      REWRITE_TAC [PRE, real_pow, REAL_ADD_LID, REAL_MUL_RID] THEN
      REWRITE_TAC [REAL_MUL_RNEG, REAL_MUL_LNEG, REAL_MUL_RID] THEN
      REWRITE_TAC [FACT, REAL_MUL_RID, REAL_NEG_NEG] THEN
      DISCH_THEN MATCH_MP_TAC THEN UNDISCH_TAC (← q r"&0 <= u") THEN REAL_ARITH_TAC,
      mpSpecDiffU THEN
      SUBGOAL_THEN (← q r"~((&1 + u) pow m = &0)") (fun th => REWRITE_TAC [th]) THENL
       [REWRITE_TAC [REAL_POW_EQ_0] THEN ASM_REWRITE_TAC [] THEN
        UNDISCH_TAC (← q r"&0 <= u") THEN REAL_ARITH_TAC,
        MATCH_MP_TAC EQ_IMP THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC [REAL_MUL_LZERO, REAL_ADD_RID] THEN
        REWRITE_TAC [REAL_ADD_LID, REAL_MUL_RID] THEN
        REWRITE_TAC [real_div, real_pow, REAL_MUL_LNEG, REAL_MUL_RNEG] THEN
        REWRITE_TAC [REAL_NEG_NEG, REAL_MUL_RID, REAL_MUL_LID] THEN
        REWRITE_TAC [REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        UNDISCH_TAC (← q "~(m = 0)") THEN SPEC_TAC (← q "m:num", ← q "p:num") THEN
        INDUCT_TAC THEN REWRITE_TAC [NOT_SUC] THEN
        REWRITE_TAC [SUC_SUB1, PRE] THEN REWRITE_TAC [FACT] THEN
        REWRITE_TAC [← GSYM REAL_OF_NUM_MUL] THEN
        REWRITE_TAC [REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
        REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
        REWRITE_TAC [real_pow, REAL_POW_2] THEN REWRITE_TAC [REAL_INV_MUL] THEN
        REWRITE_TAC [REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC [REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
        GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_LID] THEN
        REWRITE_TAC [REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        MATCH_MP_TAC REAL_MUL_LINV THEN
        REWRITE_TAC [REAL_POW_EQ_0] THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [DE_MORGAN_THM] THEN DISJ1_TAC THEN
        UNDISCH_TAC (← q r"&0 <= u") THEN REAL_ARITH_TAC]])

  let MCLAURIN_LN_NEG ← prove
   r"!x n. &0 < x /\ x < &1 /\ 0 < n
         ==> ?t. &0 < t /\
                 t < x /\
                 (--(ln(&1 - x)) = sum(0,n) (\m. (x pow m) / &m) +
                                    x pow n / (&n * (&1 - t) pow n))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPEC (← q r"\x. --(ln(&1 - x))") MCLAURIN) THEN
    DISCH_THEN (MP_TAC o SPEC
      (← q r"\n x. if n = 0 then --(ln(&1 - x))
             else &(FACT(PRE n)) * inv((&1 - x) pow n)")) THEN
    DISCH_THEN (MP_TAC o SPECL [← q "x:real", ← q "n:num"]) THEN
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [REAL_SUB_RZERO] THEN
    REWRITE_TAC [NOT_SUC, LN_1, REAL_POW_ONE] THEN
    SUBGOAL_THEN (← q "~(n = 0)") ASSUME_TAC THENL
     [UNDISCH_TAC (← q "0 < n") THEN ARITH_TAC, ASM_REWRITE_TAC []] THEN
    REWRITE_TAC [REAL_INV_1, REAL_MUL_RID, REAL_MUL_LID] THEN
    SUBGOAL_THEN (← q r"!p. ~(p = 0) ==> (&(FACT(PRE p)) / &(FACT p) = inv(&p))")
    ASSUME_TAC THENL
     [INDUCT_TAC THEN REWRITE_TAC [NOT_SUC, PRE] THEN
      REWRITE_TAC [real_div, FACT, ← GSYM REAL_OF_NUM_MUL] THEN
      REWRITE_TAC [REAL_INV_MUL] THEN
      ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
      GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_RID] THEN
      REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC REAL_MUL_LINV THEN
      REWRITE_TAC [REAL_OF_NUM_EQ] THEN
      MP_TAC (← SPEC (← q "p:num") FACT_LT) THEN ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [REAL_NEG_0] THEN
    SUBGOAL_THEN (← q r"!p. (if p = 0 then &0 else &(FACT (PRE p))) / &(FACT p) =
                      inv(&p)")
    (fun th => REWRITE_TAC [th]) THENL
     [INDUCT_TAC THENL
       [REWRITE_TAC [REAL_INV_0, real_div, REAL_MUL_LZERO],
        REWRITE_TAC [NOT_SUC] THEN FIRST_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC [NOT_SUC]], ALL_TAC] THEN
    SUBGOAL_THEN
      (← q r"!t. (&(FACT(PRE n)) * inv ((&1 - t) pow n)) / &(FACT n) * x pow n
           = x pow n / (&n * (&1 - t) pow n)")
    (fun th => REWRITE_TAC [th]) THENL
     [GEN_TAC THEN REWRITE_TAC [real_div, REAL_MUL_ASSOC] THEN
      GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN AP_TERM_TAC THEN
      REWRITE_TAC [REAL_INV_MUL] THEN
      GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
      REWRITE_TAC [REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REWRITE_TAC [← GSYM real_div] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    REWRITE_TAC [real_div, REAL_MUL_AC] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC (← q "m:num") THEN X_GEN_TAC _tu THEN STRIP_TAC THEN
    ASM_CASES_TAC (← q "m = 0") THEN ASM_REWRITE_TAC [] THENL
     [mpSpecDiffU THEN
      REWRITE_TAC [PRE, pow, FACT, REAL_SUB_LZERO] THEN
      REWRITE_TAC [REAL_MUL_RNEG, REAL_NEG_NEG, REAL_MUL_RID] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      UNDISCH_TAC (← q r"x < &1") THEN UNDISCH_TAC (← q "u:real <= x") THEN
      REAL_ARITH_TAC,
      mpSpecDiffU THEN
      SUBGOAL_THEN (← q r"~((&1 - u) pow m = &0)") (fun th => REWRITE_TAC [th]) THENL
       [REWRITE_TAC [REAL_POW_EQ_0] THEN ASM_REWRITE_TAC [] THEN
        UNDISCH_TAC (← q r"x < &1") THEN UNDISCH_TAC (← q "u:real <= x") THEN
        REAL_ARITH_TAC,
        MATCH_MP_TAC EQ_IMP THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC [REAL_SUB_LZERO, real_div, PRE] THEN
        REWRITE_TAC [REAL_MUL_LZERO, REAL_ADD_RID] THEN
        REWRITE_TAC
         [REAL_MUL_RNEG, REAL_MUL_LNEG, REAL_NEG_NEG, REAL_MUL_RID] THEN
        UNDISCH_TAC (← q "~(m = 0)") THEN SPEC_TAC (← q "m:num", ← q "p:num") THEN
        INDUCT_TAC THEN REWRITE_TAC [NOT_SUC] THEN
        REWRITE_TAC [SUC_SUB1, PRE] THEN REWRITE_TAC [FACT] THEN
        REWRITE_TAC [← GSYM REAL_OF_NUM_MUL] THEN
        REWRITE_TAC [REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
        REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
        REWRITE_TAC [real_pow, REAL_POW_2] THEN REWRITE_TAC [REAL_INV_MUL] THEN
        REWRITE_TAC [REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC [REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
        GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_LID] THEN
        REWRITE_TAC [REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        MATCH_MP_TAC REAL_MUL_LINV THEN
        REWRITE_TAC [REAL_POW_EQ_0] THEN ASM_REWRITE_TAC [] THEN
        UNDISCH_TAC (← q r"x < &1") THEN UNDISCH_TAC (← q "u:real <= x") THEN
        REAL_ARITH_TAC]])

  -- @@RETURN BEGIN
  return { MCLAURIN_ALL_LT, MCLAURIN_ZERO, MCLAURIN_ALL_LE, MCLAURIN_EXP_LEMMA,
           MCLAURIN_EXP_LT, MCLAURIN_EXP_LE, MCLAURIN_LN_POS, MCLAURIN_LN_NEG }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Versions for sin and cos.  (transc.ml 6058-6164)                          -/
/- ------------------------------------------------------------------------- -/

structure SinCosMcl where
  -- @@FIELDS
  MCLAURIN_SIN : thm
  MCLAURIN_COS : thm
  deriving Inhabited

@[nospecialize]
def setupSinCosMcl [HolBase] (D : TranscDeps) (BDiffConv : DiffConv) (BTrig1 : Trig1) (BMcLnExp : McLnExp) (AReals1 : HolLibrary.Analysis.Reals1) (AReals2 : HolLibrary.Analysis.Reals2) (ASums : HolLibrary.Analysis.Sums) :
    ExceptT String IO SinCosMcl := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, EXPAND_CASES_CONV, NUM_REDUCE_CONV, REAL_ARITH, .. } := D
  let { ADD1, ADD_ASSOC, ARITH_EQ, ARITH_EVEN, DIVISION, DIV_MULT, ETA_AX, EVEN_ADD,
        EVEN_MULT, MOD_0, MOD_MULT_ADD, REAL_ABS_DIV, REAL_ABS_INV, REAL_ABS_MUL,
        REAL_ABS_NEG, REAL_ABS_NUM, REAL_ABS_POS, REAL_ABS_POW, .. } := D.core1
  let { REAL_INV_MUL, REAL_LE_INV_EQ, REAL_LE_MUL2, REAL_LE_RMUL, REAL_MUL_ASSOC,
        REAL_MUL_LID, REAL_POW_LE, REAL_POW_NEG, REAL_POW_ONE, real_div, .. } := D.core2
  let { DIFF_CONV, .. } := BDiffConv
  let { COS_0, COS_BOUND, SIN_0, SIN_BOUND, .. } := BTrig1
  let { MCLAURIN_ALL_LE, .. } := BMcLnExp
  let { REAL_LE_REFL, REAL_MUL_LZERO, REAL_MUL_RID, REAL_NEG_NEG, .. } := AReals1
  let { REAL_NEG_0, REAL_POS, .. } := AReals2
  let { SUM_EQ, .. } := ASums
  -- @@SCOPE END
  -- `W(C SUBGOAL_THEN ttac o funpow 2 lhand o snd)`
  let subgoalLhand2 (ttac : thm_tactic) : tactic := fun gl => ExceptT.run do
    let t ← liftExcept (funpow 2 (fun (m : Except String term) => do lhand (← m)) (pure gl.2))
    ExceptT.mk (SUBGOAL_THEN t ttac gl)
  -- `W(MP_TAC o DIFF_CONV o lhand o rator o snd)`
  let mpDiffLR : tactic := fun gl => ExceptT.run do
    let t ← liftExcept (do lhand (← rator gl.2))
    ExceptT.mk (MP_TAC (← ExceptT.mk (DIFF_CONV t)) gl)

  let MCLAURIN_SIN ← prove
   r"!x n. abs(sin x -
             sum(0,n) (\m. (if EVEN m then &0
                            else -- &1 pow ((m - 1) DIV 2) / &(FACT m)) *
                            x pow m))
         <= inv(&(FACT n)) * abs(x) pow n"
   (← do
    let a4 ← ARITH_RULE (← q r"x * 4 = 2 * 2 * x")
    let a3 ← ARITH_RULE (← q r"x * 4 + 2 = 2 * (2 * x + 1)")
    let a2 ← ARITH_RULE (← q r"(x + 3) - 1 = x + 2")
    let a1 ← ARITH_RULE (← q r"(x + 1) - 1 = x")
    let r1 ← REAL_ARITH (← q r"(x = y) /\ abs(u) <= v ==> abs((x + u) - y) <= v")
    let etaT ← EQT_INTRO (← SPEC_ALL ETA_AX)
    pure (REPEAT STRIP_TAC THEN
      MP_TAC (← SPECL [← q "sin", ← q r"\n x. if n MOD 4 = 0 then sin(x)
                                else if n MOD 4 = 1 then cos(x)
                                else if n MOD 4 = 2 then --sin(x)
                                else --cos(x)"] MCLAURIN_ALL_LE) THEN
      subgoalLhand2 (fun th => REWRITE_TAC [th]) THENL
       [CONJ_TAC THENL
         [SIMP_TAC [MOD_0, ARITH_EQ, etaT], ALL_TAC] THEN
        X_GEN_TAC (← q "m:num") THEN X_GEN_TAC (← q "y:real") THEN REWRITE_TAC [] THEN
        MP_TAC (← SPECL [← q "m:num", ← q "4"] DIVISION) THEN
        REWRITE_TAC [ARITH_EQ] THEN ABBREV_TAC (← q "d = m MOD 4") THEN
        DISCH_THEN (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
        REWRITE_TAC [ADD1, ← GSYM ADD_ASSOC, MOD_MULT_ADD] THEN
        SPEC_TAC (← q "d:num", ← q "d:num") THEN CONV_TAC EXPAND_CASES_CONV THEN
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [] THEN
        REPEAT CONJ_TAC THEN
        mpDiffLR THEN
        SIMP_TAC [REAL_MUL_RID, REAL_NEG_NEG], ALL_TAC] THEN
      DISCH_THEN (MP_TAC o SPECL [← q "x:real", ← q "n:num"]) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "t:real")
        (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
      MATCH_MP_TAC r1 THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC (← q "r:num") THEN STRIP_TAC THEN
        REWRITE_TAC [SIN_0, COS_0, REAL_NEG_0] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN
        MP_TAC (← SPECL [← q "r:num", ← q "4"] DIVISION) THEN REWRITE_TAC [ARITH_EQ] THEN
        DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
        DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC
          (RAND_CONV o ONCE_DEPTH_CONV) [th] THEN
          MP_TAC (← SYM th))) THEN
        REWRITE_TAC [EVEN_ADD, EVEN_MULT, ARITH_EVEN] THEN
        UNDISCH_TAC (← q "r MOD 4 < 4") THEN
        SPEC_TAC (← q "r MOD 4", ← q "d:num") THEN CONV_TAC EXPAND_CASES_CONV THEN
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [] THEN
        REWRITE_TAC [real_div, REAL_MUL_LZERO] THEN
        SIMP_TAC [a1, a2, a3, a4] THEN
        SIMP_TAC [DIV_MULT, ARITH_EQ] THEN
        REWRITE_TAC [REAL_POW_NEG, EVEN_ADD, EVEN_MULT, ARITH_EVEN, REAL_POW_ONE],
        ALL_TAC] THEN
      REWRITE_TAC [REAL_ABS_MUL, REAL_INV_MUL] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC [REAL_ABS_POS] THEN CONJ_TAC THENL
       [REWRITE_TAC [real_div, REAL_ABS_MUL] THEN
        GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_LID] THEN
        REWRITE_TAC [REAL_ABS_INV, REAL_ABS_NUM] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN
        SIMP_TAC [REAL_LE_INV_EQ, REAL_POS] THEN
        REPEAT COND_CASES_TAC THEN REWRITE_TAC [REAL_ABS_NEG, SIN_BOUND, COS_BOUND],
        ALL_TAC] THEN
      REWRITE_TAC [REAL_ABS_POW, REAL_LE_REFL]))

  let MCLAURIN_COS ← prove
   r"!x n. abs(cos x -
                   sum(0,n) (\m. (if EVEN m
                                  then -- &1 pow (m DIV 2) / &(FACT m)
                                  else &0) * x pow m))
               <= inv(&(FACT n)) * abs(x) pow n"
   (← do
    let a2 ← ARITH_RULE (← q r"x * 4 + 0 = 2 * 2 * x")
    let a1 ← ARITH_RULE (← q r"x * 4 + 2 = 2 * (2 * x + 1)")
    let r1 ← REAL_ARITH (← q r"(x = y) /\ abs(u) <= v ==> abs((x + u) - y) <= v")
    let etaT ← EQT_INTRO (← SPEC_ALL ETA_AX)
    pure (REPEAT STRIP_TAC THEN
      MP_TAC (← SPECL [← q "cos", ← q r"\n x. if n MOD 4 = 0 then cos(x)
                                else if n MOD 4 = 1 then --sin(x)
                                else if n MOD 4 = 2 then --cos(x)
                                else sin(x)"] MCLAURIN_ALL_LE) THEN
      subgoalLhand2 (fun th => REWRITE_TAC [th]) THENL
       [CONJ_TAC THENL
         [SIMP_TAC [MOD_0, ARITH_EQ, etaT], ALL_TAC] THEN
        X_GEN_TAC (← q "m:num") THEN X_GEN_TAC (← q "y:real") THEN REWRITE_TAC [] THEN
        MP_TAC (← SPECL [← q "m:num", ← q "4"] DIVISION) THEN
        REWRITE_TAC [ARITH_EQ] THEN ABBREV_TAC (← q "d = m MOD 4") THEN
        DISCH_THEN (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
        REWRITE_TAC [ADD1, ← GSYM ADD_ASSOC, MOD_MULT_ADD] THEN
        SPEC_TAC (← q "d:num", ← q "d:num") THEN CONV_TAC EXPAND_CASES_CONV THEN
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [] THEN
        REPEAT CONJ_TAC THEN
        mpDiffLR THEN
        SIMP_TAC [REAL_MUL_RID, REAL_NEG_NEG], ALL_TAC] THEN
      DISCH_THEN (MP_TAC o SPECL [← q "x:real", ← q "n:num"]) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "t:real")
        (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
      MATCH_MP_TAC r1 THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC (← q "r:num") THEN STRIP_TAC THEN
        REWRITE_TAC [SIN_0, COS_0, REAL_NEG_0] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN
        MP_TAC (← SPECL [← q "r:num", ← q "4"] DIVISION) THEN REWRITE_TAC [ARITH_EQ] THEN
        DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
        DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC
          (RAND_CONV o ONCE_DEPTH_CONV) [th] THEN
          MP_TAC (← SYM th))) THEN
        REWRITE_TAC [EVEN_ADD, EVEN_MULT, ARITH_EVEN] THEN
        UNDISCH_TAC (← q "r MOD 4 < 4") THEN
        SPEC_TAC (← q "r MOD 4", ← q "d:num") THEN CONV_TAC EXPAND_CASES_CONV THEN
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [] THEN
        REWRITE_TAC [real_div, REAL_MUL_LZERO] THEN
        REWRITE_TAC [a1, a2] THEN
        SIMP_TAC [DIV_MULT, ARITH_EQ] THEN
        REWRITE_TAC [REAL_POW_NEG, EVEN_ADD, EVEN_MULT, ARITH_EVEN, REAL_POW_ONE],
        ALL_TAC] THEN
      REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_DIV, REAL_MUL_ASSOC, REAL_ABS_POW] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN SIMP_TAC [REAL_POW_LE, REAL_ABS_POS] THEN
      REWRITE_TAC [real_div, REAL_ABS_NUM] THEN
      GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [REAL_LE_INV_EQ, REAL_POS] THEN
      REPEAT COND_CASES_TAC THEN REWRITE_TAC [REAL_ABS_NEG, SIN_BOUND, COS_BOUND]))

  -- @@RETURN BEGIN
  return { MCLAURIN_SIN, MCLAURIN_COS }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Taylor series for atan; needs a bit more preparation.                     -/
/- (transc.ml 6166-6434)                                                     -/
/- ------------------------------------------------------------------------- -/

structure AtnSer where
  -- @@FIELDS
  REAL_ATN_POWSER_SUMMABLE : thm
  REAL_ATN_POWSER_DIFFS_SUMMABLE : thm
  REAL_ATN_POWSER_DIFFS_SUM : thm
  REAL_ATN_POWSER_DIFFS_DIFFS_SUMMABLE : thm
  REAL_ATN_POWSER_DIFFL : thm
  REAL_ATN_POWSER : thm
  MCLAURIN_ATN : thm
  deriving Inhabited

@[nospecialize]
def setupAtnSer [HolBase] (D : TranscDeps) (BPowSer : PowSer) (BTermDiff : TermDiff) (BTrig2 : Trig2) (BTan : Tan) (BInvTrig : InvTrig) (AReals1 : HolLibrary.Analysis.Reals1) (AReals2 : HolLibrary.Analysis.Reals2) (AReals3 : HolLibrary.Analysis.Reals3) (APow : HolLibrary.Analysis.Pow) (ASums : HolLibrary.Analysis.Sums) (ASeries1 : HolLibrary.Analysis.Series1) (ASeries2 : HolLibrary.Analysis.Series2) (ADiffs : HolLibrary.Analysis.Diffs) (AMvt : HolLibrary.Analysis.Mvt) :
    ExceptT String IO AtnSer := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC,
        REAL_RAT_REDUCE_CONV, num_CONV, .. } := D
  let { ADD1, ADD_CLAUSES, ADD_SYM, ARITH, ARITH_EQ, ARITH_EVEN, DIV_MULT, EQ_IMP,
        EVEN, EVEN_MULT, GE, LT_NZ, NOT_SUC, REAL_ABS_ABS, REAL_ABS_DIV, REAL_ABS_MUL,
        REAL_ABS_NEG, REAL_ABS_NUM, REAL_ABS_NZ, REAL_ABS_POS, REAL_ABS_POW,
        REAL_ADD_LID, REAL_ADD_RID, .. } := D.core1
  let { REAL_DIV_LMUL, REAL_ENTIRE, REAL_INV_1, REAL_LE_INV2, REAL_LE_LDIV_EQ,
        REAL_LE_LMUL, REAL_LE_RDIV_EQ, REAL_LE_RMUL, REAL_LT_LDIV_EQ, REAL_LT_MUL2,
        REAL_LT_RDIV_EQ, REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LNEG, REAL_MUL_SYM,
        REAL_OF_NUM_ADD, REAL_OF_NUM_EQ, REAL_OF_NUM_LE, REAL_OF_NUM_LT, REAL_POW_2,
        REAL_POW_ADD, REAL_POW_EQ_0, REAL_POW_LE, REAL_POW_MUL, REAL_POW_ONE,
        REAL_POW_POW, real_div, real_pow, .. } := D.core2
  let { diffs, .. } := BPowSer
  let { TERMDIFF, .. } := BTermDiff
  let { PI2_BOUNDS, .. } := BTrig2
  let { TAN_0, .. } := BTan
  let { DIFF_ATN, TAN_ATN, .. } := BInvTrig
  let { REAL_LE_MUL, REAL_LE_RADD, REAL_LE_REFL, REAL_LE_TRANS, REAL_LT_IMP_LE,
        REAL_MUL_LZERO, REAL_MUL_RID, REAL_MUL_RZERO, .. } := AReals1
  let { REAL_POS, REAL_SUB_LDISTRIB, REAL_SUB_REFL, .. } := AReals2
  let { REAL_LE_LDIV, REAL_LE_SUB_LADD, REAL_LT_SUB_LADD, .. } := AReals3
  let { REAL_ARCH_SIMPLE, .. } := APow
  let { sum, .. } := ASums
  let { SER_OFFSET, SER_PAIR, SUMMABLE_SUM, SUM_SUMMABLE, SUM_UNIQ, summable, .. } := ASeries1
  let { GP, SER_ABS, SER_CMUL, SER_COMPAR, SER_COMPARA, SER_LE, SER_RATIO, .. } := ASeries2
  let { DIFF_SUB, .. } := ADiffs
  let { DIFF_ISCONST_END_SIMPLE, .. } := AMvt
  -- @@SCOPE END

  let REAL_ATN_POWSER_SUMMABLE ← prove
   r"!x. abs(x) < &1
       ==> summable (\n. (if EVEN n then &0
                          else --(&1) pow ((n - 1) DIV 2) / &n) * x pow n)"
   (← do
    let a1 ← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")
    pure (REPEAT STRIP_TAC THEN MATCH_MP_TAC SER_COMPAR THEN
      EXISTS_TAC (← q r"\n. abs(x) pow n") THEN CONJ_TAC THENL
       [EXISTS_TAC (← q "0") THEN REPEAT STRIP_TAC THEN REWRITE_TAC [] THEN
        COND_CASES_TAC THEN
        SIMP_TAC [REAL_POW_LE, REAL_MUL_LZERO, REAL_ABS_POS, REAL_ABS_NUM] THEN
        REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_DIV, REAL_ABS_NEG, REAL_ABS_POW] THEN
        REWRITE_TAC [REAL_ABS_NUM, REAL_POW_ONE, REAL_MUL_LID] THEN
        REWRITE_TAC [real_div, REAL_MUL_LID] THEN
        ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REWRITE_TAC [← GSYM real_div] THEN
        MATCH_MP_TAC REAL_LE_LDIV THEN
        CONJ_TAC THENL [ASM_MESON_TAC [REAL_OF_NUM_LT, EVEN, LT_NZ], ALL_TAC] THEN
        GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN
        SIMP_TAC [REAL_POW_LE, REAL_ABS_POS] THEN
        ASM_MESON_TAC [REAL_OF_NUM_LE, EVEN, a1],
        ALL_TAC] THEN
      REWRITE_TAC [summable] THEN EXISTS_TAC (← q r"inv(&1 - abs x)") THEN
      MATCH_MP_TAC GP THEN ASM_REWRITE_TAC [REAL_ABS_ABS]))

  let REAL_ATN_POWSER_DIFFS_SUMMABLE ← prove
   r"!x. abs(x) < &1
       ==> summable (\n. diffs (\n. (if EVEN n then &0
                                     else --(&1) pow ((n - 1) DIV 2) / &n)) n *
                         x pow n)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [diffs] THEN
    MATCH_MP_TAC SER_COMPAR THEN
    EXISTS_TAC (← q r"\n. abs(x) pow n") THEN CONJ_TAC THENL
     [EXISTS_TAC (← q "0") THEN REPEAT STRIP_TAC THEN REWRITE_TAC [] THEN
      COND_CASES_TAC THEN
      SIMP_TAC [REAL_POW_LE, REAL_MUL_LZERO, REAL_MUL_RZERO,
               REAL_ABS_POS, REAL_ABS_NUM] THEN
      SIMP_TAC [REAL_MUL_ASSOC, REAL_DIV_LMUL, REAL_OF_NUM_EQ, NOT_SUC] THEN
      REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_DIV, REAL_ABS_NEG, REAL_ABS_POW] THEN
      REWRITE_TAC [REAL_ABS_NUM, REAL_POW_ONE, REAL_MUL_LID, REAL_LE_REFL],
      ALL_TAC] THEN
    REWRITE_TAC [summable] THEN EXISTS_TAC (← q r"inv(&1 - abs x)") THEN
    MATCH_MP_TAC GP THEN ASM_REWRITE_TAC [REAL_ABS_ABS])

  let REAL_ATN_POWSER_DIFFS_SUM ← prove
   r"!x. abs(x) < &1
       ==> (\n. diffs (\n. (if EVEN n then &0
                            else --(&1) pow ((n - 1) DIV 2) / &n)) n * x pow n)
           sums (inv(&1 + x pow 2))"
   (← do
    let r1 ← REAL_ARITH (← q r"&1 + x = &1 - (--x)")
    let a1 ← ARITH_RULE (← q r"SUC n - 1 = n")
    pure (REPEAT STRIP_TAC THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP REAL_ATN_POWSER_DIFFS_SUMMABLE) THEN
      DISCH_THEN (fun th => tactic_of do
        let b2 ← MATCH_MP SER_PAIR th
        let b1 ← MATCH_MP SUMMABLE_SUM th
        pure (MP_TAC b1 THEN MP_TAC b2)) THEN
      SUBGOAL_THEN
       (← q r"(\n. sum (2 * n,2) (\n. diffs
          (\n. (if EVEN n then &0
                else --(&1) pow ((n - 1) DIV 2) / &n)) n * x pow n)) =
        (\n. --(x pow 2) pow n)")
      SUBST1_TAC THENL
       [ABS_TAC THEN
        CONV_TAC (LAND_CONV (LAND_CONV (RAND_CONV (TOP_DEPTH_CONV num_CONV)))) THEN
        REWRITE_TAC [sum, diffs, ADD_CLAUSES, EVEN_MULT, ARITH_EVEN, EVEN] THEN
        REWRITE_TAC [REAL_ADD_LID, REAL_ADD_RID, REAL_MUL_LZERO,
                    REAL_MUL_RZERO] THEN
        SIMP_TAC [a1, DIV_MULT, ARITH_EQ] THEN
        SIMP_TAC [REAL_MUL_ASSOC, REAL_DIV_LMUL, REAL_OF_NUM_EQ, NOT_SUC] THEN
        ONCE_REWRITE_TAC [← GSYM REAL_POW_POW] THEN
        REWRITE_TAC [← GSYM REAL_POW_MUL] THEN
        REWRITE_TAC [REAL_MUL_LNEG, REAL_MUL_LID], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"(\n. --(x pow 2) pow n) sums inv (&1 + x pow 2)") MP_TAC THENL
       [ONCE_REWRITE_TAC [r1] THEN
        MATCH_MP_TAC GP THEN
        REWRITE_TAC [REAL_ABS_NEG, REAL_ABS_POW] THEN
        GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_LID] THEN
        ASM_SIMP_TAC [REAL_POW_2, REAL_LT_MUL2, REAL_ABS_POS], ALL_TAC] THEN
      MESON_TAC [SUM_UNIQ]))

  let REAL_ATN_POWSER_DIFFS_DIFFS_SUMMABLE ← prove
   r"!x. abs(x) < &1
       ==> summable
             (\n. diffs (diffs
                 (\n. (if EVEN n then &0
                       else --(&1) pow ((n - 1) DIV 2) / &n))) n * x pow n)"
   (← do
    let r3 ← REAL_ARITH (← q r"a <= b ==> a <= b + &1")
    let r2 ← REAL_ARITH (← q r"&1 <= x ==> x <= y ==> &1 <= y")
    let r1 ← REAL_ARITH (← q r"x + &1 <= y <=> &1 <= y - x * &1")
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [diffs] THEN
      MATCH_MP_TAC SER_COMPAR THEN
      EXISTS_TAC (← q r"\n. &(SUC n) * abs(x) pow n") THEN CONJ_TAC THENL
       [EXISTS_TAC (← q "0") THEN REPEAT STRIP_TAC THEN
        REWRITE_TAC [REAL_ABS_NUM, REAL_ABS_MUL, ← GSYM REAL_MUL_ASSOC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [REAL_POS] THEN
        COND_CASES_TAC THEN
        SIMP_TAC [REAL_POW_LE, REAL_MUL_LZERO, REAL_MUL_RZERO,
                 REAL_ABS_POS, REAL_ABS_NUM] THEN
        REWRITE_TAC [REAL_ABS_DIV, REAL_ABS_NUM, REAL_MUL_ASSOC] THEN
        SIMP_TAC [REAL_DIV_LMUL, REAL_OF_NUM_EQ, NOT_SUC] THEN
        REWRITE_TAC [REAL_ABS_POW, REAL_ABS_NEG, REAL_POW_ONE, REAL_MUL_LID,
                    REAL_ABS_NUM, REAL_LE_REFL], ALL_TAC] THEN
      MATCH_MP_TAC SER_RATIO THEN
      SUBGOAL_THEN (← q r"?c. abs(x) < c /\ c < &1") STRIP_ASSUME_TAC THENL
       [EXISTS_TAC (← q r"(&1 + abs(x)) / &2") THEN
        SIMP_TAC [REAL_LT_LDIV_EQ, REAL_LT_RDIV_EQ, REAL_OF_NUM_LT, ARITH] THEN
        UNDISCH_TAC (← q r"abs(x) < &1") THEN REAL_ARITH_TAC, ALL_TAC] THEN
      EXISTS_TAC (← q "c:real") THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"?N. !n. n >= N ==> &(SUC(SUC n)) * abs(x) <= &(SUC n) * c")
      STRIP_ASSUME_TAC THENL
       [ALL_TAC,
        EXISTS_TAC (← q "N:num") THEN REPEAT STRIP_TAC THEN
        REWRITE_TAC [real_pow, REAL_ABS_MUL, REAL_MUL_ASSOC] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [REAL_ABS_POS] THEN
        REWRITE_TAC [REAL_ABS_NUM, REAL_ABS_ABS] THEN
        GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN ASM_SIMP_TAC []] THEN
      ASM_CASES_TAC (← q r"x = &0") THENL
       [ASM_REWRITE_TAC [REAL_ABS_NUM, REAL_MUL_RZERO] THEN
        EXISTS_TAC (← q "0") THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
        REWRITE_TAC [REAL_POS] THEN UNDISCH_TAC (← q "abs(x) < c") THEN REAL_ARITH_TAC,
        ALL_TAC] THEN
      ASM_SIMP_TAC [← GSYM REAL_LE_RDIV_EQ, ← GSYM REAL_ABS_NZ] THEN
      REWRITE_TAC [real_div, ← GSYM REAL_MUL_ASSOC] THEN
      REWRITE_TAC [← GSYM real_div] THEN
      REWRITE_TAC [ADD1, ← GSYM REAL_OF_NUM_ADD] THEN
      ONCE_REWRITE_TAC [r1] THEN
      REWRITE_TAC [← GSYM REAL_SUB_LDISTRIB] THEN
      SUBGOAL_THEN (← q r"?N. &1 <= &N * (c / abs x - &1)") STRIP_ASSUME_TAC THENL
       [ALL_TAC,
        EXISTS_TAC (← q "N:num") THEN REWRITE_TAC [GE] THEN REPEAT STRIP_TAC THEN
        FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP r2) THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_SIMP_TAC [r3, REAL_OF_NUM_LE, REAL_LE_RADD] THEN
        REWRITE_TAC [REAL_LE_SUB_LADD, REAL_ADD_LID] THEN
        ASM_SIMP_TAC [REAL_LE_RDIV_EQ, ← GSYM REAL_ABS_NZ, REAL_MUL_LID,
                     REAL_LT_IMP_LE]] THEN
      ASM_SIMP_TAC [← GSYM REAL_LE_LDIV_EQ, REAL_LT_SUB_LADD, REAL_ADD_LID,
                   REAL_LT_RDIV_EQ, ← GSYM REAL_ABS_NZ, REAL_MUL_LID,
                   REAL_ARCH_SIMPLE]))

  let REAL_ATN_POWSER_DIFFL ← prove
   r"!x. abs(x) < &1
       ==> ((\x. suminf (\n. (if EVEN n then &0
                              else --(&1) pow ((n - 1) DIV 2) / &n) * x pow n))
            diffl (inv(&1 + x pow 2))) x"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP REAL_ATN_POWSER_DIFFS_SUM) THEN
    DISCH_THEN (SUBST1_TAC o MATCH_MP SUM_UNIQ) THEN
    MATCH_MP_TAC TERMDIFF THEN
    SUBGOAL_THEN (← q r"?K. abs(x) < abs(K) /\ abs(K) < &1") STRIP_ASSUME_TAC THENL
     [EXISTS_TAC (← q r"(&1 + abs(x)) / &2") THEN
      SIMP_TAC [REAL_LT_LDIV_EQ, REAL_ABS_DIV, REAL_ABS_NUM,
               REAL_LT_RDIV_EQ, REAL_OF_NUM_LT, ARITH] THEN
      UNDISCH_TAC (← q r"abs(x) < &1") THEN REAL_ARITH_TAC, ALL_TAC] THEN
    EXISTS_TAC (← q "K:real") THEN ASM_REWRITE_TAC [] THEN
    ASM_SIMP_TAC [REAL_ATN_POWSER_SUMMABLE, REAL_ATN_POWSER_DIFFS_SUMMABLE,
                 REAL_ATN_POWSER_DIFFS_DIFFS_SUMMABLE])

  let REAL_ATN_POWSER ← prove
   r"!x. abs(x) < &1
       ==> (\n. (if EVEN n then &0
                 else --(&1) pow ((n - 1) DIV 2) / &n) * x pow n)
           sums (atn x)"
   (← do
    let dAtn ← SPEC (← q "u:real") DIFF_ATN
    let r4 ← REAL_ARITH (← q r"~(x = &0) ==> &0 < x \/ x < &0")
    let r3 ← REAL_ARITH (← q r"&0 < x ==> --x < &0")
    let r2 ← REAL_ARITH (← q r"(a = &0) /\ (b = &0) ==> (a - b = &0)")
    let r1 ← REAL_ARITH (← q r"(a = b) <=> (a - b = &0)")
    pure (REPEAT STRIP_TAC THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP REAL_ATN_POWSER_SUMMABLE) THEN
      DISCH_THEN (MP_TAC o MATCH_MP SUMMABLE_SUM) THEN
      SUBGOAL_THEN
       (← q r"suminf (\n. (if EVEN n then &0
                     else --(&1) pow ((n - 1) DIV 2) / &n) * x pow n) = atn(x)")
       (fun th => REWRITE_TAC [th]) THEN
      ONCE_REWRITE_TAC [r1] THEN
      SUBGOAL_THEN
       (← q r"suminf (\n. (if EVEN n then &0
                     else --(&1) pow ((n - 1) DIV 2) / &n) * &0 pow n) -
        atn(&0) = &0")
      MP_TAC THENL
       [MATCH_MP_TAC r2 THEN
        CONJ_TAC THENL
         [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_UNIQ THEN
          MP_TAC (← SPEC (← q r"&0") GP) THEN
          REWRITE_TAC [REAL_ABS_NUM, REAL_OF_NUM_LT, ARITH] THEN
          DISCH_THEN (MP_TAC o SPEC (← q r"&0") o MATCH_MP SER_CMUL) THEN
          REWRITE_TAC [REAL_MUL_LZERO] THEN
          MATCH_MP_TAC EQ_IMP THEN
          AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
          COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_MUL_LZERO] THEN
          CONV_TAC SYM_CONV THEN
          REWRITE_TAC [REAL_ENTIRE, REAL_POW_EQ_0] THEN ASM_MESON_TAC [EVEN],
          GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← GSYM TAN_0] THEN
          MATCH_MP_TAC TAN_ATN THEN
          SIMP_TAC [PI2_BOUNDS, r3]],
        ALL_TAC] THEN
      ASM_CASES_TAC (← q r"x = &0") THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [← SYM th])) THEN
      MP_TAC (← SPEC (← q r"\x. suminf (\n. (if EVEN n then &0

                           else --(&1) pow ((n - 1) DIV 2) / &n) * x pow n) -
              atn x") DIFF_ISCONST_END_SIMPLE) THEN
      FIRST_ASSUM (DISJ_CASES_TAC o MATCH_MP r4)
      THENL
       [DISCH_THEN (MP_TAC o SPECL [← q r"&0", ← q "x:real"]),
        CONV_TAC (RAND_CONV SYM_CONV) THEN
        DISCH_THEN (MP_TAC o SPECL [← q "x:real", ← q r"&0"])] THEN
      (REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
       ASM_REWRITE_TAC [] THEN
       X_GEN_TAC (← q "u:real") THEN REPEAT STRIP_TAC THEN
       SUBGOAL_THEN (← q r"abs(u) < &1") (MP_TAC o MATCH_MP REAL_ATN_POWSER_DIFFL) THENL
        [POP_ASSUM_LIST (fun ths => tactic_of do pure (MP_TAC (← endItlistM CONJ ths))) THEN
         REAL_ARITH_TAC,
         ALL_TAC] THEN
       DISCH_THEN (MP_TAC o (fun th => CONJ th dAtn)) THEN
       DISCH_THEN (MP_TAC o MATCH_MP DIFF_SUB) THEN
       REWRITE_TAC [REAL_SUB_REFL])))

  let MCLAURIN_ATN ← prove
   r"!x n. abs(x) < &1
           ==> abs(atn x -
                   sum(0,n) (\m. (if EVEN m then &0
                                  else --(&1) pow ((m - 1) DIV 2) / &m) *
                                  x pow m))
               <= abs(x) pow n / (&1 - abs x)"
   (← do
    let a1 ← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")
    let r2 ← REAL_ARITH (← q r"abs(x) < &1 ==> abs(abs x) < &1")
    let r1 ← REAL_ARITH (← q r"abs(r) <= e ==> (f - s = r) ==> abs(f - s) <= e")
    pure (REPEAT STRIP_TAC THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP REAL_ATN_POWSER) THEN
      DISCH_THEN (fun th => tactic_of do
        let b2 ← MATCH_MP SUM_SUMMABLE th
        let b1 ← SYM (← MATCH_MP SUM_UNIQ th)
        pure (ASSUME_TAC b1 THEN MP_TAC b2)) THEN
      DISCH_THEN (MP_TAC o MATCH_MP SER_OFFSET) THEN
      DISCH_THEN (MP_TAC o SPEC (← q "n:num")) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (MP_TAC o MATCH_MP SUM_UNIQ) THEN
      MATCH_MP_TAC r1 THEN
      SUBGOAL_THEN
       (← q r"(\m. abs(x) pow (m + n)) sums (abs(x) pow n) * inv(&1 - abs(x))")
      ASSUME_TAC THENL
       [FIRST_ASSUM (MP_TAC o MATCH_MP GP o MATCH_MP r2) THEN
        DISCH_THEN (MP_TAC o SPEC (← q "abs(x) pow n") o MATCH_MP SER_CMUL) THEN
        ONCE_REWRITE_TAC [ADD_SYM] THEN REWRITE_TAC [← GSYM REAL_POW_ADD],
        ALL_TAC] THEN
      FIRST_ASSUM (SUBST1_TAC o MATCH_MP SUM_UNIQ o REWRITE_RULE [← GSYM real_div]) THEN
      SUBGOAL_THEN
       (← q r"!m. abs((if EVEN (m + n) then &0
                 else --(&1) pow (((m + n) - 1) DIV 2) / &(m + n)) *
                 x pow (m + n))
            <= abs(x) pow (m + n)")
      ASSUME_TAC THENL
       [GEN_TAC THEN COND_CASES_TAC THEN
        SIMP_TAC [REAL_MUL_LZERO, REAL_ABS_NUM, REAL_POW_LE, REAL_ABS_POS] THEN
        REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_DIV, REAL_ABS_POW, REAL_ABS_NEG] THEN
        REWRITE_TAC [REAL_ABS_NUM, REAL_POW_ONE, REAL_MUL_LID] THEN
        GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN SIMP_TAC [REAL_POW_LE, REAL_ABS_POS] THEN
        REWRITE_TAC [real_div, REAL_MUL_LID] THEN
        GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_INV_1] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        REWRITE_TAC [REAL_OF_NUM_LE, a1] THEN
        ASM_MESON_TAC [EVEN], ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       (← q r"suminf (\m. abs((if EVEN (m + n) then &0
                         else --(&1) pow (((m + n) - 1) DIV 2) / &(m + n)) *
                        x pow (m + n)))") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SER_ABS THEN MATCH_MP_TAC SER_COMPARA THEN
        EXISTS_TAC (← q r"\m. abs(x) pow (m + n)") THEN
        ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [SUM_SUMMABLE], ALL_TAC] THEN
      MATCH_MP_TAC SER_LE THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SER_COMPARA THEN
        EXISTS_TAC (← q r"\m. abs(x) pow (m + n)") THEN
        ASM_REWRITE_TAC [], ALL_TAC] THEN
      ASM_MESON_TAC [SUM_SUMMABLE]))

  -- @@RETURN BEGIN
  return { REAL_ATN_POWSER_SUMMABLE, REAL_ATN_POWSER_DIFFS_SUMMABLE,
           REAL_ATN_POWSER_DIFFS_SUM, REAL_ATN_POWSER_DIFFS_DIFFS_SUMMABLE,
           REAL_ATN_POWSER_DIFFL, REAL_ATN_POWSER, MCLAURIN_ATN }
  -- @@RETURN END

end HolLibrary.Transc
