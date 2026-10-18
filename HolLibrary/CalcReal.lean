/- ========================================================================= -/
/- Calculation with real numbers (Boehm-style but by inference).             -/
/- ========================================================================= -/
/- File: HolLibrary/CalcReal.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/calc_real.ml`, by hand, in file
  order, in the style of HolLibrary/Transc.lean and HolLibrary/Pocklington.lean
  (see there and HolMath/Base.lean for the conventions).  calc_real.ml begins
  with `needs "Library/transc.ml"`; the theorems it uses from transc.ml,
  analysis.ml and the core library are supplied via the CoreThms structures
  (SessionLibrary.CalcReal fills them).  Each section is a bundle (a
  `structure`) built by a `setup` function; SessionLibrary/CalcReal.lean
  builds the bundles in order and exports every name under its HOL Light
  name.

  The overall conversion (REALCALC_CONV, thm_eval, raw_eval, thm_wrap) is
  OCaml code that approximates real expressions by inference; its recursive
  functions are top-level `partial def`s taking a context structure (`RCtx`)
  of the theorems and conversions they use, and `realcalc_cache` is an
  `IO.Ref` created once at setup.  `num` arithmetic is exact (`Rat`).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, REAL_ARITH, TAUT) they are bound first, in
  OCaml's order.
-/

import HolLibrary.Transc

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolMath.CalcInt (dest_realintconst is_ratconst rat_of_term)

namespace HolLibrary.CalcReal

-- @@COREFILL BEGIN
/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ABS_N ABS_NZ ADD1 ADD_ASSOC ADD_CLAUSES ADD_SYM ARITH ARITH_EQ ARITH_SUC
   BETA_THM CONJ_ASSOC CONJ_SYM DE_MORGAN_THM EQ_TRANS EXISTS_OR_THM
   EXISTS_REFL FACT FACT_LE FACT_LT FACT_MONO LE LET_CASES LE_0 LE_ADD
   LE_CASES LE_EXISTS LE_LT LE_MULT2 LE_SUC LE_SUC_LT LN_1 LT LT_0 LT_CASES
   LT_EXISTS LT_SUC LT_TRANS MCLAURIN_EXP_LE MCLAURIN_LN_POS MULT_2 MULT_AC
   MULT_CLAUSES NOT_LT NOT_SUC POW_0 POW_2 REAL_ABS_0 REAL_ABS_INV
   REAL_ABS_MUL REAL_ABS_NEG REAL_ABS_NUM REAL_ABS_NZ REAL_ABS_POS
   REAL_ABS_POW REAL_ABS_SUB REAL_ABS_SUB_ABS REAL_ABS_TRIANGLE REAL_ADD_AC
   REAL_ADD_ASSOC REAL_ADD_LDISTRIB REAL_ADD_RDISTRIB REAL_ADD_RID
   REAL_ADD_SYM REAL_DIV_1 REAL_ENTIRE REAL_EQ_IMP_LE REAL_EQ_NEG2
   REAL_EXP_ADD REAL_EXP_BOUND_LEMMA REAL_EXP_MONO_LE : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (REAL_EXP_POS_LE REAL_INV_0 REAL_INV_1 REAL_INV_EQ_0 REAL_INV_INV
   REAL_INV_LE_1 REAL_INV_MUL REAL_INV_POS REAL_LET_ADD2 REAL_LET_TRANS
   REAL_LE_ADD REAL_LE_ADD2 REAL_LE_ADDL REAL_LE_ADDR REAL_LE_INV
   REAL_LE_INV2 REAL_LE_INV_EQ REAL_LE_LADD REAL_LE_LCANCEL_IMP REAL_LE_LMUL
   REAL_LE_LMUL_EQ REAL_LE_LMUL_IMP REAL_LE_LT REAL_LE_MUL REAL_LE_MUL2
   REAL_LE_POW2 REAL_LE_RADD REAL_LE_RCANCEL_IMP REAL_LE_REFL REAL_LE_RMUL
   REAL_LE_SUB_LADD REAL_LE_SUB_RADD REAL_LE_TRANS REAL_LTE_ADD2
   REAL_LTE_TRANS REAL_LT_01 REAL_LT_ADD2 REAL_LT_ADDL REAL_LT_ADDR
   REAL_LT_IMP_LE REAL_LT_IMP_NZ REAL_LT_INV2 REAL_LT_INV_EQ
   REAL_LT_LCANCEL_IMP REAL_LT_LMUL REAL_LT_LMUL_EQ REAL_LT_MUL REAL_LT_MUL2
   REAL_LT_NEGTOTAL REAL_LT_POW2 REAL_LT_RCANCEL_IMP REAL_LT_REFL
   REAL_LT_RMUL_IMP REAL_LT_SQUARE REAL_LT_SUB_RADD REAL_MUL_2 REAL_MUL_AC
   REAL_MUL_ASSOC REAL_MUL_LID REAL_MUL_LINV REAL_MUL_LNEG REAL_MUL_LZERO
   REAL_MUL_RID REAL_MUL_RINV REAL_MUL_RNEG REAL_MUL_RZERO REAL_MUL_SYM
   REAL_NEG_ADD REAL_NEG_NEG REAL_NOT_LE : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms3 where
  (REAL_NOT_LT REAL_OF_NUM_ADD REAL_OF_NUM_EQ REAL_OF_NUM_LE REAL_OF_NUM_LT
   REAL_OF_NUM_MUL REAL_OF_NUM_POW REAL_OF_NUM_SUC REAL_POS REAL_POW_1
   REAL_POW_1_LE REAL_POW_2 REAL_POW_ADD REAL_POW_EQ_0 REAL_POW_INV
   REAL_POW_LE REAL_POW_LE2 REAL_POW_LT REAL_POW_LT2 REAL_POW_MONO
   REAL_POW_ONE REAL_POW_POW REAL_SUB_LDISTRIB REAL_SUB_LZERO
   REAL_SUB_RDISTRIB REAL_SUB_REFL REAL_SUB_RZERO SQRT_POS_LE SQRT_POS_LT
   SQRT_POW2 SQRT_POW_2 SUC_INJ SUM_0 SUM_ABS_LE SUM_BOUND SUM_DIFF
   SUM_REINDEX TRUTH real_abs real_div real_ge real_gt real_pow real_sub sum : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms4 where
  deriving Inhabited

-- @@COREFILL END

/-- What calcreal.ml uses from Session besides theorems. -/
structure CalcRealDeps where
  -- decision procedures and tactics
  ARITH_TAC : tactic
  MESON_TAC : List thm → tactic
  REAL_ARITH : term → ExceptT String IO thm
  REAL_ARITH_TAC : tactic
  INDUCT_TAC : tactic
  -- `REAL_INT_REDUCE_CONV` (calc_int.ml), Session re-exports it bare.
  REAL_INT_REDUCE_CONV : ioconv
  -- `REAL_INT_EQ_CONV` (calc_int.ml 177), Session re-exports it bare.
  REAL_INT_EQ_CONV : ioconv
  -- `REAL_LET_IMP` (real.ml 601): a RULE, Session re-exports it bare.
  REAL_LET_IMP : thm → ExceptT String IO thm
  -- `REAL_LE_IMP` (real.ml 597): a rule making a `<=`/`<` monotonicity lemma
  REAL_LE_IMP : thm → ExceptT String IO thm
  -- (Session: calc_num.ml, calc_int.ml, calc_rat.ml; REAL_SUM_CONV from Analysis)
  num_CONV : ioconv
  NUM_FACT_CONV : ioconv
  REAL_RAT_REDUCE_CONV : ioconv
  REAL_SUM_CONV : ioconv
  -- numeral/real-int syntax (Session: calc_num.ml, calc_int.ml)
  mk_numeral : Rat → Except String term
  mk_small_numeral : Int → Except String term
  mk_realintconst : Rat → Except String term
  -- conversions used by the approximation code (Session: calc_num.ml / calc_int.ml)
  NUM_SUC_CONV : ioconv
  NUM_ADD_CONV : ioconv
  NUM_REDUCE_CONV : ioconv
  REAL_INT_NEG_CONV : ioconv
  REAL_INT_ABS_CONV : ioconv
  REAL_INT_MUL_CONV : ioconv
  REAL_INT_SUB_CONV : ioconv
  REAL_INT_POW_CONV : ioconv
  REAL_INT_LE_CONV : ioconv
  REAL_RAT_LE_CONV : ioconv
  core1 : CoreThms1
  core2 : CoreThms2
  core3 : CoreThms3
  core4 : CoreThms4

/- ------------------------------------------------------------------------- -/
/- Various trivial lemmas and sundry results.  (calc_real.ml 7-129)          -/
/- ------------------------------------------------------------------------- -/

structure Lemmas where
  -- @@FIELDS
  REAL_SUB_SUM0 : thm
  REAL_MUL_RSUM0 : thm
  REAL_ABS_LEMMA : thm
  REAL_ABS_LEMMA1 : thm
  REAL_ABS_TRIANGLE_LEMMA : thm
  REAL_MONO_POW2 : thm
  REAL_LE_SUC_POW2 : thm
  REAL_OPPSIGN_LEMMA : thm
  REAL_OPPSIGN : thm
  REAL_NDIV_LEMMA1a : thm
  REAL_NDIV_LEMMA1b : thm
  REAL_NDIV_LEMMA2 : thm
  REAL_NDIV_LEMMA3 : thm
  deriving Inhabited

@[nospecialize]
def setupLemmas [HolBase] (D : CalcRealDeps) :
    ExceptT String IO Lemmas := do
  -- @@SCOPE BEGIN
  let { INDUCT_TAC, REAL_ARITH, REAL_ARITH_TAC, .. } := D
  let { ADD1, ADD_CLAUSES, LE_EXISTS, LT_CASES, LT_EXISTS, REAL_ABS_MUL, REAL_ABS_NEG,
        REAL_ABS_NUM, REAL_ABS_POW, REAL_ADD_AC, REAL_ADD_ASSOC, REAL_ADD_LDISTRIB,
        REAL_ADD_RDISTRIB, .. } := D.core1
  let { REAL_LE_ADD, REAL_LE_ADDL, REAL_LE_ADDR, REAL_LE_LADD, REAL_LE_LMUL,
        REAL_LE_MUL, REAL_LE_POW2, REAL_LE_REFL, REAL_LE_TRANS, REAL_LTE_TRANS,
        REAL_LT_ADDL, REAL_LT_ADDR, REAL_LT_IMP_LE, REAL_LT_MUL, REAL_LT_NEGTOTAL,
        REAL_LT_POW2, REAL_LT_REFL, REAL_MUL_2, REAL_MUL_ASSOC, REAL_MUL_LNEG,
        REAL_MUL_LZERO, REAL_MUL_RID, REAL_MUL_RNEG, REAL_MUL_RZERO, REAL_NEG_ADD,
        REAL_NEG_NEG, REAL_NOT_LE, .. } := D.core2
  let { REAL_NOT_LT, REAL_OF_NUM_ADD, REAL_OF_NUM_POW, REAL_POS, REAL_POW_ADD,
        REAL_POW_LE, REAL_SUB_LDISTRIB, real_abs, real_pow, real_sub, sum, .. } := D.core3
  -- @@SCOPE END

  let REAL_SUB_SUM0 ← prove
   r"!x y m. sum(0,m) x - sum(0,m) y = sum(0,m) (\i. x i - y i)"
   (CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
    GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [sum] THEN
    REAL_ARITH_TAC)

  let REAL_MUL_RSUM0 ← prove
   r"!m c x. c * sum(0,m) x = sum(0,m) (\i. c * x(i))"
   (INDUCT_TAC THEN
    ASM_REWRITE_TAC [sum, REAL_MUL_RZERO, REAL_ADD_LDISTRIB])

  let REAL_ABS_LEMMA ← prove
   r"!a b n. (&a pow n) * abs b = abs((&a pow n) * b)"
   (REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_POW, REAL_ABS_NUM])

  let REAL_ABS_LEMMA1 ← prove
   r"!a b. &a * abs b = abs(&a * b)"
   (REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_NUM])

  let REAL_ABS_TRIANGLE_LEMMA ← prove
   r"!u x y z. abs(x - y) + abs(z - x) < u ==> abs(z - y) < u"
   (REAL_ARITH_TAC)

  let REAL_MONO_POW2 ← prove
   r"!m n. m <= n ==> &2 pow m <= &2 pow n"
   (REPEAT GEN_TAC THEN REWRITE_TAC [LE_EXISTS] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "d:num") SUBST1_TAC) THEN
    SPEC_TAC (← q "d:num", ← q "d:num") THEN INDUCT_TAC THEN
    REWRITE_TAC [ADD_CLAUSES, real_pow, REAL_LE_REFL] THEN
    POP_ASSUM MP_TAC THEN MP_TAC (← SPEC (← q "m:num") REAL_LT_POW2) THEN
    REAL_ARITH_TAC)

  let REAL_LE_SUC_POW2 ← prove
   r"!m. &2 pow m + &1 <= &2 pow (SUC m)"
   (GEN_TAC THEN REWRITE_TAC [real_pow, REAL_MUL_2, REAL_LE_LADD, REAL_LE_POW2])

  let REAL_OPPSIGN_LEMMA ← prove
   r"!x y. (x * y < &0) <=> (x < &0 /\ &0 < y) \/ (&0 < x /\ y < &0)"
   (REPEAT GEN_TAC THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (← SPEC (← q "x:real") REAL_LT_NEGTOTAL) THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (← SPEC (← q "y:real") REAL_LT_NEGTOTAL) THEN
    ASM_REWRITE_TAC [REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_LT_REFL] THEN
    POP_ASSUM_LIST (MP_TAC o end_itlist CONJ) THEN
    DISCH_THEN (fun th => tactic_of do
      pure (MP_TAC (← MATCH_MP REAL_LT_MUL th) THEN MP_TAC th)) THEN
    REWRITE_TAC [REAL_MUL_LNEG, REAL_MUL_RNEG, REAL_NEG_NEG] THEN
    REAL_ARITH_TAC)

  let REAL_OPPSIGN ← prove
   r"(&0 < x ==> &0 <= y) /\ (x < &0 ==> y <= &0) <=> &0 <= x * y"
   (REWRITE_TAC [← GSYM REAL_NOT_LT, REAL_OPPSIGN_LEMMA] THEN
    REAL_ARITH_TAC)

  let REAL_NDIV_LEMMA1a ← prove
   r"!a m n. &2 * abs(&2 pow m * &a - &2 pow (m + n)) <= &2 pow m
             ==> (&a = &2 pow n)"
   (← do
    let a1 ← REAL_ARITH (← q r"((a + b) - a = b) /\ (a - (a + b) = --b)")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [REAL_POW_ADD, ← GSYM REAL_SUB_LDISTRIB] THEN
    REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_POW, REAL_ABS_NUM] THEN
    REWRITE_TAC [REAL_OF_NUM_POW] THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
      (← SPECL [← q "a:num", ← q "2 EXP n"] LT_CASES) THEN
    ASM_REWRITE_TAC [] THEN
    CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN (K ALL_TAC) THEN
    POP_ASSUM (fun th => tactic_of do
      pure (X_CHOOSE_THEN (← q "d:num") SUBST1_TAC (← REWRITE_RULE [LT_EXISTS] th))) THEN
    REWRITE_TAC [← GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC [a1] THEN
    REWRITE_TAC [REAL_ABS_NEG, REAL_NOT_LE, REAL_ABS_NUM] THEN
    REWRITE_TAC [ADD1, ← GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC [REAL_MUL_2, REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB] THEN
    REWRITE_TAC [REAL_MUL_RID, REAL_ADD_ASSOC, REAL_LT_ADDL] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q "&(2 EXP m)") THEN
    REWRITE_TAC [REAL_LT_POW2, ← GSYM REAL_OF_NUM_POW] THEN
    ONCE_REWRITE_TAC [← AC REAL_ADD_AC (← q r"(a + b) + c = b + (a + c)")] THEN
    REWRITE_TAC [← GSYM REAL_MUL_2, REAL_LE_ADDR] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC [REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC [REAL_POS] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC [REAL_LT_POW2]))

  let REAL_NDIV_LEMMA1b ← prove
   r"!a m n. ~(&2 * abs(-- (&2 pow m * &a) - &2 pow (m + n)) <= &2 pow m)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [real_sub, ← GSYM REAL_NEG_ADD] THEN
    REWRITE_TAC [REAL_ABS_NEG, REAL_POW_ADD] THEN
    REWRITE_TAC [REAL_ABS_MUL, ← GSYM REAL_ADD_LDISTRIB] THEN
    SUBGOAL_THEN (← q r"&0 <= &a + &2 pow n") ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC [REAL_POS] THEN
      MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC [REAL_POS],
      REWRITE_TAC [REAL_ABS_POW, REAL_ABS_NUM] THEN
      ASM_REWRITE_TAC [real_abs, REAL_NOT_LE] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC (← q r"(&2 * &2 pow m) * &1") THEN CONJ_TAC THENL
       [REWRITE_TAC [REAL_MUL_RID, REAL_MUL_2] THEN
        REWRITE_TAC [REAL_LT_ADDR, REAL_LT_POW2],
        REWRITE_TAC [REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC [REAL_POS] THEN
          MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC [REAL_POS],
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "&2 pow n") THEN
          REWRITE_TAC [REAL_LE_POW2, REAL_LE_ADDL, REAL_POS]]]])

  let REAL_NDIV_LEMMA2 ← prove
   r"!a b m n. (?k. (b = &k) \/ (b = --(&k))) /\
               (abs(a) = &2 pow m) /\
               &2 * abs(a * b - &2 pow (m + n)) <= abs(a)
               ==> (a * b = &2 pow (m + n))"
   (← do
    let a1 ← REAL_ARITH (← q r"(a = abs a) \/ (a = --(abs a))")
    pure (REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISJ_CASES_THEN SUBST1_TAC a1 THEN
    ASM_REWRITE_TAC [REAL_MUL_LNEG, REAL_MUL_RNEG] THEN
    REWRITE_TAC [REAL_ABS_NEG, REAL_ABS_POW, REAL_ABS_NUM, REAL_NEG_NEG] THEN
    REWRITE_TAC [REAL_NDIV_LEMMA1b] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (SUBST1_TAC (← MATCH_MP REAL_NDIV_LEMMA1a th))) THEN
    REWRITE_TAC [REAL_POW_ADD]))

  let REAL_NDIV_LEMMA3 ← prove
   r"!a b m n. m <= n /\
               (?k. (b = &k) \/ (b = --(&k))) /\
               (abs(a) = &2 pow m) /\
               &2 * abs(a * b - &2 pow n) <= abs(a)
               ==> (a * b = &2 pow n)"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    POP_ASSUM (fun th => tactic_of do
      pure (CHOOSE_THEN SUBST1_TAC (← REWRITE_RULE [LE_EXISTS] th))) THEN
    REWRITE_TAC [REAL_NDIV_LEMMA2])

  -- @@RETURN BEGIN
  return { REAL_SUB_SUM0, REAL_MUL_RSUM0, REAL_ABS_LEMMA, REAL_ABS_LEMMA1,
           REAL_ABS_TRIANGLE_LEMMA, REAL_MONO_POW2, REAL_LE_SUC_POW2, REAL_OPPSIGN_LEMMA,
           REAL_OPPSIGN, REAL_NDIV_LEMMA1a, REAL_NDIV_LEMMA1b, REAL_NDIV_LEMMA2,
           REAL_NDIV_LEMMA3 }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Surely there is already an efficient way to do this...  (calc_real.ml 135) -/
/- ------------------------------------------------------------------------- -/

/-- `log2`'s inner recursion (calc_real.ml 136-138). -/
partial def log2Aux (x y : Rat) : Rat :=
  if x < num_1 then y else log2Aux (quo_num x num_2) (y + num_1)

/-- `log2 x`: least `p >= 0` with `x <= 2^p` (calc_real.ml 135-139). -/
def log2 (x : Rat) : Rat := log2Aux (x - num_1) num_0

/- ------------------------------------------------------------------------- -/
/- Theorems justifying the steps.  (calc_real.ml 145-189)                    -/
/- ------------------------------------------------------------------------- -/

structure StepsDown where
  -- @@FIELDS
  REALCALC_DOWNGRADE : thm
  REALCALC_INT : thm
  REALCALC_NEG : thm
  REALCALC_ABS : thm
  deriving Inhabited

@[nospecialize]
def setupStepsDown [HolBase] (D : CalcRealDeps) (BLemmas : Lemmas) :
    ExceptT String IO StepsDown := do
  -- @@SCOPE BEGIN
  let { INDUCT_TAC, REAL_ARITH_TAC, .. } := D
  let { ADD_SYM, REAL_ABS_0, REAL_ABS_NEG, REAL_ABS_SUB_ABS, .. } := D.core1
  let { REAL_LET_TRANS, REAL_LE_ADD2, REAL_LE_REFL, REAL_LE_TRANS, REAL_LTE_ADD2,
        REAL_LTE_TRANS, REAL_LT_01, REAL_LT_LCANCEL_IMP, REAL_MUL_2, REAL_MUL_ASSOC,
        REAL_MUL_RID, REAL_MUL_RNEG, REAL_NEG_ADD, .. } := D.core2
  let { REAL_POW_ADD, REAL_POW_LT, REAL_SUB_LDISTRIB, REAL_SUB_REFL, real_pow,
        real_sub, .. } := D.core3
  let { REAL_ABS_LEMMA, REAL_ABS_TRIANGLE_LEMMA, .. } := BLemmas
  -- @@SCOPE END

  let REALCALC_DOWNGRADE ← prove
   r"(SUC d0 = d) ==>
     (n + d = n0) ==>
     abs(a - &2 pow n0 * x) < &1 ==>
     abs((&2 pow d) * b - a) <= &2 pow d0 ==>
     abs(b - &2 pow n * x) < &1"
   (DISCH_THEN (SUBST1_TAC o SYM) THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    REPEAT DISCH_TAC THEN
    MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC (← q "&2 pow (SUC d0)") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC,
      REWRITE_TAC [REAL_ABS_LEMMA, REAL_MUL_RID, REAL_SUB_LDISTRIB] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q "&2 pow d0 + &2 pow d0") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_ABS_TRIANGLE_LEMMA THEN EXISTS_TAC (← q "a:real") THEN
        MATCH_MP_TAC REAL_LTE_ADD2 THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q "&1") THEN
        REWRITE_TAC [REAL_MUL_ASSOC, ← GSYM REAL_POW_ADD] THEN
        ONCE_REWRITE_TAC [ADD_SYM] THEN ASM_REWRITE_TAC [] THEN
        SPEC_TAC (← q "d0:num", ← q "d0:num") THEN INDUCT_TAC THEN
        REWRITE_TAC [real_pow, REAL_LE_REFL] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "&1 + &1") THEN
        REWRITE_TAC [REAL_MUL_2] THEN CONJ_TAC THENL
         [REAL_ARITH_TAC,
          MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC []],
        REWRITE_TAC [real_pow, ← GSYM REAL_MUL_2, REAL_LE_REFL]]])

  let REALCALC_INT ← prove
   r"abs((&2 pow n) * a - (&2 pow n) * a) < &1"
   (REWRITE_TAC [REAL_SUB_REFL, REAL_ABS_0, REAL_LT_01])

  let REALCALC_NEG ← prove
   r"abs(a - (&2 pow n) * x) < &1
     ==> abs(--a - (&2 pow n) * --x) < &1"
   (REWRITE_TAC [real_sub, ← GSYM REAL_NEG_ADD] THEN
    REWRITE_TAC [REAL_ABS_NEG, REAL_MUL_RNEG])

  let REALCALC_ABS ← prove
   r"abs(a - &2 pow n * x) < &1
     ==> abs(abs(a) - &2 pow n * abs(x)) < &1"
   (DISCH_TAC THEN REWRITE_TAC [REAL_ABS_LEMMA] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC (← q "abs(a - (&2 pow n) * x)") THEN
    ASM_REWRITE_TAC [REAL_ABS_SUB_ABS])

  -- @@RETURN BEGIN
  return { REALCALC_DOWNGRADE, REALCALC_INT, REALCALC_NEG, REALCALC_ABS }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Theorems justifying the steps, continued.  (calc_real.ml 191-430)         -/
/- ------------------------------------------------------------------------- -/

structure StepsInv where
  -- @@FIELDS
  REALCALC_INV_LEMMA : thm
  REALCALC_INV : thm
  deriving Inhabited

@[nospecialize]
def setupStepsInv [HolBase] (D : CalcRealDeps) (BLemmas : Lemmas) :
    ExceptT String IO StepsInv := do
  -- @@SCOPE BEGIN
  let { INDUCT_TAC, REAL_ARITH, REAL_ARITH_TAC, .. } := D
  let { ADD1, ADD_CLAUSES, ADD_SYM, ARITH_SUC, EXISTS_REFL, LE, LET_CASES, LE_LT,
        LE_SUC_LT, MULT_2, MULT_CLAUSES, NOT_LT, NOT_SUC, REAL_ABS_0, REAL_ABS_MUL,
        REAL_ABS_NEG, REAL_ABS_NUM, REAL_ABS_NZ, REAL_ABS_POS, REAL_ABS_POW,
        REAL_ABS_SUB, REAL_ABS_SUB_ABS, REAL_ENTIRE, .. } := D.core1
  let { REAL_INV_EQ_0, REAL_LET_TRANS, REAL_LE_ADDR, REAL_LE_LCANCEL_IMP, REAL_LE_LMUL,
        REAL_LE_MUL, REAL_LE_MUL2, REAL_LE_POW2, REAL_LE_RCANCEL_IMP, REAL_LE_SUB_LADD,
        REAL_LE_SUB_RADD, REAL_LE_TRANS, REAL_LTE_TRANS, REAL_LT_IMP_LE,
        REAL_LT_IMP_NZ, REAL_LT_LCANCEL_IMP, REAL_LT_LMUL, REAL_LT_MUL, REAL_LT_POW2,
        REAL_LT_RCANCEL_IMP, REAL_LT_SQUARE, REAL_LT_SUB_RADD, REAL_MUL_AC,
        REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_RID, REAL_MUL_RINV,
        REAL_MUL_RZERO, REAL_MUL_SYM, .. } := D.core2
  let { REAL_NOT_LT, REAL_OF_NUM_ADD, REAL_OF_NUM_EQ, REAL_OF_NUM_LE, REAL_OF_NUM_LT,
        REAL_OF_NUM_POW, REAL_POS, REAL_POW_ADD, REAL_POW_EQ_0, REAL_SUB_LDISTRIB,
        REAL_SUB_RDISTRIB, REAL_SUB_RZERO, SUC_INJ, real_pow, .. } := D.core3
  let { REAL_ABS_LEMMA, REAL_LE_SUC_POW2, REAL_MONO_POW2, REAL_NDIV_LEMMA3,
        REAL_OPPSIGN, .. } := BLemmas
  -- @@SCOPE END

  let REALCALC_INV_LEMMA ← prove
   r"(?m. (b = &m) \/ (b = --(&m))) /\
   (?m. (a = &m) \/ (a = --(&m))) /\
   SUC(n + k) <= (2 * e) /\
   &2 pow e <= abs(a) /\
   abs(a - &2 pow k * x) < &1 /\
   &2 * abs(a * b - &2 pow (n + k)) <= abs(a)
   ==> abs(b - &2 pow n * inv(x)) < &1"
   (← do
    let lemma1 ← REAL_ARITH
     (← q r"!x y z b. &2 * abs(x - y) <= b /\ &2 * abs(y - z) < b
              ==> &2 * abs(x - z) < &2 * b")
    let lemma2 ← REAL_ARITH
     (← q r"!x y z. x + &1 <= abs(z) /\ abs(z - y) < &1 ==> x <= abs(y)")
    let lemma3 ← REAL_ARITH
     (← q r"(abs(x) <= &1 /\ &0 < abs(y) /\ abs(y) < &1) /\
     (&0 < x ==> &0 <= y) /\ (x < &0 ==> y <= &0)
      ==> abs(x - y) < &1")
    let lemma4 ← REAL_ARITH
     (← q r"!a b c. c <= abs(a) + abs(b) /\ abs(a - b) < c ==>
             (&0 < a ==> &0 <= b) /\ (a < &0 ==> b <= &0)")
    let a1 ← REAL_ARITH (← q r"(--x = &0) = (x = &0)")
    pure (DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"~(a = &0)") ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"&2 pow e <= abs(&0)") THEN
      REWRITE_TAC [REAL_ABS_0, ← GSYM REAL_NOT_LT, REAL_LT_POW2], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"~(x = &0)") ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC (← q r"abs(a - &2 pow k * &0) < &1") THEN
      REWRITE_TAC [REAL_MUL_RZERO, REAL_SUB_RZERO, REAL_NOT_LT] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "&2 pow e") THEN
      ASM_REWRITE_TAC [REAL_LE_POW2], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(&2 pow e + &1 <= abs(a)) \/ (&2 pow e = abs(a))") MP_TAC THENL
     [REWRITE_TAC [REAL_OF_NUM_POW] THEN
      FIRST_ASSUM (CHOOSE_THEN (DISJ_CASES_THEN SUBST_ALL_TAC)) THEN
      REWRITE_TAC [REAL_ABS_NEG, REAL_ABS_NUM] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [REAL_ABS_NEG, REAL_ABS_NUM]) THEN
      REWRITE_TAC [REAL_OF_NUM_ADD, REAL_OF_NUM_LE, REAL_OF_NUM_EQ] THEN
      REWRITE_TAC [← GSYM ADD1, LE_SUC_LT, ← GSYM LE_LT] THEN
      ASM_REWRITE_TAC [← GSYM REAL_OF_NUM_LE, ← GSYM REAL_OF_NUM_POW],
      UNDISCH_TAC (← q r"&2 pow e <= abs(a)") THEN DISCH_THEN (K ALL_TAC)] THEN
    DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL
     [DISCH_TAC THEN MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
      EXISTS_TAC (← q "&2 * abs(a)") THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN
        ASM_REWRITE_TAC [← GSYM REAL_ABS_NZ] THEN REAL_ARITH_TAC,
        REWRITE_TAC [← GSYM REAL_MUL_ASSOC, ← GSYM REAL_ABS_MUL] THEN
        REWRITE_TAC [REAL_SUB_LDISTRIB, REAL_MUL_RID] THEN
        MATCH_MP_TAC lemma1 THEN EXISTS_TAC (← q "&2 pow (n + k)") THEN
        ASM_REWRITE_TAC []] THEN
      GEN_REWRITE_TAC (LAND_CONV o funpow 3 RAND_CONV) [REAL_MUL_SYM] THEN
      REWRITE_TAC [REAL_POW_ADD, ← GSYM REAL_MUL_ASSOC] THEN
      REWRITE_TAC [← GSYM REAL_SUB_LDISTRIB, REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN
      EXISTS_TAC (← q "abs(x)") THEN ASM_REWRITE_TAC [← GSYM REAL_ABS_NZ] THEN
      REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN
      ONCE_REWRITE_TAC [← GSYM REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC (← q "&2 * abs(&2 pow n) * &1") THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_LMUL THEN
        CONJ_TAC THENL [REAL_ARITH_TAC, ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
         [REWRITE_TAC [← GSYM REAL_ABS_NZ, REAL_POW_EQ_0] THEN
          CONV_TAC (RAND_CONV (LAND_CONV D.REAL_INT_EQ_CONV)) THEN REWRITE_TAC [],
          REWRITE_TAC [REAL_SUB_RDISTRIB] THEN
          ONCE_REWRITE_TAC [REAL_ABS_SUB] THEN
          GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
          REWRITE_TAC [REAL_MUL_ASSOC] THEN
          FIRST_ASSUM (fun th => tactic_of do
            pure (REWRITE_TAC [← MATCH_MP REAL_MUL_RINV th])) THEN
          ASM_REWRITE_TAC [REAL_MUL_LID]],
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC (← q "&2 pow k") THEN
      REWRITE_TAC [REAL_LT_POW2, REAL_MUL_RID, REAL_ABS_LEMMA] THEN
      ONCE_REWRITE_TAC [← AC REAL_MUL_AC (← q r"a * b * c = (a * c) * b")] THEN
      REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_POW, REAL_ABS_NUM] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q "&2 pow e * &2 pow e") THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC [← AC REAL_MUL_AC (← q r"(a * b) * c = c * b * a")] THEN
        REWRITE_TAC [← GSYM REAL_POW_ADD, ← GSYM (← CONJUNCT2 real_pow)] THEN
        MATCH_MP_TAC REAL_MONO_POW2 THEN ASM_REWRITE_TAC [← GSYM MULT_2],
        MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC [REAL_LT_POW2],
          REWRITE_TAC [REAL_ABS_LEMMA] THEN MATCH_MP_TAC lemma2 THEN
          EXISTS_TAC (← q "a:real") THEN ASM_REWRITE_TAC [],
          MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC [REAL_LT_POW2],
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "&2 pow e + &1") THEN
          ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC]],

      DISCH_TAC THEN
      DISJ_CASES_TAC (← SPECL [← q "e:num", ← q "n + k:num"] LET_CASES) THENL
       [SUBGOAL_THEN (← q r"a * b = &2 pow (n + k)") ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_NDIV_LEMMA3 THEN
          EXISTS_TAC (← q "e:num") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC (← q "abs(a)") THEN
        ASM_REWRITE_TAC [← GSYM REAL_ABS_NZ, ← GSYM REAL_ABS_MUL] THEN
        ASM_REWRITE_TAC [REAL_SUB_LDISTRIB] THEN
        ONCE_REWRITE_TAC [← AC REAL_MUL_AC (← q r"a * b * c = b * a * c")] THEN
        REWRITE_TAC [REAL_POW_ADD, ← GSYM REAL_SUB_LDISTRIB] THEN
        REWRITE_TAC [REAL_ABS_MUL, REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN EXISTS_TAC (← q "abs(x)") THEN
        ASM_REWRITE_TAC [← GSYM REAL_ABS_NZ, ← GSYM REAL_MUL_ASSOC] THEN
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← GSYM REAL_ABS_MUL] THEN
        REWRITE_TAC [REAL_SUB_RDISTRIB, ← GSYM REAL_MUL_ASSOC] THEN
        REWRITE_TAC [← MATCH_MP REAL_MUL_LINV (← ASSUME (← q r"~(x = &0)"))] THEN
        ONCE_REWRITE_TAC [REAL_ABS_SUB] THEN
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q "&2 pow n * &1") THEN
        CONJ_TAC THENL
         [REWRITE_TAC [REAL_ABS_POW, REAL_ABS_NUM] THEN
          MATCH_MP_TAC REAL_LT_LMUL THEN
          ASM_REWRITE_TAC [REAL_LT_POW2, REAL_MUL_RID],
          MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC (← q "&2 pow (SUC k)") THEN
          REWRITE_TAC [REAL_MUL_RID, REAL_LT_POW2]] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC (← q "&2 pow (2 * e)") THEN CONJ_TAC THENL
         [REWRITE_TAC [← GSYM REAL_POW_ADD, ADD_CLAUSES] THEN
          MATCH_MP_TAC REAL_MONO_POW2 THEN ASM_REWRITE_TAC [],
          SUBST1_TAC (← SYM (← ASSUME (← q r"&2 pow e = abs(a)"))) THEN
          REWRITE_TAC [MULT_2, REAL_POW_ADD, ← GSYM REAL_MUL_ASSOC] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN
          REWRITE_TAC [← MATCH_MP REAL_LT_IMP_LE (← SPEC_ALL REAL_LT_POW2)]] THEN
        ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REWRITE_TAC [real_pow] THEN
        SUBGOAL_THEN (← q r"?d. e = SUC d") (CHOOSE_THEN SUBST_ALL_TAC) THENL
         [UNDISCH_TAC (← q r"SUC (n + k) <= (2 * e)") THEN
          SPEC_TAC (← q "e:num", ← q "e:num") THEN INDUCT_TAC THEN
          REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES, LE, NOT_SUC] THEN
          REWRITE_TAC [SUC_INJ, ← GSYM EXISTS_REFL],
          REWRITE_TAC [real_pow, ← GSYM REAL_MUL_ASSOC] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [REAL_POS] THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC (← q "&2 pow (SUC d) - &1") THEN
          REWRITE_TAC [REAL_LE_SUB_RADD, REAL_LE_SUB_LADD] THEN
          REWRITE_TAC [REAL_LE_SUC_POW2] THEN
          SUBGOAL_THEN (← q r"abs(abs a - &2 pow k * abs(x)) < &1") MP_TAC THENL
           [REWRITE_TAC [REAL_ABS_LEMMA] THEN
            MATCH_MP_TAC (← D.REAL_LET_IMP REAL_ABS_SUB_ABS) THEN
            ASM_REWRITE_TAC [],
            ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC]],

        SUBGOAL_THEN (← q r"abs(b) <= &1 /\ &0 <= a * b") STRIP_ASSUME_TAC THENL
         [ASM_CASES_TAC (← q r"b = &0") THEN
          ASM_REWRITE_TAC [REAL_ABS_0, REAL_MUL_RZERO, REAL_POS] THEN
          SUBGOAL_THEN (← q r"abs(a) <= abs(a * b)") ASSUME_TAC THENL
           [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← GSYM REAL_MUL_RID] THEN
            REWRITE_TAC [REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
            REWRITE_TAC [REAL_ABS_POS] THEN
            SUBGOAL_THEN (← q r"?q. abs(b) = &q") CHOOSE_TAC THENL
             [UNDISCH_TAC (← q r"?m. (b = &m) \/ (b = --(&m))") THEN
              DISCH_THEN (X_CHOOSE_THEN (← q "p:num") DISJ_CASES_TAC) THEN
              EXISTS_TAC (← q "p:num") THEN
              ASM_REWRITE_TAC [REAL_ABS_NEG, REAL_ABS_NUM],
              UNDISCH_TAC (← q r"~(b = &0)") THEN ASM_REWRITE_TAC [REAL_ABS_NZ] THEN
              REWRITE_TAC [REAL_ABS_NUM, REAL_OF_NUM_LE, REAL_OF_NUM_LT] THEN
              REWRITE_TAC [← SYM (← REWRITE_CONV [ARITH_SUC] (← q "SUC 0"))] THEN
              REWRITE_TAC [LE_SUC_LT]],
            ALL_TAC] THEN
          SUBGOAL_THEN (← q r"abs(a * b) <= abs(a) /\ &0 <= a * b") ASSUME_TAC THENL
           [MP_TAC (← SPEC (← q "(n:num) + k") REAL_LT_POW2) THEN
            UNDISCH_TAC (← q r"&2 * abs(a * b - &2 pow (n + k)) <= abs a") THEN
            UNDISCH_TAC (← q r"abs(a) <= abs(a * b)") THEN
            SUBGOAL_THEN (← q r"~(a * b = &0)") MP_TAC THENL
             [ASM_REWRITE_TAC [REAL_ENTIRE], ALL_TAC] THEN
            SUBGOAL_THEN (← q r"&2 * &2 pow (n + k) <= abs(a)") MP_TAC THENL
             [REWRITE_TAC [← GSYM (← CONJUNCT2 real_pow)] THEN
              FIRST_ASSUM (fun th => tactic_of do
                pure (GEN_REWRITE_TAC RAND_CONV [← SYM th])) THEN
              MATCH_MP_TAC REAL_MONO_POW2 THEN ASM_REWRITE_TAC [LE_SUC_LT],
              REAL_ARITH_TAC],
            ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
            EXISTS_TAC (← q "abs(a)") THEN ASM_REWRITE_TAC
              [← GSYM REAL_ABS_NZ, ← GSYM REAL_ABS_MUL, REAL_MUL_RID]],
          ALL_TAC] THEN
        MATCH_MP_TAC lemma3 THEN CONJ_TAC THENL
         [ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
           [ASM_REWRITE_TAC [← GSYM REAL_ABS_NZ, REAL_ENTIRE, REAL_INV_EQ_0] THEN
            MATCH_MP_TAC REAL_LT_IMP_NZ THEN REWRITE_TAC [REAL_LT_POW2],
            MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC (← q "abs(x)") THEN
            ASM_REWRITE_TAC [← GSYM REAL_ABS_NZ, ← GSYM REAL_ABS_MUL] THEN
            ONCE_REWRITE_TAC [← AC REAL_MUL_AC (← q r"a * b * c = b * c * a")] THEN
            SUBGOAL_THEN (← q r"inv(x) * x = &1") SUBST1_TAC THENL
             [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC [],
              REWRITE_TAC [REAL_MUL_RID] THEN
              MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC (← q "&2 pow k") THEN
              REWRITE_TAC [REAL_LT_POW2, REAL_ABS_LEMMA] THEN
              MATCH_MP_TAC REAL_LET_TRANS THEN
              EXISTS_TAC (← q "&2 pow (SUC(n + k)) - &1") THEN
              REWRITE_TAC [REAL_LT_SUB_RADD, REAL_LE_SUB_LADD] THEN
              ONCE_REWRITE_TAC [ADD_SYM] THEN
              REWRITE_TAC [← GSYM REAL_POW_ADD] THEN
              ONCE_REWRITE_TAC [ADD_SYM] THEN
              REWRITE_TAC [REAL_LE_SUC_POW2, REAL_ABS_POW, REAL_ABS_NUM] THEN
              MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q "&2 pow e") THEN
              CONJ_TAC THENL
               [MATCH_MP_TAC REAL_MONO_POW2 THEN
                ASM_REWRITE_TAC [LE_SUC_LT],
                UNDISCH_TAC (← q r"abs(a - &2 pow k * x) < &1") THEN
                ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC]]],
          SUBGOAL_THEN (← q r"&0 <= b * (&2 pow n * inv x)") MP_TAC THENL
           [MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
            EXISTS_TAC (← q "a * a") THEN ASM_REWRITE_TAC [REAL_LT_SQUARE] THEN
            REWRITE_TAC [REAL_MUL_RZERO] THEN
            ONCE_REWRITE_TAC [← AC REAL_MUL_AC
              (← q r"(a * b) * c * d = (a * c) * (b * d)")] THEN
            MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC [] THEN
            MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
            EXISTS_TAC (← q "x * x") THEN ASM_REWRITE_TAC [REAL_LT_SQUARE] THEN
            REWRITE_TAC [REAL_MUL_RZERO] THEN
            ONCE_REWRITE_TAC [← AC REAL_MUL_AC
             (← q r"(a * b) * c * d * e = d * (e * a) * c * b")] THEN
            MATCH_MP_TAC REAL_LE_MUL THEN
            REWRITE_TAC [← MATCH_MP REAL_LT_IMP_LE (← SPEC_ALL REAL_LT_POW2)] THEN
            FIRST_ASSUM (fun th => tactic_of do
              pure (GEN_REWRITE_TAC (RAND_CONV o LAND_CONV)
                [← MATCH_MP REAL_MUL_LINV th])) THEN
            MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC (← q "&2 pow k") THEN
            REWRITE_TAC [REAL_LT_POW2, REAL_MUL_RZERO, REAL_MUL_LID] THEN
            ONCE_REWRITE_TAC [← AC REAL_MUL_AC (← q r"a * b * c = b * (a * c)")] THEN
            ONCE_REWRITE_TAC [← GSYM REAL_OPPSIGN] THEN
            MATCH_MP_TAC lemma4 THEN EXISTS_TAC (← q "&1") THEN
            ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
            EXISTS_TAC (← q "abs(a)") THEN CONJ_TAC THENL
             [UNDISCH_TAC (← q r"?m. (a = &m) \/ (a = -- (&m))") THEN
              DISCH_THEN (CHOOSE_THEN (DISJ_CASES_THEN SUBST_ALL_TAC)) THEN
              ASM_REWRITE_TAC [REAL_ABS_NEG, REAL_ABS_NUM] THEN
              REWRITE_TAC [REAL_OF_NUM_LE] THEN
              REWRITE_TAC [← SYM (← REWRITE_CONV [ARITH_SUC] (← q "SUC 0"))] THEN
              REWRITE_TAC [LE_SUC_LT] THEN RULE_ASSUM_TAC
               (REWRITE_RULE [a1]) THEN
              UNDISCH_TAC (← q r"~(&m = &0)") THEN REWRITE_TAC [REAL_OF_NUM_EQ] THEN
              CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC [NOT_LT, LE],
              REWRITE_TAC [REAL_LE_ADDR, REAL_ABS_POS]],
            REWRITE_TAC [REAL_OPPSIGN]]]]]))

  let REALCALC_INV ← prove
   r"abs(a - &2 pow k * x) < &1 ==>
   (?m. (a = &m) \/ (a = --(&m))) ==>
   (?m. (b = &m) \/ (b = --(&m))) ==>
   SUC(n + k) <= (2 * e) ==>
   &2 pow e <= abs(a) ==>
   &2 * abs(a * b - &2 pow (n + k)) <= abs(a)
   ==> abs(b - &2 pow n * inv(x)) < &1"
   (REPEAT DISCH_TAC THEN MATCH_MP_TAC REALCALC_INV_LEMMA THEN
    ASM_REWRITE_TAC [])

  -- @@RETURN BEGIN
  return { REALCALC_INV_LEMMA, REALCALC_INV }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Theorems justifying the steps, continued.  (calc_real.ml 432-501)         -/
/- ------------------------------------------------------------------------- -/

structure StepsAddMul where
  -- @@FIELDS
  REALCALC_ADD : thm
  REALCALC_MUL : thm
  deriving Inhabited

@[nospecialize]
def setupStepsAddMul [HolBase] (D : CalcRealDeps) (BLemmas : Lemmas) :
    ExceptT String IO StepsAddMul := do
  -- @@SCOPE BEGIN
  let { REAL_ARITH, REAL_ARITH_TAC, .. } := D
  let { ADD_SYM, REAL_ABS_MUL, REAL_ABS_POS, REAL_ABS_TRIANGLE, .. } := D.core1
  let { REAL_LET_ADD2, REAL_LET_TRANS, REAL_LE_LMUL, REAL_LTE_ADD2, REAL_LTE_TRANS,
        REAL_LT_ADD2, REAL_LT_IMP_LE, REAL_LT_LCANCEL_IMP, REAL_LT_LMUL, REAL_LT_MUL2,
        REAL_LT_POW2, REAL_MUL_2, REAL_MUL_AC, REAL_MUL_ASSOC, REAL_MUL_RID, .. } := D.core2
  let { REAL_POW_ADD, REAL_SUB_LDISTRIB, .. } := D.core3
  let { REAL_ABS_LEMMA, REAL_ABS_TRIANGLE_LEMMA, .. } := BLemmas
  -- @@SCOPE END

  let REALCALC_ADD ← prove
   r"(n + 2 = n') ==>
   abs(a - &2 pow n' * x) < &1 ==>
   abs(b - &2 pow n' * y) < &1 ==>
   abs(&4 * c - (a + b)) <= &2
   ==> abs(c - &2 pow n * (x + y)) < &1"
   (← do
    let a1 ← REAL_ARITH (← q r"(x + y) - a * (u + v) = (x - a * u) + (y - a * v)")
    pure (DISCH_THEN (SUBST_ALL_TAC o SYM) THEN REPEAT DISCH_TAC THEN
    MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
    EXISTS_TAC (← q "&2 pow 2") THEN
    CONV_TAC (LAND_CONV D.REAL_INT_REDUCE_CONV) THEN
    REWRITE_TAC [REAL_ABS_LEMMA, REAL_SUB_LDISTRIB, REAL_MUL_RID] THEN
    REWRITE_TAC [REAL_MUL_ASSOC, ← GSYM REAL_POW_ADD] THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN
    SUBST1_TAC (← D.REAL_INT_REDUCE_CONV (← q "&2 pow 2")) THEN
    MATCH_MP_TAC REAL_ABS_TRIANGLE_LEMMA THEN
    EXISTS_TAC (← q "a + b") THEN
    GEN_REWRITE_TAC RAND_CONV [← SYM (← D.REAL_INT_REDUCE_CONV (← q "&2 + &2"))] THEN
    MATCH_MP_TAC REAL_LTE_ADD2 THEN ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC
     [a1] THEN
    GEN_REWRITE_TAC RAND_CONV [← SYM (← D.REAL_INT_REDUCE_CONV (← q "&1 + &1"))] THEN
    MATCH_MP_TAC (← D.REAL_LET_IMP REAL_ABS_TRIANGLE) THEN
    MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC []))

  let REALCALC_MUL ← prove
   r"abs(a - &2 pow k * x) < &1 ==>
   abs(b - &2 pow l * y) < &1 ==>
   (n + m = k + l) ==>
   &2 * (abs(a) + abs(b) + &1) <= &2 pow m ==>
   &2 * abs(&2 pow m * c - a * b) <= &2 pow m
   ==> abs(c - &2 pow n * (x * y)) < &1"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC (← q "&2 pow m") THEN
    REWRITE_TAC [REAL_LT_POW2, REAL_ABS_LEMMA, REAL_SUB_LDISTRIB] THEN
    MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC (← q "&2") THEN
    CONV_TAC (LAND_CONV (EQT_INTRO o REAL_ARITH)) THEN
    REWRITE_TAC [REAL_MUL_RID] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_2] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC (← q r"&2 * abs(&2 pow m * c - a * b) +
              &2 * abs(a * b - &2 pow m * &2 pow n * x * y)") THEN
    CONV_TAC (LAND_CONV (EQT_INTRO o REAL_ARITH)) THEN REWRITE_TAC [] THEN
    MATCH_MP_TAC REAL_LET_ADD2 THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [REAL_MUL_ASSOC, ← GSYM REAL_POW_ADD] THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [REAL_POW_ADD] THEN
    ONCE_REWRITE_TAC [← AC REAL_MUL_AC (← q r"((a * b) * c) * d = (a * c) * (b * d)")] THEN
    SUBGOAL_THEN (← q r"?d. abs(d) < &1 /\ (&2 pow k * x = a + d)") MP_TAC THENL
     [EXISTS_TAC (← q "&2 pow k * x - a") THEN
      UNDISCH_TAC (← q r"abs(a - &2 pow k * x) < &1") THEN REAL_ARITH_TAC,
      DISCH_THEN (CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))] THEN
    SUBGOAL_THEN (← q r"?e. abs(e) < &1 /\ (&2 pow l * y = b + e)") MP_TAC THENL
     [EXISTS_TAC (← q "&2 pow l * y - b") THEN
      UNDISCH_TAC (← q r"abs(b - &2 pow l * y) < &1") THEN REAL_ARITH_TAC,
      DISCH_THEN (CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC (← q r"&2 * (abs(a) * &1 + abs(b) * &1 + &1 * &1)") THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN
      CONV_TAC (LAND_CONV (EQT_INTRO o REAL_ARITH)) THEN REWRITE_TAC [] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC (← q r"abs(a) * abs(e) + abs(b) * abs(d) + abs(d) * abs(e)") THEN
      CONJ_TAC THENL
       [REWRITE_TAC [← GSYM REAL_ABS_MUL] THEN REAL_ARITH_TAC,
        MATCH_MP_TAC REAL_LET_ADD2 THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [REAL_ABS_POS] THEN
          MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC [],
          MATCH_MP_TAC REAL_LET_ADD2 THEN CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [REAL_ABS_POS] THEN
            MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC [],
            MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REWRITE_TAC [REAL_ABS_POS]]]],
      ASM_REWRITE_TAC [REAL_MUL_RID]])

  -- @@RETURN BEGIN
  return { REALCALC_ADD, REALCALC_MUL }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Square root.  (calc_real.ml 507-544)                                      -/
/- ------------------------------------------------------------------------- -/

structure Sqrt where
  -- @@FIELDS
  REALCALC_SQRT : thm
  deriving Inhabited

@[nospecialize]
def setupSqrt [HolBase] (D : CalcRealDeps) :
    ExceptT String IO Sqrt := do
  -- @@SCOPE BEGIN
  let { REAL_ARITH, .. } := D
  let { ARITH, POW_2, REAL_ABS_MUL, REAL_ABS_NUM, REAL_ABS_POW, .. } := D.core1
  let { REAL_LTE_TRANS, REAL_LT_LCANCEL_IMP, REAL_LT_LMUL, REAL_LT_MUL, REAL_LT_MUL2,
        REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_RID, REAL_MUL_SYM, REAL_NOT_LE, .. } := D.core2
  let { REAL_OF_NUM_LT, REAL_POW_2, REAL_POW_LT, REAL_SUB_LDISTRIB, SQRT_POS_LE,
        SQRT_POS_LT, SQRT_POW2, SQRT_POW_2, .. } := D.core3
  -- @@SCOPE END

  let REALCALC_SQRT ← prove
   r"abs(a - &2 pow n * x) < &1
       ==> &1 <= x
           ==> abs(b pow 2 - &2 pow n * a) <= b
               ==> abs(b - &2 pow n * sqrt(x)) < &1"
   (← do
    let a7 ← REAL_ARITH (← q r"&1 <= x ==> &0 <= x")
    let a6 ← REAL_ARITH (← q r"&1 <= x ==> &0 <= x")
    let a5 ← REAL_ARITH (← q r"a < c ==> a < abs(b + c) - b")
    let a4 ← REAL_ARITH
     (← q r"!c d. abs(b - c) <= d /\ abs(c - a) < e - d
          ==> abs(b - a) < e")
    let a3 ← REAL_ARITH (← q r"(a + b) * (a - b) = a * a - b * b")
    let a2 ← REAL_ARITH (← q r"&1 <= x ==> &0 < x")
    let a1 ← REAL_ARITH
     (← q r"!z. abs(z) <= b /\ &0 < c ==> &0 < abs(b + c)")
    pure (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
    EXISTS_TAC (← q "abs(b + &2 pow n * sqrt(x))") THEN CONJ_TAC THENL
     [MATCH_MP_TAC a1 THEN
      EXISTS_TAC (← q "b pow 2 - &2 pow n * a") THEN ASM_REWRITE_TAC [] THEN
      ASM_SIMP_TAC [REAL_POW_LT, REAL_OF_NUM_LT, ARITH, REAL_LT_MUL,
                   SQRT_POS_LT, a2], ALL_TAC] THEN
    REWRITE_TAC [← GSYM REAL_ABS_MUL, REAL_MUL_RID] THEN
    ONCE_REWRITE_TAC [a3] THEN
    MATCH_MP_TAC a4 THEN
    MAP_EVERY EXISTS_TAC [← q "&2 pow n * a", ← q "b:real"] THEN
    ASM_REWRITE_TAC [← GSYM REAL_POW_2] THEN
    REWRITE_TAC [REAL_POW_2, ← GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC [← GSYM REAL_SUB_LDISTRIB, REAL_ABS_MUL] THEN
    MATCH_MP_TAC a5 THEN
    REWRITE_TAC [REAL_ABS_POW, REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN
    SIMP_TAC [REAL_POW_LT, REAL_OF_NUM_LT, ARITH] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q "&1") THEN
    ASM_SIMP_TAC [← GSYM REAL_MUL_ASSOC, ← GSYM POW_2, SQRT_POW_2, a6] THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (ASSUME_TAC (← MATCH_MP a7 th))) THEN
    UNDISCH_TAC (← q r"&1 <= x") THEN CONV_TAC CONTRAPOS_CONV THEN
    REWRITE_TAC [REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"x = sqrt(x) pow 2") SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC [SQRT_POW2],
      GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_LID] THEN
      REWRITE_TAC [POW_2] THEN MATCH_MP_TAC REAL_LT_MUL2 THEN
      ASM_SIMP_TAC [SQRT_POS_LE]]))

  -- @@RETURN BEGIN
  return { REALCALC_SQRT }
  -- @@RETURN END

/-- `W(C SUBGOAL_THEN ttac o funpow 2 (fst o dest_imp) o snd)`: take the goal's
    conclusion, strip two implications off the front (`fst o dest_imp` twice),
    and `SUBGOAL_THEN` that antecedent. -/
def subgoalImp2 [HolBase] (ttac : thm_tactic) : tactic := fun gl => ExceptT.run do
  let lhandImp (m : Except String term) : Except String term := do
    let (a, _) ← dest_imp (← m)
    pure a
  let t ← liftExcept (funpow 2 lhandImp (pure gl.2))
  ExceptT.mk (SUBGOAL_THEN t ttac gl)

/- ------------------------------------------------------------------------- -/
/- Lemmas common to all the Taylor series error analyses.                    -/
/- ------------------------------------------------------------------------- -/

structure StepLemmas where
  -- @@FIELDS
  STEP_LEMMA1 : thm
  STEP_LEMMA2 : thm
  deriving Inhabited

@[nospecialize]
def setupStepLemmas [HolBase] (D : CalcRealDeps) (BLemmas : Lemmas) :
    ExceptT String IO StepLemmas := do
  -- @@SCOPE BEGIN
  let { REAL_ARITH, REAL_ARITH_TAC, REAL_LE_IMP, .. } := D
  let { CONJ_ASSOC, REAL_ABS_MUL, REAL_ABS_POS, REAL_ABS_TRIANGLE, REAL_ADD_AC,
        REAL_ADD_ASSOC, REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB, REAL_ADD_SYM, .. } := D.core1
  let { REAL_LE_ADD2, REAL_LE_LCANCEL_IMP, REAL_LE_LMUL, REAL_LE_MUL2, REAL_LT_IMP_LE,
        REAL_LT_MUL, REAL_LT_POW2, REAL_MUL_AC, REAL_MUL_ASSOC, REAL_MUL_LINV,
        REAL_MUL_RID, REAL_MUL_SYM, .. } := D.core2
  let { REAL_POW_EQ_0, REAL_SUB_LDISTRIB, real_div, .. } := D.core3
  let { REAL_ABS_LEMMA, REAL_ABS_LEMMA1, .. } := BLemmas
  -- @@SCOPE END

  let STEP_LEMMA1 ← prove
   r"!a b c d x y.
        abs(a - c) <= x /\ abs(b - d) <= y
        ==> abs(a * b - c * d) <= abs(c) * y + abs(d) * x + x * y"
   (← do
    let r1 ← REAL_ARITH (← q r"(c + u) * (d + v) - c * d = c * v + d * u + u * v")
    pure (REPEAT GEN_TAC THEN
    ABBREV_TAC (← q r"u = a - c") THEN ABBREV_TAC (← q r"v = b - d") THEN
    SUBGOAL_THEN (← q r"a = c + u") SUBST1_TAC THENL
     [POP_ASSUM_LIST (MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC, ALL_TAC] THEN
    SUBGOAL_THEN (← q r"b = d + v") SUBST1_TAC THENL
     [POP_ASSUM_LIST (MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC, ALL_TAC] THEN
    STRIP_TAC THEN SUBST1_TAC r1 THEN
    REPEAT (MATCH_MP_TAC (← REAL_LE_IMP REAL_ABS_TRIANGLE) THEN
           MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC) THEN
    REWRITE_TAC [REAL_ABS_MUL] THENL
     [MATCH_MP_TAC REAL_LE_LMUL,
      MATCH_MP_TAC REAL_LE_LMUL,
      MATCH_MP_TAC REAL_LE_MUL2] THEN
    ASM_REWRITE_TAC [REAL_ABS_POS]))

  let STEP_LEMMA2 ← prove
   r"!n s t u x y k l a d.
        &0 < a /\
        &0 < d /\
        abs(s - &2 pow n * x) <= k /\
        abs(t - &2 pow n * y) <= l /\
        &2 * abs(u * &2 pow n * d - a * s * t) <= &2 pow n * d
        ==> abs(u - &2 pow n * (a / d) * (x * y)) <=
            (a / d) * (abs(x) + k / (&2 pow n)) * l +
            ((a / d) * k * abs(y) + &1 / &2)"
   (← do
    let ac4 ← AC REAL_ADD_AC (← q r"(a + b) + c = a + c + b")
    let ac3 ← AC REAL_MUL_AC
      (← q r"a * b * c * d * e * f = c * (a * f) * e * (d * b)")
    let ac2 ← AC REAL_MUL_AC
      (← q r"a * b * c * d * e * f * g = c * (e * g) * (f * a) * (d * b)")
    let ac1 ← AC REAL_MUL_AC
      (← q r"a * b * c * d * e * f = c * (a * e) * f * (d * b)")
    let ac0 ← AC REAL_MUL_AC
      (← q r"a * b * c * d * e * f * g = d * (a * f) * (c * g) * (e * b)")
    let r1 ← REAL_ARITH
      (← q r"abs(a - b) + abs(b - c) <= d ==> abs(a - c) <= d")
    pure (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ONCE_REWRITE_TAC [CONJ_ASSOC] THEN DISCH_THEN
     (CONJUNCTS_THEN2 (ASSUME_TAC o MATCH_MP STEP_LEMMA1) ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"&0 < &2 * &2 pow n * d") ASSUME_TAC THENL
     [REPEAT (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC [REAL_LT_POW2] THEN REAL_ARITH_TAC, ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
    EXISTS_TAC (← q r"&2 * &2 pow n * d") THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [real_div, REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB] THEN
    SUBGOAL_THEN
      (← q r"!z. (&2 * &2 pow n * d) * abs(z) = abs((&2 * &2 pow n * d) * z)")
    (fun th => REWRITE_TAC [th])
    THENL
     [GEN_TAC THEN ONCE_REWRITE_TAC [REAL_ABS_MUL] THEN AP_THM_TAC THEN
      AP_TERM_TAC THEN UNDISCH_TAC (← q r"&0 < &2 * &2 pow n * d") THEN
      REAL_ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [REAL_SUB_LDISTRIB] THEN
    (MATCH_MP_TAC o GEN_ALL) r1 THEN
    EXISTS_TAC (← q r"&2 * a * s * t") THEN
    REWRITE_TAC [← GSYM REAL_MUL_ASSOC, REAL_ADD_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_ADD_SYM] THEN
    SUBGOAL_THEN (← q r"(inv(&2) * &2 = &1) /\
                 (inv(&2 pow n) * &2 pow n = &1) /\
                 (inv(d) * d = &1)")
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_MUL_LINV THEN
      REWRITE_TAC [REAL_POW_EQ_0] THEN
      UNDISCH_TAC (← q r"&0 < d") THEN REAL_ARITH_TAC, ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      ASM_REWRITE_TAC [← GSYM REAL_MUL_ASSOC, REAL_MUL_RID] THEN
      REWRITE_TAC [← GSYM REAL_SUB_LDISTRIB, ← GSYM REAL_ABS_LEMMA1] THEN
      REWRITE_TAC [REAL_MUL_ASSOC] THEN
      GEN_REWRITE_TAC (LAND_CONV o funpow 2 RAND_CONV o LAND_CONV)
         [REAL_MUL_SYM] THEN ASM_REWRITE_TAC [← GSYM REAL_MUL_ASSOC],

      REWRITE_TAC (← (do
        let s2 ← (do GSYM (← SPEC (← q r"&2") REAL_ADD_LDISTRIB))
        let s1 ← (do GSYM (← SPEC (← q r"&2") REAL_SUB_LDISTRIB))
        pure [s1, s2])) THEN
      REWRITE_TAC [← GSYM REAL_ABS_LEMMA1] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONV_TAC (LAND_CONV (EQT_INTRO o REAL_ARITH)) THEN REWRITE_TAC [] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ac0] THEN
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV) [ac1] THEN
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [ac2] THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [ac3] THEN
      GEN_REWRITE_TAC RAND_CONV [ac4] THEN
      ASM_REWRITE_TAC [REAL_MUL_RID] THEN
      REWRITE_TAC [← GSYM REAL_ADD_LDISTRIB, ← GSYM REAL_SUB_LDISTRIB] THEN
      REWRITE_TAC [REAL_ABS_MUL] THEN
      SUBGOAL_THEN (← q r"abs(a) = a") SUBST1_TAC THENL
       [UNDISCH_TAC (← q r"&0 < a") THEN REAL_ARITH_TAC,
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC [REAL_ABS_LEMMA] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC []]]))

  -- @@RETURN BEGIN
  return { STEP_LEMMA1, STEP_LEMMA2 }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Now specific instances.                                                   -/
/- ------------------------------------------------------------------------- -/

structure StepInstances where
  -- @@FIELDS
  STEP_EXP : thm
  STEP_SIN : thm
  STEP_COS : thm
  STEP_LN : thm
  deriving Inhabited

@[nospecialize]
def setupStepInstances [HolBase] (D : CalcRealDeps) (BLemmas : Lemmas) (BStepLemmas : StepLemmas) :
    ExceptT String IO StepInstances := do
  -- @@SCOPE BEGIN
  let { REAL_ARITH, REAL_ARITH_TAC, .. } := D
  let { ADD1, ADD_ASSOC, ADD_CLAUSES, ADD_SYM, ARITH, FACT, FACT_LE, LE, LE_0, LE_ADD,
        LE_MULT2, LT_0, MULT_AC, MULT_CLAUSES, NOT_SUC, REAL_ABS_INV, REAL_ABS_MUL,
        REAL_ABS_NEG, REAL_ABS_NUM, REAL_ABS_POS, REAL_ABS_POW, REAL_ADD_ASSOC,
        REAL_ADD_LDISTRIB, REAL_EQ_IMP_LE, .. } := D.core1
  let { REAL_INV_LE_1, REAL_INV_MUL, REAL_LE_ADD, REAL_LE_ADD2, REAL_LE_INV,
        REAL_LE_INV2, REAL_LE_INV_EQ, REAL_LE_LMUL, REAL_LE_MUL, REAL_LE_MUL2,
        REAL_LE_POW2, REAL_LE_RADD, REAL_LE_RCANCEL_IMP, REAL_LE_RMUL, REAL_LE_TRANS,
        REAL_LT_01, REAL_LT_IMP_LE, REAL_LT_POW2, REAL_MUL_AC, REAL_MUL_ASSOC,
        REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_LNEG, REAL_MUL_LZERO, REAL_MUL_RID,
        REAL_MUL_RNEG, REAL_MUL_SYM, REAL_NEG_NEG, .. } := D.core2
  let { REAL_OF_NUM_ADD, REAL_OF_NUM_EQ, REAL_OF_NUM_LE, REAL_OF_NUM_LT,
        REAL_OF_NUM_MUL, REAL_POS, REAL_POW_1_LE, REAL_POW_2, REAL_POW_LE, real_div,
        real_pow, .. } := D.core3
  let { REAL_MONO_POW2, .. } := BLemmas
  let { STEP_LEMMA2, .. } := BStepLemmas
  -- @@SCOPE END

  let STEP_EXP ← prove
   r"abs(x) <= &1 /\
   abs(s - &2 pow n * x) <= &1 /\
   abs(t - &2 pow n * (x pow i / &(FACT i))) <= k /\
   &2 * abs(u * &2 pow n * &(SUC i) - s * t) <= &2 pow n * &(SUC i)
   ==> abs(u - &2 pow n * (x pow (SUC i)) / &(FACT(SUC i))) <=
            (&2 / &(SUC i)) * k + &1 / &(FACT(SUC i)) + &1 / &2"
   (← do
    let r3 ← REAL_ARITH (← q r"&0 <= a ==> abs(a) <= a")
    let r2 ← REAL_ARITH (← q r"&2 = &1 + &1")
    let r1 ← REAL_ARITH (← q r"(a = b) /\ c <= d ==> a <= c ==> b <= d")
    pure (STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"n:num", ← q r"s:real", ← q r"t:real", ← q r"u:real",
                ← q r"x:real", ← q r"x pow i / &(FACT i)",
                ← q r"&1", ← q r"k:real", ← q r"&1", ← q r"&(SUC i)"] STEP_LEMMA2) THEN
    ASM_REWRITE_TAC [REAL_LT_01, REAL_MUL_LID] THEN
    REWRITE_TAC [REAL_OF_NUM_LT, LT_0] THEN
    REWRITE_TAC [FACT, real_div, ← GSYM REAL_OF_NUM_MUL, real_pow] THEN
    REWRITE_TAC [REAL_MUL_LID, REAL_INV_MUL] THEN
    MATCH_MP_TAC r1 THEN
    CONJ_TAC THENL
     [REWRITE_TAC [REAL_MUL_AC],
      REWRITE_TAC [REAL_ADD_ASSOC, REAL_LE_RADD] THEN
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
      REWRITE_TAC [← GSYM REAL_ADD_LDISTRIB, ← GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN REWRITE_TAC [REAL_OF_NUM_LE, LE_0],
        MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
           [GEN_REWRITE_TAC RAND_CONV [r2] THEN
            MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC [] THEN
            MATCH_MP_TAC REAL_INV_LE_1 THEN REWRITE_TAC [REAL_LE_POW2],
            MATCH_MP_TAC REAL_LE_TRANS THEN
            EXISTS_TAC (← q r"abs(t - &2 pow n * (x pow i / &(FACT i)))") THEN
            ASM_REWRITE_TAC [REAL_ABS_POS]],
          REWRITE_TAC [REAL_ABS_MUL] THEN
          GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_LID] THEN
          MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC [REAL_ABS_POS] THEN
          CONJ_TAC THENL
           [REWRITE_TAC [REAL_ABS_POW] THEN MATCH_MP_TAC REAL_POW_1_LE THEN
            ASM_REWRITE_TAC [REAL_ABS_POS],
            MATCH_MP_TAC r3 THEN
            MATCH_MP_TAC REAL_LE_INV THEN
            REWRITE_TAC [REAL_OF_NUM_LE, LE_0]]]]]))

  let STEP_SIN ← prove
   r"abs(x) <= &1 /\
   abs(s - &2 pow n * --(x pow 2)) <= &1 /\
   abs(t - &2 pow n *
           x pow (2 * i + 1) / &(FACT (2 * i + 1)))
   <= &1 /\
   &2 * abs(u * &2 pow n * &(2 * i + 2) * &(2 * i + 3)
            - s * t)
   <= &2 pow n * &(2 * i + 2) * &(2 * i + 3)
   ==> abs(u - &2 pow n *
               --(x pow (2 * (SUC i) + 1)) /
               &(FACT (2 * (SUC i) + 1))) <= &1"
   (← do
    let r3 ← REAL_ARITH (← q r"&2 = &1 + &1")
    let r2 ← REAL_ARITH (← q r"&6 = &2 * &3")
    let r1 ← REAL_ARITH (← q r"(a = b) /\ c <= d ==> a <= c ==> b <= d")
    pure (STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"n:num", ← q r"s:real", ← q r"t:real", ← q r"u:real",
                ← q r"--(x pow 2)",
                ← q r"x pow (2 * i + 1) /
                 &(FACT(2 * i + 1))",
                ← q r"&1", ← q r"&1", ← q r"&1",
                ← q r"&(2 * i + 2) * &(2 * i + 3)"]
         STEP_LEMMA2) THEN
    ASM_REWRITE_TAC [REAL_LT_01, REAL_MUL_LID] THEN
    subgoalImp2 (fun th => REWRITE_TAC [th]) THENL
     [REWRITE_TAC (← (do
        let c3 ← ExceptT.mk (D.num_CONV (← q r"3"))
        let c2 ← ExceptT.mk (D.num_CONV (← q r"2"))
        let c1 ← ExceptT.mk (D.num_CONV (← q r"1"))
        pure [c3, c2, c1])) THEN
      REWRITE_TAC [REAL_OF_NUM_MUL, REAL_OF_NUM_LT] THEN
      REWRITE_TAC [ADD_CLAUSES, MULT_CLAUSES, LT_0], ALL_TAC] THEN
    MATCH_MP_TAC r1 THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN SUBGOAL_THEN
        (← q r"2 * (SUC i) + 1 = SUC(SUC(2 * i + 1))")
      SUBST1_TAC THENL
       [GEN_REWRITE_TAC I [← GSYM REAL_OF_NUM_EQ] THEN
        REWRITE_TAC [ADD1, ← GSYM REAL_OF_NUM_MUL, ← GSYM REAL_OF_NUM_ADD] THEN
        REAL_ARITH_TAC,
        REWRITE_TAC [real_pow, FACT] THEN
        REWRITE_TAC [ADD1, ← GSYM ADD_ASSOC] THEN
        REWRITE_TAC [ARITH] THEN
        REWRITE_TAC [real_div, REAL_INV_MUL, ← GSYM REAL_OF_NUM_MUL,
                    ← GSYM REAL_OF_NUM_ADD] THEN
        REWRITE_TAC [REAL_MUL_LID, REAL_MUL_RNEG, REAL_MUL_LNEG] THEN
        REWRITE_TAC [REAL_POW_2, REAL_MUL_AC]],
      GEN_REWRITE_TAC RAND_CONV
       [← SYM (← ExceptT.mk (D.REAL_RAT_REDUCE_CONV (← q r"&1 / &3 + &1 / &6 + &1 / &2")))] THEN
      REWRITE_TAC [REAL_ADD_ASSOC, REAL_LE_RADD] THEN
      SUBGOAL_THEN (← q r"&1 / (&(2 * i + 2) * &(2 * i + 3))
                  <= &1 / &6") ASSUME_TAC THENL
       [REWRITE_TAC [real_div, REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN
        CONV_TAC (LAND_CONV (EQT_INTRO o REAL_ARITH)) THEN REWRITE_TAC [] THEN
        REWRITE_TAC [r2] THEN
        REWRITE_TAC [REAL_OF_NUM_MUL, REAL_OF_NUM_LE] THEN
        MATCH_MP_TAC LE_MULT2 THEN ONCE_REWRITE_TAC [ADD_SYM] THEN
        REWRITE_TAC [LE_ADD], ALL_TAC] THEN
      REWRITE_TAC [← SYM (← ExceptT.mk (D.REAL_RAT_REDUCE_CONV (← q r"&1 / &6 * &2")))] THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [← GSYM REAL_MUL_RID] THEN
      REWRITE_TAC [← GSYM REAL_ADD_LDISTRIB] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC [] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC [real_div, REAL_MUL_LID, REAL_LE_INV_EQ] THEN
        REWRITE_TAC [REAL_OF_NUM_MUL, REAL_POS],
        MATCH_MP_TAC REAL_LE_ADD THEN
        REWRITE_TAC [REAL_MUL_RID, REAL_ABS_POS] THEN
        MATCH_MP_TAC REAL_LE_ADD THEN
        REWRITE_TAC [real_div, REAL_MUL_LID, REAL_LE_INV_EQ, REAL_ABS_POS] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC [REAL_LT_POW2],
        REWRITE_TAC [REAL_MUL_RID]] THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [r3] THEN
        MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
         [REWRITE_TAC [REAL_ABS_NEG, REAL_ABS_POW] THEN
          MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REWRITE_TAC [REAL_ABS_POS],
          REWRITE_TAC [real_div, REAL_MUL_LID] THEN
          MATCH_MP_TAC REAL_INV_LE_1 THEN REWRITE_TAC [REAL_LE_POW2]],
        REWRITE_TAC [real_div, REAL_ABS_MUL] THEN
        GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC [REAL_ABS_POS] THEN
        CONJ_TAC THENL
         [REWRITE_TAC [REAL_ABS_POW] THEN MATCH_MP_TAC REAL_POW_1_LE THEN
          ASM_REWRITE_TAC [REAL_ABS_POS],
          REWRITE_TAC [REAL_ABS_INV, REAL_ABS_NUM] THEN
          MATCH_MP_TAC REAL_INV_LE_1 THEN
          REWRITE_TAC [REAL_OF_NUM_LE, FACT_LE]]]]))

  let STEP_COS ← prove
   r"abs(x) <= &1 /\
   abs(s - &2 pow n * --(x pow 2)) <= &1 /\
   abs(t - &2 pow n *
           x pow (2 * i) / &(FACT (2 * i)))
   <= k /\
   &2 * abs(u * &2 pow n * &(2 * i + 1) * &(2 * i + 2)
            - s * t)
   <= &2 pow n * &(2 * i + 1) * &(2 * i + 2)
   ==> abs(u - &2 pow n *
               --(x pow (2 * (SUC i))) /
               &(FACT (2 * (SUC i))))
       <= (&2 * inv(&(2 * i + 1) * &(2 * i + 2))) * k
          + inv(&(FACT(2 * i + 2))) + &1 / &2"
   (← do
    let ac0 ← AC REAL_MUL_AC (← q r"(a * b) * c * d = (d * a * b) * c")
    let r2 ← REAL_ARITH (← q r"&2 = &1 + &1")
    let r1 ← REAL_ARITH (← q r"(a = b) /\ c <= d ==> a <= c ==> b <= d")
    pure (STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"n:num", ← q r"s:real", ← q r"t:real", ← q r"u:real",
                ← q r"--(x pow 2)",
                ← q r"x pow (2 * i) /
                 &(FACT(2 * i))",
                ← q r"&1", ← q r"k:real", ← q r"&1",
                ← q r"&(2 * i + 1) * &(2 * i + 2)"]
         STEP_LEMMA2) THEN
    ASM_REWRITE_TAC [REAL_LT_01, REAL_MUL_LID] THEN
    subgoalImp2 (fun th => REWRITE_TAC [th]) THENL
     [REWRITE_TAC (← (do
        let c3 ← ExceptT.mk (D.num_CONV (← q r"3"))
        let c2 ← ExceptT.mk (D.num_CONV (← q r"2"))
        let c1 ← ExceptT.mk (D.num_CONV (← q r"1"))
        pure [c3, c2, c1])) THEN
      REWRITE_TAC [REAL_OF_NUM_MUL, REAL_OF_NUM_LT] THEN
      REWRITE_TAC [ADD_CLAUSES, MULT_CLAUSES, LT_0], ALL_TAC] THEN
    MATCH_MP_TAC r1 THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN SUBGOAL_THEN
        (← q r"2 * (SUC i) = SUC(SUC(2 * i))")
      SUBST1_TAC THENL
       [GEN_REWRITE_TAC I [← GSYM REAL_OF_NUM_EQ] THEN
        REWRITE_TAC [ADD1, ← GSYM REAL_OF_NUM_MUL, ← GSYM REAL_OF_NUM_ADD] THEN
        REAL_ARITH_TAC,
        REWRITE_TAC [real_pow, FACT] THEN
        REWRITE_TAC [ADD1, ← GSYM ADD_ASSOC] THEN
        REWRITE_TAC [ARITH] THEN
        REWRITE_TAC [real_div, REAL_INV_MUL, ← GSYM REAL_OF_NUM_MUL,
                    ← GSYM REAL_OF_NUM_ADD] THEN
        REWRITE_TAC [REAL_MUL_LID, REAL_MUL_RNEG, REAL_MUL_LNEG] THEN
        REWRITE_TAC [REAL_POW_2, REAL_MUL_AC]],

      REWRITE_TAC [REAL_ADD_ASSOC, REAL_LE_RADD] THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
       [REWRITE_TAC [REAL_MUL_ASSOC] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [REWRITE_TAC [real_div, REAL_MUL_LID] THEN
          GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_SYM] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_INV THEN
            REWRITE_TAC [REAL_OF_NUM_MUL, REAL_POS],
            GEN_REWRITE_TAC RAND_CONV [r2] THEN
            MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
             [REWRITE_TAC [REAL_ABS_NEG, REAL_ABS_POW] THEN
              MATCH_MP_TAC REAL_POW_1_LE THEN
              ASM_REWRITE_TAC [REAL_ABS_POS],
              MATCH_MP_TAC REAL_INV_LE_1 THEN REWRITE_TAC [REAL_LE_POW2]]],
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
           (← q r"abs(t - &2 pow n * x pow (2 * i) / &(FACT (2 * i)))") THEN
          ASM_REWRITE_TAC [REAL_ABS_POS]],
        REWRITE_TAC [real_div, REAL_MUL_LID, REAL_INV_MUL, REAL_ABS_MUL] THEN
        GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_RID] THEN
        ONCE_REWRITE_TAC [ac0] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC [REAL_ABS_POS] THEN
        REPEAT CONJ_TAC THENL
         [REPEAT (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
          REWRITE_TAC [REAL_POS, REAL_ABS_POS, REAL_LE_INV_EQ],
          REWRITE_TAC [REAL_ABS_INV] THEN
          REWRITE_TAC [← GSYM REAL_INV_MUL, REAL_ABS_NUM] THEN
          MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
          REWRITE_TAC [← ExceptT.mk (D.num_CONV (← q r"2")),
                      ← ExceptT.mk (D.num_CONV (← q r"1")), ADD_CLAUSES] THEN
          REWRITE_TAC [← SYM (← ExceptT.mk (D.num_CONV (← q r"2"))),
                      ← SYM (← ExceptT.mk (D.num_CONV (← q r"1")))] THEN
          REWRITE_TAC [FACT, REAL_OF_NUM_MUL] THEN
          REWRITE_TAC [MULT_AC],
          REWRITE_TAC [REAL_ABS_POW] THEN MATCH_MP_TAC REAL_POW_1_LE THEN
          ASM_REWRITE_TAC [REAL_ABS_POS]]]]))

  let STEP_LN ← prove
   r"2 <= n /\
   abs(x) <= &1 / &2 /\
   abs(s - &2 pow n * --x) <= &1 /\
   abs(t - &2 pow n * -- ((--x) pow (SUC i) / &(SUC i))) <= &3 /\
   &2 * abs(u * &2 pow n * &(SUC(SUC i)) - &(SUC i) * s * t)
   <= &2 pow n * &(SUC(SUC i))
   ==> abs(u - &2 pow n * -- ((--x) pow (SUC(SUC i)) / &(SUC(SUC i)))) <= &3"
   (← do
    let r3 ← REAL_ARITH (← q r"(x = &1) ==> &0 <= x /\ x <= &1")
    let r2 ← REAL_ARITH (← q r"(x = &1) ==> &0 <= x")
    let r1 ← REAL_ARITH (← q r"(a = b) /\ c <= d ==> a <= c ==> b <= d")
    pure (STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"n:num", ← q r"s:real", ← q r"t:real", ← q r"u:real",
                ← q r"--x",
                ← q r"-- (--x pow (SUC i) / &(SUC i))",
                ← q r"&1", ← q r"&3",
                ← q r"&(SUC i)",
                ← q r"&(SUC(SUC i))"]
         STEP_LEMMA2) THEN
    ASM_REWRITE_TAC [REAL_LT_01, REAL_MUL_LID] THEN
    REWRITE_TAC [REAL_OF_NUM_LT, LT_0] THEN
    MATCH_MP_TAC r1 THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC [real_pow, real_div, REAL_INV_MUL] THEN
      REWRITE_TAC [REAL_MUL_LNEG, REAL_MUL_RNEG, REAL_NEG_NEG] THEN
      AP_TERM_TAC THEN REWRITE_TAC [REAL_MUL_ASSOC] THEN
      GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
      SUBGOAL_THEN (← q r"inv(&(SUC i)) * &(SUC i) = &1") ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_MUL_LINV THEN
        REWRITE_TAC [REAL_OF_NUM_EQ, NOT_SUC],
        ASM_REWRITE_TAC [REAL_MUL_ASSOC, REAL_MUL_LID] THEN
        REWRITE_TAC [REAL_MUL_AC]],
      GEN_REWRITE_TAC RAND_CONV [← SYM (← ExceptT.mk (D.REAL_RAT_REDUCE_CONV
        (← q r"(&1 / &2 + &1 / &4) * &3 + &1 / &4 + &1 / &2")))] THEN
      REWRITE_TAC [REAL_ADD_ASSOC, REAL_LE_RADD] THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
       [REWRITE_TAC [REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        CONV_TAC (RAND_CONV (EQT_INTRO o REAL_ARITH)) THEN REWRITE_TAC [] THEN
        GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN
          EXISTS_TAC (← q r"&(SUC(SUC i))") THEN
          REWRITE_TAC [REAL_MUL_LZERO, REAL_OF_NUM_LT, LT_0] THEN
          REWRITE_TAC [real_div, ← GSYM REAL_MUL_ASSOC] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC [REAL_POS] THEN
          MATCH_MP_TAC r2 THEN
          MATCH_MP_TAC REAL_MUL_LINV THEN
          REWRITE_TAC [REAL_OF_NUM_EQ, NOT_SUC],
          MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN
          EXISTS_TAC (← q r"&(SUC(SUC i))") THEN
          REWRITE_TAC [REAL_OF_NUM_LT, LT_0] THEN
          REWRITE_TAC [real_div, REAL_MUL_LID, ← GSYM REAL_MUL_ASSOC] THEN
          GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_RID] THEN
          MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC [REAL_POS] THEN
          REWRITE_TAC [REAL_OF_NUM_LE, LE] THEN
          MATCH_MP_TAC r3 THEN
          MATCH_MP_TAC REAL_MUL_LINV THEN
          REWRITE_TAC [REAL_OF_NUM_EQ, NOT_SUC],
          MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC [REAL_ABS_POS] THEN
          REWRITE_TAC [real_div, REAL_MUL_LID, REAL_LE_INV_EQ] THEN
          MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC [REAL_LT_POW2],
          MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC [REAL_ABS_NEG] THEN
          REWRITE_TAC [real_div, REAL_MUL_LID] THEN
          MATCH_MP_TAC REAL_LE_INV2 THEN
          CONV_TAC (LAND_CONV (EQT_INTRO o REAL_ARITH)) THEN REWRITE_TAC [] THEN
          SUBST1_TAC (← SYM (← ExceptT.mk (D.REAL_INT_REDUCE_CONV (← q r"&2 pow 2")))) THEN
          MATCH_MP_TAC REAL_MONO_POW2 THEN ASM_REWRITE_TAC []],
        REWRITE_TAC [real_div, REAL_ABS_MUL, REAL_ABS_NEG, REAL_ABS_INV] THEN
        REWRITE_TAC [REAL_ABS_POW, REAL_ABS_NEG, REAL_MUL_LID] THEN
        REWRITE_TAC [REAL_ABS_NUM] THEN REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN
        ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REWRITE_TAC [REAL_MUL_ASSOC] THEN
        SUBGOAL_THEN (← q r"inv(&(SUC i)) * &(SUC i) = &1") ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_MUL_LINV THEN REWRITE_TAC [REAL_OF_NUM_EQ, NOT_SUC],
          GEN_REWRITE_TAC RAND_CONV
           [← EQT_ELIM (← ExceptT.mk (D.REAL_RAT_REDUCE_CONV
              (← q r"inv(&4) = inv(&2) * inv(&2)")))] THEN
          ASM_REWRITE_TAC [REAL_MUL_RID, ← GSYM REAL_MUL_ASSOC] THEN
          MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC
            [REAL_POS, REAL_ABS_POS, REAL_LE_INV_EQ, ← GSYM REAL_ABS_POW] THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC [REAL_POS] THEN
            REWRITE_TAC [ADD1, ← GSYM REAL_OF_NUM_ADD] THEN
            MP_TAC (← SPEC (← q r"i:num") REAL_POS) THEN REAL_ARITH_TAC,
            REWRITE_TAC [real_pow, REAL_ABS_POW] THEN
            GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_RID] THEN
            MATCH_MP_TAC REAL_LE_MUL2 THEN
            REWRITE_TAC [REAL_LE_INV_EQ, REAL_ABS_POS] THEN
            REPEAT CONJ_TAC THENL
             [CONV_TAC (RAND_CONV (D.REAL_RAT_REDUCE_CONV)) THEN ASM_REWRITE_TAC [],
              MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC [REAL_ABS_POS],
              MATCH_MP_TAC REAL_POW_1_LE THEN REWRITE_TAC [REAL_ABS_POS] THEN
              MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"&1 / &2") THEN
              ASM_REWRITE_TAC [] THEN CONV_TAC (D.REAL_RAT_REDUCE_CONV)]]]]]))

  -- @@RETURN BEGIN
  return { STEP_EXP, STEP_SIN, STEP_COS, STEP_LN }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Expand the "!k. SUC k < r ==> P k" term for given numeral r.              -/
/- ------------------------------------------------------------------------- -/

/-- `EXPAND_RANGE_CONV`'s inner recursion `expand_conv` (calc_real.ml 967-977),
    closing over `trivial_conv`, `nontrivial_conv` and `num_CONV`. -/
partial def expandConv [HolBase] (trivial_conv nontrivial_conv num_CONV : ioconv) :
    ioconv := fun tm => ExceptT.run do
  tryCatch
    (ExceptT.mk (trivial_conv tm))
    (fun _ => do
      let mth ← ExceptT.mk (num_CONV (← liftExcept (do rand (← lhand (← body (← rand tm))))))
      let th1 ← ExceptT.mk
        (BINDER_CONV (LAND_CONV (RAND_CONV (fun _ => pure (.ok mth)))) tm)
      let th2 ← TRANS th1 (← ExceptT.mk (nontrivial_conv (← liftExcept (rand (concl th1)))))
      let th3 ← ExceptT.mk
        (COMB2_CONV (RAND_CONV (expandConv trivial_conv nontrivial_conv num_CONV))
                    (SUBS_CONV [← SYM mth])
                    (← liftExcept (rand (concl th2))))
      TRANS th2 th3)

structure ExpandRange where
  -- @@FIELDS
  EXPAND_RANGE_CONV : ioconv
  deriving Inhabited

@[nospecialize]
def setupExpandRange [HolBase] (D : CalcRealDeps) :
    ExceptT String IO ExpandRange := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, .. } := D
  let { LT, LT_SUC, .. } := D.core1
  -- @@SCOPE END

  let EXPAND_RANGE_CONV : ioconv ← do
    -- `let pth0 = ... and pth1 = ... and pth2 = ...` (left to right).
    let pth0 ← prove
     r"(!k. SUC k < 0 ==> P k) <=> T"
     (REWRITE_TAC [LT])
    let pth1 ← prove
     r"(!k. k < (SUC m) ==> P k) <=>
     (!k. k < m ==> P k) /\ P m"
     (REWRITE_TAC [LT] THEN MESON_TAC [])
    let pth2 ← prove
     r"(!k. k < 0 ==> P k) <=> T"
     (REWRITE_TAC [LT])
    let triv_conv ← GEN_REWRITE_CONV_NET id [pth0]
    let trivial_conv ← GEN_REWRITE_CONV_NET id [pth2]
    let nontrivial_conv ← GEN_REWRITE_CONV_NET id [pth1]
    -- `let s_tm = `s:real` and m_tm = `m:num` and n_tm = `n:num`` (unused in
    -- the body in OCaml too).
    let expand_conv : ioconv := expandConv trivial_conv nontrivial_conv D.num_CONV
    let hack_conv : ioconv :=
      triv_conv ORELSEC
      (BINDER_CONV (LAND_CONV
         ((RAND_CONV D.num_CONV) THENC REWR_CONV LT_SUC)) THENC
       expand_conv)
    pure hack_conv

  -- @@RETURN BEGIN
  return { EXPAND_RANGE_CONV }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Lemmas leading to iterative versions.                                     -/
/- ------------------------------------------------------------------------- -/

structure IterExp where
  -- @@FIELDS
  STEP_EXP_THM : thm
  STEP_EXP_RULE : thm → ExceptT String IO thm
  STEP_EXP_0 : thm
  STEP_EXP_1 : thm
  STEP_EXP_2 : thm
  STEP_EXP_3 : thm
  STEP_EXP_4 : thm
  STEP_EXP_5 : thm
  STEP_EXP_4_PLUS : thm
  STEPS_EXP_0 : thm
  STEPS_EXP_1 : thm
  STEPS_EXP_2 : thm
  STEPS_EXP_3 : thm
  STEPS_EXP_4 : thm
  deriving Inhabited

@[nospecialize]
def setupIterExp [HolBase] (D : CalcRealDeps) (BStepInstances : StepInstances) (BExpandRange : ExpandRange) :
    ExceptT String IO IterExp := do
  -- @@SCOPE BEGIN
  let { INDUCT_TAC, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, REAL_LE_IMP, .. } := D
  let { ADD1, ADD_CLAUSES, ARITH_SUC, FACT, FACT_MONO, LE_ADD, LE_EXISTS, LE_SUC, LT,
        LT_SUC, REAL_ABS_0, REAL_ADD_ASSOC, REAL_ADD_LDISTRIB, .. } := D.core1
  let { REAL_INV_1, REAL_LE_ADD2, REAL_LE_INV2, REAL_LE_LMUL, REAL_LE_RADD,
        REAL_LE_REFL, REAL_LE_TRANS, REAL_LT_IMP_LE, REAL_MUL_ASSOC, REAL_MUL_LID,
        REAL_MUL_RID, REAL_MUL_RZERO, REAL_MUL_SYM, .. } := D.core2
  let { REAL_OF_NUM_ADD, REAL_OF_NUM_LE, REAL_POS, REAL_SUB_REFL, real_div, real_pow,
        sum, .. } := D.core3
  let { STEP_EXP, .. } := BStepInstances
  let { EXPAND_RANGE_CONV, .. } := BExpandRange
  -- @@SCOPE END

  let STEP_EXP_THM ← prove
   r"abs(x) <= &1 /\
   abs(s - &2 pow n * x) < &1 /\
   abs(t(i) - &2 pow n * (x pow i / &(FACT i))) <= k ==>
   &2 * abs(t(SUC i) * &2 pow n * &(SUC i) - s * t(i)) <= &2 pow n * &(SUC i)
   ==> abs(t(SUC i) - &2 pow n * (x pow (SUC i)) / &(FACT(SUC i))) <=
            (&2 / &(SUC i)) * k + &1 / &(FACT(SUC i)) + &1 / &2"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC (← GEN_ALL STEP_EXP) THEN
    MAP_EVERY EXISTS_TAC [← q r"s:real", ← q r"t(i:num):real"] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    ASM_REWRITE_TAC [])

  let STEP_EXP_RULE : thm → ExceptT String IO thm ← pure (fun th => do
    let th1 ← MATCH_MP STEP_EXP_THM th
    let th2 ← UNDISCH (← PURE_REWRITE_RULE [ARITH_SUC] th1)
    let th3 ← CONV_RULE (RAND_CONV (ONCE_DEPTH_CONV D.NUM_FACT_CONV)) th2
    let th4 ← CONV_RULE (RAND_CONV D.REAL_RAT_REDUCE_CONV) th3
    let th5 ← ASSUME (← liftExcept (find is_conj (hyp th)))
    let (th6a, th6b) ← F_F (fun x => pure x) CONJUNCT1 (← CONJ_PAIR th5)
    CONJ th6a (← CONJ th6b th4))

  let STEP_EXP_0 ← (do UNDISCH (← prove
   r"abs(x) <= &1 /\
   abs(s - &2 pow n * x) < &1 /\
   (t(0) = &2 pow n) ==>
   abs(x) <= &1 /\
   abs(s - &2 pow n * x) < &1 /\
   abs(t(0) - &2 pow n * (x pow 0 / &(FACT 0))) <= &0"
   (STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [real_pow, FACT, real_div, REAL_INV_1, REAL_MUL_RID] THEN
    REWRITE_TAC [REAL_SUB_REFL, REAL_ABS_0, REAL_LE_REFL])))

  let STEP_EXP_1 ← STEP_EXP_RULE STEP_EXP_0     -- e(1) = 3/2
  let STEP_EXP_2 ← STEP_EXP_RULE STEP_EXP_1     -- e(2) = 5/2
  let STEP_EXP_3 ← STEP_EXP_RULE STEP_EXP_2     -- e(3) = 7/3
  let STEP_EXP_4 ← STEP_EXP_RULE STEP_EXP_3     -- e(4) = 41/24
  let STEP_EXP_5 ← STEP_EXP_RULE STEP_EXP_4     -- e(5) = 143/120

  let STEP_EXP_4_PLUS ← prove
   r"4 <= m /\
   abs(x) <= &1 /\
   abs(s - &2 pow n * x) < &1 /\
   (t(0) = &2 pow n) /\
   (!k. SUC k < SUC m ==>
                &2 * abs(t(SUC k) * &2 pow n * &(SUC k) - s * t(k))
                <= &2 pow n * &(SUC k))
   ==> abs(t m - &2 pow n * x pow m / &(FACT m)) <= &2"
   (← do
    let lemma ← prove
     r"(!k. k < (SUC m) ==> P k) <=>
     (!k. k < m ==> P k) /\ P m"
     (REWRITE_TAC [LT] THEN MESON_TAC [])
    let r3 ← REAL_ARITH (← q r"&0 <= &4")
    let r2 ← REAL_ARITH (← q r"&2 * &2 = &4")
    let r1 ← REAL_ARITH (← q r"b <= c ==> a <= b ==> a <= c")
    pure (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    POP_ASSUM (X_CHOOSE_THEN (← q r"d:num") SUBST1_TAC o REWRITE_RULE [LE_EXISTS]) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC [LT_SUC] THEN SPEC_TAC (← q r"d:num", ← q r"d:num") THEN
    INDUCT_TAC THENL
     [REWRITE_TAC [ADD_CLAUSES] THEN
      SUBST1_TAC (← ExceptT.mk (TOP_DEPTH_CONV D.num_CONV (← q r"4"))) THEN
      REWRITE_TAC [lemma] THEN REWRITE_TAC [ARITH_SUC] THEN
      REWRITE_TAC [LT] THEN STRIP_TAC THEN
      MP_TAC (← DISCH_ALL STEP_EXP_4) THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC r1 THEN
      CONV_TAC D.REAL_RAT_REDUCE_CONV,
      REWRITE_TAC [ADD_CLAUSES, lemma] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"&2 / &(SUC(4 + d)) * &2 +
                &1 / &(FACT(SUC(4 + d))) + &1 / &2") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC (← GEN_ALL STEP_EXP) THEN ASM_REWRITE_TAC [] THEN
        EXISTS_TAC (← q r"s:real") THEN EXISTS_TAC (← q r"t(4 + d):real") THEN
        ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC [],
          FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []],
        GEN_REWRITE_TAC RAND_CONV
          [← SYM (← ExceptT.mk (D.REAL_RAT_REDUCE_CONV (← q r"&3 / &2 + &1 / &2")))] THEN
        REWRITE_TAC [REAL_LE_RADD, REAL_ADD_ASSOC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"&4 / &5 + &1 / &120") THEN
        CONV_TAC (RAND_CONV D.REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC [] THEN
        MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
         [ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
          REWRITE_TAC [real_div, REAL_MUL_ASSOC] THEN
          REWRITE_TAC [r2] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN
          REWRITE_TAC [r3] THEN
          MATCH_MP_TAC REAL_LE_INV2 THEN
          REWRITE_TAC [ADD1, ← GSYM REAL_OF_NUM_ADD] THEN
          MP_TAC (← SPEC (← q r"d':num") REAL_POS) THEN REAL_ARITH_TAC,
          REWRITE_TAC [real_div, REAL_MUL_LID] THEN
          MATCH_MP_TAC REAL_LE_INV2 THEN
          CONV_TAC (LAND_CONV (EQT_INTRO o REAL_ARITH)) THEN REWRITE_TAC [] THEN
          SUBST1_TAC (← SYM (← ExceptT.mk (D.NUM_FACT_CONV (← q r"FACT 5")))) THEN
          REWRITE_TAC [REAL_OF_NUM_LE] THEN MATCH_MP_TAC FACT_MONO THEN
          REWRITE_TAC [← ExceptT.mk (D.num_CONV (← q r"5")), LE_SUC, LE_ADD]]]]))

  let STEPS_EXP_0 ← prove
   r"abs(x) <= &1 /\
   abs(s - &2 pow n * x) < &1 /\
   (t(0) = &2 pow n) /\
   (!k. SUC k < 0 ==>
                &2 * abs(t(SUC k) * &2 pow n * &(SUC k) - s * t(k))
                <= &2 pow n * &(SUC k))
   ==> abs(sum(0,0) t -
           &2 pow n * sum(0,0) (\i. x pow i / &(FACT i))) <= &2 * &0"
   (STRIP_TAC THEN ASM_REWRITE_TAC [sum] THEN
    REWRITE_TAC [REAL_MUL_RZERO, REAL_ABS_0, REAL_SUB_REFL, REAL_LE_REFL])

  let STEPS_EXP_1 ← prove
   r"abs(x) <= &1 /\
   abs(s - &2 pow n * x) < &1 /\
   (t(0) = &2 pow n) /\
   (!k. SUC k < 1 ==>
                &2 * abs(t(SUC k) * &2 pow n * &(SUC k) - s * t(k))
                <= &2 pow n * &(SUC k))
   ==> abs(sum(0,1) t - &2 pow n * sum(0,1)(\i. x pow i / &(FACT i)))
         <= &2 * &1"
   (CONV_TAC (ONCE_DEPTH_CONV EXPAND_RANGE_CONV) THEN REWRITE_TAC [] THEN
    STRIP_TAC THEN CONV_TAC (ONCE_DEPTH_CONV D.REAL_SUM_CONV) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"&0") THEN
    CONV_TAC (RAND_CONV D.REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC [] THEN
    MP_TAC (← DISCH_ALL STEP_EXP_0) THEN ASM_REWRITE_TAC [])

  let STEPS_EXP_2 ← prove
   r"abs(x) <= &1 /\
   abs(s - &2 pow n * x) < &1 /\
   (t(0) = &2 pow n) /\
   (!k. SUC k < 2 ==>
                &2 * abs(t(SUC k) * &2 pow n * &(SUC k) - s * t(k))
                <= &2 pow n * &(SUC k))
   ==> abs(sum(0,2) t - &2 pow n * sum(0,2) (\i. x pow i / &(FACT i)))
       <= &2 * &2"
   (← do
    let r2 ← REAL_ARITH (← q r"abs(a + b) <= abs(a) + abs(b)")
    let r1 ← REAL_ARITH (← q r"(a + b) - (c + d) = (a - c) + (b - d)")
    pure (CONV_TAC (ONCE_DEPTH_CONV EXPAND_RANGE_CONV) THEN REWRITE_TAC [] THEN
    STRIP_TAC THEN CONV_TAC (ONCE_DEPTH_CONV D.REAL_SUM_CONV) THEN
    REWRITE_TAC [REAL_ADD_LDISTRIB] THEN
    REWRITE_TAC [r1] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"&0 + &3 / &2") THEN
    CONV_TAC (RAND_CONV D.REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC [] THEN
    MATCH_MP_TAC (← REAL_LE_IMP r2) THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [MP_TAC (← DISCH_ALL STEP_EXP_0) THEN ASM_REWRITE_TAC [],
      MP_TAC (← DISCH_ALL STEP_EXP_1) THEN
      ASM_REWRITE_TAC [ADD_CLAUSES]]))

  let STEPS_EXP_3 ← prove
   r"abs(x) <= &1 /\
   abs(s - &2 pow n * x) < &1 /\
   (t(0) = &2 pow n) /\
   (!k. SUC k < 3 ==>
                &2 * abs(t(SUC k) * &2 pow n * &(SUC k) - s * t(k))
                <= &2 pow n * &(SUC k))
   ==> abs(sum(0,3) t - &2 pow n * sum(0,3) (\i. x pow i / &(FACT i)))
       <= &2 * &3"
   (← do
    let r2 ← REAL_ARITH (← q r"abs(a + b) <= abs(a) + abs(b)")
    let r1 ← REAL_ARITH (← q r"(a + b) - (c + d) = (a - c) + (b - d)")
    pure (CONV_TAC (ONCE_DEPTH_CONV EXPAND_RANGE_CONV) THEN REWRITE_TAC [] THEN
    STRIP_TAC THEN CONV_TAC (ONCE_DEPTH_CONV D.REAL_SUM_CONV) THEN
    REWRITE_TAC [REAL_ADD_LDISTRIB] THEN
    REWRITE_TAC [r1] THEN
    REWRITE_TAC [← GSYM REAL_ADD_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"&0 + &3 / &2 + &5 / &2") THEN
    CONV_TAC (RAND_CONV D.REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC [] THEN
    REPEAT
     (MATCH_MP_TAC (← REAL_LE_IMP r2) THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC)
    THENL
     [MP_TAC (← DISCH_ALL STEP_EXP_0) THEN ASM_REWRITE_TAC [],
      MP_TAC (← DISCH_ALL STEP_EXP_1) THEN ASM_REWRITE_TAC [ADD_CLAUSES],
      MP_TAC (← DISCH_ALL STEP_EXP_2) THEN ASM_REWRITE_TAC [ADD_CLAUSES]]))

  let STEPS_EXP_4 ← prove
   r"abs(x) <= &1 /\
   abs(s - &2 pow n * x) < &1 /\
   (t(0) = &2 pow n) /\
   (!k. SUC k < 4 ==>
                &2 * abs(t(SUC k) * &2 pow n * &(SUC k) - s * t(k))
                <= &2 pow n * &(SUC k))
   ==> abs(sum(0,4) t - &2 pow n * sum(0,4) (\i. x pow i / &(FACT i)))
       <= &2 * &4"
   (← do
    let r2 ← REAL_ARITH (← q r"abs(a + b) <= abs(a) + abs(b)")
    let r1 ← REAL_ARITH (← q r"(a + b) - (c + d) = (a - c) + (b - d)")
    pure (CONV_TAC (ONCE_DEPTH_CONV EXPAND_RANGE_CONV) THEN REWRITE_TAC [] THEN
    STRIP_TAC THEN CONV_TAC (ONCE_DEPTH_CONV D.REAL_SUM_CONV) THEN
    REWRITE_TAC [REAL_ADD_LDISTRIB] THEN
    REWRITE_TAC [r1] THEN
    REWRITE_TAC [← GSYM REAL_ADD_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"&0 + &3 / &2 + &5 / &2 + &7 / &3") THEN
    CONV_TAC (RAND_CONV D.REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC [] THEN
    REPEAT
     (MATCH_MP_TAC (← REAL_LE_IMP r2) THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC)
    THENL
     [MP_TAC (← DISCH_ALL STEP_EXP_0) THEN ASM_REWRITE_TAC [],
      MP_TAC (← DISCH_ALL STEP_EXP_1) THEN ASM_REWRITE_TAC [ADD_CLAUSES],
      MP_TAC (← DISCH_ALL STEP_EXP_2) THEN ASM_REWRITE_TAC [ADD_CLAUSES],
      MP_TAC (← DISCH_ALL STEP_EXP_3) THEN ASM_REWRITE_TAC [ADD_CLAUSES]]))

  -- @@RETURN BEGIN
  return { STEP_EXP_THM, STEP_EXP_RULE, STEP_EXP_0, STEP_EXP_1, STEP_EXP_2, STEP_EXP_3,
           STEP_EXP_4, STEP_EXP_5, STEP_EXP_4_PLUS, STEPS_EXP_0, STEPS_EXP_1,
           STEPS_EXP_2, STEPS_EXP_3, STEPS_EXP_4 }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Iterated versions.  (calc_real.ml 1177-1309)                              -/
/- ------------------------------------------------------------------------- -/

structure StepsIter where
  -- @@FIELDS
  STEPS_EXP_LEMMA : thm
  STEPS_EXP : thm
  STEPS_LN : thm
  deriving Inhabited

@[nospecialize]
def setupStepsIter [HolBase] (D : CalcRealDeps) (BLemmas : Lemmas) (BIterExp : IterExp) :
    ExceptT String IO StepsIter := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, INDUCT_TAC, REAL_ARITH, REAL_INT_REDUCE_CONV, REAL_LE_IMP,
        REAL_RAT_REDUCE_CONV, num_CONV, .. } := D
  let { ADD1, ADD_CLAUSES, ADD_SYM, ARITH, ARITH_EQ, ARITH_SUC, LE, LE_0, LE_ADD,
        LE_CASES, LE_EXISTS, LT, LT_0, LT_TRANS, NOT_SUC, REAL_ABS_INV, REAL_ABS_MUL,
        REAL_ABS_NEG, REAL_ABS_NUM, REAL_ABS_POS, REAL_ABS_POW, REAL_ADD_LDISTRIB,
        REAL_ADD_SYM, REAL_DIV_1, .. } := D.core1
  let { REAL_INV_1, REAL_INV_MUL, REAL_LE_ADD2, REAL_LE_INV2, REAL_LE_INV_EQ,
        REAL_LE_LCANCEL_IMP, REAL_LE_LMUL, REAL_LE_MUL, REAL_LE_MUL2,
        REAL_LE_RCANCEL_IMP, REAL_LE_RMUL, REAL_LE_SUB_LADD, REAL_LE_TRANS,
        REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_INV_EQ, REAL_LT_MUL, REAL_MUL_AC,
        REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_LNEG, REAL_MUL_RID,
        REAL_MUL_RINV, REAL_MUL_RNEG, REAL_MUL_SYM, REAL_NEG_NEG, .. } := D.core2
  let { REAL_OF_NUM_ADD, REAL_OF_NUM_EQ, REAL_OF_NUM_LE, REAL_OF_NUM_LT,
        REAL_OF_NUM_SUC, REAL_POS, REAL_POW_EQ_0, REAL_POW_INV, REAL_POW_LE,
        REAL_POW_LE2, REAL_POW_LT, REAL_POW_MONO, REAL_POW_ONE, REAL_SUB_LDISTRIB,
        REAL_SUB_RDISTRIB, SUM_ABS_LE, SUM_BOUND, real_abs, real_div, real_pow, sum, .. } := D.core3
  let { REAL_MUL_RSUM0, REAL_SUB_SUM0, .. } := BLemmas
  let { STEPS_EXP_0, STEPS_EXP_1, STEPS_EXP_2, STEPS_EXP_3, STEPS_EXP_4,
        STEP_EXP_4_PLUS, .. } := BIterExp
  -- @@SCOPE END

  let STEPS_EXP_LEMMA ← prove
   r"(!k. P(SUC k) ==> P(k)) /\
   (P(0) ==> (abs(sum(0,0) z) <= &2 * &0)) /\
   (P(1) ==> (abs(sum(0,1) z) <= &2 * &1)) /\
   (P(2) ==> (abs(sum(0,2) z) <= &2 * &2)) /\
   (P(3) ==> (abs(sum(0,3) z) <= &2 * &3)) /\
   (P(4) ==> (abs(sum(0,4) z) <= &2 * &4)) /\
   (!m. 4 <= m /\ P(SUC m) ==> (abs(z m) <= &2))
   ==> !m. P(m) ==> (abs(sum(0,m) z) <= &2 * &m)"
   (← do
    let r1 ← REAL_ARITH (← q r"abs(a + b) <= abs(a) + abs(b)")
    pure (STRIP_TAC THEN SUBGOAL_THEN
      (← q r"!d. P(d + 4) ==>
         abs(sum(0,d + 4) z) <= &2 * &(d + 4)")
    ASSUME_TAC THENL
     [INDUCT_TAC THEN ASM_REWRITE_TAC [ADD_CLAUSES] THEN
      DISCH_TAC THEN REWRITE_TAC [sum, ADD1] THEN
      ONCE_REWRITE_TAC [← GSYM REAL_OF_NUM_ADD] THEN
      REWRITE_TAC [REAL_ADD_LDISTRIB] THEN
      MATCH_MP_TAC (← REAL_LE_IMP r1) THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
        REWRITE_TAC [REAL_MUL_RID] THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC [ADD_CLAUSES] THEN ONCE_REWRITE_TAC [ADD_SYM] THEN
        REWRITE_TAC [LE_ADD]],
      GEN_TAC THEN
      DISJ_CASES_THEN MP_TAC (← SPECL [← q "4", ← q "m:num"] LE_CASES) THENL
       [DISCH_THEN (CHOOSE_THEN SUBST1_TAC o REWRITE_RULE [LE_EXISTS]) THEN
        ONCE_REWRITE_TAC [ADD_SYM] THEN ASM_REWRITE_TAC [],
        SUBST1_TAC (← ExceptT.mk (TOP_DEPTH_CONV num_CONV (← q "4"))) THEN
        REWRITE_TAC [LE] THEN REWRITE_TAC [ARITH_SUC] THEN
        DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
        ASM_REWRITE_TAC []]]))

  let STEPS_EXP ← prove
   r"abs(x) <= &1 /\
   abs(s - &2 pow n * x) < &1 /\
   (t(0) = &2 pow n) /\
   (!k. SUC k < m ==>
                &2 * abs(t(SUC k) * &2 pow n * &(SUC k) - s * t(k))
                <= &2 pow n * &(SUC k))
   ==> abs(sum(0,m) t - &2 pow n * sum(0,m) (\i. x pow i / &(FACT i)))
       <= &2 * &m"
   (REWRITE_TAC [REAL_MUL_RSUM0, REAL_SUB_SUM0] THEN
    SPEC_TAC (← q "m:num", ← q "m:num") THEN MATCH_MP_TAC STEPS_EXP_LEMMA THEN
    REWRITE_TAC [← GSYM REAL_SUB_SUM0, ← GSYM REAL_MUL_RSUM0] THEN
    REWRITE_TAC [STEPS_EXP_0, STEPS_EXP_1, STEPS_EXP_2, STEPS_EXP_3] THEN
    REWRITE_TAC [STEPS_EXP_4, STEP_EXP_4_PLUS] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC (← q "k:num") THEN
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [LT])

  let STEPS_LN ← prove
   r"2 <= n /\
   abs(x) <= &1 / &2 /\
   abs(s - &2 pow n * --x) < &1 /\
   (t(0) = --s) /\
   (!k. SUC k < m ==>
                &2 * abs(t(SUC k) * &2 pow n * &(SUC(SUC k))
                         - &(SUC k) * s * t(k))
                <= &2 pow n * &(SUC(SUC k)))
   ==> abs(sum(0,m) t - &2 pow n * sum(0,m)
                (\i. (--(&1)) pow i * x pow (SUC i) / &(SUC i))) <= &3 * &m"
   (← do
    let r4 ← REAL_ARITH
      (← q r"!y. abs(x - y) < &1 /\ abs(y) <= d - &1 ==> abs(x) <= d")
    let r3 ← REAL_ARITH
      (← q r"!y. abs(x - y) + abs(y - z) <= e ==> abs(x - z) <= e")
    let r2 ← REAL_ARITH
      (← q r"!y. abs(x - y) + abs(y - z) <= e ==> abs(x - z) <= e")
    let r1 ← REAL_ARITH (← q r"-- a - b * c = --(a - b * --c)")
    pure (REWRITE_TAC [REAL_MUL_RSUM0, REAL_SUB_SUM0] THEN
    STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC (← REAL_LE_IMP SUM_ABS_LE) THEN
    MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC [ADD_CLAUSES, LE_0] THEN
    INDUCT_TAC THENL
     [REWRITE_TAC [real_pow, ARITH, REAL_DIV_1, REAL_MUL_LID, REAL_MUL_RID] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [r1] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "&1") THEN
      ASM_SIMP_TAC [REAL_ABS_NEG, REAL_LT_IMP_LE, REAL_OF_NUM_LE, ARITH],
      ALL_TAC] THEN
    DISCH_THEN (fun th => tactic_of do pure (ASSUME_TAC th THEN MP_TAC th)) THEN
    DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN
    SUBGOAL_THEN (← q "p:num < m") (ANTE_RES_THEN MP_TAC) THENL
     [UNDISCH_TAC (← q "SUC p < m") THEN ARITH_TAC, ALL_TAC] THEN
    DISCH_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC r2 THEN
    EXISTS_TAC (← q "&(SUC p) * s * t p / (&2 pow n * &(SUC(SUC p)))") THEN
    ONCE_REWRITE_TAC [← SYM (← ExceptT.mk (REAL_RAT_REDUCE_CONV (← q r"&1 / &2 + &5 / &2")))] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN
      EXISTS_TAC (← q "&2 pow n * &(SUC(SUC p))") THEN
      SUBGOAL_THEN (← q "&0 < &2 pow n * &(SUC(SUC p))") ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN
        SIMP_TAC [REAL_POW_LT, REAL_OF_NUM_LT, LT_0, ARITH], ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"!x y. &0 < y ==> (abs(x) * y = abs(x * y))")
       (fun th => ASM_SIMP_TAC [th]) THENL
       [REPEAT STRIP_TAC THEN REWRITE_TAC [REAL_ABS_MUL] THEN
        AP_TERM_TAC THEN ASM_SIMP_TAC [real_abs, REAL_LT_IMP_LE], ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC (← q "&2") THEN
      REWRITE_TAC [REAL_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC [← GSYM REAL_MUL_ASSOC, REAL_MUL_LID] THEN
      REWRITE_TAC [REAL_SUB_RDISTRIB] THEN
      SUBGOAL_THEN (← q r"!a b c d. &0 < a ==> ((b * c * d / a) * a = b * c * d)")
       (fun th => ASM_SIMP_TAC [th]) THEN
      SIMP_TAC [real_div, ← GSYM REAL_MUL_ASSOC, REAL_MUL_LINV, REAL_MUL_RID,
               REAL_LT_IMP_NZ],
      ALL_TAC] THEN
    MATCH_MP_TAC r3 THEN
    EXISTS_TAC (← q "--(&1) pow p * s * x pow (SUC p) / &(SUC(SUC p))") THEN
    ONCE_REWRITE_TAC [← SYM (← ExceptT.mk (REAL_RAT_REDUCE_CONV (← q r"&9 / &4 + &1 / &4")))] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [SUBGOAL_THEN (← q r"--(&1) pow p * s * x pow (SUC p) / &(SUC(SUC p)) =
                  &(SUC p) * s *
                  (&2 pow n * --(&1) pow p * x pow SUC p / &(SUC p)) /
                  (&2 pow n * &(SUC (SUC p)))")
      SUBST1_TAC THENL
       [REWRITE_TAC [real_div, ← GSYM REAL_MUL_ASSOC, REAL_INV_MUL] THEN
        ONCE_REWRITE_TAC [← AC REAL_MUL_AC
         (← q r"a * b * c * d * e * f * g * h =
        d * b * e * h * (g * c) * (f * a)")] THEN
        SIMP_TAC [REAL_MUL_LINV, REAL_POW_EQ_0, REAL_OF_NUM_EQ,
                 ARITH, NOT_SUC] THEN
        REWRITE_TAC [REAL_MUL_RID], ALL_TAC] THEN
      REWRITE_TAC [← GSYM REAL_SUB_LDISTRIB, REAL_ABS_MUL] THEN
      REWRITE_TAC [real_div, REAL_MUL_ASSOC, ← GSYM REAL_SUB_RDISTRIB] THEN
      REWRITE_TAC [REAL_ABS_MUL, ← GSYM REAL_MUL_ASSOC] THEN
      REWRITE_TAC [← GSYM real_div] THEN
      ONCE_REWRITE_TAC [← AC REAL_MUL_AC (← q r"a * b * c * d = (a * b * d) * c")] THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o REDEPTH_CONV)
                      [← GSYM REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q "abs (&(SUC p) * s * inv (&2 pow n * &(SUC (SUC p)))) * &3") THEN
      ASM_SIMP_TAC [REAL_LE_LMUL, REAL_ABS_POS] THEN
      REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_NUM, REAL_ABS_INV, REAL_ABS_POW] THEN
      REWRITE_TAC [REAL_INV_MUL] THEN
      REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN
      ONCE_REWRITE_TAC [← AC REAL_MUL_AC (← q r"a * b * c * d * e =
                                     (d * a) * (b * c) * e")] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q "inv(&1) * &3 / &4 * &3") THEN
      CONV_TAC (RAND_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC [] THEN
      REWRITE_TAC [REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC [REAL_OF_NUM_LE, ARITH] THEN
      ONCE_REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      SIMP_TAC [REAL_LE_MUL, REAL_LE_INV_EQ, REAL_POS,
               REAL_POW_LE, REAL_ABS_POS] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
        EXISTS_TAC (← q "&(SUC(SUC p))") THEN
        SIMP_TAC [REAL_MUL_ASSOC, REAL_MUL_RINV, REAL_OF_NUM_EQ, NOT_SUC] THEN
        REWRITE_TAC [REAL_INV_1, REAL_MUL_LID, REAL_MUL_RID] THEN
        REWRITE_TAC [REAL_OF_NUM_LT, REAL_OF_NUM_LE] THEN ARITH_TAC,
        MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN
        EXISTS_TAC (← q "&2 pow n") THEN REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN
        SIMP_TAC [REAL_MUL_LINV, REAL_POW_EQ_0, REAL_OF_NUM_EQ, ARITH_EQ] THEN
        SIMP_TAC [REAL_POW_LT, REAL_OF_NUM_LT, ARITH, REAL_MUL_RID] THEN
        MATCH_MP_TAC r4 THEN
        EXISTS_TAC (← q "&2 pow n * --x") THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC (← q "inv(&2 pow n)") THEN
        SIMP_TAC [REAL_LT_INV_EQ, REAL_POW_LT, REAL_OF_NUM_LT, ARITH] THEN
        REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_NEG, REAL_ABS_POW, REAL_ABS_NUM] THEN
        GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
        SIMP_TAC [REAL_MUL_ASSOC, REAL_MUL_LINV, REAL_POW_EQ_0, REAL_OF_NUM_EQ,
                 ARITH_EQ] THEN
        REWRITE_TAC [REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC (← q "&1 / &2") THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [real_div, REAL_SUB_RDISTRIB, ← GSYM REAL_MUL_ASSOC] THEN
        SIMP_TAC [REAL_MUL_RINV, REAL_POW_EQ_0, REAL_OF_NUM_EQ, ARITH_EQ] THEN
        REWRITE_TAC [REAL_MUL_LID, REAL_MUL_RID] THEN
        REWRITE_TAC [REAL_LE_SUB_LADD] THEN ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
        REWRITE_TAC [← GSYM REAL_LE_SUB_LADD] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN
        REWRITE_TAC [real_div, REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN
        REWRITE_TAC [REAL_OF_NUM_LT, ARITH] THEN
        SUBST1_TAC (← SYM (← ExceptT.mk (REAL_INT_REDUCE_CONV (← q r"&2 pow 2")))) THEN
        MATCH_MP_TAC REAL_POW_MONO THEN
        ASM_REWRITE_TAC [REAL_OF_NUM_LE, ARITH]],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"--(&1) pow p * s * x pow (SUC p) / &(SUC(SUC p)) -
    &2 pow n * --(&1) pow (SUC p) * x pow (SUC(SUC p)) / &(SUC(SUC p)) =
    (--(&1) pow p * x pow (SUC p) / &(SUC(SUC p))) *
    (s - &2 pow n * --x)")
    SUBST1_TAC THENL
     [REWRITE_TAC [real_pow, real_div, ← GSYM REAL_OF_NUM_SUC] THEN
      REWRITE_TAC [REAL_SUB_LDISTRIB, ← GSYM REAL_MUL_ASSOC] THEN
      REWRITE_TAC [REAL_MUL_LNEG, REAL_MUL_RNEG, REAL_MUL_LID] THEN
      REWRITE_TAC [REAL_NEG_NEG, REAL_MUL_AC], ALL_TAC] THEN
    ONCE_REWRITE_TAC [REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q "abs (-- (&1) pow p * x pow SUC p / &(SUC (SUC p))) * &1") THEN
    ASM_SIMP_TAC [REAL_LE_LMUL, REAL_ABS_POS, REAL_LT_IMP_LE] THEN
    REWRITE_TAC [REAL_MUL_RID, real_div, REAL_ABS_MUL, REAL_ABS_POW,
                REAL_ABS_NEG, REAL_ABS_NUM, REAL_ABS_INV] THEN
    REWRITE_TAC [REAL_POW_ONE, REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "inv(&2) pow 1 * inv(&2)") THEN
    CONJ_TAC THENL [ALL_TAC, CONV_TAC REAL_RAT_REDUCE_CONV] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    SIMP_TAC [REAL_ABS_POS, REAL_POW_LE,
             REAL_LE_INV_EQ, LE_0, REAL_OF_NUM_LE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "inv(&2) pow (SUC p)") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        ASM_REWRITE_TAC [REAL_ABS_POS],
        REWRITE_TAC [REAL_POW_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV, ALL_TAC] THEN
        MATCH_MP_TAC REAL_POW_MONO THEN
        REWRITE_TAC [REAL_OF_NUM_LE, ARITH] THEN ARITH_TAC],
      MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC [REAL_OF_NUM_LT, ARITH, REAL_OF_NUM_LE] THEN ARITH_TAC]))

  -- @@RETURN BEGIN
  return { STEPS_EXP_LEMMA, STEPS_EXP, STEPS_LN }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Special version of Taylor series for exponential in limited range.         -/
/- (calc_real.ml 1311-1476)                                                   -/
/- ------------------------------------------------------------------------- -/

structure TaylorExp where
  -- @@FIELDS
  MCLAURIN_EXP_LE1 : thm
  REAL_EXP_15 : thm
  TAYLOR_EXP_WEAK : thm
  REAL_EXP_13 : thm
  TAYLOR_EXP : thm
  TAYLOR_LN : thm
  deriving Inhabited

@[nospecialize]
def setupTaylorExp [HolBase] (D : CalcRealDeps) :
    ExceptT String IO TaylorExp := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, INDUCT_TAC, NUM_FACT_CONV, REAL_ARITH, REAL_ARITH_TAC,
        REAL_RAT_REDUCE_CONV, REAL_SUM_CONV, .. } := D
  let { ABS_N, ABS_NZ, ADD1, ADD_CLAUSES, ADD_SYM, ARITH, FACT, FACT_LT, LN_1, LT_0,
        MCLAURIN_EXP_LE, MCLAURIN_LN_POS, NOT_SUC, POW_0, REAL_ABS_0, REAL_ABS_INV,
        REAL_ABS_MUL, REAL_ABS_NEG, REAL_ABS_NUM, REAL_ABS_POS, REAL_ABS_POW,
        REAL_ADD_RID, REAL_EXP_ADD, REAL_EXP_BOUND_LEMMA, REAL_EXP_MONO_LE, .. } := D.core1
  let { REAL_EXP_POS_LE, REAL_INV_0, REAL_INV_1, REAL_INV_EQ_0, REAL_INV_MUL,
        REAL_INV_POS, REAL_LET_TRANS, REAL_LE_INV_EQ, REAL_LE_LMUL_IMP, REAL_LE_LT,
        REAL_LE_MUL, REAL_LE_MUL2, REAL_LE_REFL, REAL_LE_RMUL, REAL_LE_TRANS,
        REAL_LTE_TRANS, REAL_LT_IMP_LE, REAL_LT_INV2, REAL_LT_INV_EQ, REAL_LT_LMUL,
        REAL_LT_MUL, REAL_LT_RMUL_IMP, REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LNEG,
        REAL_MUL_LZERO, REAL_MUL_RID, REAL_MUL_RNEG, REAL_MUL_RZERO, REAL_NEG_NEG, .. } := D.core2
  let { REAL_OF_NUM_EQ, REAL_OF_NUM_LE, REAL_OF_NUM_LT, REAL_POS, REAL_POW_1_LE,
        REAL_POW_EQ_0, REAL_POW_INV, REAL_POW_LE, REAL_POW_LE2, REAL_POW_LT,
        REAL_POW_LT2, REAL_POW_ONE, REAL_POW_POW, REAL_SUB_LZERO, REAL_SUB_RZERO,
        SUM_0, SUM_DIFF, SUM_REINDEX, real_abs, real_div, real_pow, .. } := D.core3
  -- @@SCOPE END

  let MCLAURIN_EXP_LE1 ← prove
   r"!x n. abs(x) <= &1
         ==> ?t. abs(t) <= &1 /\
             (exp(x) = sum(0,n) (\m. x pow m / &(FACT m)) +
                       (exp(t) / &(FACT n)) * x pow n)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q "x:real", ← q "n:num"] MCLAURIN_EXP_LE) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "t:real") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q "t:real") THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "abs(x)") THEN
    ASM_REWRITE_TAC [])

  let REAL_EXP_15 ← prove
   r"exp(&1) < &5"
   (SUBST1_TAC (← SYM (← ExceptT.mk (REAL_RAT_REDUCE_CONV (← q r"inv(&2) + inv(&2)")))) THEN
    REWRITE_TAC [REAL_EXP_ADD] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC (← q "(&1 + &2 * inv(&2)) * (&1 + &2 * inv(&2))") THEN
    CONV_TAC (RAND_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC [] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC [REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC REAL_EXP_BOUND_LEMMA THEN
    CONV_TAC REAL_RAT_REDUCE_CONV)

  let TAYLOR_EXP_WEAK ← prove
   r"abs(x) <= &1 ==>
   abs(exp(x) - sum(0,m) (\i. x pow i / &(FACT i))) < &5 * inv(&(FACT m))"
   (← do
    let r1 ← REAL_ARITH (← q r"abs((x + y) - x) = abs(y)")
    pure (DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q "m:num") o MATCH_MP MCLAURIN_EXP_LE1) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "t:real") STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC [r1] THEN
    REWRITE_TAC [real_div, REAL_ABS_MUL, ← GSYM REAL_MUL_ASSOC] THEN
    ASM_CASES_TAC (← q "x = &0") THENL
     [ASM_REWRITE_TAC [] THEN
      SPEC_TAC (← q "m:num", ← q "m:num") THEN INDUCT_TAC THENL
       [REWRITE_TAC [real_pow, FACT, ABS_N, REAL_INV_1, REAL_MUL_RID] THEN
        ASM_REWRITE_TAC [real_abs, REAL_EXP_POS_LE] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC (← q "exp(&1)") THEN REWRITE_TAC [REAL_EXP_15] THEN
        REWRITE_TAC [REAL_EXP_MONO_LE] THEN
        UNDISCH_TAC (← q "abs(t) <= &1") THEN REAL_ARITH_TAC,
        REWRITE_TAC [POW_0, REAL_ABS_0, REAL_MUL_RZERO] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC [REAL_OF_NUM_LT, ARITH] THEN
        MATCH_MP_TAC REAL_INV_POS THEN
        REWRITE_TAC [REAL_OF_NUM_LT, FACT_LT]],
      MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC (← q "&5 * abs(inv(&(FACT m))) * abs(x pow m)") THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_RMUL_IMP THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q "abs(exp(&1))") THEN
          ASM_REWRITE_TAC [real_abs, REAL_EXP_POS_LE, REAL_EXP_MONO_LE,
                         REAL_EXP_15] THEN
          UNDISCH_TAC (← q "abs(t) <= &1") THEN REAL_ARITH_TAC,
          MATCH_MP_TAC REAL_LT_MUL THEN
          ASM_REWRITE_TAC [← GSYM ABS_NZ, REAL_POW_EQ_0] THEN
          REWRITE_TAC [REAL_INV_EQ_0, REAL_OF_NUM_EQ] THEN
          MP_TAC (← SPEC (← q "m:num") FACT_LT) THEN ARITH_TAC],
        MATCH_MP_TAC REAL_LE_LMUL_IMP THEN
        REWRITE_TAC [REAL_OF_NUM_LE, ARITH] THEN
        GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC [REAL_ABS_POS] THEN
        REWRITE_TAC [REAL_ABS_INV, ABS_N, REAL_LE_REFL] THEN
        REWRITE_TAC [REAL_ABS_POW] THEN
        MATCH_MP_TAC REAL_POW_1_LE THEN
        ASM_REWRITE_TAC [REAL_ABS_POS]]]))

  let REAL_EXP_13 ← prove
   r"exp(&1) < &3"
   (← do
    let r1 ← REAL_ARITH (← q r"b + e <= c ==> abs(a - b) < e ==> a < c")
    pure (MP_TAC (← INST [(← q "&1", ← q "x:real"), (← q "5", ← q "m:num")] TAYLOR_EXP_WEAK) THEN
    CONV_TAC (ONCE_DEPTH_CONV REAL_SUM_CONV) THEN
    REWRITE_TAC [ADD_CLAUSES] THEN
    CONV_TAC (ONCE_DEPTH_CONV NUM_FACT_CONV) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC r1 THEN
    CONV_TAC REAL_RAT_REDUCE_CONV))

  let TAYLOR_EXP ← prove
   r"abs(x) <= &1 ==>
   abs(exp(x) - sum(0,m) (\i. x pow i / &(FACT i))) < &3 * inv(&(FACT m))"
   (← do
    let r1 ← REAL_ARITH (← q r"abs((x + y) - x) = abs(y)")
    pure (DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q "m:num") o MATCH_MP MCLAURIN_EXP_LE1) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "t:real") STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC [r1] THEN
    REWRITE_TAC [real_div, REAL_ABS_MUL, ← GSYM REAL_MUL_ASSOC] THEN
    ASM_CASES_TAC (← q "x = &0") THENL
     [ASM_REWRITE_TAC [] THEN
      SPEC_TAC (← q "m:num", ← q "m:num") THEN INDUCT_TAC THENL
       [REWRITE_TAC [real_pow, FACT, ABS_N, REAL_INV_1, REAL_MUL_RID] THEN
        ASM_REWRITE_TAC [real_abs, REAL_EXP_POS_LE] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC (← q "exp(&1)") THEN REWRITE_TAC [REAL_EXP_13] THEN
        REWRITE_TAC [REAL_EXP_MONO_LE] THEN
        UNDISCH_TAC (← q "abs(t) <= &1") THEN REAL_ARITH_TAC,
        REWRITE_TAC [POW_0, REAL_ABS_0, REAL_MUL_RZERO] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC [REAL_OF_NUM_LT, ARITH] THEN
        MATCH_MP_TAC REAL_INV_POS THEN
        REWRITE_TAC [REAL_OF_NUM_LT, FACT_LT]],
      MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC (← q "&3 * abs(inv(&(FACT m))) * abs(x pow m)") THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_RMUL_IMP THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q "abs(exp(&1))") THEN
          ASM_REWRITE_TAC [real_abs, REAL_EXP_POS_LE, REAL_EXP_MONO_LE,
                          REAL_EXP_13] THEN
          UNDISCH_TAC (← q "abs(t) <= &1") THEN REAL_ARITH_TAC,
          MATCH_MP_TAC REAL_LT_MUL THEN
          ASM_REWRITE_TAC [← GSYM ABS_NZ, REAL_POW_EQ_0] THEN
          REWRITE_TAC [REAL_INV_EQ_0, REAL_OF_NUM_EQ] THEN
          MP_TAC (← SPEC (← q "m:num") FACT_LT) THEN ARITH_TAC],
        MATCH_MP_TAC REAL_LE_LMUL_IMP THEN
        REWRITE_TAC [REAL_OF_NUM_LE, ARITH] THEN
        GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC [REAL_ABS_POS] THEN
        REWRITE_TAC [REAL_ABS_INV, ABS_N, REAL_LE_REFL] THEN
        REWRITE_TAC [REAL_ABS_POW] THEN
        MATCH_MP_TAC REAL_POW_1_LE THEN
        ASM_REWRITE_TAC [REAL_ABS_POS]]]))

  let TAYLOR_LN ← prove
   r"&0 <= x /\ x <= inv(&2 pow k) ==>
   abs(ln(&1 + x) - sum(0,m) (\i. --(&1) pow i * x pow SUC i / &(SUC i)))
   < inv(&2 pow (k * SUC m) * &(SUC m))"
   (← do
    let lemma ← INST [(← q "1", ← q "k:num")] (← SYM (← SPEC_ALL SUM_REINDEX))
    pure (STRIP_TAC THEN
    UNDISCH_TAC (← q "&0 <= x") THEN REWRITE_TAC [REAL_LE_LT] THEN
    DISCH_THEN (DISJ_CASES_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THENL
     [ALL_TAC,
      REWRITE_TAC [real_pow, REAL_MUL_LZERO, REAL_MUL_RZERO, real_div] THEN
      REWRITE_TAC [SUM_0, REAL_ADD_RID, REAL_SUB_LZERO, LN_1] THEN
      REWRITE_TAC [REAL_ABS_NEG, REAL_ABS_0] THEN
      SIMP_TAC [REAL_LT_INV_EQ, REAL_LT_MUL, REAL_POW_LT, REAL_OF_NUM_LT,
               LT_0, ARITH]] THEN
    SUBGOAL_THEN (← q r"!i. --(&1) pow i = --(&1) pow (SUC(SUC i))")
     (fun th => ONCE_REWRITE_TAC [th]) THENL
     [REWRITE_TAC [real_pow, REAL_MUL_LNEG, REAL_MUL_RNEG, REAL_NEG_NEG] THEN
      REWRITE_TAC [REAL_MUL_LID], ALL_TAC] THEN
    REWRITE_TAC [ADD1, lemma] THEN
    REWRITE_TAC [ADD_CLAUSES] THEN
    ONCE_REWRITE_TAC [SUM_DIFF] THEN
    CONV_TAC (ONCE_DEPTH_CONV REAL_SUM_CONV) THEN
    REWRITE_TAC [real_div, REAL_INV_0, REAL_MUL_RZERO] THEN
    REWRITE_TAC [← GSYM ADD1] THEN
    MP_TAC (← SPECL [← q "x:real", ← q "SUC m"] MCLAURIN_LN_POS) THEN
    ASM_REWRITE_TAC [LT_0] THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN REWRITE_TAC [← GSYM ADD1] THEN
    REWRITE_TAC [← GSYM real_div] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "t:real") STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC [REAL_SUB_RZERO, ← REAL_ARITH (← q r"(a + b) - a = b")] THEN
    REWRITE_TAC [real_div, REAL_ABS_MUL, REAL_ABS_INV, REAL_ABS_POW] THEN
    REWRITE_TAC [REAL_ABS_NEG, REAL_ABS_NUM, REAL_POW_ONE] THEN
    REWRITE_TAC [REAL_MUL_LID, REAL_INV_MUL, ← GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC
     (← q "inv (&2 pow (k * SUC m)) * inv (&(SUC m)) * inv(abs(&1 + t) pow SUC m)") THEN
    CONJ_TAC THENL
     [REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      SIMP_TAC [REAL_LE_MUL, REAL_LE_INV_EQ, REAL_POS, REAL_ABS_POS,
               REAL_POW_LE] THEN
      REWRITE_TAC [← GSYM REAL_POW_INV] THEN
      REWRITE_TAC [← GSYM REAL_POW_POW] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_SIMP_TAC [REAL_POW_INV, real_abs, REAL_LT_IMP_LE],
      GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_RID] THEN
      REWRITE_TAC [REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LT_LMUL THEN
      SIMP_TAC [REAL_LT_MUL, REAL_LT_INV_EQ, REAL_OF_NUM_LT, LT_0, REAL_POW_LT,
               ARITH] THEN
      REWRITE_TAC [← GSYM REAL_POW_INV, ← GSYM REAL_ABS_INV] THEN
      SUBGOAL_THEN (← q "abs(inv(&1 + t)) < &1") ASSUME_TAC THENL
       [REWRITE_TAC [REAL_ABS_INV] THEN
        GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_INV_1] THEN
        MATCH_MP_TAC REAL_LT_INV2 THEN
        UNDISCH_TAC (← q "&0 < t") THEN REAL_ARITH_TAC,
        SUBST1_TAC (← SYM (← SPEC (← q "SUC m") REAL_POW_ONE)) THEN
        MATCH_MP_TAC REAL_POW_LT2 THEN
        ASM_REWRITE_TAC [REAL_POW_ONE, NOT_SUC, REAL_ABS_POS]]]))

  -- @@RETURN BEGIN
  return { MCLAURIN_EXP_LE1, REAL_EXP_15, TAYLOR_EXP_WEAK, REAL_EXP_13, TAYLOR_EXP,
           TAYLOR_LN }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Leading from the summation to the actual function; approximation           -/
/- theorems; eliminate trivial definitions.  (calc_real.ml 1478-1727)         -/
/- ------------------------------------------------------------------------- -/

structure Approx where
  -- @@FIELDS
  APPROX_LEMMA1 : thm
  APPROX_EXP : thm
  APPROX_LN : thm
  ELIMINATE_DEF : List term → thm → ExceptT String IO thm
  deriving Inhabited

@[nospecialize]
def setupApprox [HolBase] (D : CalcRealDeps) (BLemmas : Lemmas) (BStepsIter : StepsIter) (BTaylorExp : TaylorExp) :
    ExceptT String IO Approx := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, REAL_ARITH, REAL_ARITH_TAC, num_CONV, .. } := D
  let { ADD_ASSOC, ADD_CLAUSES, ADD_SYM, ARITH, BETA_THM, DE_MORGAN_THM, LE_ADD,
        REAL_ABS_SUB, .. } := D.core1
  let { REAL_INV_INV, REAL_INV_MUL, REAL_LET_ADD2, REAL_LE_INV2, REAL_LE_LCANCEL_IMP,
        REAL_LE_LMUL, REAL_LE_TRANS, REAL_LTE_TRANS, REAL_LT_IMP_LE, REAL_LT_INV_EQ,
        REAL_LT_LCANCEL_IMP, REAL_LT_LMUL, REAL_LT_POW2, REAL_MUL_2, REAL_MUL_ASSOC,
        REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_RID, REAL_MUL_RINV, REAL_MUL_SYM, .. } := D.core2
  let { REAL_OF_NUM_LE, REAL_POW_1, REAL_POW_ADD, REAL_POW_EQ_0, REAL_POW_MONO,
        REAL_SUB_LDISTRIB, real_abs, real_div, real_pow, .. } := D.core3
  let { REAL_ABS_LEMMA, .. } := BLemmas
  let { STEPS_EXP, STEPS_LN, .. } := BStepsIter
  let { TAYLOR_EXP, TAYLOR_LN, .. } := BTaylorExp
  -- @@SCOPE END

  let APPROX_LEMMA1 ← prove
   r"abs(f(x:real) - sum(0,m) (\i. P i x)) < inv(&2 pow (n + 2)) /\
   abs(u - &2 pow (n + e + 2) * sum(0,m) (\i. P i x)) <= &k * &m /\
   &k * &m <= &2 pow e /\
   abs(s * &2 pow (e + 2) - u) <= &2 pow (e + 1)
   ==> abs(s - &2 pow n * f(x)) < &1"
   (← do
    let r2 ← REAL_ARITH (← q r"abs(a - b) + abs(b - c) < d ==> abs(a - c) < d")
    let r1 ← REAL_ARITH (← q r"abs(a - b) + abs(b - c) < d ==> abs(a - c) < d")
    pure (STRIP_TAC THEN MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
    EXISTS_TAC (← q "&2 pow (n + e + 2)") THEN
    REWRITE_TAC [REAL_LT_POW2] THEN
    REWRITE_TAC [REAL_ABS_LEMMA, REAL_SUB_LDISTRIB, REAL_MUL_RID] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN (MATCH_MP_TAC o GEN_ALL) r1 THEN
    EXISTS_TAC (← q "&2 pow n * u") THEN
    CONV_TAC (funpow 4 RAND_CONV num_CONV) THEN
    REWRITE_TAC [ADD_CLAUSES, real_pow, REAL_MUL_2] THEN
    MATCH_MP_TAC REAL_LET_ADD2 THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC [REAL_POW_ADD] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
      REWRITE_TAC [← GSYM REAL_MUL_ASSOC, ← GSYM REAL_SUB_LDISTRIB] THEN
      REWRITE_TAC [← GSYM REAL_ABS_LEMMA] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC [REAL_LT_POW2],
      REWRITE_TAC [← GSYM REAL_MUL_ASSOC, ← GSYM REAL_SUB_LDISTRIB] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_POW_ADD] THEN
      REWRITE_TAC [← GSYM REAL_ABS_LEMMA] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN REWRITE_TAC [REAL_LT_POW2] THEN
      ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN (MATCH_MP_TAC o GEN_ALL) r2 THEN
      EXISTS_TAC
        (← q r"&2 pow (n + e + 2) * sum(0,m) (\i. P i (x:real))") THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_POW_ADD] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      REWRITE_TAC [REAL_POW_1, REAL_MUL_2] THEN
      MATCH_MP_TAC REAL_LET_ADD2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q "&k * &m") THEN
        ASM_REWRITE_TAC [],
        REWRITE_TAC [← GSYM REAL_SUB_LDISTRIB, ← GSYM REAL_ABS_LEMMA] THEN
        ONCE_REWRITE_TAC [ADD_SYM] THEN REWRITE_TAC [← GSYM ADD_ASSOC] THEN
        ONCE_REWRITE_TAC [REAL_POW_ADD] THEN
        REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN
        GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LT_LMUL THEN
        REWRITE_TAC [REAL_LT_POW2] THEN ONCE_REWRITE_TAC [ADD_SYM] THEN
        MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
        EXISTS_TAC (← q "inv(&2 pow (n + 2))") THEN
        REWRITE_TAC [REAL_LT_INV_EQ, REAL_LT_POW2] THEN
        REWRITE_TAC [REAL_MUL_RID, REAL_MUL_ASSOC] THEN
        ONCE_REWRITE_TAC [REAL_ABS_SUB] THEN
        SUBGOAL_THEN (← q "inv(&2 pow (n + 2)) * &2 pow (n + 2) = &1")
        (fun th => ASM_REWRITE_TAC [th, REAL_MUL_LID]) THEN
        MATCH_MP_TAC REAL_MUL_LINV THEN REWRITE_TAC [REAL_POW_EQ_0] THEN
        REWRITE_TAC [DE_MORGAN_THM] THEN DISJ1_TAC THEN REAL_ARITH_TAC]]))

  let APPROX_EXP ← prove
   r"(n + e + 2 = p) /\
   &3 * &2 pow (n + 2) <= &(FACT m) /\
   &2 * &m <= &2 pow e /\
   abs(x) <= &1 /\
   abs(s - &2 pow p * x) < &1 /\
   (t(0) = &2 pow p) /\
   (!k. SUC k < m ==>
                &2 * abs(t(SUC k) * &2 pow p * &(SUC k) - s * t(k))
                <= &2 pow p * &(SUC k)) /\
   abs(u * &2 pow (e + 2) - sum(0,m) t) <= &2 pow (e + 1)
   ==> abs(u - &2 pow n * exp(x)) < &1"
   (← do
    let r1 ← REAL_ARITH (← q r"~(&3 = &0)")
    pure (STRIP_TAC THEN MATCH_MP_TAC (← GEN_ALL APPROX_LEMMA1) THEN
    MAP_EVERY EXISTS_TAC
     [← q r"\i x. x pow i / &(FACT i)", ← q "2", ← q "m:num", ← q "sum(0,m) t", ← q "e:num"] THEN
    ASM_REWRITE_TAC [BETA_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q "&3 * inv(&(FACT m))") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC TAYLOR_EXP THEN ASM_REWRITE_TAC [],
        SUBST1_TAC (← SYM (← SPEC (← q "&3") REAL_INV_INV)) THEN
        REWRITE_TAC [← GSYM REAL_INV_MUL] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC [REAL_LT_POW2] THEN
        MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC (← q "&3") THEN
        REWRITE_TAC [REAL_MUL_ASSOC] THEN
        REWRITE_TAC [← MATCH_MP REAL_MUL_RINV r1] THEN
        ASM_REWRITE_TAC [REAL_MUL_LID] THEN REAL_ARITH_TAC],
      MATCH_MP_TAC STEPS_EXP THEN ASM_REWRITE_TAC []]))

  let APPROX_LN ← prove
   r"~(k = 0) /\
   (n + e + 2 = p) /\
   &2 pow (n + 2) <= &2 pow (k * SUC m) * &(SUC m) /\
   &3 * &m <= &2 pow e /\
   (&0 <= x /\ x <= inv(&2 pow k)) /\
   abs(s - &2 pow p * --x) < &1 /\
   (t(0) = --s) /\
   (!k. SUC k < m ==>
                &2 * abs(t(SUC k) * &2 pow p * &(SUC(SUC k)) -
                         &(SUC k) * s * t(k))
                <= &2 pow p * &(SUC(SUC k))) /\
   abs(u * &2 pow (e + 2) - sum(0,m) t) <= &2 pow (e + 1)
   ==> abs(u - &2 pow n * ln(&1 + x)) < &1"
   (STRIP_TAC THEN
    (MATCH_MP_TAC o GEN_ALL o BETA_RULE)
      (← INST [(← q r"\x. ln(&1 + x):real", ← q "f:real->real")] APPROX_LEMMA1) THEN
    MAP_EVERY EXISTS_TAC
     [← q r"\i x. (--(&1)) pow i * x pow (SUC i) / &(SUC i)",
      ← q "3", ← q "m:num", ← q "sum(0,m) t", ← q "e:num"] THEN
    ASM_REWRITE_TAC [BETA_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC (← q "inv(&2 pow (k * SUC m) * &(SUC m))") THEN CONJ_TAC THENL
       [MATCH_MP_TAC TAYLOR_LN THEN ASM_REWRITE_TAC [],
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC [REAL_LT_POW2]],
      MATCH_MP_TAC STEPS_LN THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q "2 <= (n + e + 2)") MP_TAC THENL
       [REWRITE_TAC [ADD_ASSOC] THEN ONCE_REWRITE_TAC [ADD_SYM] THEN
        REWRITE_TAC [LE_ADD],
        SUBGOAL_THEN (← q "abs(x) <= &1 / &2") (fun th => ASM_REWRITE_TAC [th]) THEN
        ASM_REWRITE_TAC [real_abs] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC (← q "inv(&2 pow k)") THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [real_div, REAL_MUL_LID] THEN
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [← GSYM REAL_POW_1] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC [REAL_LT_POW2] THEN
        MATCH_MP_TAC REAL_POW_MONO THEN
        REWRITE_TAC [REAL_OF_NUM_LE, ARITH] THEN
        UNDISCH_TAC (← q "~(k = 0)") THEN ARITH_TAC]])

  /- --------------------------------------------------------------------- -/
  /- Eliminate trivial definitions.                                        -/
  /- --------------------------------------------------------------------- -/

  -- `ELIMINATE_DEF` (calc_real.ml 1706-1721): its `x_tm`, `a_tm` and
  -- `sconv = REWRITE_CONV[ARITH]` are built once, closed over by the rule.
  let ELIMINATE_DEF : List term → thm → ExceptT String IO thm ← do
    let x_tm ← q "x:num"
    let a_tm ← q "&0"
    let sconv ← pure (REWRITE_CONV [ARITH])
    let mkEq ← ExceptT.mk (mk_eq : IO _)
    pure (fun tdefs th =>
      if tdefs == [] then pure th else do
        let ctm ← tdefs.foldrM (init := a_tm) (fun tm acc => do
            let (l0, r) ← liftExcept (dest_eq tm)
            let l ← liftExcept (rand l0)
            ExceptT.mk (HolCore.Classic.mk_cond (← liftExcept (mkEq (x_tm, l))) r acc))
        let atm ← liftExcept (mk_abs x_tm ctm)
        let ttm ← liftExcept (do rator (← lhs (← liftExcept (hd tdefs))))
        let tth ← ASSUME (← liftExcept (mkEq (ttm, atm)))
        let ths ← tdefs.mapM (fun d => do
          EQT_ELIM (← CONV_RULE (RAND_CONV sconv) (← ExceptT.mk (SUBS_CONV [tth] d))))
        let dth ← PROVE_HYP (← HolLight.end_itlist CONJ ths) th
        MP (← INST [(atm, ttm)] (← DISCH_ALL dth)) (REFL atm))


  -- @@RETURN BEGIN
  return { APPROX_LEMMA1, APPROX_EXP, APPROX_LN, ELIMINATE_DEF }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Overall conversion.                                                       -/
/- ------------------------------------------------------------------------- -/

/-- The two kinds of lazily-cached approximation function.  In OCaml a `raw`
    function is `num->num` and a `thm` function is `num->thm`, each paired
    with a mutable cell `ref(num(-1),y0)` holding the best approximation
    computed so far (its accuracy and value/theorem). -/
abbrev RawWrapped := IO.Ref (Rat × Rat) × (Rat → ExceptT String IO Rat)
/-- A `thm`-valued approximation function with its cache cell. -/
abbrev ThmWrapped := IO.Ref (Rat × thm) × (Rat → ExceptT String IO thm)

/-- `num n` (OCaml's `Num.num_of_int`): an integer as a `Rat`. -/
def num (n : Int) : Rat := Rat.ofInt n

/-- `floor_num` (OCaml's `Num.floor_num`), on `Rat`: the greatest integer
    `<= x`. -/
def floor_num (x : Rat) : Rat := Rat.ofInt (Int.fdiv x.num (Int.ofNat x.den))

/-- `minus_num` (OCaml's unary negation on `num`). -/
def minus_num (x : Rat) : Rat := -x

/-- `ndiv x y` (calc_real.ml, the earlier part; here on `Rat` as `num`):
    round `x/y` to the nearest integer, failing if `y` divides neither of the
    three candidates evenly enough. -/
def ndiv (x y : Rat) : Except String Rat := do
  let q := quo_num x y
  let r := x - (q * y)
  if abs_num (num_2 * r) ≤ abs_num y then pure q
  else if abs_num (num_2 * (r - y)) ≤ abs_num y then pure (q + num_1)
  else if abs_num (num_2 * (r + y)) ≤ abs_num y then pure (q - num_1)
  else
    let s := (string_of_num x) ++ " and " ++ (string_of_num y)
    failwith ("ndiv: " ++ s)

/-- `raw_wrap (f:num->num)` (calc_real.ml): pair `f` with a fresh cell. -/
def raw_wrap (f : Rat → ExceptT String IO Rat) : IO RawWrapped := do
  let r ← IO.mkRef (num (-1), num 0)
  pure (r, f)

/-- `raw_eval (r,f) n` (calc_real.ml): the `n`-bit approximation, from the
    cache cell if good enough (downgraded by `ndiv` from `n0` to `n`), else
    recomputed and cached. -/
def raw_eval (w : RawWrapped) (n : Rat) : ExceptT String IO Rat := do
  let (n0, y0) ← w.1.get
  if n ≤ n0 then liftExcept (ndiv y0 (power_num (num 2) (n0 - n)))
  else do
    let y ← w.2 n
    w.1.set (n, y)
    pure y

/-- `thm_wrap (f:num->thm)` (calc_real.ml): pair `f` with a fresh cell holding
    `TRUTH` as a placeholder theorem. -/
def thm_wrap [HolBase] (TRUTH : thm) (f : Rat → ExceptT String IO thm) : IO ThmWrapped := do
  let r ← IO.mkRef (num (-1), TRUTH)
  pure (r, f)

/-- The theorems, conversions, syntax and cache that `thm_eval`, the overall
    `REALCALC_CONV` recursion and its subconversions close over (the four names
    bound by the big OCaml tuple share one closure, so they share one
    context). -/
structure RCtx where
  TRUTH : thm
  -- the step theorems and lemmas (from Prev, before this range)
  REALCALC_DOWNGRADE : thm
  REALCALC_NEG : thm
  REALCALC_ABS : thm
  REALCALC_INV : thm
  REALCALC_ADD : thm
  REALCALC_MUL : thm
  REALCALC_SQRT : thm
  APPROX_EXP : thm
  APPROX_LN : thm
  -- the three locally-proved lemmas of the subconversions
  exp_pth : thm            -- `REALCALC_EXP_CONV`'s `pth`
  exp_left_zero : thm      -- `prove(`0 + n = n`,...)` for exp
  ln_pth : thm             -- `REALCALC_LN_CONV`'s `pth`
  ln_left_zero : thm       -- `prove(`0 + n = n`,...)` for ln
  sqrt_1le_pth : thm       -- `PROVE_1_LE_SQRT`'s `pth`
  -- `INTEGER_PROVE` (calc_real.ml): a derived rule
  INTEGER_PROVE : term → ExceptT String IO thm
  -- the terms the recursion matches operators against
  (a_tm n_tm n'_tm m_tm b_tm e_tm c_tm : term)
  (neg_tm abs_tm inv_tm sqrt_tm add_tm mul_tm sub_tm exp_tm ln_tm : term)
  (add1_tm pow2_tm one_tm lt_tm : term)
  -- `thm_eval`'s `SUC` and `mk_add` (calc_real.ml)
  SUC_tm : term
  mk_add : term → Except String (term → Except String term)
  -- the `t:num->real` of the exp/ln subconversions
  t_tm : term
  -- parsing conversions and syntax
  (NUM_SUC_CONV NUM_ADD_CONV NUM_REDUCE_CONV NUM_FACT_CONV : ioconv)
  (REAL_INT_NEG_CONV REAL_INT_ABS_CONV REAL_INT_MUL_CONV REAL_INT_SUB_CONV : ioconv)
  (REAL_INT_POW_CONV REAL_INT_LE_CONV REAL_INT_REDUCE_CONV : ioconv)
  (REAL_RAT_REDUCE_CONV REAL_SUM_CONV EXPAND_RANGE_CONV : ioconv)
  REAL_RAT_LE_CONV : ioconv
  mk_numeral : Rat → Except String term
  mk_realintconst : Rat → Except String term
  mk_small_numeral : Int → Except String term
  log2 : Rat → Rat
  ELIMINATE_DEF : List term → thm → ExceptT String IO thm
  -- `real_pow` (core; used by `thm_eval`).
  real_pow : thm
  -- `realcalc_cache = ref []` (calc_real.ml 1728): created once in the setup.
  realcalc_cache : IO.Ref (List (term × (RawWrapped × ThmWrapped)))

/-- `thm_eval (r,f) n` (calc_real.ml): the `n`-bit theorem, downgraded from a
    better cached one by `REALCALC_DOWNGRADE` and the real-int conversions, or
    recomputed and cached.  (The `SUC`, `mk_add` and conversions come from the
    context `C`.) -/
def thm_eval [HolBase] (C : RCtx) (w : ThmWrapped) (n : Rat) : ExceptT String IO thm := do
  let (n0, y0th) ← w.1.get
  if n ≤ n0 then
    if n == n0 then pure y0th else do
      let th1 ← ExceptT.mk (C.NUM_SUC_CONV
        (← mk_comb C.SUC_tm (← liftExcept (C.mk_numeral (n0 - (n + num 1))))))
      let th2 ← MATCH_MP C.REALCALC_DOWNGRADE th1
      let th3 ← ExceptT.mk (C.NUM_ADD_CONV
        (← liftExcept ((← liftExcept (C.mk_add (← liftExcept (C.mk_numeral n))))
                         (← liftExcept (C.mk_numeral (n0 - n))))))
      let th4 ← MATCH_MP th2 th3
      let th5 ← MATCH_MP th4 y0th
      let tm5 := (← liftExcept (dest_imp (concl th5))).1
      let (tm5a, tm5b) ← liftExcept (dest_comb tm5)
      let th6 ← ExceptT.mk (C.REAL_INT_POW_CONV tm5b)
      let tm5c ← liftExcept (do rand (← rand tm5a))
      let (tm5d, tm5e) ← liftExcept (dest_comb tm5c)
      let (tm5f, tm5g) ← liftExcept (dest_comb (← liftExcept (rand tm5d)))
      let _ := tm5g
      let tm5h ← liftExcept (do rand (← rand tm5f))
      let bin ← liftExcept (C.mk_realintconst
        (← ndiv (← dest_realintconst tm5e) (power_num (num 2) (← dest_numeral tm5h))))
      let th7 ← AP_TERM (← liftExcept (do rator (← rand tm5f))) th1
      let th8 ← GEN_REWRITE_RULE LAND_CONV [← CONJUNCT2 C.real_pow] th7
      let th9 ← SYM (← GEN_REWRITE_RULE (LAND_CONV o RAND_CONV) [th6] th8)
      let th10 ← TRANS th9 (← ExceptT.mk (C.REAL_INT_MUL_CONV (← liftExcept (rand (concl th9)))))
      let th11 ← AP_THM (← AP_TERM (← liftExcept (rator tm5f)) th10) bin
      let th12 ← TRANS th11 (← ExceptT.mk (C.REAL_INT_MUL_CONV (← liftExcept (rand (concl th11)))))
      let th13 ← AP_THM (← AP_TERM (← liftExcept (rator tm5d)) th12) tm5e
      let th14 ← TRANS th13 (← ExceptT.mk (C.REAL_INT_SUB_CONV (← liftExcept (rand (concl th13)))))
      let th15 ← AP_TERM (← liftExcept (do rator (← rand tm5a))) th14
      let th16 ← TRANS th15 (← ExceptT.mk (C.REAL_INT_ABS_CONV (← liftExcept (rand (concl th15)))))
      let th17 ← MK_COMB (← AP_TERM (← liftExcept (rator tm5a)) th16, th6)
      let th18 ← TRANS th17 (← ExceptT.mk (C.REAL_INT_LE_CONV (← liftExcept (rand (concl th17)))))
      MATCH_MP th5 (← EQT_ELIM th18)
  else do
    let yth ← w.2 n
    w.1.set (n, yth)
    pure yth

/- `real` arithmetic helper functions local to the subconversions. -/

/-- `REALCALC_EXP_CONV`'s `calculate_m acc i r` (calc_real.ml). -/
partial def expCalculateM (acc i r : Rat) : Rat :=
  if acc ≥ r then i else
    let i' := i + num 1
    expCalculateM (i' * acc) i' r

/-- `REALCALC_EXP_CONV`'s inner `calculate_exp_sequence p2 s i` (calc_real.ml). -/
partial def expSeqAux (p2 s i : Rat) : Except String (List Rat) := do
  if i < num 0 then pure []
  else if i == num 0 then pure [p2] else do
    let acc ← expSeqAux p2 s (i - num 1)
    let t ← hd acc
    let t' ← ndiv (s * t) (p2 * i)
    pure (t' :: acc)

/-- `REALCALC_EXP_CONV`'s `calculate_exp_sequence p s m` (calc_real.ml). -/
def expCalculateSequence (p s m : Rat) : Except String (List Rat) := do
  let p2 := power_num (num 2) p
  pure (rev (← expSeqAux p2 s (m - num 1)))

/-- `REALCALC_LN_CONV`'s `calculate_m acc k2 m r` (calc_real.ml). -/
partial def lnCalculateM (acc k2 m r : Rat) : Rat :=
  if acc * (m + num 1) ≥ r then m else
    lnCalculateM (k2 * acc) k2 (m + num 1) r

/-- `REALCALC_LN_CONV`'s inner `calculate_ln_sequence p2 s i` (calc_real.ml). -/
partial def lnSeqAux (p2 s i : Rat) : Except String (List Rat) := do
  if i < num 0 then pure []
  else if i == num 0 then pure [s] else do
    let acc ← lnSeqAux p2 s (i - num 1)
    let t ← hd acc
    let t' ← ndiv (num (-1) * s * t * i) (p2 * (i + num 1))
    pure (t' :: acc)

/-- `REALCALC_LN_CONV`'s `calculate_ln_sequence p s m` (calc_real.ml). -/
def lnCalculateSequence (p s m : Rat) : Except String (List Rat) := do
  let p2 := power_num (num 2) p
  pure (rev (← lnSeqAux p2 s (m - num 1)))

/-- `REALCALC_SQRT_CONV`'s `num_sqrt`'s inner `isolate_sqrt (a,b) y`
    (calc_real.ml): integer square root by bisection. -/
partial def isolateSqrt (a b y : Rat) : Rat :=
  if abs_num (a - b) ≤ num 1 then
    (if abs_num (a * a - y) ≤ a then a else b)
  else
    let c := quo_num (a + b) (num 2)
    if c * c ≤ y then isolateSqrt c b y
    else isolateSqrt a c y

/-- `REALCALC_SQRT_CONV`'s `num_sqrt n` (calc_real.ml). -/
def num_sqrt (n : Rat) : Rat := isolateSqrt (num 0) n n

/-- `find_msd` (calc_real.ml): least `n` with `1 < |raw_eval f n|`. -/
partial def findMsdAux [HolBase] (n : Rat) (f : RawWrapped) : ExceptT String IO Rat := do
  if num 1 < abs_num (← raw_eval f n) then pure n
  else findMsdAux (n + num 1) f
/-- `find_msd f` (calc_real.ml). -/
def find_msd [HolBase] (f : RawWrapped) : ExceptT String IO Rat := findMsdAux (num 0) f

/-- `find_acc`'s inner recursion (calc_real.ml): least `n` with
    `32 < |raw_eval f n|`. -/
partial def findAccAux [HolBase] (n : Rat) (f : RawWrapped) : ExceptT String IO Rat := do
  if num 32 < abs_num (← raw_eval f n) then pure n
  else findAccAux (n + num 1) f
/-- `find_acc f` (calc_real.ml). -/
def find_acc [HolBase] (f : RawWrapped) : ExceptT String IO Rat := findAccAux (num 0) f

/-- `find_ubound f` (calc_real.ml): an upper bound on `-log2` of the value. -/
def find_ubound [HolBase] (C : RCtx) (f : RawWrapped) : ExceptT String IO Rat := do
  let k ← find_acc f
  let a := abs_num (← raw_eval f k)
  pure (k - C.log2 (a + num 1))

/-- `REALCALC_EXP_CONV` (calc_real.ml): the approximation of `exp` by Taylor
    series.  `(fn1,fn2)` are the raw and theorem approximators of the
    argument; it returns the pair of approximators of `exp` of it.
    `mk_eq` is translated as the pure `safe_mk_eq`, as elsewhere. -/
def REALCALC_EXP_CONV [HolBase] (C : RCtx) (fn1 : RawWrapped) (fn2 : ThmWrapped) :
    ExceptT String IO (RawWrapped × ThmWrapped) := do
  let t_tm := C.t_tm
  let n_tm := C.n_tm
  let m_tm := C.m_tm
  let e_tm := C.e_tm
  let p_tm ← q r"p:num"
  let s_tm ← q r"s:real"
  let u_tm ← q r"u:real"
  let x_tm ← q r"x:real"
  let pth := C.exp_pth
  let LEFT_ZERO_RULE : thm → ExceptT String IO thm :=
    fun th => ONCE_REWRITE_RULE [C.exp_left_zero] th
  let raw_fn : Rat → ExceptT String IO Rat := fun n => do
    let m := expCalculateM (num 1) (num 0) (num 3 * (power_num (num 2) (n + num 2)))
    let e := C.log2 (num 2 * m)
    let p := n + e + num 2
    let s ← raw_eval fn1 p
    let seq ← liftExcept (expCalculateSequence p s m)
    let u0 := HolCore.Lib.itlist (· + ·) seq (num 0)
    liftExcept (ndiv u0 (power_num (num 2) (e + num 2)))
  let thm_fn : Rat → ExceptT String IO thm := fun n => do
    let m := expCalculateM (num 1) (num 0) (num 3 * (power_num (num 2) (n + num 2)))
    let e := C.log2 (num 2 * m)
    let p := n + e + num 2
    let sth ← thm_eval C fn2 p
    let tm1 ← liftExcept (do rand (← lhand (concl sth)))
    let s_num ← liftExcept (lhand tm1)
    let x_num ← liftExcept (do rand (← rand tm1))
    let s ← liftExcept (dest_realintconst s_num)
    let seq ← liftExcept (expCalculateSequence p s m)
    let u0 := HolCore.Lib.itlist (· + ·) seq (num 0)
    let u ← liftExcept (ndiv u0 (power_num (num 2) (e + num 2)))
    let m_num ← liftExcept (C.mk_numeral m)
    let n_num ← liftExcept (C.mk_numeral n)
    let e_num ← liftExcept (C.mk_numeral e)
    let p_num ← liftExcept (C.mk_numeral p)
    let u_num ← liftExcept (C.mk_realintconst u)
    let tdefs ← (List.zip (upto 0 ((seq.length : Int) - 1)) seq).mapM
      (fun (ab : Int × Rat) => do
        let atm ← liftExcept (C.mk_small_numeral ab.1)
        let lt ← liftExcept (mk_comb t_tm atm)
        pure (safe_mk_eq lt (← liftExcept (C.mk_realintconst ab.2))))
    let p2th ← ExceptT.mk (C.REAL_INT_POW_CONV (← mk_comb C.pow2_tm p_num))
    let th0 ← INST [(m_num, m_tm), (n_num, n_tm), (e_num, e_tm),
                    (x_num, x_tm), (p_num, p_tm), (s_num, s_tm), (u_num, u_tm)] pth
    let th0' ← MP th0 (← EQT_ELIM (← ExceptT.mk (C.REAL_RAT_REDUCE_CONV
      (← liftExcept (lhand (concl th0))))))
    let th1 ← MP th0' sth
    let th2 ← CONV_RULE (ONCE_DEPTH_CONV C.EXPAND_RANGE_CONV) th1
    let th3 ← LEFT_ZERO_RULE (← CONV_RULE (ONCE_DEPTH_CONV C.REAL_SUM_CONV) th2)
    let ths ← tryWith (do pure (CONJUNCTS (← ASSUME (← liftExcept (HolCore.Bool.list_mk_conj tdefs)))))
                      (pure [])
    let th4 ← SUBS (p2th :: ths) th3
    let th5 ← CONV_RULE (LAND_CONV
      (DEPTH_CONV C.NUM_ADD_CONV THENC
       ONCE_DEPTH_CONV C.NUM_FACT_CONV THENC
       C.REAL_INT_REDUCE_CONV)) th4
    MP (← C.ELIMINATE_DEF tdefs th5) C.TRUTH
  pure ((← (raw_wrap raw_fn : IO RawWrapped)), (← (thm_wrap C.TRUTH thm_fn : IO ThmWrapped)))

/-- `REALCALC_LN_CONV` (calc_real.ml): the approximation of `ln(&1 + x)` by its
    Taylor series.  `default_tdefs = [`t 0 = &0`]`. -/
def REALCALC_LN_CONV [HolBase] (C : RCtx) (fn1 : RawWrapped) (fn2 : ThmWrapped) :
    ExceptT String IO (RawWrapped × ThmWrapped) := do
  let t_tm := C.t_tm
  let n_tm := C.n_tm
  let m_tm := C.m_tm
  let e_tm := C.e_tm
  let p_tm ← q r"p:num"
  let s_tm ← q r"s:real"
  let u_tm ← q r"u:real"
  let k_tm ← q r"k:num"
  let x_tm ← q r"x:real"
  let pth := C.ln_pth
  let LEFT_ZERO_RULE : thm → ExceptT String IO thm :=
    fun th => ONCE_REWRITE_RULE [C.ln_left_zero] th
  let pow2_tm := C.pow2_tm
  let default_tdefs : List term := [← q r"t 0 = &0"]
  let raw_fn : Rat → ExceptT String IO Rat := fun n => do
    let k ← find_ubound C fn1
    if k < num 1 then failwith "ln of number not provably <= 1/2" else do
      let k2 := power_num (num 2) k
      let m := lnCalculateM k2 k2 (num 0) (power_num (num 2) (n + num 2))
      let e := C.log2 (num 3 * m)
      let p := n + e + num 2
      let s ← raw_eval fn1 p
      let seq ← liftExcept (lnCalculateSequence p s m)
      let u0 := HolCore.Lib.itlist (· + ·) seq (num 0)
      liftExcept (ndiv u0 (power_num (num 2) (e + num 2)))
  let thm_fn : Rat → ExceptT String IO thm := fun n => do
    let k ← find_ubound C fn1
    if k < num 1 then failwith "ln of number not provably <= 1/2" else do
      let k2 := power_num (num 2) k
      let m := lnCalculateM k2 k2 (num 0) (power_num (num 2) (n + num 2))
      let e := C.log2 (num 3 * m)
      let p := n + e + num 2
      let sth ← thm_eval C fn2 p
      let tm1 ← liftExcept (do rand (← lhand (concl sth)))
      let s_num ← liftExcept (lhand tm1)
      let x_num ← liftExcept (do rand (← rand tm1))
      let s ← liftExcept (dest_realintconst s_num)
      let seq ← liftExcept (lnCalculateSequence p s m)
      let u0 := HolCore.Lib.itlist (· + ·) seq (num 0)
      let u ← liftExcept (ndiv u0 (power_num (num 2) (e + num 2)))
      let m_num ← liftExcept (C.mk_numeral m)
      let n_num ← liftExcept (C.mk_numeral n)
      let e_num ← liftExcept (C.mk_numeral e)
      let p_num ← liftExcept (C.mk_numeral p)
      let k_num ← liftExcept (C.mk_numeral k)
      let u_num ← liftExcept (C.mk_realintconst u)
      let tdefs0 ← (List.zip (upto 0 ((seq.length : Int) - 1)) seq).mapM
        (fun (ab : Int × Rat) => do
          let atm ← liftExcept (C.mk_small_numeral ab.1)
          let lt ← liftExcept (mk_comb t_tm atm)
          pure (safe_mk_eq lt (← liftExcept (C.mk_realintconst ab.2))))
      let tdefs := if tdefs0 == [] then default_tdefs else tdefs0
      let p2th ← ExceptT.mk (C.REAL_INT_POW_CONV (← mk_comb pow2_tm p_num))
      let th0 ← INST [(m_num, m_tm), (n_num, n_tm), (e_num, e_tm), (k_num, k_tm),
                      (x_num, x_tm), (p_num, p_tm), (s_num, s_tm), (u_num, u_tm)] pth
      let th0' ← MP th0 (← EQT_ELIM (← ExceptT.mk (C.REAL_RAT_REDUCE_CONV
        (← liftExcept (lhand (concl th0))))))
      let th1 ← MP th0' sth
      let th2 ← CONV_RULE (ONCE_DEPTH_CONV C.EXPAND_RANGE_CONV) th1
      let th3 ← LEFT_ZERO_RULE (← CONV_RULE (ONCE_DEPTH_CONV C.REAL_SUM_CONV) th2)
      let ths ← tryWith (do pure (CONJUNCTS (← ASSUME (← liftExcept (HolCore.Bool.list_mk_conj tdefs)))))
                        (pure [])
      let th4 ← SUBS (p2th :: ths) th3
      let th5 ← CONV_RULE (LAND_CONV
        (C.NUM_REDUCE_CONV THENC C.REAL_INT_REDUCE_CONV)) th4
      MP (← C.ELIMINATE_DEF tdefs th5) C.TRUTH
  pure ((← (raw_wrap raw_fn : IO RawWrapped)), (← (thm_wrap C.TRUTH thm_fn : IO ThmWrapped)))

/-- `REALCALC_SQRT_CONV` (calc_real.ml): the approximation of `sqrt`.
    `num_sqrt` is defined above; `PROVE_1_LE_SQRT` proves `&1 <= x` goals via
    `sqrt_1le_pth` and `REAL_RAT_LE_CONV`. -/
def REALCALC_SQRT_CONV [HolBase] (C : RCtx) (fn1 : RawWrapped) (fn2 : ThmWrapped) :
    ExceptT String IO (RawWrapped × ThmWrapped) := do
  let MATCH_pth : thm → ExceptT String IO thm := fun th => MATCH_MP C.REALCALC_SQRT th
  let b_tm := C.b_tm
  -- `PROVE_1_LE_SQRT tm = try prove(tm,tac) with Failure _ -> failwith ...`.
  let PROVE_1_LE_SQRT : term → ExceptT String IO thm := fun tm => do
    let tac := REPEAT (MATCH_MP_TAC C.sqrt_1le_pth) THEN CONV_TAC C.REAL_RAT_LE_CONV
    tryWith (ExceptT.mk (HolCore.Tactics.prove HolLight.HolBase.B tm tac))
            (failwith "Need root body >= &1")
  let raw_fn : Rat → ExceptT String IO Rat := fun n => do
    pure (num_sqrt (power_num (num 2) n * (← raw_eval fn1 n)))
  let thm_fn : Rat → ExceptT String IO thm := fun n => do
    let th1 ← MATCH_pth (← thm_eval C fn2 n)
    let th2 ← MP th1 (← PROVE_1_LE_SQRT (← liftExcept (lhand (concl th1))))
    let th3 ← CONV_RULE (funpow 2 LAND_CONV
      (funpow 2 RAND_CONV C.REAL_RAT_REDUCE_CONV)) th2
    let k ← liftExcept (do dest_realintconst (← rand (← rand (← lhand (← lhand (concl th3))))))
    let th4 ← INST [(← liftExcept (C.mk_realintconst (num_sqrt k)), b_tm)] th3
    MP th4 (← EQT_ELIM (← ExceptT.mk (C.REAL_RAT_REDUCE_CONV (← liftExcept (lhand (concl th4))))))
  pure ((← (raw_wrap raw_fn : IO RawWrapped)), (← (thm_wrap C.TRUTH thm_fn : IO ThmWrapped)))

/-- `REALCALC_CONV tm` (calc_real.ml): the overall recursion, returning the
    raw and theorem approximators of the real-valued term `tm`.  Looks `tm`
    up in `realcalc_cache` first.  (The `assoc`/cache lookup uses term
    equality via `BEq`.) -/
partial def REALCALC_CONV [HolBase] (C : RCtx) (tm : term) :
    ExceptT String IO (RawWrapped × ThmWrapped) := do
  match assoc tm (← C.realcalc_cache.get) with
  | .ok res => pure res
  | .error _ =>
  if is_ratconst tm then do
    let x ← liftExcept (rat_of_term tm)
    let raw_fn : Rat → ExceptT String IO Rat := fun acc =>
      pure (floor_num ((power_num (num 2) acc) * x))
    let thm_fn : Rat → ExceptT String IO thm := fun acc => do
      let a := floor_num ((power_num (num 2) acc) * x)
      let atm ← liftExcept (C.mk_realintconst a)
      let rtm ← mk_comb (← mk_comb C.mul_tm (← mk_comb C.pow2_tm (← liftExcept (C.mk_numeral acc)))) tm
      let btm ← mk_comb C.abs_tm (← mk_comb (← mk_comb C.sub_tm atm) rtm)
      let ftm ← mk_comb (← mk_comb C.lt_tm btm) C.one_tm
      EQT_ELIM (← ExceptT.mk (C.REAL_RAT_REDUCE_CONV ftm))
    pure ((← (raw_wrap raw_fn : IO RawWrapped)), (← (thm_wrap C.TRUTH thm_fn : IO ThmWrapped)))
  else do
  let (lop, r) ← liftExcept (dest_comb tm)
  if lop == C.neg_tm then do
    let (rfn, tfn) ← REALCALC_CONV C r
    let raw_fn : Rat → ExceptT String IO Rat := fun acc => do
      pure (minus_num (← raw_eval rfn acc))
    let thm_fn : Rat → ExceptT String IO thm := fun acc => do
      let th1 ← thm_eval C tfn acc
      let th2 ← MATCH_MP C.REALCALC_NEG th1
      tryWith (EQ_MP (← ExceptT.mk ((LAND_CONV (RAND_CONV (LAND_CONV C.REAL_INT_NEG_CONV)))
                                      (concl th2))) th2)
              (pure th2)
    pure ((← (raw_wrap raw_fn : IO RawWrapped)), (← (thm_wrap C.TRUTH thm_fn : IO ThmWrapped)))
  else if lop == C.abs_tm then do
    let (rfn, tfn) ← REALCALC_CONV C r
    let raw_fn : Rat → ExceptT String IO Rat := fun acc => do
      pure (abs_num (← raw_eval rfn acc))
    let thm_fn : Rat → ExceptT String IO thm := fun acc => do
      let th1 ← thm_eval C tfn acc
      let th2 ← MATCH_MP C.REALCALC_ABS th1
      CONV_RULE (LAND_CONV (RAND_CONV (LAND_CONV C.REAL_INT_ABS_CONV))) th2
    pure ((← (raw_wrap raw_fn : IO RawWrapped)), (← (thm_wrap C.TRUTH thm_fn : IO ThmWrapped)))
  else if lop == C.sqrt_tm then do
    let (rfn, tfn) ← REALCALC_CONV C r
    REALCALC_SQRT_CONV C rfn tfn
  else if lop == C.inv_tm then do
    let (rfn, tfn) ← REALCALC_CONV C r
    let x0 ← raw_eval rfn (num 0)
    let ax0 := abs_num x0
    let rr := C.log2 ax0 - num 1
    -- `get_ek(acc)`
    let get_ek : Rat → ExceptT String IO (Rat × Rat) := fun acc => do
      if rr < num 0 then do
        let p ← find_msd rfn
        let e := acc + p + num 1
        let k := e + p
        pure (e, k)
      else do
        let k := (let k0 := acc + num 1 - (num 2 * rr)
                  if k0 < num 0 then num 0 else k0)
        let e := rr + k
        pure (e, k)
    let raw_fn : Rat → ExceptT String IO Rat := fun acc => do
      let (_, k) ← get_ek acc
      let nk2 := power_num (num 2) (acc + k)
      liftExcept (ndiv nk2 (← raw_eval rfn k))
    let thm_fn : Rat → ExceptT String IO thm := fun acc => do
      let (e, k) ← get_ek acc
      let nk2 := power_num (num 2) (acc + k)
      let th1 ← thm_eval C tfn k
      let atm ← liftExcept (do lhand (← rand (← lhand (concl th1))))
      let a ← liftExcept (dest_realintconst atm)
      let b ← liftExcept (ndiv nk2 a)
      let btm ← liftExcept (C.mk_realintconst b)
      let etm ← liftExcept (C.mk_numeral e)
      let ntm ← liftExcept (C.mk_numeral acc)
      let th2 ← MATCH_MP C.REALCALC_INV th1
      let th3 ← INST [(btm, C.b_tm), (etm, C.e_tm), (ntm, C.n_tm)] th2
      let th4 ← MP th3 (← C.INTEGER_PROVE (← liftExcept (lhand (concl th3))))
      let th5 ← MP th4 (← C.INTEGER_PROVE (← liftExcept (lhand (concl th4))))
      let th6 ← MP th5 (← EQT_ELIM (← ExceptT.mk (C.NUM_REDUCE_CONV (← liftExcept (lhand (concl th5))))))
      let th7 ← MP th6 (← EQT_ELIM (← ExceptT.mk (C.REAL_INT_REDUCE_CONV (← liftExcept (lhand (concl th6))))))
      MP th7 (← EQT_ELIM (← ExceptT.mk
        ((LAND_CONV (funpow 4 RAND_CONV C.NUM_ADD_CONV) THENC C.REAL_INT_REDUCE_CONV)
          (← liftExcept (lhand (concl th7))))))
    pure ((← (raw_wrap raw_fn : IO RawWrapped)), (← (thm_wrap C.TRUTH thm_fn : IO ThmWrapped)))
  else if lop == C.exp_tm then do
    let (rfn, tfn) ← REALCALC_CONV C r
    REALCALC_EXP_CONV C rfn tfn
  else if lop == C.ln_tm then do
    let (r1, r2) ← liftExcept (dest_comb r)
    if r1 == C.add1_tm then do
      let (rfn, tfn) ← REALCALC_CONV C r2
      REALCALC_LN_CONV C rfn tfn
    else
      failwith "Can only do logs like ln(&1 + x) for small rational x"
  else do
  let (op, l) ← liftExcept (dest_comb lop)
  if op == C.add_tm then do
    let (rfn1, tfn1) ← REALCALC_CONV C l
    let (rfn2, tfn2) ← REALCALC_CONV C r
    let raw_fn : Rat → ExceptT String IO Rat := fun acc => do
      let acc' := acc + num 2
      liftExcept (ndiv ((← raw_eval rfn1 acc') + (← raw_eval rfn2 acc')) (num 4))
    let thm_fn : Rat → ExceptT String IO thm := fun acc => do
      let acc' := acc + num 2
      let th1 ← INST [(← liftExcept (C.mk_numeral acc), C.n_tm)] C.REALCALC_ADD
      let th2 ← MATCH_MP th1 (← ExceptT.mk (C.NUM_ADD_CONV (← liftExcept (do lhand (← lhand (concl th1))))))
      let th3 ← thm_eval C tfn1 acc'
      let th4 ← MATCH_MP th2 th3
      let th5 ← thm_eval C tfn2 acc'
      let th6 ← MATCH_MP th4 th5
      let n1 ← liftExcept (do dest_realintconst (← lhand (← rand (← lhand (concl th3)))))
      let n2 ← liftExcept (do dest_realintconst (← lhand (← rand (← lhand (concl th5)))))
      let ci ← liftExcept (C.mk_realintconst (← ndiv (n1 + n2) (num 4)))
      let th7 ← INST [(ci, C.c_tm)] th6
      let th8 ← EQT_ELIM (← ExceptT.mk (C.REAL_INT_REDUCE_CONV (← liftExcept (lhand (concl th7)))))
      MP th7 th8
    pure ((← (raw_wrap raw_fn : IO RawWrapped)), (← (thm_wrap C.TRUTH thm_fn : IO ThmWrapped)))
  else if op == C.mul_tm then do
    let (rfn1, tfn1) ← REALCALC_CONV C l
    let (rfn2, tfn2) ← REALCALC_CONV C r
    let get_kl : Rat → ExceptT String IO (Rat × Rat) := fun acc => do
      let n' := acc + num 2
      let rq := quo_num n' (num 2)
      let s := n' - rq
      let p := C.log2 (abs_num (← raw_eval rfn1 rq))
      let qq := C.log2 (abs_num (← raw_eval rfn2 s))
      let k := qq + rq + num 1
      let l := p + s + num 1
      if p == num 0 && qq == num 0 then
        (if k < l then pure (k + num 1, l) else pure (k, l + num 1))
      else pure (k, l)
    let raw_fn : Rat → ExceptT String IO Rat := fun acc => do
      let (k, l) ← get_kl acc
      let m := (k + l) - acc
      liftExcept (ndiv ((← raw_eval rfn1 k) * (← raw_eval rfn2 l)) (power_num (num 2) m))
    let thm_fn : Rat → ExceptT String IO thm := fun acc => do
      let (k, l) ← get_kl acc
      let m := (k + l) - acc
      let th1a ← thm_eval C tfn1 k
      let th1b ← thm_eval C tfn2 l
      let a ← liftExcept (do dest_realintconst (← lhand (← rand (← lhand (concl th1a)))))
      let b ← liftExcept (do dest_realintconst (← lhand (← rand (← lhand (concl th1b)))))
      let c ← liftExcept (ndiv (a * b) (power_num (num 2) m))
      let ntm ← liftExcept (C.mk_numeral acc)
      let mtm ← liftExcept (C.mk_numeral m)
      let ctm ← liftExcept (C.mk_realintconst c)
      let th1 ← MATCH_MP C.REALCALC_MUL th1a
      let th2 ← MATCH_MP th1 th1b
      let th3 ← INST [(ntm, C.n_tm), (mtm, C.m_tm), (ctm, C.c_tm)] th2
      let th4 ← MP th3 (← EQT_ELIM (← ExceptT.mk (C.NUM_REDUCE_CONV (← liftExcept (lhand (concl th3))))))
      let th5 ← MP th4 (← EQT_ELIM (← ExceptT.mk (C.REAL_INT_REDUCE_CONV (← liftExcept (lhand (concl th4))))))
      MP th5 (← EQT_ELIM (← ExceptT.mk (C.REAL_INT_REDUCE_CONV (← liftExcept (lhand (concl th5))))))
    pure ((← (raw_wrap raw_fn : IO RawWrapped)), (← (thm_wrap C.TRUTH thm_fn : IO ThmWrapped)))
  else failwith "No other operators work yet, sorry!"

/- ------------------------------------------------------------------------- -/
/- Apply some conversion before doing approximation.                         -/
/- ------------------------------------------------------------------------- -/

/-- `REALCALC_PRECONV conv tm` (calc_real.ml): apply `conv` to `tm`, approximate
    the right-hand side, and rewrite each theorem back with `SYM th`. -/
def REALCALC_PRECONV [HolBase] (C : RCtx) (conv : ioconv) (tm : term) :
    ExceptT String IO (RawWrapped × ThmWrapped) := do
  let th ← ExceptT.mk (conv tm)
  let (rfn, tfn) ← REALCALC_CONV C (← liftExcept (rand (concl th)))
  let thm_fn : Rat → ExceptT String IO thm := fun n => do
    let th1 ← thm_eval C tfn n
    GEN_REWRITE_RULE (LAND_CONV o funpow 3 RAND_CONV) [← SYM th] th1
  pure (rfn, (← (thm_wrap C.TRUTH thm_fn : IO ThmWrapped)))

/- ------------------------------------------------------------------------- -/
/- Calculate ordering relation between two expressions.                      -/
/- ------------------------------------------------------------------------- -/

/-- The `find_n` of `realcalc_rel_conv` and `REALCALC_REL_CONV` (calc_real.ml):
    least `n >= 1` where the two approximations differ by at least `4`. -/
partial def findNRel [HolBase] (rfn1 rfn2 : RawWrapped) (n : Rat) :
    ExceptT String IO Rat := do
  if n > num 1000 then failwith "realcalc_rel_conv: too close to discriminate"
  else if abs_num ((← raw_eval rfn1 n) - (← raw_eval rfn2 n)) ≥ num 4 then pure n
  else findNRel rfn1 rfn2 (n + num 1)


/-- The bundle for the overall conversion and the relation conversions
    (calc_real.ml 1728-2293).  `REALCALC_CONV`, `thm_eval`, `raw_eval`,
    `thm_wrap` are the four names of the big OCaml tuple; the rest are the
    relation theorems and conversions. -/
structure Overall where
  /-- `realcalc_cache` (1728); `Option` (always `some`) so the bundle can
      derive `Inhabited`, as Pocklington's `prime_theorem_cache`. -/
  realcalc_cache : Option (IO.Ref (List (term × (RawWrapped × ThmWrapped))))
  REALCALC_CONV : term → ExceptT String IO (RawWrapped × ThmWrapped)
  thm_eval : ThmWrapped → Rat → ExceptT String IO thm
  raw_eval : RawWrapped → Rat → ExceptT String IO Rat
  thm_wrap : (Rat → ExceptT String IO thm) → IO ThmWrapped
  REALCALC_PRECONV : ioconv → term → ExceptT String IO (RawWrapped × ThmWrapped)
  REALCALC_LT : thm
  REALCALC_LE : thm
  REALCALC_GT : thm
  REALCALC_GE : thm
  REALCALC_EQ : thm
  realcalc_rel_conv : term → ExceptT String IO Bool
  REALCALC_REL_CONV : term → ExceptT String IO thm
  deriving Inhabited

@[nospecialize]
def setupOverall [HolBase] (D : CalcRealDeps) (BStepsDown : StepsDown) (BStepsInv : StepsInv) (BStepsAddMul : StepsAddMul) (BSqrt : Sqrt) (BExpandRange : ExpandRange) (BApprox : Approx) :
    ExceptT String IO Overall := do
  -- @@SCOPE BEGIN
  let { NUM_ADD_CONV, NUM_FACT_CONV, NUM_REDUCE_CONV, NUM_SUC_CONV, REAL_ARITH,
        REAL_ARITH_TAC, REAL_INT_ABS_CONV, REAL_INT_LE_CONV, REAL_INT_MUL_CONV,
        REAL_INT_NEG_CONV, REAL_INT_POW_CONV, REAL_INT_REDUCE_CONV, REAL_INT_SUB_CONV,
        REAL_RAT_LE_CONV, REAL_RAT_REDUCE_CONV, REAL_SUM_CONV, mk_numeral,
        mk_realintconst, mk_small_numeral, .. } := D
  let { ADD_CLAUSES, ARITH, CONJ_SYM, EQ_TRANS, EXISTS_OR_THM, EXISTS_REFL, POW_2,
        REAL_ABS_SUB, REAL_EQ_NEG2, .. } := D.core1
  let { REAL_LE_LMUL_EQ, REAL_LT_LMUL_EQ, REAL_LT_MUL2, REAL_MUL_LID, REAL_MUL_RNEG,
        REAL_NEG_NEG, REAL_NOT_LE, .. } := D.core2
  let { REAL_OF_NUM_EQ, REAL_OF_NUM_LT, REAL_POW_LT, SQRT_POS_LE, SQRT_POW2, TRUTH,
        real_ge, real_gt, real_pow, .. } := D.core3
  let { REALCALC_ABS, REALCALC_DOWNGRADE, REALCALC_NEG, .. } := BStepsDown
  let { REALCALC_INV, .. } := BStepsInv
  let { REALCALC_ADD, REALCALC_MUL, .. } := BStepsAddMul
  let { REALCALC_SQRT, .. } := BSqrt
  let { EXPAND_RANGE_CONV, .. } := BExpandRange
  let { APPROX_EXP, APPROX_LN, ELIMINATE_DEF, .. } := BApprox
  -- @@SCOPE END
  -- `realcalc_cache = ref []` (calc_real.ml 1728): created once, here.
  let realcalc_cache : IO.Ref (List (term × (RawWrapped × ThmWrapped))) ← IO.mkRef []

  -- The operator and variable constants (calc_real.ml, head of the big `let`).
  let a_tm ← q r"a:real"
  let n_tm ← q r"n:num"
  let n'_tm ← q r"n':num"
  let m_tm ← q r"m:num"
  let b_tm ← q r"b:real"
  let e_tm ← q r"e:num"
  let c_tm ← q r"c:real"
  let neg_tm ← q r"(--)"
  let abs_tm ← q r"abs"
  let inv_tm ← q r"inv"
  let sqrt_tm ← q r"sqrt"
  let add_tm ← q r"(+)"
  let mul_tm ← q r"(*)"
  let sub_tm ← q r"(-)"
  let exp_tm ← q r"exp:real->real"
  let ln_tm ← q r"ln:real->real"
  let add1_tm ← q r"(+) (&1)"
  let pow2_tm ← q r"(pow) (&2)"
  let one_tm ← q r"&1"
  let lt_tm ← q r"(<)"

  -- `INTEGER_PROVE = EQT_ELIM o REWRITE_CONV[...]` (calc_real.ml).
  let INTEGER_PROVE : term → ExceptT String IO thm := fun tm => do
    let g ← GSYM EXISTS_REFL
    EQT_ELIM (← ExceptT.mk (REWRITE_CONV
      [REAL_EQ_NEG2, g, EXISTS_OR_THM, REAL_OF_NUM_EQ] tm))

  -- `thm_eval`'s `SUC` and `mk_add` (calc_real.ml).
  let SUC_tm ← q r"SUC"
  let plus_num_tm ← q r"(+):num->num->num"
  let mk_add : term → Except String (term → Except String term) :=
    fun t => mk_binop plus_num_tm t
  let t_tm ← q r"t:num->real"

  -- The subconversions' local lemmas (`pth`, `prove(`0 + n = n`,...)`).
  let exp_pth ← prove
   r"abs(x) <= &1 ==>
       abs(s - &2 pow p * x) < &1 ==>
       (n + e + 2 = p) /\
       &3 * &2 pow (n + 2) <= &(FACT m) /\
       &2 * &m <= &2 pow e /\
       (t(0) = &2 pow p) /\
       (!k. SUC k < m ==>
                    &2 * abs(t(SUC k) * &2 pow p * &(SUC k) - s * t(k))
                    <= &2 pow p * &(SUC k)) /\
       abs(u * &2 pow (e + 2) - sum(0,m) t) <= &2 pow (e + 1)
       ==> abs(u - &2 pow n * exp(x)) < &1"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC APPROX_EXP THEN
    ASM_REWRITE_TAC [])
  let exp_left_zero ← prove
   r"0 + n = n"
   (REWRITE_TAC [ADD_CLAUSES])
  let ln_pth ← prove
   r"&0 <= x /\ x <= inv(&2 pow k) ==>
       abs(s - &2 pow p * x) < &1 ==>
       ~(k = 0) /\
       (n + e + 2 = p) /\
       &2 pow (n + 2) <= &2 pow (k * SUC m) * &(SUC m) /\
       &3 * &m <= &2 pow e /\
       (t(0) = s) /\
       (!k. SUC k < m ==>
                    &2 * abs(t(SUC k) * &2 pow p * &(SUC(SUC k)) -
                             &(SUC k) * --s * t(k))
                    <= &2 pow p * &(SUC(SUC k))) /\
       abs(u * &2 pow (e + 2) - sum(0,m) t) <= &2 pow (e + 1)
       ==> abs(u - &2 pow n * ln(&1 + x)) < &1"
   (← do
    let a ← REAL_ARITH (← q r"abs(--a - --b) = abs(a - b)")
    let i ← INST [(← q r"--s", ← q r"s:real")] APPROX_LN
    pure (REPEAT STRIP_TAC THEN MATCH_MP_TAC i THEN
      ASM_REWRITE_TAC [REAL_NEG_NEG] THEN
      REWRITE_TAC [REAL_MUL_RNEG] THEN
      REWRITE_TAC [a] THEN
      ASM_REWRITE_TAC []))
  let ln_left_zero ← prove
   r"0 + n = n"
   (REWRITE_TAC [ADD_CLAUSES])
  let sqrt_1le_pth ← prove
   r"&1 <= x ==> &1 <= sqrt(x)"
   (← do
    let a0 ← REAL_ARITH (← q r"&1 <= x ==> &0 <= x")
    pure (DISCH_THEN (fun th => tactic_of do
        pure (ASSUME_TAC (← MATCH_MP a0 th) THEN MP_TAC th)) THEN
      CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC [REAL_NOT_LE] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN (← q r"x = sqrt(x) pow 2") SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC [SQRT_POW2],
        GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_LID] THEN
        REWRITE_TAC [POW_2] THEN MATCH_MP_TAC REAL_LT_MUL2 THEN
        ASM_SIMP_TAC [SQRT_POS_LE]]))

  -- The shared context the four tuple names and subconversions close over.
  let C : RCtx :=
    { TRUTH := TRUTH,
      REALCALC_DOWNGRADE := REALCALC_DOWNGRADE, REALCALC_NEG := REALCALC_NEG,
      REALCALC_ABS := REALCALC_ABS, REALCALC_INV := REALCALC_INV,
      REALCALC_ADD := REALCALC_ADD, REALCALC_MUL := REALCALC_MUL,
      REALCALC_SQRT := REALCALC_SQRT, APPROX_EXP := APPROX_EXP, APPROX_LN := APPROX_LN,
      exp_pth, exp_left_zero, ln_pth, ln_left_zero, sqrt_1le_pth,
      INTEGER_PROVE,
      a_tm, n_tm, n'_tm, m_tm, b_tm, e_tm, c_tm,
      neg_tm, abs_tm, inv_tm, sqrt_tm, add_tm, mul_tm, sub_tm, exp_tm, ln_tm,
      add1_tm, pow2_tm, one_tm, lt_tm,
      SUC_tm, mk_add, t_tm,
      NUM_SUC_CONV, NUM_ADD_CONV, NUM_REDUCE_CONV, NUM_FACT_CONV,
      REAL_INT_NEG_CONV, REAL_INT_ABS_CONV, REAL_INT_MUL_CONV, REAL_INT_SUB_CONV,
      REAL_INT_POW_CONV, REAL_INT_LE_CONV, REAL_INT_REDUCE_CONV,
      REAL_RAT_REDUCE_CONV, REAL_SUM_CONV, EXPAND_RANGE_CONV, REAL_RAT_LE_CONV,
      mk_numeral, mk_realintconst, mk_small_numeral,
      log2, ELIMINATE_DEF, real_pow, realcalc_cache }

  -- The four names bound by the OCaml tuple (named `_v` locally so they do
  -- not shadow the top-level recursion `REALCALC_CONV`/`thm_eval`).
  let REALCALC_CONV_v : term → ExceptT String IO (RawWrapped × ThmWrapped) :=
    fun tm => REALCALC_CONV C tm
  let thm_eval_v : ThmWrapped → Rat → ExceptT String IO thm := fun w n => thm_eval C w n
  let raw_eval_v : RawWrapped → Rat → ExceptT String IO Rat := fun w n => raw_eval w n
  let thm_wrap_v : (Rat → ExceptT String IO thm) → IO ThmWrapped :=
    fun f => thm_wrap C.TRUTH f

  -- `REALCALC_PRECONV` (calc_real.ml 2069-2076).
  let REALCALC_PRECONV_v : ioconv → term → ExceptT String IO (RawWrapped × ThmWrapped) :=
    fun conv tm => REALCALC_PRECONV C conv tm

  -- The ordering lemmas (calc_real.ml 2082-2117).
  let REALCALC_LT ← prove
   r"abs(a - &2 pow n * x) < &1 /\ abs(b - &2 pow n * y) < &1
   ==> &2 <= abs(a - b) ==> (x < y <=> a < b)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"&2 pow n * x < &2 pow n * y") THEN CONJ_TAC THENL
     [SIMP_TAC [REAL_LT_LMUL_EQ, REAL_POW_LT, REAL_OF_NUM_LT, ARITH],
      POP_ASSUM_LIST (MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC])

  let REALCALC_LE ← prove
   r"abs(a - &2 pow n * x) < &1 /\ abs(b - &2 pow n * y) < &1
   ==> &2 <= abs(a - b) ==> (x <= y <=> a <= b)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"&2 pow n * x <= &2 pow n * y") THEN CONJ_TAC THENL
     [SIMP_TAC [REAL_LE_LMUL_EQ, REAL_POW_LT, REAL_OF_NUM_LT, ARITH],
      POP_ASSUM_LIST (MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC])

  let REALCALC_GT ← prove
   r"abs(a - &2 pow n * x) < &1 /\ abs(b - &2 pow n * y) < &1
   ==> &2 <= abs(a - b) ==> (x > y <=> a > b)"
   (ONCE_REWRITE_TAC [CONJ_SYM, REAL_ABS_SUB] THEN
    REWRITE_TAC [real_gt, REALCALC_LT])

  let REALCALC_GE ← prove
   r"abs(a - &2 pow n * x) < &1 /\ abs(b - &2 pow n * y) < &1
   ==> &2 <= abs(a - b) ==> (x >= y <=> a >= b)"
   (ONCE_REWRITE_TAC [CONJ_SYM, REAL_ABS_SUB] THEN
    REWRITE_TAC [real_ge, REALCALC_LE])

  let REALCALC_EQ ← prove
   r"abs(a - &2 pow n * x) < &1 /\ abs(b - &2 pow n * y) < &1
   ==> &2 <= abs(a - b) ==> ((x = y) <=> F)"
   (ASM_CASES_TAC (← q r"x:real = y") THEN ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC)

  -- `realcalc_rel_conv` (calc_real.ml 2124-2147).
  let pops : List (term × (Rat → Rat → Bool)) :=
    [(← q r"(<)", fun a b => decide (a < b)), (← q r"(<=)", fun a b => decide (a ≤ b)),
     (← q r"(>)", fun a b => decide (a > b)), (← q r"(>=)", fun a b => decide (a ≥ b)),
     (← q r"(=):real->real->bool", fun a b => a == b)]
  let find_n_rel : RawWrapped → RawWrapped → Rat → ExceptT String IO Rat :=
    findNRel
  let «realcalc_rel_conv» : term → ExceptT String IO Bool := fun tm => do
    let (lop, r) ← liftExcept (dest_comb tm)
    let (op, l) ← liftExcept (dest_comb lop)
    let pop ← tryWith (liftExcept (assoc op pops))
                      (failwith "realcalc_rel_conv: unknown operator")
    let (rfn1, _tfn1) ← REALCALC_CONV C l
    let (rfn2, _tfn2) ← REALCALC_CONV C r
    let n ← find_n_rel rfn1 rfn2 (num 1)
    pure (pop (← raw_eval rfn1 n) (← raw_eval rfn2 n))

  -- `REALCALC_REL_CONV` (calc_real.ml 2153-2175).
  let pths : List (term × thm) :=
    [(← q r"(<)", REALCALC_LT), (← q r"(<=)", REALCALC_LE),
     (← q r"(>)", REALCALC_GT), (← q r"(>=)", REALCALC_GE),
     (← q r"(=):real->real->bool", REALCALC_EQ)]
  let «REALCALC_REL_CONV» : term → ExceptT String IO thm := fun tm => do
    let (lop, r) ← liftExcept (dest_comb tm)
    let (op, l) ← liftExcept (dest_comb lop)
    let pth ← tryWith (liftExcept (assoc op pths))
                      (failwith "realcalc_rel_conv: unknown operator")
    let (rfn1, tfn1) ← REALCALC_CONV C l
    let (rfn2, tfn2) ← REALCALC_CONV C r
    let n ← find_n_rel rfn1 rfn2 (num 1)
    let th1 ← thm_eval C tfn1 n
    let th2 ← thm_eval C tfn2 n
    let th3 ← MATCH_MP pth (← CONJ th1 th2)
    let th4 ← MP th3 (← EQT_ELIM (← ExceptT.mk (REAL_INT_REDUCE_CONV (← liftExcept (lhand (concl th3))))))
    CONV_RULE (RAND_CONV REAL_RAT_REDUCE_CONV) th4

  return {
    realcalc_cache := some realcalc_cache,
    REALCALC_CONV := REALCALC_CONV_v, thm_eval := thm_eval_v, raw_eval := raw_eval_v,
    thm_wrap := thm_wrap_v, REALCALC_PRECONV := REALCALC_PRECONV_v,
    REALCALC_LT, REALCALC_LE, REALCALC_GT, REALCALC_GE, REALCALC_EQ,
    realcalc_rel_conv := «realcalc_rel_conv», REALCALC_REL_CONV := «REALCALC_REL_CONV» }

end HolLibrary.CalcReal
