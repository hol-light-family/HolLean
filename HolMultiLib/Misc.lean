/- ========================================================================= -/
/- Various convenient background stuff not specifically to do with R^n.      -/
/- ========================================================================= -/
/- File: HolMultiLib/Misc.lean

  Original (c) Copyright, John Harrison 1998-2008
  Original (c) Copyright, Marco Maggesi 2014
  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Multivariate/misc.ml`, in the style of
  HolLibrary (see HolLibrary/Prime.lean for the conventions and
  HolMath/Base.lean for the tactic surface): pure, the proofs translated by
  hand, one `let` per OCaml `let`, in file order.  What misc.ml uses from the
  core library, from Library/card.ml and from Library/floor.ml is passed in
  `MiscDeps`; SessionMultiLib/Misc.lean supplies it.

  misc.ml's `needs "Library/card.ml"` and `needs "Library/floor.ml"` are the
  wiring's imports, and its `prioritize_real()` (misc.ml 10) is run by the
  wiring before the first bundle.  The other load-time effects are made where
  misc.ml makes them: the `real_interval` overloads (346-349) and the `hull`
  (575) and `relative_to` (1346) infixes, each just before the definition
  that uses it.
-/

import HolMath

open HolCore HolCore.Lib
open HolCore.Kernel hiding ASSUME INST
open HolCore.Equal (ioconv lhs lhand)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolLight HolLight.Syntax

namespace HolMultiLib.Misc

set_option maxHeartbeats 1000000

/- ------------------------------------------------------------------------- -/
/- What misc.ml uses from the core library (supplied by Session).            -/
/- (Three structures, each under 128 fields; see HolLibrary/Floor.lean.)     -/
/- ------------------------------------------------------------------------- -/

/-- Core theorems misc.ml uses, ADD1 to IN_CROSS. -/
structure CoreThms1 where
  (ADD1 ADD_ASSOC ADD_CLAUSES ADD_SUB ADD_SUB2 AND_FORALL_THM ARBITRARY
   ARBITRARY_UNION_OF_IDEMPOT ARBITRARY_UNION_OF_UNIONS ARITH ARITH_EQ
   ARITH_EVEN BIJECTIVE_LEFT_RIGHT_INVERSE CARD_EQ_0 CARD_EQ_BIJECTIONS_SPECIAL
   CARD_NUMSEG_1 CART_EQ COMPL_COMPL CONJ_ASSOC CONJ_SYM CONTRAPOS_THM CROSS
   DEPENDENT_CHOICE DE_MORGAN_THM DIMINDEX_FINITE_PROD DIMINDEX_GE_1 DISJOINT
   DISJOINT_SYM DIVISION DIV_UNIQ EMPTY_SUBSET EMPTY_UNIONS EQ_IMP EQ_SYM_EQ
   EQ_TRANS ETA_AX EVEN_ADD EVEN_EXISTS EVEN_MULT EVEN_OR_ODD EXISTS_IN_GSPEC
   EXISTS_IN_IMAGE EXISTS_PAIR_THM EXP EXP_ADD EXTENSION FINITE_EMPTY
   FINITE_IMAGE FINITE_INDUCT_STRONG FINITE_INSERT FINITE_INTERSECTION_OF_INC
   FINITE_INTERSECTION_OF_INTERS FINITE_NUMSEG FINITE_NUMSEG_LT FINITE_RESTRICT
   FINITE_RULES FINITE_SING FINITE_SUBSET FINITE_UNION FORALL_AND_THM
   FORALL_INTERSECTION_OF FORALL_IN_GSPEC FORALL_IN_IMAGE FORALL_IN_IMAGE_2
   FORALL_IN_INSERT FORALL_PAIR_THM FORALL_UNWIND_THM2 FUNCTION_FACTORS_LEFT
   FUN_EQ_THM FUN_IN_IMAGE GE IMAGE_CLAUSES IMAGE_CONST IMAGE_EQ IMAGE_EQ_EMPTY
   IMAGE_SUBSET IMAGE_o IMP_CONJ IMP_CONJ_ALT IMP_IMP IN INFINITE_DIFF_FINITE
   INFINITE_ENUMERATE INFINITE_IMAGE INFINITE_SUPERSET INFINITE_UNIV_PAIR
   INJECTIVE_ON_ALT INJECTIVE_ON_LEFT_INVERSE INSERT_SUBSET INTERSECTION_OF
   INTERSECTION_OF_INC INTERS_0 INTERS_1 INTERS_2 INTERS_GSPEC INTERS_IMAGE
   INTERS_INSERT INTER_INTERS INTER_SUBSET INTER_UNIONS INTER_UNIV IN_CROSS : thm)

/-- Core theorems misc.ml uses, IN_DELETE to REAL_LT_RMUL_EQ. -/
structure CoreThms2 where
  (IN_DELETE IN_DIFF IN_ELIM_PAIR_THM IN_ELIM_THM IN_IMAGE IN_INSERT IN_INTER
   IN_INTERS IN_NUMSEG IN_SING IN_UNION IN_UNIV ITERATE_EXPAND_CASES LAMBDA_BETA
   LE LEFT_ADD_DISTRIB LEFT_EXISTS_AND_THM LEFT_IMP_EXISTS_THM LET_TRANS LE_0
   LE_1 LE_ADD_LCANCEL LE_CASES LE_EXISTS LE_LT LE_MULT_LCANCEL LE_MULT_RCANCEL
   LE_REFL LE_TRANS LT LTE_TRANS LT_CASES LT_IMP_LE LT_LE LT_NZ LT_REFL
   LT_SUC_LE LT_TRANS MOD_UNIQ MONO_AND MONO_EXISTS MONO_FORALL MULT_ASSOC
   MULT_CLAUSES NEUTRAL_REAL_ADD NOT_EXISTS_THM NOT_FORALL_THM NOT_IMP
   NOT_INSERT_EMPTY NOT_IN_EMPTY NOT_LT NOT_SUC NUMSEG_EMPTY ODD_EXISTS
   OR_EXISTS_THM PAIRWISE_CHAIN_UNIONS PAIRWISE_EMPTY PAIRWISE_INSERT PAIR_EQ
   RDIV_LT_EQ REAL_ABS_MUL REAL_ABS_NEG REAL_ABS_NUM REAL_ADD_LDISTRIB
   REAL_ADD_LID REAL_ADD_SYM REAL_ARCH REAL_ARCH_INV REAL_COMPLETE REAL_DIV_LMUL
   REAL_DIV_POW2 REAL_ENTIRE REAL_EQ_LCANCEL_IMP REAL_EQ_NEG2 REAL_INF_LE_FINITE
   REAL_LET_ANTISYM REAL_LET_TRANS REAL_LE_ADD REAL_LE_ANTISYM REAL_LE_LT
   REAL_LE_MUL REAL_LE_NEG2 REAL_LE_RDIV_EQ REAL_LE_REFL REAL_LE_RMUL
   REAL_LE_TOTAL REAL_LE_TRANS REAL_LTE_TRANS REAL_LT_01 REAL_LT_ANTISYM
   REAL_LT_DIV2_EQ REAL_LT_IMP_LE REAL_LT_INF_FINITE REAL_LT_INV_EQ
   REAL_LT_LDIV_EQ REAL_LT_LE REAL_LT_MIN REAL_LT_NEG2 REAL_LT_POW2
   REAL_LT_RDIV_EQ REAL_LT_REFL REAL_LT_RMUL_EQ : thm)

/-- Core theorems misc.ml uses, REAL_LT_SQUARE_ABS to support, and the list
    theorems (lists.ml). -/
structure CoreThms3 where
  (REAL_LT_SQUARE_ABS REAL_LT_TOTAL REAL_LT_TRANS REAL_MUL_ASSOC REAL_MUL_LID
   REAL_MUL_LZERO REAL_MUL_RID REAL_MUL_RZERO REAL_MUL_SYM REAL_NOT_LE
   REAL_NOT_LT REAL_OF_NUM_ADD REAL_OF_NUM_EQ REAL_OF_NUM_LE REAL_OF_NUM_LT
   REAL_OF_NUM_MUL REAL_OF_NUM_POW REAL_OF_NUM_SUC REAL_POS REAL_POW_2
   REAL_POW_ADD REAL_POW_EQ_0 REAL_POW_LT2 REAL_POW_ONE REAL_SHRINK_GALOIS
   REAL_SHRINK_GROW REAL_SHRINK_LE REAL_SHRINK_RANGE REAL_SUB_0
   REAL_SUB_RDISTRIB REAL_SUP_LT_FINITE REAL_SUP_UNIQUE RIGHT_EXISTS_AND_THM
   RIGHT_FORALL_IMP_THM RIGHT_IMP_EXISTS_THM RIGHT_IMP_FORALL_THM
   RIGHT_OR_EXISTS_THM SIMPLE_IMAGE SIMPLE_IMAGE_GEN SKOLEM_THM SUBSET
   SUBSET_ANTISYM SUBSET_ANTISYM_EQ SUBSET_DIFF SUBSET_EMPTY SUBSET_INTERS
   SUBSET_REFL SUBSET_TRANS SUBSET_UNION SUBSET_UNIV SUB_ADD SUM_ABS SUM_CLAUSES
   SUM_CLAUSES_LEFT SUM_CLAUSES_NUMSEG SUM_CONST_NUMSEG SUM_LE SUM_LMUL
   SUM_LT_ALL SUM_OFFSET SUM_OFFSET_0 SUM_RESTRICT_SET SUM_RMUL SUM_SUB
   SUM_TRIV_NUMSEG SWAP_EXISTS_THM SWAP_FORALL_THM TRANSITIVE_STEPWISE_LE
   TRANSITIVE_STEPWISE_LT UNIONS_0 UNIONS_1 UNIONS_2 UNIONS_GSPEC UNIONS_INSERT
   UNIONS_SUBSET UNION_OF UNION_OF_INC UNION_OF_MONO UNION_SUBSET UNIV_NOT_EMPTY
   UNWIND_THM1 UNWIND_THM2 WLOG_LE WLOG_LT le_c num_CASES num_INDUCTION
   num_INFINITE num_RECURSION num_WOP numseg o_ASSOC o_THM pairwise real_div
   real_pow sum support
   EL_LIST_OF_SEQ LENGTH_EQ_NIL LENGTH_LIST_OF_SEQ LIST_EQ LIST_OF_SEQ_EQ_NIL
   NOT_CONS_NIL : thm)

/-- The theorems misc.ml uses from Library/card.ml and Library/floor.ml. -/
structure LibThms where
  (CARD_DIFF_ABSORB CARD_EQ_IMP_LE CARD_EQ_LIST CARD_EQ_REAL CARD_EQ_REFL
   CARD_EQ_SYM CARD_EQ_TRANS CARD_EXP_CONG CARD_EXP_MUL CARD_EXP_UNIV
   CARD_LE_ANTISYM CARD_LE_EXP_LEFT CARD_LE_IMAGE CARD_LE_SUBSET CARD_LE_TRANS
   CARD_LTE_TRANS CARD_MUL_CONG CARD_SQUARE_NUM COUNTABLE_ALT COUNTABLE_AS_IMAGE
   COUNTABLE_AS_IMAGE_SUBSET COUNTABLE_CART COUNTABLE_CROSS COUNTABLE_EMPTY
   COUNTABLE_IMAGE COUNTABLE_IMAGE_INJ_EQ COUNTABLE_INSERT COUNTABLE_INTER
   COUNTABLE_INTERSECTION_OF_INC COUNTABLE_INTERSECTION_OF_INTERS COUNTABLE_LIST
   COUNTABLE_PRODUCT_DEPENDENT COUNTABLE_SUBSET COUNTABLE_SUBSET_NUM
   COUNTABLE_UNION COUNTABLE_UNION_OF_INC EQ_C_BIJECTIONS FINITE_CARD_LT
   MUL_C_UNIV NUM_COUNTABLE UNCOUNTABLE_REAL exp_c mul_c
   INTEGER_CASES INTEGER_CLOSED RATIONAL_APPROXIMATION
   RATIONAL_APPROXIMATION_STRADDLE RATIONAL_CLOSED rational : thm)

/-- The decision procedures, rules, conversions and parser operations misc.ml
    uses from hol.ml's library.  Rules that can fail are in `ExceptT`. -/
structure MiscDeps where
  -- definitions and parser state
  new_definition : String → ExceptT String IO thm
  define : String → ExceptT String IO thm
  parse_as_infix : String × (Int × String) → IO Unit
  make_overloadable : String → hol_type → ExceptT String IO Unit
  overload_interface : String → term → ExceptT String IO Unit
  prove_recursive_functions_exist : thm → term → ExceptT String IO thm
  -- decision procedures
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_ARITH_TAC : tactic
  ASM_MESON_TAC : List thm → tactic
  ASM_METIS_TAC : List thm → tactic
  ASM_REAL_ARITH_TAC : tactic
  INDUCT_TAC : tactic
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  METIS_TAC : List thm → tactic
  REAL_ARITH : term → ExceptT String IO thm
  REAL_ARITH_TAC : tactic
  REAL_FIELD : term → ExceptT String IO thm
  REAL_RING : term → ExceptT String IO thm
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  -- conversions
  CNF_CONV : ioconv
  HAS_SIZE_CONV : ioconv
  NNFC_CONV : ioconv
  NUM_REDUCE_CONV : ioconv
  REAL_RAT_REDUCE_CONV : ioconv
  num_CONV : ioconv
  SELECT_CONV : ioconv
  -- theorems
  core1 : CoreThms1
  core2 : CoreThms2
  core3 : CoreThms3
  lib : LibThms

/- ------------------------------------------------------------------------- -/
/- A couple of extra tactics used in some proofs below.  (misc.ml 16-20)     -/
/- ------------------------------------------------------------------------- -/

/-- `ASSERT_TAC tm = SUBGOAL_THEN tm STRIP_ASSUME_TAC` (misc.ml 16). -/
def ASSERT_TAC [HolBase] (tm : term) : tactic :=
  SUBGOAL_THEN tm STRIP_ASSUME_TAC

/-- `EQ_TRANS_TAC tm` (misc.ml 19). -/
def EQ_TRANS_TAC [HolBase] (D : MiscDeps) (tm : term) : tactic :=
  MATCH_MP_TAC D.core1.EQ_TRANS THEN EXISTS_TAC tm THEN CONJ_TAC

/- ------------------------------------------------------------------------- -/
/- Miscellaneous lemmas, and solvability of small systems of equations.      -/
/- (misc.ml 26-311)                                                           -/
/- ------------------------------------------------------------------------- -/

structure Lemmas where
  FORALL_DIFF : thm
  EXISTS_DIFF : thm
  FORALL_DIFF_ALT : thm
  FORALL_DIFF_GEN : thm
  GE_REFL : thm
  FORALL_SUC : thm
  SEQ_MONO_LEMMA : thm
  REAL_HALF : thm
  ABS_SQUARE_LT_1 : thm
  ABS_SQUARE_LE_1 : thm
  ABS_SQUARE_EQ_1 : thm
  UPPER_BOUND_FINITE_SET : thm
  UPPER_BOUND_FINITE_SET_REAL : thm
  LOWER_BOUND_FINITE_SET : thm
  LOWER_BOUND_FINITE_SET_REAL : thm
  REAL_CONVEX_SUM_BOUND_LE : thm
  REAL_CONVEX_SUM_BOUND_LT : thm
  APPROACHABLE_LT_LE : thm
  REAL_LE_BETWEEN : thm
  REAL_LET_BETWEEN : thm
  REAL_LTE_BETWEEN : thm
  REAL_LT_BETWEEN : thm
  REAL_LT_BETWEEN_GEN : thm
  TRIANGLE_LEMMA : thm
  LAMBDA_SKOLEM : thm
  EPSILON_DELTA_MINIMAL : thm
  HAS_SIZE_1_EXISTS : thm
  LINEAR_EQUATIONS_1_EQ : thm
  LINEAR_EQUATIONS_2_EQ : thm
  deriving Inhabited

@[nospecialize]
def setupLemmas [HolBase] (D : MiscDeps) : ExceptT String IO Lemmas := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, ASM_METIS_TAC, ASM_REAL_ARITH_TAC, HAS_SIZE_CONV, MESON,
        MESON_TAC, METIS_TAC, REAL_ARITH, REAL_ARITH_TAC, REAL_FIELD,
        REAL_RAT_REDUCE_CONV, REAL_RING, SET_RULE, SET_TAC, .. } := D
  let { ARITH, ARITH_EQ, COMPL_COMPL, CONJ_SYM, CONTRAPOS_THM, DE_MORGAN_THM,
        EQ_IMP, EXISTS_IN_IMAGE, EXTENSION, FINITE_IMAGE, FINITE_INDUCT_STRONG,
        FINITE_RESTRICT, FORALL_IN_GSPEC, FORALL_IN_IMAGE, GE, IMAGE_EQ_EMPTY,
        IMP_CONJ_ALT, IMP_IMP, .. } := D.core1
  let { IN_ELIM_THM, IN_INSERT, IN_SING, ITERATE_EXPAND_CASES, LAMBDA_BETA,
        LEFT_IMP_EXISTS_THM, LE_CASES, LE_REFL, LE_TRANS, NEUTRAL_REAL_ADD,
        NOT_IN_EMPTY, NOT_SUC, REAL_ABS_MUL, REAL_ABS_NUM, REAL_ADD_LID,
        REAL_ADD_SYM, REAL_ENTIRE, REAL_INF_LE_FINITE, REAL_LET_TRANS,
        REAL_LE_ADD, REAL_LE_LT, REAL_LE_MUL, REAL_LE_RDIV_EQ, REAL_LE_REFL,
        REAL_LE_RMUL, REAL_LE_TOTAL, REAL_LE_TRANS, REAL_LTE_TRANS, REAL_LT_01,
        REAL_LT_IMP_LE, REAL_LT_INF_FINITE, REAL_LT_LDIV_EQ, REAL_LT_RDIV_EQ,
        REAL_LT_RMUL_EQ, .. } := D.core2
  let { REAL_LT_SQUARE_ABS, REAL_LT_TRANS, REAL_MUL_LZERO, REAL_MUL_RID,
        REAL_MUL_RZERO, REAL_NOT_LE, REAL_NOT_LT, REAL_OF_NUM_LT, REAL_POW_2,
        REAL_POW_LT2, REAL_SUB_RDISTRIB, REAL_SUP_LT_FINITE,
        RIGHT_IMP_EXISTS_THM, SKOLEM_THM, SUBSET_DIFF, SUM_ABS, SUM_CLAUSES,
        SUM_LE, SUM_LMUL, SUM_LT_ALL, SUM_RESTRICT_SET, SUM_SUB,
        SWAP_EXISTS_THM, UNWIND_THM2, num_CASES, sum, support, .. } := D.core3
  -- @@SCOPE END

  let FORALL_DIFF ← prove
   r"(!s:A->bool. P(UNIV DIFF s)) <=> (!s. P s)"
   (MESON_TAC [COMPL_COMPL])

  let EXISTS_DIFF ← prove
   r"(?s:A->bool. P(UNIV DIFF s)) <=> (?s. P s)"
   (MESON_TAC [COMPL_COMPL])

  let FORALL_DIFF_ALT ← prove
   r"!u:A->bool.
    (!s. s SUBSET u ==> P(u DIFF s)) <=> (!s. s SUBSET u ==> P s)"
   (GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN
    X_GEN_TAC (← q r"s:A->bool") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"u DIFF s:A->bool")) THEN
    REWRITE_TAC [SUBSET_DIFF] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_TERM_TAC THEN ASM SET_TAC [])

  let FORALL_DIFF_GEN ← prove
   r"!u:A->bool.
    (!s. P(u DIFF s)) <=> (!s. s SUBSET u ==> P s)"
   (GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN
    X_GEN_TAC (← q r"s:A->bool") THEN TRY DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"u DIFF s:A->bool")) THEN
    REWRITE_TAC [SUBSET_DIFF] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_TERM_TAC THEN ASM SET_TAC [])

  let GE_REFL ← prove
   r"!n:num. n >= n"
   (REWRITE_TAC [GE, LE_REFL])

  let FORALL_SUC ← prove
   r"(!n. ~(n = 0) ==> P n) <=> (!n. P(SUC n))"
   (MESON_TAC [num_CASES, NOT_SUC])

  let SEQ_MONO_LEMMA ← prove
   r"!d e. (!n. n >= m ==> d(n) < e(n)) /\ (!n. n >= m ==> e(n) <= e(m))
         ==> !n:num. n >= m ==> d(n) < e(m)"
   (MESON_TAC [GE, REAL_LTE_TRANS])

  let REAL_HALF ← prove
   r"(!e. &0 < e / &2 <=> &0 < e) /\
   (!e. e / &2 + e / &2 = e) /\
   (!e. &2 * (e / &2) = e)"
   REAL_ARITH_TAC

  let ABS_SQUARE_LT_1 ← prove
   r"!x. x pow 2 < &1 <=> abs(x) < &1"
   (ONCE_REWRITE_TAC [← GSYM REAL_ABS_NUM] THEN
    REWRITE_TAC [REAL_LT_SQUARE_ABS] THEN REAL_ARITH_TAC)

  let ABS_SQUARE_LE_1 ← prove
   r"!x. x pow 2 <= &1 <=> abs(x) <= &1"
   (ONCE_REWRITE_TAC [← GSYM REAL_ABS_NUM] THEN
    REWRITE_TAC [REAL_LT_SQUARE_ABS, ← GSYM REAL_NOT_LT] THEN REAL_ARITH_TAC)

  let ABS_SQUARE_EQ_1 ← prove
   r"!x. x pow 2 = &1 <=> abs(x) = &1"
   (REWRITE_TAC [← REAL_RING (← q r"x pow 2 = &1 <=> x = &1 \/ x = -- &1")] THEN
    REAL_ARITH_TAC)

  let UPPER_BOUND_FINITE_SET ← prove
   r"!f:(A->num) s. FINITE(s) ==> ?a. !x. x IN s ==> f(x) <= a"
   (GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
    METIS_TAC [LE_CASES, LE_REFL, LE_TRANS])

  let UPPER_BOUND_FINITE_SET_REAL ← prove
   r"!f:(A->real) s. FINITE(s) ==> ?a. !x. x IN s ==> f(x) <= a"
   (GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
    METIS_TAC [REAL_LE_TOTAL, REAL_LE_REFL, REAL_LE_TRANS])

  let LOWER_BOUND_FINITE_SET ← prove
   r"!f:(A->num) s. FINITE(s) ==> ?a. !x. x IN s ==> a <= f(x)"
   (GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
    METIS_TAC [LE_CASES, LE_REFL, LE_TRANS])

  let LOWER_BOUND_FINITE_SET_REAL ← prove
   r"!f:(A->real) s. FINITE(s) ==> ?a. !x. x IN s ==> a <= f(x)"
   (GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
    METIS_TAC [REAL_LE_TOTAL, REAL_LE_REFL, REAL_LE_TRANS])

  let REAL_CONVEX_SUM_BOUND_LE ← prove
   r"!s d a b x:A->real.
        (!i. i IN s ==> &0 <= x i) /\ sum s x = &1 /\
        (!i. i IN s ==> abs(a i - b) <= d)
        ==> abs(sum s (\i. a i * x i) - b) <= d"
   (REPEAT GEN_TAC THEN REWRITE_TAC [sum] THEN
    ONCE_REWRITE_TAC [ITERATE_EXPAND_CASES] THEN
    REWRITE_TAC [← GSYM sum, NEUTRAL_REAL_ADD, support, REAL_ENTIRE] THEN
    REWRITE_TAC [← SET_RULE (← q
     r"{x | x IN s /\ ~(P x \/ Q x)} =
    {x | x IN {y | y IN s /\ ~Q y} /\ ~P x}")] THEN
    ABBREV_TAC (← q r"t = {i | i IN s /\ ~((x:A->real) i = &0)}") THEN
    ASM_CASES_TAC (← q r"FINITE(t:A->bool)") THEN ASM_SIMP_TAC [FINITE_RESTRICT] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"(!i. i IN t ==> &0 <= (x:A->real) i) /\
    (!i. i IN t ==> abs(a i - b) <= d)")
    STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    REWRITE_TAC [SUM_RESTRICT_SET, ← MESON [REAL_MUL_LZERO]
     (← q r"(if ~(a = &0) then a * x else &0) = a * x")] THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"a - b = a - b * &1")] THEN
    FIRST_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC [← GSYM SUM_LMUL] THEN
    ASM_SIMP_TAC [← GSYM SUM_SUB] THEN
    W (MP_TAC o PART_MATCH (lhand o rand) SUM_ABS o lhand o snd) THEN
    ASM_REWRITE_TAC [← GSYM REAL_SUB_RDISTRIB] THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] REAL_LE_TRANS) THEN
    ASM_SIMP_TAC [REAL_ABS_MUL, ← REAL_ARITH (← q r"&0 <= x ==> abs x = x")] THEN
    TRANS_TAC REAL_LE_TRANS (← q r"sum t (\i:A. d * x i)") THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC [REAL_LE_RMUL],
      ASM_REWRITE_TAC [SUM_LMUL, REAL_MUL_RID, REAL_LE_REFL]])

  let REAL_CONVEX_SUM_BOUND_LT ← prove
   r"!s d a b x:A->real.
        (!i. i IN s ==> &0 <= x i) /\ sum s x = &1 /\
        (!i. i IN s ==> abs(a i - b) < d)
        ==> abs(sum s (\i. a i * x i) - b) < d"
   (REPEAT GEN_TAC THEN REWRITE_TAC [sum] THEN
    ONCE_REWRITE_TAC [ITERATE_EXPAND_CASES] THEN
    REWRITE_TAC [← GSYM sum, NEUTRAL_REAL_ADD, support, REAL_ENTIRE] THEN
    REWRITE_TAC [← SET_RULE (← q
     r"{x | x IN s /\ ~(P x \/ Q x)} =
    {x | x IN {y | y IN s /\ ~Q y} /\ ~P x}")] THEN
    ABBREV_TAC (← q r"t = {i | i IN s /\ ~((x:A->real) i = &0)}") THEN
    ASM_CASES_TAC (← q r"FINITE(t:A->bool)") THEN ASM_SIMP_TAC [FINITE_RESTRICT] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"(!i. i IN t ==> &0 < (x:A->real) i) /\
    (!i. i IN t ==> abs(a i - b) < d)")
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "t" THEN
      SIMP_TAC [IN_ELIM_THM, ← REAL_ARITH (← q r"&0 < x <=> &0 <= x /\ ~(x = &0)")] THEN
      ASM SET_TAC [],
      ALL_TAC] THEN
    REWRITE_TAC [SUM_RESTRICT_SET, ← MESON [REAL_MUL_LZERO]
     (← q r"(if ~(a = &0) then a * x else &0) = a * x")] THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"a - b = a - b * &1")] THEN
    FIRST_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC [← GSYM SUM_LMUL] THEN
    ASM_SIMP_TAC [← GSYM SUM_SUB] THEN
    W (MP_TAC o PART_MATCH (lhand o rand) SUM_ABS o lhand o snd) THEN
    ASM_REWRITE_TAC [← GSYM REAL_SUB_RDISTRIB] THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] REAL_LET_TRANS) THEN
    ASM_SIMP_TAC [REAL_ABS_MUL, ← REAL_ARITH (← q r"&0 < x ==> abs x = x")] THEN
    TRANS_TAC REAL_LTE_TRANS (← q r"sum t (\i:A. d * x i)") THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LT_ALL THEN ASM_SIMP_TAC [REAL_LT_RMUL_EQ] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC (REWRITE_RULE [SUM_CLAUSES]) THEN ASM_REAL_ARITH_TAC,
      ASM_REWRITE_TAC [SUM_LMUL, REAL_MUL_RID, REAL_LE_REFL]])

  let APPROACHABLE_LT_LE ← do
    let lemma ← prove
     r"&0 < d ==> x <= d / &2 ==> x < d"
     (SIMP_TAC [REAL_LE_RDIV_EQ, REAL_OF_NUM_LT, ARITH] THEN REAL_ARITH_TAC)
    prove
     r"!P f. (?d. &0 < d /\ !x. f(x) < d ==> P x) =
         (?d. &0 < d /\ !x. f(x) <= d ==> P x)"
     (MESON_TAC [REAL_LT_IMP_LE, lemma, REAL_HALF])

  let REAL_LE_BETWEEN ← prove
   r"!a b. a <= b <=> ?x. a <= x /\ x <= b"
   (MESON_TAC [REAL_LE_TRANS, REAL_LE_REFL])

  let REAL_LET_BETWEEN ← prove
   r"!a b. a < b <=> (?x. a <= x /\ x < b)"
   (MESON_TAC [REAL_LE_REFL, REAL_LET_TRANS])

  let REAL_LTE_BETWEEN ← prove
   r"!a b. a < b <=> (?x. a < x /\ x <= b)"
   (MESON_TAC [REAL_LE_REFL, REAL_LTE_TRANS])

  let REAL_LT_BETWEEN ← prove
   r"!a b. a < b <=> ?x. a < x /\ x < b"
   (REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC, MESON_TAC [REAL_LT_TRANS]] THEN
    DISCH_TAC THEN EXISTS_TAC (← q r"(a + b) / &2") THEN
    SIMP_TAC [REAL_LT_RDIV_EQ, REAL_LT_LDIV_EQ, REAL_OF_NUM_LT, ARITH] THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC)

  let REAL_LT_BETWEEN_GEN ← prove
   r"!s t:real->bool.
        FINITE s /\ FINITE t
        ==> ((?x. (!a. a IN s ==> a < x) /\ (!b. b IN t ==> x < b)) <=>
             !a b. a IN s /\ b IN t ==> a < b)"
   (REPEAT GEN_TAC THEN
    SIMP_TAC [← MESON [REAL_SUP_LT_FINITE, NOT_IN_EMPTY]
     (← q r"FINITE s ==> ((!a. a IN s ==> a < x) <=> s = {} \/ sup s < x)")] THEN
    SIMP_TAC [← MESON [REAL_LT_INF_FINITE, NOT_IN_EMPTY]
     (← q r"FINITE t ==> ((!b. b IN t ==> x < b) <=> t = {} \/ x < inf t)")] THEN
    STRIP_TAC THEN ASM_CASES_TAC (← q r"s:real->bool = {}") THEN
    ASM_REWRITE_TAC [NOT_IN_EMPTY] THENL
     [MESON_TAC [← REAL_ARITH (← q r"s - &1 < s")], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"t:real->bool = {}") THEN ASM_REWRITE_TAC [NOT_IN_EMPTY] THENL
     [MESON_TAC [← REAL_ARITH (← q r"t < t + &1")], ALL_TAC] THEN
    REWRITE_TAC [← GSYM REAL_LT_BETWEEN] THEN
    ASM_SIMP_TAC [REAL_SUP_LT_FINITE, REAL_LT_INF_FINITE] THEN MESON_TAC [])

  let TRIANGLE_LEMMA ← prove
   r"!x y z. &0 <= x /\ &0 <= y /\ &0 <= z /\ x pow 2 <= y pow 2 + z pow 2
           ==> x <= y + z"
   (REPEAT GEN_TAC THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC [REAL_NOT_LE] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q r"(y + z) pow 2") THEN
    ASM_SIMP_TAC [REAL_POW_LT2, REAL_LE_ADD, ARITH_EQ] THEN
    ASM_SIMP_TAC [REAL_LE_MUL, REAL_POW_2, ← REAL_ARITH
     (← q r"x * x + y * y <= (x + y) * (x + y) <=> &0 <= x * y")])

  let LAMBDA_SKOLEM ← prove
   r"(!i. 1 <= i /\ i <= dimindex(:N) ==> ?x. P i x) =
   (?x:A^N. !i. 1 <= i /\ i <= dimindex(:N) ==> P i (x$i))"
   (REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_TAC (← q r"x:num->A")) THEN
      EXISTS_TAC (← q r"(lambda i. x i):A^N") THEN ASM_SIMP_TAC [LAMBDA_BETA],
      DISCH_THEN (X_CHOOSE_TAC (← q r"x:A^N")) THEN
      EXISTS_TAC (← q r"\i. (x:A^N)$i") THEN ASM_REWRITE_TAC []])

  let EPSILON_DELTA_MINIMAL ← prove
   r"!P:real->A->bool Q.
        FINITE {x | Q x} /\
        (!d e x. Q x /\ &0 < e /\ e < d ==> P d x ==> P e x) /\
        (!x. Q x ==> ?d. &0 < d /\ P d x)
        ==> ?d. &0 < d /\ !x. Q x ==> P d x"
   (REWRITE_TAC [IMP_IMP] THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"{x:A | Q x} = {}") THENL
     [FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [EXTENSION]) THEN
      REWRITE_TAC [NOT_IN_EMPTY, IN_ELIM_THM] THEN
      DISCH_TAC THEN EXISTS_TAC (← q r"&1") THEN ASM_REWRITE_TAC [REAL_LT_01],
      FIRST_X_ASSUM (MP_TAC o
       GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]) THEN
      REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"d:A->real") THEN DISCH_TAC THEN
      EXISTS_TAC (← q r"inf(IMAGE d {x:A | Q x})") THEN
      ASM_SIMP_TAC [REAL_LT_INF_FINITE, FINITE_IMAGE, IMAGE_EQ_EMPTY] THEN
      ASM_SIMP_TAC [FORALL_IN_IMAGE, FORALL_IN_GSPEC] THEN
      X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN
      SUBGOAL_THEN
       (← q r"&0 < inf(IMAGE d {x:A | Q x}) /\ inf(IMAGE d {x | Q x}) <= d a")
      MP_TAC THENL
       [ASM_SIMP_TAC [REAL_LT_INF_FINITE, REAL_INF_LE_FINITE,
                      FINITE_IMAGE, IMAGE_EQ_EMPTY] THEN
        REWRITE_TAC [EXISTS_IN_IMAGE, FORALL_IN_IMAGE, IN_ELIM_THM] THEN
        ASM_MESON_TAC [REAL_LE_REFL],
        REWRITE_TAC [REAL_LE_LT] THEN STRIP_TAC THEN ASM_SIMP_TAC [] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        EXISTS_TAC (← q r"(d:A->real) a") THEN ASM_SIMP_TAC []]])

  let HAS_SIZE_1_EXISTS ← prove
   r"!s. s HAS_SIZE 1 <=> ?!x. x IN s"
   (REPEAT GEN_TAC THEN CONV_TAC (LAND_CONV HAS_SIZE_CONV) THEN
    REWRITE_TAC [EXTENSION, IN_SING] THEN MESON_TAC [])

  let LINEAR_EQUATIONS_1_EQ ← prove
   r"!a b. (?x. a * x = b) <=> a = &0 ==> b = &0"
   (REPEAT GEN_TAC THEN EQ_TAC THENL [CONV_TAC (fun t => REAL_RING t), ALL_TAC] THEN
    ASM_CASES_TAC (← q r"b = &0") THEN
    ASM_SIMP_TAC [← REAL_FIELD (← q r"~(a = &0) ==> (a * x = b <=> x = b / a)")] THEN
    MESON_TAC [REAL_MUL_RZERO])

  let LINEAR_EQUATIONS_2_EQ ← prove
   r"!a b c d u v.
        (?x y. a * x + b * y = u /\ c * x + d * y = v) <=>
        (a * d = b * c ==> d * u = b * v /\ c * u = a * v) /\
        (a = &0 /\ b = &0 /\ c = &0 /\ d = &0 ==> u = &0 /\ v = &0)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL [CONV_TAC (fun t => REAL_RING t), ALL_TAC] THEN
    ASM_CASES_TAC (← q r"u = &0 /\ v = &0") THEN ASM_REWRITE_TAC [] THENL
     [ASM_METIS_TAC [REAL_MUL_RZERO, REAL_ADD_LID], ALL_TAC] THEN
    REWRITE_TAC [DE_MORGAN_THM] THEN STRIP_TAC THENL
     [ALL_TAC,
      ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN ONCE_REWRITE_TAC [SWAP_EXISTS_THM],
      ONCE_REWRITE_TAC [CONJ_SYM],
      ONCE_REWRITE_TAC [CONJ_SYM] THEN
      ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN ONCE_REWRITE_TAC [SWAP_EXISTS_THM]] THEN
    ASM_SIMP_TAC [← REAL_FIELD (← q
     r"~(a = &0)
     ==> (a * x + b * y = u /\ c * x + d * y = v <=>
         x = (u - b * y) / a /\ (a * d - b * c) * y = a * v - c * u)")] THEN
    GEN_REWRITE_TAC id [SWAP_EXISTS_THM] THEN REWRITE_TAC [UNWIND_THM2] THEN
    REWRITE_TAC [LINEAR_EQUATIONS_1_EQ] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC (fun t => REAL_RING t))

  return { FORALL_DIFF, EXISTS_DIFF, FORALL_DIFF_ALT, FORALL_DIFF_GEN, GE_REFL,
           FORALL_SUC, SEQ_MONO_LEMMA, REAL_HALF, ABS_SQUARE_LT_1, ABS_SQUARE_LE_1,
           ABS_SQUARE_EQ_1, UPPER_BOUND_FINITE_SET, UPPER_BOUND_FINITE_SET_REAL,
           LOWER_BOUND_FINITE_SET, LOWER_BOUND_FINITE_SET_REAL,
           REAL_CONVEX_SUM_BOUND_LE, REAL_CONVEX_SUM_BOUND_LT, APPROACHABLE_LT_LE,
           REAL_LE_BETWEEN, REAL_LET_BETWEEN, REAL_LTE_BETWEEN, REAL_LT_BETWEEN,
           REAL_LT_BETWEEN_GEN, TRIANGLE_LEMMA, LAMBDA_SKOLEM, EPSILON_DELTA_MINIMAL,
           HAS_SIZE_1_EXISTS, LINEAR_EQUATIONS_1_EQ, LINEAR_EQUATIONS_2_EQ }

/- ------------------------------------------------------------------------- -/
/- Handy definitions and basic lemmas for real intervals.  (misc.ml 313-475) -/
/- ------------------------------------------------------------------------- -/

structure RealInterval where
  is_realinterval : thm
  IS_REALINTERVAL_EMPTY : thm
  IS_REALINTERVAL_UNION : thm
  IS_REALINTERVAL_UNIV : thm
  IS_REALINTERVAL_INTER : thm
  open_real_interval : thm
  closed_real_interval : thm
  real_interval : thm
  IN_REAL_INTERVAL : thm
  EMPTY_AS_REAL_INTERVAL : thm
  REAL_INTERVAL_OPEN_SUBSET_CLOSED : thm
  REAL_INTERVAL_EQ_EMPTY : thm
  REAL_INTERVAL_NE_EMPTY : thm
  REAL_INTERVAL_SING : thm
  ENDS_IN_REAL_INTERVAL : thm
  IN_REAL_INTERVAL_REFLECT : thm
  REFLECT_REAL_INTERVAL : thm
  IS_REALINTERVAL_INTERVAL : thm
  ENDS_IN_UNIT_REAL_INTERVAL : thm
  INTER_REAL_INTERVAL : thm
  REAL_OPEN_CLOSED_INTERVAL : thm
  REAL_CLOSED_OPEN_INTERVAL : thm
  IS_REALINTERVAL_SING : thm
  IS_REALINTERVAL_CONTAINS_INTERVAL : thm
  IS_REALINTERVAL_SHRINK : thm
  SUBSET_REAL_INTERVAL : thm
  deriving Inhabited

@[nospecialize]
def setupRealInterval [HolBase] (D : MiscDeps) (BLemmas : Lemmas) :
    ExceptT String IO RealInterval := do
  -- @@SCOPE BEGIN
  let { MESON, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, SET_RULE, define,
        make_overloadable, new_definition, overload_interface, .. } := D
  let { CONJ_ASSOC, EXTENSION, FORALL_AND_THM, FORALL_IN_IMAGE, IMP_CONJ,
        IMP_IMP, .. } := D.core1
  let { IN_DIFF, IN_ELIM_THM, IN_IMAGE, IN_INSERT, IN_INTER, IN_SING, IN_UNION,
        IN_UNIV, NOT_EXISTS_THM, NOT_IN_EMPTY, REAL_LE_REFL, REAL_LE_TOTAL,
        REAL_LE_TRANS, .. } := D.core2
  let { REAL_NOT_LE, REAL_NOT_LT, REAL_POS, REAL_SHRINK_GALOIS,
        REAL_SHRINK_GROW, REAL_SHRINK_LE, REAL_SHRINK_RANGE,
        RIGHT_FORALL_IMP_THM, RIGHT_IMP_FORALL_THM, SUBSET, UNWIND_THM1, .. } := D.core3
  let { REAL_LE_BETWEEN, REAL_LT_BETWEEN, .. } := BLemmas
  -- @@SCOPE END

  let is_realinterval ← new_definition
   r"is_realinterval s <=>
        !a b c. a IN s /\ b IN s /\ a <= c /\ c <= b ==> c IN s"

  let IS_REALINTERVAL_EMPTY ← prove
   r"is_realinterval {}"
   (REWRITE_TAC [is_realinterval, NOT_IN_EMPTY])

  let IS_REALINTERVAL_UNION ← prove
   r"!s t. is_realinterval s /\ is_realinterval t /\ ~(s INTER t = {})
         ==> is_realinterval(s UNION t)"
   (REWRITE_TAC [is_realinterval, IN_UNION, IN_INTER,
                 NOT_IN_EMPTY, EXTENSION] THEN
    MESON_TAC [REAL_LE_TRANS, REAL_LE_TOTAL])

  let IS_REALINTERVAL_UNIV ← prove
   r"is_realinterval (:real)"
   (REWRITE_TAC [is_realinterval, IN_UNIV])

  let IS_REALINTERVAL_INTER ← prove
   r"!s t. is_realinterval s /\ is_realinterval t
         ==> is_realinterval(s INTER t)"
   (REWRITE_TAC [is_realinterval, IN_INTER] THEN MESON_TAC [])

  let open_real_interval ← new_definition
   r"open_real_interval(a:real,b:real) = {x:real | a < x /\ x < b}"

  let closed_real_interval ← define
   r"closed_real_interval[a:real,b:real] = {x:real | a <= x /\ x <= b}"

  make_overloadable "real_interval" (← qty "A")

  overload_interface "real_interval" (← q "open_real_interval")
  overload_interface "real_interval" (← q "closed_real_interval")

  let real_interval ← prove
   r"real_interval(a,b) = {x | a < x /\ x < b} /\
   real_interval[a,b] = {x | a <= x /\ x <= b}"
   (REWRITE_TAC [open_real_interval, closed_real_interval])

  let IN_REAL_INTERVAL ← prove
   r"!a b x. (x IN real_interval[a,b] <=> a <= x /\ x <= b) /\
           (x IN real_interval(a,b) <=> a < x /\ x < b)"
   (REWRITE_TAC [real_interval, IN_ELIM_THM])

  let EMPTY_AS_REAL_INTERVAL ← prove
   r"{} = real_interval[&1,&0]"
   (REWRITE_TAC [EXTENSION, IN_REAL_INTERVAL, NOT_IN_EMPTY] THEN REAL_ARITH_TAC)

  let REAL_INTERVAL_OPEN_SUBSET_CLOSED ← prove
   r"!a b. real_interval(a,b) SUBSET real_interval[a,b]"
   (REWRITE_TAC [SUBSET, IN_REAL_INTERVAL] THEN REAL_ARITH_TAC)

  let REAL_INTERVAL_EQ_EMPTY ← prove
   r"(!a b. real_interval[a,b] = {} <=> b < a) /\
   (!a b. real_interval(a,b) = {} <=> b <= a)"
   (REWRITE_TAC [EXTENSION, IN_REAL_INTERVAL, NOT_IN_EMPTY] THEN
    REWRITE_TAC [← GSYM NOT_EXISTS_THM] THEN
    REWRITE_TAC [← GSYM REAL_LT_BETWEEN, ← GSYM REAL_LE_BETWEEN] THEN
    REAL_ARITH_TAC)

  let REAL_INTERVAL_NE_EMPTY ← prove
   r"(!a b. ~(real_interval[a,b] = {}) <=> a <= b) /\
   (!a b. ~(real_interval(a,b) = {}) <=> a < b)"
   (REWRITE_TAC [REAL_INTERVAL_EQ_EMPTY, REAL_NOT_LE, REAL_NOT_LT])

  let REAL_INTERVAL_SING ← prove
   r"!a. real_interval[a,a] = {a} /\ real_interval(a,a) = {}"
   (REWRITE_TAC [EXTENSION, IN_SING, NOT_IN_EMPTY, IN_REAL_INTERVAL] THEN
    REAL_ARITH_TAC)

  let ENDS_IN_REAL_INTERVAL ← prove
   r"(!a b. a IN real_interval[a,b] <=> ~(real_interval[a,b] = {})) /\
   (!a b. b IN real_interval[a,b] <=> ~(real_interval[a,b] = {})) /\
   (!a b. ~(a IN real_interval(a,b))) /\
   (!a b. ~(b IN real_interval(a,b)))"
   (REWRITE_TAC [IN_REAL_INTERVAL, REAL_INTERVAL_EQ_EMPTY] THEN REAL_ARITH_TAC)

  let IN_REAL_INTERVAL_REFLECT ← prove
   r"(!a b x. --x IN real_interval[--b,--a] <=> x IN real_interval[a,b]) /\
   (!a b x. --x IN real_interval(--b,--a) <=> x IN real_interval(a,b))"
   (REWRITE_TAC [IN_REAL_INTERVAL] THEN REAL_ARITH_TAC)

  let REFLECT_REAL_INTERVAL ← prove
   r"(!a b. IMAGE (--) (real_interval[a,b]) = real_interval[--b,--a]) /\
   (!a b. IMAGE (--) (real_interval(a,b)) = real_interval(--b,--a))"
   (REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_IMAGE, IN_REAL_INTERVAL] THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"x:real = --y <=> --x = y")] THEN
    REWRITE_TAC [UNWIND_THM1] THEN REAL_ARITH_TAC)

  let IS_REALINTERVAL_INTERVAL ← prove
   r"!a b. is_realinterval(real_interval(a,b)) /\
         is_realinterval(real_interval[a,b])"
   (REWRITE_TAC [is_realinterval, IN_REAL_INTERVAL] THEN REAL_ARITH_TAC)

  let ENDS_IN_UNIT_REAL_INTERVAL ← prove
   r"&0 IN real_interval[&0,&1] /\ &1 IN real_interval[&0,&1]"
   (REWRITE_TAC [IN_REAL_INTERVAL, REAL_POS, REAL_LE_REFL])

  let INTER_REAL_INTERVAL ← prove
   r"!a b c d.
        real_interval[a,b] INTER real_interval[c,d] =
        real_interval[max a c,min b d]"
   (REWRITE_TAC [EXTENSION, IN_INTER, IN_REAL_INTERVAL] THEN
    REAL_ARITH_TAC)

  let REAL_OPEN_CLOSED_INTERVAL ← prove
   r"!a b. real_interval(a,b) = real_interval[a,b] DIFF {a,b}"
   (SIMP_TAC [EXTENSION, IN_DIFF, IN_REAL_INTERVAL, IN_INSERT, NOT_IN_EMPTY] THEN
    REAL_ARITH_TAC)

  let REAL_CLOSED_OPEN_INTERVAL ← prove
   r"!a b. a <= b ==> real_interval[a,b] = real_interval(a,b) UNION {a,b}"
   (SIMP_TAC [EXTENSION, IN_UNION, IN_REAL_INTERVAL, IN_INSERT, NOT_IN_EMPTY] THEN
    REAL_ARITH_TAC)

  let IS_REALINTERVAL_SING ← prove
   r"!a. is_realinterval {a}"
   (REWRITE_TAC [is_realinterval, IN_SING] THEN REAL_ARITH_TAC)

  let IS_REALINTERVAL_CONTAINS_INTERVAL ← prove
   r"!s a b. is_realinterval s /\ a IN s /\ b IN s
           ==> real_interval[a,b] SUBSET s"
   (REWRITE_TAC [SUBSET, is_realinterval, IN_REAL_INTERVAL] THEN
    MESON_TAC [])

  let IS_REALINTERVAL_SHRINK ← prove
   r"!s. is_realinterval (IMAGE (\x. x / (&1 + abs x)) s) <=>
       is_realinterval s"
   (REWRITE_TAC [is_realinterval, IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    GEN_TAC THEN REWRITE_TAC [FORALL_IN_IMAGE] THEN
    REWRITE_TAC [RIGHT_IMP_FORALL_THM, IMP_IMP, ← GSYM CONJ_ASSOC] THEN
    REWRITE_TAC [← SET_RULE (← q r"y IN IMAGE f s <=> ?x. f x = y /\ x IN s")] THEN
    REWRITE_TAC [← MESON [REAL_SHRINK_GALOIS] (← q
     r"(?x. x / (&1 + abs x) = c /\ x IN s) <=>
    (?x. x / (&1 + abs x) = c) /\ (!x. x / (&1 + abs x) = c ==> x IN s)")] THEN
    REWRITE_TAC [← TAUT (← q r"(p ==> q /\ r) <=> (p ==> q) /\ (p ==> r)")] THEN
    REWRITE_TAC [FORALL_AND_THM, RIGHT_IMP_FORALL_THM] THEN
    MATCH_MP_TAC (← TAUT (← q r"(q <=> r) /\ p ==> (p /\ q <=> r)")) THEN
    CONJ_TAC THENL [MESON_TAC [REAL_SHRINK_LE], ALL_TAC] THEN
    MESON_TAC [REAL_SHRINK_RANGE, REAL_SHRINK_GROW, ← REAL_ARITH (← q
     r"a <= x /\ x <= b /\ abs a < &1 /\ abs b < &1 ==> abs x < &1")])

  let SUBSET_REAL_INTERVAL ← prove
   r"!a b c d.
        (real_interval[a,b] SUBSET real_interval[c,d] <=>
                b < a \/ c <= a /\ a <= b /\ b <= d) /\
        (real_interval[a,b] SUBSET real_interval(c,d) <=>
                b < a \/ c < a /\ a <= b /\ b < d) /\
        (real_interval(a,b) SUBSET real_interval[c,d] <=>
                b <= a \/ c <= a /\ a < b /\ b <= d) /\
        (real_interval(a,b) SUBSET real_interval(c,d) <=>
                b <= a \/ c <= a /\ a < b /\ b <= d)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [SUBSET, IN_REAL_INTERVAL] THEN
    REPEAT CONJ_TAC THEN (EQ_TAC THENL [ALL_TAC, REAL_ARITH_TAC]) THEN
    DISCH_THEN (fun th => tactic_of do
      pure (MP_TAC (← SPEC (← q r"(a + min b c) / &2") th) THEN
            MP_TAC (← SPEC (← q r"(max d a + b) / &2") th))) THEN
    REAL_ARITH_TAC)

  return { is_realinterval, IS_REALINTERVAL_EMPTY, IS_REALINTERVAL_UNION,
           IS_REALINTERVAL_UNIV, IS_REALINTERVAL_INTER, open_real_interval,
           closed_real_interval, real_interval, IN_REAL_INTERVAL,
           EMPTY_AS_REAL_INTERVAL, REAL_INTERVAL_OPEN_SUBSET_CLOSED,
           REAL_INTERVAL_EQ_EMPTY, REAL_INTERVAL_NE_EMPTY, REAL_INTERVAL_SING,
           ENDS_IN_REAL_INTERVAL, IN_REAL_INTERVAL_REFLECT, REFLECT_REAL_INTERVAL,
           IS_REALINTERVAL_INTERVAL, ENDS_IN_UNIT_REAL_INTERVAL,
           INTER_REAL_INTERVAL, REAL_OPEN_CLOSED_INTERVAL,
           REAL_CLOSED_OPEN_INTERVAL, IS_REALINTERVAL_SING,
           IS_REALINTERVAL_CONTAINS_INTERVAL, IS_REALINTERVAL_SHRINK,
           SUBSET_REAL_INTERVAL }

/- ------------------------------------------------------------------------- -/
/- Converting between matrices/arrays and flattened vectors. We can consider -/
/- these as curry and uncurry for Cartesian powers.  (misc.ml 477-570)       -/
/- ------------------------------------------------------------------------- -/

structure Vectorize where
  vectorize : thm
  matrify : thm
  VECTORIZE_COMPONENT : thm
  MATRIFY_COMPONENT : thm
  VECTORIZE_MATRIFY : thm
  MATRIFY_VECTORIZE : thm
  FORALL_VECTORIZE : thm
  FORALL_MATRIFY : thm
  EXISTS_VECTORIZE : thm
  EXISTS_MATRIFY : thm
  VECTORIZE_GSPEC : thm
  VECTORIZE_EQ : thm
  MATRIFY_EQ : thm
  deriving Inhabited

@[nospecialize]
def setupVectorize [HolBase] (D : MiscDeps) : ExceptT String IO Vectorize := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, MESON_TAC, new_definition, .. } := D
  let { ADD_SUB2, CART_EQ, DIMINDEX_FINITE_PROD, DIMINDEX_GE_1, DIVISION,
        DIV_UNIQ, EXTENSION, .. } := D.core1
  let { IN_ELIM_THM, LAMBDA_BETA, LE_1, LE_ADD_LCANCEL, LE_MULT_RCANCEL,
        LE_TRANS, MOD_UNIQ, RDIV_LT_EQ, .. } := D.core2
  let { SUB_ADD, .. } := D.core3
  -- @@SCOPE END

  let vectorize ← new_definition
   r"(vectorize:A^N^M->A^(M,N)finite_prod) =
        \x. lambda i. x$(1 + (i - 1) DIV dimindex(:N))
                       $(1 + (i - 1) MOD dimindex(:N))"

  let matrify ← new_definition
   r"(matrify:A^(M,N)finite_prod->A^N^M) =
        \x. lambda i j. x$((i - 1) * dimindex(:N) + j)"

  let VECTORIZE_COMPONENT ← prove
   r"!m:A^N^M i.
        1 <= i /\ i <= dimindex(:M) * dimindex(:N)
        ==> (vectorize m)$i = m$(1 + (i - 1) DIV dimindex(:N))
                              $(1 + (i - 1) MOD dimindex(:N))"
   (SIMP_TAC [vectorize, LAMBDA_BETA, DIMINDEX_FINITE_PROD])

  let MATRIFY_COMPONENT ← prove
   r"!v:A^(M,N)finite_prod i j.
        1 <= i /\ i <= dimindex(:M) /\ 1 <= j /\ j <= dimindex(:N)
        ==> (matrify v)$i$j = v$((i - 1) * dimindex(:N) + j)"
   (SIMP_TAC [matrify, LAMBDA_BETA])

  let VECTORIZE_MATRIFY ← prove
   r"!a:A^(M,N)finite_prod. vectorize(matrify a) = a"
   (GEN_TAC THEN SIMP_TAC [CART_EQ, vectorize, matrify, LAMBDA_BETA] THEN
    REWRITE_TAC [DIMINDEX_FINITE_PROD] THEN X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN
    W (MP_TAC o PART_MATCH (lhand o rand) LAMBDA_BETA o lhand o lhand o snd) THEN
    REWRITE_TAC [← ARITH_RULE (← q r"1 <= 1 + x /\ 1 + y <= z <=> y < z")] THEN
    SIMP_TAC [RDIV_LT_EQ, DIMINDEX_GE_1, LE_1] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC, DISCH_THEN SUBST1_TAC] THEN
    W (MP_TAC o PART_MATCH (lhand o rand) LAMBDA_BETA o lhand o snd) THEN
    REWRITE_TAC [← ARITH_RULE (← q r"1 <= 1 + x /\ 1 + y <= z <=> y < z")] THEN
    SIMP_TAC [DIVISION, DIMINDEX_GE_1, LE_1] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC [ADD_SUB2] THEN
    MATCH_MP_TAC (← ARITH_RULE (← q
     r"1 <= i /\ i - 1 = d * n + m /\ m < n
     ==> d * n + 1 + m = i")) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC DIVISION THEN
    SIMP_TAC [DIMINDEX_GE_1, LE_1])

  let MATRIFY_VECTORIZE ← prove
   r"!m:A^N^M. matrify(vectorize m) = m"
   (GEN_TAC THEN SIMP_TAC [CART_EQ, vectorize, matrify, LAMBDA_BETA] THEN
    X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN
    X_GEN_TAC (← q r"j:num") THEN STRIP_TAC THEN
    W (MP_TAC o PART_MATCH (lhand o rand) LAMBDA_BETA o lhand o snd) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      TRANS_TAC LE_TRANS (← q r"(i - 1) * dimindex(:N) + dimindex(:N)") THEN
      ASM_REWRITE_TAC [LE_ADD_LCANCEL] THEN
      REWRITE_TAC [← ARITH_RULE (← q r"x * n + n = (x + 1) * n")] THEN
      ASM_SIMP_TAC [SUB_ADD, DIMINDEX_FINITE_PROD] THEN
      ASM_SIMP_TAC [LE_MULT_RCANCEL, DIMINDEX_GE_1],
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC [] THEN BINOP_TAC THENL
     [AP_TERM_TAC, ALL_TAC] THEN
    MATCH_MP_TAC (← ARITH_RULE (← q r"1 <= i /\ j = i - 1 ==> 1 + j = i")) THEN
    ASM_REWRITE_TAC [] THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC (← q r"j - 1") THEN ASM_ARITH_TAC,
      MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC (← q r"i - 1") THEN ASM_ARITH_TAC])

  let FORALL_VECTORIZE ← prove
   r"!P. (!x. P x) <=> (!x. P(vectorize x))"
   (MESON_TAC [MATRIFY_VECTORIZE, VECTORIZE_MATRIFY])

  let FORALL_MATRIFY ← prove
   r"!P. (!x. P x) <=> (!x. P(matrify x))"
   (MESON_TAC [MATRIFY_VECTORIZE, VECTORIZE_MATRIFY])

  let EXISTS_VECTORIZE ← prove
   r"!P. (?x. P x) <=> (?x. P(vectorize x))"
   (MESON_TAC [MATRIFY_VECTORIZE, VECTORIZE_MATRIFY])

  let EXISTS_MATRIFY ← prove
   r"!P. (?x. P x) <=> (?x. P(matrify x))"
   (MESON_TAC [MATRIFY_VECTORIZE, VECTORIZE_MATRIFY])

  let VECTORIZE_GSPEC ← prove
   r"!P:A^N^M->bool. {vectorize m | P m} = {v | P(matrify v)}"
   (REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
    MESON_TAC [VECTORIZE_MATRIFY, MATRIFY_VECTORIZE])

  let VECTORIZE_EQ ← prove
   r"!m1 m2:real^N^M. vectorize m1 = vectorize m2 <=> m1 = m2"
   (MESON_TAC [MATRIFY_VECTORIZE])

  let MATRIFY_EQ ← prove
   r"!m1 m2:real^(M,N)finite_prod. matrify m1 = matrify m2 <=> m1 = m2"
   (MESON_TAC [VECTORIZE_MATRIFY])

  return { vectorize, matrify, VECTORIZE_COMPONENT, MATRIFY_COMPONENT,
           VECTORIZE_MATRIFY, MATRIFY_VECTORIZE, FORALL_VECTORIZE, FORALL_MATRIFY,
           EXISTS_VECTORIZE, EXISTS_MATRIFY, VECTORIZE_GSPEC, VECTORIZE_EQ,
           MATRIFY_EQ }

/- ------------------------------------------------------------------------- -/
/- A generic notion of "hull" (convex, affine, conic hull and closure).      -/
/- (misc.ml 572-746)                                                          -/
/- ------------------------------------------------------------------------- -/

structure Hull where
  hull : thm
  HULL_P : thm
  P_HULL : thm
  HULL_EQ : thm
  HULL_HULL : thm
  HULL_SUBSET : thm
  HULL_MONO : thm
  HULL_ANTIMONO : thm
  HULL_UNIV : thm
  HULL_MINIMAL : thm
  SUBSET_HULL : thm
  HULL_UNIQUE : thm
  HULL_UNION_SUBSET : thm
  HULL_UNION : thm
  HULL_UNION_LEFT : thm
  HULL_UNION_RIGHT : thm
  HULL_INSERT : thm
  HULL_REDUNDANT_EQ : thm
  HULL_REDUNDANT : thm
  HULL_INDUCT : thm
  HULL_INC : thm
  HULL_IMAGE_SUBSET : thm
  HULL_IMAGE_GALOIS : thm
  HULL_IMAGE : thm
  IS_HULL : thm
  HULLS_EQ : thm
  HULL_P_AND_Q : thm
  HULL_UNIONS_SUBSET : thm
  HULL_INTERS_SUBSET : thm
  HULL_INTER_SUBSET : thm
  deriving Inhabited

@[nospecialize]
def setupHull [HolBase] (D : MiscDeps) : ExceptT String IO Hull := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, new_definition,
        parse_as_infix, .. } := D
  let { BIJECTIVE_LEFT_RIGHT_INVERSE, EQ_IMP, EXTENSION, FORALL_IN_GSPEC,
        IMAGE_SUBSET, IN, INTERS_GSPEC, .. } := D.core1
  let { IN_ELIM_THM, IN_INTERS, .. } := D.core2
  let { SUBSET, SUBSET_ANTISYM, SUBSET_ANTISYM_EQ, SUBSET_INTERS, SUBSET_TRANS,
        SUBSET_UNION, SUBSET_UNIV, UNIONS_SUBSET, UNION_SUBSET, .. } := D.core3
  -- @@SCOPE END

  parse_as_infix ("hull", (21, "left"))

  let hull ← new_definition
   r"P hull s = INTERS {t | P t /\ s SUBSET t}"

  let HULL_P ← prove
   r"!P s. P s ==> (P hull s = s)"
   (REWRITE_TAC [hull, EXTENSION, IN_INTERS, IN_ELIM_THM] THEN
    MESON_TAC [SUBSET])

  let P_HULL ← prove
   r"!P s. (!f. (!s. s IN f ==> P s) ==> P(INTERS f)) ==> P(P hull s)"
   (REWRITE_TAC [hull] THEN SIMP_TAC [IN_ELIM_THM])

  let HULL_EQ ← prove
   r"!P s. (!f. (!s. s IN f ==> P s) ==> P(INTERS f))
         ==> ((P hull s = s) <=> P s)"
   (MESON_TAC [P_HULL, HULL_P])

  let HULL_HULL ← prove
   r"!P s. P hull (P hull s) = P hull s"
   (REWRITE_TAC [hull, EXTENSION, IN_INTERS, IN_ELIM_THM, SUBSET] THEN
    MESON_TAC [])

  let HULL_SUBSET ← prove
   r"!P s. s SUBSET (P hull s)"
   (REWRITE_TAC [hull, SUBSET, IN_INTERS, IN_ELIM_THM] THEN MESON_TAC [])

  let HULL_MONO ← prove
   r"!P s t. s SUBSET t ==> (P hull s) SUBSET (P hull t)"
   (REWRITE_TAC [hull, SUBSET, IN_INTERS, IN_ELIM_THM] THEN MESON_TAC [])

  let HULL_ANTIMONO ← prove
   r"!P Q s. P SUBSET Q ==> (Q hull s) SUBSET (P hull s)"
   (REWRITE_TAC [SUBSET, hull, IN_INTERS, IN_ELIM_THM] THEN MESON_TAC [IN])

  let HULL_UNIV ← prove
   r"!P:(A->bool)->bool. P hull UNIV = UNIV"
   (REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ, SUBSET_UNIV, HULL_SUBSET])

  let HULL_MINIMAL ← prove
   r"!P s t. s SUBSET t /\ P t ==> (P hull s) SUBSET t"
   (REWRITE_TAC [hull, SUBSET, IN_INTERS, IN_ELIM_THM] THEN MESON_TAC [])

  let SUBSET_HULL ← prove
   r"!P s t. P t ==> ((P hull s) SUBSET t <=> s SUBSET t)"
   (REWRITE_TAC [hull, SUBSET, IN_INTERS, IN_ELIM_THM] THEN MESON_TAC [])

  let HULL_UNIQUE ← prove
   r"!P s t. s SUBSET t /\ P t /\ (!t'. s SUBSET t' /\ P t' ==> t SUBSET t')
           ==> (P hull s = t)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC [hull, SUBSET, IN_INTERS, IN_ELIM_THM] THEN
    ASM_MESON_TAC [SUBSET_HULL, SUBSET])

  let HULL_UNION_SUBSET ← prove
   r"!P s t. (P hull s) UNION (P hull t) SUBSET (P hull (s UNION t))"
   (SIMP_TAC [UNION_SUBSET, HULL_MONO, SUBSET_UNION])

  let HULL_UNION ← prove
   r"!P s t. P hull (s UNION t) = P hull (P hull s UNION P hull t)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [hull] THEN
    AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM, UNION_SUBSET] THEN
    MESON_TAC [SUBSET_HULL])

  let HULL_UNION_LEFT ← prove
   r"!P s t:A->bool.
        P hull (s UNION t) = P hull (P hull s UNION t)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [hull] THEN
    AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM, UNION_SUBSET] THEN
    MESON_TAC [SUBSET_HULL])

  let HULL_UNION_RIGHT ← prove
   r"!P s t:A->bool.
        P hull (s UNION t) = P hull (s UNION P hull t)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [hull] THEN
    AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM, UNION_SUBSET] THEN
    MESON_TAC [SUBSET_HULL])

  let HULL_INSERT ← prove
   r"!P a s. P hull (a INSERT s) = P hull (a INSERT P hull s)"
   (ONCE_REWRITE_TAC [← SET_RULE (← q r"a INSERT s = {a} UNION s")] THEN
    ONCE_REWRITE_TAC [HULL_UNION] THEN REWRITE_TAC [HULL_HULL])

  let HULL_REDUNDANT_EQ ← prove
   r"!P a s. a IN (P hull s) <=> (P hull (a INSERT s) = P hull s)"
   (REWRITE_TAC [hull] THEN SET_TAC [])

  let HULL_REDUNDANT ← prove
   r"!P a s. a IN (P hull s) ==> (P hull (a INSERT s) = P hull s)"
   (REWRITE_TAC [HULL_REDUNDANT_EQ])

  let HULL_INDUCT ← prove
   r"!P p s. (!x:A. x IN s ==> p x) /\ P {x | p x}
           ==> !x. x IN P hull s ==> p x"
   (REPEAT GEN_TAC THEN
    MP_TAC (← ISPECL [← q r"P:(A->bool)->bool", ← q r"s:A->bool", ← q r"{x:A | p x}"]
                     HULL_MINIMAL) THEN
    REWRITE_TAC [SUBSET, IN_ELIM_THM])

  let HULL_INC ← prove
   r"!P s x. x IN s ==> x IN P hull s"
   (MESON_TAC [← REWRITE_RULE [SUBSET] HULL_SUBSET])

  let HULL_IMAGE_SUBSET ← prove
   r"!P f s. P(P hull s) /\ (!s. P s ==> P(IMAGE f s))
           ==> P hull (IMAGE f s) SUBSET (IMAGE f (P hull s))"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
    ASM_SIMP_TAC [IMAGE_SUBSET, HULL_SUBSET])

  let HULL_IMAGE_GALOIS ← prove
   r"!P f g s. (!s. P(P hull s)) /\
             (!s. P s ==> P(IMAGE f s)) /\ (!s. P s ==> P(IMAGE g s)) /\
             (!s t. s SUBSET IMAGE g t <=> IMAGE f s SUBSET t)
             ==> P hull (IMAGE f s) = IMAGE f (P hull s)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    ASM_SIMP_TAC [HULL_IMAGE_SUBSET] THEN
    FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC id [← GSYM th])) THEN
    MATCH_MP_TAC HULL_MINIMAL THEN
    ASM_SIMP_TAC [HULL_SUBSET])

  let HULL_IMAGE ← prove
   r"!P f s. (!s. P(P hull s)) /\ (!s. P(IMAGE f s) <=> P s) /\
           (!x y:A. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
           ==> P hull (IMAGE f s) = IMAGE f (P hull s)"
   (REPEAT GEN_TAC THEN
    REPLICATE_TAC 2 (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC [BIJECTIVE_LEFT_RIGHT_INVERSE] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"g:A->A") STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC HULL_IMAGE_GALOIS THEN EXISTS_TAC (← q r"g:A->A") THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
    X_GEN_TAC (← q r"s:A->bool") THEN
    FIRST_X_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [← GSYM th])) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC [])

  let IS_HULL ← prove
   r"!P s. (!f. (!s. s IN f ==> P s) ==> P(INTERS f))
         ==> (P s <=> ?t. s = P hull t)"
   (MESON_TAC [HULL_P, P_HULL])

  let HULLS_EQ ← prove
   r"!P s t.
        (!f. (!s. s IN f ==> P s) ==> P (INTERS f)) /\
        s SUBSET P hull t /\ t SUBSET P hull s
        ==> P hull s = P hull t"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    CONJ_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
    ASM_SIMP_TAC [P_HULL])

  let HULL_P_AND_Q ← prove
   r"!P Q. (!f. (!s. s IN f ==> P s) ==> P(INTERS f)) /\
         (!f. (!s. s IN f ==> Q s) ==> Q(INTERS f)) /\
         (!s. Q s ==> Q(P hull s))
         ==> (\x. P x /\ Q x) hull s = P hull (Q hull s)"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HULL_UNIQUE THEN ASM_SIMP_TAC [HULL_INC, SUBSET_HULL] THEN
    ASM_MESON_TAC [P_HULL, HULL_SUBSET, SUBSET_TRANS])

  let HULL_UNIONS_SUBSET ← prove
   r"!P f. UNIONS {P hull s | s IN f} SUBSET P hull (UNIONS f)"
   (REWRITE_TAC [UNIONS_SUBSET, FORALL_IN_GSPEC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC [])

  let HULL_INTERS_SUBSET ← prove
   r"!P f. P hull (INTERS f) SUBSET INTERS {P hull s | s IN f}"
   (REWRITE_TAC [SUBSET_INTERS, FORALL_IN_GSPEC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC [])

  let HULL_INTER_SUBSET ← prove
   r"!P s t. P hull (s INTER t) SUBSET (P hull s) INTER (P hull t)"
   (REWRITE_TAC [hull, INTERS_GSPEC] THEN SET_TAC [])

  return { hull, HULL_P, P_HULL, HULL_EQ, HULL_HULL, HULL_SUBSET, HULL_MONO,
           HULL_ANTIMONO, HULL_UNIV, HULL_MINIMAL, SUBSET_HULL, HULL_UNIQUE,
           HULL_UNION_SUBSET, HULL_UNION, HULL_UNION_LEFT, HULL_UNION_RIGHT,
           HULL_INSERT, HULL_REDUNDANT_EQ, HULL_REDUNDANT, HULL_INDUCT, HULL_INC,
           HULL_IMAGE_SUBSET, HULL_IMAGE_GALOIS, HULL_IMAGE, IS_HULL, HULLS_EQ,
           HULL_P_AND_Q, HULL_UNIONS_SUBSET, HULL_INTERS_SUBSET,
           HULL_INTER_SUBSET }

/- ------------------------------------------------------------------------- -/
/- Limit-argument lemmas, a sharper indexing lemma, geometric progression,   -/
/- and the segment `from n`.  (misc.ml 748-893)                               -/
/- ------------------------------------------------------------------------- -/

structure Limits where
  FORALL_POS_MONO : thm
  FORALL_POS_MONO_1 : thm
  FORALL_POS_MONO_EQ : thm
  FORALL_POS_MONO_1_EQ : thm
  REAL_ARCH_RDIV_EQ_0 : thm
  FINITE_INDEX_NUMSEG_SPECIAL : thm
  SUM_GP_BASIC : thm
  SUM_GP_MULTIPLIED : thm
  SUM_GP : thm
  SUM_GP_OFFSET : thm
  «from» : thm
  FROM_0 : thm
  IN_FROM : thm
  FROM_MONO : thm
  FROM_INTER_NUMSEG_GEN : thm
  FROM_INTER_NUMSEG_MAX : thm
  FROM_INTER_NUMSEG : thm
  INFINITE_FROM : thm
  FINITE_INTER_NUMSEG : thm
  FROM_NONEMPTY : thm
  deriving Inhabited

@[nospecialize]
def setupLimits [HolBase] (D : MiscDeps) (BLemmas : Lemmas) :
    ExceptT String IO Limits := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC,
        REAL_ARITH_TAC, SET_TAC, new_definition, .. } := D
  let { CARD_EQ_0, CARD_EQ_BIJECTIONS_SPECIAL, CARD_NUMSEG_1, EXTENSION,
        FINITE_NUMSEG, FINITE_NUMSEG_LT, FINITE_SUBSET, INFINITE_DIFF_FINITE,
        INTER_SUBSET, .. } := D.core1
  let { IN_DIFF, IN_ELIM_THM, IN_INTER, IN_NUMSEG, IN_UNIV, LE_0, LE_1, LE_REFL,
        LE_TRANS, LT_NZ, MONO_EXISTS, NOT_IN_EMPTY, REAL_ADD_LDISTRIB,
        REAL_ARCH, REAL_ARCH_INV, REAL_DIV_LMUL, REAL_EQ_LCANCEL_IMP,
        REAL_LET_ANTISYM, REAL_LE_ANTISYM, REAL_LT_INV_EQ, .. } := D.core2
  let { REAL_LT_TRANS, REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LZERO,
        REAL_MUL_RID, REAL_MUL_SYM, REAL_NOT_LT, REAL_OF_NUM_ADD,
        REAL_OF_NUM_LT, REAL_OF_NUM_SUC, REAL_POW_ADD, REAL_POW_ONE, REAL_SUB_0,
        REAL_SUB_RDISTRIB, SUBSET, SUM_CLAUSES_NUMSEG, SUM_CONST_NUMSEG,
        SUM_OFFSET_0, SUM_RMUL, SUM_TRIV_NUMSEG, num_INFINITE, real_div,
        real_pow, .. } := D.core3
  let { FORALL_SUC, .. } := BLemmas
  -- @@SCOPE END

  let FORALL_POS_MONO ← prove
   r"!P. (!d e. d < e /\ P d ==> P e) /\ (!n. ~(n = 0) ==> P(inv(&n)))
       ==> !e. &0 < e ==> P e"
   (MESON_TAC [REAL_ARCH_INV, REAL_LT_TRANS])

  let FORALL_POS_MONO_1 ← prove
   r"!P. (!d e. d < e /\ P d ==> P e) /\ (!n. P(inv(&n + &1)))
       ==> !e. &0 < e ==> P e"
   (REWRITE_TAC [REAL_OF_NUM_SUC, ← GSYM FORALL_SUC, FORALL_POS_MONO])

  let FORALL_POS_MONO_EQ ← prove
   r"!P. (!d e. d < e /\ P d ==> P e)
       ==> ((!e. &0 < e ==> P e) <=> (!n. ~(n = 0) ==> P(inv(&n))))"
   (MESON_TAC [REAL_ARCH_INV, REAL_LT_INV_EQ, REAL_LT_TRANS, LE_1,
               REAL_OF_NUM_LT])

  let FORALL_POS_MONO_1_EQ ← prove
   r"!P. (!d e. d < e /\ P d ==> P e)
       ==> ((!e. &0 < e ==> P e) <=> (!n. P(inv(&n + &1))))"
   (GEN_TAC THEN
    DISCH_THEN (fun th => tactic_of do pure (SUBST1_TAC (← MATCH_MP FORALL_POS_MONO_EQ th))) THEN
    REWRITE_TAC [REAL_OF_NUM_SUC, ← GSYM FORALL_SUC])

  let REAL_ARCH_RDIV_EQ_0 ← prove
   r"!x c. &0 <= x /\ &0 <= c /\ (!m. 0 < m ==> &m * x <= c) ==> x = &0"
   (SIMP_TAC [← GSYM REAL_LE_ANTISYM, ← GSYM REAL_NOT_LT] THEN REPEAT STRIP_TAC THEN
    POP_ASSUM (fun th => tactic_of do
      pure (STRIP_ASSUME_TAC (← SPEC (← q r"c:real") (← MATCH_MP REAL_ARCH th)))) THEN
    ASM_CASES_TAC (← q r"n=0") THENL
     [POP_ASSUM SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC (REWRITE_RULE [REAL_MUL_LZERO]) THEN
      ASM_MESON_TAC [REAL_LET_ANTISYM],
      ASM_MESON_TAC [REAL_LET_ANTISYM, REAL_MUL_SYM, LT_NZ]])

  let FINITE_INDEX_NUMSEG_SPECIAL ← prove
   r"!s a:A.
        FINITE s /\ a IN s
        ==> ?f. (!i j. i IN 1..CARD s /\ j IN 1..CARD s /\ f i = f j
                       ==> i = j) /\
                s = IMAGE f (1..CARD s) /\
                f 1 = a"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"1..CARD(s:A->bool)", ← q r"s:A->bool", ← q r"1", ← q r"a:A"]
          CARD_EQ_BIJECTIONS_SPECIAL) THEN
    ANTS_TAC THENL [ALL_TAC, MATCH_MP_TAC MONO_EXISTS THEN SET_TAC []] THEN
    ASM_REWRITE_TAC [FINITE_NUMSEG, CARD_NUMSEG_1, IN_NUMSEG, LE_REFL] THEN
    ASM_SIMP_TAC [CARD_EQ_0, ← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")] THEN
    ASM SET_TAC [])

  let SUM_GP_BASIC ← prove
   r"!x n. (&1 - x) * sum(0..n) (\i. x pow i) = &1 - x pow (SUC n)"
   (GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [SUM_CLAUSES_NUMSEG] THEN
    REWRITE_TAC [real_pow, REAL_MUL_RID, LE_0] THEN
    ASM_REWRITE_TAC [REAL_ADD_LDISTRIB, real_pow] THEN REAL_ARITH_TAC)

  let SUM_GP_MULTIPLIED ← prove
   r"!x m n. m <= n
           ==> ((&1 - x) * sum(m..n) (\i. x pow i) = x pow m - x pow (SUC n))"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC
     [SUM_OFFSET_0, REAL_POW_ADD, REAL_MUL_ASSOC, SUM_GP_BASIC, SUM_RMUL] THEN
    REWRITE_TAC [REAL_SUB_RDISTRIB, ← GSYM REAL_POW_ADD, REAL_MUL_LID] THEN
    ASM_SIMP_TAC [← ARITH_RULE (← q r"m <= n ==> (SUC(n - m) + m = SUC n)")])

  let SUM_GP ← prove
   r"!x m n.
        sum(m..n) (\i. x pow i) =
                if n < m then &0
                else if x = &1 then &((n + 1) - m)
                else (x pow m - x pow (SUC n)) / (&1 - x)"
   (REPEAT GEN_TAC THEN
    DISJ_CASES_TAC (← ARITH_RULE (← q r"n < m \/ ~(n < m) /\ m <= n:num")) THEN
    ASM_SIMP_TAC [SUM_TRIV_NUMSEG] THEN COND_CASES_TAC THENL
     [ASM_REWRITE_TAC [REAL_POW_ONE, SUM_CONST_NUMSEG, REAL_MUL_RID], ALL_TAC] THEN
    MATCH_MP_TAC REAL_EQ_LCANCEL_IMP THEN EXISTS_TAC (← q r"&1 - x") THEN
    ASM_SIMP_TAC [REAL_DIV_LMUL, REAL_SUB_0, SUM_GP_MULTIPLIED])

  let SUM_GP_OFFSET ← prove
   r"!x m n. sum(m..m+n) (\i. x pow i) =
                if x = &1 then &n + &1
                else x pow m * (&1 - x pow (SUC n)) / (&1 - x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [SUM_GP, ← ARITH_RULE (← q r"~(m + n < m:num)")] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THENL
     [REWRITE_TAC [REAL_OF_NUM_ADD] THEN AP_TERM_TAC THEN ARITH_TAC,
      REWRITE_TAC [real_div, real_pow, REAL_POW_ADD] THEN REAL_ARITH_TAC])

  let «from» ← new_definition
   r"from n = {m:num | n <= m}"

  let FROM_0 ← prove
   r"from 0 = (:num)"
   (REWRITE_TAC [«from», LE_0] THEN SET_TAC [])

  let IN_FROM ← prove
   r"!m n. m IN from n <=> n <= m"
   (REWRITE_TAC [«from», IN_ELIM_THM])

  let FROM_MONO ← prove
   r"!m n. from m SUBSET from n <=> n <= m"
   (REWRITE_TAC [SUBSET, IN_FROM] THEN MESON_TAC [LE_TRANS, LE_REFL])

  let FROM_INTER_NUMSEG_GEN ← prove
   r"!k m n. (from k) INTER (m..n) = (if m < k then k..n else m..n)"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC [«from», IN_ELIM_THM, IN_INTER, IN_NUMSEG, EXTENSION] THEN
    ARITH_TAC)

  let FROM_INTER_NUMSEG_MAX ← prove
   r"!m n p. from p INTER (m..n) = (MAX p m..n)"
   (REWRITE_TAC [EXTENSION, IN_INTER, IN_NUMSEG, IN_FROM] THEN ARITH_TAC)

  let FROM_INTER_NUMSEG ← prove
   r"!k n. (from k) INTER (0..n) = k..n"
   (REWRITE_TAC [«from», IN_ELIM_THM, IN_INTER, IN_NUMSEG, EXTENSION] THEN
    ARITH_TAC)

  let INFINITE_FROM ← prove
   r"!n. INFINITE(from n)"
   (GEN_TAC THEN
    SUBGOAL_THEN (← q r"from n = (:num) DIFF {i | i < n}")
     (fun th => SIMP_TAC [th, INFINITE_DIFF_FINITE, FINITE_NUMSEG_LT,
     num_INFINITE]) THEN
    REWRITE_TAC [EXTENSION, «from», IN_DIFF, IN_UNIV, IN_ELIM_THM] THEN ARITH_TAC)

  let FINITE_INTER_NUMSEG ← prove
   r"!s m n. FINITE(s INTER (m..n))"
   (MESON_TAC [FINITE_SUBSET, FINITE_NUMSEG, INTER_SUBSET])

  let FROM_NONEMPTY ← prove
   r"!n. ~(from n = {})"
   (GEN_TAC THEN REWRITE_TAC [EXTENSION, IN_FROM, NOT_IN_EMPTY] THEN
    MESON_TAC [LE_REFL])

  return { FORALL_POS_MONO, FORALL_POS_MONO_1, FORALL_POS_MONO_EQ,
           FORALL_POS_MONO_1_EQ, REAL_ARCH_RDIV_EQ_0, FINITE_INDEX_NUMSEG_SPECIAL,
           SUM_GP_BASIC, SUM_GP_MULTIPLIED, SUM_GP, SUM_GP_OFFSET, «from», FROM_0,
           IN_FROM, FROM_MONO, FROM_INTER_NUMSEG_GEN, FROM_INTER_NUMSEG_MAX,
           FROM_INTER_NUMSEG, INFINITE_FROM, FINITE_INTER_NUMSEG, FROM_NONEMPTY }

/- ------------------------------------------------------------------------- -/
/- Make a Horner-style evaluation of sum(m..n) (\k. a(k) * x pow k).         -/
/- (misc.ml 895-919)                                                          -/
/- ------------------------------------------------------------------------- -/

/-- The recursive `conv` of `HORNER_SUM_CONV` (misc.ml 915-918). -/
partial def hornerSumGo [HolBase] (conv_0 conv_s REAL_RAT_REDUCE_CONV : ioconv) :
    ioconv := fun tm => do
  match ← (conv_0 THENC REAL_RAT_REDUCE_CONV) tm with
  | .ok th => pure (.ok th)
  | .error _ =>
    (conv_s THENC RAND_CONV (RAND_CONV (hornerSumGo conv_0 conv_s REAL_RAT_REDUCE_CONV))
     THENC REAL_RAT_REDUCE_CONV) tm

/- ------------------------------------------------------------------------- -/
/- Some general lemmas about subsequences.  (misc.ml 921-1007)               -/
/- ------------------------------------------------------------------------- -/

structure Subseq where
  HORNER_SUM_CONV : ioconv
  SUBSEQUENCE_STEPWISE : thm
  SUBSEQUENCE_IMP_INJECTIVE : thm
  MONOTONE_BIGGER : thm
  INFINITE_ENUMERATE_WEAK : thm
  INFINITE_ENUMERATE_EQ_ALT : thm
  MONOTONE_SUBSEQUENCE : thm
  CONVERGENT_BOUNDED_INCREASING : thm
  CONVERGENT_BOUNDED_MONOTONE : thm
  deriving Inhabited

@[nospecialize]
def setupSubseq [HolBase] (D : MiscDeps) : ExceptT String IO Subseq := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, REAL_ARITH, SET_TAC,
        NUM_REDUCE_CONV, REAL_RAT_REDUCE_CONV, num_CONV,
        prove_recursive_functions_exist, .. } := D
  let { ADD1, ADD_ASSOC, DE_MORGAN_THM, FORALL_IN_IMAGE, INFINITE_ENUMERATE,
        INFINITE_IMAGE, INFINITE_SUPERSET, .. } := D.core1
  let { IN_UNIV, LE, LEFT_ADD_DISTRIB, LE_0, LT, LTE_TRANS, LT_IMP_LE, LT_LE,
        LT_REFL, LT_TRANS, MONO_EXISTS, NOT_EXISTS_THM, NOT_FORALL_THM, NOT_IMP,
        REAL_ABS_NEG, REAL_COMPLETE, REAL_LE_NEG2, REAL_LE_REFL, REAL_LE_TRANS,
        REAL_LT_LE, REAL_LT_REFL, .. } := D.core2
  let { REAL_MUL_RID, REAL_NOT_LE, REAL_NOT_LT, RIGHT_OR_EXISTS_THM, SKOLEM_THM,
        SUBSET, SUM_CLAUSES_LEFT, SUM_CLAUSES_NUMSEG, SUM_LMUL, SUM_OFFSET,
        TRANSITIVE_STEPWISE_LT, WLOG_LT, num_INFINITE, num_RECURSION,
        real_pow, .. } := D.core3
  -- @@SCOPE END

  let HORNER_SUM_CONV : ioconv ← do
    let (horner_0, horner_s) ← CONJ_PAIR (← prove
     r"(sum(0..0) (\i. c(i) * x pow i) = c 0) /\
     (sum(0..SUC n) (\i. c(i) * x pow i) =
      c(0) + x * sum(0..n) (\i. c(i+1) * x pow i))"
     (REWRITE_TAC [← CONJUNCT1 SUM_CLAUSES_NUMSEG] THEN
      REWRITE_TAC [← GSYM SUM_LMUL] THEN
      ONCE_REWRITE_TAC [← REAL_ARITH (← q r"x * c * y:real = c * x * y")] THEN
      REWRITE_TAC [← GSYM (← CONJUNCT2 real_pow), ADD1] THEN
      REWRITE_TAC [← GSYM (← SPEC (← q r"1") SUM_OFFSET)] THEN
      SIMP_TAC [SUM_CLAUSES_LEFT, LE_0, real_pow, REAL_MUL_RID]))
    let conv_0 := (← GEN_REWRITE_CONV_NET id [horner_0]) THENC NUM_REDUCE_CONV
    let conv_s := LAND_CONV (RAND_CONV num_CONV) THENC
                  (← GEN_REWRITE_CONV_NET id [horner_s]) THENC
                  (← GEN_REWRITE_CONV_NET ONCE_DEPTH_CONV [LEFT_ADD_DISTRIB]) THENC
                  (← GEN_REWRITE_CONV_NET TOP_DEPTH_CONV [← GSYM ADD_ASSOC]) THENC
                  NUM_REDUCE_CONV
    pure (hornerSumGo conv_0 conv_s REAL_RAT_REDUCE_CONV)

  let SUBSEQUENCE_STEPWISE ← prove
   r"!r:num->num. (!m n. m < n ==> r m < r n) <=> (!n. r n < r(SUC n))"
   (GEN_TAC THEN EQ_TAC THEN SIMP_TAC [← ARITH_RULE (← q r"n < SUC n")] THEN
    DISCH_TAC THEN MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN
    ASM_REWRITE_TAC [] THEN ARITH_TAC)

  let SUBSEQUENCE_IMP_INJECTIVE ← prove
   r"!r:num->num. (!m n. m < n ==> r m < r n) ==> (!m n. r m = r n <=> m = n)"
   (GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC WLOG_LT THEN
    ASM_MESON_TAC [LT_REFL])

  let MONOTONE_BIGGER ← prove
   r"!r. (!m n. m < n ==> r(m) < r(n)) ==> !n:num. n <= r(n)"
   (GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
    ASM_MESON_TAC [LE_0, ← ARITH_RULE (← q r"n <= m /\ m < p ==> SUC n <= p"), LT])

  let INFINITE_ENUMERATE_WEAK ← prove
   r"!s:num->bool.
       INFINITE s
       ==> ?r:num->num. (!m n. m < n ==> r(m) < r(n)) /\ (!n. r n IN s)"
   (GEN_TAC THEN
    DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← MATCH_MP INFINITE_ENUMERATE th))) THEN
    MATCH_MP_TAC MONO_EXISTS THEN SET_TAC [])

  let INFINITE_ENUMERATE_EQ_ALT ← prove
   r"!s:num->bool.
        INFINITE s <=> ?r. (!m n:num. m < n ==> r m < r n) /\ (!n. r n IN s)"
   (GEN_TAC THEN EQ_TAC THEN REWRITE_TAC [INFINITE_ENUMERATE_WEAK] THEN
    STRIP_TAC THEN MATCH_MP_TAC INFINITE_SUPERSET THEN
    EXISTS_TAC (← q r"IMAGE (r:num->num) (:num)") THEN
    ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
    MATCH_MP_TAC INFINITE_IMAGE THEN
    REWRITE_TAC [num_INFINITE, IN_UNIV] THEN
    ASM_MESON_TAC [SUBSEQUENCE_IMP_INJECTIVE])

  let MONOTONE_SUBSEQUENCE ← prove
   r"!s:num->real. ?r:num->num.
           (!m n. m < n ==> r(m) < r(n)) /\
           ((!m n. m <= n ==> s(r(m)) <= s(r(n))) \/
            (!m n. m <= n ==> s(r(n)) <= s(r(m))))"
   (GEN_TAC THEN
    ASM_CASES_TAC (← q r"!n:num. ?p. n < p /\ !m. p <= m ==> s(m) <= s(p)") THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC [NOT_FORALL_THM, NOT_EXISTS_THM, NOT_IMP, DE_MORGAN_THM] THEN
    REWRITE_TAC [RIGHT_OR_EXISTS_THM, SKOLEM_THM, REAL_NOT_LE, REAL_NOT_LT] THENL
     [ABBREV_TAC (← q r"N = 0"), DISCH_THEN (X_CHOOSE_THEN (← q r"N:num") MP_TAC)] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"next:num->num") STRIP_ASSUME_TAC) THEN
    tactic_of (do
      pure (MP_TAC (← prove_recursive_functions_exist num_RECURSION
       (← q r"(r 0 = next(SUC N)) /\ (!n. r(SUC n) = next(r n))")))) THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THENL
     [SUBGOAL_THEN (← q r"!m:num n:num. r n <= m ==> s(m) <= s(r n):real")
      ASSUME_TAC THEN TRY CONJ_TAC THEN TRY DISJ2_TAC THEN
      GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [LT, LE] THEN
      ASM_MESON_TAC [REAL_LE_TRANS, REAL_LE_REFL, LT_IMP_LE, LT_TRANS],
      SUBGOAL_THEN (← q r"!n. N < (r:num->num) n") ASSUME_TAC THEN
      TRY (CONJ_TAC THENL [GEN_TAC, DISJ1_TAC THEN GEN_TAC]) THEN
      INDUCT_TAC THEN ASM_REWRITE_TAC [LT, LE] THEN
      TRY STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC [REAL_LT_REFL, LT_LE, LTE_TRANS, REAL_LE_REFL,
                     REAL_LT_LE, REAL_LE_TRANS, LT]])

  let CONVERGENT_BOUNDED_INCREASING ← prove
   r"!s:num->real b. (!m n. m <= n ==> s m <= s n) /\ (!n. abs(s n) <= b)
                   ==> ?l. !e. &0 < e ==> ?N. !n. N <= n ==> abs(s n - l) < e"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPEC (← q r"\x. ?n. (s:num->real) n = x") REAL_COMPLETE) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [ASM_MESON_TAC [← REAL_ARITH (← q r"abs(x) <= b ==> x <= b")], ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"l:real") THEN STRIP_TAC THEN
    X_GEN_TAC (← q r"e:real") THEN STRIP_TAC THEN
    FIRST_X_ASSUM (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"l - e") th))) THEN
    ASM_MESON_TAC [← REAL_ARITH (← q r"&0 < e ==> ~(l <= l - e)"),
        ← REAL_ARITH (← q r"x <= y /\ y <= l /\ ~(x <= l - e) ==> abs(y - l) < e")])

  let CONVERGENT_BOUNDED_MONOTONE ← prove
   r"!s:num->real b. (!n. abs(s n) <= b) /\
                   ((!m n. m <= n ==> s m <= s n) \/
                    (!m n. m <= n ==> s n <= s m))
                   ==> ?l. !e. &0 < e ==> ?N. !n. N <= n ==> abs(s n - l) < e"
   (REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC [CONVERGENT_BOUNDED_INCREASING], ALL_TAC] THEN
    MP_TAC (← SPEC (← q r"\n. --((s:num->real) n)") CONVERGENT_BOUNDED_INCREASING) THEN
    ASM_REWRITE_TAC [REAL_LE_NEG2, REAL_ABS_NEG] THEN
    ASM_MESON_TAC [← REAL_ARITH (← q r"abs(x - --l) = abs(--x - l)")])

  return { HORNER_SUM_CONV, SUBSEQUENCE_STEPWISE, SUBSEQUENCE_IMP_INJECTIVE,
           MONOTONE_BIGGER, INFINITE_ENUMERATE_WEAK, INFINITE_ENUMERATE_EQ_ALT,
           MONOTONE_SUBSEQUENCE, CONVERGENT_BOUNDED_INCREASING,
           CONVERGENT_BOUNDED_MONOTONE }

/- ------------------------------------------------------------------------- -/
/- Monotonic functions R->R, the diagonalization argument, and countability -/
/- of some relevant sets.  (misc.ml 1009-1184)                               -/
/- ------------------------------------------------------------------------- -/

structure Diagonal where
  STRICTLY_INCREASING_ALT : thm
  STRICTLY_DECREASING_ALT : thm
  REAL_NON_MONOTONE : thm
  SUBSEQUENCE_DIAGONALIZATION_LEMMA : thm
  COUNTABLE_INTEGER : thm
  CARD_EQ_INTEGER : thm
  COUNTABLE_RATIONAL : thm
  CARD_EQ_RATIONAL : thm
  COUNTABLE_INTEGER_COORDINATES : thm
  COUNTABLE_RATIONAL_COORDINATES : thm
  deriving Inhabited

@[nospecialize]
def setupDiagonal [HolBase] (D : MiscDeps) (BSubseq : Subseq) :
    ExceptT String IO Diagonal := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, INDUCT_TAC, MESON, MESON_TAC,
        METIS_TAC, REAL_ARITH, REAL_ARITH_TAC, SET_RULE, CNF_CONV, NNFC_CONV,
        prove_recursive_functions_exist, .. } := D
  let { ADD_CLAUSES, AND_FORALL_THM, CONJ_ASSOC, CONTRAPOS_THM, DE_MORGAN_THM,
        ETA_AX, EXISTS_PAIR_THM, FORALL_AND_THM, FORALL_UNWIND_THM2, IMP_CONJ,
        IN, IN_CROSS, .. } := D.core1
  let { IN_IMAGE, IN_UNION, IN_UNIV, LEFT_IMP_EXISTS_THM, LET_TRANS, LE_EXISTS,
        LE_LT, LE_REFL, LE_TRANS, LT_IMP_LE, MONO_AND, MONO_EXISTS,
        NOT_FORALL_THM, NOT_IMP, OR_EXISTS_THM, REAL_LET_ANTISYM, REAL_LE_LT,
        REAL_LT_ANTISYM, REAL_LT_IMP_LE, REAL_LT_LE, REAL_LT_REFL, .. } := D.core2
  let { REAL_LT_TOTAL, REAL_NOT_LE, REAL_OF_NUM_EQ, SKOLEM_THM, SUBSET,
        SWAP_FORALL_THM, le_c, num_INDUCTION, num_RECURSION, o_ASSOC,
        o_THM, .. } := D.core3
  let { CARD_LE_ANTISYM, COUNTABLE_ALT, COUNTABLE_CART, COUNTABLE_CROSS,
        COUNTABLE_IMAGE, COUNTABLE_SUBSET, COUNTABLE_UNION, NUM_COUNTABLE,
        INTEGER_CASES, INTEGER_CLOSED, RATIONAL_CLOSED, rational, .. } := D.lib
  let { MONOTONE_BIGGER, .. } := BSubseq
  -- @@SCOPE END

  let STRICTLY_INCREASING_ALT ← prove
   r"!P f:real->real.
        (!x y. P x /\ P y /\ x < y ==> f x < f y) <=>
        (!x y. P x /\ P y /\ x <= y ==> f x <= f y) /\
        (!x y. P x /\ P y /\ f x = f y ==> x = y)"
   (METIS_TAC [REAL_LT_TOTAL, REAL_LE_LT, REAL_LT_ANTISYM])

  let STRICTLY_DECREASING_ALT ← prove
   r"!P f:real->real.
        (!x y. P x /\ P y /\ x < y ==> f y < f x) <=>
        (!x y. P x /\ P y /\ x <= y ==> f y <= f x) /\
        (!x y. P x /\ P y /\ f x = f y ==> x = y)"
   (METIS_TAC [REAL_LT_TOTAL, REAL_LE_LT, REAL_LT_ANTISYM])

  let REAL_NON_MONOTONE ← prove
   r"!P f:real->real.
        (!x y. P x /\ P y /\ x <= y ==> f x <= f y) \/
        (!x y. P x /\ P y /\ x <= y ==> f y <= f x) <=>
        ~(?x y z. P x /\ P y /\ P z /\ x < y /\ y < z /\
                 (f x < f y /\ f z < f y \/ f y < f x /\ f y < f z))"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [MESON_TAC [REAL_LT_IMP_LE, REAL_LET_ANTISYM], ALL_TAC] THEN
    GEN_REWRITE_TAC id [← GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC [NOT_FORALL_THM, LEFT_IMP_EXISTS_THM, NOT_IMP, DE_MORGAN_THM] THEN
    ONCE_REWRITE_TAC [IMP_CONJ] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [← GSYM CONJ_ASSOC, REAL_NOT_LE, ← MESON [REAL_LT_LE] (← q
     r"(x <= y /\ (f:real->real) y < f x <=> x < y /\ f y < f x) /\
    (x <= y /\ f x < f y <=> x < y /\ f x < f y)")] THEN
    MAP_EVERY X_GEN_TAC [← q r"u:real", ← q r"v:real"] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [← q r"w:real", ← q r"z:real"] THEN STRIP_TAC THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (← REAL_ARITH (← q
     r"u:real = w \/ u < w \/ w < u"))
    THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MATCH_MP_TAC (← MESON [] (← q r"P w v z \/ P w z v ==> ?x y z. P x y z")),
      MATCH_MP_TAC (← MESON [] (← q r"P u v \/ P u w \/ P u z ==> ?x y. P x y")) THEN
      ASM_REWRITE_TAC [OR_EXISTS_THM, REAL_LT_REFL] THEN
      MATCH_MP_TAC (← MESON [] (← q r"P(v:real) \/ P z ==> ?x. P x")),
      MATCH_MP_TAC (← MESON [] (← q r"P w u \/ P w v \/ P w z ==> ?x y. P x y")) THEN
      ASM_REWRITE_TAC [OR_EXISTS_THM, REAL_LT_REFL] THEN
      MATCH_MP_TAC (← MESON [] (← q r"P(v:real) \/ P z ==> ?x. P x"))] THEN
    ASM_SIMP_TAC [REAL_LT_REFL, ← REAL_ARITH (← q r"a < b ==> ~(b < a)")] THEN
    POP_ASSUM_LIST (fun ths => (MP_TAC o end_itlist CONJ) ths.reverse) THEN
    CONV_TAC NNFC_CONV THEN CONV_TAC CNF_CONV THEN
    REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN
    ASM_CASES_TAC (← q r"u:real = w") THEN ASM_REWRITE_TAC [REAL_LT_REFL] THEN
    ASM_CASES_TAC (← q r"u:real = z") THEN ASM_REWRITE_TAC [REAL_LT_REFL] THEN
    ASM_CASES_TAC (← q r"v:real = w") THEN ASM_REWRITE_TAC [REAL_LT_REFL] THEN
    ASM_CASES_TAC (← q r"v:real = z") THEN ASM_REWRITE_TAC [REAL_LT_REFL] THEN
    REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THEN ASM_REAL_ARITH_TAC)

  let SUBSEQUENCE_DIAGONALIZATION_LEMMA ← do
    let le_trans_conj ← REWRITE_RULE [IMP_CONJ] LE_TRANS
    let mono_le ← MESON [LE_LT] (← q
       r"!f:num->num.
        (!m n. m < n ==> f m < f n) ==> (!m n. m <= n ==> f m <= f n)")
    prove
     r"!P:num->(num->A)->bool.
    (!i r:num->A. ?k. (!m n. m < n ==> k m < k n) /\ P i (r o k)) /\
    (!i r:num->A k1 k2 N.
        P i (r o k1) /\ (!j. N <= j ==> ?j'. j <= j' /\ k2 j = k1 j')
        ==> P i (r o k2))
    ==> !r:num->A. ?k. (!m n. m < n ==> k m < k n) /\ (!i. P i (r o k))"
     (REPEAT GEN_TAC THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
      GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [SKOLEM_THM] THEN
      REWRITE_TAC [FORALL_AND_THM, ← TAUT (← q
       r"(p ==> q /\ r) <=> (p ==> q) /\ (p ==> r)")] THEN
      DISCH_THEN (X_CHOOSE_THEN
       (← q r"kk:num->(num->A)->num->num") STRIP_ASSUME_TAC) THEN
      X_GEN_TAC (← q r"r:num->A") THEN
      tactic_of (do
        pure (STRIP_ASSUME_TAC (← prove_recursive_functions_exist num_RECURSION
         (← q r"(rr 0 = (kk:num->(num->A)->num->num) 0 r) /\
       (!n. rr(SUC n) = rr n o kk (SUC n) (r o rr n))")))) THEN
      EXISTS_TAC (← q r"\n. (rr:num->num->num) n n") THEN REWRITE_TAC [ETA_AX] THEN
      SUBGOAL_THEN
       (← q r"(!i. (!m n. m < n ==> (rr:num->num->num) i m < rr i n)) /\
      (!i. (P:num->(num->A)->bool) i (r o rr i))")
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC [AND_FORALL_THM] THEN
        INDUCT_TAC THEN ASM_REWRITE_TAC [o_ASSOC] THEN
        REWRITE_TAC [o_THM] THEN ASM_MESON_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"!i j n. i <= j ==> (rr:num->num->num) i n <= rr j n")
      ASSUME_TAC THENL
       [REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [LE_EXISTS] THEN
        SIMP_TAC [LEFT_IMP_EXISTS_THM] THEN SPEC_TAC (← q r"j:num", ← q r"j:num") THEN
        ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN SIMP_TAC [FORALL_UNWIND_THM2] THEN
        INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES, LE_REFL] THEN
        ASM_REWRITE_TAC [] THEN
        FIRST_ASSUM (fun th => tactic_of do
          pure (MATCH_MP_TAC (← MATCH_MP le_trans_conj th))) THEN
        REWRITE_TAC [o_THM] THEN
        FIRST_ASSUM (fun th => tactic_of do
          pure (MATCH_MP_TAC (← MATCH_MP mono_le (← SPEC (← q r"i + d:num") th)))) THEN
        SPEC_TAC (← q r"n:num", ← q r"n:num") THEN MATCH_MP_TAC MONOTONE_BIGGER THEN
        ASM_SIMP_TAC [],
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [← q r"m:num", ← q r"n:num"] THEN DISCH_TAC THEN
        MATCH_MP_TAC LET_TRANS THEN
        EXISTS_TAC (← q r"(rr:num->num->num) n m") THEN
        ASM_MESON_TAC [LT_IMP_LE],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"!m n i. n <= m ==> ?j. i <= j /\ (rr:num->num->num) m i = rr n j")
      ASSUME_TAC THENL
       [ALL_TAC,
        X_GEN_TAC (← q r"i:num") THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        EXISTS_TAC (← q r"(rr:num->num->num) i") THEN ASM_REWRITE_TAC [] THEN
        EXISTS_TAC (← q r"i:num") THEN ASM_MESON_TAC []] THEN
      SUBGOAL_THEN
       (← q r"!p d i. ?j. i <= j /\ (rr:num->num->num) (p + d) i = rr p j")
       (fun th => MESON_TAC [LE_EXISTS, th]) THEN
      X_GEN_TAC (← q r"p:num") THEN MATCH_MP_TAC num_INDUCTION THEN
      ASM_REWRITE_TAC [ADD_CLAUSES] THEN CONJ_TAC THENL
       [MESON_TAC [LE_REFL], ALL_TAC] THEN
      X_GEN_TAC (← q r"d:num") THEN DISCH_THEN (LABEL_TAC "+") THEN
      X_GEN_TAC (← q r"i:num") THEN ASM_REWRITE_TAC [o_THM] THEN
      REMOVE_THEN "+" (fun th => tactic_of do
        pure (MP_TAC (← SPEC (← q
         r"(kk:num->(num->A)->num->num) (SUC(p + d))
          ((r:num->A) o (rr:num->num->num) (p + d)) i") th))) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"j:num") THEN
      MATCH_MP_TAC MONO_AND THEN REWRITE_TAC [] THEN
      MATCH_MP_TAC le_trans_conj THEN
      SPEC_TAC (← q r"i:num", ← q r"i:num") THEN MATCH_MP_TAC MONOTONE_BIGGER THEN
      ASM_REWRITE_TAC [o_THM] THEN ASM_MESON_TAC [])

  let COUNTABLE_INTEGER ← prove
   r"COUNTABLE integer"
   (MATCH_MP_TAC COUNTABLE_SUBSET THEN EXISTS_TAC (← q
     r"IMAGE (\n. (&n:real)) (:num) UNION IMAGE (\n. --(&n)) (:num)") THEN
    SIMP_TAC [COUNTABLE_IMAGE, COUNTABLE_UNION, NUM_COUNTABLE] THEN
    REWRITE_TAC [SUBSET, IN_UNION, IN_IMAGE, IN_UNIV] THEN
    REWRITE_TAC [IN, INTEGER_CASES])

  let CARD_EQ_INTEGER ← prove
   r"integer =_c (:num)"
   (REWRITE_TAC [← GSYM CARD_LE_ANTISYM, ← GSYM COUNTABLE_ALT, COUNTABLE_INTEGER] THEN
    REWRITE_TAC [le_c] THEN EXISTS_TAC (← q r"real_of_num") THEN
    REWRITE_TAC [IN_UNIV, REAL_OF_NUM_EQ] THEN
    REWRITE_TAC [IN, INTEGER_CLOSED])

  let COUNTABLE_RATIONAL ← prove
   r"COUNTABLE rational"
   (MATCH_MP_TAC COUNTABLE_SUBSET THEN
    EXISTS_TAC (← q r"IMAGE (\(x,y). x / y) (integer CROSS integer)") THEN
    SIMP_TAC [COUNTABLE_IMAGE, COUNTABLE_CROSS, COUNTABLE_INTEGER] THEN
    REWRITE_TAC [SUBSET, IN_IMAGE, EXISTS_PAIR_THM, IN_CROSS] THEN
    REWRITE_TAC [rational, IN] THEN MESON_TAC [])

  let CARD_EQ_RATIONAL ← prove
   r"rational =_c (:num)"
   (REWRITE_TAC [← GSYM CARD_LE_ANTISYM, ← GSYM COUNTABLE_ALT, COUNTABLE_RATIONAL] THEN
    REWRITE_TAC [le_c] THEN EXISTS_TAC (← q r"real_of_num") THEN
    REWRITE_TAC [IN_UNIV, REAL_OF_NUM_EQ] THEN
    REWRITE_TAC [IN, RATIONAL_CLOSED])

  let COUNTABLE_INTEGER_COORDINATES ← prove
   r"COUNTABLE { x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> integer(x$i) }"
   (MATCH_MP_TAC COUNTABLE_CART THEN
    REWRITE_TAC [← SET_RULE (← q r"{x | P x} = P"), COUNTABLE_INTEGER])

  let COUNTABLE_RATIONAL_COORDINATES ← prove
   r"COUNTABLE { x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> rational(x$i) }"
   (MATCH_MP_TAC COUNTABLE_CART THEN
    REWRITE_TAC [← SET_RULE (← q r"{x | P x} = P"), COUNTABLE_RATIONAL])

  return { STRICTLY_INCREASING_ALT, STRICTLY_DECREASING_ALT, REAL_NON_MONOTONE,
           SUBSEQUENCE_DIAGONALIZATION_LEMMA, COUNTABLE_INTEGER, CARD_EQ_INTEGER,
           COUNTABLE_RATIONAL, CARD_EQ_RATIONAL, COUNTABLE_INTEGER_COORDINATES,
           COUNTABLE_RATIONAL_COORDINATES }

/- ------------------------------------------------------------------------- -/
/- Natural "irrational" variants of rational approximations, and            -/
/- countability of extrema for arbitrary function R->R.  (misc.ml 1186-1340) -/
/- ------------------------------------------------------------------------- -/

structure Irrational where
  IRRATIONAL_APPROXIMATION : thm
  IRRATIONAL_BETWEEN : thm
  IRRATIONAL_BETWEEN_EQ : thm
  IRRATIONAL_APPROXIMATION_STRADDLE : thm
  IRRATIONAL_APPROXIMATION_ABOVE : thm
  IRRATIONAL_APPROXIMATION_BELOW : thm
  INFINITE_IRRATIONAL_IN_RANGE : thm
  COUNTABLE_LOCAL_MAXIMA : thm
  COUNTABLE_LOCAL_MINIMA : thm
  COUNTABLE_STRICT_LOCAL_MAXIMA : thm
  COUNTABLE_STRICT_LOCAL_MINIMA : thm
  deriving Inhabited

@[nospecialize]
def setupIrrational [HolBase] (D : MiscDeps) (BDiagonal : Diagonal) :
    ExceptT String IO Irrational := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON, MESON_TAC, REAL_ARITH,
        SET_RULE, SET_TAC, .. } := D
  let { CONJ_ASSOC, DEPENDENT_CHOICE, EQ_IMP, ETA_AX, EXISTS_IN_GSPEC,
        EXISTS_PAIR_THM, FORALL_IN_GSPEC, IMAGE_o, IN, INFINITE_IMAGE,
        INFINITE_SUPERSET, IN_CROSS, .. } := D.core1
  let { IN_ELIM_PAIR_THM, IN_ELIM_THM, IN_IMAGE, IN_INTER, IN_UNIV,
        LEFT_IMP_EXISTS_THM, LT_CASES, MONO_EXISTS, REAL_EQ_NEG2, REAL_LE_NEG2,
        REAL_LT_ANTISYM, REAL_LT_IMP_LE, REAL_LT_MIN, REAL_LT_NEG2,
        REAL_LT_REFL, .. } := D.core2
  let { REAL_LT_TRANS, REAL_SUP_UNIQUE, SIMPLE_IMAGE_GEN, SUBSET,
        SWAP_EXISTS_THM, TRANSITIVE_STEPWISE_LT, num_INFINITE, o_THM, .. } := D.core3
  let { COUNTABLE_CROSS, COUNTABLE_IMAGE, COUNTABLE_IMAGE_INJ_EQ,
        COUNTABLE_INTER, COUNTABLE_SUBSET, UNCOUNTABLE_REAL,
        RATIONAL_APPROXIMATION, RATIONAL_APPROXIMATION_STRADDLE,
        RATIONAL_CLOSED, .. } := D.lib
  let { COUNTABLE_RATIONAL, .. } := BDiagonal
  -- @@SCOPE END

  let IRRATIONAL_APPROXIMATION ← prove
   r"!x e. &0 < e ==> ?y. ~(rational y) /\ abs(y - x) < e"
   (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"?z. ~rational z") STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC (← SET_RULE (← q r"~(s = (:real)) ==> ?z. ~s z")) THEN
      MESON_TAC [COUNTABLE_RATIONAL, UNCOUNTABLE_REAL],
      MP_TAC (← ISPECL [← q r"z + x:real", ← q r"e:real"] RATIONAL_APPROXIMATION) THEN
      ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"q:real") THEN STRIP_TAC THEN EXISTS_TAC (← q r"q - z:real") THEN
      ASM_REWRITE_TAC [← REAL_ARITH (← q r"q - z - x:real = q - (z + x)")] THEN
      DISCH_TAC THEN UNDISCH_TAC (← q r"~rational z") THEN REWRITE_TAC [] THEN
      ASM_MESON_TAC [RATIONAL_CLOSED, ← REAL_ARITH (← q r"z:real = q - (q - z)")]])

  let IRRATIONAL_BETWEEN ← prove
   r"!a b. a < b ==> ?q. ~rational q /\ a < q /\ q < b"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"(a + b) / &2", ← q r"(b - a) / &4"] IRRATIONAL_APPROXIMATION) THEN
    ANTS_TAC THENL [ALL_TAC, MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC []] THEN
    ASM_REAL_ARITH_TAC)

  let IRRATIONAL_BETWEEN_EQ ← prove
   r"!a b. (?q. ~rational q /\ a < q /\ q < b) <=> a < b"
   (MESON_TAC [IRRATIONAL_BETWEEN, REAL_LT_TRANS])

  let IRRATIONAL_APPROXIMATION_STRADDLE ← prove
   r"!x e. &0 < e
         ==> ?a b. ~rational a /\ ~rational b /\
                   a < x /\ x < b /\ abs(b - a) < e"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"x - e / &4", ← q r"e / &4"] IRRATIONAL_APPROXIMATION) THEN
    ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC,
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC] THEN
    MP_TAC (← ISPECL [← q r"x + e / &4", ← q r"e / &4"] IRRATIONAL_APPROXIMATION) THEN
    ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC,
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC] THEN
    ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC)

  let IRRATIONAL_APPROXIMATION_ABOVE ← prove
   r"!x e. &0 < e ==> ?q. ~rational q /\ x < q /\ q < x + e"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"x:real", ← q r"e:real"] IRRATIONAL_APPROXIMATION_STRADDLE) THEN
    ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC)

  let IRRATIONAL_APPROXIMATION_BELOW ← prove
   r"!x e. &0 < e ==> ?q. ~rational q /\ x - e < q /\ q < x"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"x:real", ← q r"e:real"] IRRATIONAL_APPROXIMATION_STRADDLE) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN
    GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC)

  let INFINITE_IRRATIONAL_IN_RANGE ← prove
   r"!a b. a < b ==> INFINITE {q | ~rational q /\ a < q /\ q < b}"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"?q. (!n. ~rational(q n) /\ a < q n /\ q n < b) /\ (!n. q(SUC n) < q n)")
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC DEPENDENT_CHOICE THEN
      REWRITE_TAC [← GSYM CONJ_ASSOC, ← GSYM REAL_LT_MIN] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC IRRATIONAL_BETWEEN THEN
      ASM_REWRITE_TAC [REAL_LT_MIN],
      MATCH_MP_TAC INFINITE_SUPERSET THEN
      EXISTS_TAC (← q r"IMAGE (q:num->real) (:num)") THEN
      CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
      MATCH_MP_TAC INFINITE_IMAGE THEN REWRITE_TAC [num_INFINITE, IN_UNIV] THEN
      SUBGOAL_THEN (← q r"!m n. m < n ==> (q:num->real) n < q m")
       (fun th => MESON_TAC [LT_CASES, th, REAL_LT_REFL]) THEN
      MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN
      ASM_MESON_TAC [REAL_LT_TRANS]])

  let COUNTABLE_LOCAL_MAXIMA ← prove
   r"!f:real->real.
    COUNTABLE {f x |x| ?d. &0 < d /\ !x'. abs(x' - x) < d ==> f(x') <= f(x)}"
   (GEN_TAC THEN
    MATCH_MP_TAC COUNTABLE_SUBSET THEN
    EXISTS_TAC (← q
     r"IMAGE (\(a,b). sup {f x | a <= x /\ x <= b})
          ((rational CROSS rational) INTER
           {(a,b) | ?x. a < x /\ x < b /\
                        !x'. a <= x' /\ x' <= b ==> f x' <= f x})") THEN
    SIMP_TAC [COUNTABLE_INTER, COUNTABLE_CROSS, COUNTABLE_RATIONAL,
              COUNTABLE_IMAGE, SUBSET, FORALL_IN_GSPEC] THEN
    X_GEN_TAC (← q r"x:real") THEN REWRITE_TAC [IN_ELIM_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d:real") STRIP_ASSUME_TAC) THEN
    REWRITE_TAC [IN_IMAGE, IN_INTER, EXISTS_PAIR_THM] THEN
    MP_TAC (← ISPECL [← q r"x:real", ← q r"d:real"] RATIONAL_APPROXIMATION_STRADDLE) THEN
    ASM_REWRITE_TAC [IN_CROSS, IN_ELIM_PAIR_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"a:real") THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"g:real") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [IN] THEN CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_SUP_UNIQUE THEN
      REWRITE_TAC [FORALL_IN_GSPEC, EXISTS_IN_GSPEC],
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN TRY (EXISTS_TAC (← q r"x:real")) THEN
    REPEAT STRIP_TAC THEN TRY (FIRST_X_ASSUM MATCH_MP_TAC) THEN
    ASM_REAL_ARITH_TAC)

  let COUNTABLE_LOCAL_MINIMA ← prove
   r"!f:real->real.
    COUNTABLE {f x |x| ?d. &0 < d /\ !x'. abs(x' - x) < d ==> f(x) <= f(x')}"
   (GEN_TAC THEN MP_TAC (← SPEC (← q r"(--) o (f:real->real)") COUNTABLE_LOCAL_MAXIMA) THEN
    ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN REWRITE_TAC [ETA_AX, IMAGE_o] THEN
    REWRITE_TAC [o_THM, REAL_LE_NEG2] THEN MATCH_MP_TAC EQ_IMP THEN
    MATCH_MP_TAC COUNTABLE_IMAGE_INJ_EQ THEN SIMP_TAC [REAL_EQ_NEG2])

  let COUNTABLE_STRICT_LOCAL_MAXIMA ← prove
   r"!f:real->real.
    COUNTABLE {x | ?d. &0 < d /\
                       !x'. abs(x' - x) < d /\ ~(x' = x) ==> f(x') < f(x)}"
   (GEN_TAC THEN
    MATCH_MP_TAC COUNTABLE_SUBSET THEN
    EXISTS_TAC (← q
     r"IMAGE (\(a,b). @x. a < x /\ x < b /\
                        !x'. a <= x' /\ x' <= b /\ ~(x' = x)
                             ==> f x' < f x)
          ((rational CROSS rational) INTER
           {(a,b) | ?x. a < x /\ x < b /\
                        !x'. a <= x' /\ x' <= b /\ ~(x' = x)
                             ==> f x' < f x})") THEN
    SIMP_TAC [COUNTABLE_INTER, COUNTABLE_CROSS, COUNTABLE_RATIONAL,
              COUNTABLE_IMAGE, SUBSET, FORALL_IN_GSPEC] THEN
    X_GEN_TAC (← q r"x:real") THEN REWRITE_TAC [IN_ELIM_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d:real") STRIP_ASSUME_TAC) THEN
    REWRITE_TAC [IN_IMAGE, IN_INTER, EXISTS_PAIR_THM] THEN
    MP_TAC (← ISPECL [← q r"x:real", ← q r"d:real"] RATIONAL_APPROXIMATION_STRADDLE) THEN
    ASM_REWRITE_TAC [IN_CROSS, IN_ELIM_PAIR_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"a:real") THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"g:real") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [IN] THEN
    MATCH_MP_TAC (← MESON [] (← q
     r"P x /\ (!x y. P x /\ P y ==> x = y) ==> x = (@y. P y) /\ (?y. P y)")) THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC,
      ASM_MESON_TAC [REAL_LT_ANTISYM, REAL_LT_IMP_LE]])

  let COUNTABLE_STRICT_LOCAL_MINIMA ← prove
   r"!f:real->real.
    COUNTABLE {x | ?d. &0 < d /\
                       !x'. abs(x' - x) < d /\ ~(x' = x) ==> f(x) < f(x')}"
   (GEN_TAC THEN
    MP_TAC (← SPEC (← q r"(--) o (f:real->real)") COUNTABLE_STRICT_LOCAL_MAXIMA) THEN
    ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN REWRITE_TAC [ETA_AX, IMAGE_o] THEN
    REWRITE_TAC [o_THM, REAL_LT_NEG2] THEN MATCH_MP_TAC EQ_IMP THEN
    MATCH_MP_TAC COUNTABLE_IMAGE_INJ_EQ THEN SIMP_TAC [REAL_EQ_NEG2])

  return { IRRATIONAL_APPROXIMATION, IRRATIONAL_BETWEEN, IRRATIONAL_BETWEEN_EQ,
           IRRATIONAL_APPROXIMATION_STRADDLE, IRRATIONAL_APPROXIMATION_ABOVE,
           IRRATIONAL_APPROXIMATION_BELOW, INFINITE_IRRATIONAL_IN_RANGE,
           COUNTABLE_LOCAL_MAXIMA, COUNTABLE_LOCAL_MINIMA,
           COUNTABLE_STRICT_LOCAL_MAXIMA, COUNTABLE_STRICT_LOCAL_MINIMA }

/- ------------------------------------------------------------------------- -/
/- A somewhat cheap but handy way of getting localized forms of various      -/
/- topological concepts (open, closed, borel, fsigma, gdelta etc.)           -/
/- (misc.ml 1342-1647)                                                        -/
/- ------------------------------------------------------------------------- -/

structure RelativeTo where
  relative_to : thm
  RELATIVE_TO_UNIV : thm
  RELATIVE_TO_IMP_SUBSET : thm
  FORALL_RELATIVE_TO : thm
  RELATIVE_TO_INC : thm
  RELATIVE_TO : thm
  RELATIVE_TO_RELATIVE_TO : thm
  RELATIVE_TO_COMPL : thm
  RELATIVE_TO_SUBSET : thm
  RELATIVE_TO_SUBSET_TRANS : thm
  RELATIVE_TO_MONO : thm
  RELATIVE_TO_SUBSET_INC : thm
  RELATIVE_TO_INTER : thm
  RELATIVE_TO_UNION : thm
  ARBITRARY_UNION_OF_RELATIVE_TO : thm
  FINITE_UNION_OF_RELATIVE_TO : thm
  COUNTABLE_UNION_OF_RELATIVE_TO : thm
  ARBITRARY_INTERSECTION_OF_RELATIVE_TO : thm
  FINITE_INTERSECTION_OF_RELATIVE_TO : thm
  COUNTABLE_INTERSECTION_OF_RELATIVE_TO : thm
  FINITE_INTERSECTION_OF_RELATIVE_TO_ALT : thm
  COUNTABLE_INTERSECTION_OF_RELATIVE_TO_ALT : thm
  ARBITRARY_UNION_OF_NONEMPTY_FINITE_INTERSECTION : thm
  deriving Inhabited

@[nospecialize]
def setupRelativeTo [HolBase] (D : MiscDeps) (BLemmas : Lemmas) :
    ExceptT String IO RelativeTo := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, define, parse_as_infix, .. } := D
  let { ARBITRARY, ARBITRARY_UNION_OF_IDEMPOT, ARBITRARY_UNION_OF_UNIONS,
        COMPL_COMPL, EXTENSION, FINITE_IMAGE, FINITE_INSERT,
        FINITE_INTERSECTION_OF_INC, FINITE_INTERSECTION_OF_INTERS, FINITE_SING,
        FORALL_INTERSECTION_OF, FORALL_IN_IMAGE, FORALL_IN_INSERT, FUN_EQ_THM,
        IMAGE_EQ_EMPTY, IMP_CONJ_ALT, IN, INTERSECTION_OF, INTERSECTION_OF_INC,
        INTERS_0, INTERS_IMAGE, INTERS_INSERT, INTER_INTERS, INTER_SUBSET,
        INTER_UNIONS, INTER_UNIV, .. } := D.core1
  let { IN_ELIM_THM, IN_INTER, LEFT_IMP_EXISTS_THM, MONO_EXISTS,
        NOT_INSERT_EMPTY, .. } := D.core2
  let { RIGHT_IMP_EXISTS_THM, SIMPLE_IMAGE, SKOLEM_THM, SUBSET, SUBSET_ANTISYM,
        UNION_OF, UNION_OF_INC, UNION_OF_MONO, .. } := D.core3
  let { COUNTABLE_IMAGE, COUNTABLE_INSERT, COUNTABLE_INTERSECTION_OF_INC,
        COUNTABLE_INTERSECTION_OF_INTERS, .. } := D.lib
  let { EXISTS_DIFF, .. } := BLemmas
  -- @@SCOPE END

  parse_as_infix ("relative_to", (14, "left"))

  let relative_to ← define
   r"(P relative_to s) t <=> ?u. P u /\ s INTER u = t"

  let RELATIVE_TO_UNIV ← prove
   r"!P s. (P relative_to (:A)) s <=> P s"
   (REWRITE_TAC [relative_to, INTER_UNIV] THEN MESON_TAC [])

  let RELATIVE_TO_IMP_SUBSET ← prove
   r"!P s t. (P relative_to s) t ==> t SUBSET s"
   (REWRITE_TAC [relative_to] THEN SET_TAC [])

  let FORALL_RELATIVE_TO ← prove
   r"(!s. (P relative_to u) s ==> Q s) <=>
   (!s. P s ==> Q(u INTER s))"
   (REWRITE_TAC [relative_to] THEN MESON_TAC [])

  let RELATIVE_TO_INC ← prove
   r"!P u s. P s ==> (P relative_to u) (u INTER s)"
   (REWRITE_TAC [relative_to] THEN MESON_TAC [])

  let RELATIVE_TO ← prove
   r"(P relative_to u) = {u INTER s | P s}"
   (REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_INTER] THEN
    REWRITE_TAC [relative_to, IN] THEN SET_TAC [])

  let RELATIVE_TO_RELATIVE_TO ← prove
   r"!P:(A->bool)->bool s t.
        P relative_to s relative_to t = P relative_to (s INTER t)"
   (REWRITE_TAC [RELATIVE_TO] THEN
    REWRITE_TAC [← SET_RULE (← q r"{f x | {g y | P y} x} = {f(g y) | P y}")] THEN
    REWRITE_TAC [← SET_RULE (← q r"(s INTER t) INTER s' = t INTER s INTER s'")])

  let RELATIVE_TO_COMPL ← prove
   r"!P u s:A->bool.
        s SUBSET u
        ==> ((P relative_to u) (u DIFF s) <=>
             ((\c. P(UNIV DIFF c)) relative_to u) s)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [relative_to] THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM EXISTS_DIFF] THEN
    REWRITE_TAC [COMPL_COMPL] THEN
    AP_TERM_TAC THEN ABS_TAC THEN ASM SET_TAC [])

  let RELATIVE_TO_SUBSET ← prove
   r"!P s t:A->bool. s SUBSET t /\ P s ==> (P relative_to t) s"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [relative_to] THEN
    EXISTS_TAC (← q r"s:A->bool") THEN ASM SET_TAC [])

  let RELATIVE_TO_SUBSET_TRANS ← prove
   r"!P u s t:A->bool.
      (P relative_to u) s /\ s SUBSET t /\ t SUBSET u ==> (P relative_to t) s"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    REWRITE_TAC [relative_to] THEN MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC [])

  let RELATIVE_TO_MONO ← prove
   r"!P Q.
     (!s. P s ==> Q s) ==> !u. (P relative_to u) s ==> (Q relative_to u) s"
   (REWRITE_TAC [relative_to] THEN MESON_TAC [])

  let RELATIVE_TO_SUBSET_INC ← prove
   r"!P u s:A->bool.
        s SUBSET u /\ P s ==> (P relative_to u) s"
   (REWRITE_TAC [relative_to] THEN
    MESON_TAC [← SET_RULE (← q r"s SUBSET u ==> u INTER s = s")])

  let RELATIVE_TO_INTER ← prove
   r"!P s. (!c d:A->bool. P c /\ P d ==> P(c INTER d))
         ==> !c d. (P relative_to s) c /\ (P relative_to s) d
                   ==> (P relative_to s) (c INTER d)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC [relative_to] THEN DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_THEN (← q r"c':A->bool") (STRIP_ASSUME_TAC o GSYM))
     (X_CHOOSE_THEN (← q r"d':A->bool") (STRIP_ASSUME_TAC o GSYM))) THEN
    EXISTS_TAC (← q r"c' INTER d':A->bool") THEN
    ASM_SIMP_TAC [] THEN ASM SET_TAC [])

  let RELATIVE_TO_UNION ← prove
   r"!P s. (!c d:A->bool. P c /\ P d ==> P(c UNION d))
         ==> !c d. (P relative_to s) c /\ (P relative_to s) d
                   ==> (P relative_to s) (c UNION d)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC [relative_to] THEN DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_THEN (← q r"c':A->bool") (STRIP_ASSUME_TAC o GSYM))
     (X_CHOOSE_THEN (← q r"d':A->bool") (STRIP_ASSUME_TAC o GSYM))) THEN
    EXISTS_TAC (← q r"c' UNION d':A->bool") THEN
    ASM_SIMP_TAC [] THEN ASM SET_TAC [])

  let ARBITRARY_UNION_OF_RELATIVE_TO ← prove
   r"!P u:A->bool.
        ((ARBITRARY UNION_OF P) relative_to u) =
        (ARBITRARY UNION_OF (P relative_to u))"
   (REWRITE_TAC [FUN_EQ_THM] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [UNION_OF, relative_to] THEN EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_THEN (← q r"t:A->bool")
       (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"f:(A->bool)->bool")
       (STRIP_ASSUME_TAC o GSYM)) THEN
      EXISTS_TAC (← q r"{u INTER c | (c:A->bool) IN f}") THEN
      ASM_REWRITE_TAC [INTER_UNIONS] THEN
      ASM_SIMP_TAC [SIMPLE_IMAGE, ARBITRARY, FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC [],
      DISCH_THEN (X_CHOOSE_THEN (← q r"f:(A->bool)->bool") STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM (MP_TAC o
        GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]) THEN
      REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"g:(A->bool)->(A->bool)") THEN STRIP_TAC THEN
      EXISTS_TAC (← q r"UNIONS (IMAGE (g:(A->bool)->(A->bool)) f)") THEN
      CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
      EXISTS_TAC (← q r"IMAGE (g:(A->bool)->(A->bool)) f") THEN
      ASM_SIMP_TAC [ARBITRARY, FORALL_IN_IMAGE]])

  let FINITE_UNION_OF_RELATIVE_TO ← prove
   r"!P u:A->bool.
        ((FINITE UNION_OF P) relative_to u) =
        (FINITE UNION_OF (P relative_to u))"
   (REWRITE_TAC [FUN_EQ_THM] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [UNION_OF, relative_to] THEN EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_THEN (← q r"t:A->bool")
       (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"f:(A->bool)->bool")
       (STRIP_ASSUME_TAC o GSYM)) THEN
      EXISTS_TAC (← q r"{u INTER c | (c:A->bool) IN f}") THEN
      ASM_REWRITE_TAC [INTER_UNIONS] THEN
      ASM_SIMP_TAC [SIMPLE_IMAGE, FINITE_IMAGE, FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC [],
      DISCH_THEN (X_CHOOSE_THEN (← q r"f:(A->bool)->bool") STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM (MP_TAC o
        GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]) THEN
      REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"g:(A->bool)->(A->bool)") THEN STRIP_TAC THEN
      EXISTS_TAC (← q r"UNIONS (IMAGE (g:(A->bool)->(A->bool)) f)") THEN
      CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
      EXISTS_TAC (← q r"IMAGE (g:(A->bool)->(A->bool)) f") THEN
      ASM_SIMP_TAC [FINITE_IMAGE, FORALL_IN_IMAGE]])

  let COUNTABLE_UNION_OF_RELATIVE_TO ← prove
   r"!P u:A->bool.
        ((COUNTABLE UNION_OF P) relative_to u) =
        (COUNTABLE UNION_OF (P relative_to u))"
   (REWRITE_TAC [FUN_EQ_THM] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [UNION_OF, relative_to] THEN EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_THEN (← q r"t:A->bool")
       (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"f:(A->bool)->bool")
       (STRIP_ASSUME_TAC o GSYM)) THEN
      EXISTS_TAC (← q r"{u INTER c | (c:A->bool) IN f}") THEN
      ASM_REWRITE_TAC [INTER_UNIONS] THEN
      ASM_SIMP_TAC [SIMPLE_IMAGE, COUNTABLE_IMAGE, FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC [],
      DISCH_THEN (X_CHOOSE_THEN (← q r"f:(A->bool)->bool") STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM (MP_TAC o
        GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]) THEN
      REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"g:(A->bool)->(A->bool)") THEN STRIP_TAC THEN
      EXISTS_TAC (← q r"UNIONS (IMAGE (g:(A->bool)->(A->bool)) f)") THEN
      CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
      EXISTS_TAC (← q r"IMAGE (g:(A->bool)->(A->bool)) f") THEN
      ASM_SIMP_TAC [COUNTABLE_IMAGE, FORALL_IN_IMAGE]])

  let ARBITRARY_INTERSECTION_OF_RELATIVE_TO ← prove
   r"!P u:A->bool.
        ((ARBITRARY INTERSECTION_OF P) relative_to u) =
        ((ARBITRARY INTERSECTION_OF (P relative_to u)) relative_to u)"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC id [FUN_EQ_THM] THEN
    X_GEN_TAC (← q r"s:A->bool") THEN REWRITE_TAC [INTERSECTION_OF, relative_to] THEN
    EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_THEN (← q r"t:A->bool")
       (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"f:(A->bool)->bool")
       (STRIP_ASSUME_TAC o GSYM)) THEN
      EXISTS_TAC (← q r"INTERS {u INTER c | (c:A->bool) IN f}") THEN CONJ_TAC THENL
       [EXISTS_TAC (← q r"{u INTER c | (c:A->bool) IN f}") THEN
        ASM_SIMP_TAC [ARBITRARY, SIMPLE_IMAGE, FORALL_IN_IMAGE] THEN
        ASM_MESON_TAC [],
        ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [INTER_INTERS] THEN
        REWRITE_TAC [SIMPLE_IMAGE, IMAGE_EQ_EMPTY, INTERS_IMAGE, FORALL_IN_IMAGE,
                     ← SET_RULE (← q r"u INTER u INTER s = u INTER s")]],
      DISCH_THEN (X_CHOOSE_THEN (← q r"t:A->bool")
       (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"f:(A->bool)->bool") STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM (MP_TAC o
        GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]) THEN
      REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"g:(A->bool)->(A->bool)") THEN STRIP_TAC THEN
      EXISTS_TAC (← q r"INTERS (IMAGE (g:(A->bool)->(A->bool)) f)") THEN
      CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
      EXISTS_TAC (← q r"IMAGE (g:(A->bool)->(A->bool)) f") THEN
      ASM_SIMP_TAC [ARBITRARY, FORALL_IN_IMAGE]])

  let FINITE_INTERSECTION_OF_RELATIVE_TO ← prove
   r"!P u:A->bool.
        ((FINITE INTERSECTION_OF P) relative_to u) =
        ((FINITE INTERSECTION_OF (P relative_to u)) relative_to u)"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC id [FUN_EQ_THM] THEN
    X_GEN_TAC (← q r"s:A->bool") THEN REWRITE_TAC [INTERSECTION_OF, relative_to] THEN
    EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_THEN (← q r"t:A->bool")
       (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"f:(A->bool)->bool")
       (STRIP_ASSUME_TAC o GSYM)) THEN
      EXISTS_TAC (← q r"INTERS {u INTER c | (c:A->bool) IN f}") THEN CONJ_TAC THENL
       [EXISTS_TAC (← q r"{u INTER c | (c:A->bool) IN f}") THEN
        ASM_SIMP_TAC [FINITE_IMAGE, SIMPLE_IMAGE, FORALL_IN_IMAGE] THEN
        ASM_MESON_TAC [],
        ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [INTER_INTERS] THEN
        REWRITE_TAC [SIMPLE_IMAGE, IMAGE_EQ_EMPTY, INTERS_IMAGE, FORALL_IN_IMAGE,
                     ← SET_RULE (← q r"u INTER u INTER s = u INTER s")]],
      DISCH_THEN (X_CHOOSE_THEN (← q r"t:A->bool")
       (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"f:(A->bool)->bool") STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM (MP_TAC o
        GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]) THEN
      REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"g:(A->bool)->(A->bool)") THEN STRIP_TAC THEN
      EXISTS_TAC (← q r"INTERS (IMAGE (g:(A->bool)->(A->bool)) f)") THEN
      CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
      EXISTS_TAC (← q r"IMAGE (g:(A->bool)->(A->bool)) f") THEN
      ASM_SIMP_TAC [FINITE_IMAGE, FORALL_IN_IMAGE]])

  let COUNTABLE_INTERSECTION_OF_RELATIVE_TO ← prove
   r"!P u:A->bool.
        ((COUNTABLE INTERSECTION_OF P) relative_to u) =
        ((COUNTABLE INTERSECTION_OF (P relative_to u)) relative_to u)"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC id [FUN_EQ_THM] THEN
    X_GEN_TAC (← q r"s:A->bool") THEN REWRITE_TAC [INTERSECTION_OF, relative_to] THEN
    EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_THEN (← q r"t:A->bool")
       (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"f:(A->bool)->bool")
       (STRIP_ASSUME_TAC o GSYM)) THEN
      EXISTS_TAC (← q r"INTERS {u INTER c | (c:A->bool) IN f}") THEN CONJ_TAC THENL
       [EXISTS_TAC (← q r"{u INTER c | (c:A->bool) IN f}") THEN
        ASM_SIMP_TAC [COUNTABLE_IMAGE, SIMPLE_IMAGE, FORALL_IN_IMAGE] THEN
        ASM_MESON_TAC [],
        ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [INTER_INTERS] THEN
        REWRITE_TAC [SIMPLE_IMAGE, IMAGE_EQ_EMPTY, INTERS_IMAGE, FORALL_IN_IMAGE,
                     ← SET_RULE (← q r"u INTER u INTER s = u INTER s")]],
      DISCH_THEN (X_CHOOSE_THEN (← q r"t:A->bool")
       (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"f:(A->bool)->bool") STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM (MP_TAC o
        GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]) THEN
      REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"g:(A->bool)->(A->bool)") THEN STRIP_TAC THEN
      EXISTS_TAC (← q r"INTERS (IMAGE (g:(A->bool)->(A->bool)) f)") THEN
      CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
      EXISTS_TAC (← q r"IMAGE (g:(A->bool)->(A->bool)) f") THEN
      ASM_SIMP_TAC [COUNTABLE_IMAGE, FORALL_IN_IMAGE]])

  let FINITE_INTERSECTION_OF_RELATIVE_TO_ALT ← prove
   r"!P u s:A->bool.
        P u ==> ((FINITE INTERSECTION_OF P relative_to u) s <=>
                 (FINITE INTERSECTION_OF P) s /\ s SUBSET u)"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC [RELATIVE_TO_SUBSET_INC] THEN
    SPEC_TAC (← q r"s:A->bool", ← q r"s:A->bool") THEN
    REWRITE_TAC [FORALL_RELATIVE_TO, FORALL_INTERSECTION_OF] THEN
    REWRITE_TAC [INTER_SUBSET, ← GSYM INTERS_INSERT] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_INTERSECTION_OF_INTERS THEN
    ASM_REWRITE_TAC [FINITE_INSERT, FORALL_IN_INSERT] THEN
    ASM_SIMP_TAC [FINITE_INTERSECTION_OF_INC])

  let COUNTABLE_INTERSECTION_OF_RELATIVE_TO_ALT ← prove
   r"!P u s:A->bool.
        P u ==> ((COUNTABLE INTERSECTION_OF P relative_to u) s <=>
                 (COUNTABLE INTERSECTION_OF P) s /\ s SUBSET u)"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC [RELATIVE_TO_SUBSET_INC] THEN
    SPEC_TAC (← q r"s:A->bool", ← q r"s:A->bool") THEN
    REWRITE_TAC [FORALL_RELATIVE_TO, FORALL_INTERSECTION_OF] THEN
    REWRITE_TAC [INTER_SUBSET, ← GSYM INTERS_INSERT] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC COUNTABLE_INTERSECTION_OF_INTERS THEN
    ASM_REWRITE_TAC [COUNTABLE_INSERT, FORALL_IN_INSERT] THEN
    ASM_SIMP_TAC [COUNTABLE_INTERSECTION_OF_INC])

  let ARBITRARY_UNION_OF_NONEMPTY_FINITE_INTERSECTION ← prove
   r"!u:(A->bool)->bool.
        ARBITRARY UNION_OF ((\s. FINITE s /\ ~(s = {})) INTERSECTION_OF u) =
        ARBITRARY UNION_OF (FINITE INTERSECTION_OF u relative_to UNIONS u)"
   (GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC [← REWRITE_RULE [IN] SUBSET] THEN
    CONJ_TAC THEN X_GEN_TAC (← q r"s:A->bool") THENL
     [MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] UNION_OF_MONO) THEN
      REWRITE_TAC [FORALL_INTERSECTION_OF] THEN X_GEN_TAC (← q r"t:(A->bool)->bool") THEN
      STRIP_TAC THEN REWRITE_TAC [INTERSECTION_OF, relative_to] THEN
      EXISTS_TAC (← q r"INTERS t:A->bool") THEN
      CONJ_TAC THENL [ASM_MESON_TAC [], ASM SET_TAC []],
      GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV)
       [← GSYM ARBITRARY_UNION_OF_IDEMPOT] THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] UNION_OF_MONO) THEN
      REWRITE_TAC [FORALL_RELATIVE_TO, FORALL_INTERSECTION_OF] THEN
      X_GEN_TAC (← q r"t:(A->bool)->bool") THEN STRIP_TAC THEN
      ASM_CASES_TAC (← q r"t:(A->bool)->bool = {}") THENL
       [ASM_REWRITE_TAC [INTERS_0, INTER_UNIV] THEN
        MATCH_MP_TAC ARBITRARY_UNION_OF_UNIONS THEN
        X_GEN_TAC (← q r"r:A->bool") THEN DISCH_TAC THEN
        MATCH_MP_TAC UNION_OF_INC THEN
        REWRITE_TAC [ARBITRARY] THEN MATCH_MP_TAC INTERSECTION_OF_INC THEN
        REWRITE_TAC [NOT_INSERT_EMPTY, FINITE_SING] THEN ASM_MESON_TAC [IN],
        MATCH_MP_TAC UNION_OF_INC THEN
        REWRITE_TAC [ARBITRARY, INTERSECTION_OF] THEN
        EXISTS_TAC (← q r"t:(A->bool)->bool") THEN ASM SET_TAC []]])

  return { relative_to, RELATIVE_TO_UNIV, RELATIVE_TO_IMP_SUBSET,
           FORALL_RELATIVE_TO, RELATIVE_TO_INC, RELATIVE_TO,
           RELATIVE_TO_RELATIVE_TO, RELATIVE_TO_COMPL, RELATIVE_TO_SUBSET,
           RELATIVE_TO_SUBSET_TRANS, RELATIVE_TO_MONO, RELATIVE_TO_SUBSET_INC,
           RELATIVE_TO_INTER, RELATIVE_TO_UNION, ARBITRARY_UNION_OF_RELATIVE_TO,
           FINITE_UNION_OF_RELATIVE_TO, COUNTABLE_UNION_OF_RELATIVE_TO,
           ARBITRARY_INTERSECTION_OF_RELATIVE_TO,
           FINITE_INTERSECTION_OF_RELATIVE_TO,
           COUNTABLE_INTERSECTION_OF_RELATIVE_TO,
           FINITE_INTERSECTION_OF_RELATIVE_TO_ALT,
           COUNTABLE_INTERSECTION_OF_RELATIVE_TO_ALT,
           ARBITRARY_UNION_OF_NONEMPTY_FINITE_INTERSECTION }

/- ------------------------------------------------------------------------- -/
/- Reduction theorem used for sigma-sets doesn't really depend on much.      -/
/- (misc.ml 1649-1803)                                                        -/
/- ------------------------------------------------------------------------- -/

structure Reduction where
  GENERAL_REDUCTION_THEOREM : thm
  GENERAL_REDUCTION_THEOREM_2 : thm
  deriving Inhabited

@[nospecialize]
def setupReduction [HolBase] (D : MiscDeps) : ExceptT String IO Reduction := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, MESON, MESON_TAC, SET_RULE, SET_TAC,
        NUM_REDUCE_CONV, .. } := D
  let { AND_FORALL_THM, DE_MORGAN_THM, DISJOINT, DISJOINT_SYM, EMPTY_UNIONS,
        EQ_TRANS, EXTENSION, FINITE_IMAGE, FINITE_INDUCT_STRONG,
        FINITE_NUMSEG_LT, FORALL_AND_THM, FORALL_IN_GSPEC, FORALL_IN_IMAGE,
        FORALL_IN_INSERT, FORALL_PAIR_THM, IMAGE_CLAUSES, IMP_CONJ,
        INTER_UNIONS, .. } := D.core1
  let { IN_DIFF, IN_ELIM_PAIR_THM, IN_ELIM_THM, IN_IMAGE, IN_INSERT, IN_INTER,
        IN_UNIV, LEFT_EXISTS_AND_THM, LEFT_IMP_EXISTS_THM, MONO_EXISTS,
        NOT_IN_EMPTY, PAIRWISE_INSERT, PAIR_EQ, .. } := D.core2
  let { SIMPLE_IMAGE, SKOLEM_THM, SUBSET_EMPTY, UNIONS_0, UNIONS_GSPEC,
        UNIONS_INSERT, UNION_OF, WLOG_LT, num_WOP, o_THM, pairwise, .. } := D.core3
  let { CARD_SQUARE_NUM, COUNTABLE_AS_IMAGE, COUNTABLE_PRODUCT_DEPENDENT,
        COUNTABLE_SUBSET, COUNTABLE_SUBSET_NUM, COUNTABLE_UNION_OF_INC,
        EQ_C_BIJECTIONS, mul_c, .. } := D.lib
  -- @@SCOPE END

  let GENERAL_REDUCTION_THEOREM ← prove
   r"!P. P {} /\
       (!s t. P s /\ P t ==> P(s UNION t)) /\
       (!s t. P s /\ P t ==> P(s DIFF t))
       ==> !s:num->A->bool.
              (!n. (COUNTABLE UNION_OF P) (s n))
              ==> ?t. (!n. (COUNTABLE UNION_OF P) (t n)) /\
                      (!n. t n SUBSET s n) /\
                      pairwise (\m n. DISJOINT (t m) (t n)) (:num) /\
                      UNIONS {t n | n IN (:num)} = UNIONS {s n | n IN (:num)}"
   (REWRITE_TAC [UNION_OF, o_THM] THEN REPEAT STRIP_TAC THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"!k:(A->bool)->bool. FINITE k /\ (!i. i IN k ==> P i) ==> P(UNIONS k)")
    ASSUME_TAC THENL
     [REWRITE_TAC [IMP_CONJ] THEN
      MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
      ASM_SIMP_TAC [UNIONS_0, UNIONS_INSERT, FORALL_IN_INSERT],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"?c:num->num->A->bool.
        (!n m. P (c n m)) /\
        (!n. UNIONS {c n m | m IN (:num)} = s n)")
    MP_TAC THENL
     [REWRITE_TAC [AND_FORALL_THM, ← GSYM SKOLEM_THM] THEN
      X_GEN_TAC (← q r"n:num") THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q r"n:num")) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"u:(A->bool)->bool") MP_TAC) THEN
      ASM_CASES_TAC (← q r"u:(A->bool)->bool = {}") THENL
       [ASM_REWRITE_TAC [UNIONS_0] THEN
        DISCH_THEN (fun th => tactic_of do
          pure (SUBST1_TAC (← SYM (← ExceptT.mk (pure (last (CONJUNCTS th))))))) THEN
        EXISTS_TAC (← q r"(\n. {}):num->A->bool") THEN
        ASM_REWRITE_TAC [UNIONS_GSPEC] THEN SET_TAC [],
        STRIP_TAC] THEN
      MP_TAC (← ISPEC (← q r"u:(A->bool)->bool") COUNTABLE_AS_IMAGE) THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC [],
      FIRST_X_ASSUM (fun th => tactic_of do
        let _ ← GEN_REWRITE_RULE id [SKOLEM_THM] th
        pure ALL_TAC)] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->num->A->bool") STRIP_ASSUME_TAC) THEN
    MP_TAC CARD_SQUARE_NUM THEN
    REWRITE_TAC [EQ_C_BIJECTIONS, LEFT_IMP_EXISTS_THM, FORALL_PAIR_THM] THEN
    REWRITE_TAC [mul_c, IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"p:num#num->num", ← q r"q:num->num#num"] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [IN_UNIV] THEN
    REWRITE_TAC [FORALL_AND_THM] THEN STRIP_TAC THEN
    ABBREV_TAC (← q r"d:num->num->A->bool =
        \m n. c m n DIFF UNIONS {c i j | (p:num#num->num)(i,j) < p(m,n)}") THEN
    EXISTS_TAC (← q r"\n. UNIONS { d i j | i,j |
                           (d:num->num->A->bool) i j SUBSET s n /\
                           !m:num. m < n ==> ~(d i j SUBSET s m)}") THEN
    REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC (← q r"n:num") THEN
      EXISTS_TAC (← q r"{ d i j | i,j |
                  (d:num->num->A->bool) i j SUBSET s n /\
                  !m:num. m < n ==> ~(d i j SUBSET s m)}") THEN
      REWRITE_TAC [] THEN CONJ_TAC THENL
       [MATCH_MP_TAC COUNTABLE_SUBSET THEN EXISTS_TAC (← q
         r"{(d:num->num->A->bool) i j | i IN (:num) /\ j IN (:num)}") THEN
        SIMP_TAC [COUNTABLE_PRODUCT_DEPENDENT, COUNTABLE_SUBSET_NUM] THEN
        SET_TAC [],

        REWRITE_TAC [FORALL_IN_GSPEC] THEN
        MAP_EVERY X_GEN_TAC [← q r"i:num", ← q r"j:num"] THEN STRIP_TAC THEN
        EXPAND_TAC "d" THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [FORALL_IN_GSPEC] THEN
        SUBGOAL_THEN
         (← q r"{(c:num->num->A->bool) k l | (p(k,l):num) < p(i,j)} =
        IMAGE (\r. c (FST(q r)) (SND(q r))) {r | r < p(i,j)}")
         (fun th => SIMP_TAC [th, FINITE_IMAGE, FINITE_NUMSEG_LT]) THEN
        GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"v:A->bool") THEN
        REWRITE_TAC [IN_ELIM_THM, IN_IMAGE] THEN EQ_TAC THEN
        SIMP_TAC [LEFT_IMP_EXISTS_THM] THENL
         [MAP_EVERY X_GEN_TAC [← q r"a:num", ← q r"b:num"] THEN STRIP_TAC THEN
          EXISTS_TAC (← q r"(p:num#num->num)(a,b)") THEN ASM_REWRITE_TAC [],
          X_GEN_TAC (← q r"c:num") THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC
           [← q r"FST((q:num->num#num) c)", ← q r"SND((q:num->num#num) c)"] THEN
          ASM_REWRITE_TAC []]],
      ASM SET_TAC [],
      REWRITE_TAC [pairwise] THEN MATCH_MP_TAC WLOG_LT THEN
      REWRITE_TAC [] THEN CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [← q r"a:num", ← q r"b:num"] THEN REWRITE_TAC [IN_UNIV] THEN
        BINOP_TAC THENL [MESON_TAC [], MATCH_ACCEPT_TAC DISJOINT_SYM],
        REWRITE_TAC [IN_UNIV, DISJOINT, INTER_UNIONS]] THEN
      REWRITE_TAC [EMPTY_UNIONS, FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [← q r"i:num", ← q r"j:num"] THEN REPEAT DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [← q r"a:num", ← q r"b:num"] THEN STRIP_TAC THEN
      MAP_EVERY X_GEN_TAC [← q r"m:num", ← q r"n:num"] THEN STRIP_TAC THEN
      EXPAND_TAC "d" THEN REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"(p:num#num->num)(a,b) < p(m,n) \/ p(m,n) < p(a,b)")
      MP_TAC THENL
       [REWRITE_TAC [← ARITH_RULE (← q r"m < n \/ n < m <=> ~(m:num = n)")] THEN
        DISCH_THEN (MP_TAC o AP_TERM (← q r"q:num->num#num")) THEN
        ASM_REWRITE_TAC [PAIR_EQ] THEN ASM SET_TAC [],
        REWRITE_TAC [EXTENSION, IN_DIFF, IN_INTER, UNIONS_GSPEC] THEN
        SET_TAC []],
       GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"x:A") THEN
       REWRITE_TAC [UNIONS_GSPEC, IN_UNIV, IN_ELIM_THM] THEN
       ONCE_REWRITE_TAC [← MESON [] (← q r"(?n i j. P n i j) <=> (?i j n. P n i j)")] THEN
       REWRITE_TAC [LEFT_EXISTS_AND_THM, ← GSYM num_WOP] THEN
       TRANS_TAC EQ_TRANS (← q r"?i j. x IN (d:num->num->A->bool) i j") THEN
       CONJ_TAC THENL
        [REPEAT (AP_TERM_TAC THEN ABS_TAC) THEN
         MATCH_MP_TAC (← TAUT (← q r"p ==> (p /\ q <=> q)")) THEN
         EXPAND_TAC "d" THEN REWRITE_TAC [] THEN ASM SET_TAC [],
         ALL_TAC] THEN
       FIRST_ASSUM (fun t => tactic_of do
         pure (GEN_REWRITE_TAC (RAND_CONV o BINDER_CONV o RAND_CONV) [← GSYM t])) THEN
       REWRITE_TAC [UNIONS_GSPEC, IN_ELIM_THM, IN_UNIV] THEN MATCH_MP_TAC (← MESON [] (← q
        r"!p:num#num->num.
           (P <=> ?n i j. p(i,j) = n /\ Q i j) ==> (P <=> ?i j. Q i j)")) THEN
       EXISTS_TAC (← q r"p:num#num->num") THEN
       GEN_REWRITE_TAC RAND_CONV [num_WOP] THEN
       EXPAND_TAC "d" THEN REWRITE_TAC [IN_DIFF, UNIONS_GSPEC, IN_ELIM_THM] THEN
       MESON_TAC []])

  let GENERAL_REDUCTION_THEOREM_2 ← prove
   r"!P. P {} /\
       (!s t:A->bool. P s /\ P t ==> P(s UNION t)) /\
       (!s t. P s /\ P t ==> P(s DIFF t))
       ==> !s t. (COUNTABLE UNION_OF P) s /\ (COUNTABLE UNION_OF P) t
                 ==> ?s' t'. (COUNTABLE UNION_OF P) s' /\
                             (COUNTABLE UNION_OF P) t' /\
                             s' SUBSET s /\ t' SUBSET t /\ DISJOINT s' t' /\
                             s' UNION t' = s UNION t"
   (GEN_TAC THEN DISCH_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (MP_TAC (← ISPEC (← q r"\n. if n = 0 then s:A->bool else if n = 1 then t else {}")
        (← MATCH_MP GENERAL_REDUCTION_THEOREM th)))) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [GEN_TAC THEN REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
      ASM_SIMP_TAC [COUNTABLE_UNION_OF_INC],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"v:num->A->bool") MP_TAC) THEN
    REWRITE_TAC [IMP_CONJ] THEN DISCH_THEN (STRIP_ASSUME_TAC o MATCH_MP
     (← MESON [] (← q r"(!n. P n) ==> P 0 /\ P 1"))) THEN
    ONCE_REWRITE_TAC [← MESON [] (← q
     r"(!n. P n) <=> P 0 /\ P 1 /\ (!n. ~(n = 0) /\ ~(n = 1) ==> P n)")] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC [SUBSET_EMPTY] THEN
    STRIP_TAC THEN
    ONCE_REWRITE_TAC [← SET_RULE (← q
     r"(:num) = 0 INSERT 1 INSERT ((:num) DIFF {0,1})")] THEN
    SIMP_TAC [SIMPLE_IMAGE, IMAGE_CLAUSES, UNIONS_INSERT, PAIRWISE_INSERT] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (MP_TAC (← SPEC (← q r"1") (← CONJUNCT1 th)))) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [IN_INSERT] THEN STRIP_TAC THEN
    DISCH_THEN (MP_TAC o MATCH_MP (← SET_RULE (← q
     r"s UNION t UNION u = s' UNION t' UNION u'
    ==> u = {} /\ u' = {} ==> s UNION t = s' UNION t'"))) THEN
    REWRITE_TAC [EMPTY_UNIONS, FORALL_IN_IMAGE, IN_UNIV, IN_DIFF] THEN
    ASM_SIMP_TAC [IN_INSERT, NOT_IN_EMPTY, DE_MORGAN_THM] THEN
    ASM_MESON_TAC [])

  return { GENERAL_REDUCTION_THEOREM, GENERAL_REDUCTION_THEOREM_2 }

/- ------------------------------------------------------------------------- -/
/- A somewhat general formulation of "back and forth" arguments.             -/
/- (misc.ml 1805-2013)                                                        -/
/- ------------------------------------------------------------------------- -/

structure BackAndForth where
  BACK_AND_FORTH_ALT : thm
  BACK_AND_FORTH : thm
  BACK_AND_FORTH_2 : thm
  deriving Inhabited

@[nospecialize]
def setupBackAndForth [HolBase] (D : MiscDeps) : ExceptT String IO BackAndForth := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, SET_TAC, .. } := D
  let { DEPENDENT_CHOICE, EMPTY_SUBSET, EXISTS_PAIR_THM, EXTENSION,
        FINITE_IMAGE, FINITE_INSERT, FINITE_RULES, FORALL_IN_GSPEC,
        FORALL_IN_IMAGE, FORALL_IN_IMAGE_2, FORALL_PAIR_THM, IMAGE_CLAUSES,
        IMAGE_EQ, IMAGE_o, IMP_CONJ, INJECTIVE_ON_ALT,
        INJECTIVE_ON_LEFT_INVERSE, INSERT_SUBSET, IN_CROSS, .. } := D.core1
  let { IN_DIFF, IN_ELIM_THM, IN_IMAGE, IN_INSERT, IN_UNIV,
        LEFT_IMP_EXISTS_THM, MONO_AND, MONO_EXISTS, MONO_FORALL,
        PAIRWISE_CHAIN_UNIONS, PAIRWISE_EMPTY, PAIRWISE_INSERT, PAIR_EQ, .. } := D.core2
  let { RIGHT_EXISTS_AND_THM, RIGHT_FORALL_IMP_THM, SUBSET, SUBSET_REFL,
        TRANSITIVE_STEPWISE_LE, UNIONS_GSPEC, UNIONS_SUBSET, UNWIND_THM1,
        WLOG_LE, o_THM, pairwise, .. } := D.core3
  let { COUNTABLE_AS_IMAGE_SUBSET, .. } := D.lib
  -- @@SCOPE END

  let BACK_AND_FORTH_ALT ← prove
   r"!P s:A->bool t:B->bool.
    COUNTABLE s /\ COUNTABLE t /\
    (!R. FINITE R /\ R SUBSET s CROSS t /\ pairwise P R
         ==> (!x. x IN s ==> ?y. y IN t /\ pairwise P ((x,y) INSERT R)) /\
             (!y. y IN t ==> ?x. x IN s /\ pairwise P ((x,y) INSERT R)))
    ==> ?R. R SUBSET s CROSS t /\ pairwise P R /\
            (!x. x IN s ==> ?y. y IN t /\ (x,y) IN R) /\
            (!y. y IN t ==> ?x. x IN s /\ (x,y) IN R)"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"?x:num->A. ?y:num->B. s SUBSET IMAGE x (:num) /\ t SUBSET IMAGE y (:num)")
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC [COUNTABLE_AS_IMAGE_SUBSET], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"?R:num->A#B->bool.
        (!n. FINITE(R n) /\ (R n) SUBSET s CROSS t /\ pairwise P (R n) /\
             (x n IN s ==> x n IN IMAGE FST(R n)) /\
             (y n IN t ==> y n IN IMAGE SND(R n))) /\
        (!n. R n  SUBSET R(SUC n))")
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC DEPENDENT_CHOICE THEN MATCH_MP_TAC (← MESON [] (← q
       r"((!n x. P x /\ Q x /\ R x ==> ?y. B n x y) ==> X) /\
      (!n x. P x /\ Q x /\ R x ==> ?y. B n x y)
      ==> X /\
          (!n x. P x /\ Q x /\ R x /\ S n x ==> ?y. B (SUC n) x y)")) THEN
      CONJ_TAC THENL
       [DISCH_THEN (MP_TAC o SPECL [← q r"0", ← q r"{}:A#B->bool"]) THEN
        REWRITE_TAC [EMPTY_SUBSET, PAIRWISE_EMPTY, FINITE_RULES],
        MAP_EVERY X_GEN_TAC [← q r"n:num", ← q r"R:A#B->bool"] THEN STRIP_TAC] THEN
      ASM_CASES_TAC (← q r"(x:num->A) n IN s") THEN ASM_REWRITE_TAC [] THENL
       [FIRST_ASSUM (MP_TAC o SPEC (← q r"R:A#B->bool")) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
        DISCH_THEN (fun th => tactic_of do
          pure (MP_TAC (← SPEC (← q r"(x:num->A) n") (← CONJUNCT1 th)))) THEN
        ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
        X_GEN_TAC (← q r"z:B") THEN STRIP_TAC THEN
        ASM_CASES_TAC (← q r"(y:num->B) n IN t") THEN ASM_REWRITE_TAC [] THENL
         [FIRST_X_ASSUM (MP_TAC o SPEC (← q r"((x:num->A) n,z:B) INSERT R")) THEN
          ASM_REWRITE_TAC [FINITE_INSERT, INSERT_SUBSET] THEN
          ASM_REWRITE_TAC [IN_CROSS] THEN
          DISCH_THEN (fun th => tactic_of do
            pure (MP_TAC (← SPEC (← q r"(y:num->B) n") (← CONJUNCT2 th)))) THEN
          ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
          X_GEN_TAC (← q r"w:A") THEN STRIP_TAC THEN
          EXISTS_TAC (← q r"(w,y(n:num)) INSERT (x n,z) INSERT (R:A#B->bool)") THEN
          ASM_REWRITE_TAC [FINITE_INSERT, INSERT_SUBSET, IN_CROSS] THEN
          REWRITE_TAC [IMAGE_CLAUSES, IN_INSERT] THEN SET_TAC [],
          EXISTS_TAC (← q r"(x(n:num),z) INSERT (R:A#B->bool)") THEN
          ASM_REWRITE_TAC [FINITE_INSERT, INSERT_SUBSET, IN_CROSS] THEN
          REWRITE_TAC [IMAGE_CLAUSES, IN_INSERT] THEN SET_TAC []],
        ASM_CASES_TAC (← q r"(y:num->B) n IN t") THEN ASM_REWRITE_TAC [] THENL
         [ALL_TAC, ASM_MESON_TAC [SUBSET_REFL]] THEN
        FIRST_ASSUM (MP_TAC o SPEC (← q r"R:A#B->bool")) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
        DISCH_THEN (fun th => tactic_of do
          pure (MP_TAC (← SPEC (← q r"(y:num->B) n") (← CONJUNCT2 th)))) THEN
        ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
        X_GEN_TAC (← q r"w:A") THEN STRIP_TAC THEN
        EXISTS_TAC (← q r"(w,y(n:num)) INSERT (R:A#B->bool)") THEN
        ASM_REWRITE_TAC [FINITE_INSERT, INSERT_SUBSET, IN_CROSS] THEN
        REWRITE_TAC [IMAGE_CLAUSES, IN_INSERT] THEN SET_TAC []],
      EXISTS_TAC (← q r"UNIONS {R n | n IN (:num)} :A#B->bool") THEN
      ASM_REWRITE_TAC [UNIONS_SUBSET, FORALL_IN_GSPEC] THEN CONJ_TAC THENL
       [MATCH_MP_TAC PAIRWISE_CHAIN_UNIONS THEN
        ASM_REWRITE_TAC [FORALL_IN_GSPEC, IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
        REWRITE_TAC [IN_UNIV] THEN MATCH_MP_TAC WLOG_LE THEN
        CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN
        MATCH_MP_TAC (← MESON [] (← q
         r"(!x y. P x y ==> Q x y) ==> (!x y. P x y ==> Q x y \/ R x y)")) THEN
        MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN ASM_REWRITE_TAC [] THEN
        SET_TAC [],
        REWRITE_TAC [UNIONS_GSPEC, IN_UNIV, IN_ELIM_THM] THEN
        REPEAT (POP_ASSUM MP_TAC) THEN
        REWRITE_TAC [IN_IMAGE, EXISTS_PAIR_THM, UNWIND_THM1, RIGHT_EXISTS_AND_THM,
                     SUBSET, FORALL_PAIR_THM, IN_CROSS] THEN
        SET_TAC []]])

  let BACK_AND_FORTH ← prove
   r"!R s:A->bool t:B->bool.
        (!x y. x IN s /\ y IN t ==> R x x y y) /\
        (!x y x' y'. x IN s /\ x' IN s /\ y IN t /\ y' IN t /\
                     ~(x = x') /\ ~(y = y') /\ R x x' y y'
                     ==> R x' x y' y) /\
        COUNTABLE s /\ COUNTABLE t /\
        (!f s' t'. FINITE s' /\ s' SUBSET s /\ FINITE t' /\ t' SUBSET t /\
                   IMAGE f s' = t' /\
                   (!x y. x IN s' /\ y IN s' ==> (f x = f y <=> x = y)) /\
                   (!x y. x IN s' /\ y IN s' ==> R x y (f x) (f y))
                   ==> (!x. x IN s DIFF s'
                            ==> ?y. y IN t DIFF t' /\
                                    !z. z IN s' ==> R x z y (f z)) /\
                       (!y. y IN t DIFF t'
                            ==> ?x. x IN s DIFF s' /\
                                    !z. z IN s' ==> R x z y (f z)))
    ==> ?f. IMAGE f s = t /\
            (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
            (!x y. x IN s /\ y IN s ==> R x y (f x) (f y))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL
     [← q r"\(x:A,y:B) (x',y').
        (x = x' <=> y = y') /\ R x x' y y'",
      ← q r"s:A->bool", ← q r"t:B->bool"] BACK_AND_FORTH_ALT) THEN
    ASM_SIMP_TAC [PAIRWISE_INSERT, FORALL_PAIR_THM, PAIR_EQ] THEN ANTS_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [pairwise, FORALL_PAIR_THM, PAIR_EQ, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"r:A#B->bool") THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [SUBSET]) THEN
      REWRITE_TAC [FORALL_PAIR_THM, IN_CROSS] THEN STRIP_TAC THEN
      ABBREV_TAC (← q r"f:A->B = \x. @y. (x,y) IN r") THEN EXISTS_TAC (← q r"f:A->B") THEN
      SUBGOAL_THEN (← q r"!x:A y:B. x IN s ==> (f x = y <=> (x,y) IN r)")
      ASSUME_TAC THENL
       [EXPAND_TAC "f" THEN REWRITE_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_IMAGE] THEN ASM_MESON_TAC [], ALL_TAC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"y:A"] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o
        SPECL [← q r"x:A", ← q r"(f:A->B) x", ← q r"y:A", ← q r"(f:A->B) y"]) THEN
      ASM_CASES_TAC (← q r"x:A = y") THEN ASM_MESON_TAC []] THEN
    X_GEN_TAC (← q r"r:A#B->bool") THEN REWRITE_TAC [SUBSET, pairwise] THEN
    REWRITE_TAC [FORALL_PAIR_THM, PAIR_EQ, LEFT_IMP_EXISTS_THM, IN_CROSS] THEN
    STRIP_TAC THEN
    MAP_EVERY ABBREV_TAC
     [← q r"s' = IMAGE FST (r:A#B->bool)",
      ← q r"t' = IMAGE SND (r:A#B->bool)",
      ← q r"f:A->B = \x. @y. (x,y) IN r"] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL
     [← q r"f:A->B", ← q r"s':A->bool", ← q r"t':B->bool"]) THEN
    SUBGOAL_THEN
     (← q r"!x:A y:B. (x,y) IN r <=> x IN s' /\ y IN t' /\ f x = y")
    ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["f", "s'", "t'"] THEN
      REWRITE_TAC [IN_IMAGE, EXISTS_PAIR_THM] THEN ASM_MESON_TAC [],
      ASM_REWRITE_TAC []] THEN
    SUBGOAL_THEN
     (← q r"(s':A->bool) SUBSET s /\ (t':B->bool) SUBSET t")
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["s'", "t'"] THEN
      REWRITE_TAC [SUBSET, FORALL_PAIR_THM, FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"IMAGE (f:A->B) s' = t'") ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["s'", "t'"] THEN REWRITE_TAC [← GSYM IMAGE_o] THEN
      MATCH_MP_TAC IMAGE_EQ THEN
      REWRITE_TAC [FORALL_PAIR_THM, o_THM] THEN ASM_MESON_TAC [],
      ASM_REWRITE_TAC []] THEN
    ANTS_TAC THENL
     [REPLICATE_TAC 2
        (CONJ_TAC THENL [ASM_MESON_TAC [FINITE_IMAGE], ALL_TAC]) THEN
      CONJ_TAC THEN MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"y:A"] THEN
      ASM_CASES_TAC (← q r"x:A = y") THEN ASM_REWRITE_TAC [] THEN ASM SET_TAC [],
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN MATCH_MP_TAC MONO_FORALL THENL
     [X_GEN_TAC (← q r"x:A") THEN
      ASM_CASES_TAC (← q r"(x:A) IN s") THEN ASM_REWRITE_TAC [IN_DIFF] THEN
      ASM_CASES_TAC (← q r"(x:A) IN s'") THEN ASM_REWRITE_TAC [] THENL
       [EXISTS_TAC (← q r"(f:A->B) x") THEN ASM SET_TAC [], ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC [],
      X_GEN_TAC (← q r"y:B") THEN
      ASM_CASES_TAC (← q r"(y:B) IN t") THEN ASM_REWRITE_TAC [IN_DIFF] THEN
      ASM_CASES_TAC (← q r"(y:B) IN t'") THEN ASM_REWRITE_TAC [] THENL
       [SUBGOAL_THEN (← q r"?x:A. x IN s' /\ (f:A->B) x = y") STRIP_ASSUME_TAC THENL
         [ASM SET_TAC [], EXISTS_TAC (← q r"x:A") THEN ASM SET_TAC []],
        MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC []]])

  let BACK_AND_FORTH_2 ← prove
   r"!R s:A->bool t:B->bool.
        (!x y. x IN s /\ y IN t ==> R x x y y) /\
        (!x y x' y'. x IN s /\ x' IN s /\ y IN t /\ y' IN t /\
                     ~(x = x') /\ ~(y = y') /\ R x x' y y'
                     ==> R x' x y' y) /\
        COUNTABLE s /\ COUNTABLE t /\
        (!f s' t' x. FINITE s' /\ s' SUBSET s /\ FINITE t' /\ t' SUBSET t /\
                     IMAGE f s' = t' /\
                     (!x y. x IN s' /\ y IN s' ==> (f x = f y <=> x = y)) /\
                     (!x y. x IN s' /\ y IN s' ==> R x y (f x) (f y)) /\
                     x IN s DIFF s'
                     ==> ?y. y IN t DIFF t' /\
                             !z. z IN s' ==> R x z y (f z)) /\
         (!f t' s' x. FINITE t' /\ t' SUBSET t /\ FINITE s' /\ s' SUBSET s /\
                     IMAGE f t' = s' /\
                     (!x y. x IN t' /\ y IN t' ==> (f x = f y <=> x = y)) /\
                     (!x y. x IN t' /\ y IN t' ==> R (f x) (f y) x y) /\
                     x IN t DIFF t'
                     ==> ?y. y IN s DIFF s' /\
                             !z. z IN t' ==> R y (f z) x z)
    ==> ?f. IMAGE f s = t /\
            (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
            (!x y. x IN s /\ y IN s ==> R x y (f x) (f y))"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC BACK_AND_FORTH THEN
    ASM_REWRITE_TAC [] THEN
    MAP_EVERY X_GEN_TAC [← q r"f:A->B", ← q r"s':A->bool", ← q r"t':B->bool"] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [],
      FIRST_X_ASSUM (fun th => tactic_of do
        let _ ← SPEC (← q r"f:A->B") th
        pure ALL_TAC)] THEN
    FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE id [← GSYM INJECTIVE_ON_ALT]) THEN
    GEN_REWRITE_TAC LAND_CONV [INJECTIVE_ON_LEFT_INVERSE] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"g:B->A")) THEN
    X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL
     [← q r"g:B->A", ← q r"t':B->bool", ← q r"s':A->bool", ← q r"y:B"]) THEN
    ASM_REWRITE_TAC [] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC], ALL_TAC] THEN
    EXPAND_TAC "t'" THEN REWRITE_TAC [FORALL_IN_IMAGE, FORALL_IN_IMAGE_2] THEN
    ASM_SIMP_TAC [])

  return { BACK_AND_FORTH_ALT, BACK_AND_FORTH, BACK_AND_FORTH_2 }

/- ------------------------------------------------------------------------- -/
/- Definition by recursion on dyadic rationals in [0,1].  (misc.ml 2015-2128) -/
/- ------------------------------------------------------------------------- -/

structure Dyadic where
  RECURSION_ON_DYADIC_FRACTIONS : thm
  deriving Inhabited

@[nospecialize]
def setupDyadic [HolBase] (D : MiscDeps) : ExceptT String IO Dyadic := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON, MESON_TAC,
        REAL_ARITH, REAL_FIELD, NUM_REDUCE_CONV, SELECT_CONV, .. } := D
  let { ADD1, ADD_CLAUSES, ADD_SUB, ADD_SUB2, ARITH_EQ, ARITH_EVEN, EQ_SYM_EQ,
        EVEN_ADD, EVEN_EXISTS, EVEN_MULT, EVEN_OR_ODD, EXP, EXP_ADD,
        FORALL_IN_GSPEC, FORALL_PAIR_THM, FUNCTION_FACTORS_LEFT, FUN_EQ_THM,
        IMP_CONJ, IMP_CONJ_ALT, .. } := D.core1
  let { LEFT_IMP_EXISTS_THM, LE_EXISTS, LE_MULT_LCANCEL, MONO_EXISTS,
        MULT_ASSOC, MULT_CLAUSES, NOT_LT, ODD_EXISTS, REAL_DIV_POW2,
        REAL_LT_DIV2_EQ, REAL_LT_POW2, .. } := D.core2
  let { REAL_OF_NUM_EQ, REAL_OF_NUM_LE, REAL_OF_NUM_LT, REAL_OF_NUM_MUL,
        REAL_OF_NUM_POW, REAL_POW_EQ_0, RIGHT_FORALL_IMP_THM, WLOG_LE,
        num_INDUCTION, num_RECURSION, o_THM, .. } := D.core3
  -- @@SCOPE END

  let gsym_not_lt ← GSYM NOT_LT
  let RECURSION_ON_DYADIC_FRACTIONS ← prove
   r"!R a b:A.
        (!x y z. R x y /\ R y z ==> R x z) /\
        R a b /\ (!x y. R x y ==> ?z. R x z /\ R z y)
        ==> ?f. f(&0) = a /\ f(&1) = b /\
                !x y. x IN {&k / &2 pow n | k <= 2 EXP n} /\
                      y IN {&k / &2 pow n | k <= 2 EXP n} /\
                      x < y
                      ==> R (f x) (f y)"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"?f. (f 0 = \k. if k = 0 then a else b) /\
        (!n. f(SUC n) = \k.
                if EVEN k then f n (k DIV 2)
                else @z:A. R (f n ((k - 1) DIV 2)) z /\
                           R z (f n ((k + 1) DIV 2)))")
    MP_TAC THENL [REWRITE_TAC [num_RECURSION], ALL_TAC] THEN
    REWRITE_TAC [FUN_EQ_THM, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"g:num->num->A") THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"?f. !k n. f(&k / &2 pow n):A = g n k") MP_TAC THENL
     [ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MP_TAC (← ISPECL
       [← q r"\(k,n). (g:num->num->A) n k", ← q r"\(k,n). &k / &2 pow n"]
       FUNCTION_FACTORS_LEFT) THEN
      REWRITE_TAC [FORALL_PAIR_THM, FUN_EQ_THM, o_THM] THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN ONCE_REWRITE_TAC [← MESON [] (← q
        r"(!a b c d. P a b c d) <=> (!b d a c. P a b c d)")] THEN
      MATCH_MP_TAC WLOG_LE THEN REPEAT CONJ_TAC THENL [MESON_TAC [], ALL_TAC] THEN
      SIMP_TAC [← REAL_FIELD (← q r"~(y = &0) /\ ~(y' = &0)
                         ==> (x / y = x' / y' <=> y' / y * x = x')"),
         REAL_POW_EQ_0, REAL_OF_NUM_EQ, REAL_DIV_POW2, ARITH_EQ] THEN
      SIMP_TAC [LE_EXISTS, LEFT_IMP_EXISTS_THM] THEN
      SIMP_TAC [ADD_SUB2, REAL_OF_NUM_MUL, REAL_OF_NUM_EQ, REAL_OF_NUM_POW] THEN
      REWRITE_TAC [← MESON [] (← q
       r"(!n n' d. n' = f d n ==> !m m'. g d m = m' ==> P m m' n d) <=>
      (!d m n. P m (g d m) n d)")] THEN
      ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
      INDUCT_TAC THEN SIMP_TAC [EXP, MULT_CLAUSES, ADD_CLAUSES] THEN
      ASM_REWRITE_TAC [EVEN_MULT, ARITH_EVEN, ← GSYM MULT_ASSOC] THEN
      ASM_REWRITE_TAC [← ARITH_RULE (← q r"(2 * n) DIV 2 = n")],
      MATCH_MP_TAC MONO_EXISTS] THEN
    X_GEN_TAC (← q r"f:real->A") THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [SUBST1_TAC (← REAL_ARITH (← q r"&0 = &0 / &2 pow 0")) THEN
      ASM_REWRITE_TAC [],
      SUBST1_TAC (← REAL_ARITH (← q r"&1 = &1 / &2 pow 0")) THEN
      ASM_REWRITE_TAC [] THEN CONV_TAC NUM_REDUCE_CONV,
      REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [← q r"k1:num", ← q r"n1:num"] THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [← q r"k2:num", ← q r"n2:num"] THEN DISCH_TAC THEN
      CONJUNCTS_THEN SUBST1_TAC (← REAL_FIELD (← q
       r"&k1 / &2 pow n1 = (&2 pow n2 * &k1) / &2 pow (n1 + n2) /\
      &k2 / &2 pow n2 = (&2 pow n1 * &k2) / &2 pow (n1 + n2)")) THEN
      SIMP_TAC [REAL_LT_DIV2_EQ, REAL_LT_POW2,
          ← MESON [REAL_OF_NUM_MUL, REAL_OF_NUM_POW]
           (← q r"&2 pow n * &k = &(2 EXP n * k)")] THEN
      SUBGOAL_THEN (← q r"&(2 EXP n1 * k2) <= &2 pow (n1 + n2)") MP_TAC THENL
       [REWRITE_TAC [REAL_OF_NUM_POW, REAL_OF_NUM_LE, EXP_ADD] THEN
        ASM_REWRITE_TAC [LE_MULT_LCANCEL],
        SPEC_TAC (← q r"2 EXP n1 * k2", ← q r"j2:num") THEN
        SPEC_TAC (← q r"2 EXP n2 * k1", ← q r"j1:num") THEN
        SPEC_TAC (← q r"n1 + n2:num", ← q r"n:num")] THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [REAL_OF_NUM_POW, ← GSYM IMP_CONJ_ALT] THEN
      REWRITE_TAC [REAL_OF_NUM_LT, REAL_OF_NUM_LE] THEN
      REPEAT (FIRST_X_ASSUM (fun th => tactic_of do
        let _ ← GEN_REWRITE_RULE id [gsym_not_lt] th
        pure ALL_TAC))] THEN
    MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
     [ASM_SIMP_TAC [← ARITH_RULE (← q r"j1 < j2 /\ j2 <= 2 EXP 0 <=> j1 = 0 /\ j2 = 1"),
                    ARITH_EQ],
      X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN X_GEN_TAC (← q r"j:num")] THEN
    X_GEN_TAC (← q r"k:num") THEN REWRITE_TAC [EXP] THEN STRIP_TAC THEN
    DISJ_CASES_THEN MP_TAC (← SPEC (← q r"j:num") EVEN_OR_ODD) THEN
    DISJ_CASES_THEN MP_TAC (← SPEC (← q r"k:num") EVEN_OR_ODD) THEN
    REWRITE_TAC [EVEN_EXISTS, ODD_EXISTS, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"b:num") THEN DISCH_THEN SUBST_ALL_TAC THEN
    X_GEN_TAC (← q r"a:num") THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_REWRITE_TAC [ADD1, ADD_SUB, EVEN_ADD, EVEN_MULT, ARITH_EVEN,
                     ← ARITH_RULE (← q r"(2 * a) DIV 2 = a"),
                     ← ARITH_RULE (← q r"((2 * a + 1) + 1) DIV 2 = a + 1")]
    THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC,
      ALL_TAC, ALL_TAC, ALL_TAC] THEN
    (ABBREV_TAC (← q r"w = @z. R ((g:num->num->A) n a) z /\  R z (g n (a + 1))") THEN
     SUBGOAL_THEN (← q r"R ((g:num->num->A) n a) w /\ R w (g n (a + 1))")
     STRIP_ASSUME_TAC THENL
      [EXPAND_TAC "w" THEN CONV_TAC SELECT_CONV THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
       ASM_ARITH_TAC,
       ALL_TAC])
    THENL
     [ALL_TAC,
      ASM_CASES_TAC (← q r"b:num = a + 1") THEN ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC (← q r"(g:num->num->A) n (a + 1)") THEN
      ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    (ABBREV_TAC (← q r"z = @z. R ((g:num->num->A) n b) z /\ R z (g n (b + 1))") THEN
     SUBGOAL_THEN (← q r"R ((g:num->num->A) n b) z /\ R z (g n (b + 1))")
     STRIP_ASSUME_TAC THENL
      [EXPAND_TAC "z" THEN CONV_TAC SELECT_CONV THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
       ASM_ARITH_TAC,
       ALL_TAC])
    THENL
     [ASM_CASES_TAC (← q r"a:num = b") THEN ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC (← q r"(g:num->num->A) n b") THEN
      ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_ARITH_TAC,
      ASM_CASES_TAC (← q r"a + 1 = b") THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC (← q r"(g:num->num->A) n (a + 1)") THEN
      ASM_REWRITE_TAC [] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC (← q r"(g:num->num->A) n b")] THEN
    ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC)

  return { RECURSION_ON_DYADIC_FRACTIONS }

/- ------------------------------------------------------------------------- -/
/- The Suslin operation. The proof of the only non-trivial result,           -/
/- idempotence, is taken from Fremlin's "Measure Theory" volume 4.           -/
/- Definitions and the simple lemmas.  (misc.ml 2130-2218)                   -/
/- ------------------------------------------------------------------------- -/

structure Suslin where
  suslin_operation : thm
  suslin : thm
  SUSLIN_INC : thm
  SUSLIN_SUPERSET : thm
  SUSLIN_SUBSET : thm
  SUSLIN_MONO : thm
  SUSLIN_REGULAR : thm
  deriving Inhabited

@[nospecialize]
def setupSuslin [HolBase] (D : MiscDeps) : ExceptT String IO Suslin := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC,
        new_definition, .. } := D
  let { EQ_IMP, EXTENSION, FINITE_IMAGE, FINITE_NUMSEG, FORALL_IN_GSPEC,
        FORALL_IN_IMAGE, IMAGE_CONST, IMAGE_EQ_EMPTY, IN, INTERS_1,
        INTERS_GSPEC, .. } := D.core1
  let { IN_ELIM_THM, IN_INTERS, IN_NUMSEG, IN_UNIV, LE_1, LE_REFL, LE_TRANS,
        LTE_TRANS, LT_TRANS, NOT_LT, NUMSEG_EMPTY, .. } := D.core2
  let { SIMPLE_IMAGE, SIMPLE_IMAGE_GEN, SUBSET, SUBSET_ANTISYM_EQ, UNIONS_1,
        UNIV_NOT_EMPTY, numseg, EL_LIST_OF_SEQ, LENGTH_EQ_NIL,
        LENGTH_LIST_OF_SEQ, LIST_EQ, .. } := D.core3
  -- @@SCOPE END

  let suslin_operation ← new_definition
   r"suslin_operation (f:num list->A->bool) =
        UNIONS { INTERS {f (list_of_seq s n) | 1 <= n} | s IN (:num->num)}"

  let suslin ← new_definition
   r"suslin u = {suslin_operation f | !l. ~(l = []) ==> f l IN u}"

  let SUSLIN_INC ← prove
   r"!C s:A->bool. C s ==> suslin C s"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [suslin, IN_ELIM_THM] THEN
    EXISTS_TAC (← q r"(\i. s):num list->A->bool") THEN
    ASM_REWRITE_TAC [suslin_operation] THEN
    REWRITE_TAC [SIMPLE_IMAGE] THEN ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC [IMAGE_CONST, UNIV_NOT_EMPTY] THEN
    COND_CASES_TAC THEN REWRITE_TAC [INTERS_1, UNIONS_1] THEN
    MP_TAC LE_REFL THEN ASM SET_TAC [])

  let SUSLIN_SUPERSET ← prove
   r"!u:(A->bool)->bool. u SUBSET suslin u"
   (REWRITE_TAC [SUBSET, IN, SUSLIN_INC])

  let SUSLIN_SUBSET ← prove
   r"!C D:(A->bool)->bool. C SUBSET D ==> suslin C SUBSET suslin D"
   (REWRITE_TAC [suslin] THEN SET_TAC [])

  let SUSLIN_MONO ← prove
   r"!C D s:A->bool.
        (!t. C t ==> D t) /\ suslin C s ==> suslin D s"
   (REWRITE_TAC [suslin] THEN SET_TAC [])

  let SUSLIN_REGULAR ← prove
   r"!u:(A->bool)->bool.
        (!c. FINITE c /\ ~(c = {}) /\ c SUBSET u ==> INTERS c IN u)
        ==> (suslin u =
             {suslin_operation f | (!l. ~(l = []) ==> f l IN u) /\
                                   !s m n. 1 <= m /\ m <= n
                                           ==> f(list_of_seq s n) SUBSET
                                               f(list_of_seq s m)})"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [suslin, ← GSYM SUBSET_ANTISYM_EQ] THEN
    CONJ_TAC THENL [ALL_TAC, SET_TAC []] THEN
    REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN
    X_GEN_TAC (← q r"f:num list->A->bool") THEN DISCH_TAC THEN
    REWRITE_TAC [IN_ELIM_THM] THEN
    EXISTS_TAC (← q r"\l. INTERS {(f:num list->A->bool)(list_of_seq (\i. EL i l) n) |n|
                          1 <= n /\ n <= LENGTH l}") THEN
    REWRITE_TAC [IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC [] THEN ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
      SIMP_TAC [← GSYM numseg, FINITE_NUMSEG, FINITE_IMAGE, IMAGE_EQ_EMPTY] THEN
      ASM_SIMP_TAC [NUMSEG_EMPTY, NOT_LT, LENGTH_EQ_NIL, LE_1] THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_NUMSEG] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC [← GSYM LENGTH_EQ_NIL, LENGTH_LIST_OF_SEQ, LE_1],
      REWRITE_TAC [IN_INTERS, FORALL_IN_GSPEC, LENGTH_LIST_OF_SEQ] THEN
      MAP_EVERY X_GEN_TAC [← q r"s:num->num", ← q r"m:num", ← q r"n:num"] THEN
      DISCH_TAC THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN
      X_GEN_TAC (← q r"p:num") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"p:num")) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      AP_TERM_TAC THEN REWRITE_TAC [LIST_EQ] THEN
      SIMP_TAC [LENGTH_LIST_OF_SEQ, EL_LIST_OF_SEQ] THEN
      X_GEN_TAC (← q r"q:num") THEN DISCH_TAC THEN
      ASM_MESON_TAC [EL_LIST_OF_SEQ, LT_TRANS, LTE_TRANS],
      REWRITE_TAC [suslin_operation] THEN AP_TERM_TAC THEN
      ONCE_REWRITE_TAC [SIMPLE_IMAGE] THEN MATCH_MP_TAC (← SET_RULE (← q
       r"(!x. f x = g x) ==> IMAGE f UNIV = IMAGE g UNIV")) THEN
      X_GEN_TAC (← q r"s:num->num") THEN
      REWRITE_TAC [EXTENSION] THEN
      X_GEN_TAC (← q r"a:A") THEN REWRITE_TAC [INTERS_GSPEC, IN_ELIM_THM] THEN
      REWRITE_TAC [IN_UNIV, LENGTH_LIST_OF_SEQ] THEN
      SUBGOAL_THEN
       (← q r"!m n. 1 <= m /\ m <= n
            ==> list_of_seq (\i. EL i (list_of_seq s n)) m :num list =
                list_of_seq s m")
       (fun th => SIMP_TAC [th])
      THENL
       [SIMP_TAC [LIST_EQ, LENGTH_LIST_OF_SEQ, EL_LIST_OF_SEQ] THEN
        MESON_TAC [EL_LIST_OF_SEQ, LTE_TRANS],
        ASM_MESON_TAC [LE_TRANS, LE_REFL]]])

  return { suslin_operation, suslin, SUSLIN_INC, SUSLIN_SUPERSET, SUSLIN_SUBSET,
           SUSLIN_MONO, SUSLIN_REGULAR }

/- ------------------------------------------------------------------------- -/
/- Idempotence of the Suslin operation, closure under countable unions and  -/
/- intersections, and cardinality.  (misc.ml 2219-2593)                      -/
/- ------------------------------------------------------------------------- -/

structure Suslin2 where
  SUSLIN_SUSLIN : thm
  SUSLIN_INTERS : thm
  SUSLIN_INTER : thm
  SUSLIN_UNIONS : thm
  SUSLIN_UNION : thm
  CARD_SUSLIN_LE : thm
  CARD_SUSLIN_EQ : thm
  deriving Inhabited

@[nospecialize]
def setupSuslin2 [HolBase] (D : MiscDeps) (BLemmas : Lemmas) (BSuslin : Suslin) :
    ExceptT String IO Suslin2 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, MESON, MESON_TAC, SET_RULE,
        SET_TAC, NUM_REDUCE_CONV, .. } := D
  let { CROSS, DEPENDENT_CHOICE, DE_MORGAN_THM, EQ_IMP, EXTENSION,
        FINITE_EMPTY, FINITE_IMAGE, FINITE_INSERT, FINITE_NUMSEG_LT,
        FINITE_SING, FINITE_UNION, FORALL_AND_THM, FORALL_IN_GSPEC,
        FORALL_IN_IMAGE, FORALL_IN_INSERT, FORALL_PAIR_THM,
        FUNCTION_FACTORS_LEFT, FUN_EQ_THM, FUN_IN_IMAGE, IMAGE_CONST, IMP_CONJ,
        IMP_CONJ_ALT, IMP_IMP, INFINITE_UNIV_PAIR, INJECTIVE_ON_LEFT_INVERSE,
        INTERS_1, INTERS_2, INTERS_GSPEC, IN_CROSS, .. } := D.core1
  let { IN_DELETE, IN_DIFF, IN_ELIM_PAIR_THM, IN_ELIM_THM, IN_INSERT, IN_SING,
        IN_UNION, IN_UNIV, LEFT_IMP_EXISTS_THM, LE_1, LE_REFL, LT_REFL,
        LT_SUC_LE, LT_TRANS, MONO_AND, NOT_INSERT_EMPTY, NOT_IN_EMPTY,
        PAIR_EQ, .. } := D.core2
  let { RIGHT_FORALL_IMP_THM, RIGHT_IMP_EXISTS_THM, RIGHT_IMP_FORALL_THM,
        SIMPLE_IMAGE, SIMPLE_IMAGE_GEN, SKOLEM_THM, SUBSET, SUBSET_ANTISYM_EQ,
        SUBSET_UNIV, TRANSITIVE_STEPWISE_LT, UNIONS_1, UNIONS_2, UNIONS_GSPEC,
        UNIV_NOT_EMPTY, WLOG_LT, num_INFINITE, o_THM, EL_LIST_OF_SEQ,
        LENGTH_EQ_NIL, LENGTH_LIST_OF_SEQ, LIST_EQ, LIST_OF_SEQ_EQ_NIL,
        NOT_CONS_NIL, .. } := D.core3
  let { CARD_DIFF_ABSORB, CARD_EQ_IMP_LE, CARD_EQ_LIST, CARD_EQ_REAL,
        CARD_EQ_REFL, CARD_EQ_SYM, CARD_EQ_TRANS, CARD_EXP_CONG, CARD_EXP_MUL,
        CARD_EXP_UNIV, CARD_LE_ANTISYM, CARD_LE_EXP_LEFT, CARD_LE_IMAGE,
        CARD_LE_SUBSET, CARD_LE_TRANS, CARD_LTE_TRANS, CARD_MUL_CONG,
        CARD_SQUARE_NUM, COUNTABLE_AS_IMAGE, COUNTABLE_EMPTY, COUNTABLE_INSERT,
        COUNTABLE_LIST, COUNTABLE_PRODUCT_DEPENDENT, COUNTABLE_SUBSET,
        EQ_C_BIJECTIONS, FINITE_CARD_LT, MUL_C_UNIV, NUM_COUNTABLE, exp_c,
        mul_c, .. } := D.lib
  let { UPPER_BOUND_FINITE_SET, .. } := BLemmas
  let { suslin_operation, suslin, SUSLIN_SUPERSET, .. } := BSuslin
  -- @@SCOPE END

  let SUSLIN_SUSLIN ← prove
   r"!u:(A->bool)->bool. suslin (suslin u) = suslin u"
   (GEN_TAC THEN REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ, SUSLIN_SUPERSET] THEN
    REWRITE_TAC [suslin, SUBSET, FORALL_IN_GSPEC] THEN
    X_GEN_TAC (← q r"f:num list->A->bool") THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [IN_ELIM_THM, RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"g:(num)list->(num)list->A->bool") THEN
    REWRITE_TAC [← TAUT (← q r"p ==> q /\ r <=> (p ==> q) /\ (p ==> r)")] THEN
    REWRITE_TAC [FORALL_AND_THM, RIGHT_IMP_FORALL_THM, IMP_IMP] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*")) THEN
    SUBGOAL_THEN
     (← q r"suslin_operation(f:num list->A->bool) =
    suslin_operation(\l. suslin_operation (g l))")
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC BINOP_CONV [suslin_operation] THEN
      REWRITE_TAC [SIMPLE_IMAGE] THEN
      AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC id [FUN_EQ_THM] THEN X_GEN_TAC (← q r"s:num->num") THEN
      REWRITE_TAC [] THEN AP_TERM_TAC THEN MATCH_MP_TAC (← SET_RULE (← q
       r"(!x. P x ==> f x = g x) ==> {f x | P x} = {g x | P x}")) THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC [← GSYM LENGTH_EQ_NIL, LENGTH_LIST_OF_SEQ, LE_1],
      REMOVE_THEN "*" (K ALL_TAC)] THEN
    REWRITE_TAC [IN_ELIM_THM, suslin_operation] THEN
    ONCE_REWRITE_TAC [EXTENSION] THEN
    REWRITE_TAC [IN_ELIM_THM, INTERS_GSPEC, UNIONS_GSPEC, IN_UNIV] THEN
    REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN
    REWRITE_TAC [RIGHT_IMP_FORALL_THM, IMP_IMP] THEN
    SUBGOAL_THEN
     (← q r"?h:num->A->bool.
        {g l m | ~(l:num list = []) /\ ~(m:num list = [])} = IMAGE h (:num)")
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC COUNTABLE_AS_IMAGE THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC [← SET_RULE (← q r"~(x = []) <=> x IN {l | ~(l = [])}")] THEN
        MATCH_MP_TAC COUNTABLE_PRODUCT_DEPENDENT THEN
        MATCH_MP_TAC (← TAUT (← q r"(p ==> q) /\ p ==> p /\ q")) THEN SIMP_TAC [] THEN
        MATCH_MP_TAC COUNTABLE_SUBSET THEN EXISTS_TAC (← q r"(:num list)") THEN
        REWRITE_TAC [SUBSET_UNIV] THEN MATCH_MP_TAC COUNTABLE_LIST THEN
        REWRITE_TAC [NUM_COUNTABLE],
        MATCH_MP_TAC (← SET_RULE (← q r"(?x. P x) ==> ~({f x y | P x /\ P y} = {})")) THEN
        MESON_TAC [NOT_CONS_NIL]],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"?q:num#num->num.
        (!a b. 1 <= q(a,b)) /\
        q(0,0) = 1 /\ q(0,1) = 2 /\
        (!a b a' b'. q(a,b) = q(a',b') <=> a = a' /\ b = b')")
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN
       (← q r"(:num#num) DIFF {(0,0), (0,1)} =_c (:num) DIFF {0,1,2}")
      MP_TAC THENL
       [TRANS_TAC CARD_EQ_TRANS (← q r"(:num#num)") THEN CONJ_TAC THENL
         [MATCH_MP_TAC CARD_DIFF_ABSORB THEN
          REWRITE_TAC [INFINITE_UNIV_PAIR, num_INFINITE] THEN
          TRANS_TAC CARD_LTE_TRANS (← q r"(:num)") THEN
          REWRITE_TAC [← GSYM FINITE_CARD_LT, FINITE_INSERT, FINITE_EMPTY] THEN
          MATCH_MP_TAC CARD_EQ_IMP_LE THEN ONCE_REWRITE_TAC [CARD_EQ_SYM] THEN
          REWRITE_TAC [CARD_SQUARE_NUM, ← GSYM MUL_C_UNIV],
          REWRITE_TAC [← GSYM MUL_C_UNIV] THEN TRANS_TAC CARD_EQ_TRANS (← q r"(:num)") THEN
          REWRITE_TAC [CARD_SQUARE_NUM] THEN ONCE_REWRITE_TAC [CARD_EQ_SYM] THEN
          MATCH_MP_TAC CARD_DIFF_ABSORB THEN REWRITE_TAC [num_INFINITE] THEN
          REWRITE_TAC [← GSYM FINITE_CARD_LT, FINITE_INSERT, FINITE_EMPTY]],
        REWRITE_TAC [EQ_C_BIJECTIONS, LEFT_IMP_EXISTS_THM] THEN
        MAP_EVERY X_GEN_TAC [← q r"q:num#num->num", ← q r"q':num->num#num"] THEN
        REWRITE_TAC [FORALL_PAIR_THM, IN_DIFF, IN_UNIV, IN_INSERT] THEN
        REWRITE_TAC [PAIR_EQ, NOT_IN_EMPTY, DE_MORGAN_THM] THEN STRIP_TAC THEN
        SUBGOAL_THEN
         (← q r"!a b a' b'. q(a,b):num = q(a',b')
                    ==> a = 0 /\ (b = 0 \/ b = 1) \/
                        a' = 0 /\ (b' = 0 \/ b' = 1) \/
                        a = a' /\ b = b'")
        ASSUME_TAC THENL
         [MAP_EVERY X_GEN_TAC [← q r"a:num", ← q r"b:num", ← q r"c:num", ← q r"d:num"] THEN
          REWRITE_TAC [← TAUT (← q r"p ==> q \/ r <=> p ==> ~q ==> r")] THEN
          REPEAT DISCH_TAC THEN FIRST_X_ASSUM (fun th => tactic_of do
            pure (MP_TAC (← SPECL [← q r"a:num", ← q r"b:num"] th) THEN
                  MP_TAC (← SPECL [← q r"c:num", ← q r"d:num"] th))) THEN
          ASM_REWRITE_TAC [← GSYM PAIR_EQ] THEN ASM_MESON_TAC [],
          ALL_TAC] THEN
        EXISTS_TAC (← q r"\(a,b). if (a,b) = (0,0) then 1
                          else if (a,b) = (0,1) then 2 else q(a,b)") THEN
        ASM_REWRITE_TAC [PAIR_EQ, ← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        CONJ_TAC THEN REPEAT GEN_TAC THEN
        REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
        CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC []],
      ALL_TAC] THEN
    ABBREV_TAC (← q r"J = \(k,m). {(i,0) | i < k} UNION {(i,k) | i < m}") THEN
    SUBGOAL_THEN
     (← q r"?k:num->num m:num->num.
        IMAGE (\n. k n,m n) {n | 3 <= n} =
        ((:num) DELETE 0) CROSS ((:num) DELETE 0) /\
        !n. 3 <= n ==> IMAGE (q:num#num->num) (J(k n,m n)) SUBSET {a | a < n}")
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN
       (← q r"?r:num#num->num.
        (!a. a IN ((:num) DELETE 0) CROSS ((:num) DELETE 0)
             ==> r a IN {n | 3 <= n}) /\
        (!a. a IN ((:num) DELETE 0) CROSS ((:num) DELETE 0)
             ==> IMAGE (q:num#num->num) (J a) SUBSET {m | m < r a}) /\
        (!a b. a IN ((:num) DELETE 0) CROSS ((:num) DELETE 0) /\
               b IN ((:num) DELETE 0) CROSS ((:num) DELETE 0) /\
               r a = r b
               ==> a = b)")
      STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN (← q r"((:num) DELETE 0) CROSS ((:num) DELETE 0) =_c (:num)")
        MP_TAC THENL
         [TRANS_TAC CARD_EQ_TRANS (← q r"(:num) *_c (:num)") THEN
          REWRITE_TAC [CARD_SQUARE_NUM, CROSS, ← GSYM mul_c] THEN
          MATCH_MP_TAC CARD_MUL_CONG THEN REWRITE_TAC [] THEN
          REWRITE_TAC [← SET_RULE (← q r"s DELETE a = s DIFF {a}")] THEN
          MATCH_MP_TAC CARD_DIFF_ABSORB THEN
          REWRITE_TAC [num_INFINITE, ← GSYM FINITE_CARD_LT, FINITE_SING],
          REWRITE_TAC [EQ_C_BIJECTIONS, LEFT_IMP_EXISTS_THM, IN_UNIV]] THEN
        MAP_EVERY X_GEN_TAC [← q r"p':num#num->num", ← q r"p:num->num#num"] THEN
        STRIP_TAC THEN
        SUBGOAL_THEN
         (← q r"?t:num->num. (!n. IMAGE q ((J:num#num->num#num->bool)(p n)) SUBSET
                          {a | a < t n} /\ 2 < t n) /\
                     (!n. t n < t (SUC n))")
        MP_TAC THENL
         [MATCH_MP_TAC DEPENDENT_CHOICE THEN
          REWRITE_TAC [← SET_RULE (← q r"s SUBSET {a | a < y} /\ x < y <=>
                              (x INSERT s) SUBSET {a:num | a < y}")] THEN
          REPEAT STRIP_TAC THEN
          MATCH_MP_TAC (← MESON [] (← q r"(?a. P(SUC a)) ==> (?a. P a)")) THEN
          REWRITE_TAC [LT_SUC_LE, SUBSET, IN_ELIM_THM] THEN
          MATCH_MP_TAC UPPER_BOUND_FINITE_SET THEN
          REWRITE_TAC [FINITE_INSERT] THEN MATCH_MP_TAC FINITE_IMAGE THEN
          EXPAND_TAC "J" THEN
          MATCH_MP_TAC (← MESON [] (← q r"(!x. FINITE(f x)) ==> FINITE(f a)")) THEN
          REWRITE_TAC [FORALL_PAIR_THM, FINITE_UNION] THEN
          ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
          SIMP_TAC [FINITE_NUMSEG_LT, FINITE_IMAGE],
          REWRITE_TAC [← ARITH_RULE (← q r"2 < n <=> 3 <= n")] THEN STRIP_TAC] THEN
        EXISTS_TAC (← q r"(t:num->num) o (p':num#num->num)") THEN
        ASM_REWRITE_TAC [o_THM, IN_ELIM_THM] THEN
        CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
        SUBGOAL_THEN
         (← q r"((:num) DELETE 0) CROSS ((:num) DELETE 0) =
        IMAGE p (:num)")
        SUBST1_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
        REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_IMAGE] THEN
        ASM_REWRITE_TAC [IN_UNIV] THEN
        MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC [] THEN
        CONJ_TAC THENL [MESON_TAC [], ALL_TAC] THEN
        SUBGOAL_THEN (← q r"!m n. m < n ==> (t:num->num) m < t n") MP_TAC THENL
         [ALL_TAC, MESON_TAC [LT_REFL]] THEN
        MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN
        ASM_REWRITE_TAC [LT_TRANS],
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id
         [INJECTIVE_ON_LEFT_INVERSE]) THEN
        DISCH_THEN (X_CHOOSE_TAC (← q r"l:num->num#num")) THEN
        EXISTS_TAC (← q
         r"\n. if n IN IMAGE r (((:num) DELETE 0) CROSS ((:num) DELETE 0))
                then FST((l:num->num#num) n) else 1") THEN
        EXISTS_TAC (← q
         r"\n. if n IN IMAGE r (((:num) DELETE 0) CROSS ((:num) DELETE 0))
                then SND((l:num->num#num) n) else 1") THEN
        REWRITE_TAC [← MESON [] (← q
         r"(if p then x else 1),(if p then y else 1) =
        (if p then x,y else 1,1)")] THEN
        GEN_REWRITE_TAC LAND_CONV [← GSYM SUBSET_ANTISYM_EQ] THEN
        REPEAT CONJ_TAC THENL
         [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
          REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
          REWRITE_TAC [IN_CROSS, IN_UNIV, IN_DELETE] THEN
          CONV_TAC NUM_REDUCE_CONV THEN ASM SET_TAC [],
          ASM SET_TAC [],
          REPEAT STRIP_TAC THEN
          REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
          GEN_TAC THEN COND_CASES_TAC THEN
          REWRITE_TAC [IN_CROSS, IN_UNIV, IN_DELETE] THENL
           [ASM SET_TAC [], ALL_TAC] THEN
          EXPAND_TAC "J" THEN REWRITE_TAC [IN_UNION] THEN
          REWRITE_TAC [← ARITH_RULE (← q r"i < 1 <=> i = 0")] THEN
          REWRITE_TAC [← SET_RULE (← q r"{f x | x = a} = {f a}")] THEN
          REWRITE_TAC [IN_SING] THEN STRIP_TAC THEN
          ASM_REWRITE_TAC [IN_ELIM_THM] THEN ASM_ARITH_TAC]],
      ALL_TAC] THEN
    ABBREV_TAC (← q
     r"f = \l. if LENGTH l <= 2 then h(EL 0 l)
            else (g:(num)list->(num)list->A->bool)
                (list_of_seq (\i. EL (q(i,0)) l) (k(LENGTH l)))
                (list_of_seq (\i. EL (q(i,k(LENGTH l))) l) (m(LENGTH l)))") THEN
    EXISTS_TAC (← q r"f:num list->A->bool") THEN EXPAND_TAC "f" THEN
    REWRITE_TAC [] THEN CONJ_TAC THENL
     [X_GEN_TAC (← q r"l:num list") THEN DISCH_TAC THEN COND_CASES_TAC THENL
       [ASM SET_TAC [], FIRST_X_ASSUM MATCH_MP_TAC] THEN
      REWRITE_TAC [← GSYM LENGTH_EQ_NIL, LENGTH_LIST_OF_SEQ] THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP (← SET_RULE (← q
       r"IMAGE f s = t ==> !x. x IN s ==> f x IN t"))) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"LENGTH(l:num list)")) THEN
      REWRITE_TAC [IN_ELIM_THM, IN_CROSS, IN_UNIV, IN_DELETE] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    X_GEN_TAC (← q r"x:A") THEN EQ_TAC THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THENL
     [MAP_EVERY X_GEN_TAC [← q r"s:num->num", ← q r"s':num->num->num"] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       (← q r"?t. h(t 0) = (g:(num)list->(num)list->A->bool)
                   (list_of_seq s 1) (list_of_seq (s' 1) 1) /\
          (!i. t(q(i,0)) = s i) /\
          (!i j. 1 <= j ==> t(q(i,j)) = s' j i)")
      STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN
         (← q r"?t:num->num.
          (\(i,j). if j = 0 then s i else s' j i) = t o (q:num#num->num)")
        MP_TAC THENL
         [REWRITE_TAC [← GSYM FUNCTION_FACTORS_LEFT] THEN
          ASM_REWRITE_TAC [FORALL_PAIR_THM] THEN SIMP_TAC [],
          REWRITE_TAC [FUN_EQ_THM, FORALL_PAIR_THM, o_THM]] THEN
        DISCH_THEN (X_CHOOSE_TAC (← q r"t:num->num") o GSYM) THEN
        FIRST_ASSUM (MP_TAC o MATCH_MP (← SET_RULE (← q
         r"t = IMAGE f UNIV ==> !y. y IN t ==> ?x. f x = y"))) THEN
        REWRITE_TAC [FORALL_IN_GSPEC] THEN
        DISCH_THEN (MP_TAC o SPECL
         [← q r"list_of_seq s 1:num list", ← q r"list_of_seq (s' 1) 1:num list"]) THEN
        REWRITE_TAC [LIST_OF_SEQ_EQ_NIL] THEN CONV_TAC NUM_REDUCE_CONV THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"p:num") (SUBST1_TAC o SYM)) THEN
        EXISTS_TAC (← q r"\n. if n = 0 then p:num else t n") THEN
        ASM_SIMP_TAC [LE_1],
        EXISTS_TAC (← q r"t:num->num")] THEN
      X_GEN_TAC (← q r"n:num") THEN REWRITE_TAC [LENGTH_LIST_OF_SEQ] THEN
      SIMP_TAC [LE_1, EL_LIST_OF_SEQ] THEN DISCH_TAC THEN COND_CASES_TAC THENL
       [ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        CONV_TAC NUM_REDUCE_CONV,
        RULE_ASSUM_TAC (REWRITE_RULE [← ARITH_RULE (← q r"~(n <= 2) <=> 3 <= n")])] THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP (← SET_RULE (← q
       r"IMAGE f s = t ==> !x. x IN s ==> f x IN t"))) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"n:num")) THEN
      ASM_REWRITE_TAC [IN_ELIM_THM, IN_CROSS, IN_DELETE, IN_UNIV] THEN
      REWRITE_TAC [← ARITH_RULE (← q r"~(n = 0) <=> 1 <= n")] THEN
      DISCH_THEN (fun th => STRIP_ASSUME_TAC th THEN
       FIRST_X_ASSUM (fun a => tactic_of do pure (MP_TAC (← MATCH_MP a th)))) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN BINOP_TAC THEN
      SIMP_TAC [LIST_EQ, LENGTH_LIST_OF_SEQ, EL_LIST_OF_SEQ] THEN
      X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN
      W (MP_TAC o PART_MATCH (lhand o rand) EL_LIST_OF_SEQ o rand o snd) THEN
      ASM_SIMP_TAC [LE_1] THEN DISCH_THEN (MATCH_MP_TAC o GSYM),
      X_GEN_TAC (← q r"t:num->num") THEN DISCH_THEN (LABEL_TAC "*") THEN
      EXISTS_TAC (← q r"\i:num. (t:num->num)(q(i,0))") THEN
      EXISTS_TAC (← q r"\j:num i:num. (t:num->num)(q(i,j))") THEN
      MAP_EVERY X_GEN_TAC [← q r"kk:num", ← q r"mm:num"] THEN STRIP_TAC THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP (← SET_RULE (← q
       r"IMAGE f s = t ==> !y. y IN t ==> ?x. x IN s /\ f x = y"))) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"(kk:num),(mm:num)")) THEN
      ASM_SIMP_TAC [IN_CROSS, IN_DELETE, IN_UNIV, LE_1, PAIR_EQ, IN_ELIM_THM] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"n:num") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN (CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      REMOVE_THEN "*" (MP_TAC o SPEC (← q r"n:num")) THEN
      ASM_SIMP_TAC [LENGTH_LIST_OF_SEQ, ← ARITH_RULE (← q
       r"3 <= n ==> 1 <= n /\ ~(n <= 2)")] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN BINOP_TAC THEN
      SIMP_TAC [LIST_EQ, LENGTH_LIST_OF_SEQ, EL_LIST_OF_SEQ] THEN
      X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN
      MATCH_MP_TAC EL_LIST_OF_SEQ] THEN
    RULE_ASSUM_TAC (REWRITE_RULE
     [SUBSET, IN_ELIM_THM, FORALL_IN_IMAGE, RIGHT_IMP_FORALL_THM, IMP_IMP]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
    EXPAND_TAC "J" THEN REWRITE_TAC [IN_UNION, IN_ELIM_PAIR_THM] THEN
    ASM SET_TAC [])

  let SUSLIN_INTERS ← prove
   r"!C f:(A->bool)->bool.
        COUNTABLE f /\ ~(f = {}) /\
        (!s. s IN f ==> suslin C s)
        ==> suslin C (INTERS f)"
   (REPEAT GEN_TAC THEN
    REPLICATE_TAC 2 (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MP_TAC (← ISPEC (← q r"f:(A->bool)->bool") COUNTABLE_AS_IMAGE) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"f:num->A->bool") THEN DISCH_THEN SUBST1_TAC THEN
    POP_ASSUM_LIST (K ALL_TAC) THEN REWRITE_TAC [FORALL_IN_IMAGE, IN_UNIV] THEN
    DISCH_TAC THEN ONCE_REWRITE_TAC [← GSYM SUSLIN_SUSLIN] THEN
    ONCE_REWRITE_TAC [suslin] THEN
    REWRITE_TAC [IN_ELIM_THM, suslin_operation] THEN
    EXISTS_TAC (← q r"(f:num->A->bool) o (\n. n - 1) o (LENGTH:num list->num)") THEN
    ASM_REWRITE_TAC [o_THM, LENGTH_LIST_OF_SEQ] THEN
    REWRITE_TAC [SIMPLE_IMAGE, IMAGE_CONST, UNIV_NOT_EMPTY, UNIONS_1] THEN
    CONJ_TAC THENL [ASM SET_TAC [], AP_TERM_TAC] THEN
    MP_TAC (← ARITH_RULE (← q r"!n. 1 <= SUC n /\ SUC n - 1 = n")) THEN
    SET_TAC [])

  let SUSLIN_INTER ← prove
   r"!C s t:A->bool. suslin C s /\ suslin C t ==> suslin C (s INTER t)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM INTERS_2] THEN
    MATCH_MP_TAC SUSLIN_INTERS THEN
    REWRITE_TAC [COUNTABLE_INSERT, COUNTABLE_EMPTY, NOT_INSERT_EMPTY] THEN
    ASM_REWRITE_TAC [FORALL_IN_INSERT, NOT_IN_EMPTY])

  let SUSLIN_UNIONS ← prove
   r"!C f:(A->bool)->bool.
        COUNTABLE f /\ ~(f = {}) /\
        (!s. s IN f ==> suslin C s)
        ==> suslin C (UNIONS f)"
   (REPEAT GEN_TAC THEN
    REPLICATE_TAC 2 (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MP_TAC (← ISPEC (← q r"f:(A->bool)->bool") COUNTABLE_AS_IMAGE) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"f:num->A->bool") THEN DISCH_THEN SUBST1_TAC THEN
    POP_ASSUM_LIST (K ALL_TAC) THEN REWRITE_TAC [FORALL_IN_IMAGE, IN_UNIV] THEN
    DISCH_TAC THEN ONCE_REWRITE_TAC [← GSYM SUSLIN_SUSLIN] THEN
    ONCE_REWRITE_TAC [suslin] THEN
    REWRITE_TAC [IN_ELIM_THM, suslin_operation] THEN
    EXISTS_TAC (← q r"(f:num->A->bool) o (EL 0:num list->num)") THEN
    ASM_REWRITE_TAC [o_THM] THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!f:num->A->bool s.
        {f (EL 0 (list_of_seq s n)) | 1 <= n} = {f(s 0)}")
     (fun th => REWRITE_TAC [th])
    THENL
     [REPEAT GEN_TAC THEN
      MATCH_MP_TAC (← SET_RULE (← q
       r"(?x. P x) /\ (!x. P x ==> f x = a) ==> {f x | P x} = {a}")) THEN
      SIMP_TAC [EL_LIST_OF_SEQ, LE_1] THEN MESON_TAC [LE_REFL],
      REWRITE_TAC [INTERS_1] THEN AP_TERM_TAC THEN
      REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ, SUBSET, FORALL_IN_GSPEC] THEN
      SIMP_TAC [FUN_IN_IMAGE, IN_UNIV, FORALL_IN_IMAGE] THEN
      X_GEN_TAC (← q r"n:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN
      EXISTS_TAC (← q r"(\i. n):num->num") THEN REWRITE_TAC []])

  let SUSLIN_UNION ← prove
   r"!C s t:A->bool. suslin C s /\ suslin C t ==> suslin C (s UNION t)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM UNIONS_2] THEN
    MATCH_MP_TAC SUSLIN_UNIONS THEN
    REWRITE_TAC [COUNTABLE_INSERT, COUNTABLE_EMPTY, NOT_INSERT_EMPTY] THEN
    ASM_REWRITE_TAC [FORALL_IN_INSERT, NOT_IN_EMPTY])

  let CARD_SUSLIN_LE ← prove
   r"!C:(A->bool)->bool. C <=_c (:real) ==> suslin C <=_c (:real)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [suslin] THEN
    ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
    TRANS_TAC CARD_LE_TRANS
     (← q r"IMAGE suslin_operation ((C:(A->bool)->bool) ^_c (:num list))") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_LE_SUBSET THEN REWRITE_TAC [exp_c, IN_UNIV] THEN
      MATCH_MP_TAC (← SET_RULE (← q
       r"(!x. x IN s ==> ?y. y IN t /\ f x = f y)
      ==> IMAGE f s SUBSET IMAGE f t")) THEN
      X_GEN_TAC (← q r"f:num list->A->bool") THEN REWRITE_TAC [IN_ELIM_THM] THEN
      STRIP_TAC THEN
      EXISTS_TAC (← q r"\l. if l = [] then f[0] else f l:A->bool") THEN
      REWRITE_TAC [suslin_operation] THEN
      CONJ_TAC THENL [ASM_MESON_TAC [NOT_CONS_NIL], ALL_TAC] THEN
      REPEAT (AP_TERM_TAC THEN
              MATCH_MP_TAC (← SET_RULE (← q
               r"(!x. P x ==> f x = g x) ==> {f x | P x} = {g x | P x}")) THEN
              REPEAT STRIP_TAC) THEN
      ASM_SIMP_TAC [LIST_OF_SEQ_EQ_NIL, LE_1],
      ALL_TAC] THEN
    W (MP_TAC o PART_MATCH lhand CARD_LE_IMAGE o lhand o snd) THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] CARD_LE_TRANS) THEN
    TRANS_TAC CARD_LE_TRANS (← q r"(:real) ^_c (:num list)") THEN
    ASM_SIMP_TAC [CARD_LE_EXP_LEFT] THEN
    TRANS_TAC CARD_LE_TRANS (← q r"(:num->bool) ^_c (:num)") THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_EQ_IMP_LE THEN MATCH_MP_TAC CARD_EXP_CONG THEN
      SIMP_TAC [CARD_EQ_REAL, CARD_EQ_LIST, num_INFINITE],
      ALL_TAC] THEN
    REWRITE_TAC [← GSYM CARD_EXP_UNIV] THEN
    W (MP_TAC o PART_MATCH rand CARD_EXP_MUL o lhand o snd) THEN
    ONCE_REWRITE_TAC [CARD_EQ_SYM] THEN
    DISCH_THEN (MP_TAC o MATCH_MP CARD_EQ_IMP_LE) THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] CARD_LE_TRANS) THEN
    MATCH_MP_TAC CARD_EQ_IMP_LE THEN
    TRANS_TAC CARD_EQ_TRANS (← q r"(:num->bool)") THEN
    ONCE_REWRITE_TAC [CARD_EQ_SYM] THEN REWRITE_TAC [CARD_EQ_REAL] THEN
    REWRITE_TAC [← GSYM CARD_EXP_UNIV] THEN
    MATCH_MP_TAC CARD_EXP_CONG THEN REWRITE_TAC [CARD_EQ_REFL] THEN
    ONCE_REWRITE_TAC [CARD_EQ_SYM] THEN REWRITE_TAC [CARD_SQUARE_NUM])

  let CARD_SUSLIN_EQ ← prove
   r"!C:(A->bool)->bool. C =_c (:real) ==> suslin C =_c (:real)"
   (GEN_TAC THEN SIMP_TAC [← GSYM CARD_LE_ANTISYM] THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC [CARD_SUSLIN_LE] THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] CARD_LE_TRANS) THEN
    MATCH_MP_TAC CARD_LE_SUBSET THEN REWRITE_TAC [SUSLIN_SUPERSET])

  return { SUSLIN_SUSLIN, SUSLIN_INTERS, SUSLIN_INTER, SUSLIN_UNIONS,
           SUSLIN_UNION, CARD_SUSLIN_LE, CARD_SUSLIN_EQ }

end HolMultiLib.Misc
