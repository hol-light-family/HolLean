/- ========================================================================= -/
/- Arithmetic-geometric mean inequality.                                     -/
/- ========================================================================= -/
/- File: HolLibrary/Agm.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/agm.ml`, by hand, in file order, in
  the style of HolLibrary/Products.lean (see there and HolMath/Base.lean for
  the conventions).  agm.ml begins with `needs "Library/products.ml"` then
  `prioritize_real()`; products.ml's theorems it uses (PRODUCT_ADD_SPLIT,
  PRODUCT_CLAUSES_NUMSEG, PRODUCT_OFFSET, PRODUCT_POS_LE) are supplied via the
  CoreThms structures (SessionLibrary.Agm fills them from
  SessionLibrary.Products).  The whole file is one bundle (a `structure`)
  built by a `setup` function; SessionLibrary/Agm.lean builds it and exports
  every name under its HOL Light name.

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, REAL_ARITH, REAL_FIELD) they are bound
  first, in OCaml's order.
-/

import HolLibrary.Products

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

set_option maxRecDepth 8000

namespace HolLibrary.Agm

/- ------------------------------------------------------------------------- -/
/- What agm.ml uses from the core library and products.ml (via Session).     -/
/- ------------------------------------------------------------------------- -/

/-- Theorems agm.ml uses from the core library and products.ml. -/
structure CoreThms1 where
  (ADD1 ADD_SYM ARITH EVEN_EXISTS EXTENSION FINITE_NUMSEG FINITE_RULES
   IN_INSERT IN_NUMSEG LEFT_IMP_EXISTS_THM LE_EXISTS LE_REFL MULT_2 NOT_EVEN
   NOT_IN_EMPTY ODD_EXISTS PRODUCT_ADD_SPLIT PRODUCT_CLAUSES
   PRODUCT_CLAUSES_NUMSEG PRODUCT_OFFSET PRODUCT_POS_LE REAL_ADD_RID
   REAL_ENTIRE REAL_INV_EQ_0 REAL_INV_MUL REAL_LE_ANTISYM REAL_LE_DIV
   REAL_LE_LMUL_EQ REAL_LE_MUL REAL_LE_MUL2 REAL_LE_REFL REAL_LE_SQUARE
   REAL_LE_TRANS REAL_MUL_LZERO REAL_MUL_RID REAL_MUL_RZERO REAL_MUL_SYM
   REAL_NOT_LT REAL_OF_NUM_EQ REAL_OF_NUM_LE REAL_OF_NUM_MUL REAL_OF_NUM_SUC
   REAL_POS REAL_POW_LE2 REAL_POW_MUL REAL_POW_POW SUM_ADD_SPLIT SUM_CLAUSES
   SUM_CLAUSES_NUMSEG SUM_OFFSET SUM_POS_EQ_0_NUMSEG SUM_POS_LE num_WF
   real_div real_pow : thm)
  deriving Inhabited

/-- What agm.ml uses from Session besides theorems. -/
structure AgmDeps where
  -- parser state
  prioritize_real : IO Unit
  -- decision procedures and tactics
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_MESON_TAC : List thm → tactic
  MESON_TAC : List thm → tactic
  REAL_ARITH : term → ExceptT String IO thm
  REAL_FIELD : term → ExceptT String IO thm
  core1 : CoreThms1

/- ------------------------------------------------------------------------- -/
/- The whole file is one bundle.  (agm.ml 1-153)                             -/
/- ------------------------------------------------------------------------- -/

structure Agm where
  -- @@FIELDS
  FORALL_2 : thm
  NUMSEG_2 : thm
  AGM_2 : thm
  SUM_SPLIT_2 : thm
  PRODUCT_SPLIT_2 : thm
  CAUCHY_INDUCT : thm
  AGM : thm
  deriving Inhabited

@[nospecialize]
def setupAgm [HolBase] (D : AgmDeps) :
    ExceptT String IO Agm := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, MESON_TAC, REAL_ARITH, REAL_FIELD,
        prioritize_real, .. } := D
  let { ADD1, ADD_SYM, ARITH, EVEN_EXISTS, EXTENSION, FINITE_NUMSEG, FINITE_RULES,
        IN_INSERT, IN_NUMSEG, LEFT_IMP_EXISTS_THM, LE_EXISTS, LE_REFL, MULT_2,
        NOT_EVEN, NOT_IN_EMPTY, ODD_EXISTS, PRODUCT_ADD_SPLIT, PRODUCT_CLAUSES,
        PRODUCT_CLAUSES_NUMSEG, PRODUCT_OFFSET, PRODUCT_POS_LE, REAL_ADD_RID,
        REAL_ENTIRE, REAL_INV_EQ_0, REAL_INV_MUL, REAL_LE_ANTISYM, REAL_LE_DIV,
        REAL_LE_LMUL_EQ, REAL_LE_MUL, REAL_LE_MUL2, REAL_LE_REFL, REAL_LE_SQUARE,
        REAL_LE_TRANS, REAL_MUL_LZERO, REAL_MUL_RID, REAL_MUL_RZERO, REAL_MUL_SYM,
        REAL_NOT_LT, REAL_OF_NUM_EQ, REAL_OF_NUM_LE, REAL_OF_NUM_MUL, REAL_OF_NUM_SUC,
        REAL_POS, REAL_POW_LE2, REAL_POW_MUL, REAL_POW_POW, SUM_ADD_SPLIT, SUM_CLAUSES,
        SUM_CLAUSES_NUMSEG, SUM_OFFSET, SUM_POS_EQ_0_NUMSEG, SUM_POS_LE, num_WF,
        real_div, real_pow, .. } := D.core1
  -- @@SCOPE END

  prioritize_real

  /- --------------------------------------------------------------------- -/
  /- Various trivial lemmas.                                               -/
  /- --------------------------------------------------------------------- -/

  let FORALL_2 ← prove
   r"!P. (!i. 1 <= i /\ i <= 2 ==> P i) <=> P 1 /\ P 2"
   (MESON_TAC [← ARITH_RULE (← q r"1 <= i /\ i <= 2 <=> i = 1 \/ i = 2")])

  let NUMSEG_2 ← prove
   r"1..2 = {1,2}"
   (REWRITE_TAC [EXTENSION, IN_INSERT, NOT_IN_EMPTY, IN_NUMSEG] THEN ARITH_TAC)

  let AGM_2 ← prove
   r"!x y. x * y <= ((x + y) / &2) pow 2"
   (REWRITE_TAC [REAL_LE_SQUARE, ← REAL_ARITH
     (← q r"x * y <= ((x + y) / &2) pow 2 <=> &0 <= (x - y) * (x - y)")])

  let SUM_SPLIT_2 ← prove
   r"sum(1..2*n) f = sum(1..n) f + sum(n+1..2*n) f"
   (SIMP_TAC [MULT_2, ← ARITH_RULE (← q "1 <= n + 1"), SUM_ADD_SPLIT])

  let PRODUCT_SPLIT_2 ← prove
   r"product(1..2*n) f = product(1..n) f * product(n+1..2*n) f"
   (SIMP_TAC [MULT_2, ← ARITH_RULE (← q "1 <= n + 1"), PRODUCT_ADD_SPLIT])

  /- --------------------------------------------------------------------- -/
  /- Specialized induction principle.                                      -/
  /- --------------------------------------------------------------------- -/

  let CAUCHY_INDUCT ← prove
   r"!P. P 2 /\ (!n. P n ==> P(2 * n)) /\ (!n. P(n + 1) ==> P n) ==> !n. P n"
   (← do
    let m5 ← ARITH_RULE (← q r"SUC(2 * m) + 1 = 2 * (m + 1)")
    let m4 ← ARITH_RULE (← q r"SUC(2 * m) = 1 \/ m + 1 < SUC(2 * m)")
    let m3 ← ARITH_RULE (← q r"2 * n = 0 \/ n < 2 * n")
    let m2 ← ARITH_RULE (← q r"1 = 0 + 1 /\ 2 = 1 + 1")
    pure (GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC num_WF THEN
    X_GEN_TAC (← q "n:num") THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"P(0) /\ P(1)") STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC [m2], ALL_TAC] THEN
    ASM_CASES_TAC (← q "EVEN n") THENL
     [FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
      ASM_MESON_TAC [m3],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [NOT_EVEN]) THEN
    SIMP_TAC [ODD_EXISTS, LEFT_IMP_EXISTS_THM] THEN
    ASM_MESON_TAC [m4, m5]))

  /- --------------------------------------------------------------------- -/
  /- The main result.                                                      -/
  /- --------------------------------------------------------------------- -/

  let AGM ← prove
   r"!n a. 1 <= n /\ (!i. 1 <= i /\ i <= n ==> &0 <= a(i))
           ==> product(1..n) a <= (sum(1..n) a / &n) pow n"
   (← do
    -- the printing rules bound last-first, as OCaml evaluates the proof
    let asm1 ← ASSUME (← q r"1 <= n")
    let a14 ← ARITH_RULE (← q r"1 <= SUC n")
    let a13 ← ARITH_RULE (← q r"1 + n = SUC n")
    let a12 ← ARITH_RULE (← q r"1 <= n ==> ~(n = 0)")
    let f11 ← REAL_FIELD
      (← q r"&1 <= &n ==> (s + s / &n) / (&n + &1) = s / &n")
    let a10 ← ARITH_RULE (← q r"1 <= SUC n /\ ~(SUC n <= n)")
    let a9 ← ARITH_RULE (← q r"1 <= n + 1")
    let r8 ← REAL_ARITH (← q r"(x + y) * (a * b) = (x * a + y * a) * b")
    let r7 ← REAL_ARITH (← q r"&2 * &n = &n * &2")
    let a6 ← ARITH_RULE (← q r"1 <= 2 * n ==> 1 <= n")
    let a5 ← ARITH_RULE
      (← q r"1 <= i /\ i <= n ==> 1 <= i + n /\ i + n <= 2 * n")
    let a4 ← ARITH_RULE (← q r"n + 1 <= i ==> 1 <= i")
    let a3 ← ARITH_RULE (← q r"1 <= 2 * n ==> 1 <= n")
    let a2 ← ARITH_RULE (← q r"i <= n ==> i <= 2 * n")
    let a1 ← ARITH_RULE (← q r"i <= n ==> i <= 2 * n")
    pure (MATCH_MP_TAC CAUCHY_INDUCT THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC [FORALL_2, NUMSEG_2] THEN
      SIMP_TAC [SUM_CLAUSES, PRODUCT_CLAUSES, FINITE_RULES, IN_INSERT,
               NOT_IN_EMPTY, ARITH, REAL_MUL_RID, REAL_ADD_RID] THEN
      REWRITE_TAC [AGM_2],
      X_GEN_TAC (← q "n:num") THEN DISCH_TAC THEN X_GEN_TAC (← q r"a:num->real") THEN
      STRIP_TAC THEN REWRITE_TAC [SUM_SPLIT_2, PRODUCT_SPLIT_2] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"(sum(1..n) a / &n) pow n * (sum(n+1..2*n) a / &n) pow n") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC PRODUCT_POS_LE THEN
          REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG] THEN
          ASM_MESON_TAC [a1],
          FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_MESON_TAC [a2, a3],
          MATCH_MP_TAC PRODUCT_POS_LE THEN
          REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG] THEN
          ASM_MESON_TAC [a4],
          ONCE_REWRITE_TAC [ADD_SYM] THEN REWRITE_TAC [MULT_2] THEN
          REWRITE_TAC [PRODUCT_OFFSET, SUM_OFFSET] THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_MESON_TAC [a5, a6]],
        ALL_TAC] THEN
      REWRITE_TAC [← GSYM REAL_POW_MUL, ← GSYM REAL_POW_POW] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC [← GSYM REAL_OF_NUM_MUL] THEN
      SUBST1_TAC r7 THEN
      REWRITE_TAC [real_div, REAL_INV_MUL] THEN
      REWRITE_TAC [r8] THEN
      REWRITE_TAC [← GSYM real_div, AGM_2] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
      REWRITE_TAC [REAL_POS] THEN MATCH_MP_TAC SUM_POS_LE THEN
      REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      POP_ASSUM_LIST (MP_TAC o end_itlist CONJ) THEN ARITH_TAC,
      X_GEN_TAC (← q "n:num") THEN DISCH_TAC THEN X_GEN_TAC (← q r"a:num->real") THEN
      STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC
       (← q r"\i. if i <= n then a(i) else sum(1..n) a / &n")) THEN
      REWRITE_TAC [a9] THEN ANTS_TAC THENL
       [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC [REAL_POS] THEN
        ASM_SIMP_TAC [SUM_POS_LE, FINITE_NUMSEG, IN_NUMSEG],
        ALL_TAC] THEN
      ABBREV_TAC (← q r"A = sum(1..n) a / &n") THEN
      SIMP_TAC [← GSYM ADD1, PRODUCT_CLAUSES_NUMSEG, SUM_CLAUSES_NUMSEG] THEN
      SIMP_TAC [a10] THEN
      REWRITE_TAC [← GSYM REAL_OF_NUM_SUC] THEN EXPAND_TAC "A" THEN
      SIMP_TAC [REAL_OF_NUM_LE, asm1, f11] THEN
      ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN ASM_REWRITE_TAC [real_pow] THEN
      ASM_CASES_TAC (← q r"&0 < A") THEN ASM_SIMP_TAC [REAL_LE_LMUL_EQ] THEN
      SUBGOAL_THEN (← q r"A = &0") MP_TAC THENL
       [ASM_REWRITE_TAC [← GSYM REAL_LE_ANTISYM, ← GSYM REAL_NOT_LT] THEN
        REWRITE_TAC [REAL_NOT_LT] THEN EXPAND_TAC "A" THEN
        MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC [REAL_POS] THEN
        ASM_SIMP_TAC [SUM_POS_LE, FINITE_NUMSEG, IN_NUMSEG],
        ALL_TAC] THEN
      EXPAND_TAC "A" THEN
      REWRITE_TAC [real_div, REAL_ENTIRE, REAL_INV_EQ_0, REAL_OF_NUM_EQ] THEN
      ASM_SIMP_TAC [a12] THEN DISCH_TAC THEN
      DISCH_THEN (K ALL_TAC) THEN
      MP_TAC (← ISPECL [← q r"a:num->real", ← q "1", ← q "n:num"] SUM_POS_EQ_0_NUMSEG) THEN
      ASM_SIMP_TAC [] THEN DISCH_THEN (MP_TAC o SPEC (← q "n:num")) THEN
      ASM_REWRITE_TAC [LE_REFL] THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [LE_EXISTS]) THEN
      REWRITE_TAC [a13] THEN
      DISCH_THEN (CHOOSE_THEN SUBST_ALL_TAC) THEN
      ASM_REWRITE_TAC [real_pow, REAL_MUL_LZERO, PRODUCT_CLAUSES_NUMSEG] THEN
      REWRITE_TAC [a14, REAL_MUL_RZERO, REAL_LE_REFL]]))

  -- @@RETURN BEGIN
  return { FORALL_2, NUMSEG_2, AGM_2, SUM_SPLIT_2, PRODUCT_SPLIT_2, CAUCHY_INDUCT, AGM }
  -- @@RETURN END

end HolLibrary.Agm
