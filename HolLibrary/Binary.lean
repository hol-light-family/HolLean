/- ========================================================================= -/
/- Binary expansions as a bijection between numbers and finite sets.         -/
/- ========================================================================= -/
/- File: HolLibrary/Binary.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/binary.ml`, by hand, in file order,
  in the style of HolLibrary/Products.lean and HolLibrary/Card.lean (see
  there and HolMath/Base.lean for the conventions).  binary.ml has no
  `needs`: it runs on the core library.  The whole file is one bundle (a
  `structure`) built by a `setup` function; SessionLibrary/Binary.lean
  builds it and exports every name under its HOL Light name.

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, SET_RULE) they are bound first, in
  OCaml's order.
-/

import HolMath

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

set_option maxRecDepth 8000

namespace HolLibrary.Binary

/- ------------------------------------------------------------------------- -/
/- What binary.ml uses from the core library (supplied by Session).          -/
/- ------------------------------------------------------------------------- -/

/-- Theorems binary.ml uses from the core library. -/
structure CoreThms1 where
  (ADD1 ADD_ASSOC ADD_SYM ARITH ARITH_EQ BINARY_INDUCT COND_RAND CONJ_ACI
   DIV_0 DIV_1 DIV_DIV DIV_LT DIV_UNIQ EQ_ADD_RCANCEL EQ_MULT_LCANCEL EQ_TRANS
   EVEN_ADD EVEN_EXP EXP EXP_ADD EXP_EQ_0 EXTENSION FINITE_DELETE FINITE_IMAGE
   FINITE_INDUCT_STRONG FINITE_INSERT FINITE_NUMSEG FINITE_SUBSET IMP_CONJ
   IN_DELETE IN_ELIM_THM IN_IMAGE IN_INSERT IN_INTER IN_NUMSEG IN_UNION
   LEFT_ADD_DISTRIB LET_TRANS LE_0 LE_LT LT LTE_TRANS LT_EXP LT_IMP_LE
   LT_POW2_REFL LT_REFL MEMBER_NOT_EMPTY MULT_CLAUSES MULT_EQ_0 MULT_SYM
   NEUTRAL_ADD NOT_EXISTS_THM NOT_IN_EMPTY NOT_LE NOT_LT NOT_ODD NOT_SUC
   NSUM_CLAUSES NSUM_EQ NSUM_IMAGE NSUM_LMUL NSUM_SUBSET NSUM_SUPPORT
   NSUM_UNION_EQ ODD ODD_ADD ODD_MULT RIGHT_FORALL_IMP_THM SUBSET SUB_EQ_0
   SUB_REFL SUC_INJ UNWIND_THM1 num_INDUCTION o_DEF support : thm)
  deriving Inhabited

/-- What binary.ml uses from Session besides theorems. -/
structure BinaryDeps where
  -- definitions and parser state
  new_definition : String → ExceptT String IO thm
  -- decision procedures and tactics
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_MESON_TAC : List thm → tactic
  INDUCT_TAC : tactic
  MESON_TAC : List thm → tactic
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  core1 : CoreThms1

/- ------------------------------------------------------------------------- -/
/- The whole file is one bundle.  (binary.ml 1-128)                          -/
/- ------------------------------------------------------------------------- -/

structure Binary where
  -- @@FIELDS
  BOUNDED_FINITE : thm
  EVEN_NSUM : thm
  bitset : thm
  binarysum : thm
  BITSET_BOUND_LEMMA : thm
  BITSET_BOUND_WEAK : thm
  FINITE_BITSET : thm
  BITSET_0 : thm
  BITSET_STEP : thm
  BINARYSUM_BITSET : thm
  BITSET_EQ : thm
  BITSET_EQ_EMPTY : thm
  BINARYSUM_BOUND_LEMMA : thm
  BINARYSUM_DIV_DIVISIBLE : thm
  BINARYSUM_DIV : thm
  BITSET_BINARYSUM : thm
  BINARYSUM_BOUND : thm
  BITSET_BOUND : thm
  BITSET_BOUND_EQ : thm
  BINARYSUM_BOUND_EQ : thm
  deriving Inhabited

@[nospecialize]
def setupBinary [HolBase] (D : BinaryDeps) :
    ExceptT String IO Binary := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, SET_RULE, SET_TAC,
        new_definition, .. } := D
  let { ADD1, ADD_ASSOC, ADD_SYM, ARITH, ARITH_EQ, BINARY_INDUCT, COND_RAND, CONJ_ACI,
        DIV_0, DIV_1, DIV_DIV, DIV_LT, DIV_UNIQ, EQ_ADD_RCANCEL, EQ_MULT_LCANCEL,
        EQ_TRANS, EVEN_ADD, EVEN_EXP, EXP, EXP_ADD, EXP_EQ_0, EXTENSION, FINITE_DELETE,
        FINITE_IMAGE, FINITE_INDUCT_STRONG, FINITE_INSERT, FINITE_NUMSEG,
        FINITE_SUBSET, IMP_CONJ, IN_DELETE, IN_ELIM_THM, IN_IMAGE, IN_INSERT, IN_INTER,
        IN_NUMSEG, IN_UNION, LEFT_ADD_DISTRIB, LET_TRANS, LE_0, LE_LT, LT, LTE_TRANS,
        LT_EXP, LT_IMP_LE, LT_POW2_REFL, LT_REFL, MEMBER_NOT_EMPTY, MULT_CLAUSES,
        MULT_EQ_0, MULT_SYM, NEUTRAL_ADD, NOT_EXISTS_THM, NOT_IN_EMPTY, NOT_LE, NOT_LT,
        NOT_ODD, NOT_SUC, NSUM_CLAUSES, NSUM_EQ, NSUM_IMAGE, NSUM_LMUL, NSUM_SUBSET,
        NSUM_SUPPORT, NSUM_UNION_EQ, ODD, ODD_ADD, ODD_MULT, RIGHT_FORALL_IMP_THM,
        SUBSET, SUB_EQ_0, SUB_REFL, SUC_INJ, UNWIND_THM1, num_INDUCTION, o_DEF,
        support, .. } := D.core1
  -- @@SCOPE END

  let BOUNDED_FINITE ← prove
   r"!s. (!x:num. x IN s ==> x <= n) ==> FINITE s"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q "0..n") THEN
    ASM_SIMP_TAC [SUBSET, IN_NUMSEG, FINITE_NUMSEG, LE_0])

  let EVEN_NSUM ← prove
   r"!s. FINITE s /\ (!i. i IN s ==> EVEN(f i)) ==> EVEN(nsum s f)"
   (REWRITE_TAC [IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC [NSUM_CLAUSES, ARITH, EVEN_ADD, IN_INSERT])

  let bitset ← new_definition r"bitset n = {i | ODD(n DIV (2 EXP i))}"

  let binarysum ← new_definition r"binarysum s = nsum s (\i. 2 EXP i)"

  let BITSET_BOUND_LEMMA ← prove
   r"!n i. i IN (bitset n) ==> 2 EXP i <= n"
   (REWRITE_TAC [bitset, IN_ELIM_THM] THEN MESON_TAC [DIV_LT, ODD, NOT_LE])

  let BITSET_BOUND_WEAK ← prove
   r"!n i. i IN (bitset n) ==> i < n"
   (MESON_TAC [BITSET_BOUND_LEMMA, LT_POW2_REFL, LTE_TRANS])

  let FINITE_BITSET ← prove
   r"!n. FINITE(bitset n)"
   (GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q "0..n") THEN
    REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG, LE_0, SUBSET] THEN
    MESON_TAC [LT_IMP_LE, BITSET_BOUND_WEAK])

  let BITSET_0 ← prove
   r"bitset 0 = {}"
   (REWRITE_TAC [bitset, EXTENSION, NOT_IN_EMPTY, IN_ELIM_THM] THEN
    SIMP_TAC [DIV_0, EXP_EQ_0, ARITH])

  let BITSET_STEP ← prove
   r"(!n. bitset(2 * n) = IMAGE SUC (bitset n)) /\
    (!n. bitset(2 * n + 1) = 0 INSERT (IMAGE SUC (bitset n)))"
   (← do
    let a0 ← ARITH_RULE (← q r"(2 * n + 1) DIV 2 = n /\ (2 * n) DIV 2 = n")
    let t ← TAUT (← q r"a /\ (a ==> b) ==> a /\ b")
    pure (MATCH_MP_TAC t THEN CONJ_TAC THENL
     [ALL_TAC, DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← GSYM th]))] THEN
     REWRITE_TAC [bitset, EXTENSION, IN_INSERT, IN_ELIM_THM, IN_IMAGE] THEN
     GEN_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
     REWRITE_TAC [ARITH, ODD_MULT, DIV_1, NOT_SUC, ODD_ADD] THEN
     GEN_TAC THEN DISCH_THEN (K ALL_TAC) THEN
     REWRITE_TAC [SUC_INJ, UNWIND_THM1, EXP] THEN
     SIMP_TAC [← GSYM DIV_DIV, MULT_EQ_0, EXP_EQ_0, ARITH] THEN
     REWRITE_TAC [a0]))

  let BINARYSUM_BITSET ← prove
   r"!n. binarysum (bitset n) = n"
   (← do
    let a1 ← ARITH_RULE (← q "m < SUC(2 * m)")
    let a0 ← ARITH_RULE (← q r"~(2 * m = 0) ==> m < 2 * m")
    let ar ← ARITH_RULE (← q r"~(0 = x + 1)")
    pure (CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN REWRITE_TAC [binarysum] THEN
     MATCH_MP_TAC BINARY_INDUCT THEN REWRITE_TAC [BITSET_0, NSUM_CLAUSES] THEN
     SIMP_TAC [BITSET_STEP, NSUM_IMAGE, SUC_INJ, ADD1, FINITE_BITSET, ARITH,
     NSUM_CLAUSES, FINITE_IMAGE, IN_IMAGE, ar] THEN
     REWRITE_TAC [o_DEF, EXP, NSUM_LMUL] THEN
     ASM_MESON_TAC [ADD_SYM, a0, a1]))

  let BITSET_EQ ← prove
   r"!m n. bitset m = bitset n <=> m = n"
   (MESON_TAC [BINARYSUM_BITSET])

  let BITSET_EQ_EMPTY ← prove
   r"!n. bitset n = {} <=> n = 0"
   (MESON_TAC [BITSET_EQ, BITSET_0])

  let BINARYSUM_BOUND_LEMMA ← prove
   r"!k s. (!i. i IN s ==> i < k) ==> nsum s (\i. 2 EXP i) < 2 EXP k"
   (← do
    let a0 ← ARITH_RULE (← q r"a + b < 2 * a <=> b < a ")
    pure (INDUCT_TAC THEN
     SIMP_TAC [LT, ← GSYM NOT_EXISTS_THM, MEMBER_NOT_EMPTY, NSUM_CLAUSES, ARITH] THEN
     REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"FINITE(s:num->bool)") ASSUME_TAC THENL
      [ASM_MESON_TAC [BOUNDED_FINITE, LE_LT], ALL_TAC] THEN
     MATCH_MP_TAC LET_TRANS THEN
     EXISTS_TAC (← q r"nsum (k INSERT (s DELETE k)) (\i. 2 EXP i)") THEN CONJ_TAC THENL
      [MATCH_MP_TAC NSUM_SUBSET THEN SIMP_TAC [FINITE_INSERT, FINITE_DELETE],
       ASM_SIMP_TAC [NSUM_CLAUSES, FINITE_DELETE, IN_DELETE] THEN
       REWRITE_TAC [EXP, a0] THEN
       FIRST_X_ASSUM MATCH_MP_TAC] THEN
     ASM SET_TAC []))

  let BINARYSUM_DIV_DIVISIBLE ← prove
   r"!s k. FINITE s /\ (!i. i IN s ==> k <= i)
          ==> nsum s (\i. 2 EXP i) = 2 EXP k * nsum s (\i. 2 EXP (i - k))"
   (← do
    let a0 ← ARITH_RULE (← q r"i <= k:num ==> i + k - i = k")
    pure (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
     MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
     SIMP_TAC [NSUM_CLAUSES, DIV_0, EXP_EQ_0, ARITH_EQ, MULT_CLAUSES] THEN
     SIMP_TAC [IN_INSERT, ADD_ASSOC, EQ_ADD_RCANCEL, LEFT_ADD_DISTRIB] THEN
     SIMP_TAC [← GSYM EXP_ADD, a0]))

  let BINARYSUM_DIV ← prove
   r"!k s. FINITE s
          ==> (nsum s (\j. 2 EXP j)) DIV (2 EXP k) =
              nsum s (\j. if j < k then 0 else 2 EXP (j - k))"
   (← do
    let a2 ← ARITH_RULE (← q r"k <= j:num ==> ~(j < k)")
    let a1 ← ARITH_RULE (← q r"(if p then 0 else q) = 0 <=> ~p ==> q = 0")
    let a0 ← ARITH_RULE (← q r"a + x:num = y + a <=> x = y")
    pure (REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
     EXISTS_TAC (← q r"(nsum {i | i < k /\ i IN s} (\j. 2 EXP j) +
                 nsum {i | k <= i /\ i IN s} (\j. 2 EXP j)) DIV (2 EXP k)") THEN
     CONJ_TAC THENL
      [AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
       MATCH_MP_TAC NSUM_UNION_EQ THEN
       ASM_SIMP_TAC [EXTENSION, IN_INTER, IN_UNION, IN_ELIM_THM, NOT_IN_EMPTY] THEN
       CONJ_TAC THEN X_GEN_TAC (← q "i:num") THEN
       ASM_CASES_TAC (← q r"(i:num) IN s") THEN ASM_REWRITE_TAC [] THEN ARITH_TAC,
       ALL_TAC] THEN
     MATCH_MP_TAC DIV_UNIQ THEN
     EXISTS_TAC (← q r"nsum {i | i < k /\ i IN s} (\j. 2 EXP j)") THEN
     SIMP_TAC [BINARYSUM_BOUND_LEMMA, IN_ELIM_THM] THEN
     REWRITE_TAC [a0] THEN
     MATCH_MP_TAC EQ_TRANS THEN
     EXISTS_TAC (← q r"2 EXP k * nsum {i | k <= i /\ i IN s} (\i. 2 EXP (i - k))") THEN
     CONJ_TAC THENL
      [MATCH_MP_TAC BINARYSUM_DIV_DIVISIBLE THEN SIMP_TAC [IN_ELIM_THM] THEN
       MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"s:num->bool") THEN
       ASM_SIMP_TAC [SUBSET, IN_ELIM_THM],
       ALL_TAC] THEN
     GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
     REWRITE_TAC [EQ_MULT_LCANCEL, EXP_EQ_0, ARITH_EQ] THEN
     ONCE_REWRITE_TAC [← GSYM NSUM_SUPPORT] THEN
     REWRITE_TAC [support, NEUTRAL_ADD, EXP_EQ_0, ARITH, IN_ELIM_THM] THEN
     REWRITE_TAC [a1] THEN
     REWRITE_TAC [EXP_EQ_0, ARITH, NOT_LT, CONJ_ACI] THEN
     MATCH_MP_TAC NSUM_EQ THEN
     SIMP_TAC [IN_ELIM_THM, a2]))

  let BITSET_BINARYSUM ← prove
   r"!s. FINITE s ==> bitset (binarysum s) = s"
   (← do
    let sr ← SET_RULE (← q r"i IN s ==> s = i INSERT (s DELETE i)")
    pure (GEN_TAC THEN DISCH_TAC THEN
     REWRITE_TAC [bitset, binarysum, EXTENSION, IN_ELIM_THM] THEN
     X_GEN_TAC (← q "i:num") THEN ASM_SIMP_TAC [BINARYSUM_DIV] THEN
     ASM_CASES_TAC (← q r"(i:num) IN s") THEN ASM_REWRITE_TAC [] THENL
      [FIRST_ASSUM (SUBST1_TAC o MATCH_MP sr) THEN
       ASM_SIMP_TAC [NSUM_CLAUSES, FINITE_DELETE, IN_DELETE] THEN
       REWRITE_TAC [LT_REFL, SUB_REFL, ARITH, ODD_ADD],
       ALL_TAC] THEN
     REWRITE_TAC [NOT_ODD] THEN MATCH_MP_TAC EVEN_NSUM THEN
     ASM_REWRITE_TAC [FINITE_DELETE, IN_DELETE] THEN
     ONCE_REWRITE_TAC [COND_RAND] THEN SIMP_TAC [ARITH, EVEN_EXP, SUB_EQ_0] THEN
     REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC [LE_LT]))

  let BINARYSUM_BOUND ← prove
   r"!k s. (!i. i IN s ==> i < k) ==> binarysum s < 2 EXP k"
   (REWRITE_TAC [BINARYSUM_BOUND_LEMMA, binarysum])

  let BITSET_BOUND ← prove
   r"!n i k. n < 2 EXP k /\ i IN bitset n ==> i < k"
   (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q "2 EXP i < 2 EXP k") MP_TAC THENL
    [ASM_MESON_TAC [BITSET_BOUND_LEMMA, LET_TRANS],
     REWRITE_TAC [LT_EXP, ARITH]])

  let BITSET_BOUND_EQ ← prove
   r"!n k. n < 2 EXP k <=> (!i. i IN bitset n ==> i < k)"
   (MESON_TAC [BINARYSUM_BOUND, BITSET_BOUND, BINARYSUM_BITSET])

  let BINARYSUM_BOUND_EQ ← prove
   r"!s k. FINITE s ==> (binarysum s < 2 EXP k <=> (!i. i IN s ==> i < k))"
   (MESON_TAC [BINARYSUM_BOUND, BITSET_BOUND, BITSET_BINARYSUM])

  -- @@RETURN BEGIN
  return { BOUNDED_FINITE, EVEN_NSUM, bitset, binarysum, BITSET_BOUND_LEMMA,
           BITSET_BOUND_WEAK, FINITE_BITSET, BITSET_0, BITSET_STEP, BINARYSUM_BITSET,
           BITSET_EQ, BITSET_EQ_EMPTY, BINARYSUM_BOUND_LEMMA, BINARYSUM_DIV_DIVISIBLE,
           BINARYSUM_DIV, BITSET_BINARYSUM, BINARYSUM_BOUND, BITSET_BOUND,
           BITSET_BOUND_EQ, BINARYSUM_BOUND_EQ }
  -- @@RETURN END

end HolLibrary.Binary
