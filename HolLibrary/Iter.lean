/- ========================================================================= -/
/- Iterated application of a function, ITER n f x = f^n(x).                   -/
/- ========================================================================= -/
/- File: HolLibrary/Iter.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/iter.ml`, by hand, in file order, in
  the style of HolLibrary/Products.lean (see there and HolMath/Base.lean for
  the conventions).  iter.ml has no `needs`: it runs on the core library.
  The whole file is one bundle (a `structure`) built by a `setup` function;
  SessionLibrary/Iter.lean builds it and exports every name under its HOL
  Light name.

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, NUMBER_RULE) they are bound first, in
  OCaml's order.
-/

import HolMath

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolLibrary.Iter

/- ------------------------------------------------------------------------- -/
/- What iter.ml uses from the core library (supplied by Session).            -/
/- ------------------------------------------------------------------------- -/

/-- Theorems iter.ml uses from the core library. -/
structure CoreThms1 where
  (ADD ADD_AC ADD_SYM CARD_IMAGE_EQ_INJ CARD_NUMSEG CARD_SUBSET DIVIDES_LE
   FINITE_NUMSEG FUN_EQ_THM IMP_CONJ_ALT IN_NUMSEG I_THM LEFT_IMP_EXISTS_THM
   LE_1 LE_REFL MONO_EXISTS MULT NOT_FORALL_THM NOT_IMP NOT_LT
   RIGHT_FORALL_IMP_THM SUB_0 SUB_REFL WLOG_LT num_WF num_WOP o_THM : thm)
  deriving Inhabited

/-- What iter.ml uses from Session besides theorems. -/
structure IterDeps where
  -- definitions and the number conversion
  define : String → ExceptT String IO thm
  num_CONV : ioconv
  -- decision procedures and tactics
  ARITH_RULE : term → ExceptT String IO thm
  ASM_ARITH_TAC : tactic
  ASM_MESON_TAC : List thm → tactic
  ASM_SIMP_TAC : List thm → tactic
  INDUCT_TAC : tactic
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  NUMBER_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  core1 : CoreThms1

/- ------------------------------------------------------------------------- -/
/- The whole file is one bundle.  (iter.ml 1-215)                            -/
/- ------------------------------------------------------------------------- -/

structure Iter where
  -- @@FIELDS
  ITER : thm
  ITER_POINTLESS : thm
  ITER_ALT : thm
  ITER_ALT_POINTLESS : thm
  ITER_1 : thm
  ITER_ADD : thm
  ITER_ADD_POINTLESS : thm
  ITER_MUL : thm
  ITER_FIXPOINT : thm
  ORDER_EXISTENCE_GEN : thm
  ORDER_EXISTENCE_ITER : thm
  ORDER_EXISTENCE_CARD : thm
  ORDER_EXISTENCE_FINITE : thm
  deriving Inhabited

@[nospecialize]
def setupIter [HolBase] (D : IterDeps) :
    ExceptT String IO Iter := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, ASM_SIMP_TAC, INDUCT_TAC, MESON,
        MESON_TAC, NUMBER_RULE, SET_TAC, define, num_CONV, .. } := D
  let { ADD, ADD_AC, ADD_SYM, CARD_IMAGE_EQ_INJ, CARD_NUMSEG, CARD_SUBSET, DIVIDES_LE,
        FINITE_NUMSEG, FUN_EQ_THM, IMP_CONJ_ALT, IN_NUMSEG, I_THM, LEFT_IMP_EXISTS_THM,
        LE_1, LE_REFL, MONO_EXISTS, MULT, NOT_FORALL_THM, NOT_IMP, NOT_LT,
        RIGHT_FORALL_IMP_THM, SUB_0, SUB_REFL, WLOG_LT, num_WF, num_WOP, o_THM, .. } := D.core1
  -- @@SCOPE END

  let ITER ← define
   r"(!f. ITER 0 f x = x) /\
    (!f n. ITER (SUC n) f x = f (ITER n f x))"

  let ITER_POINTLESS ← prove
   r"(!f. ITER 0 f = I) /\
     (!f n. ITER (SUC n) f = f o ITER n f)"
   (REWRITE_TAC [FUN_EQ_THM, I_THM, o_THM, ITER])

  let ITER_ALT ← prove
   r"(!f x. ITER 0 f x = x) /\
     (!f n x. ITER (SUC n) f x = ITER n f (f x))"
   (REWRITE_TAC [ITER] THEN GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [ITER])

  let ITER_ALT_POINTLESS ← prove
   r"(!f. ITER 0 f = I) /\
     (!f n. ITER (SUC n) f = ITER n f o f)"
   (REWRITE_TAC [FUN_EQ_THM, I_THM, o_THM, ITER_ALT])

  let ITER_1 ← prove
   r"!f x. ITER 1 f x = f x"
   (REWRITE_TAC [← ExceptT.mk (num_CONV (← q "1")), ITER])

  let ITER_ADD ← prove
   r"!f n m x. ITER n f (ITER m f x) = ITER (n + m) f x"
   (GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ITER, ADD])

  let ITER_ADD_POINTLESS ← prove
   r"!m n. ITER (m + n) f = ITER m f o ITER n f"
   (REWRITE_TAC [FUN_EQ_THM, o_THM, ITER_ADD])

  let ITER_MUL ← prove
   r"!f n m x. ITER n (ITER m f) x = ITER (n * m) f x"
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [ITER, MULT, ITER_ADD, ADD_AC])

  let ITER_FIXPOINT ← prove
   r"!f n x. f x = x ==> ITER n f x = x"
   (GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC [ITER_ALT])

  /- --------------------------------------------------------------------- -/
  /- Existence of "order" or "characteristic" in a general setting.        -/
  /- --------------------------------------------------------------------- -/

  let ORDER_EXISTENCE_GEN ← prove
   r"!P f:num->A.
          P(f 0) /\ (!m n. P(f m) /\ ~(m = 0) ==> (P(f(m + n)) <=> P(f n)))
          ==> ?d. !n. P(f n) <=> d divides n"
   (← do
    let n4 ← NUMBER_RULE (← q r"(d:num) divides m + d <=> d divides m")
    let n3 ← NUMBER_RULE (← q r"n divides 0")
    let n2 ← NUMBER_RULE (← q r"0 divides n <=> n = 0")
    pure (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"!n. ~(n = 0) ==> ~P(f n:A)") THENL
     [EXISTS_TAC (← q "0") THEN REWRITE_TAC [n2] THEN
      ASM_MESON_TAC [],
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM])] THEN
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC (← q "d:num") THEN REWRITE_TAC [NOT_IMP] THEN
    REWRITE_TAC [← GSYM IMP_CONJ_ALT] THEN STRIP_TAC THEN
    MATCH_MP_TAC num_WF THEN X_GEN_TAC (← q "n:num") THEN DISCH_TAC THEN
    ASM_CASES_TAC (← q "n = 0") THENL
     [ASM_MESON_TAC [n3], ALL_TAC] THEN
    ASM_CASES_TAC (← q "d <= n:num") THENL
     [ALL_TAC, ASM_MESON_TAC [NOT_LT, DIVIDES_LE]] THEN
    SUBGOAL_THEN (← q "n:num = (n - d) + d") SUBST1_TAC THENL
     [ASM_ARITH_TAC, ABBREV_TAC (← q "m:num = n - d")] THEN
    REWRITE_TAC [n4] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q "m:num")) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC, ASM_MESON_TAC [ADD_SYM]]))

  let ORDER_EXISTENCE_ITER ← prove
   r"!R f z:A.
          R z z /\
          (!x y. R x y ==> R y x) /\
          (!x y z. R x y /\ R y z ==> R x z) /\
          (!x y. R x y ==> R (f x) (f y))
          ==> ?d. !n. R (ITER n f z) z <=> d divides n"
   (← do
    let m1 ← MESON []
      (← q r"!a b:num->A. (!x y. R x y ==> R y x) /\
            (!x y z. R x y /\ R y z ==> R x z) /\
            (!n. R (a n) (b n))
            ==> (!n. R (a n) z <=> R (b n) z)")
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"\x. (R:A->A->bool) x z",
                   ← q r"\n. ITER n f (z:A)"] ORDER_EXISTENCE_GEN) THEN
    ASM_REWRITE_TAC [ITER] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN X_GEN_TAC (← q "m:num") THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN REWRITE_TAC [← GSYM ITER_ADD] THEN
    MP_TAC m1 THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC [ITER] THEN
    ASM_MESON_TAC []))

  let ORDER_EXISTENCE_CARD ← prove
   r"!R f z:A k.
       FINITE { R(ITER n f z) | n IN (:num)} /\
       CARD { R(ITER n f z) | n IN (:num)} <= k /\
       R z z /\
       (!x y. R x y ==> R y x) /\
       (!x y z. R x y /\ R y z ==> R x z) /\
       (!x y. R (f x) (f y) <=> R x y)
       ==> ?d. 0 < d /\ d <= k /\ !n. R (ITER n f z) z <=> d divides n"
   (← do
    let n2 ← NUMBER_RULE (← q r"!n. 0 divides n <=> n = 0")
    let t1 ← TAUT (← q r"~p /\ (~q ==> r) ==> (p <=> q) ==> r")
    let a1 ← ARITH_RULE
      (← q r"c <= k ==> s <= c ==> ~(s = k + 1)")
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"?m. 0 < m /\ m <= k /\ (R:A->A->bool) (ITER m f z) z")
    STRIP_ASSUME_TAC THENL
      [MP_TAC (← ISPECL [← q r"\n. (R:A->A->bool) (ITER n f z)", ← q r"0..k"]
        CARD_IMAGE_EQ_INJ) THEN
       REWRITE_TAC [FINITE_NUMSEG, CARD_NUMSEG, SUB_0] THEN
       MATCH_MP_TAC t1 THEN
       CONJ_TAC THENL
        [FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP a1) THEN
         MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC [] THEN ASM SET_TAC [],
         REWRITE_TAC [NOT_FORALL_THM, NOT_IMP, LEFT_IMP_EXISTS_THM] THEN
         MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC [] THEN
         CONJ_TAC THENL [MESON_TAC [], ALL_TAC] THEN
         MAP_EVERY X_GEN_TAC [← q "p:num", ← q "q:num"] THEN
         REWRITE_TAC [IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
         EXISTS_TAC (← q "q - p:num") THEN
         REPEAT (CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC]) THEN
         SUBGOAL_THEN
          (← q r"!d. d <= p
               ==> (R:A->A->bool) (ITER (p - d) f z) (ITER (q - d) f z)")
         MP_TAC THENL
          [INDUCT_TAC THEN ASM_REWRITE_TAC [SUB_0] THENL
            [SPEC_TAC (← q "q:num", ← q "q:num") THEN INDUCT_TAC THEN
             ASM_REWRITE_TAC [ITER],
             DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o check (is_imp ∘ concl)) THEN
             ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
             SUBGOAL_THEN (← q r"q - d = SUC(q - SUC d) /\ p - d = SUC(p - SUC d)")
              (fun th => REWRITE_TAC [th]) THENL [ASM_ARITH_TAC, ALL_TAC] THEN
             ASM_REWRITE_TAC [ITER]],
           DISCH_THEN (MP_TAC o SPEC (← q "p:num")) THEN
           REWRITE_TAC [LE_REFL, SUB_REFL, ITER] THEN ASM_MESON_TAC []]],
       MP_TAC (← ISPECL [← q r"R:A->A->bool", ← q r"f:A->A", ← q r"z:A"] ORDER_EXISTENCE_ITER) THEN
       ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN
       X_GEN_TAC (← q "d:num") THEN ASM_CASES_TAC (← q "d = 0") THEN ASM_SIMP_TAC [] THEN
       DISCH_THEN (MP_TAC o SPEC (← q "m:num")) THEN
       ASM_SIMP_TAC [LE_1, n2] THEN
       DISCH_THEN (MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC]))

  let ORDER_EXISTENCE_FINITE ← prove
   r"!R f z:A.
       FINITE { R(ITER n f z) | n IN (:num)} /\
       R z z /\
       (!x y. R x y ==> R y x) /\
       (!x y z. R x y /\ R y z ==> R x z) /\
       (!x y. R (f x) (f y) <=> R x y)
       ==> ?d. 0 < d /\ !n. R (ITER n f z) z <=> d divides n"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"R:A->A->bool", ← q r"f:A->A", ← q r"z:A",
     ← q r"CARD {(R:A->A->bool)(ITER n f z) | n IN (:num)}"]
     ORDER_EXISTENCE_CARD) THEN ASM_REWRITE_TAC [LE_REFL] THEN MESON_TAC [])

  -- @@RETURN BEGIN
  return { ITER, ITER_POINTLESS, ITER_ALT, ITER_ALT_POINTLESS, ITER_1, ITER_ADD,
           ITER_ADD_POINTLESS, ITER_MUL, ITER_FIXPOINT, ORDER_EXISTENCE_GEN,
           ORDER_EXISTENCE_ITER, ORDER_EXISTENCE_CARD, ORDER_EXISTENCE_FINITE }
  -- @@RETURN END

end HolLibrary.Iter
