/- File: Hol100/Birthday.lean
Translation of HOL Light's 100/birthday.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
namespace Hol100.Birthday

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def sr (tm : term) : ExceptT String IO thm := ExceptT.mk (SET_RULE tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)

/- ========================================================================= -/
/- Birthday problem.                                                         -/
/- ========================================================================= -/

#eval phrase 1
#eval Session.prioritize_num

/- ------------------------------------------------------------------------- -/
/- Restricted function space.                                                -/
/- ------------------------------------------------------------------------- -/

#eval phrase 2
-- parse_as_infix("-->",(13,"right"));;
#eval (parse_as_infix ("-->", (13, "right")) : IO Unit)

#eval phrase 3
def funspace : thm := keep "funspace" fun _ => new_definition
 [[(s --> t) = {f:A->B | (!x. x IN s ==> f(x) IN t) /\
                        (!x. ~(x IN s) ==> f(x) = @y. T)}]]
#eval funspace

/- ------------------------------------------------------------------------- -/
/- Sizes.                                                                    -/
/- ------------------------------------------------------------------------- -/

#eval phrase 4
def FUNSPACE_EMPTY : thm := keep "FUNSPACE_EMPTY" fun _ => (do
  prove ([[({} --> t) = {(\x. @y. T)}]])
   (REWRITE_TAC [EXTENSION, IN_SING, funspace, IN_ELIM_THM, NOT_IN_EMPTY] THEN
    REWRITE_TAC [FUN_EQ_THM])
  : ExceptT String IO thm).run
#eval FUNSPACE_EMPTY

#eval phrase 5
def HAS_SIZE_FUNSPACE : thm := keep "HAS_SIZE_FUNSPACE" fun _ => (do
  let h2 ← tt (← ExceptT.mk [[(a /\ b) /\ d <=> d /\ a /\ b]])
  let h1 ← tt (← ExceptT.mk [[(a /\ b /\ c) /\ d <=> d /\ a /\ b /\ c]])
  prove ([[!s:A->bool t:B->bool m n.
        s HAS_SIZE m /\ t HAS_SIZE n ==> (s --> t) HAS_SIZE (n EXP m)]])
   (REWRITE_TAC [HAS_SIZE, (← HolLight.GSYM CONJ_ASSOC)] THEN
    ONCE_REWRITE_TAC [IMP_CONJ] THEN
    REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
     [SIMP_TAC [CARD_CLAUSES, FINITE_RULES, FUNSPACE_EMPTY, NOT_IN_EMPTY] THEN
      REPEAT GEN_TAC THEN DISCH_THEN (STRIP_ASSUME_TAC o HolLight.GSYM) THEN
      ASM_REWRITE_TAC [EXP, ARITH],
      ALL_TAC] THEN
    REWRITE_TAC [(← HolLight.GSYM HAS_SIZE)] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[(x INSERT s) --> t =
        IMAGE (\(y:B,g) u:A. if u = x then y else g(u))
              {y,g | y IN t /\ g IN s --> t}]]) SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_IMAGE, funspace, IN_ELIM_THM] THEN
      ONCE_REWRITE_TAC [h1] THEN
      REWRITE_TAC [PAIR_EQ, EXISTS_PAIR_THM, (← HolLight.GSYM CONJ_ASSOC)] THEN
      REWRITE_TAC [RIGHT_EXISTS_AND_THM, UNWIND_THM1] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      X_GEN_TAC ([[f:A->B]]) THEN EQ_TAC THENL
       [STRIP_TAC THEN MAP_EVERY EXISTS_TAC [([[(f:A->B) x]]), ([[\u. if u = x then @y. T else (f:A->B) u]])] THEN
        REWRITE_TAC [FUN_EQ_THM] THEN ASM_MESON_TAC [IN_INSERT],
        REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
        MAP_EVERY X_GEN_TAC [([[y:B]]), ([[g:A->B]])] THEN
        STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
        ASM_MESON_TAC [IN_INSERT]],
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC [FORALL_PAIR_THM, IN_ELIM_THM] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      ONCE_REWRITE_TAC [h2] THEN
      REWRITE_TAC [PAIR_EQ, EXISTS_PAIR_THM, (← HolLight.GSYM CONJ_ASSOC)] THEN
      REWRITE_TAC [RIGHT_EXISTS_AND_THM, UNWIND_THM1] THEN
      REWRITE_TAC [FUN_EQ_THM, funspace, IN_ELIM_THM] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC [IN_INSERT], ALL_TAC] THEN
      X_GEN_TAC ([[u:A]]) THEN ASM_CASES_TAC ([[u:A = x]]) THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    FIRST_X_ASSUM (SUBST_ALL_TAC o HolLight.SYM) THEN ASM_SIMP_TAC [CARD_CLAUSES, EXP] THEN
    MATCH_MP_TAC HAS_SIZE_PRODUCT THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval HAS_SIZE_FUNSPACE

/- ------------------------------------------------------------------------- -/
/- The restriction to injective functions.                                   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 6
def FACT_DIVIDES : thm := keep "FACT_DIVIDES" fun _ => (do
  prove ([[!m n. m <= n ==> ?d. FACT(n) = d * FACT(m)]])
   (REWRITE_TAC [LE_EXISTS, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC ([[m:num]]) THEN ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    SIMP_TAC [LEFT_FORALL_IMP_THM, EXISTS_REFL] THEN
    INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES, FACT] THEN
    ASM_MESON_TAC [MULT_AC, MULT_CLAUSES])
  : ExceptT String IO thm).run
#eval FACT_DIVIDES

#eval phrase 7
def FACT_DIV_MULT : thm := keep "FACT_DIV_MULT" fun _ => (do
  prove ([[!m n. m <= n ==> FACT n = (FACT(n) DIV FACT(m)) * FACT(m)]])
   (REPEAT GEN_TAC THEN DISCH_THEN (STRIP_ASSUME_TAC o HolLight.MATCH_MP FACT_DIVIDES) THEN
    ASM_REWRITE_TAC [] THEN
    GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [MULT_SYM] THEN
    ASM_SIMP_TAC [DIV_MULT, (← HolLight.GSYM LT_NZ), FACT_LT])
  : ExceptT String IO thm).run
#eval FACT_DIV_MULT

#eval phrase 8
def HAS_SIZE_FUNSPACE_INJECTIVE : thm := keep "HAS_SIZE_FUNSPACE_INJECTIVE" fun _ => (do
  let h5 ← ar (← ExceptT.mk [[n - SUC(m) = n - 1 - m]])
  let h4 ← ar (← ExceptT.mk [[~(n = 0) ==> (n - 1 < m <=> n < SUC m)]])
  let h3 ← tt (← ExceptT.mk [[(a /\ b) /\ d <=> d /\ a /\ b]])
  let h2 ← tt (← ExceptT.mk [[(a /\ b /\ c) /\ d <=> d /\ a /\ b /\ c]])
  let h1 ← sr (← ExceptT.mk [[{x | x IN s} = s]])
  prove ([[!s:A->bool t:B->bool m n.
        s HAS_SIZE m /\ t HAS_SIZE n
        ==> {f | f IN (s --> t) /\
                 (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)}
            HAS_SIZE (if n < m then 0 else (FACT n) DIV (FACT(n - m)))]])
   (REWRITE_TAC [HAS_SIZE, (← HolLight.GSYM CONJ_ASSOC)] THEN
    ONCE_REWRITE_TAC [IMP_CONJ] THEN
    REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
     [SIMP_TAC [CARD_CLAUSES, FINITE_RULES, FUNSPACE_EMPTY, NOT_IN_EMPTY] THEN
      REPEAT GEN_TAC THEN DISCH_THEN (STRIP_ASSUME_TAC o HolLight.GSYM) THEN
      REWRITE_TAC [h1] THEN
      ASM_SIMP_TAC [FINITE_RULES, CARD_CLAUSES, FACT] THEN
      SIMP_TAC [NOT_IN_EMPTY, LT, SUB_0, DIV_REFL, (← HolLight.GSYM LT_NZ), FACT_LT] THEN
      REWRITE_TAC [ARITH],
      ALL_TAC] THEN
    REWRITE_TAC [(← HolLight.GSYM HAS_SIZE)] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[{f | f IN (x INSERT s) --> t /\
    (!u v. u IN (x INSERT s) /\ v IN (x INSERT s) /\ f u = f v ==> u = v)} =
        IMAGE (\(y:B,g) u:A. if u = x then y else g(u))
              {y,g | y IN t /\
                     g IN {f | f IN (s --> (t DELETE y)) /\
                               !u v. u IN s /\ v IN s /\ f u = f v ==> u = v}}]]) SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_IMAGE, funspace, IN_ELIM_THM] THEN
      ONCE_REWRITE_TAC [h2] THEN
      REWRITE_TAC [PAIR_EQ, EXISTS_PAIR_THM, (← HolLight.GSYM CONJ_ASSOC)] THEN
      REWRITE_TAC [RIGHT_EXISTS_AND_THM, UNWIND_THM1] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      X_GEN_TAC ([[f:A->B]]) THEN EQ_TAC THENL
       [REWRITE_TAC [IN_INSERT, IN_DELETE] THEN
        STRIP_TAC THEN MAP_EVERY EXISTS_TAC [([[(f:A->B) x]]), ([[\u. if u = x then @y. T else (f:A->B) u]])] THEN
        REWRITE_TAC [FUN_EQ_THM] THEN ASM_MESON_TAC [],
        REWRITE_TAC [IN_INSERT, IN_DELETE, LEFT_IMP_EXISTS_THM] THEN
        MAP_EVERY X_GEN_TAC [([[y:B]]), ([[g:A->B]])] THEN
        STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
        ASM_MESON_TAC []],
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC [FORALL_PAIR_THM, IN_ELIM_THM] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      ONCE_REWRITE_TAC [h3] THEN
      REWRITE_TAC [PAIR_EQ, EXISTS_PAIR_THM, (← HolLight.GSYM CONJ_ASSOC)] THEN
      REWRITE_TAC [RIGHT_EXISTS_AND_THM, UNWIND_THM1] THEN
      REWRITE_TAC [FUN_EQ_THM, funspace, IN_ELIM_THM, IN_INSERT, IN_DELETE] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC [IN_INSERT], ALL_TAC] THEN
      X_GEN_TAC ([[u:A]]) THEN ASM_CASES_TAC ([[u:A = x]]) THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    FIRST_X_ASSUM (SUBST_ALL_TAC o HolLight.SYM) THEN ASM_SIMP_TAC [CARD_CLAUSES, EXP] THEN
    SUBGOAL_THEN ([[(if n < SUC (CARD s) then 0 else FACT n DIV FACT (n - SUC (CARD s))) =
    n * (if (n - 1) < CARD(s:A->bool) then 0
         else FACT(n - 1) DIV FACT (n - 1 - CARD s))]]) SUBST1_TAC THENL
     [ASM_CASES_TAC ([[n = 0]]) THEN ASM_REWRITE_TAC [MULT_CLAUSES, LT_0] THEN
      ASM_SIMP_TAC [h4] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN
      REWRITE_TAC [h5] THEN
      UNDISCH_TAC ([[~(n = 0)]]) THEN SPEC_TAC (([[n:num]]), ([[n:num]])) THEN
      INDUCT_TAC THEN REWRITE_TAC [FACT, SUC_SUB1] THEN DISCH_TAC THEN
      MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC ([[0]]) THEN
      REWRITE_TAC [ADD_CLAUSES, FACT_LT, (← HolLight.GSYM MULT_ASSOC)] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC FACT_DIV_MULT THEN ARITH_TAC,
      MATCH_MP_TAC HAS_SIZE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC [] THEN
      X_GEN_TAC ([[y:B]]) THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [HAS_SIZE]) THEN
      ASM_SIMP_TAC [HAS_SIZE, FINITE_DELETE, CARD_DELETE]])
  : ExceptT String IO thm).run
#eval HAS_SIZE_FUNSPACE_INJECTIVE

/- ------------------------------------------------------------------------- -/
/- So the actual birthday result.                                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 9
def HAS_SIZE_DIFF : thm := keep "HAS_SIZE_DIFF" fun _ => (do
  let h2 ← sr (← ExceptT.mk [[s INTER (t DIFF s) = {}]])
  let h1 ← sr (← ExceptT.mk [[s SUBSET t ==> t = s UNION (t DIFF s)]])
  prove ([[!s t:A->bool m n.
        s SUBSET t /\ s HAS_SIZE m /\ t HAS_SIZE n
        ==> (t DIFF s) HAS_SIZE (n - m)]])
   (SIMP_TAC [HAS_SIZE, FINITE_DIFF] THEN
    REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN (SUBST_ALL_TAC o HolLight.SYM) THEN FIRST_X_ASSUM (SUBST_ALL_TAC o HolLight.SYM) THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP h1) THEN
    DISCH_THEN (fun th => GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.ONCE_DEPTH_CONV) [th]) THEN
    ASM_SIMP_TAC [CARD_UNION, FINITE_DIFF, ADD_SUB2,
                 h2])
  : ExceptT String IO thm).run
#eval HAS_SIZE_DIFF

#eval phrase 10
def BIRTHDAY_THM : thm := keep "BIRTHDAY_THM" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[(if a <= b then x - y else x) = x - (if b < a then 0 else y)]])
  let h1 ← sr (← ExceptT.mk [[{f:A->B | f IN (s --> t) /\
              ?x y. x IN s /\ y IN s /\ ~(x = y) /\ f(x) = f(y)} =
    (s --> t) DIFF
    {f | f IN (s --> t) /\
                 (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)}]])
  prove ([[!s:A->bool t:B->bool m n.
        s HAS_SIZE m /\ t HAS_SIZE n
        ==> {f | f IN (s --> t) /\
                 ?x y. x IN s /\ y IN s /\ ~(x = y) /\ f(x) = f(y)}
            HAS_SIZE (if m <= n then (n EXP m) - (FACT n) DIV (FACT(n - m))
                      else n EXP m)]])
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [h1] THEN
    REWRITE_TAC [h2] THEN
    MATCH_MP_TAC HAS_SIZE_DIFF THEN
    ASM_SIMP_TAC [HAS_SIZE_FUNSPACE_INJECTIVE, HAS_SIZE_FUNSPACE] THEN
    SIMP_TAC [SUBSET, IN_ELIM_THM])
  : ExceptT String IO thm).run
#eval BIRTHDAY_THM

/- ------------------------------------------------------------------------- -/
/- The usual explicit instantiation.                                         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 11
def FACT_DIV_SIMP : thm := keep "FACT_DIV_SIMP" fun _ => (do
  let h3 ← ar (← ExceptT.mk [[x + 0 = x]])
  let h2 ← ar (← ExceptT.mk [[(m + SUC d) - 1 = m + d]])
  let h1 ← ar (← ExceptT.mk [[(m + SUC d) - 1 - m = d]])
  prove ([[!m n. m < n
         ==> (FACT n) DIV (FACT m) = n * FACT(n - 1) DIV FACT(m)]])
   (GEN_TAC THEN REWRITE_TAC [LT_EXISTS, LEFT_IMP_EXISTS_THM] THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    SIMP_TAC [LEFT_FORALL_IMP_THM, EXISTS_REFL] THEN
    REWRITE_TAC [h1] THEN
    REWRITE_TAC [h2, ADD_SUB2] THEN
    GEN_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC ([[0]]) THEN
    REWRITE_TAC [FACT_LT, h3] THEN REWRITE_TAC [FACT] THEN
    SIMP_TAC [(← HolLight.GSYM MULT_ASSOC), (← HolLight.GSYM FACT_DIV_MULT), LE_ADD] THEN
    REWRITE_TAC [ADD_CLAUSES, FACT])
  : ExceptT String IO thm).run
#eval FACT_DIV_SIMP

#eval phrase 12
def BIRTHDAY_THM_EXPLICIT : thm := keep "BIRTHDAY_THM_EXPLICIT" fun _ => (do
  prove ([[!s t. s HAS_SIZE 23 /\ t HAS_SIZE 365
         ==> 2 * CARD {f | f IN (s --> t) /\
                           ?x y. x IN s /\ y IN s /\ ~(x = y) /\ f(x) = f(y)}
             >= CARD (s --> t)]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP BIRTHDAY_THM) THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP HAS_SIZE_FUNSPACE) THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    REPEAT (CHANGED_TAC (SIMP_TAC [FACT_DIV_SIMP, ARITH_LE, ARITH_LT] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV NUM_SUB_CONV))) THEN
    SIMP_TAC [DIV_REFL, (← HolLight.GSYM LT_NZ), FACT_LT] THEN
    REWRITE_TAC [HAS_SIZE] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    CONV_TAC NUM_REDUCE_CONV)
  : ExceptT String IO thm).run
#eval BIRTHDAY_THM_EXPLICIT

end Hol100.Birthday
