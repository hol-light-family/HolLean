/- File: HolExamples/Forster.lean
Translation of HOL Light's Examples/forster.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolExamples.Common
open HolCore.Kernel Session HolLight.Syntax HolExamples
namespace HolExamples.Forster

/- The session's IO-valued `prove` lifted into `ExceptT String IO`, so tactic
   scripts read as in OCaml. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

#eval phrase 1
#eval Session.prioritize_num

#eval phrase 2
unsafe def FORSTER_PUZZLE : thm := keep "FORSTER_PUZZLE" fun _ => (do
  prove ([[(!n. f(n + 1) > f(f(n))) ==> !n. f(n) = n]])
   (REWRITE_TAC [GT, (← HolLight.GSYM ADD1)] THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[!n m. f(m) < n ==> m <= f m]]) ASSUME_TAC THENL
     [INDUCT_TAC THEN REWRITE_TAC [LT] THEN
      INDUCT_TAC THEN ASM_MESON_TAC [LE_0, LE_SUC_LT, LET_TRANS], ALL_TAC] THEN
    SUBGOAL_THEN ([[!n. n <= f n]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [LT], ALL_TAC] THEN
    SUBGOAL_THEN ([[!n. f(n) < f(SUC n)]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [LET_TRANS], ALL_TAC] THEN
    SUBGOAL_THEN ([[!m n. m < n ==> f(m) < f(n)]]) ASSUME_TAC THENL
     [GEN_TAC THEN INDUCT_TAC THEN ASM_MESON_TAC [LT, LT_TRANS], ALL_TAC] THEN
    SUBGOAL_THEN ([[!m n. (f m < f n) <=> m < n]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [LT_CASES, LT_ANTISYM, LT_REFL], ALL_TAC] THEN
    ASM_MESON_TAC [LE_ANTISYM, LT_SUC_LE])
  : ExceptT String IO thm).run
#eval FORSTER_PUZZLE

#eval phrase 3
-- Alternative; shorter but less transparent and taking longer to run.
unsafe def FORSTER_PUZZLE_2 : thm := keep "FORSTER_PUZZLE_2" fun _ => (do
  prove ([[(!n. f(n + 1) > f(f(n))) ==> !n. f(n) = n]])
   (REWRITE_TAC [GT, (← HolLight.GSYM ADD1)] THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[!n m. f(m) < n ==> m <= f m]]) ASSUME_TAC THENL
     [INDUCT_TAC THEN REWRITE_TAC [LT] THEN
      INDUCT_TAC THEN ASM_MESON_TAC [LE_0, LE_SUC_LT, LET_TRANS], ALL_TAC] THEN
    SUBGOAL_THEN ([[!n. n <= f n]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [LT], ALL_TAC] THEN
    SUBGOAL_THEN ([[!n. f(n) < f(SUC n)]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [LET_TRANS], ALL_TAC] THEN
    SUBGOAL_THEN ([[!m n. m < n ==> f(m) < f(n)]]) ASSUME_TAC THENL
     [GEN_TAC THEN INDUCT_TAC THEN ASM_MESON_TAC [LT, LT_TRANS], ALL_TAC] THEN
    ASM_MESON_TAC [LE_ANTISYM, LT_CASES, LT_ANTISYM, LT_REFL, LT_SUC_LE])
  : ExceptT String IO thm).run
#eval FORSTER_PUZZLE_2

#eval phrase 4
-- Robin Milner's proof.
unsafe def FORSTER_PUZZLE_3 : thm := keep "FORSTER_PUZZLE_3" fun _ => (do
  prove ([[(!n. f(n + 1) > f(f(n))) ==> !n. f(n) = n]])
   (REWRITE_TAC [GT, (← HolLight.GSYM ADD1)] THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[!m n. m <= f(n + m)]]) ASSUME_TAC THENL
     [INDUCT_TAC THEN REWRITE_TAC [LE_0, ADD_CLAUSES, LE_SUC_LT] THEN
      ASM_MESON_TAC [LET_TRANS, SUB_ADD], ALL_TAC] THEN
    SUBGOAL_THEN ([[!n. f(n) < f(SUC n)]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [LET_TRANS, LE_TRANS, ADD_CLAUSES], ALL_TAC] THEN
    SUBGOAL_THEN ([[!m n. m <= n ==> f(m) <= f(n)]]) ASSUME_TAC THENL
     [GEN_TAC THEN INDUCT_TAC THEN
      ASM_MESON_TAC [LE, LE_REFL, LT_IMP_LE, LE_TRANS], ALL_TAC] THEN
    ASM_REWRITE_TAC [(← HolLight.GSYM LE_ANTISYM)] THEN
    ASM_MESON_TAC [LT_SUC_LE, NOT_LT, ADD_CLAUSES])
  : ExceptT String IO thm).run
#eval FORSTER_PUZZLE_3

#eval phrase 5
-- A variant of Robin's proof avoiding explicit use of addition.
unsafe def FORSTER_PUZZLE_4 : thm := keep "FORSTER_PUZZLE_4" fun _ => (do
  prove ([[(!n. f(n + 1) > f(f(n))) ==> !n. f(n) = n]])
   (REWRITE_TAC [GT, (← HolLight.GSYM ADD1)] THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[!m n. m <= n ==> m <= f(n)]]) ASSUME_TAC THENL
     [INDUCT_TAC THEN REWRITE_TAC [LE_0] THEN
      INDUCT_TAC THEN REWRITE_TAC [LE, NOT_SUC] THEN
      ASM_MESON_TAC [LE_SUC_LT, LET_TRANS, LE_REFL, LT_IMP_LE, LE_TRANS],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!n. f(n) < f(SUC n)]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [NOT_LE], ALL_TAC] THEN
    SUBGOAL_THEN ([[!m n. m <= n ==> f(m) <= f(n)]]) ASSUME_TAC THENL
     [GEN_TAC THEN INDUCT_TAC THEN
      ASM_MESON_TAC [LE, LE_REFL, LT_IMP_LE, LE_TRANS], ALL_TAC] THEN
    ASM_REWRITE_TAC [(← HolLight.GSYM LE_ANTISYM)] THEN
    ASM_MESON_TAC [LT_SUC_LE, NOT_LT, ADD_CLAUSES])
  : ExceptT String IO thm).run
#eval FORSTER_PUZZLE_4

#eval phrase 6
-- The shortest?
unsafe def FORSTER_PUZZLE_5 : thm := keep "FORSTER_PUZZLE_5" fun _ => (do
  prove ([[(!n. f(n + 1) > f(f(n))) ==> !n. f(n) = n]])
   (REWRITE_TAC [GT, (← HolLight.GSYM ADD1)] THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[!m n. m <= f(n + m)]]) ASSUME_TAC THENL
     [INDUCT_TAC THEN REWRITE_TAC [LE_0, ADD_CLAUSES, LE_SUC_LT] THEN
      ASM_MESON_TAC [LET_TRANS, SUB_ADD], ALL_TAC] THEN
    SUBGOAL_THEN ([[!n. f(n) < f(SUC n)]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [LET_TRANS, LE_TRANS, ADD_CLAUSES], ALL_TAC] THEN
    SUBGOAL_THEN ([[!m n. f(m) < f(n) ==> m < n]]) ASSUME_TAC THENL
     [INDUCT_TAC THEN ASM_MESON_TAC [LT_LE, LE_0, LTE_TRANS, LE_SUC_LT],
      ALL_TAC] THEN
    ASM_MESON_TAC [LE_ANTISYM, ADD_CLAUSES, LT_SUC_LE])
  : ExceptT String IO thm).run
#eval FORSTER_PUZZLE_5

end HolExamples.Forster
