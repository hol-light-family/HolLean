/- File: Hol100/Subsequence.lean
Translation of HOL Light's 100/subsequence.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
open HolCore.Kernel Session HolLight.Syntax HolExamples
namespace Hol100.Subsequence

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)
private def sr (tm : term) : ExceptT String IO thm := ExceptT.mk (SET_RULE tm)
/- `ttac o check p o concl`: apply `ttac` to a theorem whose conclusion
   satisfies `p`, otherwise fail. -/
private def ifConcl (p : term → Bool) (ttac : thm → HolCore.Tactics.tactic) :
    thm → HolCore.Tactics.tactic :=
  fun th g => if p (concl th) then ttac th g else return .error "check"

/- ========================================================================= -/
/- #73: Erdos-Szekeres theorem on ascending / descending subsequences.       -/
/- ========================================================================= -/

#eval phrase 1
def lemma : thm := keep "lemma" fun _ => (do
  prove ([[!f s. s = UNIONS (IMAGE (\a. {x | x IN s /\ f(x) = a}) (IMAGE f s))]])
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN GEN_TAC THEN
    REWRITE_TAC [IN_UNIONS, IN_ELIM_THM, IN_IMAGE] THEN
    REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN
    GEN_REWRITE_TAC HolLight.RAND_CONV [SWAP_EXISTS_THM] THEN
    REWRITE_TAC [UNWIND_THM2, (← HolLight.GSYM CONJ_ASSOC), IN_ELIM_THM] THEN SET_TAC [])
  : ExceptT String IO thm).run
#eval lemma

/- ------------------------------------------------------------------------- -/
/- Pigeonhole lemma.                                                         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 2
def PIGEONHOLE_LEMMA : thm := keep "PIGEONHOLE_LEMMA" fun _ => (do
  let h3 ← ar (← ExceptT.mk [[~(n <= x) ==> x <= n - 1]])
  let h2 ← tt (← ExceptT.mk [[a /\ (a ==> b) ==> a /\ b]])
  let h1 ← sr (← ExceptT.mk [[{t x | x IN s} = IMAGE t s]])
  prove ([[!f:A->B s n.
        FINITE s /\ (n - 1) * CARD(IMAGE f s) < CARD s
        ==> ?t a. t SUBSET s /\ t HAS_SIZE n /\ (!x. x IN t ==> f(x) = a)]])
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MP_TAC (← HolLight.ISPECL [([[f:A->B]]), ([[s:A->bool]])] lemma) THEN DISCH_THEN (fun th =>
      GEN_REWRITE_TAC (HolLight.LAND_CONV o HolCore.Lib.funpow 2 HolLight.RAND_CONV) [th]) THEN
    ONCE_REWRITE_TAC [(← HolLight.GSYM CONTRAPOS_THM)] THEN REWRITE_TAC [NOT_LT] THEN
    STRIP_TAC THEN GEN_REWRITE_TAC HolLight.RAND_CONV [MULT_SYM] THEN MATCH_MP_TAC
     (← HolLight.REWRITE_RULE [h1] CARD_UNIONS_LE) THEN
    ASM_SIMP_TAC [HAS_SIZE, FINITE_IMAGE] THEN REWRITE_TAC [FORALL_IN_IMAGE] THEN
    X_GEN_TAC ([[x:A]]) THEN DISCH_TAC THEN
    MATCH_MP_TAC h2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC ([[s:A->bool]]) THEN
      ASM_SIMP_TAC [SUBSET, IN_ELIM_THM],
      ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC h3 THEN
    DISCH_TAC THEN FIRST_X_ASSUM (ifConcl HolCore.Basics.is_neg MP_TAC) THEN
    REWRITE_TAC [] THEN
    MP_TAC (← HolLight.ISPEC ([[{y | y IN s /\ (f:A->B) y = f x}]]) CHOOSE_SUBSET) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o HolLight.SPEC ([[n:num]])) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN SET_TAC [])
  : ExceptT String IO thm).run
#eval PIGEONHOLE_LEMMA

/- ------------------------------------------------------------------------- -/
/- Abbreviation for "monotonicity of f on s w.r.t. ordering r".              -/
/- ------------------------------------------------------------------------- -/

#eval phrase 3
def mono_on : thm := keep "mono_on" fun _ => define
 [[mono_on (f:num->real) r s <=>
    !i j. i IN s /\ j IN s /\ i <= j ==> r (f i) (f j)]]
#eval mono_on

#eval phrase 4
def MONO_ON_SUBSET : thm := keep "MONO_ON_SUBSET" fun _ => (do
  prove ([[!s t. t SUBSET s /\ mono_on f r s ==> mono_on f r t]])
   (REWRITE_TAC [mono_on, SUBSET] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval MONO_ON_SUBSET

/- ------------------------------------------------------------------------- -/
/- The main result.                                                          -/
/- ------------------------------------------------------------------------- -/

#eval phrase 5
def ERDOS_SZEKERES : thm := keep "ERDOS_SZEKERES" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[~(k + 1 <= k)]])
  let h1 ← ar (← ExceptT.mk [[~(m + 1 <= n) ==> n <= m]])
  prove ([[!f:num->real m n.
        (?s. s SUBSET (1..m*n+1) /\ s HAS_SIZE (m + 1) /\ mono_on f (<=) s) \/
        (?s. s SUBSET (1..m*n+1) /\ s HAS_SIZE (n + 1) /\ mono_on f (>=) s)]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     ([[!i. i IN (1..m*n+1)
        ==> ?k. (?s. s SUBSET (1..m*n+1) /\ s HAS_SIZE k /\
                     mono_on f (<=) s /\ i IN s /\ (!j. j IN s ==> i <= j)) /\
                (!l. (?s. s SUBSET (1..m*n+1) /\ s HAS_SIZE l /\
                     mono_on f (<=) s /\ i IN s /\ (!j. j IN s ==> i <= j))
                     ==> l <= k)]])
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC [(← HolLight.GSYM num_MAX)] THEN CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC [([[1]]), ([[{i:num}]])] THEN
        ASM_SIMP_TAC [SUBSET, IN_SING, LE_REFL, HAS_SIZE, FINITE_INSERT] THEN
        SIMP_TAC [FINITE_RULES, CARD_CLAUSES, NOT_IN_EMPTY, ARITH] THEN
        SIMP_TAC [mono_on, IN_SING, REAL_LE_REFL],
        EXISTS_TAC ([[CARD(1..m*n+1)]]) THEN
        ASM_MESON_TAC [CARD_SUBSET, FINITE_NUMSEG, HAS_SIZE]],
      REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[t:num->num]]) (LABEL_TAC "*" ))] THEN
    ASM_CASES_TAC ([[?i. i IN (1..m*n+1) /\ m + 1 <= t(i)]]) THENL
     [FIRST_X_ASSUM (X_CHOOSE_THEN ([[i:num]]) STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[i:num]])) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[s:num->bool]]) STRIP_ASSUME_TAC o HolLight.CONJUNCT1) THEN
      MP_TAC (← HolLight.ISPEC ([[s:num->bool]]) CHOOSE_SUBSET) THEN
      ASM_MESON_TAC [HAS_SIZE, MONO_ON_SUBSET, SUBSET_TRANS],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!i. i IN (1..m*n+1) ==> 1 <= t i /\ t i <= m]]) ASSUME_TAC THENL
     [FIRST_X_ASSUM (fun th => MP_TAC th THEN MATCH_MP_TAC MONO_FORALL) THEN
      X_GEN_TAC ([[i:num]]) THEN DISCH_THEN (fun th => DISCH_TAC THEN MP_TAC th) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o HolLight.SPEC ([[1]]) o HolLight.CONJUNCT2) THEN
      STRIP_TAC THEN CONJ_TAC THENL
       [ALL_TAC, ASM_MESON_TAC [h1]] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC ([[{i:num}]]) THEN
      ASM_SIMP_TAC [SUBSET, IN_SING, LE_REFL, HAS_SIZE, FINITE_INSERT] THEN
      SIMP_TAC [FINITE_RULES, CARD_CLAUSES, NOT_IN_EMPTY, ARITH] THEN
      SIMP_TAC [mono_on, IN_SING, REAL_LE_REFL],
      ALL_TAC] THEN
    DISJ2_TAC THEN
    SUBGOAL_THEN
     ([[?s k:num. s SUBSET (1..m*n+1) /\ s HAS_SIZE (n + 1) /\
              !i. i IN s ==> t(i) = k]])
    MP_TAC THENL
     [MATCH_MP_TAC PIGEONHOLE_LEMMA THEN
      REWRITE_TAC [FINITE_NUMSEG, CARD_NUMSEG_1, ADD_SUB] THEN
      MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC ([[n * CARD(1..m)]]) THEN
      CONJ_TAC THENL [ALL_TAC, REWRITE_TAC [CARD_NUMSEG_1] THEN ARITH_TAC] THEN
      REWRITE_TAC [LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
      MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC [FINITE_NUMSEG] THEN
      ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN ASM_MESON_TAC [IN_NUMSEG],
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[u:num->bool]]) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[k:num]]) STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC [mono_on] THEN MAP_EVERY X_GEN_TAC [([[i:num]]), ([[j:num]])] THEN
    REWRITE_TAC [LE_LT, real_ge] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [REAL_LE_REFL] THEN
    REMOVE_THEN "*" (fun th => HolLight.tactic_of do
      pure (MP_TAC (← HolLight.SPEC ([[i:num]]) th) THEN MP_TAC (← HolLight.SPEC ([[j:num]]) th))) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[s:num->bool]]) STRIP_ASSUME_TAC o HolLight.CONJUNCT1) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[k + 1]]) o HolLight.CONJUNCT2) THEN
    ASM_SIMP_TAC [h2, (← HolLight.GSYM REAL_NOT_LT)] THEN
    REWRITE_TAC [CONTRAPOS_THM] THEN
    DISCH_TAC THEN EXISTS_TAC ([[(i:num) INSERT s]]) THEN REPEAT CONJ_TAC THENL
     [HolLight.ASM SET_TAC [],
      REWRITE_TAC [HAS_SIZE_CLAUSES, (← HolLight.GSYM ADD1)] THEN ASM_MESON_TAC [NOT_LT],
      ALL_TAC,
      REWRITE_TAC [IN_INSERT],
      ASM_MESON_TAC [IN_INSERT, LE_REFL, LT_IMP_LE, LE_TRANS]] THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [mono_on]) THEN
    REWRITE_TAC [mono_on, IN_INSERT] THEN
    ASM_MESON_TAC [REAL_LE_REFL, REAL_LE_TRANS, REAL_LT_IMP_LE, NOT_LE,
                  LT_REFL, LE_TRANS])
  : ExceptT String IO thm).run
#eval ERDOS_SZEKERES

end Hol100.Subsequence
