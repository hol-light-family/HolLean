/- File: Hol100/Friendship.lean
Translation of HOL Light's 100/friendship.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionLibrary.Prime
import SessionLibrary.Pocklington
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Prime SessionLibrary.Iter SessionLibrary.Pocklington
namespace Hol100.Friendship

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def nr (tm : term) : ExceptT String IO thm := ExceptT.mk (NUMBER_RULE tm)
private def sr (tm : term) : ExceptT String IO thm := ExceptT.mk (SET_RULE tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)

/- ========================================================================= -/
/- The friendship theorem.                                                   -/
/-                                                                           -/
/- Proof from "Combinatorics Tutorial 2: Friendship Theorem", copyright      -/
/- MathOlymp.com, 2001. Apparently due to J. Q. Longyear and T. D. Parsons.  -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Library/prime.ml";;
#eval SessionLibrary.Prime.ensurePrime

#eval phrase 2
-- needs "Library/pocklington.ml";;
#eval SessionLibrary.Pocklington.ensurePocklington

/- ------------------------------------------------------------------------- -/
/- Useful inductive breakdown principle ending at gcd.                       -/
/- ------------------------------------------------------------------------- -/

#eval phrase 3
def GCD_INDUCT : thm := keep "GCD_INDUCT" fun _ => (do
  prove ([[!P. (!m n. P m /\ P (m + n) ==> P n)
       ==> !m n. P m /\ P n ==> P (gcd(m,n))]])
   (GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    WF_INDUCT_TAC ([[m + n:num]]) THEN REPEAT (POP_ASSUM MP_TAC) THEN
    MAP_EVERY (fun t => SPEC_TAC (t, t)) [([[n:num]]), ([[m:num]])] THEN
    MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL
     [REWRITE_TAC [CONJ_ACI, GCD_SYM, ADD_SYM], REPEAT STRIP_TAC] THEN
    ASM_CASES_TAC ([[m = 0]]) THENL [ASM_MESON_TAC [GCD_0], ALL_TAC] THEN
    UNDISCH_TAC ([[!m n:num. P m /\ P (m + n) ==> P n]]) THEN
    DISCH_THEN (MP_TAC o HolLight.SPECL [([[m:num]]), ([[n - m:num]])]) THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN ASM_SIMP_TAC [SUB_ADD, LT_IMP_LE] THEN
    DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [([[m:num]]), ([[n - m:num]])]) THEN
    REWRITE_TAC [IMP_IMP] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [LE_EXISTS]) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[d:num]]) SUBST_ALL_TAC) THEN
    REWRITE_TAC [ADD_SUB2, GCD_ADD])
  : ExceptT String IO thm).run
#eval GCD_INDUCT

/- ------------------------------------------------------------------------- -/
/- General theorems about loops in a sequence.                               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 4
def LOOP_GCD : thm := keep "LOOP_GCD" fun _ => (do
  prove ([[!x m n. (!i. x(i + m) = x(i)) /\ (!i. x(i + n) = x(i))
           ==> !i. x(i + gcd(m,n)) = x(i)]])
   (GEN_TAC THEN MATCH_MP_TAC GCD_INDUCT THEN MESON_TAC [ADD_AC])
  : ExceptT String IO thm).run
#eval LOOP_GCD

#eval phrase 5
def LOOP_COPRIME : thm := keep "LOOP_COPRIME" fun _ => (do
  prove ([[!x m n. (!i. x(i + m) = x(i)) /\ (!i. x(i + n) = x(i)) /\ coprime(m,n)
           ==> !i. x i = x 0]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN REWRITE_TAC [ADD1] THEN
    ASM_MESON_TAC [LOOP_GCD, COPRIME_GCD])
  : ExceptT String IO thm).run
#eval LOOP_COPRIME

/- ------------------------------------------------------------------------- -/
/- General theorem about partition into equally-sized eqv classes.           -/
/- ------------------------------------------------------------------------- -/

#eval phrase 6
def EQUIVALENCE_UNIFORM_PARTITION : thm := keep "EQUIVALENCE_UNIFORM_PARTITION" fun _ => (do
  prove ([[!R s k. FINITE s /\
           (!x. x IN s ==> R x x) /\
           (!x y. R x y ==> R y x) /\
           (!x y z. R x y /\ R y z ==> R x z) /\
           (!x:A. x IN s ==> CARD {y | y IN s /\ R x y} = k)
           ==> k divides (CARD s)]])
   (REPEAT GEN_TAC THEN
    WF_INDUCT_TAC ([[CARD(s:A->bool)]]) THEN
    ASM_CASES_TAC ([[s:A->bool = {}]]) THENL
     [ASM_MESON_TAC [CARD_CLAUSES, DIVIDES_0], REPEAT STRIP_TAC] THEN
    FIRST_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [(← HolLight.GSYM MEMBER_NOT_EMPTY)]) THEN
    DISCH_THEN (X_CHOOSE_TAC ([[a:A]])) THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[{y:A | y IN s /\ ~(R (a:A) y)}]])) THEN
    REWRITE_TAC [IMP_IMP] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC [IN_ELIM_THM, FINITE_RESTRICT] THEN ASM_REWRITE_TAC [] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CARD_PSUBSET THEN
        ASM_SIMP_TAC [PSUBSET, SUBSET, EXTENSION, IN_ELIM_THM] THEN
        ASM_MESON_TAC [],
        GEN_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN
        DISCH_THEN (CONJUNCTS_THEN2 (ANTE_RES_THEN MP_TAC) ASSUME_TAC) THEN
        DISCH_TAC THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        AP_TERM_TAC THEN HolLight.ASM SET_TAC []],
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN ([[CARD(s) = CARD {y | y IN s /\ (R:A->A->bool) a y} +
                          CARD {y | y IN s /\ ~(R a y)}]]) (fun th => ASM_SIMP_TAC [th, DIVIDES_ADD, DIVIDES_REFL]) THEN
    CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC CARD_UNION_EQ THEN HolLight.ASM SET_TAC [])
  : ExceptT String IO thm).run
#eval EQUIVALENCE_UNIFORM_PARTITION

/- ------------------------------------------------------------------------- -/
/- With explicit restricted quantification.                                  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 7
def EQUIVALENCE_UNIFORM_PARTITION_RESTRICT : thm := keep "EQUIVALENCE_UNIFORM_PARTITION_RESTRICT" fun _ => (do
  prove ([[!R s k. FINITE s /\
           (!x. x IN s ==> R x x) /\
           (!x y. x IN s /\ y IN s /\ R x y ==> R y x) /\
           (!x y z. x IN s /\ y IN s /\ z IN s /\ R x y /\ R y z ==> R x z) /\
           (!x:A. x IN s ==> CARD {y | y IN s /\ R x y} = k)
           ==> k divides (CARD s)]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC EQUIVALENCE_UNIFORM_PARTITION THEN
    EXISTS_TAC ([[\x y:A. x IN s /\ y IN s /\ R x y]]) THEN
    SIMP_TAC [] THEN ASM_REWRITE_TAC [CONJ_ASSOC] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval EQUIVALENCE_UNIFORM_PARTITION_RESTRICT

/- ------------------------------------------------------------------------- -/
/- General theorem about pairing up elements of a set.                       -/
/- ------------------------------------------------------------------------- -/

#eval phrase 8
def ELEMENTS_PAIR_UP : thm := keep "ELEMENTS_PAIR_UP" fun _ => (do
  prove ([[!s r. FINITE s /\
         (!x. x IN s ==> ~(r x x)) /\
         (!x y. x IN s /\ y IN s /\ r x y ==> r y x) /\
         (!x:A. x IN s ==> ?!y. y IN s /\ r x y)
         ==> EVEN(CARD s)]])
   (REPEAT GEN_TAC THEN WF_INDUCT_TAC ([[CARD(s:A->bool)]]) THEN
    STRIP_TAC THEN ASM_CASES_TAC ([[s:A->bool = {}]]) THEN
    ASM_REWRITE_TAC [CARD_CLAUSES, ARITH] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [(← HolLight.GSYM MEMBER_NOT_EMPTY)]) THEN
    DISCH_THEN (X_CHOOSE_TAC ([[a:A]])) THEN
    MP_TAC (← HolLight.ASSUME ([[!x:A. x IN s ==> (?!y:A. y IN s /\ r x y)]])) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[a:A]])) THEN REWRITE_TAC [(← HolLight.ASSUME ([[a:A IN s]]))] THEN
    DISCH_THEN (MP_TAC o HolLight.EXISTENCE) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[b:A]]) STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[s DELETE (a:A) DELETE b]])) THEN
    REWRITE_TAC [IMP_IMP] THEN ANTS_TAC THENL
     [ALL_TAC,
      DISCH_TAC THEN
      SUBGOAL_THEN ([[s = (a:A) INSERT b INSERT (s DELETE a DELETE b)]]) SUBST1_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
      ASM_SIMP_TAC [CARD_CLAUSES, FINITE_DELETE, FINITE_INSERT] THEN
      REWRITE_TAC [IN_INSERT, IN_DELETE] THEN ASM_MESON_TAC [EVEN]] THEN
    ASM_SIMP_TAC [FINITE_DELETE, IN_DELETE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_PSUBSET THEN HolLight.ASM SET_TAC [], ALL_TAC] THEN
    X_GEN_TAC ([[x:A]]) THEN STRIP_TAC THEN
    MP_TAC (← HolLight.ASSUME ([[!x:A. x IN s ==> (?!y. y IN s /\ r x y)]])) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[x:A]])) THEN REWRITE_TAC [(← HolLight.ASSUME ([[x:A IN s]]))] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN
    X_GEN_TAC ([[y:A]]) THEN EQ_TAC THEN SIMP_TAC [] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval ELEMENTS_PAIR_UP

/- ------------------------------------------------------------------------- -/
/- Cycles and paths.                                                         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 9
def cycle : thm := keep "cycle" fun _ => new_definition
 [[cycle r k x <=> (!i. r (x i) (x(i + 1))) /\ (!i. x(i + k) = x(i))]]
#eval cycle

#eval phrase 10
def path : thm := keep "path" fun _ => new_definition
 [[path r k x <=> (!i. i < k ==> r (x i) (x(i + 1))) /\
                 (!i. k < i ==> x(i) = @x. T)]]
#eval path

/- ------------------------------------------------------------------------- -/
/- Lemmas about these concepts.                                              -/
/- ------------------------------------------------------------------------- -/

#eval phrase 11
def CYCLE_OFFSET : thm := keep "CYCLE_OFFSET" fun _ => (do
  prove ([[!r k x:num->A. cycle r k x ==> !i m. x(m * k + i) = x(i)]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [cycle] THEN STRIP_TAC THEN GEN_TAC THEN
    INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES, MULT_CLAUSES] THEN
    ASM_MESON_TAC [ADD_AC])
  : ExceptT String IO thm).run
#eval CYCLE_OFFSET

#eval phrase 12
def CYCLE_MOD : thm := keep "CYCLE_MOD" fun _ => (do
  prove ([[!r k x:num->A. cycle r k x /\ ~(k = 0) ==> !i. x(i MOD k) = x(i)]])
   (MESON_TAC [CYCLE_OFFSET, DIVISION])
  : ExceptT String IO thm).run
#eval CYCLE_MOD

#eval phrase 13
def PATHS_MONO : thm := keep "PATHS_MONO" fun _ => (do
  prove ([[(!x y. r x y ==> s x y) ==> {x | path r k x} SUBSET {x | path s k x}]])
   (REWRITE_TAC [path, IN_ELIM_THM, SUBSET] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval PATHS_MONO

#eval phrase 14
def HAS_SIZE_PATHS : thm := keep "HAS_SIZE_PATHS" fun _ => (do
  let h9 ← ar (← ExceptT.mk [[k < SUC k]])
  let h8 ← ar (← ExceptT.mk [[N * m * m EXP k = (N * m EXP k) * m]])
  let h7 ← ar (← ExceptT.mk [[SUC k < i ==> ~(i = SUC k) /\ k < i]])
  let h6 ← ar (← ExceptT.mk [[i + 1 = SUC k <=> i = k]])
  let h5 ← ar (← ExceptT.mk [[i = k \/ i < k ==> ~(i = SUC k)]])
  let h4 ← ar (← ExceptT.mk [[k < i /\ ~(i = k + 1) ==> SUC k < i]])
  let h3 ← ar (← ExceptT.mk [[i < k ==> ~(i + 1 = SUC k)]])
  let h2 ← ar (← ExceptT.mk [[~(k = SUC k) /\ (i < k ==> ~(i = SUC k))]])
  let h1 ← tt (← ExceptT.mk [[(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b]])
  prove ([[!N m r k. (:A) HAS_SIZE N /\ (!x. {y | r x y} HAS_SIZE m)
             ==> {x:num->A | path r k x} HAS_SIZE (N * m EXP k)]])
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    INDUCT_TAC THEN REWRITE_TAC [EXP, MULT_CLAUSES] THENL
     [SUBGOAL_THEN ([[{x:num->A | path r 0 x} =
                  IMAGE (\a i. if i = 0 then a else @x. T) (:A)]]) SUBST1_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_IMAGE, IN_UNIV, path, LT] THEN
        REWRITE_TAC [FUN_EQ_THM, LT_NZ] THEN MESON_TAC [],
        ALL_TAC] THEN
      MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_REWRITE_TAC [IN_UNIV] THEN
      REWRITE_TAC [FUN_EQ_THM] THEN MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[{x:num->A | path r (SUC k) x} =
    IMAGE (\(x,a) i. if i = SUC k then a else x i)
          {x,a | x IN {x | path r k x} /\ a IN {u | r (x k) u}}]]) SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_IMAGE, EXISTS_PAIR_THM] THEN
      X_GEN_TAC ([[x:num->A]]) THEN REWRITE_TAC [PAIR_EQ] THEN
      ONCE_REWRITE_TAC [h1] THEN
      REWRITE_TAC [RIGHT_EXISTS_AND_THM, UNWIND_THM1] THEN
      REWRITE_TAC [FUN_EQ_THM, path, LT] THEN EQ_TAC THENL
       [STRIP_TAC THEN EXISTS_TAC ([[\i. if i = SUC k then @x. T else x(i):A]]) THEN
        EXISTS_TAC ([[x(SUC k):A]]) THEN SIMP_TAC [] THEN
        CONJ_TAC THENL [MESON_TAC [], ALL_TAC] THEN
        SIMP_TAC [h2] THEN
        ASM_SIMP_TAC [ADD1, h3] THEN
        ASM_MESON_TAC [h4],
        ALL_TAC] THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[z:num->A]]), ([[a:A]])] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [] THEN
      SIMP_TAC [h5] THEN
      REWRITE_TAC [h6] THEN
      ASM_MESON_TAC [h7],
      ALL_TAC] THEN
    ONCE_REWRITE_TAC [h8] THEN
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC [FORALL_PAIR_THM, IN_ELIM_PAIR_THM, IN_ELIM_THM] THEN
      REWRITE_TAC [FUN_EQ_THM, path, PAIR_EQ] THEN REPEAT GEN_TAC THEN
      STRIP_TAC THEN CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
      X_GEN_TAC ([[i:num]]) THEN ASM_CASES_TAC ([[i = SUC k]]) THEN
      ASM_MESON_TAC [h9],
      ALL_TAC] THEN
    ASM_SIMP_TAC [HAS_SIZE_PRODUCT_DEPENDENT])
  : ExceptT String IO thm).run
#eval HAS_SIZE_PATHS

#eval phrase 15
def FINITE_PATHS : thm := keep "FINITE_PATHS" fun _ => (do
  let h1 ← sr (← ExceptT.mk [[{y | T} = (:A)]])
  prove ([[!r k. FINITE(:A) ==> FINITE {x:num->A | path r k x}]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC ([[{x:num->A | path (\a b. T) k x}]]) THEN SIMP_TAC [PATHS_MONO] THEN
    MP_TAC (← HolLight.ISPECL [([[CARD(:A)]]), ([[CARD(:A)]]), ([[\a:A b:A. T]]), ([[k:num]])] HAS_SIZE_PATHS) THEN
    ANTS_TAC THEN ASM_SIMP_TAC [HAS_SIZE, h1])
  : ExceptT String IO thm).run
#eval FINITE_PATHS

#eval phrase 16
def HAS_SIZE_CYCLES : thm := keep "HAS_SIZE_CYCLES" fun _ => (do
  let h3 ← ar (← ExceptT.mk [[j < k <=> j + 1 < k \/ j + 1 = k]])
  let h2 ← ar (← ExceptT.mk [[i + 1 = (m + 1) + ik <=> i = ik + m]])
  let h1 ← ar (← ExceptT.mk [[i < k ==> ~(k < i + 1)]])
  prove ([[!r k. FINITE(:A) /\ ~(k = 0)
         ==> {x:num->A | cycle r k x} HAS_SIZE
             CARD{x:num->A | path r k x /\ x(k) = x(0)}]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[{x:num->A | cycle r k x} =
    IMAGE (\x i. x(i MOD k)) {x | path r k x /\ x(k) = x(0)}]]) SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN
      X_GEN_TAC ([[x:num->A]]) THEN EQ_TAC THENL
       [DISCH_TAC THEN
        EXISTS_TAC ([[\i. if i <= k then x(i):A else @x. T]]) THEN
        REPEAT CONJ_TAC THENL
         [ASM_SIMP_TAC [FUN_EQ_THM, LT_IMP_LE, DIVISION] THEN
          ASM_MESON_TAC [CYCLE_MOD],
          SIMP_TAC [path, LT_IMP_LE] THEN REWRITE_TAC [(← HolLight.GSYM NOT_LT)] THEN
          SIMP_TAC [h1] THEN
          ASM_MESON_TAC [cycle],
          REWRITE_TAC [LE_0, LE_REFL] THEN ASM_MESON_TAC [cycle, ADD_CLAUSES]],
        REWRITE_TAC [LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM] THEN
        X_GEN_TAC ([[y:num->A]]) THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [cycle] THEN CONJ_TAC THEN X_GEN_TAC ([[i:num]]) THENL
         [ALL_TAC,
          AP_TERM_TAC THEN MATCH_MP_TAC MOD_EQ THEN EXISTS_TAC ([[1]]) THEN
          REWRITE_TAC [MULT_CLAUSES]] THEN
        SUBGOAL_THEN ([[y((i + 1) MOD k):A = y(i MOD k + 1)]]) SUBST1_TAC THENL
         [ALL_TAC, ASM_MESON_TAC [path, DIVISION]] THEN
        SUBGOAL_THEN ([[(i + 1) MOD k = (i MOD k + 1) MOD k]]) SUBST1_TAC THENL
         [MATCH_MP_TAC MOD_EQ THEN EXISTS_TAC ([[i DIV k]]) THEN
          REWRITE_TAC [h2] THEN
          ASM_MESON_TAC [DIVISION],
          ALL_TAC] THEN
        FIRST_ASSUM (MP_TAC o HolLight.CONJUNCT2 o HolLight.SPEC ([[i:num]]) o HolLight.MATCH_MP DIVISION) THEN
        SPEC_TAC (([[i MOD k]]), ([[j:num]])) THEN GEN_TAC THEN
        ONCE_REWRITE_TAC [h3] THEN
        STRIP_TAC THEN ASM_SIMP_TAC [MOD_LT] THEN AP_TERM_TAC THEN
        MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC ([[1]]) THEN
        UNDISCH_TAC ([[~(k = 0)]]) THEN ARITH_TAC],
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [HAS_SIZE] THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC ([[{x:num->A | path r k x}]]) THEN
      ASM_SIMP_TAC [FINITE_PATHS] THEN SET_TAC []] THEN
    MAP_EVERY X_GEN_TAC [([[x:num->A]]), ([[y:num->A]])] THEN SIMP_TAC [IN_ELIM_THM] THEN
    REWRITE_TAC [path, FUN_EQ_THM] THEN STRIP_TAC THEN X_GEN_TAC ([[i:num]]) THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (← HolLight.SPECL [([[i:num]]), ([[k:num]])] LT_CASES) THENL [ASM_MESON_TAC [MOD_LT], ASM_MESON_TAC [], ASM_REWRITE_TAC []] THEN
    ASM_MESON_TAC [MOD_0])
  : ExceptT String IO thm).run
#eval HAS_SIZE_CYCLES

#eval phrase 17
def FINITE_CYCLES : thm := keep "FINITE_CYCLES" fun _ => (do
  prove ([[!r k. FINITE(:A) /\ ~(k = 0) ==> FINITE {x:num->A | cycle r k x}]])
   (MESON_TAC [HAS_SIZE_CYCLES, HAS_SIZE])
  : ExceptT String IO thm).run
#eval FINITE_CYCLES

#eval phrase 18
def CARD_PATHCYCLES_STEP : thm := keep "CARD_PATHCYCLES_STEP" fun _ => (do
  let h26 ← ar (← ExceptT.mk [[k + 2 < i ==> k < i]])
  let h25 ← ar (← ExceptT.mk [[k + 2 < i ==> ~(i = k + 1) /\ ~(i = k + 2)]])
  let h24 ← ar (← ExceptT.mk [[i < k + 2 ==> ~(i = k + 2)]])
  let h23 ← ar (← ExceptT.mk [[(k + 1) + 1 = k + 1 <=> F]])
  let h22 ← ar (← ExceptT.mk [[i + 1 = k + 2 <=> i = k + 1]])
  let h21 ← ar (← ExceptT.mk [[~(k + 2 = k + 1) /\ ~(0 = k + 1) /\ ~(0 = k + 2) /\ ~(k = k + 1) /\
    ~(k = k + 2)]])
  let h20 ← ar (← ExceptT.mk [[~(i <= k) /\ ~(i = k + 1) /\ ~(i = k + 2)
                              ==> k + 2 < i]])
  let h19 ← ar (← ExceptT.mk [[k < k + 2 /\ k + 1 < k + 2]])
  let h18 ← ar (← ExceptT.mk [[i < k ==> i < k + 2]])
  let h17 ← ar (← ExceptT.mk [[i < k ==> i + 1 <= k]])
  let h16 ← ar (← ExceptT.mk [[k < k + 1 /\ k < k + 2]])
  let h15 ← ar (← ExceptT.mk [[i < k + 2 /\ ~(i = k) /\ ~(i = k + 1)
                              ==> i < k]])
  let h14 ← ar (← ExceptT.mk [[~(x + 1 = x)]])
  let h13 ← ar (← ExceptT.mk [[i + 1 = k + 2 <=> i = k + 1]])
  let h12 ← ar (← ExceptT.mk [[i < k + 2 ==> ~(i = k + 2)]])
  let h11 ← ar (← ExceptT.mk [[k + 2 < i ==> k < i /\ ~(i = k + 1) /\ ~(i = k + 2)]])
  let h10 ← ar (← ExceptT.mk [[~(k = k + 2) /\ ~(k = k + 1)]])
  let h9 ← ar (← ExceptT.mk [[~(k + 2 = k + 1)]])
  let h8 ← ar (← ExceptT.mk [[~(0 = k + 1)]])
  let h7 ← ar (← ExceptT.mk [[k + 2 < i <=> ~(i <= k) /\ ~(i = k + 1) /\ ~(i = k + 2)]])
  let h6 ← ar (← ExceptT.mk [[i < k ==> i < k + 2]])
  let h5 ← ar (← ExceptT.mk [[i < k ==> i + 1 <= k]])
  let h4 ← ar (← ExceptT.mk [[k < k + 2]])
  let h3 ← ar (← ExceptT.mk [[k < k + 1 /\ k < k + 2]])
  let h2 ← ar (← ExceptT.mk [[~(0 = k + 1) /\ ~(0 = k + 2)]])
  let h1 ← sr (← ExceptT.mk [[{x | path r (k + 2) x /\ x(k + 2) = x(0)} =
    {x | path r (k + 2) x /\ x k = x 0 /\ x(k + 2) = x(0)} UNION
    {x | path r (k + 2) x /\ ~(x k = x 0) /\ x(k + 2) = x(0)}]])
  prove ([[!N m r k.
     (:A) HAS_SIZE N /\ ~(k = 0) /\ ~(m = 0) /\
     (!x:A. {y | r x y} HAS_SIZE m) /\
     (!x y. r x y ==> r y x) /\
     (!x y. ~(x = y) ==> ?!z. r x z /\ r z y)
     ==> {x | path r (k + 2) x /\ x(k + 2) = x(0)} HAS_SIZE
         (m * CARD {x | path r k x /\ x(k) = x(0)} +
          CARD {x | path r (k) x /\ ~(x(k) = x(0))})]])
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [h1] THEN
    MATCH_MP_TAC HAS_SIZE_UNION THEN GEN_REWRITE_TAC HolCore.Lib.I [CONJ_ASSOC] THEN
    CONJ_TAC THENL [ALL_TAC, SET_TAC []] THEN CONJ_TAC THENL
     [SUBGOAL_THEN ([[{x:num->A | path r (k + 2) x /\ x k = x 0 /\ x (k + 2) = x 0} =
      IMAGE (\(x,a) i. if i = k + 1 then a
                     else if i = k + 2 then x(0)
                     else x(i))
            {x,a | x IN {x | path r k x /\ x(k) = x(0)} /\
                   a IN {u | r (x k) u}}]]) SUBST1_TAC THENL
       [ALL_TAC,
        MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
         [REWRITE_TAC [FORALL_PAIR_THM, IN_ELIM_PAIR_THM] THEN
          REWRITE_TAC [IN_ELIM_THM, FUN_EQ_THM, PAIR_EQ] THEN
          MAP_EVERY X_GEN_TAC [([[y:num->A]]), ([[a:A]]), ([[z:num->A]]), ([[b:A]])] THEN
          DISCH_THEN (fun th => CONJ_TAC THEN MP_TAC th THENL
           [ALL_TAC, MESON_TAC []]) THEN
          REPEAT (DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
          DISCH_THEN (fun th => X_GEN_TAC ([[i:num]]) THEN MP_TAC th) THEN
          DISCH_THEN (fun th => HolLight.tactic_of do
        pure (MP_TAC th THEN MP_TAC (← HolLight.SPEC ([[0]]) th))) THEN
          REWRITE_TAC [h2] THEN
          DISCH_TAC THEN ASM_CASES_TAC ([[k:num < i]]) THENL
           [ASM_MESON_TAC [path], ALL_TAC] THEN
          DISCH_THEN (MP_TAC o HolLight.SPEC ([[i:num]])) THEN
          ASM_MESON_TAC [h3],
          ALL_TAC] THEN
        ONCE_REWRITE_TAC [MULT_SYM] THEN
        MATCH_MP_TAC HAS_SIZE_PRODUCT_DEPENDENT THEN
        ASM_REWRITE_TAC [] THEN REWRITE_TAC [HAS_SIZE] THEN
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC ([[{x:num->A | path r k x}]]) THEN CONJ_TAC THENL
         [ALL_TAC, SET_TAC []] THEN
        ASM_MESON_TAC [HAS_SIZE, FINITE_PATHS]] THEN
      REWRITE_TAC [EXTENSION, IN_IMAGE] THEN
      REWRITE_TAC [EXISTS_PAIR_THM, IN_ELIM_PAIR_THM] THEN
      REWRITE_TAC [FUN_EQ_THM, IN_ELIM_THM] THEN
      X_GEN_TAC ([[x:num->A]]) THEN EQ_TAC THENL
       [STRIP_TAC THEN
        EXISTS_TAC ([[\i. if i <= k then x(i):A else @x. T]]) THEN
        EXISTS_TAC ([[(x:num->A) (k + 1)]]) THEN
        REWRITE_TAC [IN_ELIM_THM, LE_REFL, LE_0] THEN
        ASM_REWRITE_TAC [CONJ_ASSOC] THEN CONJ_TAC THENL
         [ALL_TAC, ASM_MESON_TAC [path, h4]] THEN
        CONJ_TAC THENL
         [ALL_TAC,
          UNDISCH_TAC ([[path r (k + 2) (x:num->A)]]) THEN
          SIMP_TAC [path, LT_IMP_LE, h5] THEN
          SIMP_TAC [(← HolLight.GSYM NOT_LT)] THEN
          MESON_TAC [h6]] THEN
        X_GEN_TAC ([[i:num]]) THEN
        ASM_CASES_TAC ([[i = k + 1]]) THEN ASM_REWRITE_TAC [] THEN
        ASM_CASES_TAC ([[i = k + 2]]) THEN ASM_REWRITE_TAC [] THEN
        FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [path]) THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[i:num]]) o HolLight.CONJUNCT2) THEN
        ASM_REWRITE_TAC [h7],
        ALL_TAC] THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[z:num->A]]), ([[b:A]])] THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
      DISCH_THEN (fun th => HolLight.tactic_of do
        pure (MP_TAC th THEN MP_TAC (← HolLight.SPEC ([[0]]) th))) THEN
      REWRITE_TAC [COND_ID, h8] THEN DISCH_TAC THEN
      REWRITE_TAC [CONJ_ASSOC] THEN DISCH_THEN (LABEL_TAC "*") THEN CONJ_TAC THENL
       [ALL_TAC, REMOVE_THEN "*" (MP_TAC o HolLight.SPEC ([[k + 2]])) THEN
        ASM_REWRITE_TAC [h9]] THEN
      CONJ_TAC THENL
       [ALL_TAC, REMOVE_THEN "*" (MP_TAC o HolLight.SPEC ([[k:num]])) THEN
        ASM_REWRITE_TAC [h10]] THEN
      UNDISCH_TAC ([[path r k (z:num->A)]]) THEN ASM_REWRITE_TAC [path] THEN
      SIMP_TAC [h11] THEN
      STRIP_TAC THEN X_GEN_TAC ([[i:num]]) THEN DISCH_TAC THEN
      ASM_SIMP_TAC [h12] THEN
      REWRITE_TAC [h13] THEN
      ASM_CASES_TAC ([[i = k + 1]]) THEN ASM_REWRITE_TAC [] THENL
       [ASM_MESON_TAC [h14], ALL_TAC] THEN
      REWRITE_TAC [EQ_ADD_RCANCEL] THEN COND_CASES_TAC THEN ASM_SIMP_TAC [] THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      ASM_MESON_TAC [h15],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[{x:num->A | path r (k + 2) x /\ ~(x k = x 0) /\ x (k + 2) = x 0} =
    IMAGE (\x i. if i = k + 1 then @z. r (x k) z /\ r z (x 0)
               else if i = k + 2 then x(0)
               else x(i))
        {x | path r k x /\ ~(x(k) = x(0))}]]) SUBST1_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
       [ALL_TAC,
        REWRITE_TAC [HAS_SIZE] THEN
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC ([[{x:num->A | path r k x}]]) THEN CONJ_TAC THENL
         [ALL_TAC, SET_TAC []] THEN
        ASM_MESON_TAC [HAS_SIZE, FINITE_PATHS]] THEN
      MAP_EVERY X_GEN_TAC [([[x:num->A]]), ([[y:num->A]])] THEN
      REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN
      REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC ([[i:num]]) THEN
      ASM_CASES_TAC ([[k:num < i]]) THENL
       [ASM_MESON_TAC [path], ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [FUN_EQ_THM]) THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC ([[i:num]])) THEN
      ASM_MESON_TAC [h16]] THEN
    REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN
    X_GEN_TAC ([[x:num->A]]) THEN REWRITE_TAC [IN_ELIM_THM] THEN EQ_TAC THENL
     [STRIP_TAC THEN
      EXISTS_TAC ([[\i. if i <= k then x(i):A else @x. T]]) THEN
      ASM_REWRITE_TAC [LE_REFL, LE_0] THEN CONJ_TAC THENL
       [ALL_TAC,
        UNDISCH_TAC ([[path r (k + 2) (x:num->A)]]) THEN
        SIMP_TAC [path, LT_IMP_LE, h17] THEN
        SIMP_TAC [(← HolLight.GSYM NOT_LT)] THEN
        MESON_TAC [h18]] THEN
      REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC ([[i:num]]) THEN
      ASM_CASES_TAC ([[i = k + 1]]) THEN ASM_REWRITE_TAC [] THENL
       [CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC SELECT_UNIQUE THEN
        UNDISCH_TAC ([[path r (k + 2) (x:num->A)]]) THEN REWRITE_TAC [path] THEN
        DISCH_THEN (MP_TAC o HolLight.CONJUNCT1) THEN
        DISCH_THEN (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPEC ([[k:num]]) th) THEN
                             MP_TAC (← HolLight.SPEC ([[k + 1]]) th))) THEN
        REWRITE_TAC [h19] THEN
        REWRITE_TAC [(← HolLight.GSYM ADD_ASSOC), ARITH] THEN ASM_MESON_TAC [],
        ALL_TAC] THEN
      ASM_CASES_TAC ([[i = k + 2]]) THEN ASM_REWRITE_TAC [] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC ([[path r (k + 2) (x:num->A)]]) THEN REWRITE_TAC [path] THEN
      DISCH_THEN (MP_TAC o HolLight.CONJUNCT2) THEN
      ASM_MESON_TAC [h20],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[y:num->A]]) STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC [h21] THEN
    REWRITE_TAC [path] THEN CONJ_TAC THEN X_GEN_TAC ([[i:num]]) THEN DISCH_TAC THENL
     [REWRITE_TAC [h22] THEN
      ASM_CASES_TAC ([[i = k + 1]]) THEN ASM_REWRITE_TAC [] THENL
       [REWRITE_TAC [h23] THEN ASM_MESON_TAC [],
        ALL_TAC] THEN
      ASM_SIMP_TAC [h24] THEN
      REWRITE_TAC [EQ_ADD_RCANCEL] THEN COND_CASES_TAC THEN ASM_SIMP_TAC [] THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      UNDISCH_TAC ([[path r k (y:num->A)]]) THEN REWRITE_TAC [path] THEN
      DISCH_THEN (MATCH_MP_TAC o HolLight.CONJUNCT1) THEN
      MAP_EVERY UNDISCH_TAC [([[~(i:num = k)]]), ([[~(i = k + 1)]]), ([[i < k + 2]])] THEN
      ARITH_TAC,
      ALL_TAC] THEN
    ASM_SIMP_TAC [h25] THEN
    ASM_MESON_TAC [path, h26])
  : ExceptT String IO thm).run
#eval CARD_PATHCYCLES_STEP

/- ------------------------------------------------------------------------- -/
/- The first lemma about the number of cycles.                               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 19
def shiftable : thm := keep "shiftable" fun _ => new_definition
 [[shiftable x y <=> ?k. !i. x(i) = y(i + k)]]
#eval shiftable

#eval phrase 20
def SHIFTABLE_REFL : thm := keep "SHIFTABLE_REFL" fun _ => (do
  prove ([[!x. shiftable x x]])
   (REWRITE_TAC [shiftable] THEN MESON_TAC [ADD_CLAUSES])
  : ExceptT String IO thm).run
#eval SHIFTABLE_REFL

#eval phrase 21
def SHIFTABLE_TRANS : thm := keep "SHIFTABLE_TRANS" fun _ => (do
  prove ([[!x y z. shiftable x y /\ shiftable y z ==> shiftable x z]])
   (REWRITE_TAC [shiftable] THEN MESON_TAC [ADD_ASSOC])
  : ExceptT String IO thm).run
#eval SHIFTABLE_TRANS

#eval phrase 22
def SHIFTABLE_LOCAL : thm := keep "SHIFTABLE_LOCAL" fun _ => (do
  prove ([[!x y p r. cycle r p x /\ cycle r p y /\ ~(p = 0)
             ==> (shiftable x y <=> ?k. k < p /\ !i. x(i) = y(i + k))]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [shiftable] THEN
    EQ_TAC THENL [ALL_TAC, MESON_TAC []] THEN
    DISCH_THEN (X_CHOOSE_TAC ([[k:num]])) THEN EXISTS_TAC ([[k MOD p]]) THEN
    FIRST_ASSUM (MP_TAC o HolLight.SPEC ([[k:num]]) o HolLight.MATCH_MP DIVISION) THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th => GEN_REWRITE_TAC (HolLight.BINDER_CONV o HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [th]) THEN
    ASM_MESON_TAC [CYCLE_OFFSET, ADD_AC])
  : ExceptT String IO thm).run
#eval SHIFTABLE_LOCAL

#eval phrase 23
def SHIFTABLE_SYM : thm := keep "SHIFTABLE_SYM" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[k < p ==> (i + (p - k)) + k = i + p:num]])
  let h1 ← tt (← ExceptT.mk [[a /\ b /\ c /\ d <=> (a /\ b /\ c) /\ d]])
  prove ([[!x y p r. cycle r p x /\ cycle r p y /\ ~(p = 0) /\ shiftable x y
             ==> shiftable y x]])
   (REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC [h1] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    FIRST_ASSUM (SUBST1_TAC o HolLight.MATCH_MP SHIFTABLE_LOCAL) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[k:num]]) STRIP_ASSUME_TAC) THEN
    REWRITE_TAC [shiftable] THEN EXISTS_TAC ([[p - k:num]]) THEN
    ASM_SIMP_TAC [h2] THEN
    ASM_MESON_TAC [cycle])
  : ExceptT String IO thm).run
#eval SHIFTABLE_SYM

#eval phrase 24
def CYCLES_PRIME_LEMMA : thm := keep "CYCLES_PRIME_LEMMA" fun _ => (do
  let h4 ← nr (← ExceptT.mk [[coprime(p,p + d) <=> coprime(d,p)]])
  let h3 ← ar (← ExceptT.mk [[k < p ==> (i + p - k) + k = i + p:num]])
  let h2 ← ar (← ExceptT.mk [[i + l + pk = (i + pk) + l:num]])
  let h1 ← tt (← ExceptT.mk [[(~p ==> F) ==> p]])
  prove ([[!r p x. FINITE(:A) /\ prime p /\ (!x. ~(r x x))
           ==> p divides CARD {x:num->A | cycle r p x}]])
   (REPEAT GEN_TAC THEN ASM_CASES_TAC ([[p = 0]]) THEN ASM_REWRITE_TAC [PRIME_0] THEN
    STRIP_TAC THEN MATCH_MP_TAC EQUIVALENCE_UNIFORM_PARTITION_RESTRICT THEN
    EXISTS_TAC ([[shiftable:(num->A)->(num->A)->bool]]) THEN
    ASM_SIMP_TAC [IN_ELIM_THM, FINITE_CYCLES] THEN
    CONJ_TAC THENL [MESON_TAC [SHIFTABLE_REFL], ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC [SHIFTABLE_SYM], ALL_TAC] THEN
    CONJ_TAC THENL [MESON_TAC [SHIFTABLE_TRANS], ALL_TAC] THEN
    X_GEN_TAC ([[x:num->A]]) THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[{y:num->A | cycle r p y /\ shiftable x y} HAS_SIZE p]]) (fun th => MESON_TAC [HAS_SIZE, th]) THEN
    SUBGOAL_THEN ([[{y:num->A | cycle r p y /\ shiftable x y} =
                IMAGE (\k i. x(i + k)) {k | k < p}]]) SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN
      X_GEN_TAC ([[y:num->A]]) THEN REWRITE_TAC [FUN_EQ_THM] THEN EQ_TAC THENL
       [ASM_MESON_TAC [SHIFTABLE_LOCAL, SHIFTABLE_SYM], ALL_TAC] THEN
      REPEAT STRIP_TAC THENL
       [FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [cycle]) THEN
        ASM_REWRITE_TAC [cycle] THEN MESON_TAC [ADD_AC],
        ALL_TAC] THEN
      MATCH_MP_TAC SHIFTABLE_SYM THEN
      MAP_EVERY EXISTS_TAC [([[p:num]]), ([[r:A->A->bool]])] THEN
      ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [cycle]) THEN
      ASM_REWRITE_TAC [cycle, shiftable] THEN MESON_TAC [ADD_AC],
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN REWRITE_TAC [HAS_SIZE_NUMSEG_LT] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN MATCH_MP_TAC WLOG_LE THEN
    REWRITE_TAC [FUN_EQ_THM] THEN CONJ_TAC THENL [MESON_TAC [], ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [([[k:num]]), ([[l:num]])] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC h1 THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[!i. x(i):A = x(0)]]) MP_TAC THENL
     [ALL_TAC, ASM_MESON_TAC [cycle]] THEN
    MATCH_MP_TAC LOOP_COPRIME THEN EXISTS_TAC ([[p:num]]) THEN
    REWRITE_TAC [RIGHT_EXISTS_AND_THM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC [cycle], ALL_TAC] THEN
    EXISTS_TAC ([[l + (p - k):num]]) THEN CONJ_TAC THENL
     [X_GEN_TAC ([[i:num]]) THEN
      ONCE_REWRITE_TAC [h2] THEN
      ASSUM_LIST (REWRITE_TAC o mapR HolLight.GSYM) THEN
      SIMP_TAC [h3,
               (← HolLight.ASSUME ([[k < p:num]]))] THEN
      ASM_MESON_TAC [cycle],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[l + p - k = p + l - k:num]]) SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC [([[k < p:num]]), ([[k <= l:num]])] THEN ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [h4] THEN
    MATCH_MP_TAC PRIME_COPRIME_LT THEN
    ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC)
  : ExceptT String IO thm).run
#eval CYCLES_PRIME_LEMMA

/- ------------------------------------------------------------------------- -/
/- The theorem itself.                                                       -/
/- ------------------------------------------------------------------------- -/

#eval phrase 25
def FRIENDSHIP : thm := keep "FRIENDSHIP" fun _ => (do
  let h13 ← ar (← ExceptT.mk [[~(m = 0) ==> m - 1 + 1 = m]])
  let h12 ← nr (← ExceptT.mk [[!q. t divides q /\ m = q + 1 ==> t divides m ==> t divides w]])
  let h11 ← ar (← ExceptT.mk [[2 <= p /\ ~(p = 2) ==> 3 <= p]])
  let h10 ← nr (← ExceptT.mk [[!q c K1 K2.
        p divides q /\ p divides c /\
        c = (q + 1) * K1 + K2 /\
        K1 + K2 = ((q + 1) * q + 1) * nep2
        ==> p divides nep2]])
  let h9 ← ar (← ExceptT.mk [[~(m = 0) ==> m - 1 + 1 = m]])
  let h8 ← nr (← ExceptT.mk [[!x. p divides (x + 1) /\ p divides x ==> p divides 1]])
  let h7 ← tt (← ExceptT.mk [[(a /\ b) /\ c <=> b /\ a /\ c]])
  let h6 ← ar (← ExceptT.mk [[m - 1 - 1 = m - 2]])
  let h5 ← ar (← ExceptT.mk [[a + 1 = (m + 1) + m * c <=> a = m * (1 + c)]])
  let h4 ← tt (← ExceptT.mk [[(a /\ b) /\ c <=> b /\ a /\ c]])
  let h3 ← tt (← ExceptT.mk [[(~a /\ ~b ==> c) ==> (a \/ b) \/ c]])
  let h2 ← tt (← ExceptT.mk [[p <=> ~ ~ p]])
  let h1 ← tt (← ExceptT.mk [[a ==> b /\ c <=> (a ==> b) /\ (a ==> c)]])
  prove ([[!friend:person->person->bool.
      FINITE(:person) /\
      (!x. ~(friend x x)) /\
      (!x y. friend x y ==> friend y x) /\
      (!x y. ~(x = y) ==> ?!z. friend x z /\ friend y z)
      ==> ?u. !v. ~(v = u) ==> friend u v]])
   (REPEAT STRIP_TAC THEN UNDISCH_TAC ([[!x y:person. ~(x = y) ==> ?!z:person. friend x z /\ friend y z]]) THEN
    REWRITE_TAC [EXISTS_UNIQUE_THM] THEN
    REWRITE_TAC [h1] THEN
    REWRITE_TAC [FORALL_AND_THM, RIGHT_IMP_FORALL_THM] THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [SKOLEM_THM, IMP_IMP, (← HolLight.GSYM CONJ_ASSOC)] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    DISCH_THEN (X_CHOOSE_TAC ([[mutualfriend:person->person->person]])) THEN
    SUBGOAL_THEN ([[!s:person->bool. FINITE s]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [SUBSET_UNIV, FINITE_SUBSET], ALL_TAC] THEN
    ABBREV_TAC ([[degree = \p:person. CARD {q:person | friend p q}]]) THEN
    SUBGOAL_THEN ([[!x y:person. ~(friend x y) ==> degree(x):num <= degree(y)]]) ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_CASES_TAC ([[x:person = y]]) THENL
       [ASM_MESON_TAC [LE_REFL], ALL_TAC] THEN
      EXPAND_TAC "degree" THEN MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC ([[CARD(IMAGE (\u. (mutualfriend:person->person->person) u y)
                           {q | friend (x:person) q})]]) THEN
      CONJ_TAC THENL
       [ALL_TAC, MATCH_MP_TAC CARD_SUBSET THEN HolLight.ASM SET_TAC []] THEN
      MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC HolLight.SYM_CONV THEN
      MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [([[u1:person]]), ([[u2:person]])] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [([[x:person]]), ([[(mutualfriend:person->person->person) u1 y]]),
        ([[u1:person]]), ([[u2:person]])]) THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!x y:person. ~(friend x y) ==> degree x:num = degree y]]) ASSUME_TAC THENL [ASM_MESON_TAC [LE_ANTISYM], ALL_TAC] THEN
    GEN_REWRITE_TAC HolCore.Lib.I [h2] THEN
    GEN_REWRITE_TAC HolLight.RAND_CONV [NOT_EXISTS_THM] THEN
    DISCH_THEN (ASSUME_TAC o HolLight.REWRITE_RULE [NOT_FORALL_THM, NOT_IMP]) THEN
    SUBGOAL_THEN ([[?m:num. !x:person. degree(x) = m]]) STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM (X_CHOOSE_THEN ([[b:person]]) STRIP_ASSUME_TAC o
        HolLight.SPEC ([[a:person]])) THEN
      ABBREV_TAC ([[c = (mutualfriend:person->person->person) a b]]) THEN
      ABBREV_TAC ([[k = (degree:person->num) a]]) THEN EXISTS_TAC ([[k:num]]) THEN
      SUBGOAL_THEN ([[(degree:person->num)(b) = k /\ ~(friend a b) /\
                  friend a c /\ friend b c]]) STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN ([[!x:person. ~(x = c) ==> degree x = (k:num)]]) ASSUME_TAC THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!p:person. {q:person | friend p q} HAS_SIZE m]]) ASSUME_TAC THENL [ASM_MESON_TAC [HAS_SIZE], ALL_TAC] THEN
    SUBGOAL_THEN ([[~(m = 0)]]) ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC ([[!p:person. {q:person | friend p q} HAS_SIZE m]]) THEN
      ASM_REWRITE_TAC [HAS_SIZE_0, EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY] THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[EVEN(m)]]) ASSUME_TAC THENL
     [UNDISCH_TAC ([[!x:person. degree x = (m:num)]]) THEN
      DISCH_THEN (SUBST1_TAC o HolLight.SYM o HolLight.SPEC ([[a:person]])) THEN
      EXPAND_TAC "degree" THEN MATCH_MP_TAC ELEMENTS_PAIR_UP THEN
      EXISTS_TAC ([[\x y:person. friend a x /\ friend a y /\ friend x y]]) THEN
      REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [HAS_SIZE],
      ALL_TAC] THEN
    ABBREV_TAC ([[N = CARD(:person)]]) THEN
    SUBGOAL_THEN ([[N = m * (m - 1) + 1]]) ASSUME_TAC THENL
     [ABBREV_TAC ([[t = {q:person | friend (a:person) q}]]) THEN
      SUBGOAL_THEN ([[FINITE(t:person->bool) /\ CARD t = m]]) STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC [HAS_SIZE], ALL_TAC] THEN
      ABBREV_TAC ([[u = \b:person. {c:person | friend b c /\ ~(c IN (a INSERT t))}]]) THEN
      EXPAND_TAC "N" THEN
      SUBGOAL_THEN ([[(:person) = (a INSERT t) UNION UNIONS {u(b) | b IN t}]]) SUBST1_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_INSERT, IN_UNIV, IN_UNION, IN_UNIONS] THEN
        MAP_EVERY EXPAND_TAC ["t", "u"] THEN REWRITE_TAC [IN_ELIM_THM] THEN
        X_GEN_TAC ([[x:person]]) THEN
        MATCH_MP_TAC h3 THEN
        STRIP_TAC THEN REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN
        ONCE_REWRITE_TAC [h4] THEN
        ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN REWRITE_TAC [UNWIND_THM2] THEN
        REWRITE_TAC [IN_ELIM_THM, IN_INSERT, DE_MORGAN_THM] THEN
        EXISTS_TAC ([[mutualfriend (a:person) (x:person) :person]]) THEN
        EXPAND_TAC "t" THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[m * (m - 1) + 1 = (m + 1) + m * (m - 2)]]) SUBST1_TAC THENL
       [SIMP_TAC [h5] THEN
        AP_TERM_TAC THEN UNDISCH_TAC ([[EVEN m]]) THEN
        ASM_CASES_TAC ([[m = 1]]) THEN ASM_REWRITE_TAC [ARITH] THEN DISCH_TAC THEN
        MAP_EVERY UNDISCH_TAC [([[~(m = 0)]]), ([[~(m = 1)]])] THEN ARITH_TAC,
        ALL_TAC] THEN
      SUBGOAL_THEN ([[m + 1 = CARD((a:person) INSERT t)]]) SUBST1_TAC THENL
       [ASM_SIMP_TAC [CARD_CLAUSES, ADD1] THEN EXPAND_TAC "t" THEN
        REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[UNIONS {u b :person->bool | (b:person) IN t} HAS_SIZE m * (m - 2)]]) MP_TAC THENL
       [MATCH_MP_TAC HAS_SIZE_UNIONS THEN CONJ_TAC THENL
         [ASM_MESON_TAC [HAS_SIZE], ALL_TAC] THEN
        CONJ_TAC THENL
         [ALL_TAC,
          EXPAND_TAC "u" THEN REWRITE_TAC [DISJOINT, EXTENSION, IN_INTER] THEN
          REWRITE_TAC [NOT_IN_EMPTY, IN_ELIM_THM, IN_INSERT] THEN
          EXPAND_TAC "t" THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC []] THEN
        REPEAT STRIP_TAC THEN
        MP_TAC (← HolLight.ASSUME ([[(b:person) IN t]])) THEN EXPAND_TAC "t" THEN
        REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN
        SUBGOAL_THEN ([[u (b:person) =
        {q:person | friend q b} DELETE a DELETE (mutualfriend a b)]]) SUBST1_TAC THENL
         [MAP_EVERY EXPAND_TAC ["u", "t"] THEN
          REWRITE_TAC [EXTENSION, IN_INSERT, IN_DELETE, IN_ELIM_THM] THEN
          X_GEN_TAC ([[x:person]]) THEN
          FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [([[a:person]]), ([[b:person]]),
           ([[(mutualfriend:person->person->person) a b]]), ([[x:person]])]) THEN
          ASM_MESON_TAC [],
          ALL_TAC] THEN
        ASM_SIMP_TAC [CARD_DELETE, HAS_SIZE] THEN
        REWRITE_TAC [IN_ELIM_THM, IN_DELETE] THEN
        COND_CASES_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
        SUBGOAL_THEN ([[{q:person | friend q (b:person)} = {q | friend b q}]]) SUBST1_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
        ASM_REWRITE_TAC [h6] THEN
        ASM_MESON_TAC [HAS_SIZE],
        ALL_TAC] THEN
      REWRITE_TAC [HAS_SIZE] THEN DISCH_THEN (SUBST1_TAC o HolLight.SYM o HolLight.CONJUNCT2) THEN
      MATCH_MP_TAC CARD_UNION THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [EXTENSION, IN_INSERT, IN_INTER, NOT_IN_EMPTY, IN_UNIONS] THEN
      REWRITE_TAC [IN_ELIM_THM, LEFT_AND_EXISTS_THM] THEN
      ONCE_REWRITE_TAC [h7] THEN
      ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN REWRITE_TAC [UNWIND_THM2] THEN
      MAP_EVERY EXPAND_TAC ["u", "t"] THEN
      REWRITE_TAC [IN_ELIM_THM, IN_INSERT] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[~(m = 2)]]) ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC (HolLight.CONV_RULE NUM_REDUCE_CONV) THEN
      SUBGOAL_THEN ([[(:person) HAS_SIZE 3]]) MP_TAC THENL
       [ASM_REWRITE_TAC [HAS_SIZE], ALL_TAC] THEN
      CONV_TAC (HolLight.LAND_CONV HAS_SIZE_CONV) THEN REWRITE_TAC [NOT_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[a:person]]), ([[b:person]]), ([[c:person]])] THEN
      REWRITE_TAC [EXTENSION, IN_UNIV, IN_INSERT, NOT_IN_EMPTY] THEN
      STRIP_TAC THEN
      UNDISCH_TAC ([[!u:person. ?v:person. ~(v = u) /\ ~friend u v]]) THEN
      REWRITE_TAC [NOT_FORALL_THM, NOT_EXISTS_THM] THEN
      EXISTS_TAC ([[a:person]]) THEN
      UNDISCH_TAC ([[!p:person. {q:person | friend p q} HAS_SIZE 2]]) THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC ([[a:person]])) THEN ASM_REWRITE_TAC [] THEN
      CONV_TAC (HolLight.LAND_CONV HAS_SIZE_CONV) THEN
      REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_INSERT, NOT_IN_EMPTY] THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[x:person]]), ([[y:person]])] THEN
      STRIP_TAC THEN X_GEN_TAC ([[z:person]]) THEN
      UNDISCH_TAC ([[!x:person. x = a \/ x = b \/ x = c]]) THEN
      DISCH_THEN (fun th => MAP_EVERY (fun x => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPEC x th))) [([[x:person]]), ([[y:person]]), ([[z:person]])]) THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    MP_TAC (← HolLight.SPEC ([[m - 1]]) PRIME_FACTOR) THEN ANTS_TAC THENL
     [UNDISCH_TAC ([[~(m = 2)]]) THEN ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[p:num]]) STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN ([[~(p divides 1)]]) MP_TAC THENL
     [ASM_MESON_TAC [DIVIDES_ONE, PRIME_1], ALL_TAC] THEN
    REWRITE_TAC [] THEN
    MATCH_MP_TAC h8 THEN
    EXISTS_TAC ([[m - 1]]) THEN ASM_REWRITE_TAC [] THEN
    ASM_SIMP_TAC [h9] THEN
    MATCH_MP_TAC PRIME_DIVEXP THEN EXISTS_TAC ([[p - 2]]) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC h10 THEN
    MAP_EVERY EXISTS_TAC [([[m - 1]]), ([[CARD {x:num->person | cycle friend p x}]]),
      ([[CARD {x:num->person | path friend (p-2) x /\ x (p-2) = x 0}]]),
      ([[CARD {x:num->person | path friend (p-2) x /\ ~(x (p-2) = x 0)}]])] THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CYCLES_PRIME_LEMMA THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN ([[3 <= p]]) ASSUME_TAC THENL
     [MATCH_MP_TAC h11 THEN
      ASM_SIMP_TAC [PRIME_GE_2] THEN DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [(← HolLight.GSYM DIVIDES_2)]) THEN
      MP_TAC (DIVIDES_CONV ([[2 divides 1]])) THEN REWRITE_TAC [CONTRAPOS_THM] THEN
      MATCH_MP_TAC h12 THEN
      EXISTS_TAC ([[m - 1]]) THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC ([[~(m = 0)]]) THEN ARITH_TAC,
      ALL_TAC] THEN
    ASM_SIMP_TAC [h13] THEN CONJ_TAC THENL
     [MP_TAC (← HolLight.ISPECL [([[friend:person->person->bool]]), ([[p:num]])] HAS_SIZE_CYCLES) THEN
      ANTS_TAC THENL [ASM_MESON_TAC [PRIME_0], ALL_TAC] THEN
      SIMP_TAC [HAS_SIZE] THEN DISCH_THEN ((fun _ => ALL_TAC)) THEN
      MATCH_MP_TAC HAS_SIZE_CARD THEN
      SUBGOAL_THEN ([[p = (p - 2) + 2]]) (fun th => GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [th]) THENL [ASM_MESON_TAC [PRIME_GE_2, SUB_ADD], ALL_TAC] THEN
      MATCH_MP_TAC CARD_PATHCYCLES_STEP THEN EXISTS_TAC ([[N:num]]) THEN
      ASM_REWRITE_TAC [] THEN
      CONJ_TAC THENL [ASM_MESON_TAC [HAS_SIZE], ALL_TAC] THEN
      CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
      UNDISCH_TAC ([[3 <= p]]) THEN ARITH_TAC,
      ALL_TAC] THEN
    MP_TAC (← HolLight.ISPECL [([[N:num]]), ([[m:num]]), ([[friend:person->person->bool]]), ([[p - 2]])] HAS_SIZE_PATHS) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [HAS_SIZE], ALL_TAC] THEN
    ASM_REWRITE_TAC [HAS_SIZE] THEN
    DISCH_THEN (SUBST1_TAC o HolLight.SYM o HolLight.CONJUNCT2) THEN
    MATCH_MP_TAC CARD_UNION_EQ THEN ASM_SIMP_TAC [FINITE_PATHS] THEN SET_TAC [])
  : ExceptT String IO thm).run
#eval FRIENDSHIP

end Hol100.Friendship
