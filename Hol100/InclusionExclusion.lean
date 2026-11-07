/- File: Hol100/InclusionExclusion.lean
Translation of HOL Light's 100/inclusion_exclusion.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
namespace Hol100.InclusionExclusion

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def ms (ths : List thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (MESON ths tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)
private def sr (tm : term) : ExceptT String IO thm := ExceptT.mk (SET_RULE tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)

/- ========================================================================= -/
/- Inclusion-exclusion principle, the usual and generalized forms.           -/
/- ========================================================================= -/
/- ------------------------------------------------------------------------- -/
/- Simple set theory lemmas.                                                 -/
/- ------------------------------------------------------------------------- -/

#eval phrase 1
def SUBSET_INSERT_EXISTS : thm := keep "SUBSET_INSERT_EXISTS" fun _ => (do
  let h1 ← tt (← ExceptT.mk [[(a /\ ~b ==> c) ==> a ==> b \/ c]])
  prove ([[!s x:A t. s SUBSET (x INSERT t) <=>
                s SUBSET t \/ ?u. u SUBSET t /\ s = x INSERT u]])
   (REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC, SET_TAC []] THEN
    MATCH_MP_TAC h1 THEN
    DISCH_TAC THEN EXISTS_TAC ([[s DELETE (x:A)]]) THEN HolLight.ASM SET_TAC [])
  : ExceptT String IO thm).run
#eval SUBSET_INSERT_EXISTS

#eval phrase 2
def FINITE_SUBSETS_RESTRICT : thm := keep "FINITE_SUBSETS_RESTRICT" fun _ => (do
  prove ([[!s:A->bool p. FINITE s ==> FINITE {t | t SUBSET s /\ p t}]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC ([[{t:A->bool | t SUBSET s}]]) THEN
    ASM_SIMP_TAC [FINITE_POWERSET] THEN SET_TAC [])
  : ExceptT String IO thm).run
#eval FINITE_SUBSETS_RESTRICT

/- ------------------------------------------------------------------------- -/
/- Versions for additive real functions, where the additivity applies only   -/
/- to some specific subsets (e.g. cardinality of finite sets, measurable     -/
/- sets with bounded measure).                                               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 3
def INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED : thm := keep "INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED" fun _ => (do
  let lemma ← prove ([[{t | t SUBSET (a INSERT s) /\ P t} =
     {t | t SUBSET s /\ P t} UNION
     {a INSERT t |t| t SUBSET s /\ P(a INSERT t)}]])
     (REWRITE_TAC [SUBSET_INSERT_EXISTS] THEN
      GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN
      REWRITE_TAC [IN_ELIM_THM, IN_UNION] THEN MESON_TAC [])
  let h7 ← sr (← ExceptT.mk [[{s | P s /\ ~(s = e)} = {s | P s} DELETE e]])
  let h6 ← rr (← ExceptT.mk [[x - a:real = x + b <=> b = --a]])
  let h5 ← rr (← ExceptT.mk [[(fa + s) - fas:real = s + s' <=> fa - fas = s']])
  let h4 ← sr (← ExceptT.mk [[(s INTER t) UNION (t DIFF s) = t]])
  let h3 ← sr (← ExceptT.mk [[s UNION (t DIFF s) = s UNION t]])
  let h2 ← tt (← ExceptT.mk [[~(p /\ ~p)]])
  let h1 ← ms [HAS_SIZE] (← ExceptT.mk [[(!n s. s HAS_SIZE n ==> P s) ==> (!s. FINITE s ==> P s)]])
  prove ([[!P (f:(A->bool)->real) (A:I->bool) (x:I->(A->bool)).
        (!s t. P s /\ P t /\ DISJOINT s t
               ==> f(s UNION t) = f(s) + f(t)) /\
        P {} /\
        (!s t. P s /\ P t ==> P(s INTER t) /\ P(s UNION t) /\ P(s DIFF t)) /\
        FINITE A /\ (!a. a IN A ==> P(x a))
        ==> f(UNIONS(IMAGE x A)) =
            sum {B | B SUBSET A /\ ~(B = {})}
                (\B. (-- &1) pow (CARD B + 1) * f(INTERS(IMAGE x B)))]])
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [IMP_IMP, (← HolLight.GSYM CONJ_ASSOC)] THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [RIGHT_IMP_FORALL_THM] THEN
    REWRITE_TAC [IMP_IMP] THEN STRIP_TAC THEN
    MATCH_MP_TAC h1 THEN
    MATCH_MP_TAC num_WF THEN MATCH_MP_TAC num_INDUCTION THEN
    REWRITE_TAC [HAS_SIZE_CLAUSES, LEFT_IMP_EXISTS_THM] THEN CONJ_TAC THENL
     [DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [UNIONS_0, IMAGE_CLAUSES, SUBSET_EMPTY, h2] THEN
      ASM_REWRITE_TAC [EMPTY_GSPEC, SUM_CLAUSES] THEN REPEAT STRIP_TAC THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [([[{}:A->bool]]), ([[{}:A->bool]])])) THEN
      ASM_SIMP_TAC [UNION_EMPTY, DISJOINT_EMPTY] THEN REAL_ARITH_TAC2,
      ALL_TAC] THEN
    X_GEN_TAC ([[n:num]]) THEN DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [([[A0:I->bool]]), ([[a:I]]), ([[A:I->bool]])] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST1_TAC THEN X_GEN_TAC ([[x:I->A->bool]]) THEN
    REWRITE_TAC [FORALL_IN_INSERT] THEN STRIP_TAC THEN
    REWRITE_TAC [IMAGE_CLAUSES, UNIONS_INSERT] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC ([[(f(x a) + f(UNIONS (IMAGE (x:I->(A->bool)) A))) -
              f(x a INTER UNIONS (IMAGE x A)):real]]) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN ([[P(x a) /\ P(UNIONS(IMAGE (x:I->(A->bool)) A))]]) MP_TAC THENL
       [ASM_REWRITE_TAC [] THEN
        UNDISCH_TAC ([[!b. b IN A ==> P((x:I->(A->bool)) b)]]) THEN
        SUBGOAL_THEN ([[FINITE(A:I->bool)]]) MP_TAC THENL
         [ASM_MESON_TAC [HAS_SIZE], ALL_TAC] THEN
        SPEC_TAC (([[A:I->bool]]), ([[u:I->bool]])) THEN
        MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
        ASM_SIMP_TAC [IMAGE_CLAUSES, UNIONS_0, UNIONS_INSERT, FORALL_IN_INSERT],
        SPEC_TAC (([[UNIONS(IMAGE (x:I->(A->bool)) A)]]), ([[t:A->bool]])) THEN
        SPEC_TAC (([[(x:I->(A->bool)) a]]), ([[s:A->bool]])) THEN
        REPEAT STRIP_TAC THEN
        UNDISCH_TAC ([[!s t:A->bool. P s /\ P t /\ DISJOINT s t
                                 ==> f(s UNION t):real = f(s) + f(t)]]) THEN
        DISCH_THEN (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.ISPECL [([[s INTER t:A->bool]]), ([[t DIFF s:A->bool]])] th) THEN
       MP_TAC (← HolLight.ISPECL [([[s:A->bool]]), ([[t DIFF s:A->bool]])] th))) THEN
       ASM_SIMP_TAC [h3,
                    h4] THEN
       REPEAT (ANTS_TAC THENL [SET_TAC [], DISCH_TAC]) THEN ASM_REAL_ARITH_TAC],
      ALL_TAC] THEN
    REWRITE_TAC [INTER_UNIONS, SIMPLE_IMAGE, (← HolLight.GSYM IMAGE_o), o_DEF] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[n:num]])) THEN REWRITE_TAC [LT] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[A:I->bool]])) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.ISPEC ([[\s. (x:I->(A->bool)) a INTER x s]]) th) THEN
      MP_TAC (← HolLight.ISPEC ([[x:I->(A->bool)]]) th))) THEN
    ASM_SIMP_TAC [] THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN
    FIRST_ASSUM (ASSUME_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [HAS_SIZE]) THEN
    REWRITE_TAC [lemma] THEN
    HolCore.Lib.W (MP_TAC o HolLight.PART_MATCH (HolCore.Equal.lhand o HolCore.Kernel.rand) SUM_UNION o HolCore.Kernel.rand o HolLight.snd) THEN
    ANTS_TAC THENL
     [ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
      ASM_SIMP_TAC [FINITE_SUBSETS_RESTRICT, FINITE_IMAGE] THEN
      REWRITE_TAC [(← HolLight.GSYM SIMPLE_IMAGE_GEN)] THEN
      REWRITE_TAC [IN_DISJOINT, EXISTS_IN_GSPEC] THEN
      ONCE_REWRITE_TAC [CONJ_SYM] THEN
      REWRITE_TAC [EXISTS_IN_GSPEC] THEN HolLight.ASM SET_TAC [],
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC [NOT_INSERT_EMPTY, h5] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC ([[f((x:I->(A->bool)) a) +
              sum {B | B SUBSET A /\ ~(B = {})}
                  (\B. --(&1) pow (CARD B) *
                       f(INTERS(IMAGE x (a INSERT B))))]]) THEN
    CONJ_TAC THENL
     [REWRITE_TAC [h6] THEN
      REWRITE_TAC [(← HolLight.GSYM SUM_NEG)] THEN MATCH_MP_TAC SUM_EQ THEN
      REWRITE_TAC [IMAGE_CLAUSES, INTERS_INSERT, o_DEF, FORALL_IN_GSPEC] THEN
      REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC [REAL_POW_ADD, REAL_POW_1, REAL_MUL_RNEG, REAL_MUL_LNEG] THEN
      REWRITE_TAC [REAL_NEG_NEG, REAL_MUL_RID] THEN AP_TERM_TAC THEN
      AP_TERM_TAC THEN REWRITE_TAC [INTERS_IMAGE] THEN HolLight.ASM SET_TAC [],
      REWRITE_TAC [h7] THEN
      ASM_SIMP_TAC [SUM_DELETE_CASES, (← HolLight.GSYM DELETE), FINITE_POWERSET] THEN
      REWRITE_TAC [IN_ELIM_THM, EMPTY_SUBSET, IMAGE_CLAUSES] THEN
      GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.ONCE_DEPTH_CONV) [SIMPLE_IMAGE_GEN] THEN
      HolCore.Lib.W (MP_TAC o HolLight.PART_MATCH (HolCore.Equal.lhand o HolCore.Kernel.rand) SUM_IMAGE o HolCore.Kernel.rand o HolLight.snd) THEN
      ANTS_TAC THENL [HolLight.ASM SET_TAC [], DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC [o_DEF, INTERS_1, CARD_CLAUSES, real_pow, REAL_MUL_LID] THEN
      REWRITE_TAC [REAL_SUB_ADD2] THEN MATCH_MP_TAC SUM_EQ THEN
      REWRITE_TAC [FORALL_IN_GSPEC, REAL_POW_ADD, REAL_POW_1] THEN
      X_GEN_TAC ([[B:I->bool]]) THEN DISCH_TAC THEN
      SUBGOAL_THEN ([[FINITE(B:I->bool)]]) ASSUME_TAC THENL
       [ASM_MESON_TAC [FINITE_SUBSET], ALL_TAC] THEN
      ASM_SIMP_TAC [CARD_CLAUSES, REAL_POW_ADD, real_pow] THEN
      COND_CASES_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
      REWRITE_TAC [IMAGE_CLAUSES, real_pow] THEN REAL_ARITH_TAC2])
  : ExceptT String IO thm).run
#eval INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED

#eval phrase 4
def INCLUSION_EXCLUSION_REAL_RESTRICTED : thm := keep "INCLUSION_EXCLUSION_REAL_RESTRICTED" fun _ => (do
  prove ([[!P (f:(A->bool)->real) (A:(A->bool)->bool).
        (!s t. P s /\ P t /\ DISJOINT s t
               ==> f(s UNION t) = f(s) + f(t)) /\
        P {} /\
        (!s t. P s /\ P t ==> P(s INTER t) /\ P(s UNION t) /\ P(s DIFF t)) /\
        FINITE A /\ (!a. a IN A ==> P(a))
        ==> f(UNIONS A) =
            sum {B | B SUBSET A /\ ~(B = {})}
                (\B. (-- &1) pow (CARD B + 1) * f(INTERS B))]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[P:(A->bool)->bool]]), ([[f:(A->bool)->real]]),
                   ([[A:(A->bool)->bool]]), ([[\x:A->bool. x]])] INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED) THEN
    ASM_REWRITE_TAC [IMAGE_ID])
  : ExceptT String IO thm).run
#eval INCLUSION_EXCLUSION_REAL_RESTRICTED

/- ------------------------------------------------------------------------- -/
/- Versions for unrestrictedly additive functions.                           -/
/- ------------------------------------------------------------------------- -/

#eval phrase 5
def INCLUSION_EXCLUSION_REAL_INDEXED : thm := keep "INCLUSION_EXCLUSION_REAL_INDEXED" fun _ => (do
  prove ([[!(f:(A->bool)->real) (A:I->bool) (x:I->(A->bool)).
        (!s t. DISJOINT s t ==> f(s UNION t) = f(s) + f(t)) /\ FINITE A
        ==> f(UNIONS(IMAGE x A)) =
            sum {B | B SUBSET A /\ ~(B = {})}
                (\B. (-- &1) pow (CARD B + 1) * f(INTERS(IMAGE x B)))]])
   (MP_TAC (← HolLight.ISPEC ([[\x:A->bool. T]]) INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED) THEN
    REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval INCLUSION_EXCLUSION_REAL_INDEXED

#eval phrase 6
def INCLUSION_EXCLUSION_REAL : thm := keep "INCLUSION_EXCLUSION_REAL" fun _ => (do
  prove ([[!(f:(A->bool)->real) (A:(A->bool)->bool).
        (!s t. DISJOINT s t ==> f(s UNION t) = f(s) + f(t)) /\ FINITE A
        ==> f(UNIONS A) =
            sum {B | B SUBSET A /\ ~(B = {})}
                (\B. (-- &1) pow (CARD B + 1) * f(INTERS B))]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[f:(A->bool)->real]]), ([[A:(A->bool)->bool]]), ([[\x:A->bool. x]])] INCLUSION_EXCLUSION_REAL_INDEXED) THEN
    ASM_REWRITE_TAC [IMAGE_ID])
  : ExceptT String IO thm).run
#eval INCLUSION_EXCLUSION_REAL

/- ------------------------------------------------------------------------- -/
/- Special case of cardinality, the most common case.                        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 7
def INCLUSION_EXCLUSION : thm := keep "INCLUSION_EXCLUSION" fun _ => (do
  prove ([[!s:(A->bool)->bool.
        FINITE s /\ (!k. k IN s ==> FINITE k)
        ==> &(CARD(UNIONS s)) =
                sum {t | t SUBSET s /\ ~(t = {})}
                    (\t. (-- &1) pow (CARD t + 1) * &(CARD(INTERS t)))]])
   (REPEAT STRIP_TAC THEN MP_TAC (← HolLight.ISPECL [([[\s:A->bool. FINITE s]]), ([[\s:A->bool. &(CARD s)]]),
      ([[s:(A->bool)->bool]])] INCLUSION_EXCLUSION_REAL_RESTRICTED) THEN
    ASM_SIMP_TAC [FINITE_INTER, FINITE_UNION, FINITE_DIFF, FINITE_EMPTY] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    SIMP_TAC [CARD_UNION, DISJOINT, REAL_OF_NUM_ADD])
  : ExceptT String IO thm).run
#eval INCLUSION_EXCLUSION

/- ------------------------------------------------------------------------- -/
/- A more conventional form.                                                 -/
/- ------------------------------------------------------------------------- -/

#eval phrase 8
def INCLUSION_EXCLUSION_USUAL : thm := keep "INCLUSION_EXCLUSION_USUAL" fun _ => (do
  let h3 ← ar (← ExceptT.mk [[~(1 <= 0)]])
  let h2 ← ar (← ExceptT.mk [[1 <= a <=> ~(a = 0)]])
  let h1 ← ms [] (← ExceptT.mk [[s = t /\ sum t f = sum t g ==> sum s f = sum t g]])
  prove ([[!s:(A->bool)->bool.
        FINITE s /\ (!k. k IN s ==> FINITE k)
        ==> &(CARD(UNIONS s)) =
                sum (1..CARD s) (\n. (-- &1) pow (n + 1) *
                                     sum {t | t SUBSET s /\ t HAS_SIZE n}
                                         (\t. &(CARD(INTERS t))))]])
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [INCLUSION_EXCLUSION] THEN
    HolCore.Lib.W (MP_TAC o HolLight.PART_MATCH (HolCore.Equal.lhs o HolCore.Kernel.rand) (← HolLight.ISPEC ([[CARD]]) SUM_IMAGE_GEN) o
       HolCore.Equal.lhand o HolLight.snd) THEN
    ASM_SIMP_TAC [FINITE_SUBSETS_RESTRICT] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC h1 THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN
      REWRITE_TAC [IN_IMAGE, IN_NUMSEG, IN_ELIM_THM] THEN
      REWRITE_TAC [h2] THEN
      ASM_MESON_TAC [CHOOSE_SUBSET, CARD_SUBSET, FINITE_SUBSET, CARD_EQ_0,
                    HAS_SIZE],
      ALL_TAC] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC ([[n:num]]) THEN REWRITE_TAC [IN_NUMSEG] THEN
    STRIP_TAC THEN REWRITE_TAC [SUM_LMUL] THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [IN_ELIM_THM, HAS_SIZE] THEN
    GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM] THEN
    ASM_MESON_TAC [CARD_EQ_0, h3, FINITE_SUBSET])
  : ExceptT String IO thm).run
#eval INCLUSION_EXCLUSION_USUAL

/- ------------------------------------------------------------------------- -/
/- A combinatorial lemma about subsets of a finite set.                      -/
/- ------------------------------------------------------------------------- -/

#eval phrase 9
-- let FINITE_SUBSETS_RESTRICT = ... (rebinds FINITE_SUBSETS_RESTRICT)
def FINITE_SUBSETS_RESTRICT_2 : thm := keep "FINITE_SUBSETS_RESTRICT_2" fun _ => (do
  prove ([[!s:A->bool p. FINITE s ==> FINITE {t | t SUBSET s /\ p t}]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC ([[{t:A->bool | t SUBSET s}]]) THEN
    ASM_SIMP_TAC [FINITE_POWERSET] THEN SET_TAC [])
  : ExceptT String IO thm).run
#eval FINITE_SUBSETS_RESTRICT_2

#eval phrase 10
def CARD_ADJUST_LEMMA : thm := keep "CARD_ADJUST_LEMMA" fun _ => (do
  prove ([[!f:A->B s x y.
        FINITE s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        x = y + CARD (IMAGE f s)
        ==> x = y + CARD s]])
   (MESON_TAC [CARD_IMAGE_INJ])
  : ExceptT String IO thm).run
#eval CARD_ADJUST_LEMMA

#eval phrase 11
def CARD_SUBSETS_STEP : thm := keep "CARD_SUBSETS_STEP" fun _ => (do
  let h1 ← tt (← ExceptT.mk [[~(a /\ b) <=> b ==> ~a]])
  prove ([[!x:A s. FINITE s /\ ~(x IN s) /\ u SUBSET s
           ==> CARD {t | t SUBSET (x INSERT s) /\ u SUBSET t /\ ODD(CARD t)} =
                 CARD {t | t SUBSET s /\ u SUBSET t /\ ODD(CARD t)} +
                 CARD {t | t SUBSET s /\ u SUBSET t /\ EVEN(CARD t)} /\
               CARD {t | t SUBSET (x INSERT s) /\ u SUBSET t /\ EVEN(CARD t)} =
                 CARD {t | t SUBSET s /\ u SUBSET t /\ EVEN(CARD t)} +
                 CARD {t | t SUBSET s /\ u SUBSET t /\ ODD(CARD t)}]])
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (← HolLight.INST_TYPE [((← ExceptT.mk (HolCore.Parser.parse_type "A")), (← ExceptT.mk (HolCore.Parser.parse_type "B")))] CARD_ADJUST_LEMMA) THEN
    EXISTS_TAC ([[\u. (x:A) INSERT u]]) THEN
    ASM_SIMP_TAC [FINITE_SUBSETS_RESTRICT_2] THEN
    (CONJ_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
     CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC CARD_UNION_EQ THEN
     ASM_SIMP_TAC [FINITE_SUBSETS_RESTRICT_2, FINITE_INSERT] THEN CONJ_TAC THENL
      [REWRITE_TAC [EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN
       REWRITE_TAC [h1, FORALL_IN_IMAGE] THEN
       HolLight.ASM SET_TAC [],
       ALL_TAC] THEN
     GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN X_GEN_TAC ([[t:A->bool]]) THEN
     REWRITE_TAC [IN_ELIM_THM, IN_UNION, SUBSET_INSERT_EXISTS] THEN
     REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN
     REWRITE_TAC [RIGHT_OR_DISTRIB, LEFT_AND_EXISTS_THM] THEN AP_TERM_TAC THEN
     AP_TERM_TAC THEN GEN_REWRITE_TAC HolCore.Lib.I [FUN_EQ_THM] THEN
     X_GEN_TAC ([[v:A->bool]]) THEN
     ASM_CASES_TAC ([[t = (x:A) INSERT v]]) THEN ASM_REWRITE_TAC [] THEN
     ASM_CASES_TAC ([[(v:A->bool) SUBSET s]]) THEN ASM_REWRITE_TAC [] THEN
     BINOP_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
     ASM_MESON_TAC [CARD_CLAUSES, EVEN, NOT_ODD, FINITE_SUBSET, SUBSET] THEN
     ASM_MESON_TAC [CARD_CLAUSES, EVEN, NOT_ODD, FINITE_SUBSET, SUBSET]))
  : ExceptT String IO thm).run
#eval CARD_SUBSETS_STEP

#eval phrase 12
def CARD_SUBSUPERSETS_EVEN_ODD : thm := keep "CARD_SUBSUPERSETS_EVEN_ODD" fun _ => (do
  let h3 ← sr (← ExceptT.mk [[~((x:A) IN (u DELETE x))]])
  let h2 ← sr (← ExceptT.mk [[x IN s ==> s = x INSERT (s DELETE x)]])
  let h1 ← tt (← ExceptT.mk [[a /\ b /\ c <=> b /\ a /\ c]])
  prove ([[!s u:A->bool.
        FINITE u /\ s PSUBSET u
        ==> CARD {t | s SUBSET t /\ t SUBSET u /\ EVEN(CARD t)} =
            CARD {t | s SUBSET t /\ t SUBSET u /\ ODD(CARD t)}]])
   (ONCE_REWRITE_TAC [h1] THEN
    REPEAT GEN_TAC THEN WF_INDUCT_TAC ([[CARD(u:A->bool)]]) THEN
    REWRITE_TAC [PSUBSET_ALT] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[x:A]]) STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM (SUBST_ALL_TAC o HolLight.MATCH_MP h2) THEN
    MP_TAC h3 THEN
    ABBREV_TAC ([[v:A->bool = u DELETE x]]) THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[FINITE v /\ (s:A->bool) SUBSET v]]) STRIP_ASSUME_TAC THENL
     [HolLight.ASM SET_TAC [FINITE_INSERT], ALL_TAC] THEN
    ASM_SIMP_TAC [CARD_SUBSETS_STEP] THEN ASM_CASES_TAC ([[s:A->bool = v]]) THENL
     [REWRITE_TAC [CONJ_ASSOC, SUBSET_ANTISYM_EQ] THEN MATCH_ACCEPT_TAC ADD_SYM,
      ASM_SIMP_TAC [CARD_CLAUSES, LT, PSUBSET]])
  : ExceptT String IO thm).run
#eval CARD_SUBSUPERSETS_EVEN_ODD

#eval phrase 13
def SUM_ALTERNATING_CANCELS : thm := keep "SUM_ALTERNATING_CANCELS" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[x * &1 + x * -- &1 = &0]])
  prove ([[!s:A->bool f.
        FINITE s /\
        CARD {x | x IN s /\ EVEN(f x)} = CARD {x | x IN s /\ ODD(f x)}
        ==> sum s (\x. (-- &1) pow (f x)) = &0]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC ([[sum {x | x IN s /\ EVEN(f x)} (\x. (-- &1) pow (f x)) +
              sum {x:A | x IN s /\ ODD(f x)} (\x. (-- &1) pow (f x))]]) THEN
    CONJ_TAC THENL
     [CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC SUM_UNION_EQ THEN
      ASM_SIMP_TAC [EXTENSION, IN_ELIM_THM, IN_INTER, IN_UNION, NOT_IN_EMPTY] THEN
      REWRITE_TAC [(← HolLight.GSYM NOT_EVEN)] THEN MESON_TAC [],
      ALL_TAC] THEN
    ASM_SIMP_TAC [REAL_POW_NEG, REAL_POW_ONE, (← HolLight.GSYM NOT_EVEN), SUM_CONST,
                 FINITE_RESTRICT, h1])
  : ExceptT String IO thm).run
#eval SUM_ALTERNATING_CANCELS

/- ------------------------------------------------------------------------- -/
/- Hence a general "Moebius inversion" inclusion-exclusion principle.        -/
/- This "symmetric" form is from Ira Gessel: "Symmetric Inclusion-Exclusion" -/
/- ------------------------------------------------------------------------- -/

#eval phrase 14
def INCLUSION_EXCLUSION_SYMMETRIC : thm := keep "INCLUSION_EXCLUSION_SYMMETRIC" fun _ => (do
  let h3 ← tt (← ExceptT.mk [[(a /\ b) /\ c <=> b /\ a /\ c]])
  let h2 ← sr (← ExceptT.mk [[{x | x = a} = {a}]])
  let h1 ← sr (← ExceptT.mk [[s SUBSET t ==> (u SUBSET t /\ u SUBSET s <=> u SUBSET s)]])
  prove ([[!f g:(A->bool)->real.
    (!s. FINITE s
         ==> g(s) = sum {t | t SUBSET s} (\t. (-- &1) pow (CARD t) * f(t)))
    ==> !s. FINITE s
            ==> f(s) = sum {t | t SUBSET s} (\t. (-- &1) pow (CARD t) * g(t))]])
   (REPEAT STRIP_TAC THEN CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC ([[sum {t:A->bool | t SUBSET s}
                  (\t. (-- &1) pow (CARD t) *
                       sum {u | u IN {u | u SUBSET s} /\ u SUBSET t}
                           (\u. (-- &1) pow (CARD u) * f(u)))]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC [IN_ELIM_THM, h1] THEN
      ASM_MESON_TAC [FINITE_SUBSET],
      ALL_TAC] THEN
    REWRITE_TAC [(← HolLight.GSYM SUM_LMUL)] THEN
    HolCore.Lib.W (MP_TAC o HolLight.PART_MATCH (HolCore.Equal.lhand o HolCore.Kernel.rand) SUM_SUM_RESTRICT o HolCore.Equal.lhs o HolLight.snd) THEN
    ASM_SIMP_TAC [FINITE_POWERSET] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [SUM_RMUL, IN_ELIM_THM] THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC ([[sum {u | u SUBSET s} (\u:A->bool. if u = s then f(s) else &0)]]) THEN
    CONJ_TAC THENL [ALL_TAC, SIMP_TAC [SUM_DELTA, IN_ELIM_THM, SUBSET_REFL]] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC ([[u:A->bool]]) THEN
    REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THENL
     [REWRITE_TAC [SUBSET_ANTISYM_EQ, h2] THEN
      REWRITE_TAC [SUM_SING, REAL_MUL_ASSOC, (← HolLight.GSYM REAL_POW_ADD)] THEN
      REWRITE_TAC [REAL_POW_NEG, EVEN_ADD, REAL_POW_ONE, REAL_MUL_LID],
      ALL_TAC] THEN
    REWRITE_TAC [REAL_ENTIRE] THEN REPEAT DISJ1_TAC THEN
    MATCH_MP_TAC SUM_ALTERNATING_CANCELS THEN
    ASM_SIMP_TAC [FINITE_SUBSETS_RESTRICT_2, IN_ELIM_THM] THEN
    ONCE_REWRITE_TAC [h3] THEN
    MATCH_MP_TAC CARD_SUBSUPERSETS_EVEN_ODD THEN HolLight.ASM SET_TAC [])
  : ExceptT String IO thm).run
#eval INCLUSION_EXCLUSION_SYMMETRIC

/- ------------------------------------------------------------------------- -/
/- The more typical non-symmetric version.                                   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 15
def INCLUSION_EXCLUSION_MOBIUS : thm := keep "INCLUSION_EXCLUSION_MOBIUS" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[~(-- &1 = &0)]])
  prove ([[!f g:(A->bool)->real.
        (!s. FINITE s ==> g(s) = sum {t | t SUBSET s} f)
        ==> !s. FINITE s
                ==> f(s) = sum {t | t SUBSET s}
                               (\t. (-- &1) pow (CARD s - CARD t) * g(t))]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[\t. -- &1 pow CARD(t:A->bool) * f t]]), ([[g:(A->bool)->real]])] INCLUSION_EXCLUSION_SYMMETRIC) THEN
    REWRITE_TAC [REAL_MUL_ASSOC, (← HolLight.GSYM REAL_POW_ADD)] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC [EVEN_ADD, REAL_POW_ONE, REAL_POW_NEG, REAL_MUL_LID, ETA_AX],
      ALL_TAC] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[s:A->bool]])) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o HolLight.AP_TERM ([[(*) ((-- &1) pow (CARD(s:A->bool)))]])) THEN
    REWRITE_TAC [REAL_MUL_ASSOC, (← HolLight.GSYM REAL_POW_ADD), (← HolLight.GSYM MULT_2)] THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_POW_POW)] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC [REAL_POW_ONE, REAL_MUL_LID] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [(← HolLight.GSYM SUM_LMUL)] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC ([[u:A->bool]]) THEN REWRITE_TAC [IN_ELIM_THM, REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC [REAL_POW_SUB, h1, CARD_SUBSET] THEN
    REWRITE_TAC [REAL_POW_NEG, REAL_POW_ONE] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval INCLUSION_EXCLUSION_MOBIUS

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py; keep it in step with the `#eval`s above. -/
def ensure : IO Unit := once "Hol100.InclusionExclusion" do
  replay (
          SUBSET_INSERT_EXISTS)
  replay (
          FINITE_SUBSETS_RESTRICT)
  replay (
          INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED)
  replay (
          INCLUSION_EXCLUSION_REAL_RESTRICTED)
  replay (
          INCLUSION_EXCLUSION_REAL_INDEXED)
  replay (
          INCLUSION_EXCLUSION_REAL)
  replay (
          INCLUSION_EXCLUSION)
  replay (
          INCLUSION_EXCLUSION_USUAL)
  replay (
          FINITE_SUBSETS_RESTRICT_2)
  replay (
          CARD_ADJUST_LEMMA)
  replay (
          CARD_SUBSETS_STEP)
  replay (
          CARD_SUBSUPERSETS_EVEN_ODD)
  replay (
          SUM_ALTERNATING_CANCELS)
  replay (
          INCLUSION_EXCLUSION_SYMMETRIC)
  replay (
          INCLUSION_EXCLUSION_MOBIUS)
-- @@ENSURE END

end Hol100.InclusionExclusion
