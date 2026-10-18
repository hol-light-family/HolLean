/- File: HolExamples/Reduct.lean
Translation of HOL Light's Examples/reduct.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolExamples.Common
open HolCore.Kernel Session HolLight.Syntax HolExamples
open scoped HolLight
open SessionLibrary.RSTC

namespace HolExamples.Reduct

private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- General "reduction" properties of binary relations, -/

#eval phrase 1
-- needs "Library/rstc.ml";;
#eval SessionLibrary.RSTC.ensureRSTC

#eval phrase 2
-- Field of a binary relation.
unsafe def fld : thm := keep "fld" fun _ => new_definition
  [[fld(R) = {x | ?y. R x y \/ R y x}]]
#eval fld

#eval phrase 3
-- Normality of a term w.r.t. a reduction relation
unsafe def NORMAL : thm := keep "NORMAL" fun _ => new_definition
  [[NORMAL(R:A->A->bool) x <=> ~(?y. R x y)]]
#eval NORMAL

#eval phrase 4
-- Full Church-Rosser property.
unsafe def CR : thm := keep "CR" fun _ => new_definition
  [[CR(R:A->A->bool) <=> !x y1 y2. R x y1 /\ R x y2 ==> ?z. R y1 z /\ R y2 z]]
#eval CR

#eval phrase 5
-- Weak Church-Rosser property, i.e. the rejoining may take several steps.
unsafe def WCR : thm := keep "WCR" fun _ => new_definition
  [[WCR(R:A->A->bool) <=>
   !x y1 y2. R x y1 /\ R x y2 ==> ?z. RTC R y1 z /\ RTC R y2 z]]
#eval WCR

#eval phrase 6
-- (Weak) normalization: every term has a normal form.
unsafe def WN : thm := keep "WN" fun _ => new_definition
  [[WN(R:A->A->bool) <=> !x. ?y. RTC R x y /\ NORMAL(R) y]]
#eval WN

#eval phrase 7
-- Strong normalization: every reduction sequence terminates (Noetherian)
unsafe def SN : thm := keep "SN" fun _ => new_definition
  [[SN(R:A->A->bool) <=> ~(?seq. !n. R (seq n) (seq (SUC n)))]]
#eval SN

#eval phrase 8
-- Definition of a tree.
unsafe def TREE : thm := keep "TREE" fun _ => new_definition
  [[TREE(R:A->A->bool) <=>
        (!y. ~(TC R y y)) /\
        ?a. a IN fld(R) /\
            !y. y IN fld(R) ==> (y = a) \/ TC R a y /\ ?!x. R x y]]
#eval TREE

#eval phrase 9
-- Local finiteness (finitely branching).
unsafe def LF : thm := keep "LF" fun _ => new_definition
  [[LF(R:A->A->bool) <=> !x. FINITE {y | R x y}]]
#eval LF

#eval phrase 10
-- Wellfoundedness apparatus for SN relations.
unsafe def SN_WF : thm := keep "SN_WF" fun _ => (do
  prove ([[!R:A->A->bool. SN(R) <=> WF(INV R)]])
   (REWRITE_TAC [SN, WF_DCHAIN, INV])
  : ExceptT String IO thm).run
#eval SN_WF

#eval phrase 11
unsafe def SN_PRESERVE : thm := keep "SN_PRESERVE" fun _ => (do
  prove ([[!R:A->A->bool. SN(R) <=> !P. (!x. P x ==> ?y. P y /\ R x y) ==> ~(?x. P x)]])
   (REWRITE_TAC [SN_WF, WF, INV] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval SN_PRESERVE

#eval phrase 12
unsafe def SN_NOETHERIAN : thm := keep "SN_NOETHERIAN" fun _ => (do
  prove ([[!R:A->A->bool. SN(R) <=> !P. (!x. (!y. R x y ==> P y) ==> P x) ==> !x. P x]])
   (REWRITE_TAC [WF_IND, SN_WF, INV])
  : ExceptT String IO thm).run
#eval SN_NOETHERIAN

#eval phrase 13
-- Normality, weak or strong normalization preserved by transitive closure.
unsafe def NORMAL_TC : thm := keep "NORMAL_TC" fun _ => (do
  prove ([[!R:A->A->bool. NORMAL(TC R) x <=> NORMAL(R) x]])
   (REWRITE_TAC [NORMAL] THEN MESON_TAC [TC_CASES_R, TC_INC])
  : ExceptT String IO thm).run
#eval NORMAL_TC

#eval phrase 14
unsafe def NORMAL_RTC : thm := keep "NORMAL_RTC" fun _ => (do
  prove ([[!R:A->A->bool. NORMAL(R) x ==> !y. RTC R x y <=> (x = y)]])
   (ONCE_REWRITE_TAC [(← HolLight.GSYM NORMAL_TC)] THEN
    REWRITE_TAC [NORMAL, RTC, RC_EXPLICIT] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval NORMAL_RTC

#eval phrase 15
unsafe def WN_TC : thm := keep "WN_TC" fun _ => (do
  prove ([[!R:A->A->bool. WN(TC R) <=> WN R]])
   (REWRITE_TAC [WN, NORMAL_TC, RTC, TC_IDEMP])
  : ExceptT String IO thm).run
#eval WN_TC

#eval phrase 16
unsafe def SN_TC : thm := keep "SN_TC" fun _ => (do
  prove ([[!R:A->A->bool. SN(TC R) <=> SN R]])
   (GEN_TAC THEN REWRITE_TAC [SN_WF, (← HolLight.GSYM TC_INV), WF_TC])
  : ExceptT String IO thm).run
#eval SN_TC

#eval phrase 17
-- Strong normalization implies normalization
unsafe def SN_WN : thm := keep "SN_WN" fun _ => (do
  prove ([[!R:A->A->bool. SN(R) ==> WN(R)]])
   (GEN_TAC THEN REWRITE_TAC [SN_WF, WF, WN] THEN DISCH_TAC THEN
    X_GEN_TAC [[a:A]] THEN POP_ASSUM (MP_TAC o SPEC [[\y:A. RTC R a y]]) THEN
    REWRITE_TAC [INV, NORMAL] THEN MESON_TAC [RTC_REFL, RTC_TRANS_L])
  : ExceptT String IO thm).run
#eval SN_WN

#eval phrase 18
-- Reflexive closure preserves Church-Rosser property (pretty trivial)
unsafe def RC_CR : thm := keep "RC_CR" fun _ => (do
  prove ([[!R:A->A->bool. CR(R) ==> CR(RC R)]])
   (REWRITE_TAC [CR, RC_EXPLICIT] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval RC_CR

#eval phrase 19
-- The strip lemma.
unsafe def STRIP_LEMMA : thm := keep "STRIP_LEMMA" fun _ => (do
  prove ([[!R S. (!x y1 y2.    R x y1 /\ S x y2 ==> ?z:A. S y1 z /\    R y2 z) ==>
         (!x y1 y2. TC R x y1 /\ S x y2 ==> ?z:A. S y1 z /\ TC R y2 z)]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [TAUT [[a /\ b ==> c <=> a ==> (b ==> c)]]] THEN
    REWRITE_TAC [(← HolLight.GSYM RIGHT_IMP_FORALL_THM)] THEN
    MATCH_MP_TAC TC_INDUCT THEN ASM_MESON_TAC [TC_INC, TC_TRANS])
  : ExceptT String IO thm).run
#eval STRIP_LEMMA

#eval phrase 20
-- Transitive closure preserves Church-Rosser property.
unsafe def TC_CR : thm := keep "TC_CR" fun _ => (do
  prove ([[!R:A->A->bool. CR(R) ==> CR(TC R)]])
   (GEN_TAC THEN REWRITE_TAC [CR] THEN DISCH_TAC THEN
    MATCH_MP_TAC STRIP_LEMMA THEN REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC [CONJ_SYM] THEN
    RULE_INDUCT_TAC STRIP_LEMMA THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval TC_CR

#eval phrase 21
-- Reflexive transitive closure preserves Church-Rosser property.
unsafe def RTC_CR : thm := keep "RTC_CR" fun _ => (do
  prove ([[!R:A->A->bool. CR(R) ==> CR(RTC R)]])
   (REWRITE_TAC [RTC] THEN MESON_TAC [RC_CR, TC_CR])
  : ExceptT String IO thm).run
#eval RTC_CR

#eval phrase 22
-- Equivalent Church-Rosser property for the equivalence relation.
unsafe def STC_CR : thm := keep "STC_CR" fun _ => (do
  prove ([[!R:A->A->bool. CR(RTC R) <=>
        !x y. RSTC R x y ==> ?z:A. RTC R x z /\ RTC R y z]])
   (GEN_TAC THEN REWRITE_TAC [CR] THEN EQ_TAC THENL
     [DISCH_TAC THEN MATCH_MP_TAC RSTC_INDUCT THEN
      ASM_MESON_TAC [RTC_REFL, RTC_INC, RTC_TRANS],
      MESON_TAC [RSTC_INC_RTC, RSTC_SYM, RSTC_TRANS]])
  : ExceptT String IO thm).run
#eval STC_CR

#eval phrase 23
-- Under normalization, Church-Rosser is equivalent to uniqueness of NF
unsafe def NORM_CR : thm := keep "NORM_CR" fun _ => (do
  prove ([[!R:A->A->bool. WN(R) ==>
     (CR(RTC R) <=> (!x y1 y2. RTC R x y1 /\ NORMAL(R) y1 /\
                               RTC R x y2 /\ NORMAL(R) y2 ==> (y1 = y2)))]])
   (GEN_TAC THEN REWRITE_TAC [CR, WN] THEN DISCH_TAC THEN EQ_TAC THENL
     [MESON_TAC [NORMAL_RTC], ASM_MESON_TAC [RTC_TRANS]])
  : ExceptT String IO thm).run
#eval NORM_CR

#eval phrase 24
-- Normalizing and Church-Rosser iff every term has a unique normal form
unsafe def CR_NORM : thm := keep "CR_NORM" fun _ => (do
  prove ([[!R:A->A->bool. WN(R) /\ CR(RTC R) <=> !x. ?!y. RTC R x y /\ NORMAL(R) y]])
   (GEN_TAC THEN ONCE_REWRITE_TAC [EXISTS_UNIQUE_THM] THEN
    REWRITE_TAC [FORALL_AND_THM, (← HolLight.GSYM WN)] THEN
    MATCH_MP_TAC (TAUT [[(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)]]) THEN
    DISCH_THEN (fun th => HolLight.tactic_of do pure (REWRITE_TAC [(← HolLight.MATCH_MP NORM_CR th)])) THEN
    REWRITE_TAC [CONJ_ASSOC])
  : ExceptT String IO thm).run
#eval CR_NORM

#eval phrase 25
-- Newman's lemma.
unsafe def NEWMAN_LEMMA : thm := keep "NEWMAN_LEMMA" fun _ => (do
  prove ([[!R:A->A->bool. SN(R) /\ WCR(R) ==> CR(RTC R)]])
   (GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP SN_WN) THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
      let r ← HolLight.REWRITE_RULE [WN] th
      pure (ASSUME_TAC r THEN MP_TAC th)) THEN
    DISCH_THEN (fun th => HolLight.tactic_of do pure (REWRITE_TAC [(← HolLight.MATCH_MP NORM_CR th)])) THEN
    FIRST_ASSUM (MATCH_MP_TAC o HolLight.REWRITE_RULE [WF_IND, SN_WF]) THEN
    REWRITE_TAC [INV] THEN X_GEN_TAC [[x:A]] THEN REPEAT STRIP_TAC THEN
    MAP_EVERY UNDISCH_TAC [ [[RTC R (x:A) y1]], [[RTC R (x:A) y2]] ] THEN
    ONCE_REWRITE_TAC [RTC_CASES_R] THEN
    DISCH_THEN (DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_TAC [[z2:A]])) THEN
    DISCH_THEN (DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_TAC [[z1:A]])) THENL
     [ASM_MESON_TAC [], ASM_MESON_TAC [NORMAL], ASM_MESON_TAC [NORMAL], ALL_TAC] THEN
    FIRST_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [WCR]) THEN
    ASM_MESON_TAC [RTC_TRANS])
  : ExceptT String IO thm).run
#eval NEWMAN_LEMMA

#eval phrase 26
-- A variant of Koenig's lemma.
unsafe def LF_TC_FINITE : thm := keep "LF_TC_FINITE" fun _ => (do
  prove ([[!R. LF(R) /\ SN(R) ==> !x:A. FINITE {y | TC(R) x y}]])
   (GEN_TAC THEN REWRITE_TAC [LF] THEN STRIP_TAC THEN
    FIRST_ASSUM (MATCH_MP_TAC o HolLight.REWRITE_RULE [WF_IND, SN_WF, INV]) THEN
    GEN_TAC THEN DISCH_TAC THEN SUBGOAL_THEN
      ([[{y:A | TC(R) x y} = {y | R x y} UNION
                           (UNIONS { s | ?z. R x z /\ (s = {y | TC(R) z y})})]])
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_UNION, IN_UNIONS] THEN
      REWRITE_TAC [IN_ELIM_THM] THEN REWRITE_TAC [IN] THEN
      GEN_TAC THEN GEN_REWRITE_TAC HolLight.LAND_CONV [TC_CASES_R] THEN
      AP_TERM_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC [], ALL_TAC] THEN
    ASM_REWRITE_TAC [FINITE_UNION, FINITE_UNIONS] THEN CONJ_TAC THENL
     [MP_TAC (ISPECL [ [[\z:A. {y | TC R z y}]], [[{z | (R:A->A->bool) x z}]] ]
                    FINITE_IMAGE_EXPAND) THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [IN, IN_ELIM_THM],
      GEN_TAC THEN GEN_REWRITE_TAC HolLight.LAND_CONV [IN_ELIM_THM] THEN
      REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC])
  : ExceptT String IO thm).run
#eval LF_TC_FINITE

#eval phrase 27
unsafe def SN_NOLOOP : thm := keep "SN_NOLOOP" fun _ => (do
  prove ([[!R:A->A->bool. SN(R) ==> !z. ~(TC(R) z z)]])
   (GEN_TAC THEN ONCE_REWRITE_TAC [(← HolLight.GSYM SN_TC)] THEN
    SPEC_TAC ([[TC(R:A->A->bool)]], [[R:A->A->bool]]) THEN
    GEN_TAC THEN REWRITE_TAC [SN_WF, INV, WF] THEN
    DISCH_THEN (fun th => GEN_TAC THEN MP_TAC th) THEN
    DISCH_THEN (MP_TAC o SPEC [[\x:A. x = z]]) THEN
    REWRITE_TAC [] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval SN_NOLOOP

#eval phrase 28
unsafe def RELPOW_RTC : thm := keep "RELPOW_RTC" fun _ => (do
  prove ([[!R:A->A->bool. !n x y. RELPOW n R x y ==> RTC(R) x y]])
   (GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [RELPOW] THEN
    ASM_MESON_TAC [RTC_REFL, RTC_TRANS_L])
  : ExceptT String IO thm).run
#eval RELPOW_RTC

#eval phrase 29
unsafe def RTC_TC_LEMMA : thm := keep "RTC_TC_LEMMA" fun _ => (do
  prove ([[!R x:A. {y:A | RTC(R) x y} = x INSERT {y:A | TC(R) x y}]])
   (REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_INSERT] THEN
    REWRITE_TAC [RTC, RC_EXPLICIT, DISJ_ACI, EQ_SYM_EQ])
  : ExceptT String IO thm).run
#eval RTC_TC_LEMMA

#eval phrase 30
unsafe def HAS_SIZE_SUBSET : thm := keep "HAS_SIZE_SUBSET" fun _ => (do
  prove ([[!s:A->bool t m n. s HAS_SIZE m /\ t HAS_SIZE n /\ s SUBSET t ==> m <= n]])
   (REWRITE_TAC [HAS_SIZE] THEN MESON_TAC [CARD_SUBSET])
  : ExceptT String IO thm).run
#eval HAS_SIZE_SUBSET

#eval phrase 31
unsafe def FC_FINITE_BOUND_LEMMA : thm := keep "FC_FINITE_BOUND_LEMMA" fun _ => (do
  prove ([[!R. (!z. ~(TC R z z))
       ==> !n. {y:A | RTC(R) x y} HAS_SIZE n
               ==> !m y. RELPOW m R x y ==> m <= n]])
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (X_CHOOSE_THEN ([[f:num->A]]) STRIP_ASSUME_TAC o
      HolLight.REWRITE_RULE [RELPOW_SEQUENCE]) THEN
    SUBGOAL_THEN ([[!i. i <= m ==> RELPOW i R (x:A) (f i)]]) ASSUME_TAC THENL
     [INDUCT_TAC THEN ASM_REWRITE_TAC [RELPOW] THEN
      REWRITE_TAC [LE_SUC_LT] THEN ASM_MESON_TAC [LT_IMP_LE], ALL_TAC] THEN
    SUBGOAL_THEN ([[{z:A | ?i:num. i < m /\ (z = f i)} SUBSET {y | RTC R x y}]])
    ASSUME_TAC THENL
     [REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC [RELPOW_RTC, LT_IMP_LE],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!p. p <= m ==> {z:A | ?i. i < p /\ (z = f i)} HAS_SIZE p]])
    (fun th => HolLight.tactic_of do
      let r ← HolLight.MATCH_MP th (← Session.SPEC ([[m:num]]) LE_REFL)
      pure (ASSUME_TAC r)) THENL
     [ALL_TAC,
      MATCH_MP_TAC HAS_SIZE_SUBSET THEN
      EXISTS_TAC [[{z:A | ?i. i < m /\ (z = f i)}]] THEN
      EXISTS_TAC [[{y:A | RTC(R) x y}]] THEN ASM_REWRITE_TAC []] THEN
    INDUCT_TAC THEN DISCH_TAC THENL
     [REWRITE_TAC [HAS_SIZE_0, EXTENSION, NOT_IN_EMPTY, IN_ELIM_THM, LT],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[{z:A | ?i. i < SUC p /\ (z = f i)} =
                  f(p) INSERT {z | ?i. i < p /\ (z = f i)}]])
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_INSERT, IN_ELIM_THM] THEN
      REWRITE_TAC [LT] THEN MESON_TAC [], ALL_TAC] THEN
    REWRITE_TAC [HAS_SIZE, CARD_CLAUSES, SUC_INJ] THEN
    SUBGOAL_THEN ([[{z:A | ?i. i < p /\ (z = f i)} HAS_SIZE p]]) MP_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC [[SUC p <= m]] THEN ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [HAS_SIZE] THEN STRIP_TAC THEN
    FIRST_ASSUM (fun th => HolLight.tactic_of do
      let c ← HolLight.CONJUNCT2 CARD_CLAUSES
      let r ← HolLight.MATCH_MP c th
      pure (REWRITE_TAC [r])) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [FINITE_INSERT] THEN
    UNDISCH_TAC [[f p IN {z:A | ?i:num. i < p /\ (z = f i)}]] THEN
    CONV_TAC HolLight.CONTRAPOS_CONV THEN DISCH_TAC THEN
    REWRITE_TAC [IN_ELIM_THM, NOT_EXISTS_THM] THEN
    X_GEN_TAC [[q:num]] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    SUBGOAL_THEN ([[TC(R) ((f:num->A) q) (f p)]]) (fun th => ASM_MESON_TAC [th]) THEN
    UNDISCH_TAC [[SUC p <= m]] THEN UNDISCH_TAC [[q < p]] THEN
    REWRITE_TAC [LT_EXISTS] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[d:num]]) SUBST1_TAC) THEN
    SPEC_TAC ([[d:num]], [[d:num]]) THEN INDUCT_TAC THENL
     [REWRITE_TAC [ADD_CLAUSES] THEN DISCH_TAC THEN
      MATCH_MP_TAC TC_INC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC [[SUC (SUC q) <= m]] THEN ARITH_TAC,
      DISCH_TAC THEN MATCH_MP_TAC TC_TRANS_L THEN
      EXISTS_TAC [[(f:num->A)(q + SUC d)]] THEN CONJ_TAC THENL
       [ALL_TAC, REWRITE_TAC [ADD_CLAUSES]] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC [[SUC (q + SUC (SUC d)) <= m]] THEN ARITH_TAC])
  : ExceptT String IO thm).run
#eval FC_FINITE_BOUND_LEMMA

#eval phrase 32
unsafe def FC_FINITE_BOUND : thm := keep "FC_FINITE_BOUND" fun _ => (do
  prove ([[!R (x:A). FINITE {y | RTC(R) x y} /\
             (!z. ~(TC R z z))
             ==> ?N. !n y. RELPOW n R x y ==> n <= N]])
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_TAC THEN EXISTS_TAC [[CARD {y:A | RTC(R) x y}]] THEN
    FIRST_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP FC_FINITE_BOUND_LEMMA) THEN
    ASM_REWRITE_TAC [HAS_SIZE])
  : ExceptT String IO thm).run
#eval FC_FINITE_BOUND

#eval phrase 33
unsafe def BOUND_SN : thm := keep "BOUND_SN" fun _ => (do
  prove ([[!R. (!x:A. ?N. !n y. RELPOW n R x y ==> n <= N) ==> SN(R)]])
   (GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [SN_WF, WF_DCHAIN, INV] THEN
    DISCH_THEN (X_CHOOSE_TAC [[f:num->A]]) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC [[(f:num->A) 0]]) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[N:num]])
     (MP_TAC o SPECL [ [[SUC N]], [[f(SUC N):A]] ])) THEN
    REWRITE_TAC [(← HolLight.GSYM NOT_LT), LT] THEN
    SUBGOAL_THEN ([[!n. RELPOW n R (f 0 :A) (f n)]]) (fun th => REWRITE_TAC [th]) THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC [RELPOW] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval BOUND_SN

#eval phrase 34
unsafe def LF_SN_BOUND : thm := keep "LF_SN_BOUND" fun _ => (do
  prove ([[!R. LF(R) ==> (SN(R) <=> !x:A. ?N. !n y. RELPOW n R x y ==> n <= N)]])
   (GEN_TAC THEN DISCH_TAC THEN EQ_TAC THEN REWRITE_TAC [BOUND_SN] THEN
    DISCH_TAC THEN GEN_TAC THEN MATCH_MP_TAC FC_FINITE_BOUND THEN CONJ_TAC THENL
     [SPEC_TAC ([[x:A]], [[x:A]]) THEN REWRITE_TAC [RTC_TC_LEMMA, FINITE_INSERT] THEN
      MATCH_MP_TAC LF_TC_FINITE THEN ASM_REWRITE_TAC [],
      MATCH_MP_TAC SN_NOLOOP THEN ASM_REWRITE_TAC []])
  : ExceptT String IO thm).run
#eval LF_SN_BOUND

#eval phrase 35
-- Koenig's lemma.
unsafe def TREE_FLD : thm := keep "TREE_FLD" fun _ => (do
  prove ([[!R. TREE(R) ==> ?a:A. fld(R) = {y | RTC(R) a y}]])
   (GEN_TAC THEN REWRITE_TAC [TREE] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN ([[a:A]]) STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC [[a:A]] THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
    X_GEN_TAC [[x:A]] THEN EQ_TAC THENL
     [DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN REWRITE_TAC [RTC, RC_EXPLICIT] THEN
      MESON_TAC [],
      ONCE_REWRITE_TAC [RTC_CASES_L] THEN REPEAT (POP_ASSUM MP_TAC) THEN
      REWRITE_TAC [fld] THEN SET_TAC []])
  : ExceptT String IO thm).run
#eval TREE_FLD

#eval phrase 36
unsafe def KOENIG_LEMMA : thm := keep "KOENIG_LEMMA" fun _ => (do
  prove ([[!R:A->A->bool. TREE(R) /\ LF(R) /\ SN(R) ==> FINITE (fld R)]])
   (GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[a:A]]) SUBST1_TAC o HolLight.MATCH_MP TREE_FLD) THEN
    REWRITE_TAC [RTC_TC_LEMMA, FINITE_INSERT] THEN
    SPEC_TAC ([[a:A]], [[a:A]]) THEN MATCH_MP_TAC LF_TC_FINITE THEN
    ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval KOENIG_LEMMA

#eval phrase 37
-- Rephrasing in terms of joinability.
unsafe def JOINABLE : thm := keep "JOINABLE" fun _ => new_definition
  [[JOINABLE R s t <=> ?u. RTC R s u /\ RTC R t u]]
#eval JOINABLE

#eval phrase 38
unsafe def JOINABLE_REFL : thm := keep "JOINABLE_REFL" fun _ => (do
  prove ([[!R t. JOINABLE R t t]])
   (REWRITE_TAC [JOINABLE] THEN MESON_TAC [RTC_CASES])
  : ExceptT String IO thm).run
#eval JOINABLE_REFL

#eval phrase 39
unsafe def JOINABLE_SYM : thm := keep "JOINABLE_SYM" fun _ => (do
  prove ([[!R s t. JOINABLE R s t <=> JOINABLE R t s]])
   (REWRITE_TAC [JOINABLE] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval JOINABLE_SYM

#eval phrase 40
unsafe def JOINABLE_TRANS_R : thm := keep "JOINABLE_TRANS_R" fun _ => (do
  prove ([[!R s t u. R s t /\ JOINABLE R t u ==> JOINABLE R s u]])
   (REWRITE_TAC [JOINABLE] THEN MESON_TAC [RTC_CASES_R])
  : ExceptT String IO thm).run
#eval JOINABLE_TRANS_R

#eval phrase 41
unsafe def CR_RSTC_JOINABLE : thm := keep "CR_RSTC_JOINABLE" fun _ => (do
  prove ([[!R. CR(RTC R) ==> !x:A y. RSTC(R) x y <=> JOINABLE(R) x y]])
   (GEN_TAC THEN REWRITE_TAC [STC_CR, JOINABLE] THEN
    ASM_MESON_TAC [RSTC_TRANS, RSTC_SYM, RSTC_INC_RTC])
  : ExceptT String IO thm).run
#eval CR_RSTC_JOINABLE

#eval phrase 42
-- CR is equivalent to transitivity of joinability.
unsafe def JOINABLE_TRANS : thm := keep "JOINABLE_TRANS" fun _ => (do
  prove ([[!R. CR(RTC R) <=>
       !x y z. JOINABLE(R) x y /\ JOINABLE(R) y z ==> JOINABLE(R) x z]])
   (REWRITE_TAC [CR, JOINABLE] THEN MESON_TAC [RTC_REFL, RTC_TRANS, RTC_SYM])
  : ExceptT String IO thm).run
#eval JOINABLE_TRANS

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py from the `#eval`s above. -/
unsafe def ensure : IO Unit := once "HolExamples.Reduct" do
  replay (
          SessionLibrary.RSTC.ensureRSTC)
  replay (
          fld)
  replay (
          NORMAL)
  replay (
          CR)
  replay (
          WCR)
  replay (
          WN)
  replay (
          SN)
  replay (
          TREE)
  replay (
          LF)
  replay (
          SN_WF)
  replay (
          SN_PRESERVE)
  replay (
          SN_NOETHERIAN)
  replay (
          NORMAL_TC)
  replay (
          NORMAL_RTC)
  replay (
          WN_TC)
  replay (
          SN_TC)
  replay (
          SN_WN)
  replay (
          RC_CR)
  replay (
          STRIP_LEMMA)
  replay (
          TC_CR)
  replay (
          RTC_CR)
  replay (
          STC_CR)
  replay (
          NORM_CR)
  replay (
          CR_NORM)
  replay (
          NEWMAN_LEMMA)
  replay (
          LF_TC_FINITE)
  replay (
          SN_NOLOOP)
  replay (
          RELPOW_RTC)
  replay (
          RTC_TC_LEMMA)
  replay (
          HAS_SIZE_SUBSET)
  replay (
          FC_FINITE_BOUND_LEMMA)
  replay (
          FC_FINITE_BOUND)
  replay (
          BOUND_SN)
  replay (
          LF_SN_BOUND)
  replay (
          TREE_FLD)
  replay (
          KOENIG_LEMMA)
  replay (
          JOINABLE)
  replay (
          JOINABLE_REFL)
  replay (
          JOINABLE_SYM)
  replay (
          JOINABLE_TRANS_R)
  replay (
          CR_RSTC_JOINABLE)
  replay (
          JOINABLE_TRANS)
-- @@ENSURE END

end HolExamples.Reduct
