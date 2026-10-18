/- File: HolLogicArith/GivenSem.lean
Translation of HOL Light's Logic/givensem.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolLogicArith.Positive
open HolCore.Kernel Session HolLight.Syntax HolLogicArith
open scoped HolLight
open HolLogicArith.Fol
open HolLogicArith.Prenex
open HolLogicArith.Skolem
open HolLogicArith.FolProp
open HolLogicArith.Canon
open HolLogicArith.Fole
open HolLogicArith.Herbrand
open HolLogicArith.Unif
open HolLogicArith.Resolution
open HolLogicArith.Given
open HolLogicArith.Linear
open HolLogicArith.Support
open HolLogicArith.Positive

namespace HolLogicArith.GivenSem

/- List definitions/theorems used below are exposed by Session as fields of
   the `listDefs`/`listThms1`/`listThms2` bundles; alias the ones we need. -/
private unsafe def LENGTH : thm := Session.listDefs.LENGTH
private unsafe def ITLIST : thm := Session.listDefs.ITLIST
private unsafe def MEM : thm := Session.listDefs.MEM
private unsafe def FILTER : thm := Session.listDefs.FILTER
private unsafe def EL : thm := Session.listDefs.EL
private unsafe def HD : thm := Session.listDefs.HD
private unsafe def TL : thm := Session.listDefs.TL
private unsafe def list_CASES : thm := Session.listThms1.list_CASES
private unsafe def NOT_CONS_NIL : thm := Session.listThms1.NOT_CONS_NIL
private unsafe def MEM_EL : thm := Session.listThms2.MEM_EL

#eval HolLogicArith.Positive.ensure

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- `new_recursive_definition` lifted into `ExceptT String IO`. -/
private unsafe def newRec (ax : thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (Session.new_recursive_definition ax tm)

#eval phrase 1
unsafe def HOLDS_INTERP_SUBSUME : thm := keep "HOLDS_INTERP_SUBSUME" fun _ => (do
  prove ([[clause cl /\ clause cl' /\ (!v. holds M v (interp cl)) /\ cl subsumes cl'
   ==> !v:num->A. holds M v (interp cl')]])
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC oTIO HolLight.GEN_REWRITE_RULE HolCore.Lib.I [subsumes]) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[i:num->term]]) MP_TAC) THEN
    UNDISCH_TAC [[!v:num->A. holds M v (interp cl)]] THEN
    ASM_SIMP_TAC [CLAUSE_FINITE, HOLDS_INTERP] THEN
    MESON_TAC [IN_IMAGE, SUBSET, HOLDS_FORMSUBST])
  : ExceptT String IO thm).run
#eval HOLDS_INTERP_SUBSUME

#eval phrase 2
unsafe def isaresolvent_sem : thm := keep "isaresolvent_sem" fun _ => new_definition
  [[isaresolvent_sem M cl (c1,c2) <=>
        isaresolvent cl (c1,c2) /\
        (~(!v:num->num. holds M v (interp c1)) \/
         ~(!v. holds M v (interp c2)))]]
#eval isaresolvent_sem

#eval phrase 3
unsafe def allresolvents_sem : thm := keep "allresolvents_sem" fun _ => new_definition
  [[allresolvents_sem M s1 s2 =
        {c | ?c1 c2. c1 IN s1 /\ c2 IN s2 /\ isaresolvent_sem M c (c1,c2)}]]
#eval allresolvents_sem

#eval phrase 4
unsafe def allntresolvents_sem : thm := keep "allntresolvents_sem" fun _ => new_definition
  [[allntresolvents_sem M s1 s2 =
        {r | r IN allresolvents_sem M s1 s2 /\ ~(tautologous r)}]]
#eval allntresolvents_sem

#eval phrase 5
unsafe def ISARESOLVENT_SEM_SYM : thm := keep "ISARESOLVENT_SEM_SYM" fun _ => (do
  prove ([[!c1 c2 cl.
        clause c1 /\ clause c2 /\ isaresolvent_sem M cl (c2,c1)
        ==> ?cl'. isaresolvent_sem M cl' (c1,c2) /\ cl' subsumes cl]])
   (REWRITE_TAC [isaresolvent_sem] THEN MESON_TAC [ISARESOLVENT_SYM])
  : ExceptT String IO thm).run
#eval ISARESOLVENT_SEM_SYM

#eval phrase 6
unsafe def ALLRESOLVENTS_SEM_SYM : thm := keep "ALLRESOLVENTS_SEM_SYM" fun _ => (do
  prove ([[(!c. c IN A ==> clause c) /\ (!c. c IN B ==> clause c)
   ==> (allresolvents_sem M A B) SUBSUMES (allresolvents_sem M B A)]])
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [SUBSUMES, allresolvents_sem, IN_ELIM_THM] THEN
    X_GEN_TAC [[cl:form->bool]] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[c2:form->bool]])
          (X_CHOOSE_THEN ([[c1:form->bool]]) STRIP_ASSUME_TAC)) THEN
    REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN EXISTS_TAC [[c1:form->bool]] THEN
    ASM_REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN EXISTS_TAC [[c2:form->bool]] THEN
    ASM_SIMP_TAC [ISARESOLVENT_SEM_SYM])
  : ExceptT String IO thm).run
#eval ALLRESOLVENTS_SEM_SYM

#eval phrase 7
unsafe def ALLRESOLVENTS_SEM_UNION : thm := keep "ALLRESOLVENTS_SEM_UNION" fun _ => (do
  prove ([[(allresolvents_sem M (A UNION B) C =
        (allresolvents_sem M A C) UNION (allresolvents_sem M B C)) /\
   (allresolvents_sem M A (B UNION C) =
        (allresolvents_sem M A B) UNION (allresolvents_sem M A C))]])
   (REWRITE_TAC [EXTENSION, allresolvents_sem, IN_ELIM_THM, IN_UNION] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval ALLRESOLVENTS_SEM_UNION

#eval phrase 8
unsafe def ALLRESOLVENTS_SEM_STEP : thm := keep "ALLRESOLVENTS_SEM_STEP" fun _ => (do
  prove ([[(!c. c IN B ==> clause(c)) /\
   (!c. c IN C ==> clause(c))
   ==> ((allresolvents_sem M B (A UNION B)) UNION
        (allresolvents_sem M C (A UNION B UNION C)))
       SUBSUMES (allresolvents_sem M(B UNION C) (A UNION B UNION C))]])
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [ALLRESOLVENTS_SEM_UNION, UNION_ASSOC] THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (Session.AC UNION_ACI
     [[a UNION b UNION c UNION d UNION e UNION f =
      a UNION b UNION d UNION (c UNION e) UNION f]]))] THEN
    HolLight.GEN_REWRITE_TAC (HolLight.LAND_CONV o HolCore.Lib.funpow 3 HolLight.RAND_CONV) [(← ExceptT.mk (Session.AC UNION_ACI
     [[A UNION B = (A UNION A) UNION B]]))] THEN
    REPEAT (MATCH_MP_TAC SUBSUMES_UNION THEN ASM_REWRITE_TAC [SUBSUMES_REFL]) THEN
    ASM_SIMP_TAC [ALLRESOLVENTS_SEM_SYM])
  : ExceptT String IO thm).run
#eval ALLRESOLVENTS_SEM_STEP

#eval phrase 9
unsafe def resolvents_sem : thm := keep "resolvents_sem" fun _ => new_definition
  [[resolvents_sem M cl cls =
        list_of_set(allresolvents_sem M {cl} (set_of_list cls))]]
#eval resolvents_sem

#eval phrase 10
unsafe def ISARESOLVENT_SEM_CLAUSE : thm := keep "ISARESOLVENT_SEM_CLAUSE" fun _ => (do
  prove ([[!p q r. clause p /\ clause q /\ isaresolvent_sem M r (p,q) ==> clause r]])
   (MESON_TAC [isaresolvent_sem, ISARESOLVENT_CLAUSE])
  : ExceptT String IO thm).run
#eval ISARESOLVENT_SEM_CLAUSE

#eval phrase 11
unsafe def ALLRESOLVENTS_SEM_CLAUSE : thm := keep "ALLRESOLVENTS_SEM_CLAUSE" fun _ => (do
  prove ([[(!c. c IN s ==> clause c) /\ (!c. c IN t ==> clause c)
   ==> !c. c IN allresolvents_sem M s t ==> clause c]])
   (REWRITE_TAC [allresolvents_sem, IN_ELIM_THM] THEN
    MESON_TAC [ISARESOLVENT_SEM_CLAUSE])
  : ExceptT String IO thm).run
#eval ALLRESOLVENTS_SEM_CLAUSE

#eval phrase 12
unsafe def ISARESOLVENT_SEM_FINITE : thm := keep "ISARESOLVENT_SEM_FINITE" fun _ => (do
  prove ([[!c1 c2. clause(c1) /\ clause(c2)
           ==> FINITE {c | isaresolvent_sem M c (c1,c2)}]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC [[{c | isaresolvent c (c1,c2)}]] THEN
    ASM_SIMP_TAC [ISARESOLVENT_FINITE] THEN
    SIMP_TAC [SUBSET, IN_ELIM_THM, isaresolvent_sem])
  : ExceptT String IO thm).run
#eval ISARESOLVENT_SEM_FINITE

#eval phrase 13
unsafe def ALLRESOLVENTS_SEM_FINITE : thm := keep "ALLRESOLVENTS_SEM_FINITE" fun _ => (do
  prove ([[!s t. FINITE(s) /\ FINITE(t) /\
         (!c. c IN s ==> clause c) /\
         (!c. c IN t ==> clause c)
         ==> FINITE(allresolvents_sem M s t)]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC [[allresolvents s t]] THEN
    ASM_SIMP_TAC [ALLRESOLVENTS_FINITE] THEN
    SIMP_TAC [SUBSET, IN_ELIM_THM, isaresolvent_sem,
             allresolvents_sem, allresolvents] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval ALLRESOLVENTS_SEM_FINITE

#eval phrase 14
unsafe def step_sem : thm := keep "step_sem" fun _ => new_definition
  [[step_sem M (used,unused) =
        if unused = [] then (used,unused) else
        let new = resolvents_sem M (HD unused) (CONS (HD unused) used) in
        (insert (HD unused) used,
         ITLIST (incorporate (HD unused)) new (TL unused))]]
#eval step_sem

#eval phrase 15
unsafe def STEP_SEM : thm := keep "STEP_SEM" fun _ => (do
  prove ([[(step_sem M(used,[]) = (used,[])) /\
   (step_sem M(used,CONS cl cls) =
        let new = resolvents_sem M cl (CONS cl used) in
        insert cl used,ITLIST (incorporate cl) new cls)]])
   (REPEAT STRIP_TAC THEN HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [step_sem] THEN
    REWRITE_TAC [NOT_CONS_NIL, HD, TL])
  : ExceptT String IO thm).run
#eval STEP_SEM

#eval phrase 16
unsafe def given_sem : thm := keep "given_sem" fun _ => (do
  newRec num_RECURSION
    [[(given_sem M 0 p = p) /\
      (given_sem M (SUC n) p = step_sem M (given_sem M n p))]]
  : ExceptT String IO thm).run
#eval given_sem

#eval phrase 17
unsafe def Used_SEM : thm := keep "Used_SEM" fun _ => new_definition
  [[Used_SEM M init n = set_of_list(FST(given_sem M n init))]]
#eval Used_SEM

#eval phrase 18
unsafe def Unused_SEM : thm := keep "Unused_SEM" fun _ => new_definition
  [[Unused_SEM M init n = set_of_list(SND(given_sem M n init))]]
#eval Unused_SEM

#eval phrase 19
unsafe def Sub_SEM : thm := keep "Sub_SEM" fun _ => (do
  newRec num_RECURSION
    [[(Sub_SEM M init 0 = {}) /\
      (Sub_SEM M init (SUC n) =
           if SND(given_sem M n init) = [] then Sub_SEM M init n
           else HD(SND(given_sem M n init)) INSERT (Sub_SEM M init n))]]
  : ExceptT String IO thm).run
#eval Sub_SEM

#eval phrase 20
unsafe def ALLNTRESOLVENTS_SEM_STEP : thm := keep "ALLNTRESOLVENTS_SEM_STEP" fun _ => (do
  prove ([[(!c. c IN B ==> clause(c)) /\
   (!c. c IN C ==> clause(c))
   ==> ((allntresolvents_sem M B (A UNION B)) UNION
        (allntresolvents_sem M C (A UNION B UNION C)))
       SUBSUMES (allntresolvents_sem M (B UNION C) (A UNION B UNION C))]])
   (STRIP_TAC THEN MP_TAC ALLRESOLVENTS_SEM_STEP THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [SUBSUMES, allntresolvents_sem, IN_ELIM_THM, IN_UNION] THEN
    MESON_TAC [NONTAUTOLOGOUS_SUBSUMES])
  : ExceptT String IO thm).run
#eval ALLNTRESOLVENTS_SEM_STEP

#eval phrase 21
unsafe def ALLNTRESOLVENTS_SEM_UNION : thm := keep "ALLNTRESOLVENTS_SEM_UNION" fun _ => (do
  prove ([[(allntresolvents_sem M (A UNION B) C =
        (allntresolvents_sem M A C) UNION (allntresolvents_sem M B C)) /\
   (allntresolvents_sem M A (B UNION C) =
        (allntresolvents_sem M A B) UNION (allntresolvents_sem M A C))]])
   (REWRITE_TAC [EXTENSION, allntresolvents_sem, allresolvents_sem,
                IN_ELIM_THM, IN_UNION] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval ALLNTRESOLVENTS_SEM_UNION

#eval phrase 22
unsafe def USED_SUB : thm := keep "USED_SUB" fun _ => (do
  prove ([[!used unused n.
        Used_SEM M(used,unused) n =
        set_of_list(used) UNION Sub_SEM M (used,unused) n]])
   (GEN_TAC THEN GEN_TAC THEN
    REWRITE_TAC [Used_SEM, Unused_SEM] THEN INDUCT_TAC THEN
    REWRITE_TAC [Sub_SEM, given_sem, UNION_EMPTY] THEN
    ABBREV_TAC [[ppp = given_sem M n (used,unused)]] THEN
    SUBST1_TAC (← HolLight.SYM (← HolLight.ISPEC ([[ppp:(form->bool)list#(form->bool)list]]) PAIR)) THEN
    PURE_REWRITE_TAC [step_sem] THEN ASM_REWRITE_TAC [] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV Session.let_CONV) THEN
    REWRITE_TAC [FST, SET_OF_LIST_INSERT] THEN
    ASM_REWRITE_TAC [] THEN SET_TAC [])
  : ExceptT String IO thm).run
#eval USED_SUB

#eval phrase 23
unsafe def GIVEN_INVARIANT : thm := keep "GIVEN_INVARIANT" fun _ => (do
  let lemma1 ← prove ([[x INSERT s = s UNION {x}]]) (SET_TAC [])
  let lemma2 ← prove
   ([[(x INSERT s) UNION t = (s UNION (t UNION {x})) UNION (t UNION {x})]])
    (SET_TAC [])
  let _lemma3 ← prove
   ([[s UNION t = (s UNION t) UNION t]]) (SET_TAC [])
  let lemma4 ← prove
   ([[s UNION {x} = (x INSERT s) UNION {x}]]) (SET_TAC [])
  let lemma5 ← prove
   ([[(h INSERT s) UNION t = (s UNION t) UNION {h}]]) (SET_TAC [])
  prove ([[!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c)
        ==> !n. (!c. c IN Used_SEM M(used,unused) n ==> clause c) /\
                (!c. c IN Unused_SEM M(used,unused) n ==> clause c) /\
                (!c. c IN Sub_SEM M (used,unused) n ==> clause c) /\
                (Sub_SEM M (used,unused) n UNION Unused_SEM M(used,unused) n)
                 SUBSUMES
                 allntresolvents_sem M
                         (Sub_SEM M (used,unused) n)
                         (set_of_list(used) UNION Sub_SEM M (used,unused) n)]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
     [REWRITE_TAC [Sub_SEM, UNION_EMPTY] THEN
      ASM_REWRITE_TAC [Unused_SEM, given_sem, Used_SEM,
                      IN_SET_OF_LIST, NOT_IN_EMPTY] THEN
      MATCH_MP_TAC SUBSUMES_TRANS THEN
      EXISTS_TAC [[allresolvents_sem M {} (Used_SEM M (used,unused) 0)]] THEN
      ASM_REWRITE_TAC [Unused_SEM, given_sem, Used_SEM, IN_SET_OF_LIST] THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN ([[allresolvents_sem M {} (set_of_list used) = {}]])
        SUBST1_TAC THENL
         [REWRITE_TAC [allresolvents_sem, EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY],
          REWRITE_TAC [SUBSUMES, NOT_IN_EMPTY]],
        MATCH_MP_TAC SUBSUMES_SUBSET THEN
        EXISTS_TAC [[allntresolvents_sem M {} (set_of_list used)]] THEN
        REWRITE_TAC [SUBSUMES_REFL] THEN
        SIMP_TAC [SUBSET, allntresolvents_sem, IN_ELIM_THM]],
      ALL_TAC] THEN
    FIRST_ASSUM (fun th => HolLight.tactic_of do
      let _ ← liftExcept (HolCore.Lib.check (fun t => HolCore.Basics.is_conj t) (concl th))
      pure (UNDISCH_TAC (concl th))) THEN
    REWRITE_TAC [Sub_SEM, Unused_SEM, Used_SEM, given_sem] THEN
    ABBREV_TAC [[ppp = given_sem M n (used,unused)]] THEN
    SUBST1_TAC (← HolLight.SYM (← HolLight.ISPEC ([[ppp:(form->bool)list#(form->bool)list]]) PAIR)) THEN
    ABBREV_TAC [[used0 = FST(ppp:(form->bool)list#(form->bool)list)]] THEN
    ABBREV_TAC [[unused0 = SND(ppp:(form->bool)list#(form->bool)list)]] THEN
    REWRITE_TAC [FST, SND] THEN
    ABBREV_TAC [[sub0 = Sub_SEM M (used,unused) n]] THEN STRIP_TAC THEN
    REWRITE_TAC [step_sem] THEN
    DISJ_CASES_THEN2 SUBST_ALL_TAC MP_TAC
     (← HolLight.ISPEC ([[unused0:(form->bool)list]]) list_CASES)
    THENL
     [REWRITE_TAC [] THEN ASM_REWRITE_TAC [set_of_list, NOT_IN_EMPTY],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[cl:form->bool]])
          (X_CHOOSE_THEN ([[cls:(form->bool)list]])
                  SUBST_ALL_TAC)) THEN
    REWRITE_TAC [NOT_CONS_NIL, HD, TL] THEN LET_TAC THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV Session.let_CONV) THEN REWRITE_TAC [FST, SND] THEN
    SUBGOAL_THEN ([[clause cl]]) ASSUME_TAC THENL
     [UNDISCH_TAC [[!c. c IN set_of_list (CONS cl cls) ==> clause c]] THEN
      REWRITE_TAC [set_of_list, IN_INSERT] THEN MESON_TAC [], ALL_TAC] THEN
    CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC [insert_def] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [set_of_list, IN_INSERT] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[b /\ a /\ c ==> a /\ b /\ c]])) THEN CONJ_TAC THENL
     [REWRITE_TAC [set_of_list, IN_INSERT] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN ([[!c. MEM c new ==> clause c]]) ASSUME_TAC THENL
     [Fol.EXPAND_TAC "new" THEN REWRITE_TAC [resolvents_sem, set_of_list] THEN
      SUBGOAL_THEN ([[!c. MEM c (list_of_set (allresolvents_sem M {cl}
                                  (cl INSERT set_of_list used0))) <=>
                        c IN (allresolvents_sem M {cl} (cl INSERT set_of_list used0))]])
       (fun th => REWRITE_TAC [th])
      THENL
       [MATCH_MP_TAC MEM_LIST_OF_SET THEN
        MATCH_MP_TAC ALLRESOLVENTS_SEM_FINITE THEN
        SIMP_TAC [FINITE_RULES, FINITE_SET_OF_LIST],
        MATCH_MP_TAC ALLRESOLVENTS_SEM_CLAUSE] THEN
      ASM_SIMP_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
      ASM_MESON_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[a /\ (a ==> b) ==> a /\ b]])) THEN CONJ_TAC THENL
     [REWRITE_TAC [IN_SET_OF_LIST] THEN
      UNDISCH_TAC [[!c. MEM c new ==> clause c]] THEN
      SPEC_TAC ([[new:(form->bool)list]], [[more:(form->bool)list]]) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC [ITLIST, MEM] THENL
       [UNDISCH_TAC [[!c. c IN set_of_list (CONS cl cls) ==> clause c]] THEN
        REWRITE_TAC [IN_SET_OF_LIST, MEM] THEN MESON_TAC [], ALL_TAC] THEN
      ASM_MESON_TAC [INCORPORATE], ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC SUBSUMES_TRANS THEN
    EXISTS_TAC
     [[allntresolvents_sem M sub0 (set_of_list(used) UNION sub0) UNION
      allntresolvents_sem M {cl} (set_of_list(used) UNION sub0 UNION {cl})]] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC [IN_UNION, IN_INSERT, NOT_IN_EMPTY] THEN ASM_MESON_TAC [],
      ALL_TAC,
      HolLight.GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.ONCE_DEPTH_CONV) [lemma1] THEN
      MATCH_MP_TAC ALLNTRESOLVENTS_SEM_STEP THEN
      ASM_SIMP_TAC [IN_INSERT, NOT_IN_EMPTY]] THEN
    HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [lemma2] THEN
    MATCH_MP_TAC SUBSUMES_UNION THEN CONJ_TAC THENL
     [REWRITE_TAC [(← HolLight.GSYM lemma1)] THEN
      MATCH_MP_TAC SUBSUMES_TRANS THEN
      EXISTS_TAC [[sub0 UNION set_of_list(CONS (cl:form->bool) cls)]] THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [REWRITE_TAC [IN_UNION, IN_INSERT] THEN ASM_MESON_TAC [], ALL_TAC] THEN
      MATCH_MP_TAC SUBSUMES_UNION THEN REWRITE_TAC [SUBSUMES_REFL] THEN
      REWRITE_TAC [set_of_list] THEN ONCE_REWRITE_TAC [lemma1] THEN
      MATCH_MP_TAC SUBSUMES_UNION THEN REWRITE_TAC [SUBSUMES_REFL] THEN
      UNDISCH_TAC [[!c. MEM c new ==> clause c]] THEN
      UNDISCH_TAC [[!c. c IN set_of_list (ITLIST (incorporate cl) new cls)
                       ==> clause c]] THEN
      MATCH_MP_TAC (← ExceptT.mk (TAUT [[(b ==> a /\ c) ==> a ==> b ==> c]])) THEN
      SPEC_TAC ([[new:(form->bool)list]], [[added:(form->bool)list]]) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC [ITLIST, MEM, SUBSUMES_REFL] THENL
       [UNDISCH_TAC [[!c. c IN set_of_list (CONS cl cls) ==> clause c]] THEN
        REWRITE_TAC [set_of_list, IN_INSERT] THEN ASM_MESON_TAC [], ALL_TAC] THEN
      DISCH_TAC THEN
      MP_TAC (← HolLight.SPECL [ [[cl:form->bool]], [[h:form->bool]],
                    [[ITLIST (incorporate cl) t cls]] ]
                   INCORPORATE) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC [(← HolLight.GSYM IN_SET_OF_LIST)], ALL_TAC] THEN
      SIMP_TAC [IN_SET_OF_LIST] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (HolCore.Lib.K ALL_TAC)) THEN
      MATCH_MP_TAC SUBSUMES_TRANS THEN
      EXISTS_TAC [[set_of_list(ITLIST (incorporate cl) t cls)]] THEN
      ASM_SIMP_TAC [] THEN ASM_REWRITE_TAC [IN_SET_OF_LIST], ALL_TAC] THEN
    REWRITE_TAC [(← HolLight.GSYM UNION_ASSOC)] THEN
    SUBGOAL_THEN ([[set_of_list(used:(form->bool)list) UNION sub0 =
                  set_of_list(used0)]])
    SUBST1_TAC THENL
     [MAP_EVERY (fun s => Fol.EXPAND_TAC s) ["sub0", "used0", "ppp"] THEN
      REWRITE_TAC [(← HolLight.GSYM Used_SEM)] THEN REWRITE_TAC [USED_SUB], ALL_TAC] THEN
    SUBGOAL_THEN
     ([[allntresolvents_sem M {cl} (set_of_list used0 UNION {cl}) =
      set_of_list(FILTER (\c. ~(tautologous c)) new)]])
    SUBST1_TAC THENL
     [REWRITE_TAC [SET_OF_LIST_FILTER] THEN Fol.EXPAND_TAC "new" THEN
      REWRITE_TAC [resolvents_sem] THEN
      SUBGOAL_THEN ([[set_of_list(list_of_set
                          (allresolvents_sem M {cl}
                                         (set_of_list(CONS cl used0)))) =
                    allresolvents_sem M {cl} (set_of_list(CONS cl used0))]])
      SUBST1_TAC THENL
       [REWRITE_TAC [set_of_list] THEN
        MATCH_MP_TAC SET_OF_LIST_OF_SET THEN
        MATCH_MP_TAC ALLRESOLVENTS_SEM_FINITE THEN
        SIMP_TAC [FINITE_RULES, FINITE_SET_OF_LIST] THEN
        ASM_SIMP_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
        ASM_MESON_TAC [], ALL_TAC] THEN
      REWRITE_TAC [EXTENSION, allntresolvents_sem, IN_ELIM_THM, set_of_list] THEN
      REWRITE_TAC [(← HolLight.GSYM lemma1)], ALL_TAC] THEN
    UNDISCH_TAC [[!c. MEM c new ==> clause c]] THEN
    UNDISCH_TAC [[!c. c IN set_of_list (ITLIST (incorporate cl) new cls)
                       ==> clause c]] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[(b ==> a /\ c) ==> a ==> b ==> c]])) THEN
    SPEC_TAC ([[new:(form->bool)list]], [[added:(form->bool)list]]) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [ITLIST, MEM, FILTER] THENL
     [REWRITE_TAC [set_of_list, SUBSUMES, NOT_IN_EMPTY] THEN
      UNDISCH_TAC [[!c. c IN set_of_list (CONS cl cls) ==> clause c]] THEN
      REWRITE_TAC [set_of_list, IN_INSERT] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    DISCH_TAC THEN ASM_CASES_TAC [[tautologous h]] THEN ASM_SIMP_TAC [] THENL
     [MP_TAC (← HolLight.SPECL [ [[cl:form->bool]], [[h:form->bool]],
                    [[ITLIST (incorporate cl) t cls]] ]
                   INCORPORATE) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC [(← HolLight.GSYM IN_SET_OF_LIST)], ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [IN_SET_OF_LIST] THEN
      MATCH_MP_TAC SUBSUMES_TRANS THEN
      EXISTS_TAC [[set_of_list (ITLIST (incorporate cl) t cls) UNION {cl}]] THEN
      ASM_SIMP_TAC [SUBSUMES_UNION, SUBSUMES_REFL] THEN
      REWRITE_TAC [IN_UNION, NOT_IN_EMPTY, IN_INSERT, IN_ELIM_THM,
                  IN_SET_OF_LIST] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    MP_TAC (← HolLight.SPECL [ [[cl:form->bool]], [[h:form->bool]],
                  [[ITLIST (incorporate cl) t cls]] ]
                 INCORPORATE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC [(← HolLight.GSYM IN_SET_OF_LIST)], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [IN_SET_OF_LIST] THEN
    MATCH_MP_TAC SUBSUMES_TRANS THEN
    EXISTS_TAC
      [[set_of_list(CONS h (ITLIST (incorporate cl) t cls)) UNION {cl}]] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY, IN_UNION] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC [] THEN ASM_MESON_TAC [IN_SET_OF_LIST],
      HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [lemma4] THEN
      ASM_SIMP_TAC [SUBSUMES_UNION, SUBSUMES_REFL],
      REWRITE_TAC [set_of_list] THEN ONCE_REWRITE_TAC [lemma5] THEN
      HolLight.GEN_REWRITE_TAC HolLight.RAND_CONV [lemma1] THEN
      MATCH_MP_TAC SUBSUMES_UNION THEN REWRITE_TAC [SUBSUMES_REFL] THEN
      ASM_SIMP_TAC []])
  : ExceptT String IO thm).run
#eval GIVEN_INVARIANT

#eval phrase 24
unsafe def SUB_MONO_SUBSET : thm := keep "SUB_MONO_SUBSET" fun _ => (do
  prove ([[!init m n. m <= n ==> (Sub_SEM M init m) SUBSET (Sub_SEM M init n)]])
   (REPEAT GEN_TAC THEN SIMP_TAC [LE_EXISTS, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC [[d:num]] THEN DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN
    SPEC_TAC ([[d:num]], [[d:num]]) THEN INDUCT_TAC THEN
    REWRITE_TAC [ADD_CLAUSES, SUBSET_REFL] THEN
    REWRITE_TAC [Sub_SEM] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [SUBSET_TRANS, SUBSET, IN_INSERT])
  : ExceptT String IO thm).run
#eval SUB_MONO_SUBSET

#eval phrase 25
unsafe def SUB_MONO : thm := keep "SUB_MONO" fun _ => (do
  prove ([[!init m n. m <= n ==> (Sub_SEM M init n) SUBSUMES (Sub_SEM M init m)]])
   (MESON_TAC [SUBSUMES_SUBSET_REFL, SUB_MONO_SUBSET])
  : ExceptT String IO thm).run
#eval SUB_MONO

#eval phrase 26
unsafe def LENGTH_REPLACE : thm := keep "LENGTH_REPLACE" fun _ => (do
  prove ([[!cl current. LENGTH current <= LENGTH(replace cl current)]])
   (GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [replace] THEN
    REWRITE_TAC [LENGTH, LE_0] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [LENGTH, LE_SUC, LE_REFL])
  : ExceptT String IO thm).run
#eval LENGTH_REPLACE

#eval phrase 27
unsafe def LENGTH_INCORPORATE : thm := keep "LENGTH_INCORPORATE" fun _ => (do
  prove ([[!gcl cl current. LENGTH current <= LENGTH(incorporate gcl cl current)]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [incorporate] THEN
    COND_CASES_TAC THEN REWRITE_TAC [LE_REFL, LENGTH_REPLACE])
  : ExceptT String IO thm).run
#eval LENGTH_INCORPORATE

#eval phrase 28
unsafe def LENGTH_UNUSED_CHANGE : thm := keep "LENGTH_UNUSED_CHANGE" fun _ => (do
  prove ([[!init m n.
        LENGTH(SND(given_sem M m init))
        <= LENGTH (SND(given_sem M (m + n) init)) + n]])
   (HolLight.GEN_REWRITE_TAC HolCore.Lib.I [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[used:(form->bool)list]], [[unused:(form->bool)list]] ] THEN
    GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES, LE_REFL] THEN
    REWRITE_TAC [given_sem] THEN
    SUBST1_TAC (← HolLight.SYM (← HolLight.ISPEC ([[given_sem M (m + n) (used,unused)]]) PAIR)) THEN
    PURE_REWRITE_TAC [step_sem] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV Session.let_CONV) THEN
    COND_CASES_TAC THEN REWRITE_TAC [SND] THEN
    ASM_SIMP_TAC [(← ExceptT.mk (ARITH_RULE [[m <= n ==> m <= SUC n]]))] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC [[LENGTH (SND (given_sem M (m + n) (used,unused))) + n]] THEN
    ASM_REWRITE_TAC [] THEN
    UNDISCH_TAC [[~(SND (given_sem M (m + n) (used,unused)) = [])]] THEN
    SPEC_TAC ([[SND (given_sem M (m + n) (used,unused))]], [[l:(form->bool)list]]) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [NOT_CONS_NIL, TL, LENGTH] THEN
    MATCH_MP_TAC (← ExceptT.mk (ARITH_RULE [[x <= y ==> SUC x + n <= SUC(y + n)]])) THEN
    SPEC_TAC ([[(resolvents_sem M (HD (CONS h t))
                (CONS (HD (CONS h t)) (FST (given_sem M (m + n) (used,unused)))))]],
             [[k:(form->bool)list]]) THEN
    REWRITE_TAC [HD] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [ITLIST, LE_REFL] THEN
    ASM_MESON_TAC [LENGTH_INCORPORATE, LE_TRANS])
  : ExceptT String IO thm).run
#eval LENGTH_UNUSED_CHANGE

#eval phrase 29
unsafe def LENGTH_UNUSED_ZERO : thm := keep "LENGTH_UNUSED_ZERO" fun _ => (do
  prove ([[!used unused m n.
        (SND (given_sem M m (used,unused)) = [])
        ==> (SND (given_sem M (m + n) (used,unused)) = [])]])
   (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
    INDUCT_TAC THEN SIMP_TAC [ADD_CLAUSES] THEN
    REWRITE_TAC [given_sem] THEN
    SUBST1_TAC (← HolLight.SYM (← HolLight.ISPEC ([[given_sem M (m + n) (used,unused)]]) PAIR)) THEN
    PURE_REWRITE_TAC [step_sem] THEN ASM_SIMP_TAC [])
  : ExceptT String IO thm).run
#eval LENGTH_UNUSED_ZERO

#eval phrase 30
unsafe def REPLACE_SUBSUMES_SELF : thm := keep "REPLACE_SUBSUMES_SELF" fun _ => (do
  prove ([[!cl current n.
        n < LENGTH current
        ==> (EL n (replace cl current)) subsumes (EL n current)]])
   (GEN_TAC THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC [replace, LENGTH, (← liftExcept (Session.CONJUNCT1 LT))] THEN
    INDUCT_TAC THEN REWRITE_TAC [EL] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [HD, TL, EL, subsumes_REFL, LT_SUC])
  : ExceptT String IO thm).run
#eval REPLACE_SUBSUMES_SELF

#eval phrase 31
unsafe def INCORPORATE_SUBSUMES_SELF : thm := keep "INCORPORATE_SUBSUMES_SELF" fun _ => (do
  prove ([[!gcl cl current n.
        n < LENGTH current
        ==> (EL n (incorporate gcl cl current)) subsumes (EL n current)]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [incorporate] THEN
    COND_CASES_TAC THEN REWRITE_TAC [subsumes_REFL, REPLACE_SUBSUMES_SELF])
  : ExceptT String IO thm).run
#eval INCORPORATE_SUBSUMES_SELF

#eval phrase 32
unsafe def REPLACE_CLAUSE : thm := keep "REPLACE_CLAUSE" fun _ => (do
  prove ([[!cl current.
        (!c. MEM c current ==> clause c) /\ clause cl
        ==> !c. MEM c (replace cl current) ==> clause c]])
   (GEN_TAC THEN LIST_INDUCT_TAC THEN SIMP_TAC [replace, MEM] THEN
    STRIP_TAC THEN GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC [MEM] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval REPLACE_CLAUSE

#eval phrase 33
unsafe def INCORPORATE_CLAUSE : thm := keep "INCORPORATE_CLAUSE" fun _ => (do
  prove ([[(!c. MEM c current ==> clause c) /\ clause cl
   ==> !c. MEM c (incorporate gcl cl current) ==> clause c]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN REWRITE_TAC [incorporate] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [REPLACE_CLAUSE])
  : ExceptT String IO thm).run
#eval INCORPORATE_CLAUSE

#eval phrase 34
unsafe def INCORPORATE_CLAUSE_EL : thm := keep "INCORPORATE_CLAUSE_EL" fun _ => (do
  prove ([[(!c. MEM c current ==> clause c) /\ clause cl /\ p < LENGTH current
   ==> clause (EL p (incorporate gcl cl current))]])
   (MESON_TAC [MEM_EL, INCORPORATE_CLAUSE, LENGTH_INCORPORATE,
              LTE_TRANS])
  : ExceptT String IO thm).run
#eval INCORPORATE_CLAUSE_EL

#eval phrase 35
unsafe def UNUSED_SUBSUMES_SELF : thm := keep "UNUSED_SUBSUMES_SELF" fun _ => (do
  prove ([[!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c)
        ==> !k m n. n + k < LENGTH(SND(given_sem M m (used,unused)))
                    ==> (EL n (SND(given_sem M (m + k) (used,unused))))
                    subsumes (EL (n + k) (SND(given_sem M m (used,unused))))]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC [ADD_CLAUSES, subsumes_REFL] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [ [[SUC m]], [[n:num]] ]) THEN
    REWRITE_TAC [ADD_CLAUSES] THEN ANTS_TAC THENL
     [MP_TAC (← HolLight.SPECL [ [[(used:(form->bool)list,unused:(form->bool)list)]],
                    [[m:num]], [[1]] ] LENGTH_UNUSED_CHANGE) THEN
      REWRITE_TAC [ADD1] THEN
      MATCH_MP_TAC (← ExceptT.mk (ARITH_RULE
       [[SUC x < lm ==> lm <= lm1 + 1 ==> x < lm1]])) THEN
      ASM_REWRITE_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC (← HolLight.ONCE_REWRITE_RULE [(← ExceptT.mk (TAUT
     [[a /\ b /\ c ==> d <=> a /\ c ==> b ==> d]]))] subsumes_TRANS) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN ([[(EL n (SND (given_sem M (SUC (m + k)) (used,unused)))) IN
                    Unused_SEM M(used,unused) (SUC(m + k))]])
       (fun th => ASM_MESON_TAC [th, GIVEN_INVARIANT]) THEN
      REWRITE_TAC [Unused_SEM, IN_SET_OF_LIST] THEN
      MATCH_MP_TAC MEM_EL THEN
      MP_TAC (← HolLight.SPECL [ [[(used:(form->bool)list,unused:(form->bool)list)]],
                    [[m:num]], [[SUC k]] ] LENGTH_UNUSED_CHANGE) THEN
      UNDISCH_TAC [[SUC (n + k) < LENGTH (SND (given_sem M m (used,unused)))]] THEN
      REWRITE_TAC [ADD_CLAUSES] THEN ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [given_sem] THEN
    SUBST1_TAC (← HolLight.SYM (← HolLight.ISPEC ([[given_sem M m (used,unused)]]) PAIR)) THEN
    PURE_REWRITE_TAC [step_sem] THEN LET_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC [SND] THENL
     [UNDISCH_TAC [[SUC (n + k) < LENGTH (SND (given_sem M m (used,unused)))]] THEN
      ASM_REWRITE_TAC [LENGTH, LT], ALL_TAC] THEN
    UNDISCH_TAC [[SUC (n + k) < LENGTH (SND (given_sem M m (used,unused)))]] THEN
    SUBGOAL_THEN ([[!c. MEM c (SND (given_sem M m (used,unused))) ==> clause c]])
    MP_TAC THENL
     [REWRITE_TAC [(← HolLight.GSYM IN_SET_OF_LIST), (← HolLight.GSYM Unused_SEM)] THEN
      ASM_MESON_TAC [GIVEN_INVARIANT], ALL_TAC] THEN
    SUBGOAL_THEN ([[!c. MEM c new ==> clause c]]) MP_TAC THENL
     [Fol.EXPAND_TAC "new" THEN REWRITE_TAC [resolvents_sem, set_of_list] THEN
      ABBREV_TAC [[gcl = HD (SND (given_sem M m (used,unused)))]] THEN
      REWRITE_TAC [(← HolLight.GSYM Used_SEM)] THEN
      SUBGOAL_THEN ([[!c. MEM c (list_of_set (allresolvents_sem M {gcl}
                            (gcl INSERT Used_SEM M (used,unused) m))) <=>
                        c IN (allresolvents_sem M {gcl}
                             (gcl INSERT Used_SEM M (used,unused) m))]])
       (fun th => REWRITE_TAC [th])
      THENL
       [MATCH_MP_TAC MEM_LIST_OF_SET THEN
        MATCH_MP_TAC ALLRESOLVENTS_SEM_FINITE THEN
        SIMP_TAC [FINITE_RULES, FINITE_SET_OF_LIST] THEN
        ASM_SIMP_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
        REWRITE_TAC [FINITE_INSERT] THEN
        REWRITE_TAC [Used_SEM, FINITE_SET_OF_LIST] THEN
        REWRITE_TAC [(← HolLight.GSYM Used_SEM)],
        MATCH_MP_TAC ALLRESOLVENTS_SEM_CLAUSE THEN
        ASM_SIMP_TAC [IN_INSERT, NOT_IN_EMPTY]] THEN
      SUBGOAL_THEN ([[clause gcl]])
        (fun th => ASM_MESON_TAC [th, GIVEN_INVARIANT]) THEN
      SUBGOAL_THEN ([[gcl IN Unused_SEM M(used,unused) m]])
        (fun th => ASM_MESON_TAC [th, GIVEN_INVARIANT]) THEN
      REWRITE_TAC [Unused_SEM, IN_SET_OF_LIST] THEN
      Fol.EXPAND_TAC "gcl" THEN
      UNDISCH_TAC [[~(SND(given_sem M m (used,unused)) = [])]] THEN
      SPEC_TAC ([[SND(given_sem M m (used,unused))]], [[l:(form->bool)list]]) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC [MEM, HD], ALL_TAC] THEN
    DISCH_TAC THEN
    UNDISCH_TAC [[~(SND (given_sem M m (used,unused)) = [])]] THEN
    SPEC_TAC ([[SND(given_sem M m (used,unused))]], [[l:(form->bool)list]]) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [NOT_CONS_NIL, EL, HD, TL] THEN
    REWRITE_TAC [LENGTH, LT_SUC] THEN
    UNDISCH_TAC [[!c. MEM c new ==> clause c]] THEN
    SPEC_TAC ([[n + k:num]], [[p:num]]) THEN
    SPEC_TAC ([[new:(form->bool)list]], [[new:(form->bool)list]]) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [ITLIST, subsumes_REFL] THEN
    X_GEN_TAC [[p:num]] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[p:num]]) THEN
    ASM_REWRITE_TAC [] THEN
    ANTS_TAC THENL [ASM_MESON_TAC [MEM], ALL_TAC] THEN
    MATCH_MP_TAC (← HolLight.ONCE_REWRITE_RULE [(← ExceptT.mk (TAUT
     [[a /\ b /\ c ==> d <=> a /\ b ==> c ==> d]]))] subsumes_TRANS) THEN
    CONJ_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC INCORPORATE_SUBSUMES_SELF THEN
      UNDISCH_TAC [[p < LENGTH(t:(form->bool)list)]] THEN
      SPEC_TAC ([[t':(form->bool)list]], [[k:(form->bool)list]]) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC [ITLIST] THEN
      ASM_MESON_TAC [LENGTH_INCORPORATE, LTE_TRANS]] THEN
    MATCH_MP_TAC INCORPORATE_CLAUSE_EL THEN
    CONJ_TAC THENL
     [ALL_TAC,
      CONJ_TAC THENL [ASM_MESON_TAC [MEM], ALL_TAC] THEN
      SUBGOAL_THEN
       ([[!gcl current lis.
          LENGTH(current) <= LENGTH(ITLIST (incorporate gcl) lis current)]])
       (fun th => ASM_MESON_TAC [LTE_TRANS, th]) THEN
      GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
      REWRITE_TAC [ITLIST, LE_REFL] THEN
      ASM_MESON_TAC [LE_TRANS, LENGTH_INCORPORATE]] THEN
    SUBGOAL_THEN
     ([[!current gcl new.
          (!c. MEM c current ==> clause c) /\
          (!c. MEM c new ==> clause c)
          ==> !c. MEM c (ITLIST (incorporate gcl) new current)
                  ==> clause c]])
    MATCH_MP_TAC THENL [ALL_TAC, ASM_MESON_TAC [MEM]] THEN
    POP_ASSUM_LIST (HolCore.Lib.K ALL_TAC) THEN
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC [ITLIST, MEM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [INCORPORATE_CLAUSE])
  : ExceptT String IO thm).run
#eval UNUSED_SUBSUMES_SELF

#eval phrase 36
unsafe def SUB_SUBSUMES_UNUSED : thm := keep "SUB_SUBSUMES_UNUSED" fun _ => (do
  let lemma ← prove ([[x INSERT s = {x} UNION s]]) (SET_TAC [])
  let ar1 ← ExceptT.mk (ARITH_RULE [[x <= n ==> x <= SUC n]])
  prove ([[(!c. MEM c used ==> clause c) /\
   (!c. MEM c unused ==> clause c)
   ==> !n. Sub_SEM M (used,unused)
              (n + LENGTH(SND(given_sem M n (used,unused))))
           SUBSUMES (Sub_SEM M (used,unused) n UNION
                     Unused_SEM M(used,unused) n)]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     ([[!m n. Sub_SEM M (used,unused) (m + n) SUBSUMES
          Sub_SEM M (used,unused) m UNION
          set_of_list(FIRSTN n (SND(given_sem M m (used,unused))))]])
    MP_TAC THENL
     [ALL_TAC, ASM_MESON_TAC [LE_REFL, FIRSTN_TRIVIAL, Unused_SEM]] THEN
    GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES] THENL
     [REWRITE_TAC [FIRSTN, set_of_list, UNION_EMPTY, SUBSUMES_REFL], ALL_TAC] THEN
    REWRITE_TAC [Sub_SEM] THEN COND_CASES_TAC THENL
     [SUBGOAL_THEN ([[FIRSTN (SUC n) (SND(given_sem M m (used,unused))) =
                    FIRSTN n (SND(given_sem M m (used,unused)))]])
       (fun th => ASM_REWRITE_TAC [th]) THEN
      SUBGOAL_THEN ([[LENGTH(SND (given_sem M m (used,unused))) <= n]])
       (fun th => MESON_TAC [th, FIRSTN_TRIVIAL, LE_REFL,
                            ar1]) THEN
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC [[LENGTH(SND (given_sem M (m + n) (used,unused))) + n]] THEN
      ASM_REWRITE_TAC [LENGTH_UNUSED_CHANGE, LENGTH, ADD_CLAUSES, LE_REFL],
      ALL_TAC] THEN
    REWRITE_TAC [FIRSTN] THEN COND_CASES_TAC THENL
     [ASM_MESON_TAC [LENGTH_UNUSED_ZERO], ALL_TAC] THEN
    MATCH_MP_TAC SUBSUMES_TRANS THEN
    EXISTS_TAC
     [[HD(SND (given_sem M (m + n) (used,unused))) INSERT
      (Sub_SEM M (used,unused) m UNION
       set_of_list (FIRSTN n (SND (given_sem M m (used,unused)))))]] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [IN_INSERT] THEN
      SUBGOAL_THEN
       ([[HD(SND(given_sem M (m + n) (used,unused))) IN
          Unused_SEM M (used,unused) (m + n)]])
      MP_TAC THENL
       [ALL_TAC, ASM_MESON_TAC [GIVEN_INVARIANT]] THEN
      UNDISCH_TAC [[~(SND(given_sem M (m + n) (used,unused)) = [])]] THEN
      REWRITE_TAC [Unused_SEM, IN_SET_OF_LIST] THEN
      SPEC_TAC ([[SND(given_sem M(m + n) (used,unused))]], [[l:(form->bool)list]]) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC [MEM, HD], ALL_TAC] THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC [lemma] THEN MATCH_MP_TAC SUBSUMES_UNION THEN
      ASM_REWRITE_TAC [SUBSUMES_REFL], ALL_TAC] THEN
    REWRITE_TAC [set_of_list] THEN ONCE_REWRITE_TAC [lemma] THEN
    HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [(← ExceptT.mk (Session.AC UNION_ACI
     [[s UNION t UNION u = t UNION u UNION s]]))] THEN
    MATCH_MP_TAC SUBSUMES_UNION THEN ASM_REWRITE_TAC [SUBSUMES_REFL] THEN
    SUBGOAL_THEN
     ([[{(HD (SND (given_sem M m (used,unused))))} UNION
      set_of_list(FIRSTN n (TL (SND (given_sem M m (used,unused))))) =
      set_of_list(FIRSTN (SUC n) (SND (given_sem M m (used,unused))))]])
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC [FIRSTN] THEN
      UNDISCH_TAC [[~(SND (given_sem M m (used,unused)) = [])]] THEN
      REWRITE_TAC [set_of_list] THEN SET_TAC [], ALL_TAC] THEN
    ASM_CASES_TAC
     [[LENGTH(SND (given_sem M m (used,unused))) <= n]]
    THENL
     [ASM_SIMP_TAC [FIRSTN_SHORT] THEN
      MATCH_MP_TAC SUBSUMES_SUBSET THEN
      EXISTS_TAC [[set_of_list(FIRSTN n (SND (given_sem M m (used,unused))))]] THEN
      REWRITE_TAC [SUBSUMES_REFL] THEN SIMP_TAC [SUBSET, IN_UNION], ALL_TAC] THEN
    MATCH_MP_TAC SUBSUMES_TRANS THEN
    EXISTS_TAC
     [[set_of_list(FIRSTN n (SND (given_sem M m (used,unused)))) UNION
      {(EL n (SND (given_sem M m (used,unused))))}]] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [IN_UNION, IN_INSERT, NOT_IN_EMPTY] THEN
      REWRITE_TAC [(← HolLight.GSYM Unused_SEM)] THEN
      REWRITE_TAC [IN_SET_OF_LIST] THEN
      X_GEN_TAC [[c:form->bool]] THEN DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL
       [DISCH_THEN (MP_TAC oTIO HolLight.MATCH_MP FIRSTN_SUBLIST) THEN
        REWRITE_TAC [(← HolLight.GSYM IN_SET_OF_LIST), (← HolLight.GSYM Unused_SEM)] THEN
        ASM_MESON_TAC [GIVEN_INVARIANT], ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN
       ([[(HD(SND (given_sem M (m + n) (used,unused)))) IN
        Unused_SEM M(used,unused) (m + n)]])
       (fun th => ASM_MESON_TAC [th, GIVEN_INVARIANT]) THEN
      REWRITE_TAC [Unused_SEM, IN_SET_OF_LIST] THEN
      UNDISCH_TAC [[~(SND (given_sem M (m + n) (used,unused)) = [])]] THEN
      SPEC_TAC ([[SND (given_sem M (m + n) (used,unused))]], [[l:(form->bool)list]]) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC [MEM, HD], ALL_TAC] THEN
    CONJ_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC SUBSUMES_SUBSET THEN
      EXISTS_TAC [[set_of_list (FIRSTN (SUC n) (SND (given_sem M m (used,unused))))]] THEN
      REWRITE_TAC [SUBSUMES_REFL] THEN
      MP_TAC (← HolLight.GEN ([[x:form->bool]])
       (← HolLight.ISPECL [ [[x:form->bool]], [[n:num]], [[SND (given_sem M m (used,unused))]] ]
              FIRSTN_SUC)) THEN
      REWRITE_TAC [(← HolLight.GSYM IN_SET_OF_LIST), SET_OF_LIST_APPEND, set_of_list] THEN
      REWRITE_TAC [SUBSET, IN_UNION, IN_INSERT, NOT_IN_EMPTY]] THEN
    MATCH_MP_TAC SUBSUMES_UNION THEN REWRITE_TAC [SUBSUMES_REFL] THEN
    REWRITE_TAC [SUBSUMES, IN_INSERT, NOT_IN_EMPTY] THEN
    SUBGOAL_THEN
     ([[HD(SND(given_sem M (m + n) (used,unused))) subsumes
      (EL n (SND (given_sem M m (used,unused))))]])
     (fun th => MESON_TAC [th]) THEN
    HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM (← liftExcept (Session.CONJUNCT1 EL)))] THEN
    HolLight.GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.LAND_CONV) [(← ExceptT.mk (ARITH_RULE [[n = 0 + n]]))] THEN
    MP_TAC (← HolLight.SPECL [ [[used:(form->bool)list]], [[unused:(form->bool)list]] ]
          UNUSED_SUBSUMES_SELF) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC [[~(LENGTH (SND (given_sem M m (used,unused))) <= n)]] THEN
    ARITH_TAC)
  : ExceptT String IO thm).run
#eval SUB_SUBSUMES_UNUSED

#eval phrase 37
unsafe def break_sem : thm := keep "break_sem" fun _ => (do
  newRec num_RECURSION
    [[(break_sem M init 0 = LENGTH(SND(given_sem M 0 init))) /\
      (break_sem M init (SUC n) =
           break_sem M init n +
           LENGTH(SND(given_sem M (break_sem M init n) init)))]]
  : ExceptT String IO thm).run
#eval break_sem

#eval phrase 38
unsafe def level_sem : thm := keep "level_sem" fun _ => new_definition
  [[level_sem M init n = Sub_SEM M init (break_sem M init n)]]
#eval level_sem

#eval phrase 39
unsafe def LEVEL_0 : thm := keep "LEVEL_0" fun _ => (do
  prove ([[!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c)
        ==> level_sem M (used,unused) 0 SUBSUMES set_of_list(unused)]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC oTIO HolLight.MATCH_MP SUB_SUBSUMES_UNUSED) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[0]]) THEN
    REWRITE_TAC [ADD_CLAUSES, Sub_SEM, UNION_EMPTY] THEN
    REWRITE_TAC [Unused_SEM, given_sem, level_sem, Sub_SEM, break_sem])
  : ExceptT String IO thm).run
#eval LEVEL_0

#eval phrase 40
unsafe def LEVEL_STEP : thm := keep "LEVEL_STEP" fun _ => (do
  prove ([[!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c)
        ==> !n. level_sem M (used,unused) (SUC n) SUBSUMES
                allntresolvents_sem M (level_sem M (used,unused) (n))
                                (set_of_list(used) UNION
                                 level_sem M (used,unused) (n))]])
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUBSUMES_TRANS THEN
    EXISTS_TAC [[Sub_SEM M (used,unused) (break_sem M(used,unused) n) UNION
              Unused_SEM M(used,unused) (break_sem M(used,unused) n)]] THEN
    REWRITE_TAC [level_sem] THEN
    -- (**** why does ASM_SIMP_TAC[GIVEN_INVARIANT] seem to loop??? ***)
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC [GIVEN_INVARIANT],
      ALL_TAC,
      ASM_MESON_TAC [GIVEN_INVARIANT]] THEN
    REWRITE_TAC [break_sem] THEN
    ASM_SIMP_TAC [SUB_SUBSUMES_UNUSED])
  : ExceptT String IO thm).run
#eval LEVEL_STEP

#eval phrase 41
unsafe def level_CLAUSE : thm := keep "level_CLAUSE" fun _ => (do
  prove ([[!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c)
        ==> !n c. c IN (level_sem M (used,unused) n) ==> clause c]])
   (REWRITE_TAC [level_sem] THEN MESON_TAC [GIVEN_INVARIANT])
  : ExceptT String IO thm).run
#eval level_CLAUSE

#eval phrase 42
unsafe def BREAK_MONO : thm := keep "BREAK_MONO" fun _ => (do
  prove ([[!init m n. m <= n ==> break_sem M init m <= break_sem M init n]])
   (SUBGOAL_THEN ([[!init m d. break_sem M init m <= break_sem M init (m + d)]])
     (fun th => MESON_TAC [th, LE_EXISTS]) THEN
    GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC [ADD_CLAUSES, break_sem, LE_REFL] THEN
    ASM_MESON_TAC [LE_TRANS, LE_ADD])
  : ExceptT String IO thm).run
#eval BREAK_MONO

#eval phrase 43
unsafe def level_MONO_SUBSET : thm := keep "level_MONO_SUBSET" fun _ => (do
  prove ([[!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c)
        ==> !m n. m <= n
                  ==> level_sem M (used,unused) m SUBSET level_sem M (used,unused) n]])
   (REWRITE_TAC [level_sem] THEN MESON_TAC [SUB_MONO_SUBSET, BREAK_MONO])
  : ExceptT String IO thm).run
#eval level_MONO_SUBSET

#eval phrase 44
unsafe def level_MONO : thm := keep "level_MONO" fun _ => (do
  prove ([[!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c)
        ==> !m n. m <= n
                  ==> level_sem M (used,unused) n SUBSUMES level_sem M (used,unused) m]])
   (REWRITE_TAC [level_sem] THEN MESON_TAC [SUB_MONO, BREAK_MONO])
  : ExceptT String IO thm).run
#eval level_MONO

#eval phrase 45
unsafe def ISARESOLVENT_SEM_SUBSUME_L : thm := keep "ISARESOLVENT_SEM_SUBSUME_L" fun _ => (do
  prove ([[!p p' q r.
        clause p /\ clause p' /\ clause q /\
        p' subsumes p /\ isaresolvent_sem M r (p,q)
        ==> p' subsumes r \/
            ?r'. isaresolvent_sem M r' (p',q) /\ r' subsumes r]])
   (REWRITE_TAC [isaresolvent_sem] THEN REPEAT STRIP_TAC THEN
    ASM_MESON_TAC [HOLDS_INTERP_SUBSUME, ISARESOLVENT_SUBSUME_L])
  : ExceptT String IO thm).run
#eval ISARESOLVENT_SEM_SUBSUME_L

#eval phrase 46
unsafe def ISARESOLVENT_SEM_SUBSUME_R : thm := keep "ISARESOLVENT_SEM_SUBSUME_R" fun _ => (do
  prove ([[!p q q' r.
        clause p /\ clause q /\ clause q' /\
        q' subsumes q /\ isaresolvent_sem M r (p,q)
        ==> q' subsumes r \/
            ?r'. isaresolvent_sem M r' (p,q') /\ r' subsumes r]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [ [[q:form->bool]], [[p:form->bool]], [[r:form->bool]] ]
                 ISARESOLVENT_SEM_SYM) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[r':form->bool]]) STRIP_ASSUME_TAC) THEN
    MP_TAC (← HolLight.SPECL [ [[q:form->bool]], [[q':form->bool]], [[p:form->bool]],
                  [[r':form->bool]] ] ISARESOLVENT_SEM_SUBSUME_L) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
     [DISJ1_TAC THEN MATCH_MP_TAC subsumes_TRANS THEN
      EXISTS_TAC [[r':form->bool]] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[r'':form->bool]]) STRIP_ASSUME_TAC) THEN
    DISJ2_TAC THEN
    MP_TAC (← HolLight.SPECL [ [[p:form->bool]], [[q':form->bool]], [[r'':form->bool]] ]
                 ISARESOLVENT_SEM_SYM) THEN
    ASM_REWRITE_TAC [] THEN
    ASM MESON_TAC [ISARESOLVENT_SEM_CLAUSE, subsumes_TRANS])
  : ExceptT String IO thm).run
#eval ISARESOLVENT_SEM_SUBSUME_R

#eval phrase 47
unsafe def ISARESOLVENT_SEM_SUBSUME : thm := keep "ISARESOLVENT_SEM_SUBSUME" fun _ => (do
  prove ([[!p p' q q' r.
        clause p /\ clause p' /\ clause q /\ clause q' /\
        p' subsumes p /\ q' subsumes q /\ isaresolvent_sem M r (p,q)
        ==> p' subsumes r \/ q' subsumes r \/
            ?r'. isaresolvent_sem M r' (p',q') /\ r' subsumes r]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [ [[p:form->bool]], [[q:form->bool]],
                  [[q':form->bool]], [[r:form->bool]] ]
                 ISARESOLVENT_SEM_SUBSUME_R) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[r':form->bool]]) STRIP_ASSUME_TAC) THEN
    MP_TAC (← HolLight.SPECL [ [[p:form->bool]], [[p':form->bool]],
                  [[q':form->bool]], [[r':form->bool]] ]
                 ISARESOLVENT_SEM_SUBSUME_L) THEN
    ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [subsumes_TRANS, ISARESOLVENT_SEM_CLAUSE])
  : ExceptT String IO thm).run
#eval ISARESOLVENT_SEM_SUBSUME

#eval phrase 48
unsafe def ALLRESOLVENTS_SEM_SUBSUME_L : thm := keep "ALLRESOLVENTS_SEM_SUBSUME_L" fun _ => (do
  prove ([[!s t u.
      (!c. c IN s ==> clause c) /\
      (!c. c IN t ==> clause c) /\
      (!c. c IN u ==> clause c) /\
      s SUBSUMES t
      ==> (s UNION (allresolvents_sem M s u)) SUBSUMES
          (allresolvents_sem M t u)]])
   (REWRITE_TAC [SUBSUMES, IN_UNION, allresolvents_sem, IN_ELIM_THM] THEN
    MESON_TAC [ISARESOLVENT_SEM_SUBSUME_L, subsumes_REFL])
  : ExceptT String IO thm).run
#eval ALLRESOLVENTS_SEM_SUBSUME_L

#eval phrase 49
unsafe def ALLRESOLVENTS_SEM_SUBSUME_R : thm := keep "ALLRESOLVENTS_SEM_SUBSUME_R" fun _ => (do
  prove ([[!s t u.
      (!c. c IN s ==> clause c) /\
      (!c. c IN t ==> clause c) /\
      (!c. c IN u ==> clause c) /\
      t SUBSUMES u
      ==> (t UNION (allresolvents_sem M s t)) SUBSUMES
          (allresolvents_sem M s u)]])
   (REWRITE_TAC [SUBSUMES, IN_UNION, allresolvents_sem, IN_ELIM_THM] THEN
    MESON_TAC [ISARESOLVENT_SEM_SUBSUME_R, subsumes_REFL])
  : ExceptT String IO thm).run
#eval ALLRESOLVENTS_SEM_SUBSUME_R

#eval phrase 50
unsafe def ALLRESOLVENTS_SEM_SUBSUME : thm := keep "ALLRESOLVENTS_SEM_SUBSUME" fun _ => (do
  prove ([[!s t s' t'.
      (!c. c IN s ==> clause c) /\
      (!c. c IN s' ==> clause c) /\
      (!c. c IN t ==> clause c) /\
      (!c. c IN t' ==> clause c) /\
      s SUBSUMES s' /\ t SUBSUMES t'
      ==> (s UNION t UNION (allresolvents_sem M s t)) SUBSUMES
          (allresolvents_sem M s' t')]])
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUBSUMES_TRANS THEN
    EXISTS_TAC [[s UNION (allresolvents_sem M s t')]] THEN
    ASM_SIMP_TAC [ALLRESOLVENTS_SEM_SUBSUME_L, ALLRESOLVENTS_SEM_SUBSUME_R,
                 SUBSUMES_UNION, SUBSUMES_REFL, IN_UNION] THEN
    ASM_MESON_TAC [ALLRESOLVENTS_SEM_CLAUSE])
  : ExceptT String IO thm).run
#eval ALLRESOLVENTS_SEM_SUBSUME

#eval phrase 51
unsafe def ISARESOLVENT_SEM_TAUTOLOGY_L : thm := keep "ISARESOLVENT_SEM_TAUTOLOGY_L" fun _ => (do
  prove ([[!p q r.
      clause p /\ clause q /\
      tautologous(p) /\ isaresolvent_sem M r (p,q)
      ==> tautologous(r) \/ q subsumes r]])
   (MESON_TAC [isaresolvent_sem, ISARESOLVENT_TAUTOLOGY_L])
  : ExceptT String IO thm).run
#eval ISARESOLVENT_SEM_TAUTOLOGY_L

#eval phrase 52
unsafe def TAUTOLOGOUS_SUBSUMES : thm := keep "TAUTOLOGOUS_SUBSUMES" fun _ => (do
  prove ([[!p q. p subsumes q /\ tautologous(p) ==> tautologous(q)]])
   (MESON_TAC [subsumes, tautologous, SUBSET, TAUTOLOGOUS_INSTANCE])
  : ExceptT String IO thm).run
#eval TAUTOLOGOUS_SUBSUMES

#eval phrase 53
unsafe def ISARESOLVENT_SEM_TAUTOLOGY_R : thm := keep "ISARESOLVENT_SEM_TAUTOLOGY_R" fun _ => (do
  prove ([[!p q r.
      clause p /\ clause q /\
      tautologous(p) /\ isaresolvent_sem M r (q,p)
      ==> tautologous(r) \/ q subsumes r]])
   (MESON_TAC [ISARESOLVENT_SEM_SYM, ISARESOLVENT_SEM_TAUTOLOGY_L, subsumes_TRANS,
              TAUTOLOGOUS_SUBSUMES])
  : ExceptT String IO thm).run
#eval ISARESOLVENT_SEM_TAUTOLOGY_R

#eval phrase 54
unsafe def UNUSED_FROMNEW : thm := keep "UNUSED_FROMNEW" fun _ => (do
  prove ([[!used unused c n.
        MEM c (SND(given_sem M n (used,unused)))
        ==> MEM c unused \/
            ?m. m < n /\
                MEM c (resolvents_sem M
                         (HD(SND(given_sem M m (used,unused))))
                         (CONS (HD(SND(given_sem M m (used,unused))))
                               (FST(given_sem M m (used,unused)))))]])
   (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
    INDUCT_TAC THEN SIMP_TAC [given_sem] THEN
    SUBST1_TAC (← HolLight.SYM (← HolLight.ISPEC ([[given_sem M n (used,unused)]]) PAIR)) THEN
    PURE_REWRITE_TAC [step_sem] THEN
    COND_CASES_TAC THEN REWRITE_TAC [] THENL
     [ASM_MESON_TAC [(← ExceptT.mk (ARITH_RULE [[x < n ==> x < SUC n]]))], ALL_TAC] THEN
    LET_TAC THEN REWRITE_TAC [SND] THEN
    DISCH_THEN (MP_TAC oTIO HolLight.MATCH_MP ITLIST_INCORPORATE_FROMNEW) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THENL [ASM_MESON_TAC [LT], ALL_TAC] THEN
    SUBGOAL_THEN ([[MEM c (SND (given_sem M n (used,unused)))]])
     (fun th => FIRST_ASSUM (MP_TAC o HolCore.Lib.C HolLight.MATCH_MP th))
    THENL
     [UNDISCH_TAC [[MEM c (TL (SND (given_sem M n (used,unused))))]] THEN
      UNDISCH_TAC [[~(SND (given_sem M n (used,unused)) = [])]] THEN
      SPEC_TAC ([[SND (given_sem M n (used,unused))]], [[l:(form->bool)list]]) THEN
      LIST_INDUCT_TAC THEN SIMP_TAC [MEM, TL], ALL_TAC] THEN
    MESON_TAC [(← ExceptT.mk (ARITH_RULE [[x < n ==> x < SUC n]]))])
  : ExceptT String IO thm).run
#eval UNUSED_FROMNEW

#eval phrase 55
unsafe def SUB_FROMNEW : thm := keep "SUB_FROMNEW" fun _ => (do
  let _lemma ← prove
   ([[!l. ~(l = []) ==> MEM (HD l) l]])
    (LIST_INDUCT_TAC THEN REWRITE_TAC [MEM, HD])
  prove ([[!used unused c n.
        c IN Sub_SEM M (used,unused) n
        ==> MEM c unused \/
            ?m. m < n /\
                MEM c (resolvents_sem M
                         (HD(SND(given_sem M m (used,unused))))
                         (CONS (HD(SND(given_sem M m (used,unused))))
                               (FST(given_sem M m (used,unused)))))]])
   (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC [Sub_SEM, NOT_IN_EMPTY] THEN
    COND_CASES_TAC THENL
     [ASM_MESON_TAC [(← ExceptT.mk (ARITH_RULE [[x < n ==> x < SUC n]]))], ALL_TAC] THEN
    REWRITE_TAC [IN_INSERT] THEN STRIP_TAC THENL
     [ALL_TAC, ASM_MESON_TAC [(← ExceptT.mk (ARITH_RULE [[x < n ==> x < SUC n]]))]] THEN
    SUBGOAL_THEN ([[MEM c (SND(given_sem M n (used,unused)))]])
     (fun th => HolLight.tactic_of do
       let t ← HolLight.MATCH_MP UNUSED_FROMNEW th
       pure (MP_TAC t))
    THENL [ALL_TAC, MESON_TAC [(← ExceptT.mk (ARITH_RULE [[x < n ==> x < SUC n]]))]] THEN
    UNDISCH_TAC [[~(SND (given_sem M n (used,unused)) = [])]] THEN
    ASM_REWRITE_TAC [] THEN
    SPEC_TAC ([[SND (given_sem M n (used,unused))]], [[l:(form->bool)list]]) THEN
    LIST_INDUCT_TAC THEN SIMP_TAC [MEM, TL, HD])
  : ExceptT String IO thm).run
#eval SUB_FROMNEW

#eval phrase 56
unsafe def LEVEL_FROMNEW : thm := keep "LEVEL_FROMNEW" fun _ => (do
  prove ([[!used unused c n.
        c IN level_sem M (used,unused) n
        ==> MEM c unused \/
            ?m. MEM c (resolvents_sem M
                         (HD(SND(given_sem M m (used,unused))))
                         (CONS (HD(SND(given_sem M m (used,unused))))
                               (FST(given_sem M m (used,unused)))))]])
   (REWRITE_TAC [level_sem] THEN MESON_TAC [SUB_FROMNEW])
  : ExceptT String IO thm).run
#eval LEVEL_FROMNEW

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py from the `#eval`s above. -/
unsafe def ensure : IO Unit := once "HolLogicArith.GivenSem" do
  replay (
          HolLogicArith.Positive.ensure)
  replay (
          HOLDS_INTERP_SUBSUME)
  replay (
          isaresolvent_sem)
  replay (
          allresolvents_sem)
  replay (
          allntresolvents_sem)
  replay (
          ISARESOLVENT_SEM_SYM)
  replay (
          ALLRESOLVENTS_SEM_SYM)
  replay (
          ALLRESOLVENTS_SEM_UNION)
  replay (
          ALLRESOLVENTS_SEM_STEP)
  replay (
          resolvents_sem)
  replay (
          ISARESOLVENT_SEM_CLAUSE)
  replay (
          ALLRESOLVENTS_SEM_CLAUSE)
  replay (
          ISARESOLVENT_SEM_FINITE)
  replay (
          ALLRESOLVENTS_SEM_FINITE)
  replay (
          step_sem)
  replay (
          STEP_SEM)
  replay (
          given_sem)
  replay (
          Used_SEM)
  replay (
          Unused_SEM)
  replay (
          Sub_SEM)
  replay (
          ALLNTRESOLVENTS_SEM_STEP)
  replay (
          ALLNTRESOLVENTS_SEM_UNION)
  replay (
          USED_SUB)
  replay (
          GIVEN_INVARIANT)
  replay (
          SUB_MONO_SUBSET)
  replay (
          SUB_MONO)
  replay (
          LENGTH_REPLACE)
  replay (
          LENGTH_INCORPORATE)
  replay (
          LENGTH_UNUSED_CHANGE)
  replay (
          LENGTH_UNUSED_ZERO)
  replay (
          REPLACE_SUBSUMES_SELF)
  replay (
          INCORPORATE_SUBSUMES_SELF)
  replay (
          REPLACE_CLAUSE)
  replay (
          INCORPORATE_CLAUSE)
  replay (
          INCORPORATE_CLAUSE_EL)
  replay (
          UNUSED_SUBSUMES_SELF)
  replay (
          SUB_SUBSUMES_UNUSED)
  replay (
          break_sem)
  replay (
          level_sem)
  replay (
          LEVEL_0)
  replay (
          LEVEL_STEP)
  replay (
          level_CLAUSE)
  replay (
          BREAK_MONO)
  replay (
          level_MONO_SUBSET)
  replay (
          level_MONO)
  replay (
          ISARESOLVENT_SEM_SUBSUME_L)
  replay (
          ISARESOLVENT_SEM_SUBSUME_R)
  replay (
          ISARESOLVENT_SEM_SUBSUME)
  replay (
          ALLRESOLVENTS_SEM_SUBSUME_L)
  replay (
          ALLRESOLVENTS_SEM_SUBSUME_R)
  replay (
          ALLRESOLVENTS_SEM_SUBSUME)
  replay (
          ISARESOLVENT_SEM_TAUTOLOGY_L)
  replay (
          TAUTOLOGOUS_SUBSUMES)
  replay (
          ISARESOLVENT_SEM_TAUTOLOGY_R)
  replay (
          UNUSED_FROMNEW)
  replay (
          SUB_FROMNEW)
  replay (
          LEVEL_FROMNEW)
-- @@ENSURE END

end HolLogicArith.GivenSem
