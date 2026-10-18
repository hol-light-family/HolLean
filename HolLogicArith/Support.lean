/- File: HolLogicArith/Support.lean
Translation of HOL Light's Logic/support.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolLogicArith.Linear
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

namespace HolLogicArith.Support

/- List definitions/theorems used below are exposed by Session as fields of
   the `listDefs`/`listThms1`/`listThms2` bundles; alias the ones we need. -/
private unsafe def MEM : thm := Session.listDefs.MEM
private unsafe def MAP_o : thm := Session.listThms1.MAP_o
private unsafe def MAP_EQ : thm := Session.listThms1.MAP_EQ

#eval HolLogicArith.Linear.ensure

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- `new_inductive_definition`, panicking with HOL Light's message on failure. -/
private unsafe def newInductive (tm : term) : thm × thm × thm :=
  match unsafeIO (Session.new_inductive_definition tm) with
  | .ok (.ok t) => t
  | .ok (.error e) => panic! s!"new_inductive_definition: {e}"
  | .error e => panic! s!"new_inductive_definition IO: {e}"

#eval phrase 1
unsafe def NEGATE_LITERAL : thm := keep "NEGATE_LITERAL" fun _ => (do
  prove ([[!q. literal q ==> literal(~~q)]])
   (REWRITE_TAC [literal, ATOM] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [] THEN ASM_MESON_TAC [ATOM, NEGATE_ATOM, NEGATE_NEG])
  : ExceptT String IO thm).run
#eval NEGATE_LITERAL

#eval phrase 2
unsafe def RESOLVE_CLAUSE : thm := keep "RESOLVE_CLAUSE" fun _ => (do
  prove ([[!c1 c2 p. clause c1 /\ clause c2 ==> clause(resolve p c1 c2)]])
   (REWRITE_TAC [clause, resolve, FINITE_UNION, IN_UNION, IN_DELETE] THEN
    MESON_TAC [DELETE_SUBSET, FINITE_SUBSET])
  : ExceptT String IO thm).run
#eval RESOLVE_CLAUSE

#eval phrase 3
unsafe def PRESPROOF_CLAUSE : thm := keep "PRESPROOF_CLAUSE" fun _ => (do
  prove ([[!hyps cl. (!c. c IN hyps ==> clause c) /\ presproof hyps cl ==> clause cl]])
   (REWRITE_TAC [IMP_CONJ] THEN
    GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC presproof_INDUCT THEN ASM_MESON_TAC [RESOLVE_CLAUSE])
  : ExceptT String IO thm).run
#eval PRESPROOF_CLAUSE

#eval phrase 4
unsafe def RESOLVE_MONO : thm := keep "RESOLVE_MONO" fun _ => (do
  prove ([[!c1 c2 c1' c2' p.
        c1 SUBSET c1' /\ c2 SUBSET c2'
        ==> (resolve p c1 c2) SUBSET (resolve p c1' c2')]])
   (REWRITE_TAC [SUBSET, resolve, IN_UNION, IN_DELETE] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval RESOLVE_MONO

#eval phrase 5
unsafe def RESOLVE_SYM : thm := keep "RESOLVE_SYM" fun _ => (do
  prove ([[!c1 c2 p. literal p ==> (resolve (~~p) c1 c2 = resolve p c2 c1)]])
   (SIMP_TAC [resolve, NEGATE_NEGATE, UNION_ACI])
  : ExceptT String IO thm).run
#eval RESOLVE_SYM

#eval phrase 6
unsafe def RESOLVE_TAUT_L : thm := keep "RESOLVE_TAUT_L" fun _ => (do
  prove ([[!c1 c2 p. clause c1 /\ tautologous c1
             ==> tautologous(resolve p c1 c2) \/ c2 SUBSET (resolve p c1 c2)]])
   (REWRITE_TAC [tautologous, SUBSET, resolve, IN_DELETE, IN_UNION, clause] THEN
    REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[q:form]]) STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC [[(p = q) \/ (p = ~~q)]] THENL
     [FIRST_X_ASSUM (DISJ_CASES_THEN SUBST_ALL_TAC), ALL_TAC] THEN
    ASM_MESON_TAC [NEGATE_REFL, NEGATE_NEGATE])
  : ExceptT String IO thm).run
#eval RESOLVE_TAUT_L

#eval phrase 7
unsafe def RESOLVE_TAUT_R : thm := keep "RESOLVE_TAUT_R" fun _ => (do
  prove ([[!c1 c2 p. clause c2 /\ tautologous c2 /\ literal p
             ==> tautologous(resolve p c1 c2) \/ c1 SUBSET (resolve p c1 c2)]])
   (REWRITE_TAC [tautologous, SUBSET, resolve, IN_DELETE, IN_UNION, clause] THEN
    REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[q:form]]) STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC [[(p = q) \/ (p = ~~q)]] THENL
     [FIRST_X_ASSUM (DISJ_CASES_THEN SUBST_ALL_TAC), ALL_TAC] THEN
    ASM_MESON_TAC [NEGATE_REFL, NEGATE_NEGATE])
  : ExceptT String IO thm).run
#eval RESOLVE_TAUT_R

#eval phrase 8
unsafe def SUBSET_TAUT : thm := keep "SUBSET_TAUT" fun _ => (do
  prove ([[!c1 c2. tautologous c1 /\ c1 SUBSET c2 ==> tautologous c2]])
   (REWRITE_TAC [tautologous, SUBSET] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval SUBSET_TAUT

#eval phrase 9
unsafe def npresproof_triple : thm × thm × thm := keep "npresproof_triple" fun _ =>
  newInductive
    [[(!cl. cl IN hyps ==> npresproof hyps cl 1) /\
      (!p n1 n2 cl1 cl2.
                  npresproof hyps cl1 n1 /\
                  npresproof hyps cl2 n2 /\
                  p IN cl1 /\
                  ~~ p IN cl2
                  ==> npresproof hyps (resolve p cl1 cl2) (n1 + n2 + 1))]]
unsafe def npresproof_RULES : thm := npresproof_triple.1
unsafe def npresproof_INDUCT : thm := npresproof_triple.2.1
unsafe def npresproof_CASES : thm := npresproof_triple.2.2
#eval do IO.println npresproof_RULES; IO.println npresproof_INDUCT; IO.println npresproof_CASES

#eval phrase 10
unsafe def NPRESPROOF : thm := keep "NPRESPROOF" fun _ => (do
  prove ([[!hyps cl. presproof hyps cl <=> ?n. npresproof hyps cl n]])
   (GEN_TAC THEN REWRITE_TAC [(← ExceptT.mk (TAUT [[(a <=> b) <=> (a ==> b) /\ (b ==> a)]]))] THEN
    REWRITE_TAC [FORALL_AND_THM, LEFT_IMP_EXISTS_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC presproof_INDUCT THEN MESON_TAC [npresproof_RULES],
      MATCH_MP_TAC npresproof_INDUCT THEN MESON_TAC [presproof_RULES]])
  : ExceptT String IO thm).run
#eval NPRESPROOF

#eval phrase 11
unsafe def NPRESPROOF_CLAUSE : thm := keep "NPRESPROOF_CLAUSE" fun _ => (do
  prove ([[!hyps cl n. (!c. c IN hyps ==> clause c) /\ npresproof hyps cl n
                ==> clause cl]])
   (MESON_TAC [NPRESPROOF, PRESPROOF_CLAUSE])
  : ExceptT String IO thm).run
#eval NPRESPROOF_CLAUSE

#eval phrase 12
unsafe def psresproof_triple : thm × thm × thm := keep "psresproof_triple" fun _ =>
  newInductive
    [[(!c. c IN hyps /\ ~(tautologous c)
           ==> psresproof hyps sos (c IN sos) c) /\
      (!c1 c2 s1 s2 p.
          psresproof hyps sos s1 c1 /\
          psresproof hyps sos s2 c2 /\
          p IN c1 /\ ~~p IN c2 /\ (s1 \/ s2) /\ ~tautologous(resolve p c1 c2)
          ==> psresproof hyps sos T (resolve p c1 c2))]]
unsafe def psresproof_RULES : thm := psresproof_triple.1
unsafe def psresproof_INDUCT : thm := psresproof_triple.2.1
unsafe def psresproof_CASES : thm := psresproof_triple.2.2
#eval do IO.println psresproof_RULES; IO.println psresproof_INDUCT; IO.println psresproof_CASES

#eval phrase 13
unsafe def PSRESPROOF_CLAUSE : thm := keep "PSRESPROOF_CLAUSE" fun _ => (do
  prove ([[!hyps sos. (!c. c IN hyps ==> clause(c))
              ==> !s cl. psresproof hyps sos s cl ==> clause cl]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC psresproof_INDUCT THEN ASM_SIMP_TAC [RESOLVE_CLAUSE])
  : ExceptT String IO thm).run
#eval PSRESPROOF_CLAUSE

#eval phrase 14
unsafe def SUPPORT_ASYMMETRIC : thm := keep "SUPPORT_ASYMMETRIC" fun _ => (do
  prove ([[!hyps sos A B C p q nb nc.
      (!c. c IN hyps ==> clause c /\ ~tautologous c) /\
      ~tautologous(resolve p A (resolve q B C)) /\
      psresproof hyps sos T A /\
      npresproof (hyps DIFF sos) B nb /\
      npresproof (hyps DIFF sos) C nc /\
      p IN A /\ ~~p IN (resolve q B C) /\ q IN B /\ ~~ q IN C /\
      ~~p IN B /\ ~(q = ~~p) /\
      (!m. m < nb + nc + 1
              ==> (!c1 c2 p.
                       psresproof hyps sos T c1 /\
                       npresproof (hyps DIFF sos) c2 m /\
                       p IN c1 /\
                       ~~ p IN c2 /\
                       ~tautologous (resolve p c1 c2)
                       ==> (?cl'. cl' SUBSET resolve p c1 c2 /\
                                  (psresproof hyps sos T cl' \/
                                   (?m'. m' < m /\
                                         npresproof (hyps DIFF sos) cl' m')))))
      ==> ?cl'. cl' SUBSET resolve p A (resolve q B C) /\
                (psresproof hyps sos T cl' \/
                 ?m. m < nb + nc + 1 /\ npresproof (hyps DIFF sos) cl' m)]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[clause A /\ clause B /\ clause C]]) STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC [PSRESPROOF_CLAUSE, NPRESPROOF_CLAUSE, IN_DIFF],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[literal p /\ literal q]]) STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC [clause], ALL_TAC] THEN
    ASM_CASES_TAC [[tautologous (resolve q B C)]] THENL
     [ASM_MESON_TAC [RESOLVE_TAUT_R, RESOLVE_CLAUSE, clause], ALL_TAC] THEN
    ASM_CASES_TAC [[p:form = q]] THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN ([[(resolve q A C) SUBSET (resolve q A (resolve q B C))]])
      ASSUME_TAC THENL
       [MATCH_MP_TAC RESOLVE_MONO THEN REWRITE_TAC [SUBSET_REFL] THEN
        ASM_MESON_TAC [RESOLVE_TAUT_L, tautologous], ALL_TAC] THEN
      FIRST_ASSUM (MP_TAC oTIO (HolCore.Lib.C HolLight.MATCH_MP (← ExceptT.mk (ARITH_RULE [[nc < nb + nc + 1]])))) THEN
      DISCH_THEN (MP_TAC o HolLight.SPECL [ [[A:form->bool]], [[C:form->bool]], [[q:form]] ]) THEN
      ASM_REWRITE_TAC [] THEN
      ANTS_TAC THENL [ASM_MESON_TAC [SUBSET_TAUT], ALL_TAC] THEN
      ASM_MESON_TAC [SUBSET_TRANS, (← ExceptT.mk (ARITH_RULE [[x < c ==> x < b + c + 1]]))],
      ALL_TAC] THEN
    SUBGOAL_THEN
     ([[~(~~p IN C)
      ==> (resolve q (resolve p A B) C) SUBSET (resolve p A (resolve q B C))]])
    ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [ [[p:form IN A]], [[~~p IN B]], [[~~p IN resolve q B C]],
        [[q:form IN B]], [[~~q IN C]] ] THEN
      REWRITE_TAC [resolve, IN_UNION, IN_DELETE, SUBSET] THEN
      MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN
     ([[~~p IN C ==> (resolve p A (resolve q (resolve p A B) C)) SUBSET
                   (resolve p A (resolve q B C))]])
    ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [ [[p:form IN A]], [[~~p IN B]], [[~~p IN resolve q B C]],
        [[q:form IN B]], [[~~q IN C]] ] THEN
      REWRITE_TAC [resolve, IN_UNION, IN_DELETE, SUBSET] THEN
      MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN
     ([[~~p IN C ==> ~~p IN (resolve q (resolve p A B) C)]])
    ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [ [[p:form IN A]], [[~~p IN B]], [[~~p IN resolve q B C]],
        [[q:form IN B]], [[~~q IN C]], [[~(q = ~~ p)]], [[~(p:form = q)]] ] THEN
      REWRITE_TAC [resolve, IN_UNION, IN_DELETE, SUBSET] THEN
      ASM_MESON_TAC [NEGATE_NEGATE], ALL_TAC] THEN
    ASM_CASES_TAC [[tautologous(resolve q (resolve p A B) C)]] THENL
     [SUBGOAL_THEN ([[~~p IN C]])
       (fun th => RULE_ASSUM_TAC (HolLight.REWRITE_RULE [th]) THEN ASSUME_TAC th) THEN
      ASM_MESON_TAC [RESOLVE_TAUT_R, SUBSET_TRANS, RESOLVE_CLAUSE, SUBSET_TAUT],
      ALL_TAC] THEN
    ASM_CASES_TAC [[tautologous(resolve p A B)]] THENL
     [ASM_CASES_TAC [[~~p IN C]] THENL
       [REPEAT (FIRST_X_ASSUM (ASSUME_TAC oTIO (HolCore.Lib.C HolLight.MATCH_MP (ASSUME [[~~p IN C]])))) THEN
        SUBGOAL_THEN ([[(resolve p A C) SUBSET (resolve p A (resolve q B C))]])
        ASSUME_TAC THENL
         [ASM_MESON_TAC [RESOLVE_MONO, SUBSET_REFL, SUBSET_TRANS,
                        RESOLVE_TAUT_L, RESOLVE_CLAUSE], ALL_TAC] THEN
        FIRST_X_ASSUM (MP_TAC oTIO (HolCore.Lib.C HolLight.MATCH_MP (← ExceptT.mk (ARITH_RULE [[nc < nb + nc + 1]])))) THEN
        DISCH_THEN (MP_TAC o
          HolLight.SPECL [ [[A:form->bool]], [[C:form->bool]], [[p:form]] ]) THEN
        ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
         [ASM_MESON_TAC [SUBSET_TAUT], ALL_TAC] THEN
        ASM_MESON_TAC [SUBSET_TRANS, (← ExceptT.mk (ARITH_RULE [[x < nc ==> x < nb + nc + 1]]))],
        ALL_TAC] THEN
      REPEAT (FIRST_X_ASSUM (ASSUME_TAC oTIO (HolCore.Lib.C HolLight.MATCH_MP (ASSUME [[~(~~p IN C)]])))) THEN
      ASM_MESON_TAC [SUBSET_TRANS, RESOLVE_TAUT_L, RESOLVE_CLAUSE, (← ExceptT.mk (ARITH_RULE
          [[nc < nb + nc + 1]]))],
      ALL_TAC] THEN
    FIRST_ASSUM (MP_TAC o HolLight.SPEC [[nb:num]]) THEN
    REWRITE_TAC [(← ExceptT.mk (ARITH_RULE [[nb < nb + nc + 1]]))] THEN
    DISCH_THEN (MP_TAC o HolLight.SPECL [ [[A:form->bool]], [[B:form->bool]], [[p:form]] ]) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[D:form->bool]]) (CONJUNCTS_THEN ASSUME_TAC)) THEN
    ASM_CASES_TAC [[q:form IN D]] THENL
     [ALL_TAC,
      EXISTS_TAC [[D:form->bool]] THEN CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [ [[D SUBSET resolve p A B]], [[~(q:form IN D)]],
          [[~(~~ p IN C)
           ==> resolve q (resolve p A B) C SUBSET
               resolve p A (resolve q B C)]] ] THEN
        REWRITE_TAC [resolve, SUBSET, IN_UNION, IN_DELETE] THEN
        MESON_TAC [], ALL_TAC] THEN
      ASM_MESON_TAC [(← ExceptT.mk (ARITH_RULE [[x < nb ==> x < nb + nc + 1]]))]] THEN
    FIRST_X_ASSUM (DISJ_CASES_THEN MP_TAC) THENL
     [ALL_TAC,
      DISCH_THEN (X_CHOOSE_THEN ([[nd:num]]) STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC [[~~p IN C]] THENL
       [REPEAT (FIRST_X_ASSUM (ASSUME_TAC oTIO (HolCore.Lib.C HolLight.MATCH_MP (ASSUME [[~~p IN C]])))) THEN
        FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[nd + nc + 1]]) THEN
        REWRITE_TAC [LT_ADD_RCANCEL] THEN ASM_REWRITE_TAC [] THEN
        DISCH_THEN (MP_TAC o HolLight.SPECL
         [ [[A:form->bool]], [[resolve q D C]], [[p:form]] ]) THEN
        ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
         [REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC (← liftExcept (Session.CONJUNCT2 (← ExceptT.mk (HolLight.SPEC_ALL npresproof_RULES)))) THEN
            ASM_REWRITE_TAC [],
            SUBGOAL_THEN ([[~(~~p = ~~q)]]) MP_TAC THENL
             [ASM_MESON_TAC [NEGATE_NEGATE], ALL_TAC] THEN
            UNDISCH_TAC [[~~p IN C]] THEN
            REWRITE_TAC [resolve, IN_UNION, IN_DELETE] THEN MESON_TAC [],
            ASM_MESON_TAC [SUBSET_TAUT, RESOLVE_MONO, SUBSET_REFL,
                          SUBSET_TRANS]],
          ALL_TAC] THEN
        ASM_MESON_TAC [RESOLVE_MONO, SUBSET_REFL, SUBSET_TRANS,
                      (← ExceptT.mk (ARITH_RULE [[d < b /\ m < d + c ==> m < b + c]]))],
        ALL_TAC] THEN
      REPEAT (FIRST_X_ASSUM (ASSUME_TAC oTIO (HolCore.Lib.C HolLight.MATCH_MP (ASSUME [[~(~~p IN C)]])))) THEN
      EXISTS_TAC [[resolve q D C]] THEN CONJ_TAC THENL
       [ASM_MESON_TAC [RESOLVE_MONO, SUBSET_REFL, SUBSET_TRANS], ALL_TAC] THEN
      DISJ2_TAC THEN EXISTS_TAC [[nd + nc + 1]] THEN
      ASM_REWRITE_TAC [LT_ADD_RCANCEL] THEN
      MATCH_MP_TAC (← liftExcept (Session.CONJUNCT2 (← ExceptT.mk (HolLight.SPEC_ALL npresproof_RULES)))) THEN
      ASM_REWRITE_TAC []] THEN
    DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC oTIO (HolCore.Lib.C HolLight.MATCH_MP (← ExceptT.mk (ARITH_RULE [[nc < nb + nc + 1]])))) THEN
    DISCH_THEN (MP_TAC o HolLight.SPECL [ [[D:form->bool]], [[C:form->bool]], [[q:form]] ]) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [ASM_MESON_TAC [SUBSET_TAUT, RESOLVE_MONO, SUBSET_REFL, SUBSET_TRANS],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[E:form->bool]]) MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (DISJ_CASES_THEN MP_TAC)) THENL
     [DISCH_TAC THEN
      ASM_CASES_TAC [[~~p IN C]] THENL
       [ALL_TAC,
        REPEAT (FIRST_X_ASSUM (ASSUME_TAC oTIO
         (HolCore.Lib.C HolLight.MATCH_MP (ASSUME [[~(~~p IN C)]])))) THEN
        EXISTS_TAC [[E:form->bool]] THEN ASM_REWRITE_TAC [] THEN
        ASM_MESON_TAC [RESOLVE_MONO, SUBSET_REFL, SUBSET_TRANS]] THEN
      ASM_CASES_TAC [[~~p IN E]] THENL
       [EXISTS_TAC [[resolve p A E]] THEN CONJ_TAC THENL
         [ASM_MESON_TAC [RESOLVE_MONO, SUBSET_REFL, SUBSET_TRANS], ALL_TAC] THEN
        DISJ1_TAC THEN MATCH_MP_TAC (← liftExcept (Session.CONJUNCT2 (← ExceptT.mk (HolLight.SPEC_ALL psresproof_RULES)))) THEN
        REPEAT (EXISTS_TAC [[T]]) THEN ASM_REWRITE_TAC [] THEN
        ASM_MESON_TAC [SUBSET_TAUT, RESOLVE_MONO, SUBSET_REFL, SUBSET_TRANS],
        ALL_TAC] THEN
      EXISTS_TAC [[E:form->bool]] THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC [[resolve p A E]] THEN
      CONJ_TAC THENL
       [ALL_TAC, ASM_MESON_TAC [RESOLVE_MONO, SUBSET_REFL, SUBSET_TRANS]] THEN
      UNDISCH_TAC [[~(~~p IN E)]] THEN
      REWRITE_TAC [resolve, SUBSET, IN_UNION, IN_DELETE] THEN MESON_TAC [],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[ne:num]]) STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC [[~~p IN C]] THENL
     [ALL_TAC,
      REPEAT (FIRST_X_ASSUM (ASSUME_TAC oTIO (HolCore.Lib.C HolLight.MATCH_MP (ASSUME [[~(~~p IN C)]])))) THEN
      EXISTS_TAC [[E:form->bool]] THEN ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC [RESOLVE_MONO, SUBSET_REFL, SUBSET_TRANS,
                    (← ExceptT.mk (ARITH_RULE [[ne < nc ==> ne < nb + nc + 1]]))]] THEN
    REPEAT (FIRST_X_ASSUM (ASSUME_TAC oTIO (HolCore.Lib.C HolLight.MATCH_MP (ASSUME [[~~p IN C]])))) THEN
    ASM_CASES_TAC [[~~p IN E]] THENL
     [ALL_TAC,
      EXISTS_TAC [[E:form->bool]] THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC [[resolve p A E]] THEN
        CONJ_TAC THENL
         [ALL_TAC, ASM_MESON_TAC [RESOLVE_MONO, SUBSET_REFL, SUBSET_TRANS]] THEN
        UNDISCH_TAC [[~(~~p IN E)]] THEN
        REWRITE_TAC [resolve, SUBSET, IN_UNION, IN_DELETE] THEN MESON_TAC [],
        ALL_TAC] THEN
      ASM_MESON_TAC [(← ExceptT.mk (ARITH_RULE [[ne < nc ==> ne < nb + nc + 1]]))]] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[ne:num]]) THEN
    ASM_SIMP_TAC [(← ExceptT.mk (ARITH_RULE [[ne < nc ==> ne < nb + nc + 1]]))] THEN
    DISCH_THEN (MP_TAC o HolLight.SPECL [ [[A:form->bool]], [[E:form->bool]], [[p:form]] ]) THEN
    ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [SUBSET_TAUT, RESOLVE_MONO, SUBSET_REFL, SUBSET_TRANS,
                  (← ExceptT.mk (ARITH_RULE [[m < ne /\ ne < nc ==> m < nb + nc + 1]]))])
  : ExceptT String IO thm).run
#eval SUPPORT_ASYMMETRIC

#eval phrase 15
unsafe def SUPPORT_SYMMETRIC : thm := keep "SUPPORT_SYMMETRIC" fun _ => (do
  prove ([[!hyps sos A B C p q nb nc.
      (!c. c IN hyps ==> clause c /\ ~tautologous c) /\
      ~tautologous(resolve p A (resolve q B C)) /\
      psresproof hyps sos T A /\
      npresproof (hyps DIFF sos) B nb /\
      npresproof (hyps DIFF sos) C nc /\
      p IN A /\ ~~p IN (resolve q B C) /\ q IN B /\ ~~ q IN C /\
      (!m. m < nb + nc + 1
              ==> (!c1 c2 p.
                       psresproof hyps sos T c1 /\
                       npresproof (hyps DIFF sos) c2 m /\
                       p IN c1 /\
                       ~~ p IN c2 /\
                       ~tautologous (resolve p c1 c2)
                       ==> (?cl'. cl' SUBSET resolve p c1 c2 /\
                                  (psresproof hyps sos T cl' \/
                                   (?m'. m' < m /\
                                         npresproof (hyps DIFF sos) cl' m')))))
      ==> ?cl'. cl' SUBSET resolve p A (resolve q B C) /\
                (psresproof hyps sos T cl' \/
                 ?m. m < nb + nc + 1 /\ npresproof (hyps DIFF sos) cl' m)]])
   (REPEAT STRIP_TAC THEN MP_TAC (ASSUME [[~~p IN (resolve q B C)]]) THEN
    DISCH_THEN (MP_TAC oTIO HolLight.REWRITE_RULE [resolve, IN_UNION, IN_DELETE]) THEN
    STRIP_TAC THENL
     [MP_TAC (← HolLight.SPECL [ [[hyps:(form->bool)->bool]], [[sos:(form->bool)->bool]],
                    [[A:form->bool]], [[B:form->bool]], [[C:form->bool]],
                    [[p:form]], [[q:form]], [[nb:num]], [[nc:num]] ]
                   SUPPORT_ASYMMETRIC) THEN
      ASM_REWRITE_TAC [],
      MP_TAC (← HolLight.SPECL [ [[hyps:(form->bool)->bool]], [[sos:(form->bool)->bool]],
                    [[A:form->bool]], [[C:form->bool]], [[B:form->bool]],
                    [[p:form]], [[~~q]], [[nc:num]], [[nb:num]] ]
                   SUPPORT_ASYMMETRIC) THEN
      ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN ([[clause A /\ clause B /\ clause C]]) STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC [PSRESPROOF_CLAUSE, NPRESPROOF_CLAUSE, IN_DIFF],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[literal q]]) ASSUME_TAC THENL
       [ASM_MESON_TAC [clause], ALL_TAC] THEN
      HolLight.GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV)
       [(← ExceptT.mk (ARITH_RULE [[a + b + 1 = b + a + 1]]))] THEN
      ASM_SIMP_TAC [RESOLVE_SYM, NEGATE_NEGATE]])
  : ExceptT String IO thm).run
#eval SUPPORT_SYMMETRIC

#eval phrase 16
unsafe def SUPPORT_LEMMA : thm := keep "SUPPORT_LEMMA" fun _ => (do
  prove ([[!hyps sos.
        (!c. c IN hyps ==> clause c /\ ~tautologous c)
        ==> !n c1 c2 p.
                psresproof hyps sos T c1 /\
                npresproof (hyps DIFF sos) c2 n /\
                p IN c1 /\ ~~p IN c2 /\
                ~(tautologous(resolve p c1 c2))
                ==> ?cl'. cl' SUBSET (resolve p c1 c2) /\
                          (psresproof hyps sos T cl' \/
                           ?m. m < n /\ npresproof (hyps DIFF sos) cl' m)]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC num_WF THEN
    X_GEN_TAC [[n:num]] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [ [[A:form->bool]], [[Z:form->bool]], [[p:form]] ] THEN
    STRIP_TAC THEN
    MP_TAC (ASSUME [[npresproof (hyps DIFF sos) Z n]]) THEN
    HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [npresproof_CASES] THEN
    DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL
     [DISCH_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
      EXISTS_TAC [[resolve p A Z]] THEN REWRITE_TAC [SUBSET_REFL] THEN
      DISJ1_TAC THEN MATCH_MP_TAC (← liftExcept (Session.CONJUNCT2 (← ExceptT.mk (HolLight.SPEC_ALL psresproof_RULES)))) THEN
      MAP_EVERY EXISTS_TAC [ [[T]], [[F]] ] THEN ASM_REWRITE_TAC [] THEN
      MP_TAC (← HolLight.SPECL [ [[hyps:(form->bool)->bool]], [[sos:(form->bool)->bool]] ]
                   psresproof_RULES) THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC [[Z:form->bool]] oTIO HolLight.CONJUNCT1) THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [IN_DIFF]) THEN ASM_SIMP_TAC [], ALL_TAC] THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
     [ [[q:form]], [[nb:num]], [[nc:num]], [[B:form->bool]], [[C:form->bool]] ] THEN
    DISCH_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [ [[hyps:(form->bool)->bool]], [[sos:(form->bool)->bool]],
                    [[A:form->bool]], [[B:form->bool]], [[C:form->bool]],
                    [[p:form]], [[q:form]], [[nb:num]], [[nc:num]] ]
                 SUPPORT_SYMMETRIC) THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval SUPPORT_LEMMA

#eval phrase 17
unsafe def SUPPORT_INDUCT_LEMMA : thm := keep "SUPPORT_INDUCT_LEMMA" fun _ => (do
  prove ([[!hyps sos p c1 c2.
        (!c. c IN hyps ==> clause c /\ ~tautologous c) /\
        psresproof hyps sos T c1 /\
        presproof (hyps DIFF sos) c2 /\
        p IN c1 /\ ~~p IN c2 /\ ~(tautologous(resolve p c1 c2))
        ==> ?cl'. cl' SUBSET (resolve p c1 c2) /\
                  (presproof (hyps DIFF sos) cl' \/
                   psresproof hyps sos T cl')]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [ [[hyps:(form->bool)->bool]], [[sos:(form->bool)->bool]] ]
                 SUPPORT_LEMMA) THEN ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [NPRESPROOF]) THEN
    DISCH_THEN (X_CHOOSE_TAC [[n:num]]) THEN
    DISCH_THEN (MP_TAC o HolLight.SPECL
     [ [[n:num]], [[c1:form->bool]], [[c2:form->bool]], [[p:form]] ]) THEN
    ASM_REWRITE_TAC [] THEN MESON_TAC [NPRESPROOF])
  : ExceptT String IO thm).run
#eval SUPPORT_INDUCT_LEMMA

#eval phrase 18
unsafe def SUPPORT_INDUCT : thm := keep "SUPPORT_INDUCT" fun _ => (do
  prove ([[!hyps sos.
     (!c. c IN hyps ==> clause c /\ ~(tautologous c))
     ==> !cl. presproof hyps cl
              ==> clause cl /\
                  (~(tautologous cl)
                   ==> ?cl'. cl' SUBSET cl /\
                                 (presproof (hyps DIFF sos) cl' \/
                                  psresproof hyps sos T cl'))]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC presproof_INDUCT THEN CONJ_TAC THENL
     [X_GEN_TAC [[cl:form->bool]] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [] THEN
      EXISTS_TAC [[cl:form->bool]] THEN REWRITE_TAC [SUBSET_REFL] THEN
      ASM_CASES_TAC [[cl:form->bool IN sos]] THENL
       [ALL_TAC, ASM_MESON_TAC [presproof_RULES, IN_DIFF]] THEN
      DISJ2_TAC THEN
      MP_TAC (← HolLight.SPECL [ [[hyps:(form->bool)->bool]], [[sos:(form->bool)->bool]] ]
                   psresproof_RULES) THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC [[cl:form->bool]] oTIO HolLight.CONJUNCT1) THEN
      ASM_SIMP_TAC [], ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [ [[p:form]], [[c1:form->bool]], [[c2:form->bool]] ] THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    ASM_SIMP_TAC [RESOLVE_CLAUSE] THEN DISCH_TAC THEN
    ASM_CASES_TAC [[tautologous c1]] THENL
     [SUBGOAL_THEN ([[~(tautologous c2)]]) ASSUME_TAC THENL
       [ASM_MESON_TAC [RESOLVE_TAUT_L, SUBSET_TAUT], ALL_TAC] THEN
      ASM_MESON_TAC [RESOLVE_TAUT_L, SUBSET_TRANS, SUBSET_UNION], ALL_TAC] THEN
    ASM_CASES_TAC [[tautologous c2]] THENL
     [ASM_MESON_TAC [RESOLVE_TAUT_R, clause, SUBSET_TRANS, SUBSET_UNION],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC oTIO (HolCore.Lib.C HolLight.MATCH_MP (ASSUME [[~(tautologous c2)]]))) THEN
    FIRST_X_ASSUM (MP_TAC oTIO (HolCore.Lib.C HolLight.MATCH_MP (ASSUME [[~(tautologous c1)]]))) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[c1':form->bool]])
     (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[c2':form->bool]])
     (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    ASM_CASES_TAC [[p:form IN c1']] THENL
     [ALL_TAC,
      EXISTS_TAC [[c1':form->bool]] THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [SUBSET, resolve, IN_UNION, IN_DELETE] THEN
      ASM_MESON_TAC [SUBSET]] THEN
    ASM_CASES_TAC [[~~p IN c2']] THENL
     [ALL_TAC,
      EXISTS_TAC [[c2':form->bool]] THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [SUBSET, resolve, IN_UNION, IN_DELETE] THEN
      ASM_MESON_TAC [SUBSET]] THEN
    UNDISCH_THEN
     ([[presproof (hyps DIFF sos) c1' \/ psresproof hyps sos T c1']])
     DISJ_CASES_TAC THEN FIRST_X_ASSUM DISJ_CASES_TAC
    THENL
     [ASM_MESON_TAC [presproof_RULES, RESOLVE_MONO],
      MP_TAC (← HolLight.SPECL [ [[hyps:(form->bool)->bool]], [[sos:(form->bool)->bool]],
                    [[~~p]], [[c2':form->bool]], [[c1':form->bool]] ]
                   SUPPORT_INDUCT_LEMMA) THEN
      ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
       [ASM_MESON_TAC [NEGATE_NEGATE, SUBSET_TAUT, RESOLVE_MONO,
                      clause, SUBSET, RESOLVE_SYM],
        ASM_MESON_TAC [RESOLVE_MONO, SUBSET_TRANS, SUBSET_TAUT,
                      clause, SUBSET, RESOLVE_SYM]],
      MP_TAC (← HolLight.SPECL [ [[hyps:(form->bool)->bool]], [[sos:(form->bool)->bool]],
                    [[p:form]], [[c1':form->bool]], [[c2':form->bool]] ]
                   SUPPORT_INDUCT_LEMMA) THEN
      ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC [RESOLVE_MONO, SUBSET_TRANS, SUBSET_TAUT],
      EXISTS_TAC [[resolve p c1' c2']] THEN ASM_SIMP_TAC [RESOLVE_MONO] THEN
      DISJ2_TAC THEN MATCH_MP_TAC (← liftExcept (Session.CONJUNCT2 (← ExceptT.mk (HolLight.SPEC_ALL psresproof_RULES)))) THEN
      REPEAT (EXISTS_TAC [[T]]) THEN ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC [SUBSET_TAUT, RESOLVE_MONO]])
  : ExceptT String IO thm).run
#eval SUPPORT_INDUCT

#eval phrase 19
unsafe def SUPPORT : thm := keep "SUPPORT" fun _ => (do
  prove ([[!sos hyps cl.
     (!c. c IN hyps ==> clause c /\ ~(tautologous c)) /\
     presproof hyps cl /\ ~(tautologous cl)
     ==> ?cl'. cl' SUBSET cl /\
               (presproof (hyps DIFF sos) cl' \/ psresproof hyps sos T cl')]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [ [[hyps:(form->bool)->bool]], [[sos:(form->bool)->bool]] ]
                 SUPPORT_INDUCT) THEN
    ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval SUPPORT

#eval phrase 20
unsafe def spresproof_triple : thm × thm × thm := keep "spresproof_triple" fun _ =>
  newInductive
    [[(!c. c IN hyps /\ c IN sos /\ ~(tautologous c)
           ==> spresproof hyps sos c) /\
      (!c1 c2 p.
               spresproof hyps sos c1 /\
               (spresproof hyps sos c2 \/ c2 IN hyps) /\
               p IN c1 /\ ~~p IN c2 /\
               ~(tautologous(resolve p c1 c2))
               ==> spresproof hyps sos (resolve p c1 c2))]]
unsafe def spresproof_RULES : thm := spresproof_triple.1
unsafe def spresproof_INDUCT : thm := spresproof_triple.2.1
unsafe def spresproof_CASES : thm := spresproof_triple.2.2
#eval do IO.println spresproof_RULES; IO.println spresproof_INDUCT; IO.println spresproof_CASES

#eval phrase 21
unsafe def SPRESPROOF_PSRESPROOF : thm := keep "SPRESPROOF_PSRESPROOF" fun _ => (do
  prove ([[!hyps sos. (!c. c IN hyps ==> clause c /\ ~(tautologous c))
              ==> !cl. spresproof hyps sos cl = psresproof hyps sos T cl]])
   (GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [(← ExceptT.mk (TAUT [[(a <=> b) <=> (a ==> b) /\ (b ==> a)]]))] THEN
    REWRITE_TAC [FORALL_AND_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC spresproof_INDUCT THEN CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN
        MP_TAC (← HolLight.SPECL [ [[hyps:(form->bool)->bool]], [[sos:(form->bool)->bool]] ]
                     psresproof_RULES) THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC [[c:form->bool]] oTIO HolLight.CONJUNCT1) THEN
        ASM_REWRITE_TAC [], ALL_TAC] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC (← liftExcept (Session.CONJUNCT2 (← ExceptT.mk (HolLight.SPEC_ALL psresproof_RULES)))) THENL
       [REPEAT (EXISTS_TAC [[T]]) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [ [[T]], [[c2:form->bool IN sos]] ] THEN
      ASM_SIMP_TAC [psresproof_RULES] THEN
      MATCH_MP_TAC (← liftExcept (Session.CONJUNCT1 (← ExceptT.mk (HolLight.SPEC_ALL psresproof_RULES)))) THEN
      ASM_MESON_TAC [IN_DIFF], ALL_TAC] THEN
    SUBGOAL_THEN
     ([[!s cl. psresproof hyps sos s cl
             ==> (if s then spresproof hyps sos cl
                  else cl IN hyps /\ ~(cl IN sos) /\ ~(tautologous cl))]])
     (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPEC ([[T]]) th) THEN REWRITE_TAC [])) THEN
    MATCH_MP_TAC psresproof_INDUCT THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
      ASM_MESON_TAC [spresproof_RULES], ALL_TAC] THEN
    REPEAT GEN_TAC THEN DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    REWRITE_TAC [] THEN
    POP_ASSUM_LIST (fun ths => HolLight.tactic_of do
      pure (MP_TAC (← HolLight.end_itlist HolLight.CONJ ths))) THEN
    MAP_EVERY BOOL_CASES_TAC [ [[s1:bool]], [[s2:bool]] ] THEN
    ASM_REWRITE_TAC [] THENL
     [MESON_TAC [spresproof_RULES],
      MESON_TAC [spresproof_RULES, IN_DIFF],
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[resolve p c1 c2 = resolve (~~p) c2 c1]]) SUBST_ALL_TAC THENL
     [ASM_MESON_TAC [RESOLVE_SYM, clause], ALL_TAC] THEN
    MATCH_MP_TAC (← liftExcept (Session.CONJUNCT2 (← ExceptT.mk (HolLight.SPEC_ALL spresproof_RULES)))) THEN
    ASM_REWRITE_TAC [IN_DIFF] THEN ASM_MESON_TAC [NEGATE_NEGATE, clause])
  : ExceptT String IO thm).run
#eval SPRESPROOF_PSRESPROOF

#eval phrase 22
unsafe def SPRESPROOF_CLAUSE_NONTAUT : thm := keep "SPRESPROOF_CLAUSE_NONTAUT" fun _ => (do
  prove ([[!hyps sos.
        (!c. c IN hyps ==> clause c /\ ~(tautologous c))
        ==> !c. spresproof hyps sos c ==> clause c /\ ~(tautologous c)]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC spresproof_INDUCT THEN
    ASM_SIMP_TAC [RESOLVE_CLAUSE, IN_DIFF] THEN ASM_MESON_TAC [RESOLVE_CLAUSE])
  : ExceptT String IO thm).run
#eval SPRESPROOF_CLAUSE_NONTAUT

#eval phrase 23
unsafe def SPRESPROOF_CLAUSE : thm := keep "SPRESPROOF_CLAUSE" fun _ => (do
  prove ([[!hyps sos.
        (!c. c IN hyps ==> clause c)
        ==> !c. spresproof hyps sos c ==> clause c]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC spresproof_INDUCT THEN
    ASM_SIMP_TAC [RESOLVE_CLAUSE, IN_DIFF] THEN ASM_MESON_TAC [RESOLVE_CLAUSE])
  : ExceptT String IO thm).run
#eval SPRESPROOF_CLAUSE

#eval phrase 24
unsafe def SPRESPROOF_MONO : thm := keep "SPRESPROOF_MONO" fun _ => (do
  prove ([[!hyps1 hyps2 sos cl.
      spresproof hyps1 sos cl /\ hyps1 SUBSET hyps2
      ==> spresproof hyps2 sos cl]])
   (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
    ONCE_REWRITE_TAC [IMP_CONJ_ALT] THEN
    REWRITE_TAC [SUBSET, RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC spresproof_INDUCT THEN
    ASM_MESON_TAC [IN_DIFF, spresproof_RULES])
  : ExceptT String IO thm).run
#eval SPRESPROOF_MONO

#eval phrase 25
unsafe def SPRESPROOF_MONO_SOS : thm := keep "SPRESPROOF_MONO_SOS" fun _ => (do
  prove ([[!hyps1 hyps2 sos1 sos2 cl.
      spresproof hyps1 sos1 cl /\ hyps1 SUBSET hyps2 /\ sos1 SUBSET sos2
      ==> spresproof hyps2 sos2 cl]])
   (ONCE_REWRITE_TAC [(← ExceptT.mk (TAUT [[a /\ b /\ c ==> d <=> b /\ c ==> a ==> d]]))] THEN
    REWRITE_TAC [SUBSET, RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN
    STRIP_TAC THEN MATCH_MP_TAC spresproof_INDUCT THEN
    ASM_MESON_TAC [spresproof_RULES])
  : ExceptT String IO thm).run
#eval SPRESPROOF_MONO_SOS

#eval phrase 26
unsafe def TAUTOLOGOUS_SATISFIED : thm := keep "TAUTOLOGOUS_SATISFIED" fun _ => (do
  prove ([[!c d. clause c /\ tautologous c ==> pholds d (interp c)]])
   (SIMP_TAC [clause, tautologous, PHOLDS_INTERP] THEN MESON_TAC [PHOLDS_NEGATE])
  : ExceptT String IO thm).run
#eval TAUTOLOGOUS_SATISFIED

#eval phrase 27
unsafe def PRESPROOF_SOUND : thm := keep "PRESPROOF_SOUND" fun _ => (do
  prove ([[!asm. (!c. c IN asm ==> clause c) /\ presproof asm {}
         ==> ~psatisfiable (IMAGE interp asm)]])
   (MESON_TAC [PSATISFIABLE_MONO, PPRESPROOF_SOUND, IMAGE_SUBSET, PPRESPROOF])
  : ExceptT String IO thm).run
#eval PRESPROOF_SOUND

#eval phrase 28
unsafe def SPRESPROOF_REFUTATION_COMPLETE : thm := keep "SPRESPROOF_REFUTATION_COMPLETE" fun _ => (do
  prove ([[!hyps sos.
        (!c. c IN hyps ==> clause c) /\
        ~(psatisfiable {interp cl | cl IN hyps}) /\
        psatisfiable {interp cl | cl IN (hyps DIFF sos)}
        ==> spresproof hyps sos {}]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [ [[sos:(form->bool)->bool]],
                  [[{c | c IN hyps /\ ~(tautologous c)}]],
                  [[ {}:(form->bool) ]] ] SUPPORT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC [IN_ELIM_THM],
        MATCH_MP_TAC PRESPROOF_REFUTATION_COMPLETE THEN CONJ_TAC THENL
         [ASM_SIMP_TAC [IN_ELIM_THM], ALL_TAC] THEN
        UNDISCH_TAC [[~psatisfiable {interp cl | cl IN hyps}]] THEN
        REWRITE_TAC [(← ExceptT.mk (TAUT [[~b ==> ~a <=> a ==> b]])), psatisfiable] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[d:form->bool]] THEN
        SIMP_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC [[p:form]] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC [[cl:form->bool]] THEN
        ASM_CASES_TAC [[tautologous cl]] THEN ASM_REWRITE_TAC [] THEN
        ASM_SIMP_TAC [TAUTOLOGOUS_SATISFIED],
        REWRITE_TAC [tautologous, NOT_IN_EMPTY]],
      ALL_TAC] THEN
    REWRITE_TAC [SUBSET_EMPTY, UNWIND_THM2] THEN STRIP_TAC THENL
     [FIRST_ASSUM (MP_TAC oTIO HolLight.MATCH_MP
       (← HolLight.REWRITE_RULE [IMP_CONJ_ALT]
                     PRESPROOF_SOUND)) THEN
      UNDISCH_TAC [[psatisfiable {interp cl | cl IN hyps DIFF sos}]] THEN
      MATCH_MP_TAC (← ExceptT.mk (TAUT [[(a ==> c) /\ b ==> a ==> (b ==> ~c) ==> d]])) THEN
      CONJ_TAC THENL [ALL_TAC, ASM_SIMP_TAC [IN_ELIM_THM, IN_DIFF]] THEN
      MATCH_MP_TAC (← HolLight.ONCE_REWRITE_RULE [IMP_CONJ_ALT]
                  PSATISFIABLE_MONO) THEN
      REWRITE_TAC [SUBSET, IN_IMAGE, IN_ELIM_THM, IN_DIFF] THEN MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[spresproof {c | c IN hyps /\ ~tautologous c} sos {}]])
    MP_TAC THENL
     [UNDISCH_TAC [[psresproof {c | c IN hyps /\ ~tautologous c} sos T {}]] THEN
      MATCH_MP_TAC (← ExceptT.mk (TAUT [[(b <=> a) ==> a ==> b]])) THEN
      SPEC_TAC ([[ {}:form->bool ]], [[cl:form->bool]]) THEN
      MATCH_MP_TAC SPRESPROOF_PSRESPROOF THEN ASM_SIMP_TAC [IN_ELIM_THM],
      ALL_TAC] THEN
    MATCH_MP_TAC (← HolLight.ONCE_REWRITE_RULE [(← ExceptT.mk (TAUT [[(a /\ b ==> c) <=> b ==> a ==> c]]))]
                  SPRESPROOF_MONO) THEN
    SIMP_TAC [IN_ELIM_THM, SUBSET])
  : ExceptT String IO thm).run
#eval SPRESPROOF_REFUTATION_COMPLETE

#eval phrase 29
unsafe def sresproof_triple : thm × thm × thm := keep "sresproof_triple" fun _ =>
  newInductive
    [[(!c. c IN hyps /\ c IN sos /\ ~(tautologous c)
           ==> sresproof hyps sos c) /\
      (!cl1 cl2 cl2' ps1 ps2 i.
         sresproof hyps sos cl1 /\
         (sresproof hyps sos cl2 \/ cl2 IN hyps) /\
         (IMAGE (formsubst (rename cl2 (FVS cl1))) cl2 = cl2') /\
         ps1 SUBSET cl1 /\
         ps2 SUBSET cl2' /\
         ~(ps1 = {}) /\
         ~(ps2 = {}) /\
         (?i. Unifies i (ps1 UNION {~~ p | p IN ps2})) /\
         (mgu (ps1 UNION {~~ p | p IN ps2}) = i) /\
         ~(tautologous(IMAGE (formsubst i) (cl1 DIFF ps1 UNION cl2' DIFF ps2)))
         ==> sresproof hyps sos
             (IMAGE (formsubst i) (cl1 DIFF ps1 UNION cl2' DIFF ps2)))]]
unsafe def sresproof_RULES : thm := sresproof_triple.1
unsafe def sresproof_INDUCT : thm := sresproof_triple.2.1
unsafe def sresproof_CASES : thm := sresproof_triple.2.2
#eval do IO.println sresproof_RULES; IO.println sresproof_INDUCT; IO.println sresproof_CASES

#eval phrase 30
unsafe def SRESPROOF_CLAUSE : thm := keep "SRESPROOF_CLAUSE" fun _ => (do
  prove ([[!hyps sos.
     (!c. c IN hyps ==> clause c)
     ==> !c. sresproof hyps sos c ==> clause c]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC sresproof_INDUCT THEN
    ASM_MESON_TAC [CLAUSE_UNION, CLAUSE_DIFF, IMAGE_FORMSUBST_CLAUSE])
  : ExceptT String IO thm).run
#eval SRESPROOF_CLAUSE

#eval phrase 31
unsafe def PSATISFIES_IMAGE_LEMMA : thm := keep "PSATISFIES_IMAGE_LEMMA" fun _ => (do
  prove ([[(!c. c IN s ==> clause c)
   ==> !d. d psatisfies {formsubst v p | prop v /\ p IN IMAGE interp s} <=>
           d psatisfies {interp cl | cl IN
                       {IMAGE (formsubst v) c | prop v /\ c IN s}}]])
   (STRIP_TAC THEN REWRITE_TAC [psatisfies, IN_ELIM_THM] THEN
    GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [IN_IMAGE, PHOLDS_INTERP_IMAGE])
  : ExceptT String IO thm).run
#eval PSATISFIES_IMAGE_LEMMA

#eval phrase 32
unsafe def SOS_RESOLUTION_COMPLETE : thm := keep "SOS_RESOLUTION_COMPLETE" fun _ => (do
  prove ([[(!cl. cl IN hyps ==> clause cl) /\ sos SUBSET hyps /\
   ~(?M:(term->bool)#(num->term list->term)#(num->term list->bool).
        interpretation (language(IMAGE interp hyps)) M /\ ~(Dom M = {}) /\
        M satisfies (IMAGE interp hyps)) /\
   (?M:(A->bool)#(num->A list->A)#(num->A list->bool).
        interpretation (language(IMAGE interp hyps)) M /\ ~(Dom M = {}) /\
        M satisfies (IMAGE interp (hyps DIFF sos)))
   ==> sresproof hyps sos {}]])
   (REWRITE_TAC [SUBSET] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPEC ([[IMAGE interp hyps]]) HERBRAND_THEOREM) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [REWRITE_TAC [IN_IMAGE] THEN ASM_MESON_TAC [QFREE_INTERP], ALL_TAC] THEN
    SUBGOAL_THEN
     ([[?d. d psatisfies
            {formsubst v p | v,p |
                 (!x. v x IN herbase (functions (IMAGE interp hyps))) /\
                 p IN IMAGE interp (hyps DIFF sos)}]])
    MP_TAC THENL
     [FIRST_ASSUM (MP_TAC oTIO HolLight.MATCH_MP SATISFIES_INSTANCES) THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC [[IMAGE interp (hyps DIFF sos)]]) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (MP_TAC oTIO HolLight.MATCH_MP (← HolLight.ONCE_REWRITE_RULE
       [(← ExceptT.mk (TAUT [[a /\ b /\ c ==> d <=> b ==> a /\ c ==> d]]))]
       (← HolLight.GEN_ALL SATISFIES_PSATISFIES))) THEN
      FIRST_ASSUM (X_CHOOSE_TAC [[v:num->A]] oTIO HolLight.MATCH_MP VALUATION_EXISTS) THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC [[v:num->A]]) THEN ASM_REWRITE_TAC [] THEN
      ANTS_TAC THENL
       [REWRITE_TAC [IN_ELIM_THM, IN_IMAGE, IN_DIFF] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
        ASM_MESON_TAC [QFREE_FORMSUBST, QFREE_INTERP, clause], ALL_TAC] THEN
      DISCH_THEN (fun th => HolLight.tactic_of do
        let l ← liftExcept (HolCore.Equal.lhand (concl th))
        pure (EXISTS_TAC l THEN MP_TAC th)) THEN
      REWRITE_TAC [psatisfies] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC [[p:form]] THEN
      MATCH_MP_TAC (← ExceptT.mk (TAUT [[(a ==> b) ==> (b ==> c) ==> (a ==> c)]])) THEN
      REWRITE_TAC [IN_ELIM_THM, IN_IMAGE, language] THEN
      MESON_TAC [HERBASE_SUBSET_TERMS], ALL_TAC] THEN
    ASM_SIMP_TAC [PSATISFIES_IMAGE_LEMMA, IMAGE_FORMSUBST_CLAUSE, IN_DIFF] THEN
    REWRITE_TAC [(← HolLight.GSYM IN_DIFF), psatisfies, (← HolLight.GSYM psatisfiable)] THEN
    DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN
     ([[spresproof {IMAGE (formsubst v) cl | v,cl | cl IN hyps}
                 {IMAGE (formsubst v) cl | v,cl | cl IN sos} {}]])
    MP_TAC THENL
     [MATCH_MP_TAC SPRESPROOF_MONO_SOS THEN
      EXISTS_TAC
       [[{IMAGE (formsubst v) c | v,c |
           (!x. v x IN herbase(functions(IMAGE interp hyps))) /\
           c IN hyps}]] THEN
      EXISTS_TAC
       [[{IMAGE (formsubst v) c | v,c |
           (!x. v x IN herbase(functions(IMAGE interp hyps))) /\
           c IN sos}]] THEN
      REPEAT CONJ_TAC THENL
       [ALL_TAC,
        REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN MESON_TAC [],
        REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN MESON_TAC []] THEN
      MATCH_MP_TAC SPRESPROOF_REFUTATION_COMPLETE THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN
        ASM_MESON_TAC [IMAGE_FORMSUBST_CLAUSE],
        ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      FIRST_ASSUM (MATCH_MP_TAC oTIO HolLight.MATCH_MP (← HolLight.ONCE_REWRITE_RULE
       [IMP_CONJ] PSATISFIABLE_MONO)) THEN
      REWRITE_TAC [SUBSET, IN_ELIM_THM, IN_DIFF] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN
      ([[!cl0. spresproof {IMAGE (formsubst v) cl | v,cl | cl IN hyps}
             {IMAGE (formsubst v) cl | v,cl | cl IN sos} cl0
             ==> ?cl. sresproof hyps sos cl /\ cl0 instance_of cl]])
    MP_TAC THENL
     [ALL_TAC,
      DISCH_THEN (MP_TAC o HolLight.SPEC [[ {}:form->bool ]]) THEN
      MATCH_MP_TAC (← ExceptT.mk (TAUT [[(b ==> c) ==> (a ==> b) ==> (a ==> c)]])) THEN
      MESON_TAC [INSTANCE_OF_EMPTY]] THEN
    MATCH_MP_TAC spresproof_INDUCT THEN CONJ_TAC THENL
     [REWRITE_TAC [IN_IMAGE, instance_of, IN_ELIM_THM] THEN
      ASM_MESON_TAC [sresproof_RULES, TAUTOLOGOUS_INSTANCE], ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [ [[A':form->bool]], [[B':form->bool]], [[p:form]] ] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN ([[A:form->bool]]) STRIP_ASSUME_TAC)
                               MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    REWRITE_TAC [IN_ELIM_THM] THEN
    HolLight.GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV) [SWAP_EXISTS_THM] THEN
    REWRITE_TAC [OR_EXISTS_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[B:form->bool]]) MP_TAC) THEN
    REWRITE_TAC [RIGHT_EXISTS_AND_THM] THEN
    REWRITE_TAC [(← HolLight.GSYM instance_of)] THEN
    REWRITE_TAC [(← ExceptT.mk (TAUT [[a /\ c \/ b /\ c <=> (a \/ b) /\ c]]))] THEN
    DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC) THEN
    MP_TAC (← HolLight.SPECL
     [ [[A:form->bool]], [[IMAGE (formsubst (rename B (FVS A))) B]],
      [[A':form->bool]], [[B':form->bool]], [[resolve p A' B']], [[p:form]] ]
     LIFTING_LEMMA) THEN
    ABBREV_TAC [[C = IMAGE (formsubst (rename B (FVS A))) B]] THEN
    MP_TAC (← HolLight.SPECL [ [[B:form->bool]], [[FVS(A)]] ] rename) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC [FVS_CLAUSE_FINITE, SRESPROOF_CLAUSE], ALL_TAC] THEN
    ASM_REWRITE_TAC [«renaming»] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    HolLight.GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.TOP_DEPTH_CONV)
     [FUN_EQ_THM, o_THM, I_DEF, BETA_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[j:num->term]]) (ASSUME_TAC oTIO HolLight.CONJUNCT1)) THEN
    ANTS_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC [SRESPROOF_CLAUSE],
      ASM_MESON_TAC [IMAGE_FORMSUBST_CLAUSE, SRESPROOF_CLAUSE],
      ONCE_REWRITE_TAC [INTER_COMM] THEN ASM_REWRITE_TAC [],
      UNDISCH_TAC [[B' instance_of B]] THEN REWRITE_TAC [instance_of] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[k:num->term]]) SUBST1_TAC) THEN
      Fol.EXPAND_TAC "C" THEN REWRITE_TAC [(← HolLight.GSYM IMAGE_o)] THEN
      EXISTS_TAC [[termsubst k o (j:num->term)]] THEN
      SUBGOAL_THEN
       ([[termsubst k = termsubst (termsubst k o j) o termsubst (rename B (FVS A))]])
      MP_TAC THENL
       [REWRITE_TAC [FUN_EQ_THM] THEN MATCH_MP_TAC term_INDUCT THEN CONJ_TAC THENL
         [ASM_REWRITE_TAC [termsubst, (← HolLight.GSYM TERMSUBST_TERMSUBST), o_THM],
          SIMP_TAC [termsubst, term_INJ, o_THM, (← HolLight.GSYM MAP_o)] THEN
          REPEAT STRIP_TAC THEN MATCH_MP_TAC MAP_EQ THEN ASM_REWRITE_TAC [o_THM]],
        ALL_TAC] THEN
      REWRITE_TAC [(← HolLight.GSYM FORMSUBST_TERMSUBST_LEMMA)] THEN
      REWRITE_TAC [EXTENSION, IN_IMAGE, o_THM] THEN
      ASM_MESON_TAC [SRESPROOF_CLAUSE, clause, QFREE_LITERAL], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[A1:form->bool]]) (X_CHOOSE_THEN ([[B1:form->bool]])
        MP_TAC)) THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[mgu (A1 UNION {~~ l | l IN B1})]]) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [MATCH_MP_TAC ISMGU_MGU THEN ASM_REWRITE_TAC [FINITE_UNION] THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC [SRESPROOF_CLAUSE, clause, FINITE_SUBSET],
        SUBGOAL_THEN ([[{~~l | l IN B1} = IMAGE (~~) B1]]) SUBST1_TAC THENL
         [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN
          MESON_TAC [], ALL_TAC] THEN
        ASM_MESON_TAC [SRESPROOF_CLAUSE, clause, FINITE_SUBSET, FINITE_IMAGE],
        REWRITE_TAC [IN_UNION, IN_ELIM_THM] THEN
        ASM_MESON_TAC [SRESPROOF_CLAUSE, clause, QFREE_LITERAL, SUBSET,
                      IMAGE_FORMSUBST_CLAUSE, QFREE_NEGATE]],
      ALL_TAC] THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
      let r ← liftExcept (HolCore.Kernel.rand (concl th))
      pure (ASSUME_TAC th THEN EXISTS_TAC r)) THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC (← liftExcept (Session.CONJUNCT2 (← ExceptT.mk (HolLight.SPEC_ALL sresproof_RULES)))) THEN
    EXISTS_TAC [[B:form->bool]] THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC oTIO HolLight.MATCH_MP TAUTOLOGOUS_INSTANCE) THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [instance_of]) THEN
    REWRITE_TAC [NOT_IMP, NOT_FORALL_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    DISCH_THEN (SUBST1_TAC oTIO HolLight.SYM) THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval SOS_RESOLUTION_COMPLETE

#eval phrase 33
unsafe def SOS_GIVEN_GENERAL : thm := keep "SOS_GIVEN_GENERAL" fun _ => (do
  prove ([[!used unused cl.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c) /\
        sresproof (set_of_list(used) UNION set_of_list(unused))
                  (set_of_list unused) cl
        ==> clause cl /\
            ?n cl'. cl' subsumes cl /\ cl' IN level(used,unused) n]])
   (GEN_TAC THEN GEN_TAC THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (TAUT [[a /\ b /\ c ==> d <=> a /\ b ==> c ==> d]]))] THEN
    REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC sresproof_INDUCT THEN CONJ_TAC THENL
     [X_GEN_TAC [[c:form->bool]] THEN STRIP_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC [IN_SET_OF_LIST], ALL_TAC] THEN
      EXISTS_TAC [[0]] THEN FIRST_ASSUM (MP_TAC oTIO HolLight.MATCH_MP LEVEL_0) THEN
      REWRITE_TAC [SUBSUMES, IN_UNION] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC
     [ [[c1:form->bool]], [[c2:form->bool]], [[c2':form->bool]],
      [[ps1:form->bool]], [[ps2:form->bool]], [[i:num->term]] ] THEN
    DISCH_THEN (CONJUNCTS_THEN2
       (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC [[n1:num]])) MP_TAC) THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN
     ([[?n2. c2 IN set_of_list(used) \/
           ?cl'. cl' subsumes c2 /\ (cl' IN level (used,unused) n2)]])
    MP_TAC THENL
     [FIRST_X_ASSUM (DISJ_CASES_THEN MP_TAC) THENL
       [REWRITE_TAC [IN_UNION] THEN MESON_TAC [], ALL_TAC] THEN
      REWRITE_TAC [IN_UNION] THEN DISCH_THEN DISJ_CASES_TAC THENL
       [ASM_MESON_TAC [subsumes_REFL], ALL_TAC] THEN
      EXISTS_TAC [[0]] THEN FIRST_ASSUM (MP_TAC oTIO HolLight.MATCH_MP LEVEL_0) THEN
      REWRITE_TAC [SUBSUMES] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_TAC [[n2:num]]) THEN
    SUBGOAL_THEN
     ([[?n cl1 cl2. cl1 subsumes c1 /\ cl2 subsumes c2 /\
                  cl1 IN level(used,unused) n /\
                  ((cl2 = c2) /\ c2 IN set_of_list(used) \/
                   cl2 IN level(used,unused) n)]])
    MP_TAC THENL
     [EXISTS_TAC [[n1 + n2:num]] THEN REWRITE_TAC [IN_UNION] THEN
      ONCE_REWRITE_TAC [(← ExceptT.mk (TAUT [[a /\ b /\ c /\ d <=> (a /\ c) /\ (b /\ d)]]))] THEN
      REWRITE_TAC [RIGHT_EXISTS_AND_THM, LEFT_EXISTS_AND_THM] THEN CONJ_TAC THENL
       [ASM_MESON_TAC [level_MONO_SUBSET, SUBSET, LE_ADD], ALL_TAC] THEN
      UNDISCH_TAC
       [[c2 IN set_of_list used \/
        (?cl'. cl' subsumes c2 /\ cl' IN level (used,unused) n2)]] THEN
      REWRITE_TAC [IN_UNION] THEN STRIP_TAC THEN
      ASM_MESON_TAC [subsumes_REFL, level_MONO_SUBSET, SUBSET,
                    (← ExceptT.mk (ARITH_RULE [[n <= m + n:num]]))],
      ALL_TAC] THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[n:num]], [[cl1:form->bool]], [[cl2:form->bool]] ] THEN
    SUBGOAL_THEN ([[clause c2]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [IN_SET_OF_LIST, IN_UNION], ALL_TAC] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[a /\ (a ==> c ==> b) ==> c ==> a /\ b]])) THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC [IMAGE_FORMSUBST_CLAUSE, CLAUSE_UNION, CLAUSE_DIFF],
      ALL_TAC] THEN
    DISCH_TAC THEN STRIP_TAC THENL
     [MP_TAC (← HolLight.SPECL [ [[c1:form->bool]], [[cl1:form->bool]], [[c2:form->bool]],
                    [[IMAGE (formsubst i) (c1 DIFF ps1 UNION c2' DIFF ps2)]] ]
                   ISARESOLVENT_SUBSUME_L) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
         [ASM_MESON_TAC [level_CLAUSE], ALL_TAC] THEN
        ASM_REWRITE_TAC [isaresolvent] THEN
        CONV_TAC (HolLight.ONCE_DEPTH_CONV Session.let_CONV) THEN
        MAP_EVERY EXISTS_TAC [ [[ps1:form->bool]], [[ps2:form->bool]] ] THEN
        CONV_TAC (HolLight.ONCE_DEPTH_CONV Session.let_CONV) THEN ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      DISCH_THEN (DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[r:form->bool]]) STRIP_ASSUME_TAC) THEN
      EXISTS_TAC [[SUC n]] THEN
      FIRST_ASSUM (MP_TAC o HolLight.SPEC [[n:num]] oTIO HolLight.MATCH_MP LEVEL_STEP) THEN
      REWRITE_TAC [SUBSUMES, allntresolvents, IN_ELIM_THM, allresolvents] THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC [[r:form->bool]]) THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [ALL_TAC,
          ASM_MESON_TAC [TAUTOLOGOUS_INSTANCE, SUBSET_TAUT, subsumes]] THEN
        MAP_EVERY EXISTS_TAC [ [[cl1:form->bool]], [[c2:form->bool]] ] THEN
        ASM_REWRITE_TAC [IN_UNION], ALL_TAC] THEN
      ASM_MESON_TAC [subsumes_TRANS, level_CLAUSE], ALL_TAC] THEN
    MP_TAC (← HolLight.SPECL [ [[c1:form->bool]], [[cl1:form->bool]], [[c2:form->bool]],
                  [[cl2:form->bool]],
                  [[IMAGE (formsubst i) (c1 DIFF ps1 UNION c2' DIFF ps2)]] ]
                 ISARESOLVENT_SUBSUME) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [ASM_MESON_TAC [level_CLAUSE], ALL_TAC] THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC [level_CLAUSE], ALL_TAC] THEN
      ASM_REWRITE_TAC [isaresolvent] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV Session.let_CONV) THEN
      MAP_EVERY EXISTS_TAC [ [[ps1:form->bool]], [[ps2:form->bool]] ] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV Session.let_CONV) THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    DISCH_THEN (DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
     [ASM_MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN (DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
     [ASM_MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[r:form->bool]]) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC [[SUC n]] THEN
    FIRST_ASSUM (MP_TAC o HolLight.SPEC [[n:num]] oTIO HolLight.MATCH_MP LEVEL_STEP) THEN
    REWRITE_TAC [SUBSUMES, allntresolvents, IN_ELIM_THM, allresolvents] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[r:form->bool]]) THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [ALL_TAC,
        ASM_MESON_TAC [TAUTOLOGOUS_INSTANCE, SUBSET_TAUT, subsumes]] THEN
      MAP_EVERY EXISTS_TAC [ [[cl1:form->bool]], [[cl2:form->bool]] ] THEN
      ASM_REWRITE_TAC [IN_UNION], ALL_TAC] THEN
    ASM_MESON_TAC [subsumes_TRANS, level_CLAUSE])
  : ExceptT String IO thm).run
#eval SOS_GIVEN_GENERAL

#eval phrase 34
unsafe def SUBSUMES_EMPTY : thm := keep "SUBSUMES_EMPTY" fun _ => (do
  prove ([[!c. (c subsumes {}) = (c = {})]])
   (REWRITE_TAC [subsumes, IN_IMAGE, NOT_IN_EMPTY, EXTENSION, SUBSET] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval SUBSUMES_EMPTY

#eval phrase 35
unsafe def SOS_GIVEN : thm := keep "SOS_GIVEN" fun _ => (do
  prove ([[!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c) /\
        sresproof (set_of_list(used) UNION set_of_list(unused))
                  (set_of_list unused) {}
        ==> ?n. {} IN level(used,unused) n]])
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC oTIO HolLight.MATCH_MP SOS_GIVEN_GENERAL) THEN
    SIMP_TAC [SUBSUMES_EMPTY, UNWIND_THM2])
  : ExceptT String IO thm).run
#eval SOS_GIVEN

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py from the `#eval`s above. -/
unsafe def ensure : IO Unit := once "HolLogicArith.Support" do
  replay (
          HolLogicArith.Linear.ensure)
  replay (
          NEGATE_LITERAL)
  replay (
          RESOLVE_CLAUSE)
  replay (
          PRESPROOF_CLAUSE)
  replay (
          RESOLVE_MONO)
  replay (
          RESOLVE_SYM)
  replay (
          RESOLVE_TAUT_L)
  replay (
          RESOLVE_TAUT_R)
  replay (
          SUBSET_TAUT)
  replay (
          do IO.println npresproof_RULES; IO.println npresproof_INDUCT; IO.println npresproof_CASES)
  replay (
          NPRESPROOF)
  replay (
          NPRESPROOF_CLAUSE)
  replay (
          do IO.println psresproof_RULES; IO.println psresproof_INDUCT; IO.println psresproof_CASES)
  replay (
          PSRESPROOF_CLAUSE)
  replay (
          SUPPORT_ASYMMETRIC)
  replay (
          SUPPORT_SYMMETRIC)
  replay (
          SUPPORT_LEMMA)
  replay (
          SUPPORT_INDUCT_LEMMA)
  replay (
          SUPPORT_INDUCT)
  replay (
          SUPPORT)
  replay (
          do IO.println spresproof_RULES; IO.println spresproof_INDUCT; IO.println spresproof_CASES)
  replay (
          SPRESPROOF_PSRESPROOF)
  replay (
          SPRESPROOF_CLAUSE_NONTAUT)
  replay (
          SPRESPROOF_CLAUSE)
  replay (
          SPRESPROOF_MONO)
  replay (
          SPRESPROOF_MONO_SOS)
  replay (
          TAUTOLOGOUS_SATISFIED)
  replay (
          PRESPROOF_SOUND)
  replay (
          SPRESPROOF_REFUTATION_COMPLETE)
  replay (
          do IO.println sresproof_RULES; IO.println sresproof_INDUCT; IO.println sresproof_CASES)
  replay (
          SRESPROOF_CLAUSE)
  replay (
          PSATISFIES_IMAGE_LEMMA)
  replay (
          SOS_RESOLUTION_COMPLETE)
  replay (
          SOS_GIVEN_GENERAL)
  replay (
          SUBSUMES_EMPTY)
  replay (
          SOS_GIVEN)
-- @@ENSURE END

end HolLogicArith.Support
