/- File: HolLogicArith/Linear.lean
Translation of HOL Light's Logic/linear.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolLogicArith.Given
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

namespace HolLogicArith.Linear

/- List definitions/theorems used below are exposed by Session as fields of
   the `listDefs`/`listThms1`/`listThms2` bundles; alias the ones we need. -/
private unsafe def LENGTH : thm := Session.listDefs.LENGTH
private unsafe def MEM : thm := Session.listDefs.MEM
private unsafe def ALL : thm := Session.listDefs.ALL
private unsafe def ALL2 : thm := Session.listDefs.ALL2
private unsafe def LAST : thm := Session.listDefs.LAST
private unsafe def NOT_CONS_NIL : thm := Session.listThms1.NOT_CONS_NIL
private unsafe def CONS_11 : thm := Session.listThms1.CONS_11
private unsafe def ALL_MEM : thm := Session.listThms1.ALL_MEM
private unsafe def MAP_o : thm := Session.listThms1.MAP_o
private unsafe def MAP_EQ : thm := Session.listThms1.MAP_EQ
private unsafe def list_INDUCT : thm := Session.list_INDUCT

#eval HolLogicArith.Given.ensure

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- `new_recursive_definition` lifted into `ExceptT String IO`. -/
private unsafe def newRec (ax : thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (Session.new_recursive_definition ax tm)

/- `new_inductive_definition`, panicking with HOL Light's message on failure. -/
private unsafe def newInductive (tm : term) : thm × thm × thm :=
  match unsafeIO (Session.new_inductive_definition tm) with
  | .ok (.ok t) => t
  | .ok (.error e) => panic! s!"new_inductive_definition: {e}"
  | .error e => panic! s!"new_inductive_definition IO: {e}"

#eval phrase 1
unsafe def RESOLVE_CLAUSE : thm := keep "RESOLVE_CLAUSE" fun _ => (do
  prove ([[!c1 c2 p. clause c1 /\ clause c2 ==> clause(resolve p c1 c2)]])
   (REWRITE_TAC [clause, resolve, FINITE_UNION, IN_UNION, IN_DELETE] THEN
    MESON_TAC [DELETE_SUBSET, FINITE_SUBSET])
  : ExceptT String IO thm).run
#eval RESOLVE_CLAUSE

#eval phrase 2
unsafe def PRESPROOF_CLAUSE : thm := keep "PRESPROOF_CLAUSE" fun _ => (do
  prove ([[!hyps cl. (!c. c IN hyps ==> clause c) /\ presproof hyps cl ==> clause cl]])
   (REWRITE_TAC [IMP_CONJ] THEN
    GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC presproof_INDUCT THEN ASM_MESON_TAC [RESOLVE_CLAUSE])
  : ExceptT String IO thm).run
#eval PRESPROOF_CLAUSE

#eval phrase 3
unsafe def RESOLVE_MONO : thm := keep "RESOLVE_MONO" fun _ => (do
  prove ([[!c1 c2 c1' c2' p.
        c1 SUBSET c1' /\ c2 SUBSET c2'
        ==> (resolve p c1 c2) SUBSET (resolve p c1' c2')]])
   (REWRITE_TAC [SUBSET, resolve, IN_UNION, IN_DELETE] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval RESOLVE_MONO

#eval phrase 4
unsafe def ppresproof_triple : thm × thm × thm := keep "ppresproof_triple" fun _ =>
  newInductive
    [[(!c. clause(c) ==> ppresproof {c} c) /\
      (!p asm1 asm2 c1 c2.
              ppresproof asm1 c1 /\ ppresproof asm2 c2 /\
              p IN c1 /\ ~~ p IN c2
                  ==> ppresproof (asm1 UNION asm2) (resolve p c1 c2))]]
unsafe def ppresproof_RULES : thm := ppresproof_triple.1
unsafe def ppresproof_INDUCT : thm := ppresproof_triple.2.1
unsafe def ppresproof_CASES : thm := ppresproof_triple.2.2
#eval do IO.println ppresproof_RULES; IO.println ppresproof_INDUCT; IO.println ppresproof_CASES

#eval phrase 5
unsafe def PPRESPROOF : thm := keep "PPRESPROOF" fun _ => (do
  prove ([[!hyps. (!c. c IN hyps ==> clause c)
          ==> !c. presproof hyps c <=>
                        ?asm. asm SUBSET hyps /\ ppresproof asm c]])
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [SPEC_TAC ([[c:form->bool]], [[c:form->bool]]) THEN
      MATCH_MP_TAC presproof_INDUCT THEN CONJ_TAC THENL
       [X_GEN_TAC [[c:form->bool]] THEN DISCH_TAC THEN
        EXISTS_TAC [[{c:form->bool}]] THEN
        ASM_SIMP_TAC [ppresproof_RULES] THEN
        UNDISCH_TAC [[c:form->bool IN hyps]] THEN SET_TAC [],
        ALL_TAC] THEN
      REWRITE_TAC [SUBSET] THEN MESON_TAC [ppresproof_RULES, IN_UNION],
      DISCH_THEN (X_CHOOSE_THEN ([[asm:(form->bool)->bool]]) MP_TAC) THEN
      ONCE_REWRITE_TAC [IMP_CONJ_ALT] THEN
      MAP_EVERY (fun s => SPEC_TAC (s, s))
       [ [[c:form->bool]], [[asm:(form->bool)->bool]] ] THEN
      MATCH_MP_TAC ppresproof_INDUCT THEN
      REWRITE_TAC [SUBSET, IN_INSERT, IN_UNION, NOT_IN_EMPTY] THEN
      MESON_TAC [presproof_RULES]])
  : ExceptT String IO thm).run
#eval PPRESPROOF

#eval phrase 6
unsafe def PPRESPROOF_CLAUSE : thm := keep "PPRESPROOF_CLAUSE" fun _ => (do
  prove ([[!asm cl. ppresproof asm cl ==> clause cl /\ (!c. c IN asm ==> clause c)]])
   (MATCH_MP_TAC ppresproof_INDUCT THEN SIMP_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
    SIMP_TAC [IN_UNION, RESOLVE_CLAUSE] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval PPRESPROOF_CLAUSE

#eval phrase 7
unsafe def PPRESPROOF_CONSEQUENCE : thm := keep "PPRESPROOF_CONSEQUENCE" fun _ => (do
  prove ([[!asm cl. ppresproof asm cl
            ==> !d. d psatisfies (IMAGE interp asm) ==> pholds d (interp cl)]])
   (SUBGOAL_THEN
     ([[!asm cl. ppresproof asm cl
              ==> !d. (!c. c IN asm ==> ?p. p IN c /\ pholds d p)
                      ==> ?p. p IN cl /\ pholds d p]])
    MP_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      ASM_CASES_TAC [[ppresproof asm cl]] THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [psatisfies] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      SIMP_TAC [IN_IMAGE, LEFT_IMP_EXISTS_THM] THEN
      ASM_MESON_TAC [PHOLDS_INTERP, clause, PPRESPROOF_CLAUSE]] THEN
    MATCH_MP_TAC ppresproof_INDUCT THEN CONJ_TAC THENL
     [REWRITE_TAC [IMAGE, IN_INSERT, NOT_IN_EMPTY, psatisfies, IN_ELIM_THM] THEN
      MESON_TAC [], ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC
     [ [[p:form]], [[asm1:(form->bool)->bool]], [[asm2:(form->bool)->bool]],
      [[c1:form->bool]], [[c2:form->bool]] ] THEN
    REWRITE_TAC [IMAGE_UNION] THEN
    REWRITE_TAC [psatisfies, IN_UNION] THEN
    DISCH_THEN (fun th => GEN_TAC THEN DISCH_TAC THEN MP_TAC th) THEN
    REWRITE_TAC [CONJ_ASSOC, AND_FORALL_THM] THEN
    REWRITE_TAC [(← HolLight.GSYM CONJ_ASSOC)] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (MP_TAC o HolLight.SPEC [[d:form->bool]]) MP_TAC) THEN
    STRIP_TAC THEN ASM_SIMP_TAC [] THEN
    DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_THEN ([[q:form]]) STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN ([[r:form]]) STRIP_ASSUME_TAC)) THEN
    REWRITE_TAC [resolve, IN_UNION, IN_DELETE] THEN
    ASM_MESON_TAC [PHOLDS_NEGATE])
  : ExceptT String IO thm).run
#eval PPRESPROOF_CONSEQUENCE

#eval phrase 8
unsafe def PPRESPROOF_SOUND : thm := keep "PPRESPROOF_SOUND" fun _ => (do
  prove ([[!asm. ppresproof asm {} ==> ~(psatisfiable (IMAGE interp asm))]])
   (GEN_TAC THEN DISCH_THEN (MP_TAC oTIO HolLight.MATCH_MP PPRESPROOF_CONSEQUENCE) THEN
    REWRITE_TAC [psatisfiable] THEN
    SIMP_TAC [PHOLDS_INTERP, FINITE_RULES, NOT_IN_EMPTY] THEN
    REWRITE_TAC [psatisfies] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval PPRESPROOF_SOUND

#eval phrase 9
unsafe def PPRESPROOF_ALLNEGATIVE : thm := keep "PPRESPROOF_ALLNEGATIVE" fun _ => (do
  prove ([[!asm. ppresproof asm {} ==> ?c. c IN asm /\ !p. p IN c ==> negative p]])
   (GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC oTIO HolLight.MATCH_MP PPRESPROOF_SOUND) THEN
    CONV_TAC HolLight.CONTRAPOS_CONV THEN REWRITE_TAC [psatisfiable] THEN
    REWRITE_TAC [NOT_EXISTS_THM] THEN DISCH_TAC THEN
    EXISTS_TAC [[\x:form. T]] THEN
    SIMP_TAC [IN_IMAGE, LEFT_IMP_EXISTS_THM] THEN
    GEN_TAC THEN X_GEN_TAC [[c:form->bool]] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (HolCore.Lib.K ALL_TAC) ASSUME_TAC) THEN
    SUBGOAL_THEN ([[FINITE(c:form->bool)]])
     (fun th => SIMP_TAC [th, PHOLDS_INTERP])
    THENL [ASM_MESON_TAC [PPRESPROOF_CLAUSE, clause], ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[c:form->bool]]) THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [NOT_FORALL_THM, NOT_IMP] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[q:form]] THEN
    SIMP_TAC [] THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[literal q]]) MP_TAC THENL
     [ASM_MESON_TAC [PPRESPROOF_CLAUSE, clause], ALL_TAC] THEN
    REWRITE_TAC [literal, ATOM] THEN
    REPEAT STRIP_TAC THEN UNDISCH_TAC [[~(negative q)]] THEN
    ASM_REWRITE_TAC [pholds] THEN
    REWRITE_TAC [negative, Not_DEF, form_INJ] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval PPRESPROOF_ALLNEGATIVE

#eval phrase 10
unsafe def lpresproof_triple : thm × thm × thm := keep "lpresproof_triple" fun _ =>
  newInductive
    [[(!cl. cl IN hyps ==> lpresproof hyps [cl]) /\
      (!c1 c2 lis p.
          lpresproof hyps (CONS c1 lis) /\
          (c2 IN hyps \/ MEM c2 lis) /\
          p IN c1 /\ ~~p IN c2
          ==> lpresproof hyps (CONS (resolve p c1 c2) (CONS c1 lis)))]]
unsafe def lpresproof_RULES : thm := lpresproof_triple.1
unsafe def lpresproof_INDUCT : thm := lpresproof_triple.2.1
unsafe def lpresproof_CASES : thm := lpresproof_triple.2.2
#eval do IO.println lpresproof_RULES; IO.println lpresproof_INDUCT; IO.println lpresproof_CASES

#eval phrase 11
unsafe def LPRESPROOF_MONO : thm := keep "LPRESPROOF_MONO" fun _ => (do
  prove ([[!hyps hyps' c.
        hyps SUBSET hyps' /\ lpresproof hyps c ==> lpresproof hyps' c]])
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    SPEC_TAC ([[c:(form->bool)list]], [[c:(form->bool)list]]) THEN
    MATCH_MP_TAC lpresproof_INDUCT THEN
    ASM_MESON_TAC [lpresproof_RULES, SUBSET])
  : ExceptT String IO thm).run
#eval LPRESPROOF_MONO

#eval phrase 12
unsafe def RESOLVE_SYM : thm := keep "RESOLVE_SYM" fun _ => (do
  prove ([[!c1 c2 p. literal p ==> (resolve (~~p) c1 c2 = resolve p c2 c1)]])
   (SIMP_TAC [resolve, NEGATE_NEGATE, UNION_ACI])
  : ExceptT String IO thm).run
#eval RESOLVE_SYM

#eval phrase 13
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

#eval phrase 14
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

#eval phrase 15
unsafe def SUBSET_TAUT : thm := keep "SUBSET_TAUT" fun _ => (do
  prove ([[!c1 c2. tautologous c1 /\ c1 SUBSET c2 ==> tautologous c2]])
   (REWRITE_TAC [tautologous, SUBSET] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval SUBSET_TAUT

#eval phrase 16
unsafe def suffix : thm := keep "suffix" fun _ => (do
  newRec Session.list_RECURSION
    [[(suffix lis [] <=> (lis = [])) /\
      (suffix lis (CONS s cs) <=> (lis = CONS s cs) \/ suffix lis cs)]]
  : ExceptT String IO thm).run
#eval suffix

#eval phrase 17
unsafe def SUFFIX_REFL : thm := keep "SUFFIX_REFL" fun _ => (do
  prove ([[!lis. suffix lis lis]])
   (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [suffix])
  : ExceptT String IO thm).run
#eval SUFFIX_REFL

#eval phrase 18
unsafe def SUFFIX_BUTLAST : thm := keep "SUFFIX_BUTLAST" fun _ => (do
  prove ([[!l1 l2. suffix l1 l2 /\ ~(l1 = []) ==> (LAST l1 :A = LAST l2)]])
   (GEN_TAC THEN ASM_CASES_TAC [[l1:(A)list = [] ]] THEN ASM_REWRITE_TAC [] THEN
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [suffix, LAST] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [LAST] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [] THEN ASM_MESON_TAC [suffix])
  : ExceptT String IO thm).run
#eval SUFFIX_BUTLAST

#eval phrase 19
unsafe def SUFFIX_TRANS : thm := keep "SUFFIX_TRANS" fun _ => (do
  prove ([[!l1 l2 l3. suffix l1 l2 /\ suffix l2 l3 ==> suffix l1 l3]])
   (GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [suffix] THEN
    ASM_MESON_TAC [suffix])
  : ExceptT String IO thm).run
#eval SUFFIX_TRANS

#eval phrase 20
unsafe def SUFFIX_MEM : thm := keep "SUFFIX_MEM" fun _ => (do
  prove ([[!x:A l lis. suffix (CONS x l) lis ==> MEM x lis]])
   (GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC [MEM, suffix, NOT_CONS_NIL, CONS_11] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval SUFFIX_MEM

#eval phrase 21
unsafe def SUFFIX_CONS : thm := keep "SUFFIX_CONS" fun _ => (do
  prove ([[!x l1 l2. suffix l1 l2 ==> suffix l1 (CONS x l2)]])
   (MESON_TAC [suffix])
  : ExceptT String IO thm).run
#eval SUFFIX_CONS

#eval phrase 22
unsafe def SUFFIX_LENGTH : thm := keep "SUFFIX_LENGTH" fun _ => (do
  prove ([[!l1 l2. suffix l1 l2 ==> LENGTH l1 <= LENGTH l2]])
   (ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
    ASM_SIMP_TAC [suffix, LENGTH, NOT_CONS_NIL, LE_0] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [LENGTH, LE_SUC, LE_REFL] THEN
    ASM_MESON_TAC [(← ExceptT.mk (ARITH_RULE [[x <= y ==> x <= SUC y]]))])
  : ExceptT String IO thm).run
#eval SUFFIX_LENGTH

#eval phrase 23
unsafe def NOT_SUFFIX_TAIL : thm := keep "NOT_SUFFIX_TAIL" fun _ => (do
  prove ([[!x l. ~(suffix (CONS x l) l)]])
   (MESON_TAC [SUFFIX_LENGTH, LENGTH, (← ExceptT.mk (ARITH_RULE [[~(SUC n <= n)]]))])
  : ExceptT String IO thm).run
#eval NOT_SUFFIX_TAIL

#eval phrase 24
unsafe def SUFFIX_ANTISYM : thm := keep "SUFFIX_ANTISYM" fun _ => (do
  prove ([[!l1 l2. suffix l1 l2 /\ suffix l2 l1 ==> (l1 = l2)]])
   (LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC [suffix, NOT_CONS_NIL, CONS_11] THEN
    ASM_MESON_TAC [NOT_SUFFIX_TAIL, SUFFIX_TRANS, SUFFIX_CONS])
  : ExceptT String IO thm).run
#eval SUFFIX_ANTISYM

#eval phrase 25
unsafe def NEGATE_LITERAL : thm := keep "NEGATE_LITERAL" fun _ => (do
  prove ([[!q. literal q ==> literal(~~q)]])
   (REWRITE_TAC [literal, ATOM] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [] THEN ASM_MESON_TAC [ATOM, NEGATE_ATOM, NEGATE_NEG])
  : ExceptT String IO thm).run
#eval NEGATE_LITERAL

#eval phrase 26
unsafe def SYMMETRY_LEMMA_1 : thm := keep "SYMMETRY_LEMMA_1" fun _ => (do
  prove ([[(!q basm B casm C c.
        literal q
        ==> (P q basm B casm C c = P (~~q) casm C basm B c)) /\
    (!q basm B casm C. literal q
        ==> (Q q basm B casm C = Q (~~q) casm C basm B)) /\
    (!q basm B casm C.
        Q q basm B casm C
        ==> literal q ==> !c. c IN basm ==> P q basm B casm C c)
    ==> !q basm B casm C.
        Q q basm B casm C
        ==> literal q ==> !c. c IN basm UNION casm ==> P q basm B casm C c]])
   (REWRITE_TAC [IN_UNION] THEN MESON_TAC [NEGATE_LITERAL, NEGATE_NEGATE])
  : ExceptT String IO thm).run
#eval SYMMETRY_LEMMA_1

#eval phrase 27
unsafe def SYMMETRY_LEMMA_2 : thm := keep "SYMMETRY_LEMMA_2" fun _ => (do
  prove ([[(!p q basm B casm C main aasm A.
        literal q
        ==> (P p q basm B casm C main aasm A =
             P p (~~q) casm C basm B main aasm A)) /\
    (!p q basm B casm C main aasm A.
        ~~p IN B ==> literal q ==> P p q basm B casm C main aasm A)
    ==> !p q basm B casm C main aasm A.
            ~~p IN B \/ ~~p IN C ==> literal q
            ==> P p q basm B casm C main aasm A]])
   (REWRITE_TAC [IN_UNION] THEN MESON_TAC [NEGATE_LITERAL, NEGATE_NEGATE])
  : ExceptT String IO thm).run
#eval SYMMETRY_LEMMA_2

#eval phrase 28
unsafe def LINEARIZATION : thm := keep "LINEARIZATION" fun _ => (do
  prove ([[!asm cl. ppresproof asm cl
            ==> !c. c IN asm
                    ==> ?cl' lis. lpresproof asm (CONS cl' lis) /\
                                  cl' SUBSET cl /\
                                  (LAST (CONS cl' lis) = c)]])
   (SUBGOAL_THEN
     ([[!asm cl. ppresproof asm cl
               ==> (!c. c IN asm ==> clause c) /\ clause cl /\
                   (!c. c IN asm
                        ==> ?cl' lis. lpresproof asm (CONS cl' lis) /\
                                      cl' SUBSET cl /\
                                      (LAST (CONS cl' lis) = c)) /\
                   (!c lis p asm'.
                          clause c /\
                          lpresproof asm' (CONS c lis) /\ p IN c /\ ~~p IN cl
                          ==> ?c' lis'. suffix (CONS c lis) (CONS c' lis') /\
                                        lpresproof (asm UNION asm')
                                                   (CONS c' lis') /\
                                        c' SUBSET (resolve p c cl))]])
     (fun th => SIMP_TAC [th]) THEN
    MATCH_MP_TAC ppresproof_INDUCT THEN CONJ_TAC THENL
     [X_GEN_TAC [[cl:form->bool]] THEN DISCH_TAC THEN
      ASM_SIMP_TAC [IN_INSERT, NOT_IN_EMPTY] THEN CONJ_TAC THENL
       [GEN_TAC THEN DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN
        MAP_EVERY EXISTS_TAC [ [[cl:form->bool]], [[ []:(form->bool)list ]] ] THEN
        REWRITE_TAC [LAST, SUBSET_REFL] THEN
        SIMP_TAC [lpresproof_RULES, IN_INSERT, NOT_IN_EMPTY], ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC
       [ [[c:form->bool]], [[lis:(form->bool)list]], [[p:form]],
        [[hyp:(form->bool)->bool]] ] THEN
      STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [ [[resolve p c cl]], [[CONS (c:form->bool) lis]] ] THEN
      REWRITE_TAC [SUBSET_REFL, suffix, SUFFIX_REFL] THEN
      MATCH_MP_TAC (← liftExcept (Session.CONJUNCT2 (← ExceptT.mk (HolLight.SPEC_ALL lpresproof_RULES)))) THEN
      ASM_REWRITE_TAC [IN_UNION, IN_INSERT] THEN
      ASM_MESON_TAC [IN_UNION, SUBSET, LPRESPROOF_MONO], ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC
     [ [[q:form]], [[basm:(form->bool)->bool]], [[casm:(form->bool)->bool]],
      [[B:form->bool]], [[C:form->bool]] ] THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    ASM_SIMP_TAC [RESOLVE_CLAUSE] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC [IN_UNION],
      ASM_SIMP_TAC [RESOLVE_CLAUSE] THEN
      SUBGOAL_THEN ([[literal q]]) MP_TAC THENL [ASM_MESON_TAC [clause], ALL_TAC] THEN
      POP_ASSUM_LIST (fun ths => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.end_itlist HolLight.CONJ ths))) THEN
      MAP_EVERY (fun s => SPEC_TAC (s, s))
       [ [[C:form->bool]], [[casm:(form->bool)->bool]],
        [[B:form->bool]], [[basm:(form->bool)->bool]], [[q:form]] ] THEN
      MATCH_MP_TAC SYMMETRY_LEMMA_1 THEN REPEAT CONJ_TAC THENL
       [SIMP_TAC [resolve, NEGATE_NEGATE, UNION_ACI],
        SIMP_TAC [CONJ_ACI, NEGATE_NEGATE],
        ALL_TAC] THEN
      REPEAT GEN_TAC THEN DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
      DISCH_TAC THEN X_GEN_TAC [[c:form->bool]] THEN DISCH_TAC THEN
      UNDISCH_TAC
       [[!c. c IN basm
             ==> (?cl' lis.
                      lpresproof basm (CONS cl' lis) /\
                      cl' SUBSET B /\
                      (LAST (CONS cl' lis) = c))]] THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC [[c:form->bool]]) THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [ [[B1:form->bool]], [[main:(form->bool)list]] ] THEN
      STRIP_TAC THEN ASM_CASES_TAC [[q:form IN B1]] THENL
       [UNDISCH_TAC
         [[!c lis p asm'.
             clause c /\ lpresproof asm' (CONS c lis) /\ p IN c /\ ~~ p IN C
             ==> (?c' lis'.
                      suffix (CONS c lis) (CONS c' lis') /\
                      lpresproof (casm UNION asm') (CONS c' lis') /\
                      c' SUBSET resolve p c C)]] THEN
        DISCH_THEN (MP_TAC o HolLight.SPECL
         [ [[B1:form->bool]], [[main:(form->bool)list]], [[q:form]],
          [[basm:(form->bool)->bool]] ]) THEN ASM_REWRITE_TAC [] THEN
        ANTS_TAC THENL [ASM_MESON_TAC [CLAUSE_SUBSET], ALL_TAC] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[D:form->bool]] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[final:(form->bool)list]] THEN
        STRIP_TAC THEN REPEAT CONJ_TAC THENL
         [ONCE_REWRITE_TAC [UNION_COMM] THEN ASM_REWRITE_TAC [],
          ASM_MESON_TAC [RESOLVE_MONO, SUBSET_TRANS, SUBSET_REFL],
          ASM_MESON_TAC [SUFFIX_BUTLAST, NOT_CONS_NIL]],
        ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [ [[B1:form->bool]], [[main:(form->bool)list]] ] THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [ASM_MESON_TAC [LPRESPROOF_MONO, IN_UNION, SUBSET], ALL_TAC] THEN
      UNDISCH_TAC [[B1:(form->bool) SUBSET B]] THEN
      UNDISCH_TAC [[~(q:form IN B1)]] THEN
      REWRITE_TAC [resolve, SUBSET, IN_UNION, IN_DELETE] THEN MESON_TAC [],
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [ [[A:form->bool]], [[main:(form->bool)list]],
                         [[p:form]], [[aasm:(form->bool)->bool]] ] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN ([[~~p IN B \/ ~~p IN C]])
     (fun th1 =>
        SUBGOAL_THEN ([[literal q]])
          (fun th2 => POP_ASSUM_LIST (fun ths => HolLight.tactic_of do
                        pure (MP_TAC (← HolLight.end_itlist HolLight.CONJ ths))) THEN
                      MP_TAC th2 THEN MP_TAC th1)
        THENL [ASM_MESON_TAC [clause], ALL_TAC])
    THENL
     [UNDISCH_TAC [[~~p IN resolve q B C]] THEN
      REWRITE_TAC [resolve, IN_UNION, IN_DELETE] THEN MESON_TAC [], ALL_TAC] THEN
    MAP_EVERY (fun s => SPEC_TAC (s, s))
      [ [[A:form->bool]], [[aasm:(form->bool)->bool]], [[main:(form->bool)list]],
       [[C:form->bool]], [[casm:(form->bool)->bool]],
       [[B:form->bool]], [[basm:(form->bool)->bool]], [[q:form]], [[p:form]] ] THEN
    MATCH_MP_TAC SYMMETRY_LEMMA_2 THEN CONJ_TAC THENL
     [SIMP_TAC [resolve, NEGATE_NEGATE] THEN
      REWRITE_TAC [UNION_ACI] THEN REWRITE_TAC [CONJ_ACI], ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC
     [ [[p:form]], [[q:form]], [[basm:(form->bool)->bool]], [[B:form->bool]],
      [[casm:(form->bool)->bool]], [[C:form->bool]], [[main:(form->bool)list]],
      [[aasm:(form->bool)->bool]], [[A:form->bool]] ] THEN
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC [[p:form = q]] THENL
     [UNDISCH_THEN ([[p:form = q]]) SUBST_ALL_TAC THEN
      UNDISCH_TAC
       [[!c lis p asm'.
             clause c /\ lpresproof asm' (CONS c lis) /\ p IN c /\ ~~ p IN C
             ==> (?c' lis'.
                      suffix (CONS c lis) (CONS c' lis') /\
                      lpresproof (casm UNION asm') (CONS c' lis') /\
                      c' SUBSET resolve p c C)]] THEN
      DISCH_THEN (MP_TAC o HolLight.SPECL
       [ [[A:form->bool]], [[main:(form->bool)list]], [[q:form]],
        [[aasm:(form->bool)->bool]] ]) THEN
      ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[D:form->bool]] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[final:(form->bool)list]] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THENL
       [MATCH_MP_TAC LPRESPROOF_MONO THEN
        EXISTS_TAC [[casm:(form->bool)->bool UNION aasm]] THEN
        ASM_REWRITE_TAC [] THEN REWRITE_TAC [SUBSET, IN_UNION] THEN
        GEN_TAC THEN CONV_TAC TAUT,
        SUBGOAL_THEN ([[C SUBSET (resolve q B C)]]) (fun th =>
          ASM_MESON_TAC [SUBSET_TRANS, RESOLVE_MONO, SUBSET_REFL, th]) THEN
        UNDISCH_TAC [[~~q IN B]] THEN
        REWRITE_TAC [SUBSET, resolve, IN_UNION, IN_DELETE] THEN
        MESON_TAC [NEGATE_REFL]], ALL_TAC] THEN
    ASM_CASES_TAC [[p = ~~q]] THENL
     [UNDISCH_THEN ([[p = ~~q]]) SUBST_ALL_TAC THEN
      UNDISCH_TAC
        [[!c lis p asm'.
             clause c /\ lpresproof asm' (CONS c lis) /\ p IN c /\ ~~ p IN B
             ==> (?c' lis'.
                      suffix (CONS c lis) (CONS c' lis') /\
                      lpresproof (basm UNION asm') (CONS c' lis') /\
                      c' SUBSET resolve p c B)]] THEN
      DISCH_THEN (MP_TAC o HolLight.SPECL
       [ [[A:form->bool]], [[main:(form->bool)list]], [[~~q]],
        [[aasm:(form->bool)->bool]] ]) THEN
      SUBST_ALL_TAC (← HolLight.MATCH_MP NEGATE_NEGATE (ASSUME [[literal q]])) THEN
      ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[D:form->bool]] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[final:(form->bool)list]] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THENL
       [MATCH_MP_TAC LPRESPROOF_MONO THEN
        EXISTS_TAC [[basm:(form->bool)->bool UNION aasm]] THEN
        ASM_REWRITE_TAC [] THEN REWRITE_TAC [SUBSET, IN_UNION] THEN
        GEN_TAC THEN CONV_TAC TAUT,
        SUBGOAL_THEN ([[B SUBSET (resolve q B C)]]) (fun th =>
          ASM_MESON_TAC [SUBSET_TRANS, RESOLVE_MONO, SUBSET_REFL, th]) THEN
        SUBGOAL_THEN ([[q:form IN C]]) MP_TAC THENL
         [ALL_TAC,
          REWRITE_TAC [SUBSET, resolve, IN_UNION, IN_DELETE] THEN
          MESON_TAC [NEGATE_REFL]] THEN
        UNDISCH_TAC [[q IN resolve q B C]] THEN
        REWRITE_TAC [resolve, IN_UNION, IN_DELETE] THEN MESON_TAC []],
      ALL_TAC] THEN
    UNDISCH_TAC
     [[!c lis p asm'.
             clause c /\ lpresproof asm' (CONS c lis) /\ p IN c /\ ~~ p IN B
             ==> (?c' lis'.
                      suffix (CONS c lis) (CONS c' lis') /\
                      lpresproof (basm UNION asm') (CONS c' lis') /\
                      c' SUBSET resolve p c B)]] THEN
    DISCH_THEN (MP_TAC o HolLight.SPECL
     [ [[A:form->bool]], [[main:(form->bool)list]], [[p:form]],
      [[aasm:(form->bool)->bool]] ]) THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[D:form->bool]], [[middle:(form->bool)list]] ] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     ([[?c' lis'.
         suffix (CONS D middle) (CONS c' lis') /\
         suffix (CONS A main) (CONS c' lis') /\
         lpresproof ((basm UNION casm) UNION aasm) (CONS c' lis') /\
         c' SUBSET resolve q (resolve p A B) C]])
    MP_TAC THENL
     [ASM_CASES_TAC [[q:form IN D]] THENL
       [UNDISCH_TAC
         [[!c lis p asm'.
                 clause c /\ lpresproof asm' (CONS c lis) /\ p IN c /\ ~~ p IN C
                 ==> (?c' lis'.
                          suffix (CONS c lis) (CONS c' lis') /\
                          lpresproof (casm UNION asm') (CONS c' lis') /\
                          c' SUBSET resolve p c C)]] THEN
        DISCH_THEN (MP_TAC o HolLight.SPECL
         [ [[D:form->bool]], [[middle:(form->bool)list]],
          [[q:form]], [[basm:(form->bool)->bool UNION aasm]] ]) THEN
        ASM_REWRITE_TAC [] THEN
        ANTS_TAC THENL
         [ASM_MESON_TAC [RESOLVE_CLAUSE, CLAUSE_SUBSET], ALL_TAC] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[E:form->bool]] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[final:(form->bool)list]] THEN
        SIMP_TAC [UNION_ACI] THEN REPEAT STRIP_TAC THENL
         [ASM_MESON_TAC [SUFFIX_TRANS], ALL_TAC] THEN
        ASM_MESON_TAC [RESOLVE_MONO, SUBSET_REFL, SUBSET_TRANS], ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [ [[D:form->bool]], [[middle:(form->bool)list]] ] THEN
      ASM_REWRITE_TAC [SUFFIX_REFL] THEN CONJ_TAC THENL
       [ASM_MESON_TAC [LPRESPROOF_MONO, SUBSET, IN_UNION], ALL_TAC] THEN
      UNDISCH_TAC [[D SUBSET resolve p A B]] THEN
      UNDISCH_TAC [[~(q:form IN D)]] THEN
      REWRITE_TAC [resolve, SUBSET, IN_UNION, IN_DELETE] THEN
      MESON_TAC [], ALL_TAC] THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[E:form->bool]], [[final:(form->bool)list]] ] THEN
    STRIP_TAC THEN ASM_CASES_TAC [[~~p IN E]] THENL
     [ALL_TAC,
      MAP_EVERY EXISTS_TAC [ [[E:form->bool]], [[final:(form->bool)list]] ] THEN
      ASM_REWRITE_TAC [] THEN
      MAP_EVERY UNDISCH_TAC
       [ [[E SUBSET resolve q (resolve p A B) C]],
        [[~(~~ p IN E)]], [[~(p = ~~ q)]], [[~(p:form = q)]],
        [[q:form IN B]], [[~~q IN C]], [[~~p IN resolve q B C]],
        [[~~p IN B]] ] THEN
      REWRITE_TAC [resolve, IN_UNION, IN_DELETE, SUBSET] THEN
      MESON_TAC []] THEN
    ASM_CASES_TAC [[CONS (A:form->bool) main = CONS E final]] THENL
     [ALL_TAC,
      EXISTS_TAC [[resolve (~~p) E A]] THEN
      EXISTS_TAC [[CONS (E:form->bool) final]] THEN REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC [suffix],
        MATCH_MP_TAC (← liftExcept (Session.CONJUNCT2 (← ExceptT.mk (HolLight.SPEC_ALL lpresproof_RULES)))) THEN
        ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
         [DISJ2_TAC THEN
          UNDISCH_TAC [[suffix (CONS (A:form->bool) main) (CONS E final)]] THEN
          ASM_REWRITE_TAC [suffix] THEN MESON_TAC [SUFFIX_MEM],
          SUBGOAL_THEN ([[~~(~~p) = p]]) (fun th => ASM_REWRITE_TAC [th]) THEN
          MATCH_MP_TAC NEGATE_NEGATE THEN ASM_MESON_TAC [clause]],
        SUBGOAL_THEN ([[(~~(~~p) = p) /\ (~~(~~q) = q)]]) MP_TAC THENL
         [ASM_MESON_TAC [NEGATE_NEGATE, clause], ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC
         [ [[~~ p IN E]],
          [[E SUBSET resolve q (resolve p A B) C]],
          [[~(p = ~~ q)]], [[~(p:form = q)]], [[q:form IN B]],
          [[~~q IN C]], [[p:form IN A]], [[~~p IN resolve q B C]],
          [[~~p IN B]] ] THEN
        REWRITE_TAC [resolve, IN_UNION, IN_DELETE, SUBSET] THEN
        MESON_TAC []]] THEN
    UNDISCH_TAC [[CONS (A:form->bool) main = CONS E final]] THEN
    REWRITE_TAC [CONS_11] THEN
    DISCH_THEN (CONJUNCTS_THEN (SUBST_ALL_TAC oTIO HolLight.SYM)) THEN
    SUBGOAL_THEN ([[CONS (D:form->bool) middle = CONS A main]]) MP_TAC THENL
     [ASM_MESON_TAC [SUFFIX_ANTISYM], ALL_TAC] THEN
    REWRITE_TAC [CONS_11] THEN DISCH_THEN (CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    MAP_EVERY EXISTS_TAC [ [[A:form->bool]], [[main:(form->bool)list]] ] THEN
    ASM_REWRITE_TAC [] THEN
    UNDISCH_TAC [[A SUBSET resolve p A B]] THEN
    UNDISCH_TAC [[A SUBSET resolve q (resolve p A B) C]] THEN
    REWRITE_TAC [SUBSET, resolve, IN_UNION, IN_DELETE] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval LINEARIZATION

#eval phrase 29
unsafe def lresproof_triple : thm × thm × thm := keep "lresproof_triple" fun _ =>
  newInductive
    [[(!cl. cl IN hyps ==> lresproof hyps [cl]) /\
      (!c1 c2 lis cl.
          lresproof hyps (CONS c1 lis) /\ (c2 IN hyps \/ MEM c2 lis) /\
          isaresolvent cl (c1,c2)
          ==> lresproof hyps (CONS cl (CONS c1 lis)))]]
unsafe def lresproof_RULES : thm := lresproof_triple.1
unsafe def lresproof_INDUCT : thm := lresproof_triple.2.1
unsafe def lresproof_CASES : thm := lresproof_triple.2.2
#eval do IO.println lresproof_RULES; IO.println lresproof_INDUCT; IO.println lresproof_CASES

#eval phrase 30
unsafe def ALL2_BUTLAST : thm := keep "ALL2_BUTLAST" fun _ => (do
  prove ([[!P:(A->A->bool) l1 l2.
       ~(l1 = []) /\ ALL2 P l1 l2 ==> P (LAST l1) (LAST l2)]])
   (GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [NOT_CONS_NIL] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [ALL2] THEN
    REWRITE_TAC [LAST] THEN
    ASM_CASES_TAC [[t:A list = [] ]] THEN ASM_REWRITE_TAC [] THENL
     [SPEC_TAC ([[t':A list]], [[t':A list]]) THEN
      LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [ALL2, NOT_CONS_NIL],
      ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [] THEN
    UNDISCH_TAC [[~(t:A list = [])]] THEN
    SPEC_TAC ([[t:A list]], [[t:A list]]) THEN
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [ALL2, NOT_CONS_NIL])
  : ExceptT String IO thm).run
#eval ALL2_BUTLAST

#eval phrase 31
unsafe def ALL2_MEM : thm := keep "ALL2_MEM" fun _ => (do
  prove ([[!l1 l2. ALL2 P l1 l2 /\ MEM x l1 ==> ?y. MEM y l2 /\ P x y]])
   (LIST_INDUCT_TAC THEN REWRITE_TAC [MEM] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [ALL2, MEM] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval ALL2_MEM

#eval phrase 32
unsafe def LRESPROOF_CLAUSE : thm := keep "LRESPROOF_CLAUSE" fun _ => (do
  prove ([[!hyps. (!c. c IN hyps ==> clause c)
          ==> !lis. lresproof hyps lis ==> ALL clause lis]])
   (GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC lresproof_INDUCT THEN
    REWRITE_TAC [ALL] THEN ASM_MESON_TAC [ISARESOLVENT_CLAUSE, ALL_MEM])
  : ExceptT String IO thm).run
#eval LRESPROOF_CLAUSE

#eval phrase 33
unsafe def LINEAR_RESOLUTION_COMPLETE : thm := keep "LINEAR_RESOLUTION_COMPLETE" fun _ => (do
  prove ([[(!cl. cl IN hyps ==> clause cl) /\
   ~(?M:(term->bool)#(num->term list->term)#(num->term list->bool).
        interpretation (language(IMAGE interp hyps)) M /\ ~(Dom M = {}) /\
        M satisfies (IMAGE interp hyps))
   ==> ?lis. lresproof hyps (CONS {} lis) /\
             (!p. p IN (LAST (CONS {} lis)) ==> negative p)]])
   (REPEAT STRIP_TAC THEN MP_TAC (← HolLight.SPEC ([[IMAGE interp hyps]]) HERBRAND_THEOREM) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [REWRITE_TAC [IN_IMAGE] THEN ASM_MESON_TAC [QFREE_INTERP], ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     ([[~(psatisfiable
          {interp cl |
           cl IN {IMAGE(formsubst v) cl | cl,v | cl IN hyps}})]])
    MP_TAC THENL
     [REWRITE_TAC [psatisfiable] THEN
      FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        let t ← ExceptT.mk (TAUT [[(b ==> a) ==> ~a ==> ~b]])
        pure (MP_TAC th THEN MATCH_MP_TAC t)) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[d:form->bool]] THEN
      REWRITE_TAC [psatisfies] THEN
      SIMP_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM, LEFT_AND_EXISTS_THM,
               RIGHT_AND_EXISTS_THM, IN_IMAGE] THEN
      ASM_SIMP_TAC [PHOLDS_INTERP_IMAGE] THEN MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN (MP_TAC oTIO HolLight.MATCH_MP
     (← HolLight.REWRITE_RULE [IMP_CONJ_ALT]
                  PRESPROOF_REFUTATION_COMPLETE)) THEN
    ANTS_TAC THENL
     [SIMP_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
      ASM_SIMP_TAC [IMAGE_FORMSUBST_CLAUSE], ALL_TAC] THEN
    MP_TAC (← HolLight.SPEC ([[{IMAGE (formsubst v) cl | cl,v | cl IN hyps}]]) PPRESPROOF) THEN
    ANTS_TAC THENL
     [REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN
      ASM_MESON_TAC [IMAGE_FORMSUBST_CLAUSE], ALL_TAC] THEN
    DISCH_THEN (fun th => ONCE_REWRITE_TAC [th]) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[asm:(form->bool)->bool]]) STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM (MP_TAC oTIO HolLight.MATCH_MP PPRESPROOF_ALLNEGATIVE) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[sos:form->bool]]) STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM (MP_TAC oTIO HolLight.MATCH_MP LINEARIZATION) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[sos:form->bool]]) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[emptyclause:form->bool]]) MP_TAC) THEN
    REWRITE_TAC [SUBSET_EMPTY] THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (TAUT [[a /\ b /\ c <=> b /\ a /\ c]]))] THEN
    REWRITE_TAC [RIGHT_EXISTS_AND_THM] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[qlist:(form->bool)list]]) STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     ([[!plis. lpresproof asm plis
             ==> ?lis. lresproof hyps lis /\ ALL2 (instance_of) plis lis]])
    MP_TAC THENL
     [ALL_TAC,
      DISCH_THEN (MP_TAC o HolLight.SPEC [[CONS {} (qlist:(form->bool)list)]]) THEN
      ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [ALL2] THEN
      MAP_EVERY X_GEN_TAC [ [[emp:form->bool]], [[lis:(form->bool)list]] ] THEN
      DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN STRIP_TAC THEN
      SUBGOAL_THEN ([[emp:form->bool = {}]]) SUBST_ALL_TAC THENL
       [UNDISCH_TAC [[{} instance_of emp]] THEN
        REWRITE_TAC [instance_of, EXTENSION, IN_IMAGE, NOT_IN_EMPTY] THEN
        MESON_TAC [], ALL_TAC] THEN
      EXISTS_TAC [[lis:(form->bool)list]] THEN
      ASM_REWRITE_TAC [] THEN
      X_GEN_TAC [[p:form]] THEN
      SUBGOAL_THEN ([[sos instance_of (LAST (CONS {} lis))]]) MP_TAC THENL
       [Fol.EXPAND_TAC "sos" THEN MATCH_MP_TAC ALL2_BUTLAST THEN
        ASM_REWRITE_TAC [ALL2, NOT_CONS_NIL], ALL_TAC] THEN
      REWRITE_TAC [instance_of] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[jj:num->term]]) SUBST_ALL_TAC) THEN
      DISCH_TAC THEN FIRST_ASSUM (MP_TAC o HolLight.SPEC [[formsubst jj p]]) THEN
      REWRITE_TAC [NEGATIVE_FORMSUBST] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC [IN_IMAGE] THEN ASM_MESON_TAC []] THEN
    SUBGOAL_THEN
     ([[!plis. lpresproof asm plis
             ==> (!c. MEM c plis ==> clause c) /\
                 ?lis. lresproof hyps lis /\ ALL2 (instance_of) plis lis]])
     (fun th => MESON_TAC [th]) THEN
    MATCH_MP_TAC lpresproof_INDUCT THEN CONJ_TAC THENL
     [X_GEN_TAC [[cl:form->bool]] THEN DISCH_TAC THEN CONJ_TAC THENL
       [SUBGOAL_THEN ([[clause cl]]) (fun th => ASM_MESON_TAC [MEM, th]) THEN
        UNDISCH_TAC [[asm SUBSET {IMAGE (formsubst v) cl | cl,v | cl IN hyps}]] THEN
        REWRITE_TAC [SUBSET] THEN DISCH_THEN (MP_TAC o HolLight.SPEC [[cl:form->bool]]) THEN
        ASM_REWRITE_TAC [IN_ELIM_THM, IN_IMAGE] THEN
        ASM_MESON_TAC [IMAGE_FORMSUBST_CLAUSE], ALL_TAC] THEN
      UNDISCH_TAC [[asm SUBSET {IMAGE (formsubst v) cl | cl,v | cl IN hyps}]] THEN
      REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC [[cl:form->bool]]) THEN
      ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [ [[cl0:form->bool]], [[jj:num->term]] ] THEN
      STRIP_TAC THEN EXISTS_TAC [[ [cl0:form->bool] ]] THEN
      ASM_SIMP_TAC [lresproof_RULES, ALL2] THEN
      REWRITE_TAC [instance_of] THEN MESON_TAC [], ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC
     [ [[A':form->bool]], [[B':form->bool]], [[lis':(form->bool)list]], [[p:form]] ] THEN
    DISCH_THEN (CONJUNCTS_THEN2
     (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN ([[alist:(form->bool)list]]) STRIP_ASSUME_TAC))
     (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    SUBGOAL_THEN ([[clause A']]) ASSUME_TAC THENL
     [ASM_MESON_TAC [MEM], ALL_TAC] THEN
    SUBGOAL_THEN ([[clause B']]) ASSUME_TAC THENL
     [FIRST_X_ASSUM DISJ_CASES_TAC THENL
       [ALL_TAC, ASM_MESON_TAC [MEM]] THEN
      UNDISCH_TAC [[asm SUBSET {IMAGE (formsubst v) cl | cl,v | cl IN hyps}]] THEN
      REWRITE_TAC [SUBSET] THEN DISCH_THEN (MP_TAC o HolLight.SPEC [[B':form->bool]]) THEN
      ASM_REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN
      ASM_MESON_TAC [IMAGE_FORMSUBST_CLAUSE], ALL_TAC] THEN
    CONJ_TAC THENL
     [GEN_TAC THEN ONCE_REWRITE_TAC [MEM] THEN ASM_MESON_TAC [RESOLVE_CLAUSE],
      ALL_TAC] THEN
    UNDISCH_TAC [[lresproof hyps alist]] THEN
    UNDISCH_TAC [[ALL2 (instance_of) (CONS A' lis') alist]] THEN
    SPEC_TAC ([[alist:(form->bool)list]], [[alist:(form->bool)list]]) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [ALL2] THEN
    MAP_EVERY X_GEN_TAC [ [[A:form->bool]], [[lis:(form->bool)list]] ] THEN
    DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN STRIP_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[clause A /\ !c. MEM c lis ==> clause c]]) STRIP_ASSUME_TAC THENL
     [REWRITE_TAC [ALL_MEM, (← HolLight.GSYM (← liftExcept (Session.CONJUNCT2 ALL)))] THEN
      ASM_MESON_TAC [LRESPROOF_CLAUSE], ALL_TAC] THEN
    SUBGOAL_THEN ([[?B. B' instance_of B /\ (B IN hyps \/ MEM B lis)]]) MP_TAC THENL
     [FIRST_X_ASSUM DISJ_CASES_TAC THENL
       [UNDISCH_TAC [[asm SUBSET {IMAGE (formsubst v) cl | cl,v | cl IN hyps}]] THEN
        REWRITE_TAC [SUBSET] THEN DISCH_THEN (MP_TAC o HolLight.SPEC [[B':form->bool]]) THEN
        ASM_REWRITE_TAC [IN_ELIM_THM, IN_IMAGE] THEN
        REWRITE_TAC [instance_of] THEN MESON_TAC [], ALL_TAC] THEN
      ASM_MESON_TAC [ALL2_MEM], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[B:form->bool]]) (CONJUNCTS_THEN ASSUME_TAC)) THEN
    SUBGOAL_THEN ([[clause B]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [], ALL_TAC] THEN
    MP_TAC (← HolLight.SPECL
     [ [[A:form->bool]], [[IMAGE (formsubst (rename B (FVS A))) B]],
      [[A':form->bool]], [[B':form->bool]], [[resolve p A' B']], [[p:form]] ]
     LIFTING_LEMMA) THEN
    ABBREV_TAC [[C = IMAGE (formsubst (rename B (FVS A))) B]] THEN
    MP_TAC (← HolLight.SPECL [ [[B:form->bool]], [[FVS(A)]] ] rename) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC [FVS_CLAUSE_FINITE, RESPROOF_CLAUSE], ALL_TAC] THEN
    ASM_REWRITE_TAC [«renaming»] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    HolLight.GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.TOP_DEPTH_CONV)
     [FUN_EQ_THM, o_THM, I_DEF, BETA_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[j:num->term]]) (ASSUME_TAC oTIO HolLight.CONJUNCT1)) THEN
    ANTS_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC [IMAGE_FORMSUBST_CLAUSE, RESPROOF_CLAUSE],
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
      ASM_MESON_TAC [RESPROOF_CLAUSE, clause, QFREE_LITERAL], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[A1:form->bool]]) (X_CHOOSE_THEN ([[B1:form->bool]])
        MP_TAC)) THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[mgu (A1 UNION {~~ l | l IN B1})]]) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [MATCH_MP_TAC ISMGU_MGU THEN ASM_REWRITE_TAC [FINITE_UNION] THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC [RESPROOF_CLAUSE, clause, FINITE_SUBSET],
        SUBGOAL_THEN ([[{~~l | l IN B1} = IMAGE (~~) B1]]) SUBST1_TAC THENL
         [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN
          MESON_TAC [], ALL_TAC] THEN
        ASM_MESON_TAC [RESPROOF_CLAUSE, clause, FINITE_SUBSET, FINITE_IMAGE],
        REWRITE_TAC [IN_UNION, IN_ELIM_THM] THEN
        ASM_MESON_TAC [RESPROOF_CLAUSE, clause, QFREE_LITERAL, SUBSET,
                      IMAGE_FORMSUBST_CLAUSE, QFREE_NEGATE]],
      ALL_TAC] THEN
    DISCH_TAC THEN
    EXISTS_TAC [[CONS (IMAGE (formsubst (mgu (A1 UNION {~~ l | l IN B1})))
                            (A DIFF A1 UNION C DIFF B1))
                     (CONS A lis)]] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC (← liftExcept (Session.CONJUNCT2 (← ExceptT.mk (HolLight.SPEC_ALL lresproof_RULES)))) THEN
      EXISTS_TAC [[B:form->bool]] THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [isaresolvent] THEN ASM_REWRITE_TAC [] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV Session.let_CONV) THEN
      MAP_EVERY EXISTS_TAC [ [[A1:form->bool]], [[B1:form->bool]] ] THEN
      ASM_REWRITE_TAC [] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV Session.let_CONV) THEN REWRITE_TAC [], ALL_TAC] THEN
    ASM_REWRITE_TAC [ALL2])
  : ExceptT String IO thm).run
#eval LINEAR_RESOLUTION_COMPLETE

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py from the `#eval`s above. -/
unsafe def ensure : IO Unit := once "HolLogicArith.Linear" do
  replay (
          HolLogicArith.Given.ensure)
  replay (
          RESOLVE_CLAUSE)
  replay (
          PRESPROOF_CLAUSE)
  replay (
          RESOLVE_MONO)
  replay (
          do IO.println ppresproof_RULES; IO.println ppresproof_INDUCT; IO.println ppresproof_CASES)
  replay (
          PPRESPROOF)
  replay (
          PPRESPROOF_CLAUSE)
  replay (
          PPRESPROOF_CONSEQUENCE)
  replay (
          PPRESPROOF_SOUND)
  replay (
          PPRESPROOF_ALLNEGATIVE)
  replay (
          do IO.println lpresproof_RULES; IO.println lpresproof_INDUCT; IO.println lpresproof_CASES)
  replay (
          LPRESPROOF_MONO)
  replay (
          RESOLVE_SYM)
  replay (
          RESOLVE_TAUT_L)
  replay (
          RESOLVE_TAUT_R)
  replay (
          SUBSET_TAUT)
  replay (
          suffix)
  replay (
          SUFFIX_REFL)
  replay (
          SUFFIX_BUTLAST)
  replay (
          SUFFIX_TRANS)
  replay (
          SUFFIX_MEM)
  replay (
          SUFFIX_CONS)
  replay (
          SUFFIX_LENGTH)
  replay (
          NOT_SUFFIX_TAIL)
  replay (
          SUFFIX_ANTISYM)
  replay (
          NEGATE_LITERAL)
  replay (
          SYMMETRY_LEMMA_1)
  replay (
          SYMMETRY_LEMMA_2)
  replay (
          LINEARIZATION)
  replay (
          do IO.println lresproof_RULES; IO.println lresproof_INDUCT; IO.println lresproof_CASES)
  replay (
          ALL2_BUTLAST)
  replay (
          ALL2_MEM)
  replay (
          LRESPROOF_CLAUSE)
  replay (
          LINEAR_RESOLUTION_COMPLETE)
-- @@ENSURE END

end HolLogicArith.Linear
