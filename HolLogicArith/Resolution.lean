/- File: HolLogicArith/Resolution.lean
Translation of HOL Light's Logic/resolution.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolLogicArith.Herbrand
import HolLogicArith.Unif
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

namespace HolLogicArith.Resolution

/- List definitions/theorems used below are exposed by Session as fields of
   the `listDefs`/`listThms1`/`listThms2` bundles; alias the ones we need. -/
private unsafe def LENGTH : thm := Session.listDefs.LENGTH
private unsafe def MAP : thm := Session.listDefs.MAP
private unsafe def ITLIST : thm := Session.listDefs.ITLIST
private unsafe def MEM : thm := Session.listDefs.MEM
private unsafe def MAP_o : thm := Session.listThms1.MAP_o
private unsafe def MAP_EQ : thm := Session.listThms1.MAP_EQ

#eval HolLogicArith.Herbrand.ensure
#eval HolLogicArith.Unif.ensure

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- `new_recursive_definition` lifted into `ExceptT String IO`. -/
private unsafe def newRec (ax : thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (Session.new_recursive_definition ax tm)

/- `new_specification` lifted into `ExceptT String IO`. -/
private unsafe def newSpec (names : List String) (th : thm) : ExceptT String IO thm :=
  ExceptT.mk (Session.new_specification names th)

/- `new_inductive_definition`, panicking with HOL Light's message on failure. -/
private unsafe def newInductive (tm : term) : thm × thm × thm :=
  match unsafeIO (Session.new_inductive_definition tm) with
  | .ok (.ok t) => t
  | .ok (.error e) => panic! s!"new_inductive_definition: {e}"
  | .error e => panic! s!"new_inductive_definition IO: {e}"

#eval phrase 1
unsafe def atom : thm := keep "atom" fun _ => (do
  newRec form_RECURSION
    [[(atom False <=> F) /\
      (atom (Atom p l) <=> T) /\
      (atom (q --> r) <=> F) /\
      (atom (!! x q) <=> F)]]
  : ExceptT String IO thm).run
#eval atom

#eval phrase 2
unsafe def literal : thm := keep "literal" fun _ => new_definition
  [[literal p <=> atom(p) \/ ?q. atom(q) /\ (p = Not q)]]
#eval literal

#eval phrase 3
unsafe def clause : thm := keep "clause" fun _ => new_definition
  [[clause cl <=> FINITE cl /\ !p. p IN cl ==> literal p]]
#eval clause

#eval phrase 4
unsafe def LITERAL : thm := keep "LITERAL" fun _ => (do
  prove ([[literal(Atom r args) /\
   literal(Not(Atom r args))]])
   (MESON_TAC [literal, atom])
  : ExceptT String IO thm).run
#eval LITERAL

#eval phrase 5
unsafe def ATOM : thm := keep "ATOM" fun _ => (do
  prove ([[atom p <=> ?q l. p = Atom q l]])
   (MESON_TAC [atom, form_CASES])
  : ExceptT String IO thm).run
#eval ATOM

#eval phrase 6
unsafe def negative : thm := keep "negative" fun _ => new_definition
  [[negative p <=> ?q. p = Not q]]
#eval negative

#eval phrase 7
unsafe def positive : thm := keep "positive" fun _ => new_definition
  [[positive p <=> ~(negative p)]]
#eval positive

#eval phrase 8
unsafe def negate : thm := keep "negate" fun _ => new_definition
  [[~~p = if negative p then @q. (Not q = p) else Not p]]
#eval negate

#eval phrase 9
unsafe def PHOLDS_NEGATE : thm := keep "PHOLDS_NEGATE" fun _ => (do
  prove ([[pholds d (~~p) <=> ~(pholds d p)]])
   (REWRITE_TAC [negate] THEN
    COND_CASES_TAC THEN REWRITE_TAC [PHOLDS] THEN
    POP_ASSUM (CHOOSE_THEN SUBST1_TAC oTIO HolLight.REWRITE_RULE [negative]) THEN
    REWRITE_TAC [Not_DEF, form_INJ, SELECT_REFL, PHOLDS])
  : ExceptT String IO thm).run
#eval PHOLDS_NEGATE

#eval phrase 10
unsafe def HOLDS_NEGATE : thm := keep "HOLDS_NEGATE" fun _ => (do
  prove ([[holds M v (~~p) <=> ~(holds M v p)]])
   (REWRITE_TAC [negate] THEN
    COND_CASES_TAC THEN REWRITE_TAC [HOLDS] THEN
    POP_ASSUM (CHOOSE_THEN SUBST1_TAC oTIO HolLight.REWRITE_RULE [negative]) THEN
    REWRITE_TAC [Not_DEF, form_INJ, SELECT_REFL, HOLDS])
  : ExceptT String IO thm).run
#eval HOLDS_NEGATE

#eval phrase 11
unsafe def NEGATE_NEG : thm := keep "NEGATE_NEG" fun _ => (do
  prove ([[~~(Not p) = p]])
   (REWRITE_TAC [negate, negative, Not_DEF, form_INJ, (← HolLight.GSYM EXISTS_REFL)])
  : ExceptT String IO thm).run
#eval NEGATE_NEG

#eval phrase 12
unsafe def NEGATE_ATOM : thm := keep "NEGATE_ATOM" fun _ => (do
  prove ([[!p. atom p ==> (~~p = Not p)]])
   (MATCH_MP_TAC form_INDUCTION THEN REWRITE_TAC [atom] THEN
    REWRITE_TAC [negate, negative, Not_DEF, form_DISTINCT])
  : ExceptT String IO thm).run
#eval NEGATE_ATOM

#eval phrase 13
unsafe def NEGATE_REFL : thm := keep "NEGATE_REFL" fun _ => (do
  prove ([[!p. ~(~~p = p)]])
   (MESON_TAC [PHOLDS_NEGATE])
  : ExceptT String IO thm).run
#eval NEGATE_REFL

#eval phrase 14
unsafe def PHOLDS_ATOM : thm := keep "PHOLDS_ATOM" fun _ => (do
  prove ([[!p d. atom(p) ==> (pholds d p = d(p))]])
   (MATCH_MP_TAC form_INDUCTION THEN REWRITE_TAC [atom, pholds])
  : ExceptT String IO thm).run
#eval PHOLDS_ATOM

#eval phrase 15
unsafe def NEGATE_NEGATE : thm := keep "NEGATE_NEGATE" fun _ => (do
  prove ([[!p. literal p ==> (~~(~~p) = p)]])
   (REWRITE_TAC [literal] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [NEGATE_ATOM, NEGATE_NEG])
  : ExceptT String IO thm).run
#eval NEGATE_NEGATE

#eval phrase 16
unsafe def resolve : thm := keep "resolve" fun _ => new_definition
  [[resolve (p:form) cl1 cl2 = (cl1 DELETE p) UNION (cl2 DELETE ~~p)]]
#eval resolve

#eval phrase 17
unsafe def presproof_triple : thm × thm × thm := keep "presproof_triple" fun _ =>
  newInductive
    [[(!cl. cl IN hyps ==> presproof hyps cl) /\
      (!p cl1 cl2.
          presproof hyps cl1 /\ presproof hyps cl2 /\ p IN cl1 /\ ~~p IN cl2
         ==> presproof hyps (resolve p cl1 cl2))]]
unsafe def presproof_RULES : thm := presproof_triple.1
unsafe def presproof_INDUCT : thm := presproof_triple.2.1
unsafe def presproof_CASES : thm := presproof_triple.2.2
#eval do IO.println presproof_RULES; IO.println presproof_INDUCT; IO.println presproof_CASES

#eval phrase 18
unsafe def interp : thm := keep "interp" fun _ => new_definition
  [[interp cl = ITLIST (||) (list_of_set cl) False]]
#eval interp

#eval phrase 19
unsafe def UNPSATISFIABLE_FINITE_SUBSET : thm := keep "UNPSATISFIABLE_FINITE_SUBSET" fun _ => (do
  prove ([[!s. ~(psatisfiable s)
       ==> ?t. FINITE t /\ t SUBSET s /\ ~(psatisfiable t)]])
   (REWRITE_TAC [psatisfiable] THEN MESON_TAC [COMPACT_PROP])
  : ExceptT String IO thm).run
#eval UNPSATISFIABLE_FINITE_SUBSET

#eval phrase 20
unsafe def PRESPROOF_MONO : thm := keep "PRESPROOF_MONO" fun _ => (do
  prove ([[!hyps1 hyps2 c.
        presproof hyps1 c /\ hyps1 SUBSET hyps2 ==> presproof hyps2 c]])
   (GEN_TAC THEN HolLight.GEN_REWRITE_TAC HolCore.Lib.I [SWAP_FORALL_THM] THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC presproof_INDUCT THEN MESON_TAC [presproof_RULES, SUBSET])
  : ExceptT String IO thm).run
#eval PRESPROOF_MONO

#eval phrase 21
unsafe def PRESPROOF_TRANS : thm := keep "PRESPROOF_TRANS" fun _ => (do
  prove ([[!hyps hyps' c.
        (!c'. c' IN hyps' ==> presproof hyps c') /\ presproof hyps' c
        ==> presproof hyps c]])
   (HolLight.GEN_REWRITE_TAC HolCore.Lib.I [SWAP_FORALL_THM] THEN GEN_TAC THEN
    ONCE_REWRITE_TAC [IMP_CONJ_ALT] THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC presproof_INDUCT THEN MESON_TAC [presproof_RULES])
  : ExceptT String IO thm).run
#eval PRESPROOF_TRANS

#eval phrase 22
unsafe def IMAGE_CLAUSE : thm := keep "IMAGE_CLAUSE" fun _ => (do
  prove ([[{interp cl | cl IN hyps} = IMAGE interp hyps]])
   (REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_IMAGE, CONJ_ACI])
  : ExceptT String IO thm).run
#eval IMAGE_CLAUSE

#eval phrase 23
unsafe def PHOLDS_INTERP : thm := keep "PHOLDS_INTERP" fun _ => (do
  prove ([[!cl d. FINITE cl ==> (pholds d (interp cl) <=> ?p. p IN cl /\ pholds d p)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [interp] THEN
    FIRST_X_ASSUM (fun th => HolLight.tactic_of do
      let mmp ← HolLight.MATCH_MP LIST_OF_SET_PROPERTIES th
      let c1 ← liftExcept (Session.CONJUNCT1 mmp)
      let g ← HolLight.GSYM c1
      pure (HolLight.GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.ONCE_DEPTH_CONV)
         [g])) THEN
    SPEC_TAC ([[list_of_set(cl:form->bool)]], [[l:form list]]) THEN
    LIST_INDUCT_TAC THEN
    REWRITE_TAC [ITLIST, PHOLDS, set_of_list, NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC [IN_INSERT] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval PHOLDS_INTERP

#eval phrase 24
unsafe def HOLDS_INTERP : thm := keep "HOLDS_INTERP" fun _ => (do
  prove ([[!cl M v. FINITE cl
            ==> (holds M v (interp cl) <=> ?p. p IN cl /\ holds M v p)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [interp] THEN
    FIRST_X_ASSUM (fun th => HolLight.tactic_of do
      let mmp ← HolLight.MATCH_MP LIST_OF_SET_PROPERTIES th
      let c1 ← liftExcept (Session.CONJUNCT1 mmp)
      let g ← HolLight.GSYM c1
      pure (HolLight.GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.ONCE_DEPTH_CONV)
         [g])) THEN
    SPEC_TAC ([[list_of_set(cl:form->bool)]], [[l:form list]]) THEN
    LIST_INDUCT_TAC THEN
    REWRITE_TAC [ITLIST, HOLDS, set_of_list, NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC [IN_INSERT] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval HOLDS_INTERP

#eval phrase 25
unsafe def PRESPROOF_REFUTATION_COMPLETE_FINITE : thm := keep "PRESPROOF_REFUTATION_COMPLETE_FINITE" fun _ => (do
  prove ([[FINITE hyps /\
   (!cl. cl IN hyps ==> clause cl) /\
   ~(psatisfiable {interp cl | cl IN hyps})
   ==> presproof hyps {}]])
   (REWRITE_TAC [IMAGE_CLAUSE] THEN
    SUBGOAL_THEN
     ([[!n hyps. FINITE hyps /\
             (CARD(UNIONS hyps) = n) /\
             (!cl. cl IN hyps ==> clause cl) /\
             ~(psatisfiable (IMAGE interp hyps))
             ==> presproof hyps {}]])
     (fun th => MESON_TAC [th]) THEN
    MATCH_MP_TAC num_WF THEN X_GEN_TAC [[n:num]] THEN DISCH_TAC THEN
    X_GEN_TAC [[hyps:(form->bool)->bool]] THEN
    ASM_CASES_TAC [[{}:form->bool IN hyps]] THENL
     [ASM_SIMP_TAC [presproof_RULES], ALL_TAC] THEN
    ASM_CASES_TAC [[hyps:(form->bool)->bool = {}]] THENL
     [ASM_REWRITE_TAC [psatisfiable, IMAGE_CLAUSES, NOT_IN_EMPTY], ALL_TAC] THEN
    STRIP_TAC THEN SUBGOAL_THEN ([[FINITE(UNIONS hyps :form->bool)]])
    ASSUME_TAC THENL
     [ASM_MESON_TAC [clause, FINITE_UNIONS], ALL_TAC] THEN
    SUBGOAL_THEN ([[?p. atom p /\ p IN UNIONS hyps /\ ~~p IN UNIONS hyps]])
     (X_CHOOSE_THEN ([[p:form]]) STRIP_ASSUME_TAC)
    THENL
     [SUBGOAL_THEN ([[?p. literal p /\ p IN UNIONS hyps /\ ~~p IN UNIONS hyps]])
      MP_TAC THENL
       [ALL_TAC,
        REWRITE_TAC [literal] THEN STRIP_TAC THENL
         [ASM_MESON_TAC [], ALL_TAC] THEN
        EXISTS_TAC [[~~p]] THEN ASM_REWRITE_TAC [NEGATE_NEG] THEN
        ASM_MESON_TAC [NEGATE_ATOM]] THEN
      HolLight.GEN_REWRITE_TAC HolCore.Lib.I [(← ExceptT.mk (TAUT [[p <=> ~ ~ p]]))] THEN
      PURE_ONCE_REWRITE_TAC [NOT_EXISTS_THM] THEN
      REWRITE_TAC [(← ExceptT.mk (TAUT [[~(a /\ b /\ c) <=> a ==> ~b \/ ~c]]))] THEN
      REWRITE_TAC [IN_UNIONS, NOT_EXISTS_THM] THEN
      REWRITE_TAC [(← ExceptT.mk (TAUT [[~(a /\ b) <=> a ==> ~b]]))] THEN STRIP_TAC THEN
      FIRST_ASSUM (MP_TAC oTIO HolLight.GEN_REWRITE_RULE HolLight.RAND_CONV [psatisfiable]) THEN
      REWRITE_TAC [] THEN EXISTS_TAC [[\p:form. p IN UNIONS hyps]] THEN
      REWRITE_TAC [IN_IMAGE, LEFT_IMP_EXISTS_THM] THEN
      GEN_TAC THEN X_GEN_TAC [[cl:form->bool]] THEN
      DISCH_THEN (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
      SUBGOAL_THEN ([[FINITE(cl:form->bool)]]) ASSUME_TAC THENL
       [ASM_MESON_TAC [clause], ALL_TAC] THEN
      ASM_SIMP_TAC [PHOLDS_INTERP] THEN
      SUBGOAL_THEN ([[?p:form. p IN cl]]) MP_TAC THENL
       [ASM_MESON_TAC [EXTENSION, NOT_IN_EMPTY], ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC [[q:form]] THEN DISCH_TAC THEN
      SUBGOAL_THEN ([[literal q]]) MP_TAC THENL
       [ASM_MESON_TAC [clause], ALL_TAC] THEN
      REWRITE_TAC [literal] THEN
      STRIP_TAC THEN ASM_SIMP_TAC [PHOLDS, PHOLDS_ATOM] THEN
      ASM_MESON_TAC [IN_UNIONS, NEGATE_ATOM, literal],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC oTIO
      HolLight.GEN_REWRITE_RULE HolLight.BINDER_CONV [RIGHT_IMP_FORALL_THM]) THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (TAUT [[(a ==> b /\ c /\ d ==> e) <=>
                         (c ==> a /\ b /\ d ==> e)]]))] THEN
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SIMP_TAC [] THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    REWRITE_TAC [LEFT_FORALL_IMP_THM, EXISTS_REFL] THEN
    UNDISCH_THEN ([[CARD (UNIONS hyps :form->bool) = n]]) (SUBST1_TAC oTIO HolLight.SYM) THEN
    ABBREV_TAC [[hyps' = {cl | cl IN hyps /\ ~(p IN cl) /\ ~(~~p IN cl)} UNION
                      {cl | ?cl1 cl2. cl1 IN hyps /\ cl2 IN hyps /\
                                      p IN cl1 /\ ~(~~p IN cl1) /\
                                      ~~p IN cl2 /\ ~(p IN cl2) /\
                                      (cl = resolve p cl1 cl2)}]] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[hyps':(form->bool)->bool]]) THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT
     [[(e ==> f) /\ b /\ c /\ a /\ (c ==> d)
    ==> (a /\ b /\ c /\ d ==> e) ==> f]])) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC (← HolLight.ONCE_REWRITE_RULE [IMP_CONJ]
                  PRESPROOF_TRANS) THEN
      X_GEN_TAC [[cl:form->bool]] THEN Fol.EXPAND_TAC "hyps'" THEN
      REWRITE_TAC [IN_UNION, IN_ELIM_THM] THEN MESON_TAC [presproof_RULES],
      ALL_TAC] THEN
    CONJ_TAC THENL
     [Fol.EXPAND_TAC "hyps'" THEN REWRITE_TAC [FINITE_UNION] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC [[hyps:(form->bool)->bool]] THEN
        ASM_SIMP_TAC [SUBSET, IN_ELIM_THM], ALL_TAC] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC [[IMAGE (\(cl1,cl2). resolve p cl1 cl2)
                      {(cl1,cl2) | cl1 IN hyps /\ cl2 IN hyps}]] THEN
      ASM_SIMP_TAC [FINITE_IMAGE, FINITE_PRODUCT] THEN
      REWRITE_TAC [SUBSET, IN_IMAGE, IN_ELIM_THM] THEN
      ONCE_REWRITE_TAC [EXISTS_PAIR_THM] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC [PAIR_EQ],
      ALL_TAC] THEN
    CONJ_TAC THENL
     [GEN_TAC THEN Fol.EXPAND_TAC "hyps'" THEN
      REWRITE_TAC [IN_UNION, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC [] THEN REWRITE_TAC [clause, resolve] THEN
      REWRITE_TAC [FINITE_UNION, FINITE_DELETE, IN_UNION, IN_DELETE] THEN
      ASM_MESON_TAC [clause], ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LET_TRANS THEN
      EXISTS_TAC [[CARD(((UNIONS hyps) DELETE p) DELETE ~~p)]] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
         [ALL_TAC,
          ASM_SIMP_TAC [FINITE_UNIONS, FINITE_DELETE] THEN
          ASM_MESON_TAC [clause]] THEN
        Fol.EXPAND_TAC "hyps'" THEN
        REWRITE_TAC [SUBSET, IN_UNIONS, IN_UNION, IN_DELETE, IN_ELIM_THM] THEN
        REWRITE_TAC [EXTENSION, resolve, IN_UNION, IN_DELETE] THEN MESON_TAC [],
        ASM_SIMP_TAC [CARD_DELETE, FINITE_DELETE] THEN
        ASM_REWRITE_TAC [IN_DELETE, NEGATE_REFL] THEN
        ASM_MESON_TAC [HAS_SIZE, HAS_SIZE_0, MEMBER_NOT_EMPTY,
                      (← ExceptT.mk (ARITH_RULE [[~(n = 0) ==> n - 1 - 1 < n]]))]],
      ALL_TAC] THEN
    DISCH_TAC THEN
    UNDISCH_TAC [[~psatisfiable (IMAGE interp hyps)]] THEN
    REWRITE_TAC [(← ExceptT.mk (TAUT [[~a ==> ~b <=> b ==> a]]))] THEN
    SIMP_TAC [psatisfiable, IN_IMAGE, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC [[d:form->bool]] THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    ONCE_REWRITE_TAC [IMP_CONJ] THEN
    REWRITE_TAC [LEFT_FORALL_IMP_THM, EXISTS_REFL] THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [clause]) THEN
    ASM_SIMP_TAC [PHOLDS_INTERP] THEN DISCH_TAC THEN
    ASM_CASES_TAC
     ([[!cl. cl IN hyps /\ p IN cl /\ ~(~~p IN cl)
         ==> ?q. q IN (cl DELETE p) /\ pholds d q]])
    THENL
     [EXISTS_TAC [[\x:form. if x = p then F else d(x)]] THEN
      X_GEN_TAC [[cl:form->bool]] THEN DISCH_TAC THEN
      ASM_CASES_TAC [[~~p IN cl]] THENL
       [EXISTS_TAC [[~~p]] THEN ASM_SIMP_TAC [PHOLDS_NEGATE, PHOLDS_ATOM],
        ALL_TAC] THEN
      ASM_CASES_TAC [[p:form IN cl]] THENL
       [UNDISCH_TAC
         ([[!cl. cl IN hyps /\ p IN cl /\ ~(~~p IN cl)
             ==> (?q. q IN cl DELETE p /\ pholds d q)]]) THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC [[cl:form->bool]]) THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[q:form]] THEN
        REWRITE_TAC [IN_DELETE] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
        SUBGOAL_THEN ([[literal q]]) MP_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
        REWRITE_TAC [literal] THEN
        DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL
         [ASM_SIMP_TAC [PHOLDS_ATOM] THEN ASM_MESON_TAC [PHOLDS_ATOM],
          ALL_TAC] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[r:form]])
         (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
        ASM_SIMP_TAC [PHOLDS, PHOLDS_ATOM] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
        ASM_MESON_TAC [PHOLDS, PHOLDS_ATOM], ALL_TAC] THEN
      UNDISCH_TAC [[!x. x IN hyps' ==> (?p. p IN x /\ pholds d p)]] THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC [[cl:form->bool]]) THEN
      Fol.EXPAND_TAC "hyps'" THEN REWRITE_TAC [IN_UNION] THEN
      MATCH_MP_TAC (← ExceptT.mk (TAUT [[((a ==> c) ==> d) ==> (a \/ b ==> c) ==> d]])) THEN
      ASM_REWRITE_TAC [IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC [[q:form]] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN ([[literal q]]) MP_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      REWRITE_TAC [literal] THEN
      DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL
       [ASM_SIMP_TAC [PHOLDS_ATOM] THEN
        COND_CASES_TAC THEN ASM_MESON_TAC [PHOLDS_ATOM],
        ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[r:form]])
       (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
      ASM_SIMP_TAC [PHOLDS, PHOLDS_ATOM] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC [PHOLDS, PHOLDS_ATOM], ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [NOT_FORALL_THM]) THEN
    REWRITE_TAC [NOT_IMP, NOT_EXISTS_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[cl1:form->bool]]) STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC
     ([[!cl. cl IN hyps /\ ~~p IN cl /\ ~(p IN cl)
         ==> ?q. q IN (cl DELETE ~~p) /\ pholds d q]])
    THENL
     [EXISTS_TAC [[\x:form. if x = p then T else d(x)]] THEN
      X_GEN_TAC [[cl:form->bool]] THEN DISCH_TAC THEN
      ASM_CASES_TAC [[p:form IN cl]] THENL
       [EXISTS_TAC [[p:form]] THEN ASM_SIMP_TAC [PHOLDS_NEGATE, PHOLDS_ATOM],
        ALL_TAC] THEN
      ASM_CASES_TAC [[~~p IN cl]] THENL
       [UNDISCH_TAC
         ([[!cl. cl IN hyps /\ ~~p IN cl /\ ~(p IN cl)
             ==> (?q. q IN cl DELETE ~~p /\ pholds d q)]]) THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC [[cl:form->bool]]) THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[q:form]] THEN
        REWRITE_TAC [IN_DELETE] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
        SUBGOAL_THEN ([[literal q]]) MP_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
        REWRITE_TAC [literal] THEN
        DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL
         [ASM_SIMP_TAC [PHOLDS_ATOM] THEN
          COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [PHOLDS_ATOM],
          ALL_TAC] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[r:form]])
         (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
        ASM_SIMP_TAC [PHOLDS, PHOLDS_ATOM] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
        ASM_MESON_TAC [PHOLDS, PHOLDS_ATOM, NEGATE_ATOM], ALL_TAC] THEN
      UNDISCH_TAC [[!x. x IN hyps' ==> (?p. p IN x /\ pholds d p)]] THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC [[cl:form->bool]]) THEN
      Fol.EXPAND_TAC "hyps'" THEN REWRITE_TAC [IN_UNION] THEN
      MATCH_MP_TAC (← ExceptT.mk (TAUT [[((a ==> c) ==> d) ==> (a \/ b ==> c) ==> d]])) THEN
      ASM_REWRITE_TAC [IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC [[q:form]] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN ([[literal q]]) MP_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      REWRITE_TAC [literal] THEN
      DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL
       [ASM_SIMP_TAC [PHOLDS_ATOM] THEN
        COND_CASES_TAC THEN ASM_MESON_TAC [PHOLDS_ATOM],
        ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[r:form]])
       (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
      ASM_SIMP_TAC [PHOLDS, PHOLDS_ATOM] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THENL
       [ASM_MESON_TAC [NEGATE_ATOM],
        ASM_MESON_TAC [PHOLDS, PHOLDS_ATOM]], ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [NOT_FORALL_THM]) THEN
    REWRITE_TAC [NOT_IMP, NOT_EXISTS_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[cl2:form->bool]]) STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC [[!x. x IN hyps' ==> (?p. p IN x /\ pholds d p)]] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[~a ==> a ==> b]])) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[resolve p cl1 cl2]]) THEN
    Fol.EXPAND_TAC "hyps'" THEN REWRITE_TAC [IN_UNION] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[b /\ ~c ==> ~(a \/ b ==> c)]])) THEN
    CONJ_TAC THENL
     [REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [],
      REWRITE_TAC [resolve, IN_UNION] THEN ASM_MESON_TAC []])
  : ExceptT String IO thm).run
#eval PRESPROOF_REFUTATION_COMPLETE_FINITE

#eval phrase 26
unsafe def PRESPROOF_REFUTATION_COMPLETE : thm := keep "PRESPROOF_REFUTATION_COMPLETE" fun _ => (do
  prove ([[(!cl. cl IN hyps ==> clause cl) /\
   ~(psatisfiable {interp cl | cl IN hyps})
   ==> presproof hyps {}]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC PRESPROOF_MONO THEN
    FIRST_ASSUM (MP_TAC oTIO HolLight.MATCH_MP UNPSATISFIABLE_FINITE_SUBSET) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[t:form->bool]]) STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
      ([[?h. FINITE h /\ h SUBSET hyps /\ t SUBSET {interp cl | cl IN h}]])
    MP_TAC THENL
     [REWRITE_TAC [IMAGE_CLAUSE] THEN MATCH_MP_TAC FINITE_SUBSET_IMAGE_IMP THEN
      ASM_REWRITE_TAC [(← HolLight.GSYM IMAGE_CLAUSE)], ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC [] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC PRESPROOF_REFUTATION_COMPLETE_FINITE THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
      [ [[~(psatisfiable t)]], [[t SUBSET {interp cl | cl IN h}]] ] THEN
    REWRITE_TAC [PSATISFIABLE_MONO, (← ExceptT.mk (TAUT [[b ==> ~c ==> ~a <=> a /\ b ==> c]]))])
  : ExceptT String IO thm).run
#eval PRESPROOF_REFUTATION_COMPLETE

#eval phrase 27
#eval parse_as_infix ("instance_of", (12, "right"))

#eval phrase 28
unsafe def instance_of : thm := keep "instance_of" fun _ => new_definition
  [[cl1 instance_of cl2 <=> ?i. cl1 = IMAGE (formsubst i) cl2]]
#eval instance_of

#eval phrase 29
unsafe def FVS : thm := keep "FVS" fun _ => new_definition
  [[FVS(cl) = UNIONS {FV(p) | p IN cl}]]
#eval FVS

#eval phrase 30
unsafe def NEGATIVE_FORMSUBST : thm := keep "NEGATIVE_FORMSUBST" fun _ => (do
  prove ([[!p. negative (formsubst i p) = negative p]])
   (MATCH_MP_TAC form_INDUCTION THEN
    REWRITE_TAC [negative, form_DISTINCT, Not_DEF, formsubst] THEN
    CONV_TAC (HolLight.TOP_DEPTH_CONV Session.let_CONV) THEN REWRITE_TAC [form_DISTINCT] THEN
    SIMP_TAC [form_INJ, LEFT_EXISTS_AND_THM, (← HolLight.GSYM EXISTS_REFL)] THEN
    GEN_TAC THEN X_GEN_TAC [[r:form]] THEN STRIP_TAC THEN
    SPEC_TAC ([[r:form]], [[r:form]]) THEN MATCH_MP_TAC form_INDUCTION THEN
    REWRITE_TAC [formsubst, LET_DEF, LET_END_DEF, form_DISTINCT])
  : ExceptT String IO thm).run
#eval NEGATIVE_FORMSUBST

#eval phrase 31
unsafe def FORMSUBST_NEGATE : thm := keep "FORMSUBST_NEGATE" fun _ => (do
  prove ([[!p i. formsubst i (~~p) = ~~(formsubst i p)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [negate, NEGATIVE_FORMSUBST] THEN
    COND_CASES_TAC THEN REWRITE_TAC [Not_DEF, formsubst] THEN
    FIRST_ASSUM (X_CHOOSE_THEN ([[q:form]]) SUBST1_TAC oTIO
      HolLight.GEN_REWRITE_RULE HolCore.Lib.I [negative]) THEN
    REWRITE_TAC [Not_DEF, form_INJ, formsubst])
  : ExceptT String IO thm).run
#eval FORMSUBST_NEGATE

#eval phrase 32
unsafe def FORMSUBST_ATOM : thm := keep "FORMSUBST_ATOM" fun _ => (do
  prove ([[!p i. atom (formsubst i p) = atom p]])
   (MATCH_MP_TAC form_INDUCTION THEN
    REWRITE_TAC [formsubst, atom, LET_DEF, LET_END_DEF])
  : ExceptT String IO thm).run
#eval FORMSUBST_ATOM

#eval phrase 33
unsafe def FORMSUBST_NOT : thm := keep "FORMSUBST_NOT" fun _ => (do
  prove ([[!i p. formsubst i (Not p) = Not(formsubst i p)]])
   (REWRITE_TAC [Not_DEF, formsubst])
  : ExceptT String IO thm).run
#eval FORMSUBST_NOT

#eval phrase 34
unsafe def NOT_NOT_ATOM : thm := keep "NOT_NOT_ATOM" fun _ => (do
  prove ([[!p. ~atom(Not p)]])
   (REWRITE_TAC [Not_DEF, atom, form_INJ])
  : ExceptT String IO thm).run
#eval NOT_NOT_ATOM

#eval phrase 35
unsafe def FORMSUBST_LITERAL : thm := keep "FORMSUBST_LITERAL" fun _ => (do
  prove ([[!p i. literal (formsubst i p) = literal p]])
   (MATCH_MP_TAC form_INDUCTION THEN
    REWRITE_TAC [formsubst] THEN
    CONV_TAC (HolLight.TOP_DEPTH_CONV Session.let_CONV) THEN
    REWRITE_TAC [literal, form_DISTINCT, atom, Not_DEF] THEN
    MAP_EVERY X_GEN_TAC [ [[s:form]], [[r:form]] ] THEN STRIP_TAC THEN
    SPEC_TAC ([[r:form]], [[r:form]]) THEN MATCH_MP_TAC form_INDUCTION THEN
    REWRITE_TAC [formsubst, LET_DEF, LET_END_DEF, form_DISTINCT, form_INJ] THEN
    MESON_TAC [FORMSUBST_NOT, FORMSUBST_ATOM])
  : ExceptT String IO thm).run
#eval FORMSUBST_LITERAL

#eval phrase 36
unsafe def QFREE_NOT : thm := keep "QFREE_NOT" fun _ => (do
  prove ([[!p. qfree(Not p) = qfree p]])
   (REWRITE_TAC [Not_DEF, qfree])
  : ExceptT String IO thm).run
#eval QFREE_NOT

#eval phrase 37
unsafe def QFREE_ATOM : thm := keep "QFREE_ATOM" fun _ => (do
  prove ([[!p. atom p ==> qfree p]])
   (MATCH_MP_TAC form_INDUCTION THEN REWRITE_TAC [atom, qfree])
  : ExceptT String IO thm).run
#eval QFREE_ATOM

#eval phrase 38
unsafe def QFREE_LITERAL : thm := keep "QFREE_LITERAL" fun _ => (do
  prove ([[!p. literal p ==> qfree p]])
   (REWRITE_TAC [literal] THEN MESON_TAC [QFREE_ATOM, QFREE_NOT])
  : ExceptT String IO thm).run
#eval QFREE_LITERAL

#eval phrase 39
unsafe def QFREE_NEGATE : thm := keep "QFREE_NEGATE" fun _ => (do
  prove ([[!p. qfree(~~p) = qfree p]])
   (GEN_TAC THEN REWRITE_TAC [negate] THEN
    COND_CASES_TAC THEN REWRITE_TAC [QFREE_NOT] THEN
    FIRST_ASSUM (CHOOSE_THEN SUBST1_TAC oTIO HolLight.GEN_REWRITE_RULE HolCore.Lib.I [negative]) THEN
    REWRITE_TAC [QFREE_NOT, Not_DEF, form_INJ])
  : ExceptT String IO thm).run
#eval QFREE_NEGATE

#eval phrase 40
unsafe def LIFTING_LEMMA : thm := keep "LIFTING_LEMMA" fun _ => (do
  prove ([[!A B A' B' C' p.
        clause A /\ clause B /\ (FVS(A) INTER FVS(B) = {}) /\
        A' instance_of A /\ B' instance_of B /\
        p IN A' /\ ~~p IN B' /\ (C' = resolve p A' B')
        ==> ?A1 B1. A1 SUBSET A /\ B1 SUBSET B /\ ~(A1 = {}) /\ ~(B1 = {}) /\
                    (?i. Unifies i (A1 UNION {~~l | l IN B1})) /\
                    !j. ismgu (A1 UNION {~~l | l IN B1}) j
                        ==> C' instance_of (IMAGE (formsubst j)
                                           ((A DIFF A1) UNION (B DIFF B1)))]])
   (REWRITE_TAC [clause] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[?i. (A' = IMAGE (formsubst i) A) /\
                    (B' = IMAGE (formsubst i) B)]])
     (X_CHOOSE_THEN ([[i:num->term]]) (STRIP_ASSUME_TAC oTIO HolLight.GSYM))
    THENL
     [UNDISCH_TAC [[A' instance_of A]] THEN REWRITE_TAC [instance_of] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[ia:num->term]]) SUBST1_TAC) THEN
      UNDISCH_TAC [[B' instance_of B]] THEN REWRITE_TAC [instance_of] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[ib:num->term]]) SUBST1_TAC) THEN
      EXISTS_TAC [[\x. if x IN FVS(A) then ia(x) else ib(x):term]] THEN
      REWRITE_TAC [EXTENSION, IN_IMAGE] THEN CONJ_TAC THEN
      X_GEN_TAC [[r:form]] THEN AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN
      X_GEN_TAC [[q:form]] THEN
      MATCH_MP_TAC (← ExceptT.mk (TAUT [[(b ==> (a <=> a')) ==> (a /\ b <=> a' /\ b)]])) THEN
      DISCH_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC FORMSUBST_VALUATION THEN
      X_GEN_TAC [[x:num]] THEN DISCH_TAC THEN REWRITE_TAC [] THENL
       [SUBGOAL_THEN ([[x IN FVS(A)]]) (fun th => REWRITE_TAC [th]) THEN
        REWRITE_TAC [FVS, IN_UNIONS, IN_ELIM_THM] THEN ASM_MESON_TAC [],
        SUBGOAL_THEN ([[~(x IN FVS(A))]]) (fun th => REWRITE_TAC [th]) THEN
        UNDISCH_TAC [[FVS(A) INTER FVS(B) = {}]] THEN
        REWRITE_TAC [EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
        REWRITE_TAC [FVS, IN_UNIONS, IN_ELIM_THM] THEN ASM_MESON_TAC []],
      ALL_TAC] THEN
    ABBREV_TAC [[A1 = {q | q IN A /\ (formsubst i q = p)}]] THEN
    ABBREV_TAC [[B1 = {r | r IN B /\ (formsubst i r = ~~p)}]] THEN
    MAP_EVERY EXISTS_TAC [ [[A1:form->bool]], [[B1:form->bool]] ] THEN
    SUBGOAL_THEN ([[Unifies i (A1 UNION {~~l | l IN B1})]]) ASSUME_TAC THENL
     [MAP_EVERY Fol.EXPAND_TAC ["A1", "B1"] THEN
      REWRITE_TAC [Unifies_DEF, IN_UNION, IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [FORMSUBST_NEGATE] THEN
      ASM_MESON_TAC [NEGATE_NEGATE, FORMSUBST_LITERAL],
      ALL_TAC] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[a /\ b /\ c /\ d /\ e /\
                     (a /\ b /\ c /\ d ==> f)
                     ==> a /\ b /\ c /\ d /\ e /\ f]])) THEN
    REPEAT CONJ_TAC THENL
     [Fol.EXPAND_TAC "A1" THEN SIMP_TAC [SUBSET, IN_ELIM_THM],
      Fol.EXPAND_TAC "B1" THEN SIMP_TAC [SUBSET, IN_ELIM_THM],
      Fol.EXPAND_TAC "A1" THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY] THEN
      UNDISCH_TAC [[p:form IN A']] THEN Fol.EXPAND_TAC "A'" THEN
      REWRITE_TAC [IN_IMAGE] THEN MESON_TAC [],
      Fol.EXPAND_TAC "B1" THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY] THEN
      UNDISCH_TAC [[~~p IN B']] THEN Fol.EXPAND_TAC "B'" THEN
      REWRITE_TAC [IN_IMAGE] THEN MESON_TAC [],
      EXISTS_TAC [[i:num->term]] THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    STRIP_TAC THEN X_GEN_TAC [[j:num->term]] THEN
    REWRITE_TAC [ISMGU] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[i:num->term]]) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[k:num->term]]) (ASSUME_TAC oTIO HolLight.GSYM)) THEN
    ASM_REWRITE_TAC [instance_of] THEN EXISTS_TAC [[k:num->term]] THEN
    MAP_EVERY Fol.EXPAND_TAC ["A'", "B'"] THEN
    REWRITE_TAC [IMAGE_UNION, (← HolLight.GSYM IMAGE_o), resolve] THEN
    SUBGOAL_THEN ([[IMAGE (formsubst i) A DELETE p =
                IMAGE (formsubst i) (A DIFF A1)]])
    SUBST1_TAC THENL
     [Fol.EXPAND_TAC "A1" THEN
      REWRITE_TAC [EXTENSION, IN_IMAGE, IN_DELETE, IN_DIFF, IN_ELIM_THM] THEN
      MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN ([[IMAGE (formsubst i) B DELETE ~~p =
                IMAGE (formsubst i) (B DIFF B1)]])
    SUBST1_TAC THENL
     [Fol.EXPAND_TAC "B1" THEN
      REWRITE_TAC [EXTENSION, IN_IMAGE, IN_DELETE, IN_DIFF, IN_ELIM_THM] THEN
      MESON_TAC [], ALL_TAC] THEN
    REWRITE_TAC [(← HolLight.GSYM IMAGE_UNION)] THEN
    SUBGOAL_THEN ([[!q. q IN (A DIFF A1 UNION B DIFF B1)
                    ==> (formsubst k (formsubst j q) = formsubst i q)]])
    MP_TAC THENL
     [REWRITE_TAC [IN_UNION, IN_DIFF] THEN ASM_MESON_TAC [QFREE_LITERAL],
      ALL_TAC] THEN
    ABBREV_TAC [[s:form->bool = A DIFF A1 UNION B DIFF B1]] THEN
    REWRITE_TAC [EXTENSION, IN_IMAGE, o_THM] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval LIFTING_LEMMA

#eval phrase 41
unsafe def FVS_CLAUSE_FINITE : thm := keep "FVS_CLAUSE_FINITE" fun _ => (do
  prove ([[!cl. clause(cl) ==> FINITE(FVS cl)]])
   (REWRITE_TAC [clause, FVS] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (← HolLight.MATCH_MP (← ExceptT.mk (TAUT [[(a ==> (b <=> c)) ==> a /\ c ==> b]]))
                          (← HolLight.SPEC_ALL FINITE_FINITE_UNIONS)) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN ([[FINITE (IMAGE FV cl)]]) MP_TAC THENL
       [ASM_SIMP_TAC [FINITE_IMAGE], ALL_TAC] THEN
      MATCH_MP_TAC EQ_IMP THEN
      AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN
      MESON_TAC [],
      SIMP_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM, FV_FINITE]])
  : ExceptT String IO thm).run
#eval FVS_CLAUSE_FINITE

#eval phrase 42
unsafe def RENAME_AWAY : thm := keep "RENAME_AWAY" fun _ => (do
  let lemma ← (do
    prove ([[((UNIONS s) INTER y = {}) <=> !x. x IN s ==> (x INTER y = {})]])
     (SET_TAC [])
    : ExceptT String IO thm)
  prove ([[!cl s. FINITE(s) /\ clause(cl)
          ==> ?i. renaming(i) /\ (FVS(IMAGE (formsubst i) cl) INTER s = {})]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[?n. !x. x IN s \/ x IN FVS cl ==> x < n]]) MP_TAC THENL
     [REWRITE_TAC [(← HolLight.GSYM IN_UNION)] THEN
      SUBGOAL_THEN ([[FINITE(s UNION FVS(cl))]]) MP_TAC THENL
       [ASM_SIMP_TAC [FINITE_UNION, FVS_CLAUSE_FINITE], ALL_TAC] THEN
      SPEC_TAC ([[s UNION FVS(cl)]], [[s:num->bool]]) THEN
      MATCH_MP_TAC FINITE_INDUCT THEN REWRITE_TAC [NOT_IN_EMPTY] THEN
      REWRITE_TAC [IN_INSERT] THEN
      MESON_TAC [(← ExceptT.mk (ARITH_RULE [[(x < a ==> x < a + b + 1) /\ b < a + b + 1]]))],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_TAC [[N:num]]) THEN
    EXISTS_TAC [[\x. if x < N then V(x + N) else if x < 2 * N then V(x - N)
                  else V(x)]] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [«renaming»] THEN
      EXISTS_TAC [[\x. if x < N then V(x + N) else if x < 2 * N then V(x - N)
                    else V(x)]] THEN
      REWRITE_TAC [] THEN REWRITE_TAC [FUN_EQ_THM, o_THM, I_DEF] THEN
      REWRITE_TAC [TERMSUBST_TERMSUBST] THEN GEN_TAC THEN
      HolLight.GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.GSYM TERMSUBST_TRIV)] THEN
      MATCH_MP_TAC TERMSUBST_VALUATION THEN
      GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [termsubst, o_THM] THEN
      POP_ASSUM_LIST (HolCore.Lib.K ALL_TAC) THEN
      REPEAT (COND_CASES_TAC THEN REWRITE_TAC [termsubst]) THEN
      REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC [ADD_SUB]) THEN
      AP_TERM_TAC THEN POP_ASSUM_LIST (fun ths => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.end_itlist HolLight.CONJ ths))) THEN ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [FVS, lemma] THEN
    SIMP_TAC [IN_IMAGE, LEFT_AND_EXISTS_THM, IN_ELIM_THM,
             LEFT_IMP_EXISTS_THM] THEN
    GEN_TAC THEN GEN_TAC THEN X_GEN_TAC [[r:form]] THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[!x. x IN FV(r) ==> x < N:num]]) ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC [FVS, IN_UNIONS, IN_ELIM_THM] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    REWRITE_TAC [EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
    X_GEN_TAC [[x:num]] THEN REWRITE_TAC [FORMSUBST_FV] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[y:num]]) MP_TAC) THEN
    REPEAT (COND_CASES_TAC THEN
           ASM_REWRITE_TAC [FVT, IN_INSERT, NOT_IN_EMPTY]) THEN
    ASM_MESON_TAC [(← ExceptT.mk (ARITH_RULE [[~(x + N < N)]])),
                  (← ExceptT.mk (ARITH_RULE [[y < 2 * N ==> y - N < N]]))])
  : ExceptT String IO thm).run
#eval RENAME_AWAY

#eval phrase 43
unsafe def rename : thm := keep "rename" fun _ => (do
  newSpec ["rename"]
    (← HolLight.REWRITE_RULE [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] RENAME_AWAY)
  : ExceptT String IO thm).run
#eval rename

#eval phrase 44
unsafe def resproof_triple : thm × thm × thm := keep "resproof_triple" fun _ =>
  newInductive
    [[(!cl. cl IN hyps ==> resproof hyps cl) /\
      (!cl1 cl2 cl2' ps1 ps2 i.
           resproof hyps cl1 /\ resproof hyps cl2 /\
           (IMAGE (formsubst (rename cl2 (FVS cl1))) cl2 = cl2') /\
           ps1 SUBSET cl1 /\ ps2 SUBSET cl2' /\ ~(ps1 = {}) /\ ~(ps2 = {}) /\
           (?i. Unifies i (ps1 UNION {~~p | p IN ps2})) /\
           (mgu (ps1 UNION {~~p | p IN ps2}) = i)
           ==> resproof hyps
                  (IMAGE (formsubst i) ((cl1 DIFF ps1) UNION (cl2' DIFF ps2))))]]
unsafe def resproof_RULES : thm := resproof_triple.1
unsafe def resproof_INDUCT : thm := resproof_triple.2.1
unsafe def resproof_CASES : thm := resproof_triple.2.2
#eval do IO.println resproof_RULES; IO.println resproof_INDUCT; IO.println resproof_CASES

#eval phrase 45
unsafe def PHOLDS_FORMSUBST : thm := keep "PHOLDS_FORMSUBST" fun _ => (do
  prove ([[!p i d. qfree(p)
           ==> (pholds d (formsubst i p) <=> pholds (d o formsubst i) p)]])
   (MATCH_MP_TAC form_INDUCTION THEN
    SIMP_TAC [o_THM, qfree, pholds, formsubst])
  : ExceptT String IO thm).run
#eval PHOLDS_FORMSUBST

#eval phrase 46
unsafe def QFREE_INTERP : thm := keep "QFREE_INTERP" fun _ => (do
  prove ([[!cl. clause cl ==> qfree(interp cl)]])
   (REWRITE_TAC [clause, interp] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[!p. MEM p (list_of_set cl) ==> qfree p]]) MP_TAC THENL
     [ASM_MESON_TAC [MEM_LIST_OF_SET, QFREE_LITERAL], ALL_TAC] THEN
    SPEC_TAC ([[list_of_set cl :form list]], [[l:form list]]) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [MEM, ITLIST, Or_DEF, qfree] THEN
    ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval QFREE_INTERP

#eval phrase 47
unsafe def PHOLDS_INTERP_IMAGE : thm := keep "PHOLDS_INTERP_IMAGE" fun _ => (do
  prove ([[!cl v d. clause cl
            ==> (pholds d (interp (IMAGE (formsubst v) cl)) <=>
                 pholds d (formsubst v (interp cl)))]])
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC oTIO HolLight.REWRITE_RULE [clause]) THEN
    ASM_SIMP_TAC [QFREE_INTERP, PHOLDS_FORMSUBST] THEN
    ASM_SIMP_TAC [PHOLDS_INTERP, QFREE_LITERAL, FINITE_IMAGE] THEN
    REWRITE_TAC [IN_IMAGE] THEN ASM_MESON_TAC [PHOLDS_FORMSUBST, QFREE_LITERAL])
  : ExceptT String IO thm).run
#eval PHOLDS_INTERP_IMAGE

#eval phrase 48
unsafe def IMAGE_FORMSUBST_CLAUSE : thm := keep "IMAGE_FORMSUBST_CLAUSE" fun _ => (do
  prove ([[!v cl. clause(cl) ==> clause(IMAGE (formsubst v) cl)]])
   (SIMP_TAC [clause, IN_IMAGE, FINITE_IMAGE] THEN
    MESON_TAC [FORMSUBST_LITERAL])
  : ExceptT String IO thm).run
#eval IMAGE_FORMSUBST_CLAUSE

#eval phrase 49
unsafe def INSTANCE_OF_EMPTY : thm := keep "INSTANCE_OF_EMPTY" fun _ => (do
  prove ([[!cl. {} instance_of cl ==> (cl = {})]])
   (REWRITE_TAC [instance_of, EXTENSION, NOT_IN_EMPTY, IN_IMAGE] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval INSTANCE_OF_EMPTY

#eval phrase 50
unsafe def RESPROOF_CLAUSE : thm := keep "RESPROOF_CLAUSE" fun _ => (do
  let lemma ← (do
    prove ([[s DIFF t SUBSET s]]) (SET_TAC [])
    : ExceptT String IO thm)
  prove ([[(!cl. cl IN hyps ==> clause cl)
   ==> !cl. resproof hyps cl ==> clause cl]])
   (DISCH_TAC THEN MATCH_MP_TAC resproof_INDUCT THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [clause, IMAGE_UNION, FINITE_UNION] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC [clause, FINITE_IMAGE, lemma, FINITE_SUBSET], ALL_TAC] THEN
    Fol.EXPAND_TAC "cl2'" THEN REWRITE_TAC [IN_IMAGE, IN_UNION, IN_DIFF] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC [FORMSUBST_LITERAL])
  : ExceptT String IO thm).run
#eval RESPROOF_CLAUSE

#eval phrase 51
unsafe def RESOLUTION_COMPLETE : thm := keep "RESOLUTION_COMPLETE" fun _ => (do
  prove ([[(!cl. cl IN hyps ==> clause cl) /\
   ~(?M:(term->bool)#(num->term list->term)#(num->term list->bool).
        interpretation (language(IMAGE interp hyps)) M /\ ~(Dom M = {}) /\
        M satisfies (IMAGE interp hyps))
   ==> resproof hyps {}]])
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
    SUBGOAL_THEN
      ([[!cl0. presproof {IMAGE (formsubst v) cl | cl,v | cl IN hyps} cl0
           ==> ?cl. resproof hyps cl /\ cl0 instance_of cl]])
    MP_TAC THENL
     [ALL_TAC,
      DISCH_THEN (MP_TAC o HolLight.SPEC [[{}:form->bool]]) THEN
      MATCH_MP_TAC (← ExceptT.mk (TAUT [[(b ==> c) ==> (a ==> b) ==> (a ==> c)]])) THEN
      MESON_TAC [INSTANCE_OF_EMPTY]] THEN
    MATCH_MP_TAC presproof_INDUCT THEN CONJ_TAC THENL
     [REWRITE_TAC [IN_IMAGE, instance_of, IN_ELIM_THM] THEN
      MESON_TAC [resproof_RULES], ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [ [[p:form]], [[A':form->bool]], [[B':form->bool]] ] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN ([[A:form->bool]]) STRIP_ASSUME_TAC)
                               MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN ([[B:form->bool]]) STRIP_ASSUME_TAC)
      STRIP_ASSUME_TAC) THEN
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
     [ASM_MESON_TAC [RESPROOF_CLAUSE],
      ASM_MESON_TAC [IMAGE_FORMSUBST_CLAUSE, RESPROOF_CLAUSE],
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
    DISCH_THEN (fun th => HolLight.tactic_of do
      let r ← liftExcept (HolCore.Kernel.rand (concl th))
      pure (ASSUME_TAC th THEN EXISTS_TAC r)) THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC (← liftExcept (Session.CONJUNCT2 (← ExceptT.mk (HolLight.SPEC_ALL resproof_RULES)))) THEN
    EXISTS_TAC [[B:form->bool]] THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval RESOLUTION_COMPLETE

#eval phrase 52
unsafe def isaresolvent : thm := keep "isaresolvent" fun _ => new_definition
  [[isaresolvent cl (cl1,cl2) <=>
        let cl2' = IMAGE (formsubst (rename cl2 (FVS cl1))) cl2 in
        ?ps1 ps2.
            ps1 SUBSET cl1 /\ ps2 SUBSET cl2' /\ ~(ps1 = {}) /\ ~(ps2 = {}) /\
            (?i. Unifies i (ps1 UNION {~~p | p IN ps2})) /\
            let i = mgu (ps1 UNION {~~p | p IN ps2}) in
            cl = IMAGE (formsubst i) ((cl1 DIFF ps1) UNION (cl2' DIFF ps2))]]
#eval isaresolvent

#eval phrase 53
unsafe def RESPROOF_RULES : thm := keep "RESPROOF_RULES" fun _ => (do
  prove ([[!hyps. (!cl. cl IN hyps ==> resproof hyps cl) /\
          (!cl1 cl2 cl.
                resproof hyps cl1 /\ resproof hyps cl2 /\
                isaresolvent cl (cl1,cl2)
                ==> resproof hyps cl)]])
   (REWRITE_TAC [isaresolvent] THEN
    CONV_TAC (HolLight.TOP_DEPTH_CONV Session.let_CONV) THEN
    REWRITE_TAC [resproof_RULES] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC (← liftExcept (Session.CONJUNCT2 (← ExceptT.mk (HolLight.SPEC_ALL resproof_RULES)))) THEN
    EXISTS_TAC [[cl2:form->bool]] THEN ASM_REWRITE_TAC [] THEN
    EXISTS_TAC [[i:num->term]] THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval RESPROOF_RULES

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py from the `#eval`s above. -/
unsafe def ensure : IO Unit := once "HolLogicArith.Resolution" do
  replay (
          HolLogicArith.Herbrand.ensure)
  replay (
          HolLogicArith.Unif.ensure)
  replay (
          atom)
  replay (
          literal)
  replay (
          clause)
  replay (
          LITERAL)
  replay (
          ATOM)
  replay (
          negative)
  replay (
          positive)
  replay (
          negate)
  replay (
          PHOLDS_NEGATE)
  replay (
          HOLDS_NEGATE)
  replay (
          NEGATE_NEG)
  replay (
          NEGATE_ATOM)
  replay (
          NEGATE_REFL)
  replay (
          PHOLDS_ATOM)
  replay (
          NEGATE_NEGATE)
  replay (
          resolve)
  replay (
          do IO.println presproof_RULES; IO.println presproof_INDUCT; IO.println presproof_CASES)
  replay (
          interp)
  replay (
          UNPSATISFIABLE_FINITE_SUBSET)
  replay (
          PRESPROOF_MONO)
  replay (
          PRESPROOF_TRANS)
  replay (
          IMAGE_CLAUSE)
  replay (
          PHOLDS_INTERP)
  replay (
          HOLDS_INTERP)
  replay (
          PRESPROOF_REFUTATION_COMPLETE_FINITE)
  replay (
          PRESPROOF_REFUTATION_COMPLETE)
  replay (
          parse_as_infix ("instance_of", (12, "right")))
  replay (
          instance_of)
  replay (
          FVS)
  replay (
          NEGATIVE_FORMSUBST)
  replay (
          FORMSUBST_NEGATE)
  replay (
          FORMSUBST_ATOM)
  replay (
          FORMSUBST_NOT)
  replay (
          NOT_NOT_ATOM)
  replay (
          FORMSUBST_LITERAL)
  replay (
          QFREE_NOT)
  replay (
          QFREE_ATOM)
  replay (
          QFREE_LITERAL)
  replay (
          QFREE_NEGATE)
  replay (
          LIFTING_LEMMA)
  replay (
          FVS_CLAUSE_FINITE)
  replay (
          RENAME_AWAY)
  replay (
          rename)
  replay (
          do IO.println resproof_RULES; IO.println resproof_INDUCT; IO.println resproof_CASES)
  replay (
          PHOLDS_FORMSUBST)
  replay (
          QFREE_INTERP)
  replay (
          PHOLDS_INTERP_IMAGE)
  replay (
          IMAGE_FORMSUBST_CLAUSE)
  replay (
          INSTANCE_OF_EMPTY)
  replay (
          RESPROOF_CLAUSE)
  replay (
          RESOLUTION_COMPLETE)
  replay (
          isaresolvent)
  replay (
          RESPROOF_RULES)
-- @@ENSURE END

end HolLogicArith.Resolution
