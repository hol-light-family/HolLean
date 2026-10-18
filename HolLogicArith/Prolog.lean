/- File: HolLogicArith/Prolog.lean
Translation of HOL Light's Logic/prolog.ml, phrase by phrase.
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

namespace HolLogicArith.Prolog

/- List definitions/theorems used below are exposed by Session as fields of
   the `listDefs`/`listThms1` bundles; alias the ones we need. -/
private unsafe def LENGTH : thm := Session.listDefs.LENGTH
private unsafe def MAP : thm := Session.listDefs.MAP
private unsafe def ITLIST : thm := Session.listDefs.ITLIST
private unsafe def MEM : thm := Session.listDefs.MEM
private unsafe def ALL : thm := Session.listDefs.ALL
private unsafe def MEM_MAP : thm := Session.listThms1.MEM_MAP
private unsafe def ALL2 : thm := Session.listDefs.ALL2
private unsafe def ALL_MEM : thm := Session.listThms1.ALL_MEM
private unsafe def ALL_IMP : thm := Session.listThms1.ALL_IMP
private unsafe def ALL_MAP : thm := Session.listThms1.ALL_MAP
private unsafe def ALL_T : thm := Session.listThms1.ALL_T
private unsafe def EX_MAP : thm := Session.listThms1.EX_MAP
private unsafe def EX_MEM : thm := Session.listThms1.EX_MEM
private unsafe def MAP_EQ : thm := Session.listThms1.MAP_EQ
private unsafe def MAP_EQ_DEGEN : thm := Session.listThms1.MAP_EQ_DEGEN
private unsafe def FORALL_ALL : thm := Session.listThms1.FORALL_ALL
private unsafe def LENGTH_EQ_NIL : thm := Session.listThms1.LENGTH_EQ_NIL

#eval HolLogicArith.Given.ensure

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

/- `INST_TYPE [`:term`,`:A`]` as a thm->thm action, for the `o MATCH_MP th`
   compositions below. -/
private unsafe def instTermForA (th : thm) : ExceptT String IO thm := do
  let tyterm ← ExceptT.mk (HolCore.Parser.parse_type "term")
  HolLight.INST_TYPE [(tyterm, mk_vartype "A")] th

#eval phrase 1
unsafe def SATISFIES_IMAGE : thm := keep "SATISFIES_IMAGE" fun _ => (do
  prove ([[M satisfies (IMAGE f s) <=>
   !x v. valuation(M) v /\ x IN s ==> holds M v (f x)]])
   (REWRITE_TAC [satisfies, IN_IMAGE] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval SATISFIES_IMAGE

#eval phrase 2
unsafe def definite : thm := keep "definite" fun _ => new_definition
  [[definite(cl) <=> clause(cl) /\ (CARD {p | p IN cl /\ positive p} = 1)]]
#eval definite

#eval phrase 3
unsafe def horn : thm := keep "horn" fun _ => new_definition
  [[horn(cl) <=> clause(cl) /\ CARD {p | p IN cl /\ positive p} <= 1]]
#eval horn

#eval phrase 4
unsafe def DEFINITE_IMP_HORN : thm := keep "DEFINITE_IMP_HORN" fun _ => (do
  prove ([[!cl. definite(cl) ==> horn(cl)]])
   (SIMP_TAC [definite, horn, LE_REFL])
  : ExceptT String IO thm).run
#eval DEFINITE_IMP_HORN

#eval phrase 5
unsafe def falsify : thm := keep "falsify" fun _ => new_definition
  [[falsify ff cl = if definite(cl) then cl else ff INSERT cl]]
#eval falsify

#eval phrase 6
unsafe def FALSIFY_FINITE : thm := keep "FALSIFY_FINITE" fun _ => (do
  prove ([[FINITE(cl) ==> FINITE(falsify ff cl)]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [falsify] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [FINITE_RULES])
  : ExceptT String IO thm).run
#eval FALSIFY_FINITE

#eval phrase 7
unsafe def FALSIFY_DEFINITE : thm := keep "FALSIFY_DEFINITE" fun _ => (do
  prove ([[horn(cl) ==> definite(falsify (Atom P args) cl)]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [falsify] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC [[~(definite cl)]] THEN
    REWRITE_TAC [horn, definite] THEN
    ASM_CASES_TAC [[clause cl]] THEN ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN ([[{p | p IN Atom P args INSERT cl /\ positive p} =
                (Atom P args) INSERT {p | p IN cl /\ positive p}]])
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_INSERT] THEN
      SUBGOAL_THEN ([[positive(Atom P args)]]) (fun th => MESON_TAC [th]) THEN
      REWRITE_TAC [positive, negative, ATOM] THEN
      REWRITE_TAC [Not_DEF, form_DISTINCT], ALL_TAC] THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC [clause, IN_INSERT, FINITE_INSERT] THEN
      ASM_MESON_TAC [clause, literal, ATOM], ALL_TAC] THEN
    SUBGOAL_THEN ([[FINITE {p | p IN cl /\ positive p}]]) ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC [[cl:form->bool]] THEN
      SIMP_TAC [SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC [clause], ALL_TAC] THEN
    ASM_SIMP_TAC [CARD_CLAUSES] THEN COND_CASES_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC (← ExceptT.mk (ARITH_RULE [[x <= 1 /\ ~(x = 1) ==> (SUC x = 1)]])) THEN
      ASM_REWRITE_TAC []] THEN
    UNDISCH_TAC [[Atom P args IN {p | p IN cl /\ positive p}]] THEN
    SUBGOAL_THEN ([[{p | p IN cl /\ positive p} = {}]])
     (fun th => REWRITE_TAC [th, NOT_IN_EMPTY]) THEN
    ONCE_REWRITE_TAC [(← HolLight.GSYM HAS_SIZE_0)] THEN ASM_REWRITE_TAC [HAS_SIZE] THEN
    MATCH_MP_TAC (← ExceptT.mk (ARITH_RULE [[x <= 1 /\ ~(x = 1) ==> (x = 0)]])) THEN
    ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval FALSIFY_DEFINITE

#eval phrase 8
unsafe def HOLDS_FALSIFY : thm := keep "HOLDS_FALSIFY" fun _ => (do
  prove ([[FINITE(cl) /\ holds M v (interp cl)
   ==> holds M v (interp(falsify ff cl))]])
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_SIMP_TAC [FALSIFY_FINITE, HOLDS_INTERP] THEN
    REWRITE_TAC [falsify] THEN COND_CASES_TAC THEN SIMP_TAC [IN_INSERT] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval HOLDS_FALSIFY

#eval phrase 9
unsafe def REDUCE_HORN_DEFINITE : thm := keep "REDUCE_HORN_DEFINITE" fun _ => (do
  prove ([[(!c. c IN s ==> clause c) /\
   ~((Atom ff []) IN UNIONS s) /\ ~(Not(Atom ff []) IN UNIONS s)
   ==> (~(satisfiable (U:A->bool) (IMAGE interp s)) <=>
        !M. ~(Dom M = {}) /\
            M satisfies (IMAGE interp (IMAGE (falsify (Atom ff [])) s))
            ==> !v:num->A. valuation(M) v ==> holds M v (Atom ff [])) ]])
   (REWRITE_TAC [satisfiable] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [NOT_EXISTS_THM, (← HolLight.GSYM IMAGE_o)] THEN
    REWRITE_TAC [SATISFIES_IMAGE] THEN EQ_TAC THENL
     [MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      ASM_CASES_TAC [[(Dom M):A->bool = {}]] THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [NOT_FORALL_THM] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [ [[cl:form->bool]], [[v:num->A]] ] THEN
      REWRITE_TAC [NOT_IMP] THEN STRIP_TAC THEN
      DISCH_THEN (MP_TAC o HolLight.SPECL [ [[cl:form->bool]], [[v:num->A]] ]) THEN
      ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [o_THM, falsify] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN ([[holds M (v:num->A) (interp (Atom ff [] INSERT cl)) <=>
                  holds M v (Atom ff []) \/ holds M v (interp cl)]])
      SUBST1_TAC THENL
       [SUBGOAL_THEN ([[FINITE (cl:form->bool)]]) ASSUME_TAC THENL
         [ASM_MESON_TAC [clause], ALL_TAC] THEN
        UNDISCH_TAC [[~(holds M (v:num->A) (interp cl))]] THEN
        ASM_SIMP_TAC [HOLDS_INTERP, FINITE_INSERT, IN_INSERT] THEN
        ASM_MESON_TAC [], ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (fun th => REPEAT STRIP_TAC THEN MP_TAC th) THEN
      MATCH_MP_TAC EQ_IMP THEN
      MATCH_MP_TAC HOLDS_VALUATION THEN
      REWRITE_TAC [FV, NOT_IN_EMPTY, MAP, LIST_UNION], ALL_TAC] THEN
    DISCH_THEN (fun th => GEN_TAC THEN DISCH_TAC THEN MP_TAC th) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC
     [[((Dom M):A->bool),Fun M,
      (\p args. if (p = ff) /\ (args = []) then F else Pred M p args)]]) THEN
    REWRITE_TAC [NOT_IMP] THEN CONJ_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [holds, Pred_DEF, MAP, NOT_FORALL_THM] THEN
      MATCH_MP_TAC VALUATION_EXISTS THEN ASM_REWRITE_TAC [Dom_DEF]] THEN
    ASM_REWRITE_TAC [Dom_DEF] THEN
    MAP_EVERY X_GEN_TAC [ [[cl:form->bool]], [[v:num->A]] ] THEN
    SUBGOAL_THEN
     ([[valuation(Dom M,Fun M,
           (\p args. if (p = ff) /\ (args = []) then F else Pred M p args)) v =
      valuation M (v:num->A)]])
    SUBST1_TAC THENL [REWRITE_TAC [valuation, Dom_DEF], ALL_TAC] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM (CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o HolLight.SPECL [ [[cl:form->bool]], [[v:num->A]] ])) THEN
    SUBGOAL_THEN ([[FINITE (cl:form->bool)]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [clause], ALL_TAC] THEN
    ASM_SIMP_TAC [o_THM, HOLDS_INTERP, FINITE_INSERT, IN_INSERT] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[p:form]]) STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC HOLDS_FALSIFY THEN ASM_REWRITE_TAC [] THEN
    ASM_SIMP_TAC [HOLDS_INTERP] THEN EXISTS_TAC [[p:form]] THEN
    ASM_REWRITE_TAC [] THEN
    UNDISCH_TAC [[holds M (v:num->A) p]] THEN
    MATCH_MP_TAC EQ_IMP THEN
    SPEC_TAC ([[v:num->A]], [[v:num->A]]) THEN
    MATCH_MP_TAC HOLDS_PREDICATES THEN
    REWRITE_TAC [Fun_DEF, Dom_DEF, Pred_DEF] THEN
    MAP_EVERY X_GEN_TAC [ [[r:num]], [[zs:(A)list]] ] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [LENGTH] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[~a ==> a ==> b]])) THEN
    SUBGOAL_THEN ([[~((Atom ff []) IN cl) /\ ~(Not(Atom ff []) IN cl)]]) MP_TAC THENL
     [UNDISCH_TAC [[~((Atom ff []) IN UNIONS s)]] THEN
      UNDISCH_TAC [[~(Not(Atom ff []) IN UNIONS s)]] THEN
      REWRITE_TAC [IN_UNIONS] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    REWRITE_TAC [(← ExceptT.mk (TAUT [[~a /\ ~b ==> ~c <=> c ==> a \/ b]]))] THEN
    SUBGOAL_THEN ([[literal p]]) MP_TAC THENL
     [ASM_MESON_TAC [clause], ALL_TAC] THEN
    REWRITE_TAC [literal, ATOM] THEN
    STRIP_TAC THEN UNDISCH_TAC [[p:form IN cl]] THEN
    ASM_REWRITE_TAC [predicates_form, IN_INSERT, NOT_IN_EMPTY, PAIR_EQ,
                    Not_DEF, IN_UNION, NOT_IN_EMPTY] THEN
    MESON_TAC [LENGTH_EQ_NIL])
  : ExceptT String IO thm).run
#eval REDUCE_HORN_DEFINITE

#eval phrase 10
unsafe def minmodel : thm := keep "minmodel" fun _ => new_definition
  [[minmodel s =
     herbase(functions s),
     Fn,
     (\p zs. !H. (Dom(H) = herbase(functions s)) /\
                 (Fun(H) = Fn) /\
                 H satisfies s
                 ==> Pred(H) p zs)]]
#eval minmodel

#eval phrase 11
unsafe def MINMODEL_MINIMAL : thm := keep "MINMODEL_MINIMAL" fun _ => (do
  prove ([[!p v s.
        atom p
        ==> (holds (minmodel s) v p <=>
             !H. (Dom(H) = herbase(functions s)) /\
                 (Fun(H) = Fn) /\ H satisfies s
                 ==> holds H v p)]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [ATOM, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[p:num]], [[args:term list]] ] THEN
    DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC [holds, minmodel, Pred_DEF, Fun_DEF] THEN
    AP_TERM_TAC THEN HolLight.GEN_REWRITE_TAC HolCore.Lib.I [FUN_EQ_THM] THEN
    X_GEN_TAC
     [[H:(term->bool)#((num->((term)list->term))#(num->((term)list->bool)))]] THEN
    REWRITE_TAC [] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[(a ==> (b <=> c)) ==> ((a ==> b) <=> (a ==> c))]])) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     ([[termval
      (herbase (functions s),
       Fn,
       (\p zs.
            !H. (Dom H = herbase (functions s)) /\ (Fun H = Fn) /\ H satisfies s
                ==> Pred H p zs)) =
      termval H]])
     (fun th => REWRITE_TAC [th]) THEN
    HolLight.GEN_REWRITE_TAC HolCore.Lib.I [FUN_EQ_THM] THEN X_GEN_TAC [[v:num->term]] THEN
    HolLight.GEN_REWRITE_TAC HolCore.Lib.I [FUN_EQ_THM] THEN X_GEN_TAC [[t:term]] THEN
    SPEC_TAC ([[v:num->term]], [[v:num->term]]) THEN
    MATCH_MP_TAC TERMVAL_FUNCTIONS THEN ASM_REWRITE_TAC [Fun_DEF])
  : ExceptT String IO thm).run
#eval MINMODEL_MINIMAL

#eval phrase 12
unsafe def HOLDS_ITLIST_IMP : thm := keep "HOLDS_ITLIST_IMP" fun _ => (do
  prove ([[!M v asm c.
        holds M v (ITLIST (-->) asm c) <=>
        (?p. MEM p asm /\ ~(holds M v p)) \/ holds M v c]])
   (GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN GEN_TAC THEN
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MEM, ITLIST, HOLDS] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval HOLDS_ITLIST_IMP

#eval phrase 13
unsafe def breakhorn : thm := keep "breakhorn" fun _ => new_definition
  [[breakhorn(cl) =
        if definite cl then
          let p = @p. p IN cl /\ positive p in
          MAP (~~) (list_of_set(cl DELETE p)),p
        else MAP (~~) (list_of_set cl),False]]
#eval breakhorn

#eval phrase 14
unsafe def hypotheses : thm := keep "hypotheses" fun _ => new_definition
  [[hypotheses cl = FST(breakhorn cl)]]
#eval hypotheses

#eval phrase 15
unsafe def conclusion : thm := keep "conclusion" fun _ => new_definition
  [[conclusion cl = SND(breakhorn cl)]]
#eval conclusion

#eval phrase 16
unsafe def HOLDS_HORN : thm := keep "HOLDS_HORN" fun _ => (do
  prove ([[!cl. horn(cl)
        ==> ALL atom (hypotheses cl) /\
            (if definite(cl) then atom(conclusion cl)
             else (conclusion cl = False)) /\
            !M (v:num->A).
                holds M v (interp cl) <=>
                holds M v (ITLIST (-->) (hypotheses cl) (conclusion cl))]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [horn] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (DISJ_CASES_TAC oTIO HolLight.MATCH_MP (← ExceptT.mk (ARITH_RULE
     [[x <= 1 ==> (x = 0) \/ (x = 1)]]))) THEN
    ASM_REWRITE_TAC [definite, ARITH, conclusion, hypotheses, breakhorn] THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN ([[ALL (\p. literal p /\ negative p) (list_of_set cl)]])
        MP_TAC THENL
         [RULE_ASSUM_TAC (HolLight.REWRITE_RULE [clause]) THEN
          ASM_SIMP_TAC [(← HolLight.GSYM ALL_MEM), MEM_LIST_OF_SET] THEN
          SUBGOAL_THEN ([[{p | p IN cl /\ positive p} = {}]]) MP_TAC THENL
           [ONCE_REWRITE_TAC [(← HolLight.GSYM HAS_SIZE_0)] THEN
            ASM_REWRITE_TAC [HAS_SIZE] THEN MATCH_MP_TAC FINITE_SUBSET THEN
            EXISTS_TAC [[cl:form->bool]] THEN ASM_REWRITE_TAC [] THEN
            SIMP_TAC [SUBSET, IN_ELIM_THM],
            REWRITE_TAC [EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY] THEN
            MESON_TAC [positive]],
          REWRITE_TAC [ALL_MAP] THEN MATCH_MP_TAC (← HolLight.ONCE_REWRITE_RULE
           [IMP_CONJ] ALL_IMP) THEN
          SIMP_TAC [o_THM, negate] THEN X_GEN_TAC [[p:form]] THEN STRIP_TAC THEN
          FIRST_X_ASSUM (X_CHOOSE_THEN ([[q:form]]) SUBST_ALL_TAC oTIO
                        HolLight.GEN_REWRITE_RULE HolCore.Lib.I [negative]) THEN
          REWRITE_TAC [Not_DEF, form_INJ] THEN
          UNDISCH_TAC [[literal (Not q)]] THEN
          SIMP_TAC [literal, ATOM, Not_DEF, form_DISTINCT, form_INJ] THEN
          MESON_TAC []],
        REPEAT GEN_TAC THEN REWRITE_TAC [interp] THEN
        SPEC_TAC ([[list_of_set(cl:form->bool)]], [[l:form list]]) THEN
        LIST_INDUCT_TAC THEN
        ASM_REWRITE_TAC [ITLIST, HOLDS, MAP, HOLDS_NEGATE] THEN
        CONV_TAC TAUT], ALL_TAC] THEN
    SUBGOAL_THEN ([[FINITE {p | p IN cl /\ positive p}]]) ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC [[cl:form->bool]] THEN
      SIMP_TAC [SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC [clause], ALL_TAC] THEN
    SUBGOAL_THEN ([[{p | p IN cl /\ positive p} HAS_SIZE (SUC 0)]]) MP_TAC THENL
     [ASM_REWRITE_TAC [ARITH, HAS_SIZE], ALL_TAC] THEN
    REWRITE_TAC [HAS_SIZE_SUC] THEN STRIP_TAC THEN LET_TAC THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV Session.let_CONV) THEN
    SUBGOAL_THEN ([[p IN cl /\ positive p]]) STRIP_ASSUME_TAC THENL
     [Fol.EXPAND_TAC "p" THEN CONV_TAC (fun t => pure (SELECT_CONV t)) THEN
      UNDISCH_TAC [[~({p | p IN cl /\ positive p} = {})]] THEN
      REWRITE_TAC [EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY] THEN MESON_TAC [],
      ALL_TAC] THEN
    REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[p:form]]) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC [IN_ELIM_THM], ALL_TAC] THEN
    REWRITE_TAC [HAS_SIZE_0] THEN
    REWRITE_TAC [EXTENSION, IN_DELETE, IN_ELIM_THM, NOT_IN_EMPTY] THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN ([[ALL (\p. literal p /\ negative p)
                        (list_of_set(cl DELETE p))]])
      MP_TAC THENL
       [RULE_ASSUM_TAC (HolLight.REWRITE_RULE [clause]) THEN
        ASM_SIMP_TAC [(← HolLight.GSYM ALL_MEM), MEM_LIST_OF_SET, FINITE_DELETE] THEN
        SUBGOAL_THEN ([[!q. q IN (cl DELETE p) ==> literal q /\ ~(positive q)]])
         (fun th => MESON_TAC [th, positive]) THEN
        REWRITE_TAC [IN_DELETE] THEN ASM_MESON_TAC [], ALL_TAC] THEN
      REWRITE_TAC [ALL_MAP] THEN MATCH_MP_TAC (← HolLight.ONCE_REWRITE_RULE
       [IMP_CONJ] ALL_IMP) THEN
      SIMP_TAC [o_THM, negate] THEN X_GEN_TAC [[r:form]] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (X_CHOOSE_THEN ([[q:form]]) SUBST_ALL_TAC oTIO
                    HolLight.GEN_REWRITE_RULE HolCore.Lib.I [negative]) THEN
      REWRITE_TAC [Not_DEF, form_INJ] THEN
      UNDISCH_TAC [[literal (Not q)]] THEN
      SIMP_TAC [literal, ATOM, Not_DEF, form_DISTINCT, form_INJ] THEN
      MESON_TAC [], ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN ([[literal p]]) MP_TAC THENL
       [ASM_MESON_TAC [clause], ALL_TAC] THEN
      REWRITE_TAC [literal] THEN STRIP_TAC THEN
      UNDISCH_TAC [[positive p]] THEN ASM_REWRITE_TAC [positive, negative] THEN
      REWRITE_TAC [Not_DEF, form_INJ, (← HolLight.GSYM EXISTS_REFL)], ALL_TAC] THEN
    REPEAT GEN_TAC THEN RULE_ASSUM_TAC (HolLight.REWRITE_RULE [clause]) THEN
    ASM_SIMP_TAC [HOLDS_INTERP] THEN
    REWRITE_TAC [HOLDS_ITLIST_IMP, MEM_MAP] THEN
    ASM_SIMP_TAC [MEM_LIST_OF_SET, FINITE_DELETE] THEN
    REWRITE_TAC [IN_DELETE] THEN ASM_MESON_TAC [HOLDS_NEGATE])
  : ExceptT String IO thm).run
#eval HOLDS_HORN

#eval phrase 17
unsafe def MINMODEL_MODEL : thm := keep "MINMODEL_MODEL" fun _ => (do
  prove ([[(!cl. cl IN s ==> definite(cl))
   ==> minmodel(IMAGE interp s) satisfies (IMAGE interp s)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [satisfies] THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    REWRITE_TAC [IMP_CONJ_ALT, RIGHT_FORALL_IMP_THM] THEN
    GEN_TAC THEN REWRITE_TAC [IN_IMAGE] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[cl:form->bool]]) MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    SUBGOAL_THEN ([[definite cl]]) ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN ([[horn cl]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [DEFINITE_IMP_HORN], ALL_TAC] THEN
    FIRST_ASSUM (MP_TAC o instTermForA oTIO HolLight.MATCH_MP HOLDS_HORN) THEN
    MAP_EVERY ABBREV_TAC [ [[asm = hypotheses cl]], [[c = conclusion cl]] ] THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC [[v:num->term]] THEN DISCH_TAC THEN
    REWRITE_TAC [HOLDS_ITLIST_IMP] THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (TAUT [[a \/ b <=> ~a ==> b]]))] THEN
    REWRITE_TAC [NOT_EXISTS_THM] THEN
    REWRITE_TAC [(← ExceptT.mk (TAUT [[~(a /\ ~b) <=> a ==> b]]))] THEN
    REWRITE_TAC [ALL_MEM] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV (fun t => pure (ETA_CONV t))) THEN
    ASM_SIMP_TAC [MINMODEL_MINIMAL] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     ([[ALL (\c. !H. (Dom H = herbase (functions (IMAGE interp s))) /\
                   (Fun H = Fn) /\
                   H satisfies IMAGE interp s
                   ==> holds H v c) asm]])
    MP_TAC THENL
     [MATCH_MP_TAC ALL_IMP THEN
      EXISTS_TAC [[holds (minmodel (IMAGE interp s)) v]] THEN
      ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC [ALL_MEM, MINMODEL_MINIMAL], ALL_TAC] THEN
    REWRITE_TAC [(← HolLight.GSYM FORALL_ALL)] THEN
    MATCH_MP_TAC MONO_FORALL THEN
    X_GEN_TAC
     [[H:(term->bool)#((num->((term)list->term))#(num->((term)list->bool)))]] THEN
    DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN ([[holds H (v:num->term) (ITLIST (-->) asm c)]]) MP_TAC THENL
     [FIRST_ASSUM (fun th => HolLight.tactic_of do
        let g ← HolLight.GSYM th
        pure (HolLight.GEN_REWRITE_TAC HolCore.Lib.I [g])) THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [satisfies, IN_IMAGE]) THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
      UNDISCH_TAC [[valuation (minmodel (IMAGE interp s)) v]] THEN
      ASM_REWRITE_TAC [valuation, Dom_DEF, minmodel], ALL_TAC] THEN
    REWRITE_TAC [HOLDS_ITLIST_IMP] THEN REWRITE_TAC [(← HolLight.GSYM ALL_MEM)] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval MINMODEL_MODEL

#eval phrase 18
unsafe def CONCLUSION_DEFINITE : thm := keep "CONCLUSION_DEFINITE" fun _ => (do
  prove ([[!cl p. definite cl /\ p IN cl /\ positive p
          ==> (conclusion cl = p)]])
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [conclusion, breakhorn] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV Session.let_CONV) THEN REWRITE_TAC [SND] THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC [[q:form]] THEN
    REWRITE_TAC [] THEN EQ_TAC THEN ASM_SIMP_TAC [] THEN STRIP_TAC THEN
    UNDISCH_TAC [[definite cl]] THEN REWRITE_TAC [definite] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (TAUT [[a ==> b <=> ~b ==> ~a]]))] THEN DISCH_TAC THEN
    MATCH_MP_TAC (← ExceptT.mk (ARITH_RULE [[2 <= a ==> ~(a = 1)]])) THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC [[CARD {p, (q:form)}]] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC [CARD_CLAUSES, FINITE_RULES, IN_SING, NOT_IN_EMPTY, ARITH],
      ALL_TAC] THEN
    MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
     [REWRITE_TAC [SUBSET, IN_ELIM_THM, IN_INSERT, NOT_IN_EMPTY] THEN
      ASM_MESON_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC [[cl:form->bool]] THEN
    SIMP_TAC [SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC [clause])
  : ExceptT String IO thm).run
#eval CONCLUSION_DEFINITE

#eval phrase 19
unsafe def CONCLUSION_DEFINITE_ALT : thm := keep "CONCLUSION_DEFINITE_ALT" fun _ => (do
  prove ([[!cl p. clause cl /\ p IN cl /\ positive p /\
          (!q. q IN cl /\ ~(q = p) ==> negative q)
          ==> (conclusion cl = p)]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC CONCLUSION_DEFINITE THEN
    ASM_REWRITE_TAC [definite] THEN
    SUBGOAL_THEN ([[{p | p IN cl /\ positive p} = {p}]]) SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_SING] THEN
      ASM_MESON_TAC [positive],
      SIMP_TAC [CARD_CLAUSES, NOT_IN_EMPTY, FINITE_RULES, ARITH]])
  : ExceptT String IO thm).run
#eval CONCLUSION_DEFINITE_ALT

#eval phrase 20
unsafe def HYPOTHESES_CONCLUSION : thm := keep "HYPOTHESES_CONCLUSION" fun _ => (do
  prove ([[!cl. definite cl
        ==> (set_of_list(hypotheses cl) =
             IMAGE (~~) (cl DELETE (conclusion cl)))]])
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [hypotheses, breakhorn, conclusion] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV Session.let_CONV) THEN REWRITE_TAC [FST, SND] THEN
    REWRITE_TAC [IN_IMAGE, EXTENSION, IN_SET_OF_LIST, IN_DELETE] THEN
    REWRITE_TAC [MEM_MAP] THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [definite, clause]) THEN
    ASM_SIMP_TAC [MEM_LIST_OF_SET, FINITE_DELETE] THEN
    REWRITE_TAC [IN_DELETE] THEN REWRITE_TAC [CONJ_ACI])
  : ExceptT String IO thm).run
#eval HYPOTHESES_CONCLUSION

#eval phrase 21
unsafe def gbackchain_triple : thm × thm × thm := keep "gbackchain_triple" fun _ =>
  newInductive
    [[!cl i ns. cl IN s /\
               (!x. i(x) IN herbase(functions(IMAGE interp s))) /\
               ALL2 (gbackchain s) ns (MAP (formsubst i) (hypotheses cl))
               ==> gbackchain s (ITLIST (+) ns 1)
                                (formsubst i (conclusion cl))]]
unsafe def gbackchain_RULES : thm := gbackchain_triple.1
unsafe def gbackchain_INDUCT : thm := gbackchain_triple.2.1
unsafe def gbackchain_CASES : thm := gbackchain_triple.2.2
#eval do IO.println gbackchain_RULES; IO.println gbackchain_INDUCT; IO.println gbackchain_CASES

#eval phrase 22
unsafe def ALL2_TRIV : thm := keep "ALL2_TRIV" fun _ => (do
  prove ([[!l1 l2. ALL2 (\n. P) l1 l2 <=> (LENGTH l1 = LENGTH l2) /\ ALL P l2]])
   (LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [ALL2, ALL, LENGTH, NOT_SUC, SUC_INJ] THEN
    REWRITE_TAC [CONJ_ACI])
  : ExceptT String IO thm).run
#eval ALL2_TRIV

#eval phrase 23
unsafe def GBACKCHAIN_SOUND : thm := keep "GBACKCHAIN_SOUND" fun _ => (do
  prove ([[(!cl. cl IN s ==> definite(cl)) /\ valuation (minmodel (IMAGE interp s)) v
   ==> !n p. gbackchain s n p ==> holds (minmodel(IMAGE interp s)) v p]])
   (STRIP_TAC THEN MATCH_MP_TAC gbackchain_INDUCT THEN
    REWRITE_TAC [ALL2_TRIV] THEN
    MAP_EVERY X_GEN_TAC [ [[cl:form->bool]], [[i:num->term]], [[ns:num list]] ] THEN
    REWRITE_TAC [] THEN CONV_TAC (HolLight.ONCE_DEPTH_CONV (fun t => pure (ETA_CONV t))) THEN STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC oTIO HolLight.MATCH_MP MINMODEL_MODEL) THEN
    REWRITE_TAC [satisfies] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC
     [[termval (minmodel (IMAGE interp s)) (v:num->term) o (i:num->term)]]) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[interp cl]]) THEN ANTS_TAC THENL
     [ALL_TAC,
      SUBGOAL_THEN ([[horn cl]]) MP_TAC THENL
       [ASM_MESON_TAC [DEFINITE_IMP_HORN], ALL_TAC] THEN
      DISCH_THEN (MP_TAC o instTermForA oTIO HolLight.MATCH_MP HOLDS_HORN) THEN
      ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [HOLDS_ITLIST_IMP] THEN
      REWRITE_TAC [(← HolLight.GSYM HOLDS_FORMSUBST)] THEN
      UNDISCH_TAC [[ALL (holds (minmodel (IMAGE interp s)) v)
                       (MAP (formsubst i) (hypotheses cl))]] THEN
      REWRITE_TAC [ALL_MAP] THEN REWRITE_TAC [(← HolLight.GSYM ALL_MEM)] THEN
      REWRITE_TAC [o_THM] THEN MESON_TAC []] THEN
    CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [IN_IMAGE]] THEN
    REWRITE_TAC [valuation, o_THM] THEN X_GEN_TAC [[x:num]] THEN
    SUBGOAL_THEN ([[i(x:num) IN herbase (functions (IMAGE interp s))]]) MP_TAC THENL
     [ASM_REWRITE_TAC [], ALL_TAC] THEN
    SPEC_TAC ([[(i:num->term) x]], [[t:term]]) THEN
    GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC INTERPRETATION_TERMVAL THEN
    HolCore.Lib.W (fun g => HolLight.tactic_of do
      let (v, _) ← liftExcept (HolCore.Basics.dest_exists (HolLight.snd g))
      pure (EXISTS_TAC v)) THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN
     ([[interpretation (functions(IMAGE interp s),predicates(IMAGE interp s))
                     (minmodel (IMAGE interp s))]])
    MP_TAC THENL
     [MATCH_MP_TAC HERBRAND_INTERPRETATION THEN
      REWRITE_TAC [herbrand, minmodel, Dom_DEF, Fun_DEF], ALL_TAC] THEN
    MATCH_MP_TAC INTERPRETATION_SUBLANGUAGE THEN
    ASM_SIMP_TAC [HERBASE_FUNCTIONS])
  : ExceptT String IO thm).run
#eval GBACKCHAIN_SOUND

#eval phrase 24
unsafe def GBACKCHAIN_COMPLETE : thm := keep "GBACKCHAIN_COMPLETE" fun _ => (do
  prove ([[(!cl. cl IN s ==> definite(cl)) /\
   atom(p) /\ (FV p = {}) /\ (!v. holds (minmodel (IMAGE interp s)) v p)
   ==> ?n. gbackchain s n p]])
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    FIRST_ASSUM (fun th => HolLight.tactic_of do
      let t ← HolLight.MATCH_MP MINMODEL_MINIMAL th
      pure (REWRITE_TAC [t])) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[v:num->term]]) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC
     [[herbase(functions(IMAGE interp s)),Fn,
      (\p tms. ?n. gbackchain s n (Atom p tms))]]) THEN
    REWRITE_TAC [Dom_DEF, Fun_DEF] THEN
    FIRST_ASSUM (X_CHOOSE_THEN ([[P:num]]) MP_TAC oTIO HolLight.GEN_REWRITE_RULE HolCore.Lib.I [ATOM]) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[tms:term list]]) SUBST_ALL_TAC) THEN
    REWRITE_TAC [holds, Pred_DEF] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[(b <=> c) /\ a ==> (a ==> b) ==> c]])) THEN CONJ_TAC THENL
     [AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
      AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ_DEGEN THEN
      UNDISCH_TAC [[FV(Atom P tms) = {}]] THEN
      REWRITE_TAC [EXTENSION, NOT_IN_EMPTY, FV, IN_LIST_UNION] THEN
      REWRITE_TAC [EX_MAP] THEN REWRITE_TAC [(← HolLight.GSYM ALL_MEM), (← HolLight.GSYM EX_MEM)] THEN
      REWRITE_TAC [o_THM, NOT_EXISTS_THM] THEN DISCH_TAC THEN
      X_GEN_TAC [[t:term]] THEN DISCH_TAC THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC [[termval(herbase (functions (IMAGE interp s)),
                          Fn,(\p tms. ?n. gbackchain s n (Atom p tms))) V t]] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC TERMVAL_VALUATION THEN ASM_MESON_TAC [], ALL_TAC] THEN
      SPEC_TAC ([[t:term]], [[t:term]]) THEN MATCH_MP_TAC TERMVAL_TRIV THEN
      REWRITE_TAC [Fun_DEF], ALL_TAC] THEN
    REWRITE_TAC [satisfies] THEN REPEAT GEN_TAC THEN
    REWRITE_TAC [valuation, Dom_DEF] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN REWRITE_TAC [IN_IMAGE] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[cl:form->bool]])
          (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN ([[horn cl]]) MP_TAC THENL
     [ASM_MESON_TAC [DEFINITE_IMP_HORN], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o instTermForA oTIO HolLight.MATCH_MP HOLDS_HORN) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [HOLDS_ITLIST_IMP] THEN
    REWRITE_TAC [(← ExceptT.mk (TAUT [[a \/ b <=> ~a ==> b]])), NOT_EXISTS_THM] THEN
    REWRITE_TAC [(← ExceptT.mk (TAUT [[~(a /\ ~b) <=> a ==> b]]))] THEN
    REWRITE_TAC [ALL_MEM] THEN CONV_TAC (HolLight.ONCE_DEPTH_CONV (fun t => pure (ETA_CONV t))) THEN
    ABBREV_TAC [[gbmod = herbase (functions (IMAGE interp s)),
                        Fn,
                        (\p tms. ?n. gbackchain s n (Atom p tms))]] THEN
    SUBGOAL_THEN
     ([[!p. atom p ==> (holds gbmod v p <=>
                      ?n. gbackchain s n (formsubst v p))]])
    ASSUME_TAC THENL
     [SIMP_TAC [ATOM, LEFT_IMP_EXISTS_THM] THEN
      Fol.EXPAND_TAC "gbmod" THEN REWRITE_TAC [HOLDS] THEN
      REWRITE_TAC [Pred_DEF, formsubst] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
      AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
      AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ THEN
      REWRITE_TAC [(← HolLight.GSYM ALL_MEM)] THEN
      X_GEN_TAC [[t:term]] THEN DISCH_TAC THEN
      CONV_TAC HolLight.SYM_CONV THEN
      SPEC_TAC ([[t:term]], [[t:term]]) THEN SPEC_TAC ([[v:num->term]], [[v:num->term]]) THEN
      MATCH_MP_TAC TERMSUBST_TERMVAL THEN REWRITE_TAC [Fun_DEF], ALL_TAC] THEN
    SUBGOAL_THEN
     ([[holds gbmod v (conclusion cl) <=>
      ?n. gbackchain s n (formsubst v (conclusion cl))]])
    SUBST1_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        let _ ← liftExcept (HolCore.Lib.check (fun t => HolCore.Classic.is_cond t) (concl th))
        pure (MP_TAC th)) THEN
      COND_CASES_TAC THEN REWRITE_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN
     ([[ALL (holds gbmod v) (hypotheses cl) <=>
      ALL (\p. ?n. gbackchain s n (formsubst v p)) (hypotheses cl)]])
    SUBST1_TAC THENL
     [UNDISCH_TAC [[ALL atom (hypotheses cl)]] THEN
      REWRITE_TAC [(← HolLight.GSYM ALL_MEM)] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[!b. (a ==> b) /\ (b ==> c) ==> a ==> c]])) THEN EXISTS_TAC
     [[?ns. ALL2 (gbackchain s) ns (MAP (formsubst v) (hypotheses cl))]] THEN
    CONJ_TAC THENL
     [SPEC_TAC ([[hypotheses cl]], [[l:form list]]) THEN
      POP_ASSUM_LIST (HolCore.Lib.K ALL_TAC) THEN LIST_INDUCT_TAC THEN
      REWRITE_TAC [ALL, MAP] THENL
       [EXISTS_TAC [[[]:num list]] THEN REWRITE_TAC [ALL2], ALL_TAC] THEN
      DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC ([[n:num]])) ASSUME_TAC) THEN
      FIRST_ASSUM (fun th => HolLight.tactic_of do
        let t ← liftExcept (HolCore.Lib.check (fun u => HolCore.Basics.is_imp u) (concl th))
        pure (UNDISCH_TAC t)) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC ([[ns:num list]])) THEN
      EXISTS_TAC [[CONS (n:num) ns]] THEN ASM_REWRITE_TAC [ALL2], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_TAC ([[ns:num list]])) THEN
    EXISTS_TAC [[ITLIST (+) ns 1]] THEN
    MATCH_MP_TAC gbackchain_RULES THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval GBACKCHAIN_COMPLETE

#eval phrase 25
unsafe def GBACKCHAIN_MINIMAL : thm := keep "GBACKCHAIN_MINIMAL" fun _ => (do
  prove ([[!s p. (!cl. cl IN s ==> definite cl) /\ atom p /\ (FV p = {})
         ==> !v. holds (minmodel (IMAGE interp s)) v p <=> ?n. gbackchain s n p]])
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN MATCH_MP_TAC GBACKCHAIN_COMPLETE THEN
      ASM_REWRITE_TAC [] THEN GEN_TAC THEN
      ASM_SIMP_TAC [HOLDS_VALUATION, NOT_IN_EMPTY],
      DISCH_TAC THEN
      SUBGOAL_THEN ([[?w. valuation (minmodel (IMAGE interp s)) w]])
        (X_CHOOSE_TAC ([[w:num->term]]))
      THENL
       [MATCH_MP_TAC VALUATION_EXISTS THEN
        MATCH_MP_TAC HERBRAND_NONEMPTY THEN
        REWRITE_TAC [herbrand, minmodel, Dom_DEF, Fun_DEF] THEN
        EXISTS_TAC [[functions(IMAGE interp s),predicates summat]] THEN
        REWRITE_TAC [FST], ALL_TAC] THEN
      SUBGOAL_THEN ([[holds (minmodel (IMAGE interp s)) w p]]) MP_TAC THENL
       [UNDISCH_TAC [[?n. gbackchain s n p]] THEN
        REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
        SPEC_TAC ([[p:form]], [[p:form]]) THEN
        ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
        MATCH_MP_TAC GBACKCHAIN_SOUND THEN
        ASM_REWRITE_TAC [], ALL_TAC] THEN
      ASM_SIMP_TAC [HOLDS_VALUATION, NOT_IN_EMPTY]])
  : ExceptT String IO thm).run
#eval GBACKCHAIN_MINIMAL

#eval phrase 26
unsafe def iminmodel : thm := keep "iminmodel" fun _ => new_definition
  [[iminmodel s =
     terms(functions s),
     Fn,
     (\p zs. !C. (Dom(C) = terms(functions s)) /\
                 (Fun(C) = Fn) /\
                 (!v p. p IN s /\ valuation C v ==> holds C v p)
                 ==> Pred(C) p zs)]]
#eval iminmodel

#eval phrase 27
unsafe def IMINMODEL_MINIMAL : thm := keep "IMINMODEL_MINIMAL" fun _ => (do
  prove ([[!p v s.
      atom p
      ==> (holds (iminmodel s) v p <=>
           !C. (Dom(C) = terms(functions s)) /\
               (Fun(C) = Fn) /\
               (!v q. q IN s /\ valuation C v ==> holds C v q)
               ==> holds C v p)]])
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [ATOM, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[p:num]], [[args:term list]] ] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    REWRITE_TAC [holds, iminmodel, Pred_DEF, Fun_DEF] THEN
    AP_TERM_TAC THEN HolLight.GEN_REWRITE_TAC HolCore.Lib.I [FUN_EQ_THM] THEN
    X_GEN_TAC
     [[C:(term->bool)#((num->((term)list->term))#(num->((term)list->bool)))]] THEN
    REWRITE_TAC [] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[(a ==> (b <=> c)) ==> ((a ==> b) <=> (a ==> c))]])) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     ([[termval
      (terms (functions s),
       Fn,
       (\p zs.
            !C. (Dom C = terms (functions s)) /\ (Fun C = Fn) /\
                (!v p. p IN s /\ valuation C v ==> holds C v p)
                ==> Pred C p zs)) =
      termval C]])
     (fun th => REWRITE_TAC [th]) THEN
    HolLight.GEN_REWRITE_TAC HolCore.Lib.I [FUN_EQ_THM] THEN X_GEN_TAC [[w:num->term]] THEN
    HolLight.GEN_REWRITE_TAC HolCore.Lib.I [FUN_EQ_THM] THEN X_GEN_TAC [[t:term]] THEN
    SPEC_TAC ([[w:num->term]], [[w:num->term]]) THEN
    MATCH_MP_TAC TERMVAL_FUNCTIONS THEN ASM_REWRITE_TAC [Fun_DEF])
  : ExceptT String IO thm).run
#eval IMINMODEL_MINIMAL

#eval phrase 28
unsafe def IMINMODEL_MODEL : thm := keep "IMINMODEL_MODEL" fun _ => (do
  prove ([[(!cl. cl IN s ==> definite(cl))
   ==> !v p. p IN s /\ (!x. v(x) IN terms(functions(IMAGE interp s)))
             ==> holds (iminmodel(IMAGE interp s)) v (interp p)]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    X_GEN_TAC [[cl:form->bool]] THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[definite cl]]) ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN ([[horn cl]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [DEFINITE_IMP_HORN], ALL_TAC] THEN
    FIRST_ASSUM (MP_TAC o instTermForA oTIO HolLight.MATCH_MP HOLDS_HORN) THEN
    MAP_EVERY ABBREV_TAC [ [[asm = hypotheses cl]], [[c = conclusion cl]] ] THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC [[v:num->term]] THEN DISCH_TAC THEN
    REWRITE_TAC [HOLDS_ITLIST_IMP] THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (TAUT [[a \/ b <=> ~a ==> b]]))] THEN
    REWRITE_TAC [NOT_EXISTS_THM] THEN
    REWRITE_TAC [(← ExceptT.mk (TAUT [[~(a /\ ~b) <=> a ==> b]]))] THEN
    REWRITE_TAC [ALL_MEM] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV (fun t => pure (ETA_CONV t))) THEN
    ASM_SIMP_TAC [IMINMODEL_MINIMAL] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     ([[ALL (\c. !C. (Dom C = terms (functions (IMAGE interp s))) /\
                   (Fun C = Fn) /\
                   (!v p. p IN (IMAGE interp s) /\ valuation C v ==> holds C v p)
                   ==> holds C v c) asm]])
    MP_TAC THENL
     [MATCH_MP_TAC ALL_IMP THEN
      EXISTS_TAC [[holds (iminmodel (IMAGE interp s)) v]] THEN
      ASM_REWRITE_TAC [] THEN
      X_GEN_TAC [[p:form]] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      SUBGOAL_THEN ([[atom p]])
       (fun th => HolLight.tactic_of do
          let t ← HolLight.MATCH_MP IMINMODEL_MINIMAL th
          pure (REWRITE_TAC [t])) THEN
      ASM_MESON_TAC [ALL_MEM], ALL_TAC] THEN
    REWRITE_TAC [(← HolLight.GSYM FORALL_ALL)] THEN
    MATCH_MP_TAC MONO_FORALL THEN
    X_GEN_TAC
     [[C:(term->bool)#((num->((term)list->term))#(num->((term)list->bool)))]] THEN
    DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN ([[holds C (v:num->term) (ITLIST (-->) asm c)]]) MP_TAC THENL
     [FIRST_ASSUM (fun th => HolLight.tactic_of do
        let g ← HolLight.GSYM th
        pure (HolLight.GEN_REWRITE_TAC HolCore.Lib.I [g])) THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [valuation, Dom_DEF] THEN ASM_MESON_TAC [IN_IMAGE], ALL_TAC] THEN
    REWRITE_TAC [HOLDS_ITLIST_IMP] THEN REWRITE_TAC [(← HolLight.GSYM ALL_MEM)] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval IMINMODEL_MODEL

#eval phrase 29
unsafe def IMINMODEL_INTERPRETATION : thm := keep "IMINMODEL_INTERPRETATION" fun _ => (do
  prove ([[!s. interpretation(language s) (iminmodel s)]])
   (GEN_TAC THEN REWRITE_TAC [interpretation, iminmodel, language, Dom_DEF] THEN
    REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC [Fun_DEF, IN] THEN CONV_TAC (HolLight.ONCE_DEPTH_CONV (fun t => pure (ETA_CONV t))) THEN
    ASM_SIMP_TAC [terms_RULES])
  : ExceptT String IO thm).run
#eval IMINMODEL_INTERPRETATION

#eval phrase 30
unsafe def ibackchain_triple : thm × thm × thm := keep "ibackchain_triple" fun _ =>
  newInductive
    [[!cl i ns. cl IN s /\ (!x. i(x) IN terms(functions(IMAGE interp s))) /\
               ALL2 (ibackchain s) ns (MAP (formsubst i) (hypotheses cl))
               ==> ibackchain s (ITLIST (+) ns 1)
                                (formsubst i (conclusion cl))]]
unsafe def ibackchain_RULES : thm := ibackchain_triple.1
unsafe def ibackchain_INDUCT : thm := ibackchain_triple.2.1
unsafe def ibackchain_CASES : thm := ibackchain_triple.2.2
#eval do IO.println ibackchain_RULES; IO.println ibackchain_INDUCT; IO.println ibackchain_CASES

#eval phrase 31
unsafe def IBACKCHAIN_SOUND : thm := keep "IBACKCHAIN_SOUND" fun _ => (do
  prove ([[(!cl. cl IN s ==> definite(cl))
   ==> !v n p. ibackchain s n p /\
               (!x. v(x) IN terms(functions(IMAGE interp s)))
               ==> holds (iminmodel(IMAGE interp s)) v p]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
    ONCE_REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC ibackchain_INDUCT THEN REWRITE_TAC [ALL2_TRIV] THEN
    MAP_EVERY X_GEN_TAC [ [[cl:form->bool]], [[i:num->term]], [[ns:num list]] ] THEN
    REWRITE_TAC [] THEN CONV_TAC (HolLight.ONCE_DEPTH_CONV (fun t => pure (ETA_CONV t))) THEN STRIP_TAC THEN
    DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC oTIO HolLight.MATCH_MP IMINMODEL_MODEL) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC
     [[termval (iminmodel (IMAGE interp s)) (v:num->term) o (i:num->term)]]) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[cl:form->bool]]) THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN ([[horn cl]]) MP_TAC THENL
     [ASM_MESON_TAC [DEFINITE_IMP_HORN], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o instTermForA oTIO HolLight.MATCH_MP HOLDS_HORN) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [HOLDS_ITLIST_IMP] THEN
    REWRITE_TAC [(← HolLight.GSYM HOLDS_FORMSUBST)] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[a /\ ~b ==> ((a ==> b \/ c) ==> c)]])) THEN CONJ_TAC THENL
     [X_GEN_TAC [[x:num]] THEN REWRITE_TAC [o_THM] THEN
      SUBGOAL_THEN ([[termval(iminmodel (IMAGE interp s)) v (i(x:num)) IN
                    Dom(iminmodel (IMAGE interp s))]])
      MP_TAC THENL [ALL_TAC, REWRITE_TAC [iminmodel, Dom_DEF]] THEN
      MATCH_MP_TAC INTERPRETATION_TERMVAL THEN
      EXISTS_TAC [[({}:(num#num)->bool)]] THEN CONJ_TAC THENL
       [MP_TAC (← HolLight.SPEC ([[IMAGE interp s]]) IMINMODEL_INTERPRETATION) THEN
        REWRITE_TAC [language] THEN MATCH_MP_TAC INTERPRETATION_SUBLANGUAGE THEN
        SUBGOAL_THEN ([[i(x:num) IN terms(FST(language(IMAGE interp s)))]])
        MP_TAC THENL [ASM_REWRITE_TAC [language, FST], ALL_TAC] THEN
        DISCH_THEN (MP_TAC oTIO HolLight.MATCH_MP STUPID_CANONDOM_LEMMA) THEN
        REWRITE_TAC [language, FST],
        ASM_REWRITE_TAC [valuation, iminmodel, Dom_DEF]],
      ALL_TAC] THEN
    UNDISCH_TAC [[ALL
         (\p. (!x. v x IN terms (functions (IMAGE interp s)))
              ==> holds (iminmodel (IMAGE interp s)) v p)
         (MAP (formsubst i) (hypotheses cl))]] THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [ALL_MAP] THEN REWRITE_TAC [(← HolLight.GSYM ALL_MEM)] THEN
    REWRITE_TAC [o_THM] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval IBACKCHAIN_SOUND

#eval phrase 32
unsafe def IBACKCHAIN_COMPLETE : thm := keep "IBACKCHAIN_COMPLETE" fun _ => (do
  prove ([[(!cl. cl IN s ==> definite(cl)) /\
   atom(p) /\
   (!v. (!x. v(x) IN terms(functions(IMAGE interp s)))
        ==> holds (iminmodel (IMAGE interp s)) v p)
   ==> ?n. ibackchain s n p]])
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    FIRST_ASSUM (fun th => HolLight.tactic_of do
      let t ← HolLight.MATCH_MP IMINMODEL_MINIMAL th
      pure (REWRITE_TAC [t])) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[V]]) THEN ANTS_TAC THENL
     [REWRITE_TAC [terms_RULES, IN], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC
     [[terms(functions(IMAGE interp s)),Fn,
      (\p tms. ?n. ibackchain s n (Atom p tms))]]) THEN
    REWRITE_TAC [Dom_DEF, Fun_DEF] THEN
    FIRST_ASSUM (X_CHOOSE_THEN ([[P:num]]) MP_TAC oTIO HolLight.GEN_REWRITE_RULE HolCore.Lib.I [ATOM]) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[tms:term list]]) SUBST_ALL_TAC) THEN
    REWRITE_TAC [holds, Pred_DEF] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[(b <=> c) /\ a ==> (a ==> b) ==> c]])) THEN CONJ_TAC THENL
     [AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
      AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ_DEGEN THEN
      REWRITE_TAC [(← HolLight.GSYM ALL_MEM), (← HolLight.GSYM EX_MEM)] THEN
      X_GEN_TAC [[t:term]] THEN DISCH_TAC THEN
      SPEC_TAC ([[t:term]], [[t:term]]) THEN MATCH_MP_TAC TERMVAL_TRIV THEN
      REWRITE_TAC [Fun_DEF], ALL_TAC] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [IN_IMAGE] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[cl:form->bool]])
          (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN ([[horn cl]]) MP_TAC THENL
     [ASM_MESON_TAC [DEFINITE_IMP_HORN], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o instTermForA oTIO HolLight.MATCH_MP HOLDS_HORN) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [HOLDS_ITLIST_IMP] THEN
    REWRITE_TAC [(← ExceptT.mk (TAUT [[a \/ b <=> ~a ==> b]])), NOT_EXISTS_THM] THEN
    REWRITE_TAC [(← ExceptT.mk (TAUT [[~(a /\ ~b) <=> a ==> b]]))] THEN
    REWRITE_TAC [ALL_MEM] THEN CONV_TAC (HolLight.ONCE_DEPTH_CONV (fun t => pure (ETA_CONV t))) THEN
    ABBREV_TAC [[gbmod = terms (functions (IMAGE interp s)),
                        Fn,
                        (\p tms. ?n. ibackchain s n (Atom p tms))]] THEN
    SUBGOAL_THEN
     ([[!p. atom p ==> (holds gbmod v p <=>
                      ?n. ibackchain s n (formsubst v p))]])
    ASSUME_TAC THENL
     [SIMP_TAC [ATOM, LEFT_IMP_EXISTS_THM] THEN
      Fol.EXPAND_TAC "gbmod" THEN REWRITE_TAC [HOLDS] THEN
      REWRITE_TAC [Pred_DEF, formsubst] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
      AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
      AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ THEN
      REWRITE_TAC [(← HolLight.GSYM ALL_MEM)] THEN
      X_GEN_TAC [[t:term]] THEN DISCH_TAC THEN
      CONV_TAC HolLight.SYM_CONV THEN
      SPEC_TAC ([[t:term]], [[t:term]]) THEN SPEC_TAC ([[v:num->term]], [[v:num->term]]) THEN
      MATCH_MP_TAC TERMSUBST_TERMVAL THEN REWRITE_TAC [Fun_DEF], ALL_TAC] THEN
    SUBGOAL_THEN
     ([[holds gbmod v (conclusion cl) <=>
      ?n. ibackchain s n (formsubst v (conclusion cl))]])
    SUBST1_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        let _ ← liftExcept (HolCore.Lib.check (fun t => HolCore.Classic.is_cond t) (concl th))
        pure (MP_TAC th)) THEN
      COND_CASES_TAC THEN REWRITE_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN
     ([[ALL (holds gbmod v) (hypotheses cl) <=>
      ALL (\p. ?n. ibackchain s n (formsubst v p)) (hypotheses cl)]])
    SUBST1_TAC THENL
     [UNDISCH_TAC [[ALL atom (hypotheses cl)]] THEN
      REWRITE_TAC [(← HolLight.GSYM ALL_MEM)] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[!b. (a ==> b) /\ (b ==> c) ==> a ==> c]])) THEN EXISTS_TAC
     [[?ns. ALL2 (ibackchain s) ns (MAP (formsubst v) (hypotheses cl))]] THEN
    CONJ_TAC THENL
     [SPEC_TAC ([[hypotheses cl]], [[l:form list]]) THEN
      POP_ASSUM_LIST (HolCore.Lib.K ALL_TAC) THEN LIST_INDUCT_TAC THEN
      REWRITE_TAC [ALL, MAP] THENL
       [EXISTS_TAC [[[]:num list]] THEN REWRITE_TAC [ALL2], ALL_TAC] THEN
      DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC ([[n:num]])) ASSUME_TAC) THEN
      FIRST_ASSUM (fun th => HolLight.tactic_of do
        let t ← liftExcept (HolCore.Lib.check (fun u => HolCore.Basics.is_imp u) (concl th))
        pure (UNDISCH_TAC t)) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC ([[ns:num list]])) THEN
      EXISTS_TAC [[CONS (n:num) ns]] THEN ASM_REWRITE_TAC [ALL2], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_TAC ([[ns:num list]])) THEN
    EXISTS_TAC [[ITLIST (+) ns 1]] THEN
    MATCH_MP_TAC ibackchain_RULES THEN ASM_REWRITE_TAC [] THEN
    UNDISCH_TAC [[valuation gbmod (v:num->term)]] THEN
    Fol.EXPAND_TAC "gbmod" THEN REWRITE_TAC [valuation, Dom_DEF])
  : ExceptT String IO thm).run
#eval IBACKCHAIN_COMPLETE

#eval phrase 33
unsafe def IBACKCHAIN_MINIMAL : thm := keep "IBACKCHAIN_MINIMAL" fun _ => (do
  prove ([[!s p. (!cl. cl IN s ==> definite cl) /\ atom p
         ==> ((!v. (!x. v(x) IN terms(functions(IMAGE interp s)))
                   ==> holds (iminmodel(IMAGE interp s)) v p) <=>
              ?n. ibackchain s n p)]])
   (MESON_TAC [IBACKCHAIN_SOUND, IBACKCHAIN_COMPLETE])
  : ExceptT String IO thm).run
#eval IBACKCHAIN_MINIMAL

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py from the `#eval`s above. -/
unsafe def ensure : IO Unit := once "HolLogicArith.Prolog" do
  replay (
          HolLogicArith.Given.ensure)
  replay (
          SATISFIES_IMAGE)
  replay (
          definite)
  replay (
          horn)
  replay (
          DEFINITE_IMP_HORN)
  replay (
          falsify)
  replay (
          FALSIFY_FINITE)
  replay (
          FALSIFY_DEFINITE)
  replay (
          HOLDS_FALSIFY)
  replay (
          REDUCE_HORN_DEFINITE)
  replay (
          minmodel)
  replay (
          MINMODEL_MINIMAL)
  replay (
          HOLDS_ITLIST_IMP)
  replay (
          breakhorn)
  replay (
          hypotheses)
  replay (
          conclusion)
  replay (
          HOLDS_HORN)
  replay (
          MINMODEL_MODEL)
  replay (
          CONCLUSION_DEFINITE)
  replay (
          CONCLUSION_DEFINITE_ALT)
  replay (
          HYPOTHESES_CONCLUSION)
  replay (
          do IO.println gbackchain_RULES; IO.println gbackchain_INDUCT; IO.println gbackchain_CASES)
  replay (
          ALL2_TRIV)
  replay (
          GBACKCHAIN_SOUND)
  replay (
          GBACKCHAIN_COMPLETE)
  replay (
          GBACKCHAIN_MINIMAL)
  replay (
          iminmodel)
  replay (
          IMINMODEL_MINIMAL)
  replay (
          IMINMODEL_MODEL)
  replay (
          IMINMODEL_INTERPRETATION)
  replay (
          do IO.println ibackchain_RULES; IO.println ibackchain_INDUCT; IO.println ibackchain_CASES)
  replay (
          IBACKCHAIN_SOUND)
  replay (
          IBACKCHAIN_COMPLETE)
  replay (
          IBACKCHAIN_MINIMAL)
-- @@ENSURE END

end HolLogicArith.Prolog
