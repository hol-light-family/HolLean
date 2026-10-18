/- File: HolLogicArith/Positive.lean
Translation of HOL Light's Logic/positive.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolLogicArith.Support
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

namespace HolLogicArith.Positive

/- List definitions/theorems used below are exposed by Session as fields of
   the `listDefs`/`listThms1`/`listThms2` bundles; alias the ones we need. -/
private unsafe def LENGTH : thm := Session.listDefs.LENGTH
private unsafe def MAP : thm := Session.listDefs.MAP
private unsafe def ITLIST : thm := Session.listDefs.ITLIST
private unsafe def ALL : thm := Session.listDefs.ALL
private unsafe def MEM : thm := Session.listDefs.MEM
private unsafe def MAP_o : thm := Session.listThms1.MAP_o
private unsafe def MAP_EQ : thm := Session.listThms1.MAP_EQ
private unsafe def MEM_MAP : thm := Session.listThms1.MEM_MAP
private unsafe def ALL_MEM : thm := Session.listThms1.ALL_MEM
private unsafe def EX_MEM : thm := Session.listThms1.EX_MEM
private unsafe def list_CASES : thm := Session.listThms1.list_CASES
private unsafe def LENGTH_EQ_NIL : thm := Session.listThms1.LENGTH_EQ_NIL

/- `RESOLVE_CLAUSE` and `NEGATE_LITERAL` are bound in both Linear and Support;
   OCaml uses the latest binding (support.ml's), so we do too. -/
private unsafe def RESOLVE_CLAUSE : thm := HolLogicArith.Support.RESOLVE_CLAUSE
private unsafe def NEGATE_LITERAL : thm := HolLogicArith.Support.NEGATE_LITERAL

#eval HolLogicArith.Support.ensure

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
unsafe def allpositive : thm := keep "allpositive" fun _ => new_definition
  [[allpositive cl <=> !p. p IN cl ==> positive p]]
#eval allpositive

#eval phrase 2
unsafe def NOT_NEGATIVE_ATOM : thm := keep "NOT_NEGATIVE_ATOM" fun _ => (do
  prove ([[!p a. ~(negative (Atom p a))]])
   (REWRITE_TAC [negative, Not_DEF, form_DISTINCT])
  : ExceptT String IO thm).run
#eval NOT_NEGATIVE_ATOM

#eval phrase 3
unsafe def NEGATIVE_NOT : thm := keep "NEGATIVE_NOT" fun _ => (do
  prove ([[!p. negative(Not p)]])
   (MESON_TAC [negative])
  : ExceptT String IO thm).run
#eval NEGATIVE_NOT

#eval phrase 4
unsafe def CLAUSE_FINITE : thm := keep "CLAUSE_FINITE" fun _ => (do
  prove ([[!c. clause c ==> FINITE c]])
   (SIMP_TAC [clause])
  : ExceptT String IO thm).run
#eval CLAUSE_FINITE

#eval phrase 5
unsafe def POSITIVE_LITERAL_ATOM : thm := keep "POSITIVE_LITERAL_ATOM" fun _ => (do
  prove ([[!p. literal(p) /\ positive(p) <=> atom(p)]])
   (REWRITE_TAC [literal, positive, negative] THEN
    MESON_TAC [Not_DEF, form_DISTINCT, ATOM])
  : ExceptT String IO thm).run
#eval POSITIVE_LITERAL_ATOM

#eval phrase 6
unsafe def PHOLDS_ATOM : thm := keep "PHOLDS_ATOM" fun _ => (do
  prove ([[!v p. atom(p) ==> (pholds v p <=> v p)]])
   (SIMP_TAC [ATOM, LEFT_IMP_EXISTS_THM, PHOLDS])
  : ExceptT String IO thm).run
#eval PHOLDS_ATOM

#eval phrase 7
unsafe def PHOLDS_ALLTRUE_POSLIT : thm := keep "PHOLDS_ALLTRUE_POSLIT" fun _ => (do
  prove ([[!p. literal p /\ positive p ==> pholds (\x. T) p]])
   (REWRITE_TAC [literal, ATOM, positive, negative] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [PHOLDS] THEN
    ASM_MESON_TAC [atom, Not_DEF, form_DISTINCT])
  : ExceptT String IO thm).run
#eval PHOLDS_ALLTRUE_POSLIT

#eval phrase 8
unsafe def PHOLDS_ALLFALSE_NEGLIT : thm := keep "PHOLDS_ALLFALSE_NEGLIT" fun _ => (do
  prove ([[!p. literal p /\ negative p ==> pholds (\x. F) p]])
   (REWRITE_TAC [literal, ATOM, positive, negative] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [PHOLDS] THEN
    ASM_MESON_TAC [atom, Not_DEF, form_DISTINCT])
  : ExceptT String IO thm).run
#eval PHOLDS_ALLFALSE_NEGLIT

#eval phrase 9
unsafe def PHOLDS_ALLTRUE_POSCLAUSE : thm := keep "PHOLDS_ALLTRUE_POSCLAUSE" fun _ => (do
  prove ([[!c. clause(c) /\ allpositive c /\ ~(c = {}) ==> pholds (\x. T) (interp c)]])
   (SIMP_TAC [clause, PHOLDS_INTERP, allpositive, EXTENSION, NOT_IN_EMPTY] THEN
    MESON_TAC [PHOLDS_ALLTRUE_POSLIT])
  : ExceptT String IO thm).run
#eval PHOLDS_ALLTRUE_POSCLAUSE

#eval phrase 10
unsafe def PHOLDS_ALLFALSE_NONPOSCLAUSE : thm := keep "PHOLDS_ALLFALSE_NONPOSCLAUSE" fun _ => (do
  prove ([[!c. clause(c) /\ ~allpositive c ==> pholds (\x. F) (interp c)]])
   (SIMP_TAC [clause, PHOLDS_INTERP, allpositive, EXTENSION, NOT_IN_EMPTY] THEN
    MESON_TAC [PHOLDS_ALLFALSE_NEGLIT, positive])
  : ExceptT String IO thm).run
#eval PHOLDS_ALLFALSE_NONPOSCLAUSE

#eval phrase 11
unsafe def PRESOLUTION_LEMMA : thm := keep "PRESOLUTION_LEMMA" fun _ => (do
  prove ([[!s. FINITE s /\ (!c. c IN s ==> clause c) /\
       ~psatisfiable (IMAGE interp s) /\ ~({} IN s)
       ==> ?c1 c2 p. c1 IN s /\ c2 IN s /\
                     (allpositive c1 \/ allpositive c2) /\
                     p IN c1 /\ ~~p IN c2 /\
                     ~((resolve p c1 c2) IN s)]])
   (REPEAT STRIP_TAC THEN
    ABBREV_TAC [[P = {c | c IN s /\ allpositive c}]] THEN
    ABBREV_TAC [[N = {c | c IN s /\ ~(allpositive c)}]] THEN
    SUBGOAL_THEN ([[~(P:(form->bool)->bool = {})]]) ASSUME_TAC THENL
     [Fol.EXPAND_TAC "P" THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
      REWRITE_TAC [NOT_IN_EMPTY, (← ExceptT.mk (TAUT [[~(a /\ b) <=> a ==> ~b]]))] THEN
      DISCH_TAC THEN
      UNDISCH_TAC [[~psatisfiable (IMAGE interp s)]] THEN
      REWRITE_TAC [psatisfiable] THEN EXISTS_TAC [[\p:form. F]] THEN
      ASM_SIMP_TAC [IN_IMAGE, LEFT_IMP_EXISTS_THM, PHOLDS_ALLFALSE_NONPOSCLAUSE],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[~(N:(form->bool)->bool = {})]]) ASSUME_TAC THENL
     [Fol.EXPAND_TAC "N" THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
      REWRITE_TAC [NOT_IN_EMPTY, (← ExceptT.mk (TAUT [[~(a /\ b) <=> a ==> ~b]]))] THEN
      DISCH_TAC THEN
      UNDISCH_TAC [[~psatisfiable (IMAGE interp s)]] THEN
      REWRITE_TAC [psatisfiable] THEN EXISTS_TAC [[\p:form. T]] THEN
      SIMP_TAC [IN_IMAGE, LEFT_IMP_EXISTS_THM] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC PHOLDS_ALLTRUE_POSCLAUSE THEN
      ASM_MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN ([[?n v. v psatisfies (IMAGE interp P) /\ v HAS_SIZE n]])
    MP_TAC THENL
     [EXISTS_TAC [[CARD((UNIONS P):form->bool)]] THEN
      EXISTS_TAC [[(UNIONS P):form->bool]] THEN
      REWRITE_TAC [HAS_SIZE] THEN CONJ_TAC THENL
       [REWRITE_TAC [psatisfies, IN_IMAGE, IN_UNIONS, LEFT_IMP_EXISTS_THM] THEN
        GEN_TAC THEN X_GEN_TAC [[c:form->bool]] THEN
        DISCH_THEN (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
        SUBGOAL_THEN ([[FINITE(c:form->bool)]]) ASSUME_TAC THENL
         [RULE_ASSUM_TAC (HolLight.REWRITE_RULE [EXTENSION, IN_ELIM_THM]) THEN
          ASM_MESON_TAC [clause], ALL_TAC] THEN
        ASM_SIMP_TAC [PHOLDS_INTERP] THEN
        SUBGOAL_THEN ([[~(c:form->bool = {})]]) MP_TAC THENL
         [RULE_ASSUM_TAC (HolLight.REWRITE_RULE [EXTENSION, IN_ELIM_THM]) THEN
          ASM_MESON_TAC [], ALL_TAC] THEN
        REWRITE_TAC [EXTENSION, NOT_IN_EMPTY, NOT_FORALL_THM] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[q:form]] THEN DISCH_TAC THEN
        ASM_REWRITE_TAC [] THEN
        SUBGOAL_THEN ([[positive q]]) ASSUME_TAC THENL
         [RULE_ASSUM_TAC (HolLight.REWRITE_RULE [EXTENSION, IN_ELIM_THM]) THEN
          ASM_MESON_TAC [allpositive], ALL_TAC] THEN
        SUBGOAL_THEN ([[atom q]]) MP_TAC THENL
         [RULE_ASSUM_TAC (HolLight.REWRITE_RULE [EXTENSION, IN_ELIM_THM]) THEN
          ASM_MESON_TAC [clause, literal, positive, negative], ALL_TAC] THEN
        SIMP_TAC [ATOM, LEFT_IMP_EXISTS_THM, PHOLDS] THEN
        REPEAT GEN_TAC THEN DISCH_THEN (SUBST1_TAC oTIO HolLight.SYM) THEN
        HolLight.GEN_REWRITE_TAC HolCore.Lib.I [(← HolLight.GSYM IN)] THEN REWRITE_TAC [IN_UNIONS] THEN
        ASM_MESON_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[FINITE(P:(form->bool)->bool)]]) MP_TAC THENL
       [Fol.EXPAND_TAC "P" THEN MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC [[s:(form->bool)->bool]] THEN
        ASM_SIMP_TAC [SUBSET, IN_ELIM_THM], ALL_TAC] THEN
      SIMP_TAC [FINITE_UNIONS] THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [EXTENSION, IN_ELIM_THM]) THEN
      ASM_MESON_TAC [clause], ALL_TAC] THEN
    HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [num_WOP] THEN
    REWRITE_TAC [NOT_EXISTS_THM, RIGHT_IMP_FORALL_THM] THEN
    REWRITE_TAC [(← ExceptT.mk (TAUT [[a ==> ~(b /\ c) <=> a /\ c ==> ~b]]))] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[n:num]]) MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[v:form->bool]]) STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN ([[?m c. c IN N /\
                      ~(pholds v (interp c)) /\
                      {p | p IN c /\ negative p} HAS_SIZE m]])
    MP_TAC THENL
     [HolLight.GEN_REWRITE_TAC HolCore.Lib.I [SWAP_EXISTS_THM] THEN
      UNDISCH_TAC [[~psatisfiable (IMAGE interp s)]] THEN
      REWRITE_TAC [psatisfiable, NOT_EXISTS_THM, NOT_FORALL_THM] THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC [[v:form->bool]]) THEN
      SIMP_TAC [LEFT_IMP_EXISTS_THM, IN_IMAGE, NOT_FORALL_THM] THEN
      REWRITE_TAC [NOT_IMP] THEN GEN_TAC THEN
      REWRITE_TAC [LEFT_FORALL_IMP_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[k:form->bool]] THEN
      STRIP_TAC THEN EXISTS_TAC [[CARD {p | p IN k /\ negative p}]] THEN
      ASM_REWRITE_TAC [HAS_SIZE] THEN CONJ_TAC THENL
       [Fol.EXPAND_TAC "N" THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN
        SUBGOAL_THEN ([[(k:form->bool) IN P]]) ASSUME_TAC THENL
         [RULE_ASSUM_TAC (HolLight.REWRITE_RULE [EXTENSION, IN_ELIM_THM]) THEN
          ASM_MESON_TAC [], ALL_TAC] THEN
        ASM_MESON_TAC [IN_IMAGE, psatisfies], ALL_TAC] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC [[k:form->bool]] THEN
      SIMP_TAC [SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC [clause],
      ALL_TAC] THEN
    HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [num_WOP] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[m:num]]) (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[k:form->bool]]) STRIP_ASSUME_TAC) THEN
    MP_TAC (ASSUME [[(k:form->bool) IN N]]) THEN Fol.EXPAND_TAC "N" THEN
    REWRITE_TAC [IN_ELIM_THM] THEN DISCH_THEN (MP_TAC oTIO HolLight.CONJUNCT2) THEN
    REWRITE_TAC [allpositive, NOT_FORALL_THM, NOT_IMP, positive] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[r:form]]) MP_TAC) THEN REWRITE_TAC [negative] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[l:form]]) SUBST_ALL_TAC) THEN
    SUBGOAL_THEN ([[clause k]]) ASSUME_TAC THENL
     [RULE_ASSUM_TAC (HolLight.REWRITE_RULE [EXTENSION, IN_ELIM_THM]) THEN
      ASM_MESON_TAC [clause], ALL_TAC] THEN
    SUBGOAL_THEN ([[atom l]]) ASSUME_TAC THENL
     [SUBGOAL_THEN ([[literal(Not l)]]) MP_TAC THENL
       [ASM_MESON_TAC [clause], ALL_TAC] THEN
      SIMP_TAC [LEFT_IMP_EXISTS_THM, literal, Not_DEF, form_INJ, atom],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[v(l:form) = T]]) ASSUME_TAC THENL
     [UNDISCH_TAC [[~pholds v (interp k)]] THEN
      ASM_SIMP_TAC [PHOLDS_INTERP, CLAUSE_FINITE, NOT_EXISTS_THM] THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC [[Not l]]) THEN ASM_REWRITE_TAC [PHOLDS] THEN
      FIRST_ASSUM (STRIP_ASSUME_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [ATOM]) THEN
      ASM_REWRITE_TAC [PHOLDS], ALL_TAC] THEN
    SUBGOAL_THEN
     ([[?j. j IN P /\ l IN j /\ ~(pholds v (interp (j DELETE l)))]])
    MP_TAC THENL
     [FIRST_ASSUM (MP_TAC o HolLight.SPECL
       [ [[n - 1]], [[\p:form. if p = l then F else v(p)]] ]) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC (← ExceptT.mk (ARITH_RULE [[~(n = 0) ==> n - 1 < n]])) THEN
          DISCH_THEN SUBST_ALL_TAC THEN
          FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [HAS_SIZE_0]) THEN
          REWRITE_TAC [EXTENSION] THEN DISCH_THEN (MP_TAC o HolLight.SPEC [[l:form]]) THEN
          REWRITE_TAC [NOT_IN_EMPTY] THEN ASM_REWRITE_TAC [IN],
          ALL_TAC] THEN
        RULE_ASSUM_TAC (HolLight.REWRITE_RULE [HAS_SIZE]) THEN
        ASM_REWRITE_TAC [HAS_SIZE] THEN
        SUBGOAL_THEN ([[(\p:form. if p = l then F else v(p)) = v DELETE l]])
        SUBST1_TAC THENL
         [REWRITE_TAC [EXTENSION, IN_DELETE] THEN GEN_TAC THEN
          REWRITE_TAC [IN] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [],
          ALL_TAC] THEN
        ASM_SIMP_TAC [FINITE_DELETE, CARD_DELETE] THEN
        ASM_REWRITE_TAC [IN],
        ALL_TAC] THEN
      ONCE_REWRITE_TAC [(← ExceptT.mk (TAUT [[~a ==> b <=> ~b ==> a]]))] THEN
      REWRITE_TAC [NOT_EXISTS_THM] THEN
      REWRITE_TAC [(← ExceptT.mk (TAUT [[~(a /\ b /\ ~c) <=> a /\ b ==> c]]))] THEN
      DISCH_TAC THEN
      REWRITE_TAC [psatisfies] THEN GEN_TAC THEN REWRITE_TAC [IN_IMAGE] THEN
      SIMP_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC [[c:form->bool]] THEN
      DISCH_THEN (ASSUME_TAC oTIO HolLight.CONJUNCT2) THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[c:form->bool]]) THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN ([[clause c /\ clause(c DELETE l)]]) MP_TAC THENL
       [MATCH_MP_TAC (← ExceptT.mk (TAUT [[a /\ (a ==> b) ==> a /\ b]])) THEN CONJ_TAC THENL
         [RULE_ASSUM_TAC (HolLight.REWRITE_RULE [EXTENSION, IN_ELIM_THM]) THEN
          ASM_MESON_TAC [], ALL_TAC] THEN
        SIMP_TAC [clause, IN_DELETE, FINITE_DELETE], ALL_TAC] THEN
      SIMP_TAC [clause, PHOLDS_INTERP] THEN
      REWRITE_TAC [(← HolLight.GSYM clause)] THEN STRIP_TAC THEN
      ASM_CASES_TAC [[l:form IN c]] THEN ASM_REWRITE_TAC [] THENL
       [MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[q:form]] THEN
        SIMP_TAC [IN_DELETE] THEN
        DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
        SUBGOAL_THEN ([[atom q]]) MP_TAC THENL
         [RULE_ASSUM_TAC (HolLight.REWRITE_RULE [EXTENSION, IN_ELIM_THM]) THEN
          ASM_MESON_TAC [POSITIVE_LITERAL_ATOM, allpositive, clause],
          ALL_TAC] THEN
        SIMP_TAC [PHOLDS_ATOM] THEN ASM_REWRITE_TAC [],
        UNDISCH_TAC [[v psatisfies IMAGE interp P]] THEN
        REWRITE_TAC [psatisfies] THEN DISCH_THEN (MP_TAC o HolLight.SPEC [[interp c]]) THEN
        REWRITE_TAC [IN_IMAGE, LEFT_IMP_EXISTS_THM] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC [[c:form->bool]]) THEN ASM_REWRITE_TAC [] THEN
        ASM_SIMP_TAC [PHOLDS_INTERP, CLAUSE_FINITE] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[q:form]] THEN STRIP_TAC THEN
        SUBGOAL_THEN ([[atom q]]) MP_TAC THENL
         [RULE_ASSUM_TAC (HolLight.REWRITE_RULE [EXTENSION, IN_ELIM_THM]) THEN
          ASM_MESON_TAC [POSITIVE_LITERAL_ATOM, allpositive, clause],
          ALL_TAC] THEN
        ASM_SIMP_TAC [PHOLDS_ATOM] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [PHOLDS_ATOM]],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[j:form->bool]]) STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [ [[j:form->bool]], [[k:form->bool]], [[l:form]] ] THEN
    REWRITE_TAC [(← HolLight.GSYM negative), (← HolLight.GSYM positive)] THEN
    CONJ_TAC THENL
     [RULE_ASSUM_TAC (HolLight.REWRITE_RULE [EXTENSION, IN_ELIM_THM]) THEN
      ASM_MESON_TAC [allpositive], ALL_TAC] THEN
    CONJ_TAC THENL
     [RULE_ASSUM_TAC (HolLight.REWRITE_RULE [EXTENSION, IN_ELIM_THM]) THEN
      ASM_MESON_TAC [allpositive], ALL_TAC] THEN
    CONJ_TAC THENL
     [RULE_ASSUM_TAC (HolLight.REWRITE_RULE [EXTENSION, IN_ELIM_THM]) THEN
      ASM_MESON_TAC [allpositive], ALL_TAC] THEN
    ASM_REWRITE_TAC [negate] THEN CONJ_TAC THENL
     [COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [EXTENSION, IN_ELIM_THM]) THEN
      ASM_MESON_TAC [allpositive, positive], ALL_TAC] THEN
    FIRST_ASSUM (fun th => HolLight.tactic_of do
      pure (MP_TAC (← HolLight.SPEC ([[m - 1]]) th) THEN ANTS_TAC)) THENL
     [MATCH_MP_TAC (← ExceptT.mk (ARITH_RULE [[~(n = 0) ==> n - 1 < n]])) THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [HAS_SIZE_0]) THEN
      REWRITE_TAC [EXTENSION, NOT_IN_EMPTY] THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC [[Not l]]) THEN
      ASM_REWRITE_TAC [IN_ELIM_THM, negative] THEN MESON_TAC [],
      ALL_TAC] THEN
    REWRITE_TAC [NOT_EXISTS_THM] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[resolve l j k]]) THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (TAUT [[~a ==> ~b <=> b ==> a]]))] THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[~pholds v (interp (resolve l j k))]]) ASSUME_TAC THENL
     [UNDISCH_TAC [[~pholds v (interp k)]] THEN
      UNDISCH_TAC [[~pholds v (interp (j DELETE l))]] THEN
      SUBGOAL_THEN ([[clause j]]) ASSUME_TAC THENL
       [RULE_ASSUM_TAC (HolLight.REWRITE_RULE [EXTENSION, IN_ELIM_THM]) THEN
        ASM_MESON_TAC [clause], ALL_TAC] THEN
      ASM_SIMP_TAC [PHOLDS_INTERP, CLAUSE_FINITE, RESOLVE_CLAUSE,
                   FINITE_DELETE] THEN
      REWRITE_TAC [resolve, IN_UNION, IN_DELETE] THEN MESON_TAC [],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [SUBGOAL_THEN ([[~(resolve l j k IN P)]]) MP_TAC THENL
       [ASM_MESON_TAC [psatisfies, IN_IMAGE], ALL_TAC] THEN
      UNDISCH_TAC [[resolve l j k IN s]] THEN
      MAP_EVERY Fol.EXPAND_TAC ["P", "N"] THEN
      REWRITE_TAC [IN_ELIM_THM] THEN CONV_TAC TAUT, ALL_TAC] THEN
    SUBGOAL_THEN ([[{p | p IN resolve l j k /\ negative p} =
                  {p | p IN k /\ negative p} DELETE (Not l)]])
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_DELETE, IN_ELIM_THM, resolve, IN_UNION] THEN
      SUBGOAL_THEN ([[~~l = Not l]]) SUBST1_TAC THENL
       [REWRITE_TAC [negate] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
        RULE_ASSUM_TAC (HolLight.REWRITE_RULE [EXTENSION, IN_ELIM_THM]) THEN
        ASM_MESON_TAC [allpositive, positive], ALL_TAC] THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [EXTENSION, IN_ELIM_THM]) THEN
      GEN_TAC THEN MATCH_MP_TAC (← ExceptT.mk (TAUT
       [[(a ==> ~e) ==> ((a /\ b \/ c /\ d) /\ e <=> (c /\ e) /\ d)]])) THEN
      REWRITE_TAC [(← HolLight.GSYM positive)] THEN
      ASM_MESON_TAC [allpositive], ALL_TAC] THEN
    SUBGOAL_THEN ([[FINITE {p | p IN k /\ negative p}]]) MP_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC [[k:form->bool]] THEN
      ASM_SIMP_TAC [CLAUSE_FINITE, SUBSET, IN_ELIM_THM], ALL_TAC] THEN
    SIMP_TAC [HAS_SIZE, CARD_DELETE, FINITE_DELETE] THEN
    DISCH_TAC THEN UNDISCH_TAC [[{p | p IN k /\ negative p} HAS_SIZE m]] THEN
    SIMP_TAC [HAS_SIZE] THEN DISCH_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [negative])
  : ExceptT String IO thm).run
#eval PRESOLUTION_LEMMA

#eval phrase 12
unsafe def pposresproof_triple : thm × thm × thm := keep "pposresproof_triple" fun _ =>
  newInductive
    [[(!cl. cl IN hyps ==> pposresproof hyps cl) /\
      (!p cl1 cl2.
          pposresproof hyps cl1 /\ pposresproof hyps cl2 /\
          (allpositive cl1 \/ allpositive cl2) /\
          p IN cl1 /\ ~~p IN cl2
         ==> pposresproof hyps (resolve p cl1 cl2))]]
unsafe def pposresproof_RULES : thm := pposresproof_triple.1
unsafe def pposresproof_INDUCT : thm := pposresproof_triple.2.1
unsafe def pposresproof_CASES : thm := pposresproof_triple.2.2
#eval do IO.println pposresproof_RULES; IO.println pposresproof_INDUCT; IO.println pposresproof_CASES

#eval phrase 13
unsafe def POSRESPROOF_FINITE : thm := keep "POSRESPROOF_FINITE" fun _ => (do
  prove ([[!hyps. FINITE hyps /\ (!cl. cl IN hyps ==> clause cl)
        ==> FINITE {cl | pposresproof hyps cl}]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC [[{t | t SUBSET (UNIONS hyps)} :(form->bool)->bool]] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_POWERSET THEN RULE_ASSUM_TAC (HolLight.REWRITE_RULE [clause]) THEN
      ASM_SIMP_TAC [FINITE_UNIONS], ALL_TAC] THEN
    REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN
    MATCH_MP_TAC pposresproof_INDUCT THEN CONJ_TAC THENL
     [MESON_TAC [IN_UNIONS],
      REWRITE_TAC [resolve, IN_UNION, IN_DELETE] THEN MESON_TAC []])
  : ExceptT String IO thm).run
#eval POSRESPROOF_FINITE

#eval phrase 14
unsafe def PPOSRESPROOF_REFUTATION_COMPLETE_FINITE : thm := keep "PPOSRESPROOF_REFUTATION_COMPLETE_FINITE" fun _ => (do
  prove ([[FINITE hyps /\
   (!cl. cl IN hyps ==> clause cl) /\
   ~(psatisfiable {interp cl | cl IN hyps})
   ==> pposresproof hyps {}]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPEC ([[hyps:(form->bool)->bool]]) POSRESPROOF_FINITE) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    MP_TAC (← HolLight.SPEC ([[{cl | pposresproof hyps cl}]]) PRESOLUTION_LEMMA) THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN ([[~psatisfiable (IMAGE interp {cl | pposresproof hyps cl})]])
    ASSUME_TAC THENL
     [UNDISCH_TAC [[~psatisfiable {interp cl | cl IN hyps}]] THEN
      REWRITE_TAC [(← ExceptT.mk (TAUT [[~a ==> ~b <=> b ==> a]]))] THEN
      MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_CONJ_ALT]
                   PSATISFIABLE_MONO) THEN
      REWRITE_TAC [SUBSET, IN_IMAGE, IN_ELIM_THM] THEN
      MESON_TAC [pposresproof_RULES], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [IN_ELIM_THM] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[~c /\ a ==> (a /\ ~b ==> c) ==> b]])) THEN
    CONJ_TAC THENL [MESON_TAC [pposresproof_RULES], ALL_TAC] THEN
    MATCH_MP_TAC pposresproof_INDUCT THEN ASM_SIMP_TAC [RESOLVE_CLAUSE])
  : ExceptT String IO thm).run
#eval PPOSRESPROOF_REFUTATION_COMPLETE_FINITE

#eval phrase 15
unsafe def PPOSRESPROOF_MONO : thm := keep "PPOSRESPROOF_MONO" fun _ => (do
  prove ([[!hyps1 hyps2 c.
        pposresproof hyps1 c /\ hyps1 SUBSET hyps2 ==> pposresproof hyps2 c]])
   (GEN_TAC THEN HolLight.GEN_REWRITE_TAC HolCore.Lib.I [SWAP_FORALL_THM] THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC pposresproof_INDUCT THEN
    MESON_TAC [pposresproof_RULES, SUBSET])
  : ExceptT String IO thm).run
#eval PPOSRESPROOF_MONO

#eval phrase 16
unsafe def PPOSRESPROOF_REFUTATION_COMPLETE : thm := keep "PPOSRESPROOF_REFUTATION_COMPLETE" fun _ => (do
  prove ([[(!cl. cl IN hyps ==> clause cl) /\
   ~(psatisfiable {interp cl | cl IN hyps})
   ==> pposresproof hyps {}]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC PPOSRESPROOF_MONO THEN
    FIRST_ASSUM (MP_TAC oTIO HolLight.MATCH_MP UNPSATISFIABLE_FINITE_SUBSET) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[t:form->bool]]) STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
      ([[?h. FINITE h /\ h SUBSET hyps /\ t SUBSET {interp cl | cl IN h}]])
    MP_TAC THENL
     [REWRITE_TAC [IMAGE_CLAUSE] THEN MATCH_MP_TAC FINITE_SUBSET_IMAGE_IMP THEN
      ASM_REWRITE_TAC [(← HolLight.GSYM IMAGE_CLAUSE)], ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC [] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC PPOSRESPROOF_REFUTATION_COMPLETE_FINITE THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
      [ [[~(psatisfiable t)]], [[t SUBSET {interp cl | cl IN h}]] ] THEN
    REWRITE_TAC [PSATISFIABLE_MONO, (← ExceptT.mk (TAUT [[b ==> ~c ==> ~a <=> a /\ b ==> c]]))])
  : ExceptT String IO thm).run
#eval PPOSRESPROOF_REFUTATION_COMPLETE

#eval phrase 17
unsafe def psemresproof_triple : thm × thm × thm := keep "psemresproof_triple" fun _ =>
  newInductive
    [[(!cl. cl IN hyps ==> psemresproof v hyps cl) /\
      (!p cl1 cl2.
          psemresproof v hyps cl1 /\ psemresproof v hyps cl2 /\
          (~pholds v (interp cl1) \/ ~pholds v (interp cl2)) /\
          p IN cl1 /\ ~~p IN cl2
         ==> psemresproof v hyps (resolve p cl1 cl2))]]
unsafe def psemresproof_RULES : thm := psemresproof_triple.1
unsafe def psemresproof_INDUCT : thm := psemresproof_triple.2.1
unsafe def psemresproof_CASES : thm := psemresproof_triple.2.2
#eval do IO.println psemresproof_RULES; IO.println psemresproof_INDUCT; IO.println psemresproof_CASES

#eval phrase 18
unsafe def propflip : thm := keep "propflip" fun _ => new_definition
  [[propflip w p = if (negative p = pholds w p) then p else ~~p]]
#eval propflip

#eval phrase 19
unsafe def PHOLDS_LITERAL_PROPFLIP : thm := keep "PHOLDS_LITERAL_PROPFLIP" fun _ => (do
  prove ([[!p w. literal(p) ==> (pholds w p <=> pholds (\x. F) (propflip w p))]])
   (REWRITE_TAC [literal, ATOM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [propflip] THEN REWRITE_TAC [PHOLDS] THEN
    REWRITE_TAC [NEGATIVE_NOT, NOT_NEGATIVE_ATOM] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [PHOLDS_NEGATE, PHOLDS])
  : ExceptT String IO thm).run
#eval PHOLDS_LITERAL_PROPFLIP

#eval phrase 20
unsafe def PROPFLIP_INVOLUTE : thm := keep "PROPFLIP_INVOLUTE" fun _ => (do
  prove ([[!w p. literal p ==> (propflip w (propflip w p) = p)]])
   (REWRITE_TAC [literal, ATOM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [propflip] THEN REWRITE_TAC [PHOLDS] THEN
    REWRITE_TAC [NEGATIVE_NOT, NOT_NEGATIVE_ATOM] THENL
     [ASM_CASES_TAC [[w(Atom q l):bool]] THEN
      ASM_REWRITE_TAC [negate, NOT_NEGATIVE_ATOM, NEGATIVE_NOT, PHOLDS] THEN
      REWRITE_TAC [Not_DEF, form_INJ, SELECT_REFL],
      ASM_CASES_TAC [[w(Atom q' l):bool]] THEN
      ASM_REWRITE_TAC [negate, NOT_NEGATIVE_ATOM, NEGATIVE_NOT, PHOLDS] THEN
      REWRITE_TAC [Not_DEF, form_INJ, SELECT_REFL] THEN
      ASM_REWRITE_TAC [NOT_NEGATIVE_ATOM, PHOLDS]])
  : ExceptT String IO thm).run
#eval PROPFLIP_INVOLUTE

#eval phrase 21
unsafe def PROPFLIP_INJ : thm := keep "PROPFLIP_INJ" fun _ => (do
  prove ([[!w p q. literal p /\ literal q /\ (propflip w p = propflip w q)
           ==> (p = q)]])
   (MESON_TAC [PROPFLIP_INVOLUTE])
  : ExceptT String IO thm).run
#eval PROPFLIP_INJ

#eval phrase 22
unsafe def PROPFLIP_NEGATE : thm := keep "PROPFLIP_NEGATE" fun _ => (do
  prove ([[!w p. literal p ==> (propflip w (~~p) = ~~(propflip w p))]])
   (REWRITE_TAC [literal, ATOM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [propflip] THEN REWRITE_TAC [PHOLDS] THEN
    REWRITE_TAC [NEGATIVE_NOT, NOT_NEGATIVE_ATOM, NEGATE_NEG] THEN
    SIMP_TAC [NEGATE_ATOM, atom] THEN REWRITE_TAC [PHOLDS, NEGATIVE_NOT] THEN
    REWRITE_TAC [NEGATIVE_NOT, NOT_NEGATIVE_ATOM, NEGATE_NEG] THEN
    SIMP_TAC [NEGATE_ATOM, atom] THEN
    COND_CASES_TAC THEN SIMP_TAC [NEGATE_ATOM, atom, NEGATE_NEG])
  : ExceptT String IO thm).run
#eval PROPFLIP_NEGATE

#eval phrase 23
unsafe def PROPFLIP_RESOLVE : thm := keep "PROPFLIP_RESOLVE" fun _ => (do
  prove ([[!cl1 cl2 p w.
     clause cl1 /\ clause cl2 /\ p IN cl1
     ==> (IMAGE (propflip w) (resolve p cl1 cl2) =
          resolve (propflip w p)
                  (IMAGE (propflip w) cl1) (IMAGE (propflip w) cl2))]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [resolve, IMAGE_UNION] THEN BINOP_TAC THEN
    (REWRITE_TAC [EXTENSION, IN_IMAGE, IN_DELETE] THEN
     X_GEN_TAC [[q:form]] THEN EQ_TAC THENL
      [ALL_TAC, ASM_MESON_TAC [PROPFLIP_NEGATE, clause]] THEN
     REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN
     MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[r:form]] THEN
     STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
     ASM_MESON_TAC [PROPFLIP_INJ, clause, PROPFLIP_NEGATE, NEGATE_LITERAL]))
  : ExceptT String IO thm).run
#eval PROPFLIP_RESOLVE

#eval phrase 24
unsafe def PPOSRESPROOF_CLAUSE : thm := keep "PPOSRESPROOF_CLAUSE" fun _ => (do
  prove ([[!hyps. (!c. c IN hyps ==> clause c)
          ==> !c. pposresproof hyps c ==> clause c]])
   (GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC pposresproof_INDUCT THEN
    ASM_SIMP_TAC [RESOLVE_CLAUSE])
  : ExceptT String IO thm).run
#eval PPOSRESPROOF_CLAUSE

#eval phrase 25
unsafe def PSEMRESPROOF_CLAUSE : thm := keep "PSEMRESPROOF_CLAUSE" fun _ => (do
  prove ([[!hyps w. (!c. c IN hyps ==> clause c)
            ==> !c. psemresproof w hyps c ==> clause c]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC psemresproof_INDUCT THEN
    ASM_SIMP_TAC [RESOLVE_CLAUSE])
  : ExceptT String IO thm).run
#eval PSEMRESPROOF_CLAUSE

#eval phrase 26
unsafe def LITERAL_PROPFLIP : thm := keep "LITERAL_PROPFLIP" fun _ => (do
  prove ([[!p w. literal p ==> literal (propflip w p)]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [propflip] THEN
    COND_CASES_TAC THEN SIMP_TAC [NEGATE_LITERAL])
  : ExceptT String IO thm).run
#eval LITERAL_PROPFLIP

#eval phrase 27
unsafe def CLAUSE_IMAGE_PROPFLIP : thm := keep "CLAUSE_IMAGE_PROPFLIP" fun _ => (do
  prove ([[!cl w. clause cl ==> clause (IMAGE (propflip w) cl)]])
   (SIMP_TAC [clause, FINITE_IMAGE] THEN
    MESON_TAC [LITERAL_PROPFLIP, IN_IMAGE])
  : ExceptT String IO thm).run
#eval CLAUSE_IMAGE_PROPFLIP

#eval phrase 28
unsafe def PHOLDS_LITERAL_PROPFLIP_SAME : thm := keep "PHOLDS_LITERAL_PROPFLIP_SAME" fun _ => (do
  prove ([[!p w. literal(p) ==> (pholds w (propflip w p) <=> ~(positive p))]])
   (REWRITE_TAC [literal, ATOM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [propflip] THEN REWRITE_TAC [PHOLDS] THEN
    REWRITE_TAC [NEGATIVE_NOT, NOT_NEGATIVE_ATOM, positive] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [PHOLDS_NEGATE, PHOLDS])
  : ExceptT String IO thm).run
#eval PHOLDS_LITERAL_PROPFLIP_SAME

#eval phrase 29
unsafe def PHOLDS_IMAGE_PROPFLIP_SAME : thm := keep "PHOLDS_IMAGE_PROPFLIP_SAME" fun _ => (do
  prove ([[!v cl. clause cl
          ==> (pholds v (interp (IMAGE (propflip v) cl)) <=> ~(allpositive cl))]])
   (SIMP_TAC [clause, PHOLDS_INTERP, FINITE_IMAGE, allpositive] THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (TAUT [[a /\ b <=> ~(a ==> ~b)]]))] THEN
    SIMP_TAC [IN_IMAGE, LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [NOT_IMP, NOT_FORALL_THM] THEN
    MESON_TAC [PHOLDS_LITERAL_PROPFLIP_SAME])
  : ExceptT String IO thm).run
#eval PHOLDS_IMAGE_PROPFLIP_SAME

#eval phrase 30
unsafe def PPOSRESPROOF_PSEMRESPROOF : thm := keep "PPOSRESPROOF_PSEMRESPROOF" fun _ => (do
  prove ([[!hyps. (!c. c IN hyps ==> clause c)
          ==> !w cl. pposresproof hyps cl
                     ==> psemresproof w (IMAGE (IMAGE (propflip w)) hyps)
                                        (IMAGE (propflip w) cl)]])
   (GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    SUBGOAL_THEN
     ([[!cl. pposresproof hyps cl
           ==> clause cl /\ psemresproof w (IMAGE (IMAGE (propflip w)) hyps)
                                           (IMAGE (propflip w) cl)]])
     (fun th => SIMP_TAC [th]) THEN
    MATCH_MP_TAC pposresproof_INDUCT THEN
    ASM_SIMP_TAC [RESOLVE_CLAUSE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC [psemresproof_RULES, IN_IMAGE], ALL_TAC] THEN
    ASM_SIMP_TAC [PROPFLIP_RESOLVE] THEN
    REPEAT GEN_TAC THEN DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    MATCH_MP_TAC (← liftExcept (Session.CONJUNCT2 (← ExceptT.mk (HolLight.SPEC_ALL psemresproof_RULES)))) THEN
    ASM_SIMP_TAC [PHOLDS_IMAGE_PROPFLIP_SAME] THEN
    ASM_MESON_TAC [PROPFLIP_NEGATE, clause, NEGATE_LITERAL, IN_IMAGE])
  : ExceptT String IO thm).run
#eval PPOSRESPROOF_PSEMRESPROOF

#eval phrase 31
unsafe def PHOLDS_ATOM_PROPFLIP_DIFF : thm := keep "PHOLDS_ATOM_PROPFLIP_DIFF" fun _ => (do
  prove ([[!p v w. atom(p) ==> (pholds v (propflip w p) <=> ~(v p = w p))]])
   (SIMP_TAC [ATOM, LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    REWRITE_TAC [propflip, NOT_NEGATIVE_ATOM, positive, negate, PHOLDS] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [PHOLDS])
  : ExceptT String IO thm).run
#eval PHOLDS_ATOM_PROPFLIP_DIFF

#eval phrase 32
unsafe def PHOLDS_LITERAL_PROPFLIP_DIFF : thm := keep "PHOLDS_LITERAL_PROPFLIP_DIFF" fun _ => (do
  prove ([[!p v w. literal(p)
           ==> (pholds v (propflip w p) <=> pholds (\x. ~(v x = w x)) p)]])
   (REWRITE_TAC [literal, ATOM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [propflip] THEN REWRITE_TAC [PHOLDS] THEN
    REWRITE_TAC [NEGATIVE_NOT, NOT_NEGATIVE_ATOM, positive] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [PHOLDS_NEGATE, PHOLDS])
  : ExceptT String IO thm).run
#eval PHOLDS_LITERAL_PROPFLIP_DIFF

#eval phrase 33
unsafe def PHOLDS_INTERP_IMAGE_PROPFLIP_DIFF : thm := keep "PHOLDS_INTERP_IMAGE_PROPFLIP_DIFF" fun _ => (do
  prove ([[!v cl. clause cl
          ==> (pholds v (interp (IMAGE (propflip w) cl)) <=>
               pholds (\x. ~(v x = w x)) (interp cl))]])
   (SIMP_TAC [clause, PHOLDS_INTERP, FINITE_IMAGE] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC [IN_IMAGE, LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
    REWRITE_TAC [UNWIND_THM2, (← HolLight.GSYM CONJ_ASSOC)] THEN
    AP_TERM_TAC THEN HolLight.GEN_REWRITE_TAC HolCore.Lib.I [FUN_EQ_THM] THEN
    GEN_TAC THEN REWRITE_TAC [] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)]])) THEN
    ASM_SIMP_TAC [PHOLDS_LITERAL_PROPFLIP_DIFF])
  : ExceptT String IO thm).run
#eval PHOLDS_INTERP_IMAGE_PROPFLIP_DIFF

#eval phrase 34
unsafe def PSATISFIABLE_CLAUSES_PROPFLIP : thm := keep "PSATISFIABLE_CLAUSES_PROPFLIP" fun _ => (do
  prove ([[!w s. (!c. c IN s ==> clause c)
         ==> (psatisfiable (IMAGE (interp o IMAGE (propflip w)) s) <=>
              psatisfiable (IMAGE interp s))]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [psatisfiable, IMAGE_o] THEN EQ_TAC THEN
    DISCH_THEN (X_CHOOSE_THEN ([[v:form->bool]]) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC [[\p:form. ~(v(p):bool = w(p))]] THEN
    ASM_SIMP_TAC [IN_IMAGE, LEFT_IMP_EXISTS_THM, RIGHT_AND_EXISTS_THM] THENL
     [ASM_SIMP_TAC [(← HolLight.GSYM PHOLDS_INTERP_IMAGE_PROPFLIP_DIFF)],
      ASM_SIMP_TAC [PHOLDS_INTERP_IMAGE_PROPFLIP_DIFF] THEN
      REWRITE_TAC [(← ExceptT.mk (TAUT [[~(~(a <=> b) <=> b) <=> a]]))] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV (fun t => pure (ETA_CONV t)))] THEN
    ASM_MESON_TAC [IN_IMAGE])
  : ExceptT String IO thm).run
#eval PSATISFIABLE_CLAUSES_PROPFLIP

#eval phrase 35
unsafe def PSEMRESPROOF_MONO : thm := keep "PSEMRESPROOF_MONO" fun _ => (do
  prove ([[!w hyps1 hyps2 c.
        psemresproof w hyps1 c /\ hyps1 SUBSET hyps2
        ==> psemresproof w hyps2 c]])
   (GEN_TAC THEN GEN_TAC THEN HolLight.GEN_REWRITE_TAC HolCore.Lib.I [SWAP_FORALL_THM] THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC psemresproof_INDUCT THEN
    MESON_TAC [psemresproof_RULES, SUBSET])
  : ExceptT String IO thm).run
#eval PSEMRESPROOF_MONO

#eval phrase 36
unsafe def PROPFLIP_INVOLUTE_CLAUSE : thm := keep "PROPFLIP_INVOLUTE_CLAUSE" fun _ => (do
  prove ([[!w cl. clause cl ==> (IMAGE (propflip w) (IMAGE (propflip w) cl) = cl)]])
   (REWRITE_TAC [clause] THEN REPEAT STRIP_TAC THEN
    HolLight.GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN REWRITE_TAC [IN_IMAGE] THEN
    ASM_MESON_TAC [PROPFLIP_INVOLUTE])
  : ExceptT String IO thm).run
#eval PROPFLIP_INVOLUTE_CLAUSE

#eval phrase 37
unsafe def PSEMRESPROOF_REFUTATION_COMPLETE : thm := keep "PSEMRESPROOF_REFUTATION_COMPLETE" fun _ => (do
  let lemma ← (do
    prove ([[{interp cl | cl IN hyps} = IMAGE interp hyps]])
     (REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN MESON_TAC [])
    : ExceptT String IO thm)
  prove ([[!hyps w. (!cl. cl IN hyps ==> clause cl) /\
            ~(psatisfiable {interp cl | cl IN hyps})
            ==> psemresproof w hyps {}]])
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC [lemma] THEN
    ASM_SIMP_TAC [(← HolLight.GSYM PSATISFIABLE_CLAUSES_PROPFLIP)] THEN
    REWRITE_TAC [IMAGE_o, (← HolLight.GSYM lemma)] THEN
    SUBGOAL_THEN ([[!cl. cl IN IMAGE (IMAGE (propflip w)) hyps ==> clause cl]])
    MP_TAC THENL
     [ASM_SIMP_TAC [CLAUSE_IMAGE_PROPFLIP, IN_IMAGE, LEFT_IMP_EXISTS_THM],
      ALL_TAC] THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (TAUT [[a ==> b ==> c <=> a /\ b ==> a ==> c]]))] THEN
    DISCH_THEN (MP_TAC oTIO HolLight.MATCH_MP PPOSRESPROOF_REFUTATION_COMPLETE) THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (TAUT [[b ==> a ==> c <=> a /\ b ==> c]]))] THEN
    DISCH_THEN (MP_TAC oTIO HolLight.MATCH_MP
      (← HolLight.REWRITE_RULE [RIGHT_IMP_FORALL_THM, IMP_IMP]
                    PPOSRESPROOF_PSEMRESPROOF)) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[w:form->bool]]) THEN REWRITE_TAC [IMAGE_CLAUSES] THEN
    MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_CONJ_ALT]
                           PSEMRESPROOF_MONO) THEN
    SIMP_TAC [SUBSET, IN_IMAGE, LEFT_IMP_EXISTS_THM, RIGHT_AND_EXISTS_THM] THEN
    ASM_MESON_TAC [PROPFLIP_INVOLUTE_CLAUSE])
  : ExceptT String IO thm).run
#eval PSEMRESPROOF_REFUTATION_COMPLETE

#eval phrase 38
unsafe def posresproof_triple : thm × thm × thm := keep "posresproof_triple" fun _ =>
  newInductive
    [[(!cl. cl IN hyps ==> posresproof hyps cl) /\
      (!cl1 cl2 cl2' ps1 ps2 i.
           posresproof hyps cl1 /\ posresproof hyps cl2 /\
           (allpositive cl1 \/ allpositive cl2) /\
           (IMAGE (formsubst (rename cl2 (FVS cl1))) cl2 = cl2') /\
           ps1 SUBSET cl1 /\ ps2 SUBSET cl2' /\ ~(ps1 = {}) /\ ~(ps2 = {}) /\
           (?i. Unifies i (ps1 UNION {~~p | p IN ps2})) /\
           (mgu (ps1 UNION {~~p | p IN ps2}) = i)
           ==> posresproof hyps
                  (IMAGE (formsubst i) ((cl1 DIFF ps1) UNION (cl2' DIFF ps2))))]]
unsafe def posresproof_RULES : thm := posresproof_triple.1
unsafe def posresproof_INDUCT : thm := posresproof_triple.2.1
unsafe def posresproof_CASES : thm := posresproof_triple.2.2
#eval do IO.println posresproof_RULES; IO.println posresproof_INDUCT; IO.println posresproof_CASES

#eval phrase 39
unsafe def POSRESPROOF_CLAUSE : thm := keep "POSRESPROOF_CLAUSE" fun _ => (do
  let lemma ← (do
    prove ([[s DIFF t SUBSET s]]) (SET_TAC []) : ExceptT String IO thm)
  prove ([[(!cl. cl IN hyps ==> clause cl)
   ==> !cl. posresproof hyps cl ==> clause cl]])
   (DISCH_TAC THEN MATCH_MP_TAC posresproof_INDUCT THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [clause, IMAGE_UNION, FINITE_UNION] THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN CONJ_TAC THENL
     [ASM_MESON_TAC [clause, FINITE_IMAGE, lemma, FINITE_SUBSET], ALL_TAC] THEN
    Fol.EXPAND_TAC "cl2'" THEN REWRITE_TAC [IN_IMAGE, IN_UNION, IN_DIFF] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC [FORMSUBST_LITERAL])
  : ExceptT String IO thm).run
#eval POSRESPROOF_CLAUSE

#eval phrase 40
unsafe def ALLPOSITIVE_INSTANCE_OF : thm := keep "ALLPOSITIVE_INSTANCE_OF" fun _ => (do
  prove ([[!cl1 cl2. cl1 instance_of cl2 /\ allpositive cl1 ==> allpositive cl2]])
   (REWRITE_TAC [allpositive, instance_of] THEN REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC [] THEN MESON_TAC [positive, NEGATIVE_FORMSUBST, IN_IMAGE])
  : ExceptT String IO thm).run
#eval ALLPOSITIVE_INSTANCE_OF

#eval phrase 41
unsafe def POSRESOLUTION_COMPLETE : thm := keep "POSRESOLUTION_COMPLETE" fun _ => (do
  prove ([[(!cl. cl IN hyps ==> clause cl) /\
   ~(?M:(term->bool)#(num->term list->term)#(num->term list->bool).
        interpretation (language(IMAGE interp hyps)) M /\ ~(Dom M = {}) /\
        M satisfies (IMAGE interp hyps))
   ==> posresproof hyps {}]])
   (REPEAT STRIP_TAC THEN MP_TAC (← HolLight.SPEC ([[IMAGE interp hyps]]) HERBRAND_THEOREM) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [REWRITE_TAC [IN_IMAGE] THEN ASM_MESON_TAC [QFREE_INTERP], ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     ([[~(psatisfiable
          {interp cl |
           cl IN {IMAGE(formsubst v) cl | v,cl | cl IN hyps}})]])
    MP_TAC THENL
     [REWRITE_TAC [psatisfiable] THEN
      FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (MP_TAC th THEN
          MATCH_MP_TAC (← ExceptT.mk (TAUT [[(b ==> a) ==> ~a ==> ~b]])))) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[d:form->bool]] THEN
      REWRITE_TAC [psatisfies] THEN
      SIMP_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM, LEFT_AND_EXISTS_THM,
               RIGHT_AND_EXISTS_THM, IN_IMAGE] THEN
      ASM_SIMP_TAC [PHOLDS_INTERP_IMAGE] THEN MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN (MP_TAC oTIO HolLight.MATCH_MP
     (← HolLight.REWRITE_RULE [IMP_CONJ_ALT]
                  PPOSRESPROOF_REFUTATION_COMPLETE)) THEN
    ANTS_TAC THENL
     [SIMP_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
      ASM_SIMP_TAC [IMAGE_FORMSUBST_CLAUSE], ALL_TAC] THEN
    SUBGOAL_THEN
      ([[!cl0. pposresproof {IMAGE (formsubst v) cl | v,cl | cl IN hyps} cl0
             ==> ?cl. posresproof hyps cl /\ cl0 instance_of cl]])
    MP_TAC THENL
     [ALL_TAC,
      DISCH_THEN (MP_TAC o HolLight.SPEC [[ {}:form->bool ]]) THEN
      MATCH_MP_TAC (← ExceptT.mk (TAUT [[(b ==> c) ==> (a ==> b) ==> (a ==> c)]])) THEN
      MESON_TAC [INSTANCE_OF_EMPTY]] THEN
    MATCH_MP_TAC pposresproof_INDUCT THEN CONJ_TAC THENL
     [REWRITE_TAC [IN_IMAGE, instance_of, IN_ELIM_THM] THEN
      MESON_TAC [posresproof_RULES], ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [ [[p:form]], [[A':form->bool]], [[B':form->bool]] ] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN ([[A:form->bool]]) STRIP_ASSUME_TAC)
                               MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN ([[B:form->bool]]) STRIP_ASSUME_TAC)
                 (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    MP_TAC (← HolLight.SPECL
     [ [[A:form->bool]], [[IMAGE (formsubst (rename B (FVS A))) B]],
      [[A':form->bool]], [[B':form->bool]], [[resolve p A' B']], [[p:form]] ]
     LIFTING_LEMMA) THEN
    ABBREV_TAC [[C = IMAGE (formsubst (rename B (FVS A))) B]] THEN
    MP_TAC (← HolLight.SPECL [ [[B:form->bool]], [[FVS(A)]] ] rename) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC [FVS_CLAUSE_FINITE, POSRESPROOF_CLAUSE], ALL_TAC] THEN
    ASM_REWRITE_TAC [«renaming»] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    HolLight.GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.TOP_DEPTH_CONV)
     [FUN_EQ_THM, o_THM, I_DEF, BETA_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[j:num->term]]) (ASSUME_TAC oTIO HolLight.CONJUNCT1)) THEN
    ANTS_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC [POSRESPROOF_CLAUSE],
      ASM_MESON_TAC [IMAGE_FORMSUBST_CLAUSE, POSRESPROOF_CLAUSE],
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
      ASM_MESON_TAC [POSRESPROOF_CLAUSE, clause, QFREE_LITERAL], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[A1:form->bool]]) (X_CHOOSE_THEN ([[B1:form->bool]])
        MP_TAC)) THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[mgu (A1 UNION {~~ l | l IN B1})]]) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [MATCH_MP_TAC ISMGU_MGU THEN ASM_REWRITE_TAC [FINITE_UNION] THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC [POSRESPROOF_CLAUSE, clause, FINITE_SUBSET],
        SUBGOAL_THEN ([[{~~l | l IN B1} = IMAGE (~~) B1]]) SUBST1_TAC THENL
         [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN
          MESON_TAC [], ALL_TAC] THEN
        ASM_MESON_TAC [POSRESPROOF_CLAUSE, clause, FINITE_SUBSET, FINITE_IMAGE],
        REWRITE_TAC [IN_UNION, IN_ELIM_THM] THEN
        ASM_MESON_TAC [POSRESPROOF_CLAUSE, clause, QFREE_LITERAL, SUBSET,
                      IMAGE_FORMSUBST_CLAUSE, QFREE_NEGATE]],
      ALL_TAC] THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
      let r ← liftExcept (HolCore.Kernel.rand (concl th))
      pure (ASSUME_TAC th THEN EXISTS_TAC r)) THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC (← liftExcept (Session.CONJUNCT2 (← ExceptT.mk (HolLight.SPEC_ALL posresproof_RULES)))) THEN
    EXISTS_TAC [[B:form->bool]] THEN ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [ALLPOSITIVE_INSTANCE_OF])
  : ExceptT String IO thm).run
#eval POSRESOLUTION_COMPLETE

#eval phrase 42
unsafe def semresproof_triple : thm × thm × thm := keep "semresproof_triple" fun _ =>
  newInductive
    [[(!cl. cl IN hyps ==> semresproof M hyps cl) /\
      (!cl1 cl2 cl2' ps1 ps2 i.
           semresproof M hyps cl1 /\ semresproof M hyps cl2 /\
           (~(!v:num->A. holds M v (interp cl1)) \/
            ~(!v:num->A. holds M v (interp cl2))) /\
           (IMAGE (formsubst (rename cl2 (FVS cl1))) cl2 = cl2') /\
           ps1 SUBSET cl1 /\ ps2 SUBSET cl2' /\ ~(ps1 = {}) /\ ~(ps2 = {}) /\
           (?i. Unifies i (ps1 UNION {~~p | p IN ps2})) /\
           (mgu (ps1 UNION {~~p | p IN ps2}) = i)
           ==> semresproof M hyps
                  (IMAGE (formsubst i) ((cl1 DIFF ps1) UNION (cl2' DIFF ps2))))]]
unsafe def semresproof_RULES : thm := semresproof_triple.1
unsafe def semresproof_INDUCT : thm := semresproof_triple.2.1
unsafe def semresproof_CASES : thm := semresproof_triple.2.2
#eval do IO.println semresproof_RULES; IO.println semresproof_INDUCT; IO.println semresproof_CASES

#eval phrase 43
unsafe def SEMRESPROOF_CLAUSE : thm := keep "SEMRESPROOF_CLAUSE" fun _ => (do
  let lemma ← (do
    prove ([[s DIFF t SUBSET s]]) (SET_TAC []) : ExceptT String IO thm)
  prove ([[(!c. c IN hyps ==> clause c) ==> (!c. semresproof M hyps c ==> clause c)]])
   (DISCH_TAC THEN MATCH_MP_TAC semresproof_INDUCT THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [clause, IMAGE_UNION, FINITE_UNION] THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN CONJ_TAC THENL
     [ASM_MESON_TAC [clause, FINITE_IMAGE, lemma, FINITE_SUBSET], ALL_TAC] THEN
    Fol.EXPAND_TAC "cl2'" THEN REWRITE_TAC [IN_IMAGE, IN_UNION, IN_DIFF] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC [FORMSUBST_LITERAL])
  : ExceptT String IO thm).run
#eval SEMRESPROOF_CLAUSE

#eval phrase 44
unsafe def QFREE_HOLDS_PHOLDS : thm := keep "QFREE_HOLDS_PHOLDS" fun _ => (do
  prove ([[!p. qfree(p) ==> (holds M v p <=> pholds (holds M v) p)]])
   (MATCH_MP_TAC form_INDUCTION THEN SIMP_TAC [HOLDS, PHOLDS, qfree])
  : ExceptT String IO thm).run
#eval QFREE_HOLDS_PHOLDS

#eval phrase 45
unsafe def LIFTING_FALSIFY : thm := keep "LIFTING_FALSIFY" fun _ => (do
  prove ([[!p M w. qfree(p) /\ (!v. holds M v p)
           ==> pholds (holds M w) (formsubst i p)]])
   (SIMP_TAC [(← HolLight.GSYM QFREE_HOLDS_PHOLDS), QFREE_FORMSUBST, HOLDS_FORMSUBST])
  : ExceptT String IO thm).run
#eval LIFTING_FALSIFY

#eval phrase 46
unsafe def LIFTING_FALSITY_CLAUSE : thm := keep "LIFTING_FALSITY_CLAUSE" fun _ => (do
  prove ([[clause A /\ (!v:num->A. holds M v (interp A)) /\ A' instance_of A
   ==> pholds (holds M w) (interp A')]])
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [instance_of]) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[i:num->term]]) SUBST1_TAC) THEN
    SUBGOAL_THEN ([[pholds (holds M (w:num->A)) (formsubst i (interp A))]])
    MP_TAC THENL [ASM_MESON_TAC [LIFTING_FALSIFY, QFREE_INTERP], ALL_TAC] THEN
    ASM_SIMP_TAC [PHOLDS_INTERP, IMAGE_FORMSUBST_CLAUSE, FINITE_IMAGE,
                 CLAUSE_FINITE, PHOLDS_FORMSUBST, QFREE_INTERP] THEN
    ASM_MESON_TAC [IN_IMAGE, clause, QFREE_LITERAL, PHOLDS_FORMSUBST])
  : ExceptT String IO thm).run
#eval LIFTING_FALSITY_CLAUSE

#eval phrase 47
unsafe def SEMRESOLUTION_COMPLETE : thm := keep "SEMRESOLUTION_COMPLETE" fun _ => (do
  prove ([[(!cl. cl IN hyps ==> clause cl) /\
   ~(?M:(term->bool)#(num->term list->term)#(num->term list->bool).
        interpretation (language(IMAGE interp hyps)) M /\ ~(Dom M = {}) /\
        M satisfies (IMAGE interp hyps))
   ==> !M:(A->bool)#(num->A list->A)#(num->A list->bool).
           semresproof M hyps {}]])
   (REPEAT STRIP_TAC THEN MP_TAC (← HolLight.SPEC ([[IMAGE interp hyps]]) HERBRAND_THEOREM) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [REWRITE_TAC [IN_IMAGE] THEN ASM_MESON_TAC [QFREE_INTERP], ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     ([[~(psatisfiable
          {interp cl |
           cl IN {IMAGE(formsubst v) cl | v,cl |
                  cl IN hyps /\
                  (!x. v(x) IN herbase (functions (IMAGE interp hyps)))}})]])
    MP_TAC THENL
     [REWRITE_TAC [psatisfiable] THEN
      FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (MP_TAC th THEN
          MATCH_MP_TAC (← ExceptT.mk (TAUT [[(b ==> a) ==> ~a ==> ~b]])))) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[d:form->bool]] THEN
      REWRITE_TAC [psatisfies] THEN
      SIMP_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM, LEFT_AND_EXISTS_THM,
               RIGHT_AND_EXISTS_THM, IN_IMAGE] THEN
      ASM_SIMP_TAC [PHOLDS_INTERP_IMAGE] THEN MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN (MP_TAC oTIO HolLight.MATCH_MP
     (← HolLight.REWRITE_RULE [IMP_CONJ_ALT]
                  PSEMRESPROOF_REFUTATION_COMPLETE)) THEN
    REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN ANTS_TAC THENL
     [SIMP_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
      ASM_SIMP_TAC [IMAGE_FORMSUBST_CLAUSE], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[holds M (@x:num->A. T)]]) THEN
    ABBREV_TAC [[w = @x:num->A. T]] THEN
    ABBREV_TAC
      [[ghyps = {IMAGE(formsubst v) cl | v,cl |
                cl IN hyps /\
                (!x. v(x) IN herbase (functions (IMAGE interp hyps)))}]] THEN
    SUBGOAL_THEN
      ([[!cl0. psemresproof (holds M (w:num->A)) ghyps cl0
             ==> ?cl. semresproof M hyps cl /\ cl0 instance_of cl]])
    MP_TAC THENL
     [ALL_TAC,
      DISCH_THEN (MP_TAC o HolLight.SPEC [[ {}:form->bool ]]) THEN
      MATCH_MP_TAC (← ExceptT.mk (TAUT [[(b ==> c) ==> (a ==> b) ==> (a ==> c)]])) THEN
      MESON_TAC [INSTANCE_OF_EMPTY]] THEN
    MATCH_MP_TAC psemresproof_INDUCT THEN CONJ_TAC THENL
     [Fol.EXPAND_TAC "ghyps" THEN
      REWRITE_TAC [IN_IMAGE, instance_of, IN_ELIM_THM] THEN
      MESON_TAC [semresproof_RULES], ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [ [[p:form]], [[A':form->bool]], [[B':form->bool]] ] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN ([[A:form->bool]]) STRIP_ASSUME_TAC)
                               MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN ([[B:form->bool]]) STRIP_ASSUME_TAC)
                 (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    MP_TAC (← HolLight.SPECL
     [ [[A:form->bool]], [[IMAGE (formsubst (rename B (FVS A))) B]],
      [[A':form->bool]], [[B':form->bool]], [[resolve p A' B']], [[p:form]] ]
     LIFTING_LEMMA) THEN
    ABBREV_TAC [[C = IMAGE (formsubst (rename B (FVS A))) B]] THEN
    MP_TAC (← HolLight.SPECL [ [[B:form->bool]], [[FVS(A)]] ] rename) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC [FVS_CLAUSE_FINITE, SEMRESPROOF_CLAUSE], ALL_TAC] THEN
    ASM_REWRITE_TAC [«renaming»] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    HolLight.GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.TOP_DEPTH_CONV)
     [FUN_EQ_THM, o_THM, I_DEF, BETA_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[j:num->term]]) (ASSUME_TAC oTIO HolLight.CONJUNCT1)) THEN
    ANTS_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC [SEMRESPROOF_CLAUSE],
      ASM_MESON_TAC [IMAGE_FORMSUBST_CLAUSE, SEMRESPROOF_CLAUSE],
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
      ASM_MESON_TAC [SEMRESPROOF_CLAUSE, clause, QFREE_LITERAL], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[A1:form->bool]]) (X_CHOOSE_THEN ([[B1:form->bool]])
        MP_TAC)) THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[mgu (A1 UNION {~~ l | l IN B1})]]) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [MATCH_MP_TAC ISMGU_MGU THEN ASM_REWRITE_TAC [FINITE_UNION] THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC [SEMRESPROOF_CLAUSE, clause, FINITE_SUBSET],
        SUBGOAL_THEN ([[{~~l | l IN B1} = IMAGE (~~) B1]]) SUBST1_TAC THENL
         [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN
          MESON_TAC [], ALL_TAC] THEN
        ASM_MESON_TAC [SEMRESPROOF_CLAUSE, clause, FINITE_SUBSET, FINITE_IMAGE],
        REWRITE_TAC [IN_UNION, IN_ELIM_THM] THEN
        ASM_MESON_TAC [SEMRESPROOF_CLAUSE, clause, QFREE_LITERAL, SUBSET,
                      IMAGE_FORMSUBST_CLAUSE, QFREE_NEGATE]],
      ALL_TAC] THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
      let r ← liftExcept (HolCore.Kernel.rand (concl th))
      pure (ASSUME_TAC th THEN EXISTS_TAC r)) THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC (← liftExcept (Session.CONJUNCT2 (← ExceptT.mk (HolLight.SPEC_ALL semresproof_RULES)))) THEN
    EXISTS_TAC [[B:form->bool]] THEN ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [SEMRESPROOF_CLAUSE, LIFTING_FALSITY_CLAUSE])
  : ExceptT String IO thm).run
#eval SEMRESOLUTION_COMPLETE

#eval phrase 48
unsafe def semresproof2_triple : thm × thm × thm := keep "semresproof2_triple" fun _ =>
  newInductive
    [[(!cl. cl IN hyps ==> semresproof2 M hyps cl) /\
      (!cl1 cl2 cl2' ps1 ps2 i.
           semresproof2 M hyps cl1 /\ semresproof2 M hyps cl2 /\
           (~(!v:num->A. valuation M v ==> holds M v (interp cl1)) \/
            ~(!v:num->A. valuation M v ==> holds M v (interp cl2))) /\
           (IMAGE (formsubst (rename cl2 (FVS cl1))) cl2 = cl2') /\
           ps1 SUBSET cl1 /\ ps2 SUBSET cl2' /\ ~(ps1 = {}) /\ ~(ps2 = {}) /\
           (?i. Unifies i (ps1 UNION {~~p | p IN ps2})) /\
           (mgu (ps1 UNION {~~p | p IN ps2}) = i)
           ==> semresproof2 M hyps
                  (IMAGE (formsubst i) ((cl1 DIFF ps1) UNION (cl2' DIFF ps2))))]]
unsafe def semresproof2_RULES : thm := semresproof2_triple.1
unsafe def semresproof2_INDUCT : thm := semresproof2_triple.2.1
unsafe def semresproof2_CASES : thm := semresproof2_triple.2.2
#eval do IO.println semresproof2_RULES; IO.println semresproof2_INDUCT; IO.println semresproof2_CASES

#eval phrase 49
unsafe def SEMRESPROOF2_CLAUSE : thm := keep "SEMRESPROOF2_CLAUSE" fun _ => (do
  let lemma ← (do
    prove ([[s DIFF t SUBSET s]]) (SET_TAC []) : ExceptT String IO thm)
  prove ([[(!c. c IN hyps ==> clause c) ==> (!c. semresproof2 M hyps c ==> clause c)]])
   (DISCH_TAC THEN MATCH_MP_TAC semresproof2_INDUCT THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [clause, IMAGE_UNION, FINITE_UNION] THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN CONJ_TAC THENL
     [ASM_MESON_TAC [clause, FINITE_IMAGE, lemma, FINITE_SUBSET], ALL_TAC] THEN
    Fol.EXPAND_TAC "cl2'" THEN REWRITE_TAC [IN_IMAGE, IN_UNION, IN_DIFF] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC [FORMSUBST_LITERAL])
  : ExceptT String IO thm).run
#eval SEMRESPROOF2_CLAUSE

#eval phrase 50
unsafe def QFREE_HOLDS_PHOLDS_2 : thm := keep "QFREE_HOLDS_PHOLDS_2" fun _ => (do
  prove ([[!p. qfree(p) ==> (holds M v p <=> pholds (holds M v) p)]])
   (MATCH_MP_TAC form_INDUCTION THEN SIMP_TAC [HOLDS, PHOLDS, qfree])
  : ExceptT String IO thm).run
#eval QFREE_HOLDS_PHOLDS_2

#eval phrase 51
unsafe def LIFTING_FALSIFY_2 : thm := keep "LIFTING_FALSIFY_2" fun _ => (do
  prove ([[!p M w. qfree(p) /\
           (!v. valuation M v ==> holds M v p) /\
           (!x f l. (f,LENGTH l) IN functions_term(i x) /\
                    ALL (\a. a IN Dom(M)) l
                    ==> Fun M f l IN Dom(M))
           ==> !w. valuation M w ==> pholds (holds M w) (formsubst i p)]])
   (SIMP_TAC [(← HolLight.GSYM QFREE_HOLDS_PHOLDS_2), QFREE_FORMSUBST, HOLDS_FORMSUBST] THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC [valuation, o_THM] THEN X_GEN_TAC [[v:num]] THEN
    MATCH_MP_TAC INTERPRETATION_TERMVAL THEN ASM_REWRITE_TAC [] THEN
    ASM_REWRITE_TAC [interpretation])
  : ExceptT String IO thm).run
#eval LIFTING_FALSIFY_2

#eval phrase 52
unsafe def LIFTING_FALSITY_CLAUSE_2 : thm := keep "LIFTING_FALSITY_CLAUSE_2" fun _ => (do
  prove ([[clause A /\ (A' = IMAGE (formsubst i) A) /\
   (!v:num->A. valuation M v ==> holds M v (interp A)) /\
   (!x f l. (f,LENGTH l) IN functions_term(i x) /\
            ALL (\a. a IN Dom(M)) l
            ==> Fun M f l IN Dom(M))
   ==> !w. valuation M w ==> pholds (holds M w) (interp A')]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[pholds (holds M (w:num->A)) (formsubst i (interp A))]])
    MP_TAC THENL
     [UNDISCH_TAC [[valuation M (w:num->A)]] THEN
      SPEC_TAC ([[w:num->A]], [[w:num->A]]) THEN
      MATCH_MP_TAC LIFTING_FALSIFY_2 THEN ASM_REWRITE_TAC [] THEN
      ASM_SIMP_TAC [QFREE_INTERP], ALL_TAC] THEN
    ASM_SIMP_TAC [PHOLDS_INTERP, IMAGE_FORMSUBST_CLAUSE, FINITE_IMAGE,
                 CLAUSE_FINITE, PHOLDS_FORMSUBST, QFREE_INTERP] THEN
    ASM_MESON_TAC [IN_IMAGE, clause, QFREE_LITERAL, PHOLDS_FORMSUBST])
  : ExceptT String IO thm).run
#eval LIFTING_FALSITY_CLAUSE_2

#eval phrase 53
unsafe def FUNCTIONS_FORM_INTERP : thm := keep "FUNCTIONS_FORM_INTERP" fun _ => (do
  prove ([[!s. FINITE s ==> (functions_form(interp s) = functions s)]])
   (REWRITE_TAC [interp] THEN
    SUBGOAL_THEN
     ([[!l. functions_form(ITLIST (||)  l False) = functions(set_of_list l)]])
     (fun th => MESON_TAC [SET_OF_LIST_OF_SET, th]) THEN
    LIST_INDUCT_TAC THEN
    REWRITE_TAC [ITLIST, And_DEF, Or_DEF, Not_DEF,
                functions_form, set_of_list] THENL
     [REWRITE_TAC [functions, NOT_IN_EMPTY, EXTENSION, IN_ELIM_THM, IN_UNIONS],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [functions, IN_INSERT, EXTENSION, IN_ELIM_THM, IN_UNIONS,
                IN_UNION] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval FUNCTIONS_FORM_INTERP

#eval phrase 54
unsafe def FUNCTIONS_IMAGE_INTERP : thm := keep "FUNCTIONS_IMAGE_INTERP" fun _ => (do
  prove ([[!s. (!c. c IN s ==> FINITE(c))
       ==> (functions (IMAGE interp s) = UNIONS {functions p | p IN s})]])
   (REPEAT STRIP_TAC THEN HolLight.GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN
    REWRITE_TAC [functions_form, functions, IN_UNIONS,
                IN_ELIM_THM, IN_IMAGE] THEN
    HolLight.GEN_REWRITE_TAC HolCore.Lib.I [FORALL_PAIR_THM] THEN
    ONCE_REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (TAUT [[(a /\ b) /\ c <=> b /\ a /\ c]]))] THEN
    REWRITE_TAC [UNWIND_THM2] THEN
    REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
    REWRITE_TAC [UNWIND_THM2, (← HolLight.GSYM CONJ_ASSOC)] THEN
    REWRITE_TAC [(← HolLight.GSYM functions)] THEN
    ASM_MESON_TAC [FUNCTIONS_FORM_INTERP])
  : ExceptT String IO thm).run
#eval FUNCTIONS_IMAGE_INTERP

#eval phrase 55
unsafe def FUNCTIONS_RESOLVE : thm := keep "FUNCTIONS_RESOLVE" fun _ => (do
  prove ([[functions(resolve p cl1 cl2) SUBSET (functions cl1 UNION functions cl2)]])
   (REWRITE_TAC [SUBSET, functions, IN_UNION, resolve, IN_DIFF, IN_UNION,
                IN_UNIONS, IN_ELIM_THM, IN_DELETE] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval FUNCTIONS_RESOLVE

#eval phrase 56
unsafe def PSEMRESPROOF_FUNCTIONS : thm := keep "PSEMRESPROOF_FUNCTIONS" fun _ => (do
  prove ([[(!c. c IN hyps ==> clause c)
   ==> !c. psemresproof M hyps c
           ==> functions c SUBSET functions(IMAGE interp hyps)]])
   (DISCH_TAC THEN
    MATCH_MP_TAC psemresproof_INDUCT THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC [FUNCTIONS_IMAGE_INTERP,
                   PSEMRESPROOF_CLAUSE, CLAUSE_FINITE] THEN
      REWRITE_TAC [SUBSET, IN_UNIONS, IN_ELIM_THM] THEN MESON_TAC [],
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC [[functions cl1 UNION functions cl2]] THEN
    REWRITE_TAC [FUNCTIONS_RESOLVE] THEN ASM_MESON_TAC [SUBSET, IN_UNION])
  : ExceptT String IO thm).run
#eval PSEMRESPROOF_FUNCTIONS

#eval phrase 57
unsafe def FUNCTIONS_TERM_NOCONSTANTS : thm := keep "FUNCTIONS_TERM_NOCONSTANTS" fun _ => (do
  prove ([[!t. ~(?c. c,0 IN functions_term t) ==> ~(FVT t = {})]])
   (MATCH_MP_TAC term_INDUCT THEN
    REWRITE_TAC [functions_term, NOT_IN_EMPTY, FVT] THEN CONJ_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_SING, NOT_IN_EMPTY] THEN MESON_TAC [],
      ALL_TAC] THEN
    GEN_TAC THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC [ALL, LENGTH, IN_INSERT, MAP, LIST_UNION] THENL
     [MESON_TAC [], ALL_TAC] THEN
    REWRITE_TAC [IN_UNION, EMPTY_UNION] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval FUNCTIONS_TERM_NOCONSTANTS

#eval phrase 58
unsafe def HERBASE : thm := keep "HERBASE" fun _ => (do
  prove ([[!t. t IN herbase fns <=>
        functions_term t SUBSET fns /\
        (FVT(t) = if ?c. c,0 IN fns then {} else {0})]])
   (GEN_TAC THEN EQ_TAC THEN SPEC_TAC ([[t:term]], [[t:term]]) THENL
     [HolLight.GEN_REWRITE_TAC (HolLight.BINDER_CONV o HolLight.LAND_CONV) [IN] THEN
      MATCH_MP_TAC herbase_INDUCT THEN
      SIMP_TAC [FVT, functions_term, EMPTY_SUBSET] THEN
      REWRITE_TAC [(← HolLight.GSYM ALL_MEM)] THEN
      MAP_EVERY X_GEN_TAC [ [[f:num]], [[tms:term list]] ] THEN STRIP_TAC THEN
      CONJ_TAC THENL
       [REWRITE_TAC [SUBSET, IN_INSERT, IN_LIST_UNION, (← HolLight.GSYM EX_MEM), MEM_MAP] THEN
        ASM_MESON_TAC [SUBSET], ALL_TAC] THEN
      HolLight.GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN X_GEN_TAC [[y:num]] THEN
      REWRITE_TAC [IN_LIST_UNION, (← HolLight.GSYM EX_MEM), MEM_MAP] THEN
      REWRITE_TAC [RIGHT_AND_EXISTS_THM, (← HolLight.GSYM CONJ_ASSOC)] THEN
      ONCE_REWRITE_TAC [(← ExceptT.mk (TAUT [[a /\ b /\ c <=> c /\ a /\ b]]))] THEN
      ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN REWRITE_TAC [UNWIND_THM2] THEN
      HolLight.GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV)
       [(← ExceptT.mk (TAUT [[a /\ b <=> ~(b ==> ~a)]]))] THEN
      ASM_SIMP_TAC [] THEN REWRITE_TAC [NOT_IMP] THEN
      COND_CASES_TAC THEN REWRITE_TAC [NOT_IN_EMPTY] THEN
      SUBGOAL_THEN ([[~(tms:term list = [])]])
       (fun th => ASM_MESON_TAC [th, list_CASES, MEM, LENGTH_EQ_NIL]) THEN
      ASM_MESON_TAC [LENGTH],
      ALL_TAC] THEN
    MATCH_MP_TAC term_INDUCT THEN CONJ_TAC THENL
     [REWRITE_TAC [functions_term, EMPTY_SUBSET, FVT] THEN
      COND_CASES_TAC THEN REWRITE_TAC [EXTENSION, IN_SING, NOT_IN_EMPTY] THEN
      ASM_MESON_TAC [IN, herbase_RULES], ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [ [[f:num]], [[tms:term list]] ] THEN
    REWRITE_TAC [(← HolLight.GSYM ALL_MEM)] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [IN] THEN MATCH_MP_TAC (← liftExcept (Session.CONJUNCT2 (← ExceptT.mk (HolLight.SPEC_ALL herbase_RULES)))) THEN
    UNDISCH_TAC [[functions_term (Fn f tms) SUBSET fns]] THEN
    REWRITE_TAC [SUBSET, functions_term, IN_INSERT, IN_LIST_UNION] THEN
    SIMP_TAC [(← ExceptT.mk (TAUT [[(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)]])),
             FORALL_AND_THM] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[(a ==> a') /\ (b ==> b') ==> a /\ b ==> a' /\ b']])) THEN
    CONJ_TAC THENL [MESON_TAC [], ALL_TAC] THEN
    REWRITE_TAC [(← HolLight.GSYM ALL_MEM), (← HolLight.GSYM EX_MEM), MEM_MAP] THEN
    SIMP_TAC [LEFT_IMP_EXISTS_THM, RIGHT_AND_EXISTS_THM] THEN
    HolLight.GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.BINDER_CONV) [SWAP_FORALL_THM] THEN
    HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [SWAP_FORALL_THM] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC [[t:term]] THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (TAUT [[a /\ b /\ c ==> d <=> c ==> a /\ b ==> d]]))] THEN
    SIMP_TAC [] THEN ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[functions_term t]]) THEN REWRITE_TAC [] THEN
    REPEAT STRIP_TAC THEN HolLight.GEN_REWRITE_TAC HolCore.Lib.I [(← HolLight.GSYM IN)] THEN
    FIRST_ASSUM (MATCH_MP_TAC o HolLight.REWRITE_RULE [(← ExceptT.mk (TAUT
     [[a ==> b ==> c <=> a /\ b ==> c]]))]) THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [ASM_MESON_TAC [SUBSET, IN], ALL_TAC] THEN
    UNDISCH_TAC [[FVT(Fn f tms) = (if ?c:num. c,0 IN fns then {} else {0})]] THEN
    REWRITE_TAC [FVT] THEN COND_CASES_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_LIST_UNION, MEM_MAP, NOT_IN_EMPTY,
                  (← HolLight.GSYM EX_MEM)] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[~(FVT t = {})]]) MP_TAC THENL
     [ASM_MESON_TAC [FUNCTIONS_TERM_NOCONSTANTS], ALL_TAC] THEN
    REWRITE_TAC [EXTENSION, NOT_IN_EMPTY, IN_SING] THEN
    REWRITE_TAC [IN_LIST_UNION, MEM_MAP, NOT_IN_EMPTY,
                  (← HolLight.GSYM EX_MEM)] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval HERBASE

#eval phrase 59
unsafe def HERBASE_LEMMA : thm := keep "HERBASE_LEMMA" fun _ => (do
  prove ([[functions_form q SUBSET fns /\
   (!v. i(v) IN herbase fns) /\
   ~(j(x) IN herbase fns) /\
   x IN FV(p)
   ==> ~(formsubst j p = formsubst i q)]])
   (REWRITE_TAC [HERBASE] THEN
    REWRITE_TAC [DE_MORGAN_THM] THEN REPEAT STRIP_TAC THENL
     [SUBGOAL_THEN ([[functions_form(formsubst i q) SUBSET fns /\
                    ~(functions_form(formsubst j p) SUBSET fns)]])
       (fun th => ASM_MESON_TAC [th]) THEN
      REWRITE_TAC [FORMSUBST_FUNCTIONS_FORM] THEN CONJ_TAC THENL
       [REWRITE_TAC [SUBSET, IN_UNION, IN_ELIM_THM] THEN
        ASM_MESON_TAC [SUBSET], ALL_TAC] THEN
      UNDISCH_TAC [[~(functions_term (j(x:num)) SUBSET fns)]] THEN
      REWRITE_TAC [SUBSET] THEN REWRITE_TAC [NOT_FORALL_THM, NOT_IMP] THEN
      MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC [[fn:num#num]] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [IN_UNION, IN_ELIM_THM] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[?y. y IN FVT(j(x:num)) /\ !z:num. ~(y IN FVT(i z))]])
    MP_TAC THENL
     [ALL_TAC,
      DISCH_THEN (X_CHOOSE_THEN ([[y:num]]) STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN ([[~(FV(formsubst j p) = FV(formsubst i q))]])
       (fun th => ASM_MESON_TAC [th]) THEN
      REWRITE_TAC [EXTENSION, NOT_FORALL_THM, IN_ELIM_THM, FORMSUBST_FV] THEN
      ASM_MESON_TAC []] THEN
    ASM_REWRITE_TAC [] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THENL
     [UNDISCH_TAC
        [[~(FVT(j(x:num)) = (if ?c:num. c,0 IN fns then {} else {0}))]] THEN
      ASM_REWRITE_TAC [EXTENSION, IN_SING, NOT_IN_EMPTY] THEN MESON_TAC [],
      ALL_TAC] THEN
    UNDISCH_TAC
     [[~(FVT(j(x:num)) = (if ?c:num. c,0 IN fns then {} else {0}))]] THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN ([[~(FVT(j(x:num)) = {})]]) MP_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [EXTENSION, NOT_IN_EMPTY, IN_SING] THEN MESON_TAC []] THEN
    MATCH_MP_TAC FUNCTIONS_TERM_NOCONSTANTS THEN
    SUBGOAL_THEN ([[functions_term(j(x:num)) SUBSET fns]])
     (fun th => ASM_MESON_TAC [th, SUBSET]) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC [[functions_form(formsubst j p)]] THEN CONJ_TAC THENL
     [REWRITE_TAC [FORMSUBST_FUNCTIONS_FORM] THEN
      REWRITE_TAC [SUBSET, IN_UNION, IN_ELIM_THM] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [FORMSUBST_FUNCTIONS_FORM, SUBSET] THEN
    REWRITE_TAC [IN_UNION, IN_ELIM_THM] THEN ASM_MESON_TAC [SUBSET])
  : ExceptT String IO thm).run
#eval HERBASE_LEMMA

#eval phrase 60
unsafe def SEMRESOLUTION_COMPLETE_2 : thm := keep "SEMRESOLUTION_COMPLETE_2" fun _ => (do
  prove ([[(!cl. cl IN hyps ==> clause cl) /\
   ~(?M:(term->bool)#(num->term list->term)#(num->term list->bool).
        interpretation (language(IMAGE interp hyps)) M /\ ~(Dom M = {}) /\
        M satisfies (IMAGE interp hyps))
   ==> !M:(A->bool)#(num->A list->A)#(num->A list->bool).
           interpretation (language(IMAGE interp hyps)) M /\ ~(Dom M = {})
           ==> semresproof2 M hyps {}]])
   (REPEAT STRIP_TAC THEN MP_TAC (← HolLight.SPEC ([[IMAGE interp hyps]]) HERBRAND_THEOREM) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [REWRITE_TAC [IN_IMAGE] THEN ASM_MESON_TAC [QFREE_INTERP], ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     ([[~(psatisfiable
          {interp cl |
           cl IN {IMAGE(formsubst v) cl | v,cl |
                  cl IN hyps /\
                  (!x. v(x) IN herbase (functions (IMAGE interp hyps)))}})]])
    MP_TAC THENL
     [REWRITE_TAC [psatisfiable] THEN
      FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (MP_TAC th THEN
          MATCH_MP_TAC (← ExceptT.mk (TAUT [[(b ==> a) ==> ~a ==> ~b]])))) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[d:form->bool]] THEN
      REWRITE_TAC [psatisfies] THEN
      SIMP_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM, LEFT_AND_EXISTS_THM,
               RIGHT_AND_EXISTS_THM, IN_IMAGE] THEN
      ASM_SIMP_TAC [PHOLDS_INTERP_IMAGE] THEN MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN (MP_TAC oTIO HolLight.MATCH_MP
     (← HolLight.REWRITE_RULE [IMP_CONJ_ALT]
                  PSEMRESPROOF_REFUTATION_COMPLETE)) THEN
    REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN ANTS_TAC THENL
     [SIMP_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
      ASM_SIMP_TAC [IMAGE_FORMSUBST_CLAUSE], ALL_TAC] THEN
    FIRST_ASSUM (X_CHOOSE_TAC [[w:num->A]] oTIO HolLight.MATCH_MP VALUATION_EXISTS) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[holds M (w:num->A)]]) THEN
    ABBREV_TAC
      [[ghyps = {IMAGE(formsubst v) cl | v,cl |
                cl IN hyps /\
                (!x. v(x) IN herbase (functions (IMAGE interp hyps)))}]] THEN
    SUBGOAL_THEN
      ([[!cl0. psemresproof (holds M (w:num->A)) ghyps cl0
             ==> ?cl. semresproof2 M hyps cl /\
                      ?i. (!x. i(x) IN herbase(functions(IMAGE interp hyps))) /\
                          (cl0 = IMAGE (formsubst i) cl)]])
    MP_TAC THENL
     [ALL_TAC,
      DISCH_THEN (MP_TAC o HolLight.SPEC [[ {}:form->bool ]]) THEN
      MATCH_MP_TAC (← ExceptT.mk (TAUT [[(b ==> c) ==> (a ==> b) ==> (a ==> c)]])) THEN
      MESON_TAC [INSTANCE_OF_EMPTY, instance_of]] THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (TAUT [[a ==> b <=> a ==> a /\ b]]))] THEN
    MATCH_MP_TAC psemresproof_INDUCT THEN CONJ_TAC THENL
     [SIMP_TAC [(← liftExcept (Session.CONJUNCT1 (← ExceptT.mk (HolLight.SPEC_ALL psemresproof_RULES))))] THEN
      Fol.EXPAND_TAC "ghyps" THEN
      REWRITE_TAC [IN_IMAGE, instance_of, IN_ELIM_THM] THEN
      MESON_TAC [semresproof2_RULES], ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [ [[p:form]], [[A':form->bool]], [[B':form->bool]] ] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN ([[A:form->bool]]) MP_TAC)) MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN ([[B:form->bool]]) MP_TAC)) MP_TAC) THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[k1:num->term]]) (STRIP_ASSUME_TAC oTIO HolLight.GSYM)) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[k2:num->term]]) (STRIP_ASSUME_TAC oTIO HolLight.GSYM)) THEN
    CONJ_TAC THENL [ASM_SIMP_TAC [psemresproof_RULES], ALL_TAC] THEN
    MP_TAC (← HolLight.SPECL
     [ [[A:form->bool]], [[IMAGE (formsubst (rename B (FVS A))) B]],
      [[A':form->bool]], [[B':form->bool]], [[resolve p A' B']], [[p:form]] ]
     LIFTING_LEMMA) THEN
    ABBREV_TAC [[C = IMAGE (formsubst (rename B (FVS A))) B]] THEN
    MP_TAC (← HolLight.SPECL [ [[B:form->bool]], [[FVS(A)]] ] rename) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC [FVS_CLAUSE_FINITE, SEMRESPROOF2_CLAUSE], ALL_TAC] THEN
    ASM_REWRITE_TAC [«renaming»] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    HolLight.GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.TOP_DEPTH_CONV)
     [FUN_EQ_THM, o_THM, I_DEF, BETA_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[j:num->term]]) (ASSUME_TAC oTIO HolLight.CONJUNCT1)) THEN
    ANTS_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC [SEMRESPROOF2_CLAUSE],
      ASM_MESON_TAC [IMAGE_FORMSUBST_CLAUSE, SEMRESPROOF2_CLAUSE],
      ONCE_REWRITE_TAC [INTER_COMM] THEN ASM_REWRITE_TAC [],
      ASM_MESON_TAC [instance_of],
      SUBGOAL_THEN ([[B' instance_of B]]) MP_TAC THENL
       [ASM_MESON_TAC [instance_of], ALL_TAC] THEN
      REWRITE_TAC [instance_of] THEN
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
      ASM_MESON_TAC [SEMRESPROOF2_CLAUSE, clause, QFREE_LITERAL], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[A1:form->bool]]) (X_CHOOSE_THEN ([[B1:form->bool]])
        MP_TAC)) THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[mgu (A1 UNION {~~ l | l IN B1})]]) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [MATCH_MP_TAC ISMGU_MGU THEN ASM_REWRITE_TAC [FINITE_UNION] THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC [SEMRESPROOF2_CLAUSE, clause, FINITE_SUBSET],
        SUBGOAL_THEN ([[{~~l | l IN B1} = IMAGE (~~) B1]]) SUBST1_TAC THENL
         [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN
          MESON_TAC [], ALL_TAC] THEN
        ASM_MESON_TAC [SEMRESPROOF2_CLAUSE, clause, FINITE_SUBSET, FINITE_IMAGE],
        REWRITE_TAC [IN_UNION, IN_ELIM_THM] THEN
        ASM_MESON_TAC [SEMRESPROOF2_CLAUSE, clause, QFREE_LITERAL, SUBSET,
                      IMAGE_FORMSUBST_CLAUSE, QFREE_NEGATE]],
      ALL_TAC] THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
      let r ← liftExcept (HolCore.Kernel.rand (concl th))
      pure (ASSUME_TAC th THEN EXISTS_TAC r)) THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [MATCH_MP_TAC (← liftExcept (Session.CONJUNCT2 (← ExceptT.mk (HolLight.SPEC_ALL semresproof2_RULES)))) THEN
      EXISTS_TAC [[B:form->bool]] THEN ASM_REWRITE_TAC [] THEN
      FIRST_ASSUM (fun th => HolLight.tactic_of do
        let _ ← liftExcept (HolCore.Lib.check (fun t => HolCore.Basics.is_disj t) (concl th))
        pure (UNDISCH_TAC (concl th))) THEN
      MAP_EVERY Fol.EXPAND_TAC ["A'", "B'"] THEN
      UNDISCH_TAC [[valuation M (w:num->A)]] THEN
      MATCH_MP_TAC (← ExceptT.mk (TAUT
       [[(d ==> a ==> b) /\ (e ==> a ==> c)
        ==> a ==> ~b \/ ~c ==> ~d \/ ~e]])) THEN
      CONJ_TAC THEN DISCH_TAC THEN SPEC_TAC ([[w:num->A]], [[w:num->A]]) THEN
      MATCH_MP_TAC (← HolLight.GEN_ALL LIFTING_FALSITY_CLAUSE_2) THENL
       [MAP_EVERY EXISTS_TAC [ [[A:form->bool]], [[k2:num->term]] ],
        MAP_EVERY EXISTS_TAC [ [[B:form->bool]], [[k1:num->term]] ]] THEN
      (ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
        [ASM_MESON_TAC [SEMRESPROOF2_CLAUSE], ALL_TAC] THEN
       REPEAT STRIP_TAC THEN
       FIRST_ASSUM (MATCH_MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [interpretation] o
                     HolLight.REWRITE_RULE [language]) THEN
       ASM_REWRITE_TAC [])
      THENL
       [UNDISCH_TAC [[f,LENGTH(l:A list) IN functions_term (k2(x:num))]],
        UNDISCH_TAC [[f,LENGTH(l:A list) IN functions_term (k1(x:num))]]] THEN
      SPEC_TAC ([[f:num,LENGTH(l:A list)]], [[fn:num#num]]) THEN
      REWRITE_TAC [(← HolLight.GSYM SUBSET)] THEN MATCH_MP_TAC HERBASE_FUNCTIONS THEN
      ASM_REWRITE_TAC [], ALL_TAC] THEN
    UNDISCH_TAC
     [[resolve p A' B' instance_of
       IMAGE (formsubst (mgu (A1 UNION {~~ l | l IN B1})))
       (A DIFF A1 UNION C DIFF B1)]] THEN
    REWRITE_TAC [instance_of] THEN
    DISCH_THEN (X_CHOOSE_TAC [[i:num->term]]) THEN
    ABBREV_TAC [[D = IMAGE (formsubst (mgu (A1 UNION {~~ l | l IN B1})))
                          (A DIFF A1 UNION C DIFF B1)]] THEN
    ABBREV_TAC
     [[i' = \x:num. if i(x) IN herbase (functions (IMAGE interp hyps))
                   then i(x)
                   else @x. x IN herbase (functions (IMAGE interp hyps))]] THEN
    EXISTS_TAC [[i':num->term]] THEN CONJ_TAC THENL
     [GEN_TAC THEN Fol.EXPAND_TAC "i'" THEN REWRITE_TAC [] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC [] THEN CONV_TAC (fun t => pure (SELECT_CONV t)) THEN
      REWRITE_TAC [HERBASE_NONEMPTY], ALL_TAC] THEN
    SUBGOAL_THEN
     ([[!p x. p IN D /\ x IN FV(p) ==> (i'(x):term = i(x))]])
    MP_TAC THENL
     [ALL_TAC,
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [EXTENSION, IN_IMAGE] THEN
      MESON_TAC [FORMSUBST_VALUATION]] THEN
    SUBGOAL_THEN ([[!p x. p IN D /\ x IN FV(p)
                        ==> i(x) IN herbase(functions (IMAGE interp hyps))]])
    MP_TAC THENL
     [ALL_TAC,
      Fol.EXPAND_TAC "i'" THEN SIMP_TAC [] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [] THEN
      ASM_MESON_TAC []] THEN
    SUBGOAL_THEN
     ([[!p. p IN D ==> ?v q. (!x. v x IN herbase(functions(IMAGE interp hyps))) /\
                           functions_form q SUBSET
                              functions(IMAGE interp hyps) /\
                           (formsubst i p = formsubst v q)]])
     (fun th => ASM_MESON_TAC [th, HERBASE_LEMMA]) THEN
    SUBGOAL_THEN
     ([[!p. p IN D ==> functions_form(formsubst i p) SUBSET
                        functions(IMAGE interp ghyps) /\
                     ?v q. (!x. v x IN herbase(functions(IMAGE interp hyps))) /\
                           (formsubst i p = formsubst v q)]])
    MP_TAC THENL
     [X_GEN_TAC [[q:form]] THEN DISCH_TAC THEN
      SUBGOAL_THEN ([[(formsubst i q) IN resolve p A' B']]) ASSUME_TAC THENL
       [ASM_MESON_TAC [EXTENSION, IN_IMAGE], ALL_TAC] THEN
      CONJ_TAC THENL
       [ALL_TAC,
        UNDISCH_TAC [[(formsubst i q) IN resolve p A' B']] THEN
        REWRITE_TAC [resolve, IN_UNION, IN_DELETE] THEN
        MAP_EVERY Fol.EXPAND_TAC ["A'", "B'"] THEN ASM_MESON_TAC [IN_IMAGE]] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC [[functions(resolve p A' B')]] THEN CONJ_TAC THENL
       [REWRITE_TAC [functions, SUBSET, IN_UNIONS, IN_ELIM_THM] THEN
        ASM_MESON_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN ([[psemresproof (holds M (w:num->A)) ghyps (resolve p A' B')]])
      MP_TAC THENL
       [MATCH_MP_TAC (← liftExcept (Session.CONJUNCT2 (← ExceptT.mk (HolLight.SPEC_ALL psemresproof_RULES)))) THEN
        ASM_REWRITE_TAC [], ALL_TAC] THEN
      SPEC_TAC ([[resolve p A' B']], [[cl:form->bool]]) THEN
      MATCH_MP_TAC PSEMRESPROOF_FUNCTIONS THEN
      Fol.EXPAND_TAC "ghyps" THEN REWRITE_TAC [IN_ELIM_THM] THEN
      ASM_MESON_TAC [IMAGE_FORMSUBST_CLAUSE], ALL_TAC] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC [[q:form]] THEN
    DISCH_THEN (fun th => DISCH_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_THEN ([[ii:num->term]]) MP_TAC)) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[r:form]]) STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [ [[ii:num->term]], [[r:form]] ] THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC [[functions_form(formsubst i q)]] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC [] THEN REWRITE_TAC [FORMSUBST_FUNCTIONS_FORM] THEN
      SIMP_TAC [SUBSET, IN_UNION], ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC [[functions(IMAGE interp ghyps)]] THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN
     ([[functions(IMAGE interp ghyps) = UNIONS {functions p | p IN ghyps}]])
    SUBST1_TAC THENL
     [MATCH_MP_TAC FUNCTIONS_IMAGE_INTERP THEN
      ASM_SIMP_TAC [CLAUSE_FINITE] THEN Fol.EXPAND_TAC "ghyps" THEN
      REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC [FINITE_IMAGE, CLAUSE_FINITE], ALL_TAC] THEN
    REWRITE_TAC [SUBSET, IN_UNIONS, IN_ELIM_THM] THEN
    X_GEN_TAC [[fn:num#num]] THEN
    DISCH_THEN (CHOOSE_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[cl:form->bool]])
     (CONJUNCTS_THEN2 MP_TAC SUBST_ALL_TAC)) THEN
    Fol.EXPAND_TAC "ghyps" THEN REWRITE_TAC [IN_ELIM_THM, IN_IMAGE] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[vv:num->term]]) MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[c:form->bool]]) MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST_ALL_TAC) THEN
    UNDISCH_TAC [[fn IN functions (IMAGE (formsubst vv) c)]] THEN
    HolLight.GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [functions] THEN
    REWRITE_TAC [IN_UNIONS, IN_ELIM_THM, IN_IMAGE] THEN
    DISCH_THEN (CHOOSE_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    DISCH_THEN (CHOOSE_THEN (CONJUNCTS_THEN2 MP_TAC SUBST_ALL_TAC)) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[s:form]])
     (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
    UNDISCH_TAC [[fn IN functions_form (formsubst vv s)]] THEN
    REWRITE_TAC [FORMSUBST_FUNCTIONS_FORM] THEN
    REWRITE_TAC [IN_UNION, IN_ELIM_THM] THEN
    DISCH_THEN (DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
     [ASM_SIMP_TAC [FUNCTIONS_IMAGE_INTERP, CLAUSE_FINITE] THEN
      REWRITE_TAC [IN_UNIONS, functions, IN_ELIM_THM] THEN
      EXISTS_TAC [[UNIONS {functions_form f | f IN c}]] THEN
      CONJ_TAC THENL
       [EXISTS_TAC [[c:form->bool]] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
      REWRITE_TAC [IN_UNIONS, IN_ELIM_THM] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    ASM_MESON_TAC [HERBASE_FUNCTIONS, SUBSET])
  : ExceptT String IO thm).run
#eval SEMRESOLUTION_COMPLETE_2

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py from the `#eval`s above. -/
unsafe def ensure : IO Unit := once "HolLogicArith.Positive" do
  replay (
          HolLogicArith.Support.ensure)
  replay (
          allpositive)
  replay (
          NOT_NEGATIVE_ATOM)
  replay (
          NEGATIVE_NOT)
  replay (
          CLAUSE_FINITE)
  replay (
          POSITIVE_LITERAL_ATOM)
  replay (
          PHOLDS_ATOM)
  replay (
          PHOLDS_ALLTRUE_POSLIT)
  replay (
          PHOLDS_ALLFALSE_NEGLIT)
  replay (
          PHOLDS_ALLTRUE_POSCLAUSE)
  replay (
          PHOLDS_ALLFALSE_NONPOSCLAUSE)
  replay (
          PRESOLUTION_LEMMA)
  replay (
          do IO.println pposresproof_RULES; IO.println pposresproof_INDUCT; IO.println pposresproof_CASES)
  replay (
          POSRESPROOF_FINITE)
  replay (
          PPOSRESPROOF_REFUTATION_COMPLETE_FINITE)
  replay (
          PPOSRESPROOF_MONO)
  replay (
          PPOSRESPROOF_REFUTATION_COMPLETE)
  replay (
          do IO.println psemresproof_RULES; IO.println psemresproof_INDUCT; IO.println psemresproof_CASES)
  replay (
          propflip)
  replay (
          PHOLDS_LITERAL_PROPFLIP)
  replay (
          PROPFLIP_INVOLUTE)
  replay (
          PROPFLIP_INJ)
  replay (
          PROPFLIP_NEGATE)
  replay (
          PROPFLIP_RESOLVE)
  replay (
          PPOSRESPROOF_CLAUSE)
  replay (
          PSEMRESPROOF_CLAUSE)
  replay (
          LITERAL_PROPFLIP)
  replay (
          CLAUSE_IMAGE_PROPFLIP)
  replay (
          PHOLDS_LITERAL_PROPFLIP_SAME)
  replay (
          PHOLDS_IMAGE_PROPFLIP_SAME)
  replay (
          PPOSRESPROOF_PSEMRESPROOF)
  replay (
          PHOLDS_ATOM_PROPFLIP_DIFF)
  replay (
          PHOLDS_LITERAL_PROPFLIP_DIFF)
  replay (
          PHOLDS_INTERP_IMAGE_PROPFLIP_DIFF)
  replay (
          PSATISFIABLE_CLAUSES_PROPFLIP)
  replay (
          PSEMRESPROOF_MONO)
  replay (
          PROPFLIP_INVOLUTE_CLAUSE)
  replay (
          PSEMRESPROOF_REFUTATION_COMPLETE)
  replay (
          do IO.println posresproof_RULES; IO.println posresproof_INDUCT; IO.println posresproof_CASES)
  replay (
          POSRESPROOF_CLAUSE)
  replay (
          ALLPOSITIVE_INSTANCE_OF)
  replay (
          POSRESOLUTION_COMPLETE)
  replay (
          do IO.println semresproof_RULES; IO.println semresproof_INDUCT; IO.println semresproof_CASES)
  replay (
          SEMRESPROOF_CLAUSE)
  replay (
          QFREE_HOLDS_PHOLDS)
  replay (
          LIFTING_FALSIFY)
  replay (
          LIFTING_FALSITY_CLAUSE)
  replay (
          SEMRESOLUTION_COMPLETE)
  replay (
          do IO.println semresproof2_RULES; IO.println semresproof2_INDUCT; IO.println semresproof2_CASES)
  replay (
          SEMRESPROOF2_CLAUSE)
  replay (
          QFREE_HOLDS_PHOLDS_2)
  replay (
          LIFTING_FALSIFY_2)
  replay (
          LIFTING_FALSITY_CLAUSE_2)
  replay (
          FUNCTIONS_FORM_INTERP)
  replay (
          FUNCTIONS_IMAGE_INTERP)
  replay (
          FUNCTIONS_RESOLVE)
  replay (
          PSEMRESPROOF_FUNCTIONS)
  replay (
          FUNCTIONS_TERM_NOCONSTANTS)
  replay (
          HERBASE)
  replay (
          HERBASE_LEMMA)
  replay (
          SEMRESOLUTION_COMPLETE_2)
-- @@ENSURE END

end HolLogicArith.Positive
