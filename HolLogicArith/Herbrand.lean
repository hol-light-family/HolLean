/- File: HolLogicArith/Herbrand.lean
Translation of HOL Light's Logic/herbrand.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolLogicArith.Canon
open HolCore.Kernel Session HolLight.Syntax HolLogicArith
open scoped HolLight
open HolLogicArith.Fol
open HolLogicArith.Prenex
open HolLogicArith.Skolem
open HolLogicArith.FolProp
open HolLogicArith.Canon

namespace HolLogicArith.Herbrand

/- List definitions/theorems used below are exposed by Session as fields of
   the `listDefs`/`listThms1` bundles; alias the ones we need. -/
private unsafe def LENGTH : thm := Session.listDefs.LENGTH
private unsafe def ALL : thm := Session.listDefs.ALL
private unsafe def MAP_EQ_DEGEN : thm := Session.listThms1.MAP_EQ_DEGEN
private unsafe def MEM_MAP : thm := Session.listThms1.MEM_MAP
private unsafe def ALL_MEM : thm := Session.listThms1.ALL_MEM
private unsafe def EX_MEM : thm := Session.listThms1.EX_MEM

#eval HolLogicArith.Canon.ensure

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
unsafe def herbase_triple : thm × thm × thm := keep "herbase_triple" fun _ =>
  newInductive
    [[(~(?c. (c,0) IN fns) ==> herbase fns (V 0)) /\
      (!f l. (f,LENGTH l) IN fns /\ ALL (herbase fns) l
             ==> herbase fns (Fn f l))]]
unsafe def herbase_RULES : thm := herbase_triple.1
unsafe def herbase_INDUCT : thm := herbase_triple.2.1
unsafe def herbase_CASES : thm := herbase_triple.2.2
#eval do IO.println herbase_RULES; IO.println herbase_INDUCT; IO.println herbase_CASES

#eval phrase 2
unsafe def herbrand : thm := keep "herbrand" fun _ => new_definition
  [[herbrand (L:(num#num->bool)#(num#num->bool)) M <=>
       (Dom M = herbase (FST L)) /\
       (!f. Fun(M) f = Fn f)]]
#eval herbrand

#eval phrase 3
unsafe def HERBRAND_INTERPRETATION : thm := keep "HERBRAND_INTERPRETATION" fun _ => (do
  prove ([[!L M. herbrand L M ==> interpretation L M]])
   (HolLight.GEN_REWRITE_TAC HolCore.Lib.I [FORALL_PAIR_THM] THEN
    SIMP_TAC [herbrand, interpretation] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC [IN] THEN CONV_TAC (HolLight.ONCE_DEPTH_CONV (fun t => pure (ETA_CONV t))) THEN
    ASM_SIMP_TAC [herbase_RULES])
  : ExceptT String IO thm).run
#eval HERBRAND_INTERPRETATION

#eval phrase 4
unsafe def HERBASE_FUNCTIONS : thm := keep "HERBASE_FUNCTIONS" fun _ => (do
  prove ([[!fns t. t IN herbase fns ==> (functions_term t) SUBSET fns]])
   (GEN_TAC THEN REWRITE_TAC [IN] THEN MATCH_MP_TAC herbase_INDUCT THEN
    REWRITE_TAC [functions_term, EMPTY_SUBSET] THEN
    REWRITE_TAC [SUBSET, IN_INSERT, IN_LIST_UNION, (← HolLight.GSYM ALL_MEM), (← HolLight.GSYM EX_MEM),
                MEM_MAP] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval HERBASE_FUNCTIONS

#eval phrase 5
unsafe def HERBASE_NONEMPTY : thm := keep "HERBASE_NONEMPTY" fun _ => (do
  prove ([[!fns. ?t. t IN herbase fns]])
   (GEN_TAC THEN REWRITE_TAC [IN] THEN ONCE_REWRITE_TAC [herbase_CASES] THEN
    MESON_TAC [ALL, LENGTH])
  : ExceptT String IO thm).run
#eval HERBASE_NONEMPTY

#eval phrase 6
unsafe def HERBRAND_NONEMPTY : thm := keep "HERBRAND_NONEMPTY" fun _ => (do
  prove ([[!L M. herbrand L M ==> ~(Dom M = {})]])
   (SIMP_TAC [herbrand, Dom_DEF, EXTENSION, NOT_IN_EMPTY] THEN
    REWRITE_TAC [NOT_FORALL_THM, HERBASE_NONEMPTY])
  : ExceptT String IO thm).run
#eval HERBRAND_NONEMPTY

#eval phrase 7
unsafe def herbrand_of_prop : thm := keep "herbrand_of_prop" fun _ => new_definition
  [[herbrand_of_prop (L:((num#num)->bool)#((num#num)->bool)) (d:form->bool) =
   herbase(FST L),Fn,\p l. d(Atom p l)]]
#eval herbrand_of_prop

#eval phrase 8
unsafe def PROP_OF_HERBRAND_OF_PROP : thm := keep "PROP_OF_HERBRAND_OF_PROP" fun _ => (do
  prove ([[!p l. prop_of_model (herbrand_of_prop L d) V (Atom p l) = d (Atom p l)]])
   (REWRITE_TAC [prop_of_model, herbrand_of_prop, holds, Pred_DEF] THEN
    REPEAT GEN_TAC THEN REPEAT AP_TERM_TAC THEN
    MATCH_MP_TAC MAP_EQ_DEGEN THEN
    SPEC_TAC ([[l:term list]], [[l:term list]]) THEN
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [ALL] THEN
    SPEC_TAC ([[h:term]], [[t:term]]) THEN
    MATCH_MP_TAC term_INDUCT THEN
    REWRITE_TAC [termval, Fun_DEF] THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC MAP_EQ_DEGEN THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval PROP_OF_HERBRAND_OF_PROP

#eval phrase 9
unsafe def HOLDS_HERBRAND_OF_PROP : thm := keep "HOLDS_HERBRAND_OF_PROP" fun _ => (do
  prove ([[!p. qfree p ==> (holds (herbrand_of_prop L d) V p <=> pholds d p)]])
   (GEN_TAC THEN DISCH_THEN (fun th => HolLight.tactic_of do
      let mmp ← HolLight.MATCH_MP PHOLDS_PROP_OF_MODEL th
      let g ← HolLight.GSYM mmp
      pure (MP_TAC th THEN REWRITE_TAC [g])) THEN
    SPEC_TAC ([[p:form]], [[p:form]]) THEN
    MATCH_MP_TAC form_INDUCTION THEN
    REWRITE_TAC [pholds, qfree, PROP_OF_HERBRAND_OF_PROP] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN (ANTE_RES_THEN SUBST1_TAC)) THEN REFL_TAC)
  : ExceptT String IO thm).run
#eval HOLDS_HERBRAND_OF_PROP

#eval phrase 10
unsafe def HOLDS_HERBRAND_OF_PROP_GENERAL : thm := keep "HOLDS_HERBRAND_OF_PROP_GENERAL" fun _ => (do
  prove ([[qfree p ==> (holds (herbrand_of_prop L d) v p <=> pholds d (formsubst v p))]])
   (DISCH_THEN (fun th => HolLight.tactic_of do
      let mmp ← HolLight.MATCH_MP PHOLDS_PROP_OF_MODEL th
      let g ← HolLight.GSYM mmp
      pure (MP_TAC th THEN REWRITE_TAC [g])) THEN
    SPEC_TAC ([[p:form]], [[p:form]]) THEN
    MATCH_MP_TAC form_INDUCTION THEN
    REWRITE_TAC [formsubst, pholds, qfree, PROP_OF_HERBRAND_OF_PROP] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THENL
     [ALL_TAC,
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      DISCH_THEN (CONJUNCTS_THEN (ANTE_RES_THEN SUBST1_TAC)) THEN
      REFL_TAC] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [prop_of_model, herbrand_of_prop, holds] THEN
    REWRITE_TAC [Pred_DEF] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [FUN_EQ_THM] THEN SIMP_TAC [(← HolLight.GSYM TERMSUBST_TERMVAL), Fun_DEF])
  : ExceptT String IO thm).run
#eval HOLDS_HERBRAND_OF_PROP_GENERAL

#eval phrase 11
unsafe def HERBRAND_HERBRAND_OF_PROP : thm := keep "HERBRAND_HERBRAND_OF_PROP" fun _ => (do
  prove ([[!d. herbrand L (herbrand_of_prop L d)]])
   (REWRITE_TAC [herbrand, herbrand_of_prop, Dom_DEF, Fun_DEF, FUN_EQ_THM])
  : ExceptT String IO thm).run
#eval HERBRAND_HERBRAND_OF_PROP

#eval phrase 12
unsafe def INTERPRETATION_HERBRAND_OF_PROP : thm := keep "INTERPRETATION_HERBRAND_OF_PROP" fun _ => (do
  prove ([[!L d. interpretation L (herbrand_of_prop L d)]])
   (REWRITE_TAC [FORALL_PAIR_THM, interpretation, herbrand_of_prop, Fun_DEF,
                Dom_DEF, IN, ETA_AX] THEN
    MESON_TAC [herbase_RULES, IN])
  : ExceptT String IO thm).run
#eval INTERPRETATION_HERBRAND_OF_PROP

#eval phrase 13
unsafe def PSATISFIES_HERBRAND_INSTANCES : thm := keep "PSATISFIES_HERBRAND_INSTANCES" fun _ => (do
  prove ([[(!p. p IN s ==> qfree p) /\
   d psatisfies {formsubst v p | (!x. v x IN herbase(FST L)) /\ p IN s}
   ==> (herbrand_of_prop L d) satisfies s]])
   (REWRITE_TAC [satisfies, psatisfies, IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
    STRIP_TAC THEN
    REPEAT GEN_TAC THEN HolLight.GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.TOP_DEPTH_CONV)
     [herbrand_of_prop, Dom_DEF, valuation] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [ [[formsubst v p]], [[v:num->term]], [[p:form]] ]) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[holds (herbrand_of_prop L d) V (formsubst v p)]]) MP_TAC THENL
     [ASM_MESON_TAC [HOLDS_HERBRAND_OF_PROP, QFREE_FORMSUBST], ALL_TAC] THEN
    SUBGOAL_THEN ([[holds (herbrand_of_prop L d) V (formsubst v p) <=>
                holds (herbrand_of_prop L d)
                      (termval (herbrand_of_prop L d) V o v)
                      p]])
    SUBST1_TAC THENL
     [REWRITE_TAC [HOLDS_FORMSUBST] THEN
      ASM_MESON_TAC [INTER_EMPTY, QFREE_BV_EMPTY],
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
      AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM, o_THM] THEN
      GEN_TAC THEN SPEC_TAC ([[(v:num->term) x]], [[t:term]]) THEN
      MATCH_MP_TAC TERMVAL_TRIV THEN
      REWRITE_TAC [herbrand_of_prop, Fun_DEF]])
  : ExceptT String IO thm).run
#eval PSATISFIES_HERBRAND_INSTANCES

#eval phrase 14
unsafe def SATISFIES_SUBSET : thm := keep "SATISFIES_SUBSET" fun _ => (do
  prove ([[!M s t. s SUBSET t /\ M satisfies t ==> M satisfies s]])
   (REWRITE_TAC [satisfies, SUBSET] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval SATISFIES_SUBSET

#eval phrase 15
unsafe def HERBASE_SUBSET_TERMS : thm := keep "HERBASE_SUBSET_TERMS" fun _ => (do
  prove ([[!t. t IN herbase fns ==> t IN terms fns]])
   (REWRITE_TAC [IN] THEN MATCH_MP_TAC herbase_INDUCT THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV (fun t => pure (ETA_CONV t))) THEN REWRITE_TAC [terms_RULES])
  : ExceptT String IO thm).run
#eval HERBASE_SUBSET_TERMS

#eval phrase 16
unsafe def HERBRAND_THEOREM : thm := keep "HERBRAND_THEOREM" fun _ => (do
  prove ([[!s. (!p. p IN s ==> qfree p)
       ==> ((?M:(term->bool)#(num->term list->term)#(num->term list->bool).
                 interpretation (language s) M /\ ~(Dom M = {}) /\
                 M satisfies s) <=>
            (?d. d psatisfies
                 {formsubst v p | (!x. v x IN herbase(functions s)) /\
                                  p IN s}))]])
   (GEN_TAC THEN DISCH_TAC THEN EQ_TAC THEN STRIP_TAC THENL
     [FIRST_ASSUM (X_CHOOSE_TAC ([[v:num->term]]) oTIO HolLight.MATCH_MP VALUATION_EXISTS) THEN
      EXISTS_TAC [[prop_of_model M (v:num->term)]] THEN
      MATCH_MP_TAC SATISFIES_PSATISFIES THEN ASM_REWRITE_TAC [] THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM, QFREE_FORMSUBST],
        FIRST_ASSUM (MP_TAC oTIO HolLight.MATCH_MP SATISFIES_INSTANCES) THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC [[s:form->bool]]) THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_CONJ]
                     SATISFIES_SUBSET) THEN
        REWRITE_TAC [SUBSET, IN_ELIM_THM, language] THEN
        MESON_TAC [HERBASE_SUBSET_TERMS, SUBSET]],
      EXISTS_TAC [[herbrand_of_prop (language s) d]] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC [INTERPRETATION_HERBRAND_OF_PROP],
        REWRITE_TAC [herbrand_of_prop, Dom_DEF, language,
                    EXTENSION, NOT_IN_EMPTY] THEN
        REWRITE_TAC [IN] THEN MESON_TAC [herbase_RULES, ALL, LENGTH],
        ASM_SIMP_TAC [PSATISFIES_HERBRAND_INSTANCES, language]]])
  : ExceptT String IO thm).run
#eval HERBRAND_THEOREM

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py from the `#eval`s above. -/
unsafe def ensure : IO Unit := once "HolLogicArith.Herbrand" do
  replay (
          HolLogicArith.Canon.ensure)
  replay (
          do IO.println herbase_RULES; IO.println herbase_INDUCT; IO.println herbase_CASES)
  replay (
          herbrand)
  replay (
          HERBRAND_INTERPRETATION)
  replay (
          HERBASE_FUNCTIONS)
  replay (
          HERBASE_NONEMPTY)
  replay (
          HERBRAND_NONEMPTY)
  replay (
          herbrand_of_prop)
  replay (
          PROP_OF_HERBRAND_OF_PROP)
  replay (
          HOLDS_HERBRAND_OF_PROP)
  replay (
          HOLDS_HERBRAND_OF_PROP_GENERAL)
  replay (
          HERBRAND_HERBRAND_OF_PROP)
  replay (
          INTERPRETATION_HERBRAND_OF_PROP)
  replay (
          PSATISFIES_HERBRAND_INSTANCES)
  replay (
          SATISFIES_SUBSET)
  replay (
          HERBASE_SUBSET_TERMS)
  replay (
          HERBRAND_THEOREM)
-- @@ENSURE END

end HolLogicArith.Herbrand
