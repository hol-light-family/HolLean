/- File: HolLogicArith/Canon.lean
Translation of HOL Light's Logic/canon.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolLogicArith.Skolem
import HolLogicArith.FolProp
open HolCore.Kernel Session HolLight.Syntax HolLogicArith
open scoped HolLight
open HolLogicArith.Fol
open HolLogicArith.Prenex
open HolLogicArith.Skolem
open HolLogicArith.FolProp

namespace HolLogicArith.Canon

/- List definitions/theorems used below are exposed by Session as fields of
   the `listDefs`/`listThms1` bundles; alias the ones we need. -/
private unsafe def HD : thm := Session.listDefs.HD
private unsafe def TL : thm := Session.listDefs.TL
private unsafe def REVERSE : thm := Session.listDefs.REVERSE
private unsafe def APPEND : thm := Session.listDefs.APPEND
private unsafe def LENGTH : thm := Session.listDefs.LENGTH
private unsafe def MAP : thm := Session.listDefs.MAP
private unsafe def ALL : thm := Session.listDefs.ALL
private unsafe def ITLIST : thm := Session.listDefs.ITLIST
private unsafe def MEM : thm := Session.listDefs.MEM
private unsafe def MAP2 : thm := Session.listDefs.MAP2
private unsafe def MAP2_DEF : thm := Session.listDefs.MAP2_DEF
private unsafe def MAP_EQ : thm := Session.listThms1.MAP_EQ
private unsafe def MAP_EQ_DEGEN : thm := Session.listThms1.MAP_EQ_DEGEN
private unsafe def MAP_o : thm := Session.listThms1.MAP_o
private unsafe def LENGTH_MAP : thm := Session.listThms1.LENGTH_MAP
private unsafe def ALL_T : thm := Session.listThms1.ALL_T
private unsafe def ALL_MAP : thm := Session.listThms1.ALL_MAP
private unsafe def ALL_IMP : thm := Session.listThms1.ALL_IMP
private unsafe def ITLIST_EXTRA : thm := Session.listThms1.ITLIST_EXTRA

#eval HolLogicArith.Skolem.ensure
#eval HolLogicArith.FolProp.ensure

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

/- `new_definition`. -/

#eval phrase 1
unsafe def terms_triple : thm × thm × thm := keep "terms_triple" fun _ =>
  newInductive
    [[(!x. terms fns (V x)) /\
      (!f l. (f,LENGTH l) IN fns /\ ALL (terms fns) l
             ==> terms fns (Fn f l))]]
unsafe def terms_RULES : thm := terms_triple.1
unsafe def terms_INDUCT : thm := terms_triple.2.1
unsafe def terms_CASES : thm := terms_triple.2.2
#eval do IO.println terms_RULES; IO.println terms_INDUCT; IO.println terms_CASES

#eval phrase 2
unsafe def STUPID_CANONDOM_LEMMA : thm := keep "STUPID_CANONDOM_LEMMA" fun _ => (do
  let lemma0 ← prove
   ([[a SUBSET s /\ b SUBSET s ==> (a UNION b) SUBSET s]]) (SET_TAC [])
  let lemma1 ← prove
   ([[a IN s /\ b SUBSET s ==> (a INSERT b) SUBSET s]]) (SET_TAC [])
  let lemma2 ← prove
   ([[!l. ALL (\x. x SUBSET s) l ==> LIST_UNION l SUBSET s]])
   (LIST_INDUCT_TAC THEN REWRITE_TAC [ALL, LIST_UNION, EMPTY_SUBSET] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma0 THEN ASM_MESON_TAC [])
  prove ([[!t. t IN terms(FST L) ==> functions_term t SUBSET (FST L)]])
   (REWRITE_TAC [IN] THEN MATCH_MP_TAC terms_INDUCT THEN
    REWRITE_TAC [functions_term, EMPTY_SUBSET] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma1 THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC lemma2 THEN
    ASM_REWRITE_TAC [ALL_MAP, o_DEF])
  : ExceptT String IO thm).run
#eval STUPID_CANONDOM_LEMMA

#eval phrase 3
unsafe def FINITE_SUBSET_INSTANCE : thm := keep "FINITE_SUBSET_INSTANCE" fun _ => (do
  prove ([[!t'. FINITE(t')
        ==> t' SUBSET { formsubst v p | P(v) /\ p IN s}
            ==> ?t. FINITE(t) /\ t SUBSET s /\
                    t' SUBSET {formsubst v p | P(v) /\ p IN t}]])
   (HolLight.tactic_of do
     let lemma ← prove
      ([[(a INSERT s) SUBSET t <=> a IN t /\ s SUBSET t]]) (SET_TAC [])
     pure
      (MATCH_MP_TAC FINITE_INDUCT THEN CONJ_TAC THENL
        [REWRITE_TAC [EMPTY_SUBSET] THEN
         EXISTS_TAC [[EMPTY:form->bool]] THEN
         REWRITE_TAC [FINITE_RULES, EMPTY_SUBSET],
         REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [lemma] THEN
         DISCH_THEN (fun th => STRIP_ASSUME_TAC th THEN
                              (ANTE_RES_THEN MP_TAC oT Session.CONJUNCT2) th) THEN
         DISCH_THEN (X_CHOOSE_THEN ([[t0:form->bool]]) STRIP_ASSUME_TAC) THEN
         EXISTS_TAC [[(@p. ?v. (P v /\ p IN s) /\ (x = formsubst v p)) INSERT t0]] THEN
         ASM_REWRITE_TAC [FINITE_INSERT, lemma] THEN
         FIRST_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [IN]) THEN
         DISCH_THEN (MP_TAC o HolLight.REWRITE_RULE [IN_ELIM_THM]) THEN
         ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
         DISCH_THEN (MP_TAC oT Session.SELECT_RULE) THEN
         DISCH_THEN (X_CHOOSE_THEN ([[v:num->term]]) MP_TAC) THEN
         SPEC_TAC ([[@p. ?v. (P v /\ p IN s) /\ (x = formsubst v p)]], [[q:form]]) THEN
         UNDISCH_TAC [[s' SUBSET {formsubst v p | P v /\ p IN t0}]] THEN
         UNDISCH_TAC [[x IN {formsubst v p | P v /\ p IN s}]] THEN
         REWRITE_TAC [SUBSET, IN_ELIM_THM, IN_INSERT] THEN MESON_TAC []]))
  : ExceptT String IO thm).run
#eval FINITE_SUBSET_INSTANCE

#eval phrase 4
unsafe def FINITE_SUBSET_SKOLEM : thm := keep "FINITE_SUBSET_SKOLEM" fun _ => (do
  prove ([[!s u. FINITE(u)
        ==> u SUBSET { SKOLEM p | p IN s}
            ==> ?t. FINITE(t) /\ t SUBSET s /\
                    (u = {SKOLEM p | p IN t})]])
   (HolLight.tactic_of do
     let lemma ← prove
      ([[(a INSERT s) SUBSET t <=> a IN t /\ s SUBSET t]]) (SET_TAC [])
     let lemma2 ← prove
      ([[{SKOLEM p | p IN x INSERT s} =
         (SKOLEM x) INSERT {SKOLEM p | p IN s}]])
      (REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_INSERT] THEN SET_TAC [])
     pure
      (GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT THEN CONJ_TAC THENL
        [REWRITE_TAC [EMPTY_SUBSET] THEN
         EXISTS_TAC [[EMPTY:form->bool]] THEN
         REWRITE_TAC [FINITE_RULES, EMPTY_SUBSET, NOT_IN_EMPTY] THEN
         REWRITE_TAC [EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY], ALL_TAC] THEN
       REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [lemma] THEN
       DISCH_THEN (fun th => STRIP_ASSUME_TAC th THEN
                            (ANTE_RES_THEN MP_TAC oT Session.CONJUNCT2) th) THEN
       DISCH_THEN (X_CHOOSE_THEN ([[t0:form->bool]]) STRIP_ASSUME_TAC) THEN
       EXISTS_TAC [[(@p. p IN s /\ (x = SKOLEM p)) INSERT t0]] THEN
       ASM_REWRITE_TAC [FINITE_INSERT, lemma] THEN
       FIRST_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [IN]) THEN
       DISCH_THEN (MP_TAC o HolLight.REWRITE_RULE [IN_ELIM_THM]) THEN
       DISCH_THEN (MP_TAC oT Session.SELECT_RULE) THEN STRIP_TAC THEN
       ASM_REWRITE_TAC [lemma2] THEN
       REPEAT (FIRST_X_ASSUM (SUBST_ALL_TAC oTIO HolLight.SYM)) THEN REFL_TAC))
  : ExceptT String IO thm).run
#eval FINITE_SUBSET_SKOLEM

#eval phrase 5
unsafe def VALUATION_EXISTS : thm := keep "VALUATION_EXISTS" fun _ => (do
  prove ([[!M. ~(Dom(M) = EMPTY) ==> ?v:num->A. valuation(M) v]])
   (GEN_TAC THEN REWRITE_TAC [(← HolLight.GSYM MEMBER_NOT_EMPTY)] THEN
    DISCH_THEN (X_CHOOSE_TAC [[a:A]]) THEN
    EXISTS_TAC [[\x:num. a:A]] THEN
    ASM_REWRITE_TAC [valuation])
  : ExceptT String IO thm).run
#eval VALUATION_EXISTS

#eval phrase 6
unsafe def HOLDS_ITLIST_EXISTS : thm := keep "HOLDS_ITLIST_EXISTS" fun _ => (do
  prove ([[!M xs v. holds M v (ITLIST ?? xs p) <=>
            ?as. (LENGTH as = LENGTH xs) /\
                 ALL (Dom M) as /\
                 holds M
                   (ITLIST valmod (REVERSE (MAP2 (\x a:A. (x,a)) xs as)) v)
                   p]])
   (GEN_TAC THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [HOLDS, LENGTH, ITLIST, MAP2_DEF, HD,
                  TL, REVERSE, APPEND] THENL
     [MESON_TAC [ALL, LENGTH], REWRITE_TAC [ITLIST_EXTRA, IN]] THEN
    GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_THEN ([[a:A]]) (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[as:A list]]) STRIP_ASSUME_TAC) THEN
      EXISTS_TAC [[CONS (a:A) as]] THEN ASM_REWRITE_TAC [ALL, TL, HD, LENGTH],
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH, NOT_SUC] THEN
      REWRITE_TAC [ALL, SUC_INJ, HD, TL] THEN MESON_TAC []])
  : ExceptT String IO thm).run
#eval HOLDS_ITLIST_EXISTS

#eval phrase 7
unsafe def canonical : thm := keep "canonical" fun _ => new_definition
  [[canonical (L:(num#num->bool)#(num#num->bool)) M <=>
       (Dom M = terms (FST L)) /\
       (!f. Fun(M) f = Fn f)]]
#eval canonical

#eval phrase 8
unsafe def prop_of_model : thm := keep "prop_of_model" fun _ => new_definition
  [[prop_of_model M v (Atom p l) <=> holds M v (Atom p l)]]
#eval prop_of_model

#eval phrase 9
unsafe def canon_of_prop : thm := keep "canon_of_prop" fun _ => new_definition
  [[canon_of_prop (L:((num#num)->bool)#((num#num)->bool)) (d:form->bool) =
   terms(FST L),Fn,\p l. d(Atom p l)]]
#eval canon_of_prop

#eval phrase 10
unsafe def PHOLDS_PROP_OF_MODEL : thm := keep "PHOLDS_PROP_OF_MODEL" fun _ => (do
  prove ([[!p. qfree(p) ==> (pholds (prop_of_model M v) p <=> holds M v p)]])
   (MATCH_MP_TAC form_INDUCTION THEN
    REWRITE_TAC [qfree, holds, pholds] THEN CONJ_TAC THENL
     [REWRITE_TAC [prop_of_model, holds],
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      DISCH_THEN (CONJUNCTS_THEN (ANTE_RES_THEN SUBST1_TAC)) THEN REFL_TAC])
  : ExceptT String IO thm).run
#eval PHOLDS_PROP_OF_MODEL

#eval phrase 11
unsafe def PROP_OF_CANON_OF_PROP : thm := keep "PROP_OF_CANON_OF_PROP" fun _ => (do
  prove ([[!p l. prop_of_model (canon_of_prop L d) V (Atom p l) = d (Atom p l)]])
   (REWRITE_TAC [prop_of_model, canon_of_prop, holds, Pred_DEF] THEN
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
#eval PROP_OF_CANON_OF_PROP

#eval phrase 12
unsafe def HOLDS_CANON_OF_PROP : thm := keep "HOLDS_CANON_OF_PROP" fun _ => (do
  prove ([[!p. qfree p ==> (holds (canon_of_prop L d) V p <=> pholds d p)]])
   (GEN_TAC THEN DISCH_THEN (fun th => HolLight.tactic_of do
      let mmp ← HolLight.MATCH_MP PHOLDS_PROP_OF_MODEL th
      let g ← HolLight.GSYM mmp
      pure (MP_TAC th THEN REWRITE_TAC [g])) THEN
    SPEC_TAC ([[p:form]], [[p:form]]) THEN
    MATCH_MP_TAC form_INDUCTION THEN
    REWRITE_TAC [pholds, qfree, PROP_OF_CANON_OF_PROP] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN (ANTE_RES_THEN SUBST1_TAC)) THEN REFL_TAC)
  : ExceptT String IO thm).run
#eval HOLDS_CANON_OF_PROP

#eval phrase 13
unsafe def HOLDS_CANON_OF_PROP_GENERAL : thm := keep "HOLDS_CANON_OF_PROP_GENERAL" fun _ => (do
  prove ([[qfree p ==> (holds (canon_of_prop L d) v p <=> pholds d (formsubst v p))]])
   (DISCH_THEN (fun th => HolLight.tactic_of do
      let mmp ← HolLight.MATCH_MP PHOLDS_PROP_OF_MODEL th
      let g ← HolLight.GSYM mmp
      pure (MP_TAC th THEN REWRITE_TAC [g])) THEN
    SPEC_TAC ([[p:form]], [[p:form]]) THEN
    MATCH_MP_TAC form_INDUCTION THEN
    REWRITE_TAC [formsubst, pholds, qfree, PROP_OF_CANON_OF_PROP] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THENL
     [ALL_TAC,
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      DISCH_THEN (CONJUNCTS_THEN (ANTE_RES_THEN SUBST1_TAC)) THEN
      REFL_TAC] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [prop_of_model, canon_of_prop, holds] THEN
    REWRITE_TAC [Pred_DEF] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [FUN_EQ_THM] THEN SIMP_TAC [(← HolLight.GSYM TERMSUBST_TERMVAL), Fun_DEF])
  : ExceptT String IO thm).run
#eval HOLDS_CANON_OF_PROP_GENERAL

#eval phrase 14
unsafe def CANONICAL_CANON_OF_PROP : thm := keep "CANONICAL_CANON_OF_PROP" fun _ => (do
  prove ([[!d. canonical L (canon_of_prop L d)]])
   (REWRITE_TAC [canonical, canon_of_prop, Dom_DEF, Fun_DEF, FUN_EQ_THM])
  : ExceptT String IO thm).run
#eval CANONICAL_CANON_OF_PROP

#eval phrase 15
unsafe def INTERPRETATION_CANON_OF_PROP : thm := keep "INTERPRETATION_CANON_OF_PROP" fun _ => (do
  prove ([[!L d. interpretation L (canon_of_prop L d)]])
   (REWRITE_TAC [FORALL_PAIR_THM, IN, ETA_AX,
              interpretation, canon_of_prop, Fun_DEF, Dom_DEF] THEN
    MESON_TAC [terms_RULES, IN])
  : ExceptT String IO thm).run
#eval INTERPRETATION_CANON_OF_PROP

#eval phrase 16
unsafe def PROP_VALID_IMP_FOL_VALID : thm := keep "PROP_VALID_IMP_FOL_VALID" fun _ => (do
  prove ([[!p. qfree(p) /\ (!d. pholds d p) ==> !M v. holds M v p]])
   (MESON_TAC [PHOLDS_PROP_OF_MODEL])
  : ExceptT String IO thm).run
#eval PROP_VALID_IMP_FOL_VALID

#eval phrase 17
unsafe def FOL_VALID_IMP_PROP_VALID : thm := keep "FOL_VALID_IMP_PROP_VALID" fun _ => (do
  prove ([[!p. qfree(p) /\
       (!C (v:num->term). canonical(language {p}) C ==> holds C v p)
       ==> !d. pholds d p]])
   (MESON_TAC [CANONICAL_CANON_OF_PROP, HOLDS_CANON_OF_PROP])
  : ExceptT String IO thm).run
#eval FOL_VALID_IMP_PROP_VALID

#eval phrase 18
unsafe def SATISFIES_PSATISFIES : thm := keep "SATISFIES_PSATISFIES" fun _ => (do
  prove ([[(!p. p IN s ==> qfree p) /\ M satisfies s /\ valuation(M) v
   ==> (prop_of_model M v) psatisfies s]])
   (REWRITE_TAC [satisfies, psatisfies] THEN MESON_TAC [PHOLDS_PROP_OF_MODEL])
  : ExceptT String IO thm).run
#eval SATISFIES_PSATISFIES

#eval phrase 19
unsafe def PSATISFIES_INSTANCES : thm := keep "PSATISFIES_INSTANCES" fun _ => (do
  prove ([[(!p. p IN s ==> qfree p) /\
   d psatisfies {formsubst v p | (!x. v x IN terms(FST L)) /\ p IN s}
   ==> (canon_of_prop L d) satisfies s]])
   (REWRITE_TAC [satisfies, psatisfies, IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
    STRIP_TAC THEN
    REPEAT GEN_TAC THEN HolLight.GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.TOP_DEPTH_CONV)
     [canon_of_prop, Dom_DEF, valuation] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [ [[formsubst v p]], [[v:num->term]], [[p:form]] ]) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[holds (canon_of_prop L d) V (formsubst v p)]]) MP_TAC THENL
     [ASM_MESON_TAC [HOLDS_CANON_OF_PROP, QFREE_FORMSUBST], ALL_TAC] THEN
    SUBGOAL_THEN ([[holds (canon_of_prop L d) V (formsubst v p) <=>
                holds (canon_of_prop L d) (termval (canon_of_prop L d) V o v)
                      p]])
    SUBST1_TAC THENL
     [REWRITE_TAC [HOLDS_FORMSUBST] THEN
      ASM_MESON_TAC [INTER_EMPTY, QFREE_BV_EMPTY],
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
      AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM, o_THM] THEN
      GEN_TAC THEN SPEC_TAC ([[(v:num->term) x]], [[t:term]]) THEN
      MATCH_MP_TAC TERMVAL_TRIV THEN
      REWRITE_TAC [canon_of_prop, Fun_DEF]])
  : ExceptT String IO thm).run
#eval PSATISFIES_INSTANCES

#eval phrase 20
unsafe def SATISFIES_INSTANCES : thm := keep "SATISFIES_INSTANCES" fun _ => (do
  prove ([[!M:(A->bool)#(num->A list->A)#(num->A list->bool) s t.
        interpretation(language t) M
        ==> (M satisfies
             {formsubst i p | p IN s /\
                              (!x. i x IN terms(FST(language t)))} <=>
             M satisfies s)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [satisfies, IN_ELIM_THM] THEN
    EQ_TAC THEN REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC [FORMSUBST_TRIV, terms_RULES, IN], ALL_TAC] THEN
    ASM_REWRITE_TAC [HOLDS_FORMSUBST] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [valuation, o_THM] THEN GEN_TAC THEN
    MATCH_MP_TAC INTERPRETATION_TERMVAL THEN
    EXISTS_TAC [[predicates t]] THEN ASM_REWRITE_TAC [] THEN
    UNDISCH_TAC [[interpretation (language t)
                (M:(A->bool)#(num->A list->A)#(num->A list->bool))]] THEN
    REWRITE_TAC [language] THEN MATCH_MP_TAC INTERPRETATION_SUBLANGUAGE THEN
    SUBGOAL_THEN ([[functions t = FST(language t)]]) SUBST1_TAC THENL
     [REWRITE_TAC [language], ALL_TAC] THEN
    MATCH_MP_TAC STUPID_CANONDOM_LEMMA THEN
    ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval SATISFIES_INSTANCES

#eval phrase 21
unsafe def COMPACT_CANON_QFREE : thm := keep "COMPACT_CANON_QFREE" fun _ => (do
  prove ([[(!p. p IN s ==> qfree p) /\
   (!t. FINITE t /\ t SUBSET s ==> ?M. interpretation(language ss) M /\
                                       ~(Dom(M):A->bool = EMPTY) /\
                                       M satisfies t)
   ==> ?C. interpretation (language ss) C /\
           canonical (language ss) C /\
           C satisfies s]])
   (HolLight.tactic_of do
     let satInst ← liftExcept (Session.SPEC_VAR SATISFIES_INSTANCES)
     pure
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN
        ([[psatisfiable {formsubst v p | (!x. v x IN terms(FST(language ss))) /\
                                  p IN s}]])
       MP_TAC THENL
        [REWRITE_TAC [psatisfiable] THEN MATCH_MP_TAC COMPACT_PROP THEN
         REWRITE_TAC [(← HolLight.GSYM psatisfiable)] THEN
         X_GEN_TAC [[u:form->bool]] THEN STRIP_TAC THEN
         SUBGOAL_THEN
          ([[?t. FINITE(t) /\ t SUBSET s /\
          u SUBSET {formsubst v p |
                              (!x. v x IN terms (FST (language ss))) /\
                                    p IN t}]])
         STRIP_ASSUME_TAC THENL
          [MATCH_MP_TAC (← (do
             let taut ← ExceptT.mk (TAUT [[(a ==> b ==> c) <=> a /\ b ==> c]])
             let ga ← HolLight.GEN_ALL FINITE_SUBSET_INSTANCE
             HolLight.REWRITE_RULE [taut] ga)) THEN
           ASM_REWRITE_TAC [], ALL_TAC] THEN
         MATCH_MP_TAC SATISFIABLE_MONO THEN
         EXISTS_TAC [[{formsubst v p |
                          (!x. v x IN terms (FST (language ss))) /\
                          p IN t}]] THEN
         ASM_REWRITE_TAC [] THEN
         FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[t:form->bool]]) THEN ASM_REWRITE_TAC [] THEN
         STRIP_TAC THEN
         FIRST_ASSUM (CHOOSE_TAC oTIO HolLight.MATCH_MP VALUATION_EXISTS) THEN
         MP_TAC (← (do
           let s1 ← HolLight.SPEC ([[t:form->bool]]) satInst.2
           HolLight.SPEC ([[ss:form->bool]]) s1)) THEN
         ASM_REWRITE_TAC [] THEN
         SUBGOAL_THEN ([[!p. p IN t ==> qfree p]]) (fun th => REWRITE_TAC [th]) THENL
          [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN DISCH_TAC THEN
         REWRITE_TAC [psatisfiable] THEN
         EXISTS_TAC [[prop_of_model M (v:num->A)]] THEN
         REWRITE_TAC [(← HolLight.GSYM psatisfies)] THEN
         MATCH_MP_TAC SATISFIES_PSATISFIES THEN ASM_REWRITE_TAC [] THEN
         CONJ_TAC THENL
          [REWRITE_TAC [IN_ELIM_THM] THEN
           REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [QFREE_FORMSUBST] THEN
           ASM_MESON_TAC [SUBSET],
           RULE_ASSUM_TAC (HolLight.REWRITE_RULE [CONJ_ACI]) THEN
           ASM_REWRITE_TAC [CONJ_ACI]], ALL_TAC] THEN
       REWRITE_TAC [psatisfiable, (← HolLight.GSYM psatisfies)] THEN
       DISCH_THEN (X_CHOOSE_THEN ([[d:form->bool]]) ASSUME_TAC) THEN
       EXISTS_TAC [[canon_of_prop (language ss) d]] THEN
       REWRITE_TAC [CANONICAL_CANON_OF_PROP, INTERPRETATION_CANON_OF_PROP] THEN
       MATCH_MP_TAC PSATISFIES_INSTANCES THEN ASM_REWRITE_TAC []))
  : ExceptT String IO thm).run
#eval COMPACT_CANON_QFREE

#eval phrase 22
unsafe def INTERPRETATION_RESTRICTLANGUAGE : thm := keep "INTERPRETATION_RESTRICTLANGUAGE" fun _ => (do
  prove ([[!M s t. t SUBSET s /\ interpretation(language s) M
         ==> interpretation(language t) M]])
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [IMP_CONJ] THEN
    DISCH_TAC THEN
    REWRITE_TAC [language] THEN
    MATCH_MP_TAC INTERPRETATION_SUBLANGUAGE THEN
    REWRITE_TAC [functions] THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC [SUBSET, IN_ELIM_THM, IN_UNIONS] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval INTERPRETATION_RESTRICTLANGUAGE

#eval phrase 23
unsafe def INTERPRETATION_EXTENDLANGUAGE : thm := keep "INTERPRETATION_EXTENDLANGUAGE" fun _ => (do
  prove ([[!M s t.
        interpretation (language t) M /\
        ~(Dom M :A->bool = EMPTY) /\
        M satisfies t
        ==> ?M'. (Dom M' = Dom M) /\
                 (Pred M' = Pred M) /\
                 interpretation(language s) M' /\
                 M' satisfies t]])
   (REPEAT STRIP_TAC THEN
    EXISTS_TAC [[Dom(M):A->bool,
              (\g zs. if (g,LENGTH zs) IN functions t then Fun(M) g zs
                      else @a. a IN Dom(M)),
              Pred(M)]] THEN
    REWRITE_TAC [Dom_DEF, Fun_DEF, Pred_DEF, interpretation, language] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THENL
       [FIRST_ASSUM (MATCH_MP_TAC o HolLight.REWRITE_RULE [language, interpretation]) THEN
        ASM_REWRITE_TAC [],
        CONV_TAC (fun t => pure (SELECT_CONV t)) THEN ASM_REWRITE_TAC [MEMBER_NOT_EMPTY]],
      FIRST_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [satisfies]) THEN
      REWRITE_TAC [satisfies] THEN
      REWRITE_TAC [valuation, Dom_DEF] THEN
      MATCH_MP_TAC EQ_IMP THEN
      AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
      MATCH_MP_TAC (← ExceptT.mk (TAUT [[(a ==> (b <=> c)) ==> ((a ==> b) <=> (a ==> c))]])) THEN
      STRIP_TAC THEN SPEC_TAC ([[v:num->A]], [[v:num->A]]) THEN
      MATCH_MP_TAC HOLDS_FUNCTIONS THEN
      REWRITE_TAC [Dom_DEF, Fun_DEF, Pred_DEF] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC [] THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [functions, IN_UNIONS, IN_ELIM_THM]) THEN
      ASM_MESON_TAC []])
  : ExceptT String IO thm).run
#eval INTERPRETATION_EXTENDLANGUAGE

#eval phrase 24
unsafe def COMPACT_LS : thm := keep "COMPACT_LS" fun _ => (do
  prove ([[(!t. FINITE t /\ t SUBSET s ==> ?M. interpretation(language s) M /\
                                       ~(Dom(M):A->bool = EMPTY) /\
                                       M satisfies t)
   ==> ?C. interpretation (language s) C /\
           ~(Dom(C):term->bool = EMPTY) /\
           C satisfies s]])
   (HolLight.tactic_of do
     let lemma ← prove
      ([[(!y. p y ==> p' y)
         ==> (?x. p x) ==> (?x. p' x)]])
      (MESON_TAC [])
     pure
      (REPEAT STRIP_TAC THEN
       SUBGOAL_THEN
        ([[!u. FINITE u /\ u SUBSET {SKOLEM p | p IN s}
        ==> ?M. interpretation(language {SKOLEM p | p IN s}) M /\
                ~(Dom(M):A->bool = EMPTY) /\
                M satisfies u]])
       ASSUME_TAC THENL
        [REPEAT STRIP_TAC THEN
         SUBGOAL_THEN ([[?t. (u = {SKOLEM p | p IN t}) /\
                      FINITE t /\ t SUBSET s]])
         (CHOOSE_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)) THENL
          [MP_TAC (← HolLight.SPECL [ [[s:form->bool]], [[u:form->bool]] ] FINITE_SUBSET_SKOLEM) THEN
           ASM_REWRITE_TAC [CONJ_ACI], ALL_TAC] THEN
         FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[t:form->bool]]) THEN ASM_REWRITE_TAC [] THEN
         DISCH_THEN (X_CHOOSE_THEN
          ([[M:(A->bool)#(num->A list->A)#(num->A list->bool)]])
          STRIP_ASSUME_TAC) THEN
         SUBGOAL_THEN
          ([[(?M. ~(Dom M:A->bool = EMPTY) /\
           interpretation(language t) M /\
           M satisfies t)]])
         (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [SKOLEM_SATISFIABLE]) THENL
          [EXISTS_TAC [[M:(A->bool)#(num->A list->A)#(num->A list->bool)]] THEN
           ASM_REWRITE_TAC [] THEN
           MATCH_MP_TAC INTERPRETATION_RESTRICTLANGUAGE THEN
           EXISTS_TAC [[s:form->bool]] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
         DISCH_THEN (X_CHOOSE_THEN
          ([[M0:(A->bool)#(num->A list->A)#(num->A list->bool)]])
          STRIP_ASSUME_TAC) THEN
         MP_TAC (← HolLight.ISPEC ([[M0:(A->bool)#(num->A list->A)#(num->A list->bool)]])
           INTERPRETATION_EXTENDLANGUAGE) THEN
         DISCH_THEN (MP_TAC o HolLight.SPECL
          [ [[{SKOLEM p | p IN s}]], [[{SKOLEM p | p IN t}]] ]) THEN
         ASM_REWRITE_TAC [] THEN
         DISCH_THEN (X_CHOOSE_THEN
          ([[M1:(A->bool)#(num->A list->A)#(num->A list->bool)]])
          STRIP_ASSUME_TAC) THEN
         EXISTS_TAC [[M1:(A->bool)#(num->A list->A)#(num->A list->bool)]] THEN
         ASM_REWRITE_TAC [], ALL_TAC] THEN
       MP_TAC (← liftExcept (HolCore.Kernel.INST [([[{SKOLEM p | p IN s}]], [[s:form->bool]]),
                    ([[{SKOLEM p | p IN s}]], [[ss:form->bool]])]
                   COMPACT_CANON_QFREE)) THEN
       ASM_REWRITE_TAC [] THEN
       HolCore.Lib.W (fun g => HolLight.tactic_of do
         let t ← liftExcept (HolCore.Lib.funpow 2 (fun (m : Except String term) => do HolCore.Equal.lhand (← m)) (pure (HolLight.snd g)))
         pure (HolCore.Lib.C SUBGOAL_THEN (fun th => REWRITE_TAC [th]) t)) THENL
        [REWRITE_TAC [IN_ELIM_THM] THEN
         REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [SKOLEM_QFREE], ALL_TAC] THEN
       ONCE_REWRITE_TAC [(← ExceptT.mk (Session.AC CONJ_ACI [[a /\ b /\ c <=> b /\ a /\ c]]))] THEN
       HolLight.GEN_REWRITE_TAC HolLight.RAND_CONV [SKOLEM_SATISFIABLE] THEN
       MATCH_MP_TAC lemma THEN REWRITE_TAC [canonical] THEN
       GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
       REWRITE_TAC [EXTENSION, NOT_IN_EMPTY, IN] THEN
       MESON_TAC [terms_RULES]))
  : ExceptT String IO thm).run
#eval COMPACT_LS

#eval phrase 25
unsafe def CANON : thm := keep "CANON" fun _ => (do
  prove ([[!M:(A->bool)#(num->A list->A)#(num->A list->bool) s.
        interpretation (language s) M /\
        ~(Dom(M) = EMPTY) /\
        (!p. p IN s ==> qfree p) /\ M satisfies s
        ==> ?C. interpretation (language s) C /\
                ~(Dom C :term->bool = EMPTY) /\
                C satisfies s]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_LS THEN
    ASM_MESON_TAC [satisfies, SUBSET])
  : ExceptT String IO thm).run
#eval CANON

#eval phrase 26
unsafe def term_of_num : thm := keep "term_of_num" fun _ => new_definition
  [[term_of_num n = (@t. num_of_term t = n)]]
#eval term_of_num

#eval phrase 27
unsafe def TERM_OF_NUM : thm := keep "TERM_OF_NUM" fun _ => (do
  prove ([[term_of_num(num_of_term t) = t]])
   (REWRITE_TAC [term_of_num, NUM_OF_TERM_INJ])
  : ExceptT String IO thm).run
#eval TERM_OF_NUM

#eval phrase 28
unsafe def LOWMOD : thm := keep "LOWMOD" fun _ => new_definition
  [[LOWMOD M = {num_of_term t | t IN Dom(M)},
              (\g zs. num_of_term (Fun(M) g (MAP term_of_num zs))),
              (\p zs. Pred(M) p (MAP term_of_num zs))]]
#eval LOWMOD

#eval phrase 29
unsafe def LOWMOD_DOM_EMPTY : thm := keep "LOWMOD_DOM_EMPTY" fun _ => (do
  prove ([[(Dom(LOWMOD M) = EMPTY) <=> (Dom(M) = EMPTY)]])
   (REWRITE_TAC [Dom_DEF, LOWMOD, EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval LOWMOD_DOM_EMPTY

#eval phrase 30
unsafe def LOWMOD_TERMVAL : thm := keep "LOWMOD_TERMVAL" fun _ => (do
  prove ([[!v. valuation (LOWMOD M) v
       ==> !t. termval (LOWMOD M) v t =
               num_of_term (termval M (term_of_num o v) t)]])
   (GEN_TAC THEN DISCH_THEN
     (ASSUME_TAC o HolLight.REWRITE_RULE [valuation, LOWMOD, Dom_DEF, IN_ELIM_THM]) THEN
    MATCH_MP_TAC term_INDUCT THEN  REWRITE_TAC [termval, o_THM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC [TERM_OF_NUM], ALL_TAC] THEN
    REWRITE_TAC [LOWMOD, Fun_DEF] THEN REWRITE_TAC [(← HolLight.GSYM LOWMOD)] THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [(← HolLight.GSYM MAP_o)] THEN MATCH_MP_TAC MAP_EQ THEN
    MATCH_MP_TAC ALL_IMP THEN
    FIRST_ASSUM (EXISTS_TAC o HolCore.Equal.lhand o concl) THEN
    ASM_REWRITE_TAC [] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [o_THM, TERM_OF_NUM])
  : ExceptT String IO thm).run
#eval LOWMOD_TERMVAL

#eval phrase 31
unsafe def LOWMOD_HOLDS : thm := keep "LOWMOD_HOLDS" fun _ => (do
  prove ([[!p v. valuation (LOWMOD M) v
         ==> (holds (LOWMOD M) v p <=> holds M (term_of_num o v) p)]])
   (MATCH_MP_TAC form_INDUCTION THEN
    REWRITE_TAC [holds] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC [LOWMOD, Pred_DEF] THEN
      REWRITE_TAC [(← HolLight.GSYM LOWMOD)] THEN AP_TERM_TAC THEN
      REWRITE_TAC [(← HolLight.GSYM MAP_o)] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC [FUN_EQ_THM, o_THM] THEN
      ASM_SIMP_TAC [LOWMOD_TERMVAL, TERM_OF_NUM],
      MESON_TAC [],
      REPEAT STRIP_TAC THEN
      REWRITE_TAC [Dom_DEF, LOWMOD] THEN REWRITE_TAC [(← HolLight.GSYM LOWMOD)] THEN
      SUBGOAL_THEN ([[!a. a IN {num_of_term t | t IN Dom M}
                      ==> valuation (LOWMOD M) (valmod (a0:num,a) v)]])
      MP_TAC THENL
       [GEN_TAC THEN REWRITE_TAC [valuation, valmod, LOWMOD, Dom_DEF] THEN
        CONV_TAC (HolLight.ONCE_DEPTH_CONV COND_ELIM_CONV) THEN
        REWRITE_TAC [IN_ELIM_THM] THEN
        RULE_ASSUM_TAC (HolLight.REWRITE_RULE [valuation, LOWMOD, Dom_DEF, IN_ELIM_THM]) THEN
        ASM_MESON_TAC [], ALL_TAC] THEN
      DISCH_THEN (fun th => ASM_SIMP_TAC [th]) THEN
      SUBGOAL_THEN ([[!P. (!a. a IN {num_of_term t | t IN Dom(M)} ==> P(a)) <=>
                      (!a. a IN Dom(M) ==> P(num_of_term a))]])
       (fun th => REWRITE_TAC [th])
      THENL [REWRITE_TAC [IN_ELIM_THM] THEN MESON_TAC [], ALL_TAC] THEN
      AP_TERM_TAC THEN ABS_TAC THEN
      MATCH_MP_TAC (← ExceptT.mk (TAUT [[(a ==> (b <=> c)) ==> ((a ==> b) <=> (a ==> c))]])) THEN
      DISCH_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC [valmod, FUN_EQ_THM, o_THM] THEN
      GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [TERM_OF_NUM]])
  : ExceptT String IO thm).run
#eval LOWMOD_HOLDS

#eval phrase 32
unsafe def LOWMOD_INTERPRETATION : thm := keep "LOWMOD_INTERPRETATION" fun _ => (do
  prove ([[!L M. interpretation L (LOWMOD M) = interpretation L M]])
   (REWRITE_TAC [FORALL_PAIR_THM, interpretation] THEN
    REWRITE_TAC [Fun_DEF, Dom_DEF, LOWMOD] THEN
    SUBGOAL_THEN ([[!P x. num_of_term x IN {num_of_term y | P y} <=> x IN P]])
     (fun th => REWRITE_TAC [th]) THENL
     [REWRITE_TAC [IN_ELIM_THM, IN, NUM_OF_TERM_INJ] THEN MESON_TAC [],
      ALL_TAC] THEN
    REPEAT GEN_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
    EQ_TAC THEN DISCH_TAC THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [ALL, MAP, LENGTH] THENL
     [DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[[] :num list]]) THEN
      ASM_REWRITE_TAC [ALL, MAP, LENGTH] THEN
      REWRITE_TAC [IN] THEN CONV_TAC (HolLight.ONCE_DEPTH_CONV (fun t => pure (ETA_CONV t))),
      STRIP_TAC THEN FIRST_X_ASSUM
       (MP_TAC o HolLight.SPEC [[CONS (num_of_term h) (MAP num_of_term t)]]) THEN
      ASM_REWRITE_TAC [ALL, MAP, LENGTH, LENGTH_MAP] THEN
      REWRITE_TAC [ALL_MAP, IN_ELIM_THM] THEN
      HolCore.Lib.W (fun g => HolLight.tactic_of do
        let t ← liftExcept (HolCore.Lib.funpow 2 (fun (m : Except String term) => do HolCore.Equal.lhand (← m)) (pure (HolLight.snd g)))
        pure (HolCore.Lib.C SUBGOAL_THEN (fun th => REWRITE_TAC [th]) t)) THENL
       [CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
        MATCH_MP_TAC ALL_IMP THEN
        FIRST_ASSUM (EXISTS_TAC o HolCore.Equal.lhand o concl) THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [o_THM, NUM_OF_TERM_INJ] THEN ASM_MESON_TAC [], ALL_TAC] THEN
      REWRITE_TAC [TERM_OF_NUM, (← HolLight.GSYM MAP_o), o_DEF] THEN
      SIMP_TAC [MAP_EQ_DEGEN, ALL_T],
      DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[[] :term list]]) THEN
      ASM_REWRITE_TAC [ALL, MAP, LENGTH] THEN
      REWRITE_TAC [IN] THEN CONV_TAC (HolLight.ONCE_DEPTH_CONV (fun t => pure (ETA_CONV t))),
      STRIP_TAC THEN FIRST_X_ASSUM
       (MP_TAC o HolLight.SPEC [[CONS (term_of_num h) (MAP term_of_num t)]]) THEN
      ASM_REWRITE_TAC [ALL, MAP, LENGTH, LENGTH_MAP] THEN
      HolCore.Lib.W (fun g => HolLight.tactic_of do
        let t ← liftExcept (HolCore.Lib.funpow 2 (fun (m : Except String term) => do HolCore.Equal.lhand (← m)) (pure (HolLight.snd g)))
        pure (HolCore.Lib.C SUBGOAL_THEN (fun th => REWRITE_TAC [th]) t)) THENL
       [CONJ_TAC THENL
         [RULE_ASSUM_TAC (HolLight.REWRITE_RULE [IN_ELIM_THM]) THEN
          ASM_MESON_TAC [TERM_OF_NUM], ALL_TAC] THEN
        REWRITE_TAC [ALL_MAP] THEN MATCH_MP_TAC ALL_IMP THEN
        FIRST_ASSUM (EXISTS_TAC o HolCore.Equal.lhand o concl) THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [IN_ELIM_THM, o_THM] THEN MESON_TAC [TERM_OF_NUM],
        ALL_TAC] THEN
      REWRITE_TAC [IN] THEN CONV_TAC (HolLight.ONCE_DEPTH_CONV (fun t => pure (ETA_CONV t)))])
  : ExceptT String IO thm).run
#eval LOWMOD_INTERPRETATION

#eval phrase 33
unsafe def LS : thm := keep "LS" fun _ => (do
  prove ([[!M:(A->bool)#(num->A list->A)#(num->A list->bool) s.
        interpretation (language s) M /\
        ~(Dom(M) = EMPTY) /\
        (!p. p IN s ==> qfree p) /\ M satisfies s
        ==> ?N. interpretation (language s) N /\
                ~(Dom N :num->bool = EMPTY) /\
                N satisfies s]])
   (REPEAT GEN_TAC THEN
    DISCH_THEN (STRIP_ASSUME_TAC oTIO HolLight.MATCH_MP CANON) THEN
    EXISTS_TAC [[LOWMOD C]] THEN
    ASM_REWRITE_TAC [LOWMOD_DOM_EMPTY, LOWMOD_INTERPRETATION] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [satisfies]) THEN
    REWRITE_TAC [satisfies] THEN SIMP_TAC [LOWMOD_HOLDS] THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [valuation]) THEN
    ASM_REWRITE_TAC [valuation] THEN REWRITE_TAC [LOWMOD, Dom_DEF] THEN
    REWRITE_TAC [IN_ELIM_THM, o_THM] THEN
    MESON_TAC [TERM_OF_NUM])
  : ExceptT String IO thm).run
#eval LS

#eval phrase 34
unsafe def UNIFORMITY : thm := keep "UNIFORMITY" fun _ => (do
  prove ([[qfree p /\ (!C v. ~(Dom C = EMPTY) /\
                     valuation(C) v ==> holds C (v:num->term) (ITLIST ?? xs p))
   ==> ?is. (!i x. MEM i is ==> terms(FST(language {p})) (i x)) /\
            !d. pholds(d) (ITLIST (||) (MAP (\i. formsubst i p) is) False)]])
   (HolLight.tactic_of do
     let phlds3 ← liftExcept (HolCore.Lib.el 3 (Session.CONJUNCTS PHOLDS))
     let psiContra ← (do
       let g ← HolLight.GSYM CONTRAPOS_THM
       HolLight.GEN_REWRITE_RULE HolCore.Lib.I [g] PSATISFIES_INSTANCES)
     let compactDisj ← HolLight.SPEC ([[{formsubst i q | q IN {p} /\
                                (!x. i x IN terms(FST(language {p})))}]])
              COMPACT_DISJ
     pure
      (STRIP_TAC THEN
       MP_TAC compactDisj THEN
       HolCore.Lib.W (fun g => HolLight.tactic_of do
         let t ← liftExcept (HolCore.Lib.funpow 2 (fun (m : Except String term) => do HolCore.Equal.lhand (← m)) (pure (HolLight.snd g)))
         pure (HolCore.Lib.C SUBGOAL_THEN (fun th => REWRITE_TAC [th]) t)) THENL
        [ALL_TAC,
         REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY, IN_ELIM_THM, (← HolLight.GSYM CONJ_ASSOC)] THEN
         REWRITE_TAC [UNWIND_THM2] THEN
         DISCH_THEN (X_CHOOSE_THEN ([[ps:form list]]) STRIP_ASSUME_TAC) THEN
         EXISTS_TAC [[MAP (\q. @i. (!x. i x IN terms (FST (language {p}))) /\
                             (q = formsubst i p)) ps]] THEN
         REWRITE_TAC [(← HolLight.GSYM MAP_o), o_DEF] THEN CONJ_TAC THENL
          [REPEAT GEN_TAC THEN
           FIRST_ASSUM
            (fun th => HolLight.tactic_of do
              let c := concl th
              let tm ← liftExcept (HolCore.Lib.check
                (fun t => match HolCore.Kernel.rand t with | .ok r => r == ([[ps:form list]] : term) | .error _ => false) c)
              pure (UNDISCH_TAC tm)) THEN
           SPEC_TAC ([[ps:form list]], [[ps:form list]]) THEN
           LIST_INDUCT_TAC THEN REWRITE_TAC [ALL, MAP, MEM] THEN
           DISCH_TAC THEN DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL
            [ALL_TAC, FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []] THEN
           FIRST_ASSUM (ASSUME_TAC oT (Session.SELECT_RULE oM Session.CONJUNCT1)) THEN
           DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [IN] THEN
           RULE_ASSUM_TAC (HolLight.REWRITE_RULE [IN]) THEN
           FIRST_ASSUM (MATCH_ACCEPT_TAC oTIO (Session.CONJUNCT1 oEIO HolLight.SPEC_ALL)),
           X_GEN_TAC [[d:form->bool]] THEN
           FIRST_ASSUM (MP_TAC o HolLight.SPEC [[d:form->bool]]) THEN
           MATCH_MP_TAC EQ_IMP THEN
           AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
           MATCH_MP_TAC (← HolLight.GSYM MAP_EQ_DEGEN) THEN
           FIRST_ASSUM
            (fun th => HolLight.tactic_of do
              let c := concl th
              let tm ← liftExcept (HolCore.Lib.check
                (fun t => match HolCore.Kernel.rand t with | .ok r => r == ([[ps:form list]] : term) | .error _ => false) c)
              pure (UNDISCH_TAC tm)) THEN
           SPEC_TAC ([[ps:form list]], [[ps:form list]]) THEN
           LIST_INDUCT_TAC THEN REWRITE_TAC [ALL, MAP, MEM] THEN
           DISCH_THEN (CONJUNCTS_THEN2 (ASSUME_TAC oT Session.SELECT_RULE) ASSUME_TAC) THEN
           CONJ_TAC THENL [FIRST_ASSUM (MATCH_ACCEPT_TAC oT Session.CONJUNCT2), ALL_TAC] THEN
           MATCH_MP_TAC ALL_IMP THEN
           FIRST_ASSUM (fun th => HolLight.tactic_of do
              let l ← liftExcept (HolCore.Equal.lhand (concl th))
              pure (EXISTS_TAC l THEN
                CONJ_TAC THENL [ALL_TAC, FIRST_ASSUM ACCEPT_TAC])) THEN
           X_GEN_TAC [[r:form]] THEN REWRITE_TAC [] THEN
           DISCH_THEN (MP_TAC oT (Session.SELECT_RULE oM Session.CONJUNCT2)) THEN
           DISCH_THEN (ACCEPT_TAC oT Session.CONJUNCT2)]] THEN
       X_GEN_TAC [[d:form->bool]] THEN
       SUBGOAL_THEN ([[~((canon_of_prop (language {p}) d) satisfies {(Not p)})]])
       ASSUME_TAC THENL
        [REWRITE_TAC [satisfies, IN_INSERT, NOT_IN_EMPTY] THEN STRIP_TAC THEN
         FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[canon_of_prop (language {p}) d]]) THEN
         REWRITE_TAC [HOLDS_ITLIST_EXISTS, NOT_FORALL_THM, NOT_IMP] THEN
         SUBGOAL_THEN ([[?v:num->term. valuation (canon_of_prop (language {p}) d) v]])
         CHOOSE_TAC THENL
          [MATCH_MP_TAC VALUATION_EXISTS THEN
           REWRITE_TAC [(← HolLight.GSYM MEMBER_NOT_EMPTY)] THEN
           REWRITE_TAC [Dom_DEF, canon_of_prop, IN] THEN
           MESON_TAC [terms_RULES], ALL_TAC] THEN
         EXISTS_TAC [[v:num->term]] THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
          [REWRITE_TAC [canon_of_prop, Dom_DEF] THEN
           REWRITE_TAC [language, EXTENSION, NOT_IN_EMPTY, NOT_FORALL_THM] THEN
           EXISTS_TAC [[V 0]] THEN REWRITE_TAC [IN] THEN MESON_TAC [terms_CASES],
           ALL_TAC] THEN
         REWRITE_TAC [NOT_EXISTS_THM] THEN
         REWRITE_TAC [(← ExceptT.mk (TAUT [[~(a /\ b /\ c) <=> a /\ b ==> ~c]]))] THEN
         REWRITE_TAC [(← HolLight.GSYM HOLDS)] THEN REPEAT STRIP_TAC THEN
         FIRST_ASSUM MATCH_MP_TAC THEN
         REWRITE_TAC [valuation, IN] THEN GEN_TAC THEN
         UNDISCH_TAC [[valuation (canon_of_prop (language {p}) d) (v:num->term)]] THEN
         SPEC_TAC ([[v:num->term]], [[v:num->term]]) THEN
         UNDISCH_TAC [[ALL (Dom (canon_of_prop (language {p}) d)) as]] THEN
         UNDISCH_TAC [[LENGTH (as:term list) = LENGTH (xs:num list)]] THEN
         SPEC_TAC ([[as:term list]], [[as:term list]]) THEN
         SPEC_TAC ([[xs:num list]], [[xs:num list]]) THEN
         LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
         REWRITE_TAC [LENGTH, NOT_SUC, MAP2, REVERSE, ITLIST, ALL] THENL
          [REWRITE_TAC [valuation, IN] THEN MESON_TAC [], ALL_TAC] THEN
         REWRITE_TAC [SUC_INJ, ITLIST_EXTRA] THEN
         DISCH_THEN (ANTE_RES_THEN ASSUME_TAC) THEN
         DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
         DISCH_THEN (ANTE_RES_THEN ASSUME_TAC) THEN
         REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
         REWRITE_TAC [valuation, valmod] THEN
         RULE_ASSUM_TAC (HolLight.REWRITE_RULE [valuation]) THEN
         GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
         ASM_REWRITE_TAC [IN], ALL_TAC] THEN
       SUBGOAL_THEN ([[!q. q IN {(Not p)} ==> qfree q]]) ASSUME_TAC THENL
        [REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
         REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [QFREE], ALL_TAC] THEN
       FIRST_ASSUM (MP_TAC oTIO HolLight.MATCH_MP psiContra) THEN
       ASM_REWRITE_TAC [] THEN
       REWRITE_TAC [psatisfies, IN_ELIM_THM, IN_INSERT, NOT_IN_EMPTY] THEN
       REWRITE_TAC [RIGHT_EXISTS_AND_THM, (← HolLight.GSYM CONJ_ASSOC)] THEN
       REWRITE_TAC [UNWIND_THM2] THEN
       REWRITE_TAC [Not_DEF, formsubst] THEN REWRITE_TAC [(← HolLight.GSYM Not_DEF)] THEN
       MESON_TAC [phlds3]))
  : ExceptT String IO thm).run
#eval UNIFORMITY

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py from the `#eval`s above. -/
unsafe def ensure : IO Unit := once "HolLogicArith.Canon" do
  replay (
          HolLogicArith.Skolem.ensure)
  replay (
          HolLogicArith.FolProp.ensure)
  replay (
          do IO.println terms_RULES; IO.println terms_INDUCT; IO.println terms_CASES)
  replay (
          STUPID_CANONDOM_LEMMA)
  replay (
          FINITE_SUBSET_INSTANCE)
  replay (
          FINITE_SUBSET_SKOLEM)
  replay (
          VALUATION_EXISTS)
  replay (
          HOLDS_ITLIST_EXISTS)
  replay (
          canonical)
  replay (
          prop_of_model)
  replay (
          canon_of_prop)
  replay (
          PHOLDS_PROP_OF_MODEL)
  replay (
          PROP_OF_CANON_OF_PROP)
  replay (
          HOLDS_CANON_OF_PROP)
  replay (
          HOLDS_CANON_OF_PROP_GENERAL)
  replay (
          CANONICAL_CANON_OF_PROP)
  replay (
          INTERPRETATION_CANON_OF_PROP)
  replay (
          PROP_VALID_IMP_FOL_VALID)
  replay (
          FOL_VALID_IMP_PROP_VALID)
  replay (
          SATISFIES_PSATISFIES)
  replay (
          PSATISFIES_INSTANCES)
  replay (
          SATISFIES_INSTANCES)
  replay (
          COMPACT_CANON_QFREE)
  replay (
          INTERPRETATION_RESTRICTLANGUAGE)
  replay (
          INTERPRETATION_EXTENDLANGUAGE)
  replay (
          COMPACT_LS)
  replay (
          CANON)
  replay (
          term_of_num)
  replay (
          TERM_OF_NUM)
  replay (
          LOWMOD)
  replay (
          LOWMOD_DOM_EMPTY)
  replay (
          LOWMOD_TERMVAL)
  replay (
          LOWMOD_HOLDS)
  replay (
          LOWMOD_INTERPRETATION)
  replay (
          LS)
  replay (
          UNIFORMITY)
-- @@ENSURE END

end HolLogicArith.Canon
