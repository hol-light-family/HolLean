/- File: HolLogicArith/Birkhoff.lean
Translation of HOL Light's Logic/birkhoff.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolLogicArith.Positive
import HolLogicArith.Prolog
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
open HolLogicArith.Prolog

namespace HolLogicArith.Birkhoff

/- List definitions/theorems used below are exposed by Session as fields of
   the `listDefs`/`listThms1`/`listThms2` bundles; alias the ones we need. -/
private unsafe def LENGTH : thm := Session.listDefs.LENGTH
private unsafe def MAP : thm := Session.listDefs.MAP
private unsafe def ALL : thm := Session.listDefs.ALL
private unsafe def ITLIST : thm := Session.listDefs.ITLIST
private unsafe def MEM : thm := Session.listDefs.MEM
private unsafe def ALL2 : thm := Session.listDefs.ALL2
private unsafe def CONS_11 : thm := Session.listThms1.CONS_11
private unsafe def REPLICATE : thm := Session.listDefs.REPLICATE
private unsafe def MAP_o : thm := Session.listThms1.MAP_o
private unsafe def LENGTH_MAP : thm := Session.listThms1.LENGTH_MAP
private unsafe def LENGTH_REPLICATE : thm := Session.listThms1.LENGTH_REPLICATE
private unsafe def ALL_MAP : thm := Session.listThms1.ALL_MAP
private unsafe def ALL_MEM : thm := Session.listThms1.ALL_MEM
private unsafe def EX_MEM : thm := Session.listThms1.EX_MEM
private unsafe def MEM_MAP : thm := Session.listThms1.MEM_MAP
private unsafe def NOT_EX : thm := Session.listThms1.NOT_EX
private unsafe def ALL2_MAP2 : thm := Session.listThms2.ALL2_MAP2
private unsafe def ALL2_ALL : thm := Session.listThms2.ALL2_ALL
private unsafe def AND_ALL2 : thm := Session.listThms2.AND_ALL2
private unsafe def MONO_ALL2 : thm := Session.MONO_ALL2

#eval HolLogicArith.Positive.ensure
#eval HolLogicArith.Prolog.ensure

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
unsafe def ALL2_SYM : thm := keep "ALL2_SYM" fun _ => (do
  prove ([[!l1 l2. ALL2 P l1 l2 <=> ALL2 (\x y. P y x) l2 l1]])
   (LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [ALL2])
  : ExceptT String IO thm).run
#eval ALL2_SYM

#eval phrase 2
unsafe def MAP_EQ_ALL2 : thm := keep "MAP_EQ_ALL2" fun _ => (do
  prove ([[!f l1 l2. ALL2 (\x y. f x = f y) l1 l2 ==> (MAP f l1 = MAP f l2)]])
   (GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
    ASM_SIMP_TAC [ALL2, MAP, CONS_11] THEN STRIP_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval MAP_EQ_ALL2

#eval phrase 3
unsafe def FORMSUBST_EQ : thm := keep "FORMSUBST_EQ" fun _ => (do
  prove ([[!i s t. formsubst i (s === t) = (termsubst i s === termsubst i t)]])
   (REWRITE_TAC [Equal_DEF, formsubst, MAP])
  : ExceptT String IO thm).run
#eval FORMSUBST_EQ

#eval phrase 4
unsafe def TERMS_UNIV : thm := keep "TERMS_UNIV" fun _ => (do
  prove ([[terms UNIV = UNIV]])
   (REWRITE_TAC [IN_UNIV, EXTENSION] THEN REWRITE_TAC [IN] THEN
    MATCH_MP_TAC term_INDUCT THEN REWRITE_TAC [terms_RULES] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV (fun t => pure (ETA_CONV t))) THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (← liftExcept (Session.CONJUNCT2 (← ExceptT.mk (HolLight.SPEC_ALL terms_RULES)))) THEN
    ASM_REWRITE_TAC [IN_UNIV])
  : ExceptT String IO thm).run
#eval TERMS_UNIV

#eval phrase 5
unsafe def FUNCTIONS_UNIV : thm := keep "FUNCTIONS_UNIV" fun _ => (do
  prove ([[functions UNIV = UNIV]])
   (REWRITE_TAC [IN_UNIV, EXTENSION] THEN
    REWRITE_TAC [functions, IN_UNIONS, IN_ELIM_THM, IN_UNIV] THEN
    ONCE_REWRITE_TAC [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[f:num]], [[n:num]] ] THEN
    EXISTS_TAC [[functions_form(Atom p [Fn f (REPLICATE n (V x))])]] THEN
    REWRITE_TAC [functions_form, MAP, LIST_UNION, UNION_EMPTY] THEN
    REWRITE_TAC [functions_term, IN_INSERT, LENGTH_REPLICATE] THEN
    EXISTS_TAC [[Atom p [Fn f (REPLICATE n (V x))] ]] THEN
    REWRITE_TAC [functions_form, MAP, LIST_UNION, UNION_EMPTY] THEN
    REWRITE_TAC [functions_term, IN_INSERT, LENGTH_REPLICATE])
  : ExceptT String IO thm).run
#eval FUNCTIONS_UNIV

#eval phrase 6
unsafe def PREDICATES_UNIV : thm := keep "PREDICATES_UNIV" fun _ => (do
  prove ([[predicates UNIV = UNIV]])
   (REWRITE_TAC [IN_UNIV, EXTENSION] THEN
    REWRITE_TAC [predicates, IN_UNIONS, IN_ELIM_THM, IN_UNIV] THEN
    ONCE_REWRITE_TAC [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[p:num]], [[n:num]] ] THEN
    EXISTS_TAC [[predicates_form(Atom p (REPLICATE n (V x)))]] THEN
    REWRITE_TAC [predicates_form, LENGTH_REPLICATE, IN_INSERT] THEN
    EXISTS_TAC [[Atom p (REPLICATE n (V x))]] THEN
    REWRITE_TAC [predicates_form, LENGTH_REPLICATE, IN_INSERT])
  : ExceptT String IO thm).run
#eval PREDICATES_UNIV

#eval phrase 7
unsafe def LANGUAGE_UNIV : thm := keep "LANGUAGE_UNIV" fun _ => (do
  prove ([[language UNIV = UNIV,UNIV]])
   (REWRITE_TAC [language, FUNCTIONS_UNIV, PREDICATES_UNIV])
  : ExceptT String IO thm).run
#eval LANGUAGE_UNIV

#eval phrase 8
unsafe def EQUAL_INJ : thm := keep "EQUAL_INJ" fun _ => (do
  prove ([[!s t u v. ((s === t) = (u === v)) <=> (s = u) /\ (t = v)]])
   (REWRITE_TAC [Equal_DEF, form_INJ, CONS_11])
  : ExceptT String IO thm).run
#eval EQUAL_INJ

#eval phrase 9
unsafe def EQUAL_INJ_ALT : thm := keep "EQUAL_INJ_ALT" fun _ => (do
  prove ([[!s t u v. ((s === t) = (u === v)) <=> (u = s) /\ (v = t)]])
   (REWRITE_TAC [EQUAL_INJ, EQ_SYM_EQ])
  : ExceptT String IO thm).run
#eval EQUAL_INJ_ALT

#eval phrase 10
#eval parse_as_infix ("|-", (11, "right"))

#eval phrase 11
unsafe def provable_triple : thm × thm × thm := keep "provable_triple" fun _ =>
  newInductive
   [[(!s t. s === t IN E ==> E |- s === t) /\
     (!t. E |- t === t) /\
     (!s t. E |- s === t ==> E |- t === s) /\
     (!s t u. E |- s === t /\ E |- t === u ==> E |- s === u) /\
     (!f a b. ALL2 (\l r. E |- l === r) a b ==> E |- Fn f a === Fn f b) /\
     (!s t i. E |- s === t ==> E |- formsubst i (s === t))]]
unsafe def provable_RULES : thm := provable_triple.1
unsafe def provable_INDUCT : thm := provable_triple.2.1
unsafe def provable_CASES : thm := provable_triple.2.2
#eval do IO.println provable_RULES; IO.println provable_INDUCT; IO.println provable_CASES

#eval phrase 12
#eval parse_as_infix ("|--", (11, "right"))

#eval phrase 13
unsafe def wcprovable_triple : thm × thm × thm := keep "wcprovable_triple" fun _ =>
  newInductive
   [[(!s t i. s === t IN E ==> E |-- formsubst i (s === t)) /\
     (!s t i. s === t IN E ==> E |-- formsubst i (t === s)) /\
     (!t. E |-- t === t) /\
     (!s t u. E |-- s === t /\ E |-- t === u ==> E |-- s === u) /\
     (!f a b. ALL2 (\l r. E |-- l === r) a b ==> E |-- Fn f a === Fn f b)]]
unsafe def wcprovable_RULES : thm := wcprovable_triple.1
unsafe def wcprovable_INDUCT : thm := wcprovable_triple.2.1
unsafe def wcprovable_CASES : thm := wcprovable_triple.2.2
#eval do IO.println wcprovable_RULES; IO.println wcprovable_INDUCT; IO.println wcprovable_CASES

#eval phrase 14
unsafe def WCPROVABLE_SYM : thm := keep "WCPROVABLE_SYM" fun _ => (do
  prove ([[!E a. E |-- a ==> !s t. (a = (s === t)) ==> E |-- t === s]])
   (GEN_TAC THEN MATCH_MP_TAC wcprovable_INDUCT THEN
    SIMP_TAC [EQUAL_INJ_ALT, LEFT_FORALL_IMP_THM,
             RIGHT_EXISTS_AND_THM, LEFT_EXISTS_AND_THM, EXISTS_REFL] THEN
    REWRITE_TAC [wcprovable_RULES] THEN REPEAT CONJ_TAC THENL
     [ALL_TAC,
      ALL_TAC,
      MESON_TAC [wcprovable_RULES],
      ONCE_REWRITE_TAC [(← HolLight.GSYM ALL2_SYM)] THEN REWRITE_TAC [wcprovable_RULES]] THEN
    REWRITE_TAC [FORMSUBST_EQ] THEN
    SIMP_TAC [EQUAL_INJ_ALT, LEFT_FORALL_IMP_THM,
             RIGHT_EXISTS_AND_THM, LEFT_EXISTS_AND_THM, EXISTS_REFL] THEN
    REWRITE_TAC [(← HolLight.GSYM FORMSUBST_EQ)] THEN REWRITE_TAC [wcprovable_RULES])
  : ExceptT String IO thm).run
#eval WCPROVABLE_SYM

#eval phrase 15
unsafe def WCPROVABLE_INST : thm := keep "WCPROVABLE_INST" fun _ => (do
  prove ([[!E a. E |-- a
           ==> !i s t. (a = (s === t)) ==> (E |-- formsubst i (s === t))]])
   (GEN_TAC THEN MATCH_MP_TAC wcprovable_INDUCT THEN
    SIMP_TAC [EQUAL_INJ_ALT, LEFT_FORALL_IMP_THM, FORMSUBST_EQ,
             RIGHT_EXISTS_AND_THM, LEFT_EXISTS_AND_THM, EXISTS_REFL] THEN
    REWRITE_TAC [TERMSUBST_TERMSUBST] THEN REPEAT CONJ_TAC THENL
     [SIMP_TAC [(← HolLight.GSYM FORMSUBST_EQ), wcprovable_RULES],
      SIMP_TAC [(← HolLight.GSYM FORMSUBST_EQ), wcprovable_RULES],
      REWRITE_TAC [wcprovable_RULES],
      MESON_TAC [wcprovable_RULES],
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [termsubst] THEN
    MATCH_MP_TAC (← liftExcept (HolCore.Lib.last (Session.CONJUNCTS (← ExceptT.mk (HolLight.SPEC_ALL wcprovable_RULES))))) THEN
    REWRITE_TAC [ALL2_MAP2] THEN
    POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_ALL2 THEN SIMP_TAC [])
  : ExceptT String IO thm).run
#eval WCPROVABLE_INST

#eval phrase 16
unsafe def WCPROVABLE_PROVABLE : thm := keep "WCPROVABLE_PROVABLE" fun _ => (do
  prove ([[!E s t. (E |-- s === t) <=> (E |- s === t)]])
   (GEN_TAC THEN
    SUBGOAL_THEN
     ([[(!a. E |- a ==> !s t. (a = (s === t)) ==> E |-- s === t) /\
        (!a. E |-- a ==> !s t. (a = (s === t)) ==> E |- s === t)]])
     (fun th => MESON_TAC [th]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC provable_INDUCT,
      MATCH_MP_TAC wcprovable_INDUCT] THEN
    SIMP_TAC [EQUAL_INJ_ALT, LEFT_FORALL_IMP_THM,
             RIGHT_EXISTS_AND_THM, LEFT_EXISTS_AND_THM, EXISTS_REFL] THEN
    REWRITE_TAC [provable_RULES, wcprovable_RULES] THENL
     [MESON_TAC [FORMSUBST_TRIV, wcprovable_RULES, Equal_DEF, WCPROVABLE_SYM,
                WCPROVABLE_INST],
      MESON_TAC [FORMSUBST_TRIV, provable_RULES, Equal_DEF]])
  : ExceptT String IO thm).run
#eval WCPROVABLE_PROVABLE

#eval phrase 17
#eval parse_as_infix ("|---", (11, "right"))

#eval phrase 18
#eval parse_as_infix ("|--_axiom", (11, "right"))

#eval phrase 19
#eval parse_as_infix ("|--_cong", (11, "right"))

#eval phrase 20
#eval parse_as_infix ("|--_achain", (11, "right"))

#eval phrase 21
#eval parse_as_infix ("|--_cchain", (11, "right"))

#eval phrase 22
unsafe def aprovable_triple : thm × thm × thm := keep "aprovable_triple" fun _ =>
  newInductive
   [[(!s t i. s === t IN E ==> E |--_axiom formsubst i (s === t)) /\
     (!s t i. s === t IN E ==> E |--_axiom formsubst i (t === s))]]
unsafe def aprovable_RULES : thm := aprovable_triple.1
unsafe def aprovable_INDUCT : thm := aprovable_triple.2.1
unsafe def aprovable_CASES : thm := aprovable_triple.2.2
#eval do IO.println aprovable_RULES; IO.println aprovable_INDUCT; IO.println aprovable_CASES

#eval phrase 23
unsafe def cprovable_triple : thm × thm × thm := keep "cprovable_triple" fun _ =>
  newInductive
   [[(!s t. E |--_axiom s === t ==> E |--_achain s === t) /\
     (!s t. E |--_cong s === t ==> E |--_cchain s === t) /\
     (!s t u. E |--_axiom s === t /\ E |--- t === u ==> E |--_achain s === u) /\
     (!s t u. E |--_cong s === t /\ E |--_achain t === u
              ==> E |--_cchain s === u) /\
     (!f a b. ALL2 (\l r. E |--- l === r) a b
              ==> E |--_cong Fn f a === Fn f b) /\
     (!s t. (s = t) \/ E |--_achain s === t \/ E |--_cchain s === t
            ==> E |--- s === t)]]
unsafe def cprovable_RULES : thm := cprovable_triple.1
unsafe def cprovable_INDUCT : thm := cprovable_triple.2.1
unsafe def cprovable_CASES : thm := cprovable_triple.2.2
#eval do IO.println cprovable_RULES; IO.println cprovable_INDUCT; IO.println cprovable_CASES

#eval phrase 24
unsafe def CPROVABLE_PROVABLE_LEMMA : thm := keep "CPROVABLE_PROVABLE_LEMMA" fun _ => (do
  let cr ← ExceptT.mk (HolLight.SPEC_ALL cprovable_RULES)
  let cr1 ← liftExcept (HolCore.Lib.el 1 (Session.CONJUNCTS cr))
  let cr3 ← liftExcept (HolCore.Lib.el 3 (Session.CONJUNCTS cr))
  let cr4 ← liftExcept (HolCore.Lib.el 4 (Session.CONJUNCTS cr))
  let cr5 ← liftExcept (HolCore.Lib.el 5 (Session.CONJUNCTS cr))
  let taut_ab ← ExceptT.mk (TAUT [[a /\ b <=> ~(a ==> ~b)]])
  let taut_abc ← ExceptT.mk (TAUT [[a /\ b /\ c ==> d <=> a ==> b ==> c ==> d]])
  prove ([[!E a. E |-- a
           ==> E |-- a /\
               E |--- a /\
               !u s t. (a = (s === t))
                       ==> E |--- t === u ==> E |--- s === u]])
   (GEN_TAC THEN MATCH_MP_TAC wcprovable_INDUCT THEN
    SIMP_TAC [EQUAL_INJ_ALT, LEFT_FORALL_IMP_THM,
             RIGHT_EXISTS_AND_THM, LEFT_EXISTS_AND_THM, EXISTS_REFL] THEN
    REWRITE_TAC [wcprovable_RULES] THEN
    REPEAT (CONJ_TAC THENL
     [MESON_TAC [FORMSUBST_EQ, wcprovable_RULES,
                cprovable_RULES, aprovable_RULES], ALL_TAC]) THEN
    REWRITE_TAC [(← HolLight.GSYM AND_ALL2)] THEN SIMP_TAC [wcprovable_RULES] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC [cprovable_RULES] THEN X_GEN_TAC [[u:term]] THEN
    HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [cprovable_CASES] THEN
    REWRITE_TAC [EQUAL_INJ_ALT] THEN
    ONCE_REWRITE_TAC [taut_ab] THEN
    SIMP_TAC [] THEN REWRITE_TAC [NOT_IMP, LEFT_EXISTS_AND_THM] THEN
    REWRITE_TAC [LEFT_EXISTS_AND_THM, RIGHT_EXISTS_AND_THM, EXISTS_REFL] THEN
    DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL
     [DISCH_THEN (SUBST1_TAC oTIO HolLight.SYM) THEN
      MATCH_MP_TAC cr5 THEN
      DISJ2_TAC THEN DISJ2_TAC THEN
      MATCH_MP_TAC cr1 THEN
      MATCH_MP_TAC cr4 THEN
      ASM_REWRITE_TAC [], ALL_TAC] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [MATCH_MP_TAC cr5 THEN
      DISJ2_TAC THEN DISJ2_TAC THEN
      MATCH_MP_TAC cr3 THEN
      EXISTS_TAC [[Fn f b]] THEN ASM_SIMP_TAC [cprovable_RULES], ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC oTIO HolLight.GEN_REWRITE_RULE HolCore.Lib.I [cprovable_CASES]) THEN
    REWRITE_TAC [EQUAL_INJ_ALT] THEN
    ONCE_REWRITE_TAC [taut_ab] THEN
    SIMP_TAC [] THEN REWRITE_TAC [NOT_IMP, LEFT_EXISTS_AND_THM] THEN
    REWRITE_TAC [LEFT_EXISTS_AND_THM, RIGHT_EXISTS_AND_THM, EXISTS_REFL] THEN
    DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL
     [HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [cprovable_CASES] THEN
      REWRITE_TAC [EQUAL_INJ_ALT, term_INJ, LEFT_IMP_EXISTS_THM] THEN
      GEN_TAC THEN GEN_TAC THEN X_GEN_TAC [[c:term list]] THEN
      REWRITE_TAC [(← HolLight.GSYM CONJ_ASSOC)] THEN
      SIMP_TAC [taut_abc] THEN
      DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN
      DISCH_THEN (CONJUNCTS_THEN2 (SUBST1_TAC oTIO HolLight.SYM) ASSUME_TAC) THEN
      MATCH_MP_TAC cr5 THEN
      DISJ2_TAC THEN DISJ2_TAC THEN
      MATCH_MP_TAC cr1 THEN
      MATCH_MP_TAC cr4 THEN
      MAP_EVERY UNDISCH_TAC
       [ [[ALL2 (\l r. !u. E |--- r === u ==> E |--- l === u) a b]],
        [[ALL2 (\l r. E |--- l === r) b c]] ] THEN
      REWRITE_TAC [IMP_IMP] THEN
      MAP_EVERY (fun s => SPEC_TAC (s, s))
       [ [[c:term list]], [[b:term list]], [[a:term list]] ] THEN
      LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
      REWRITE_TAC [ALL2] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      FIRST_ASSUM (fun th => HolLight.tactic_of do
        let r ← liftExcept (HolCore.Kernel.rand (concl th))
        pure (EXISTS_TAC r THEN ASM_REWRITE_TAC [] THEN NO_TAC)),
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[s:term]]) (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [cprovable_CASES] THEN
    REWRITE_TAC [EQUAL_INJ_ALT, term_INJ, LEFT_IMP_EXISTS_THM] THEN
    GEN_TAC THEN GEN_TAC THEN X_GEN_TAC [[c:term list]] THEN
    REWRITE_TAC [(← HolLight.GSYM CONJ_ASSOC)] THEN
    SIMP_TAC [taut_abc] THEN
    DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (SUBST_ALL_TAC oTIO HolLight.SYM) ASSUME_TAC) THEN
    MATCH_MP_TAC cr5 THEN DISJ2_TAC THEN
    DISJ2_TAC THEN MATCH_MP_TAC cr3 THEN
    EXISTS_TAC [[Fn f c]] THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC cr4 THEN
    MAP_EVERY UNDISCH_TAC
     [ [[ALL2 (\l r. !u. E |--- r === u ==> E |--- l === u) a b]],
      [[ALL2 (\l r. E |--- l === r) b c]] ] THEN
    REWRITE_TAC [IMP_IMP] THEN
    MAP_EVERY (fun s => SPEC_TAC (s, s))
     [ [[c:term list]], [[b:term list]], [[a:term list]] ] THEN
    LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC [ALL2] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM (fun th => HolLight.tactic_of do
      let r ← liftExcept (HolCore.Kernel.rand (concl th))
      pure (EXISTS_TAC r THEN ASM_REWRITE_TAC [] THEN NO_TAC)))
  : ExceptT String IO thm).run
#eval CPROVABLE_PROVABLE_LEMMA

#eval phrase 25
unsafe def CPROVABLE_PROVABLE : thm := keep "CPROVABLE_PROVABLE" fun _ => (do
  prove ([[!E s t. (E |--- s === t) <=> (E |- s === t)]])
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [ALL_TAC, MESON_TAC [CPROVABLE_PROVABLE_LEMMA, WCPROVABLE_PROVABLE]] THEN
    SUBGOAL_THEN
     ([[(!a. E |--_achain a ==> !s t. (a = (s === t)) ==> E |- s === t) /\
        (!a. E |--_cchain a ==> !s t. (a = (s === t)) ==> E |- s === t) /\
        (!a. E |--_cong a ==> !s t. (a = (s === t)) ==> E |- s === t) /\
        (!a. E |--- a ==> !s t. (a = (s === t)) ==> E |- s === t)]])
     (fun th => MESON_TAC [th]) THEN
    MATCH_MP_TAC cprovable_INDUCT THEN
    SIMP_TAC [EQUAL_INJ_ALT, LEFT_FORALL_IMP_THM,
             RIGHT_EXISTS_AND_THM, LEFT_EXISTS_AND_THM, EXISTS_REFL] THEN
    REWRITE_TAC [provable_RULES] THEN
    SUBGOAL_THEN ([[!a. E |--_axiom a ==> !s t. (a = (s === t)) ==> E |- s === t]])
     (fun th => MESON_TAC [th, provable_RULES]) THEN
    MATCH_MP_TAC aprovable_INDUCT THEN
    REWRITE_TAC [FORMSUBST_EQ, EQUAL_INJ_ALT] THEN
    SIMP_TAC [] THEN MESON_TAC [provable_RULES, FORMSUBST_EQ])
  : ExceptT String IO thm).run
#eval CPROVABLE_PROVABLE

#eval phrase 26
unsafe def subterms : thm := keep "subterms" fun _ => (do
  newRec term_RECURSION
   [[(subterms (V x) = {(V x)}) /\
     (subterms (Fn f args) =
          (Fn f args) INSERT (LIST_UNION (MAP subterms args)))]]
  : ExceptT String IO thm).run
#eval subterms

#eval phrase 27
unsafe def subtermsa : thm := keep "subtermsa" fun _ => (do
  newRec form_RECURSION
   [[subtermsa (Atom P args) = LIST_UNION (MAP subterms args)]]
  : ExceptT String IO thm).run
#eval subtermsa

#eval phrase 28
unsafe def subtermss : thm := keep "subtermss" fun _ => new_definition
  [[subtermss E = UNIONS {subtermsa p | p IN E}]]
#eval subtermss

#eval phrase 29
unsafe def SUBTERMS_REFL : thm := keep "SUBTERMS_REFL" fun _ => (do
  prove ([[!t. t IN subterms t]])
   (MATCH_MP_TAC term_INDUCT THEN REWRITE_TAC [subterms, IN_INSERT])
  : ExceptT String IO thm).run
#eval SUBTERMS_REFL

#eval phrase 30
unsafe def esubterms : thm := keep "esubterms" fun _ => new_definition
  [[esubterms E s t =
        subtermss ((s === t) INSERT {formsubst i p |i,p| p IN E})]]
#eval esubterms

#eval phrase 31
#eval parse_as_infix ("|----", (11, "right"))

#eval phrase 32
#eval parse_as_infix ("|--_scong", (11, "right"))

#eval phrase 33
#eval parse_as_infix ("|--_sachain", (11, "right"))

#eval phrase 34
#eval parse_as_infix ("|--_scchain", (11, "right"))

#eval phrase 35
unsafe def scprovable_triple : thm × thm × thm := keep "scprovable_triple" fun _ =>
  newInductive
   [[(!s t. E |--_axiom s === t ==> E |--_sachain s === t) /\
     (!s t. E |--_scong s === t ==> E |--_scchain s === t) /\
     (!s t u. E |--_axiom s === t /\ E |---- t === u /\ t IN esubterms E s u
              ==> E |--_sachain s === u) /\
     (!s t u. E |--_scong s === t /\ E |--_sachain t === u /\ t IN esubterms E s u
              ==> E |--_scchain s === u) /\
     (!f a b. ALL2 (\l r. E |---- l === r) a b
              ==> E |--_scong Fn f a === Fn f b) /\
     (!s t. (s = t) \/ E |--_sachain s === t \/ E |--_scchain s === t
            ==> E |---- s === t)]]
unsafe def scprovable_RULES : thm := scprovable_triple.1
unsafe def scprovable_INDUCT : thm := scprovable_triple.2.1
unsafe def scprovable_CASES : thm := scprovable_triple.2.2
#eval do IO.println scprovable_RULES; IO.println scprovable_INDUCT; IO.println scprovable_CASES

#eval phrase 36
unsafe def ESUBTERMS_TRIVIAL_L : thm := keep "ESUBTERMS_TRIVIAL_L" fun _ => (do
  prove ([[!u. u IN subterms s ==> u IN esubterms E s t]])
   (REWRITE_TAC [esubterms, subtermss, IN_UNIONS, IN_INSERT, IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC [[subterms s UNION subterms t]] THEN
    ASM_REWRITE_TAC [IN_UNION] THEN
    EXISTS_TAC [[s === t]] THEN REWRITE_TAC [subtermsa, Equal_DEF, MAP, LIST_UNION] THEN
    REWRITE_TAC [UNION_EMPTY])
  : ExceptT String IO thm).run
#eval ESUBTERMS_TRIVIAL_L

#eval phrase 37
unsafe def ESUBTERMS_TRIVIAL_R : thm := keep "ESUBTERMS_TRIVIAL_R" fun _ => (do
  prove ([[!u. u IN subterms t ==> u IN esubterms E s t]])
   (REWRITE_TAC [esubterms, subtermss, IN_UNIONS, IN_INSERT, IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC [[subterms s UNION subterms t]] THEN
    ASM_REWRITE_TAC [IN_UNION] THEN
    EXISTS_TAC [[s === t]] THEN REWRITE_TAC [subtermsa, Equal_DEF, MAP, LIST_UNION] THEN
    REWRITE_TAC [UNION_EMPTY])
  : ExceptT String IO thm).run
#eval ESUBTERMS_TRIVIAL_R

#eval phrase 38
unsafe def SCPROVABLE_SUBTERMS : thm := keep "SCPROVABLE_SUBTERMS" fun _ => (do
  prove ([[!a. E |--_sachain a
         ==> !s t. (a = (s === t))
                   ==> !u v. s IN esubterms E u v]])
   (GEN_TAC THEN HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [scprovable_CASES] THEN
    SUBGOAL_THEN
     ([[!a. E |--_axiom a
         ==> !s t. (a = (s === t))
                   ==> !u v. s IN esubterms E u v]])
     (fun th => STRIP_TAC THEN ASM_REWRITE_TAC [EQUAL_INJ_ALT] THEN
                ASM_MESON_TAC [th]) THEN
    GEN_TAC THEN ONCE_REWRITE_TAC [aprovable_CASES] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [FORMSUBST_EQ, EQUAL_INJ_ALT] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    (REWRITE_TAC [esubterms, subtermss, IN_UNIONS, IN_ELIM_THM, IN_INSERT] THEN
     EXISTS_TAC [[subtermsa (formsubst i (s === t))]] THEN CONJ_TAC THENL
      [ASM_MESON_TAC [], ALL_TAC] THEN
     REWRITE_TAC [subtermsa, FORMSUBST_EQ] THEN
     REWRITE_TAC [subtermsa, Equal_DEF, MAP, LIST_UNION, UNION_EMPTY] THEN
     MESON_TAC [IN_UNION, SUBTERMS_REFL]))
  : ExceptT String IO thm).run
#eval SCPROVABLE_SUBTERMS

#eval phrase 39
unsafe def SCPROVABLE_CPROVABLE_LEMMA : thm := keep "SCPROVABLE_CPROVABLE_LEMMA" fun _ => (do
  let sr ← ExceptT.mk (HolLight.SPEC_ALL scprovable_RULES)
  let sr2 ← liftExcept (HolCore.Lib.el 2 (Session.CONJUNCTS sr))
  let sr3 ← liftExcept (HolCore.Lib.el 3 (Session.CONJUNCTS sr))
  prove ([[(!a. E |--_achain a ==> !s t. (a = (s === t)) ==> E |--_sachain s === t) /\
     (!a. E |--_cchain a ==> !s t. (a = (s === t)) ==> E |--_scchain s === t) /\
     (!a. E |--_cong a ==> !s t. (a = (s === t)) ==> E |--_scong s === t) /\
     (!a. E |--- a ==> !s t. (a = (s === t)) ==> E |---- s === t)]])
   (MATCH_MP_TAC cprovable_INDUCT THEN
    SIMP_TAC [EQUAL_INJ_ALT, LEFT_FORALL_IMP_THM,
             RIGHT_EXISTS_AND_THM, LEFT_EXISTS_AND_THM, EXISTS_REFL] THEN
    REWRITE_TAC [scprovable_RULES] THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC sr2 THEN
      EXISTS_TAC [[t:term]] THEN ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MP_TAC oTIO HolLight.GEN_REWRITE_RULE HolCore.Lib.I [aprovable_CASES]) THEN
      REWRITE_TAC [FORMSUBST_EQ, EQUAL_INJ_ALT] THEN
      DISCH_THEN (HolLight.REPEAT_TCL DISJ_CASES_THEN MP_TAC) THEN
      (REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [ [[v:term]], [[w:term]], [[i:num->term]] ] THEN
      DISCH_THEN (STRIP_ASSUME_TAC oTIO HolLight.GSYM) THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [esubterms, subtermss, IN_UNIONS, IN_ELIM_THM, IN_INSERT] THEN
      EXISTS_TAC [[subtermsa (formsubst i (v === w))]] THEN CONJ_TAC THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      REWRITE_TAC [subtermsa, FORMSUBST_EQ] THEN
      REWRITE_TAC [subtermsa, Equal_DEF, MAP, LIST_UNION, UNION_EMPTY] THEN
      MESON_TAC [IN_UNION, SUBTERMS_REFL]),
      ALL_TAC] THEN
    MATCH_MP_TAC sr3 THEN
    EXISTS_TAC [[t:term]] THEN ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [SCPROVABLE_SUBTERMS])
  : ExceptT String IO thm).run
#eval SCPROVABLE_CPROVABLE_LEMMA

#eval phrase 40
unsafe def SCPROVABLE_CPROVABLE : thm := keep "SCPROVABLE_CPROVABLE" fun _ => (do
  prove ([[!E s t. (E |--- s === t) <=> (E |---- s === t)]])
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [ASM_MESON_TAC [SCPROVABLE_CPROVABLE_LEMMA], ALL_TAC] THEN
    SUBGOAL_THEN
     ([[(!a. E |--_sachain a ==> !s t. (a = (s === t)) ==> E |--_achain s === t) /\
        (!a. E |--_scchain a ==> !s t. (a = (s === t)) ==> E |--_cchain s === t) /\
        (!a. E |--_scong a ==> !s t. (a = (s === t)) ==> E |--_cong s === t) /\
        (!a. E |---- a ==> !s t. (a = (s === t)) ==> E |--- s === t)]])
     (fun th => MESON_TAC [th]) THEN
    MATCH_MP_TAC scprovable_INDUCT THEN
    SIMP_TAC [EQUAL_INJ_ALT, LEFT_FORALL_IMP_THM,
             RIGHT_EXISTS_AND_THM, LEFT_EXISTS_AND_THM, EXISTS_REFL] THEN
    REWRITE_TAC [cprovable_RULES] THEN MESON_TAC [cprovable_RULES])
  : ExceptT String IO thm).run
#eval SCPROVABLE_CPROVABLE

#eval phrase 41
unsafe def SCPROVABLE_PROVABLE : thm := keep "SCPROVABLE_PROVABLE" fun _ => (do
  prove ([[!E s t. (E |--- s === t) <=> (E |- s === t)]])
   (MESON_TAC [SCPROVABLE_CPROVABLE, CPROVABLE_PROVABLE])
  : ExceptT String IO thm).run
#eval SCPROVABLE_PROVABLE

#eval phrase 42
unsafe def Eqclause_Func : thm := keep "Eqclause_Func" fun _ => new_definition
  [[Eqclause_Func (f,n) =
      set_of_list
        (CONS (Fn f (MAP FST (Varpairs n)) === Fn f (MAP SND (Varpairs n)))
              (MAP (\(s,t). Not(s === t)) (Varpairs n)))]]
#eval Eqclause_Func

#eval phrase 43
unsafe def Eqclause_Pred : thm := keep "Eqclause_Pred" fun _ => new_definition
  [[Eqclause_Pred (p,n) =
       set_of_list
        (CONS (Atom p (MAP SND (Varpairs n)))
              (CONS (Not(Atom p (MAP FST (Varpairs n))))
                    (MAP (\(s,t). Not(s === t)) (Varpairs n))))]]
#eval Eqclause_Pred

#eval phrase 44
unsafe def Eqclauses_DEF : thm := keep "Eqclauses_DEF" fun _ => new_definition
  [[Eqclauses L =
     {(V 0 === V 0)} INSERT
     {(Not(V 0 === V 1)), (Not(V 2 === V 1)), (V 0 === V 2)} INSERT
     ({Eqclause_Func fa | fa IN FST L} UNION
      {Eqclause_Pred pa | pa IN SND L})]]
#eval Eqclauses_DEF

#eval phrase 45
unsafe def EQCLAUSE_EQAXIOM_FUNC : thm := keep "EQCLAUSE_EQAXIOM_FUNC" fun _ => (do
  let taut1 ← ExceptT.mk (TAUT [[(a \/ b) /\ c <=> a /\ c \/ b /\ c]])
  let taut2 ← ExceptT.mk (TAUT [[(a ==> (b <=> c)) ==> (a ==> b <=> a ==> c)]])
  let taut3 ← ExceptT.mk (TAUT [[(~a <=> b) ==> (c \/ a <=> b ==> c)]])
  prove ([[!M f n. ~(Dom M :A->bool = {})
             ==> (M satisfies {(interp(Eqclause_Func (f,n)))} <=>
                  M satisfies {(Eqaxiom_Func (f,n))})]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [Eqclause_Func, Eqaxiom_Func] THEN
    SIMP_TAC [satisfies, IN_INSERT, NOT_IN_EMPTY] THEN
    REWRITE_TAC [LEFT_FORALL_IMP_THM, RIGHT_EXISTS_AND_THM] THEN
    REWRITE_TAC [EXISTS_REFL] THEN
    SIMP_TAC [HOLDS_UCLOSE_ALL_EQ] THEN
    SIMP_TAC [HOLDS_INTERP, FINITE_SET_OF_LIST] THEN
    REWRITE_TAC [set_of_list, IN_INSERT, HOLDS] THEN
    REWRITE_TAC [taut1, EXISTS_OR_THM] THEN
    REWRITE_TAC [UNWIND_THM2] THEN DISCH_TAC THEN
    AP_TERM_TAC THEN HolLight.GEN_REWRITE_TAC HolCore.Lib.I [FUN_EQ_THM] THEN
    X_GEN_TAC [[v:num->A]] THEN REWRITE_TAC [] THEN
    MATCH_MP_TAC taut2 THEN
    DISCH_TAC THEN
    MATCH_MP_TAC taut3 THEN
    SPEC_TAC ([[Varpairs n]], [[l:(term#term)list]]) THEN
    ONCE_REWRITE_TAC [CONJ_SYM] THEN
    REWRITE_TAC [EX_MEM, IN_SET_OF_LIST] THEN
    REWRITE_TAC [NOT_EX, ALL_MAP, o_THM] THEN
    MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC [ALL, ITLIST, HOLDS, MAP] THEN SIMP_TAC [] THEN
    HolLight.GEN_REWRITE_TAC HolCore.Lib.I [FORALL_PAIR_THM] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [o_THM] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC [HOLDS])
  : ExceptT String IO thm).run
#eval EQCLAUSE_EQAXIOM_FUNC

#eval phrase 46
unsafe def Eqaxiom_Pred_imp : thm := keep "Eqaxiom_Pred_imp" fun _ => new_definition
  [[Eqaxiom_Pred_imp (p,n) =
        uclose
         (ITLIST (&&) (MAP (\(s,t). s === t) (Varpairs n)) True
          --> Atom p (MAP FST (Varpairs n))
              --> Atom p (MAP SND (Varpairs n)))]]
#eval Eqaxiom_Pred_imp

#eval phrase 47
unsafe def lemma : thm := keep "lemma" fun _ => (do
  prove ([[a INSERT s = {a} UNION s]]) (SET_TAC [])
  : ExceptT String IO thm).run
#eval lemma

#eval phrase 48
unsafe def EQCLAUSES_EQAXIOMS : thm := keep "EQCLAUSES_EQAXIOMS" fun _ => (do
  let taut1 ← ExceptT.mk (TAUT [[(a' <=> a) /\ (a ==> (b' <=> b)) ==> (a' /\ b' <=> a /\ b)]])
  let taut2 ← ExceptT.mk (TAUT [[(a \/ b) /\ c <=> a /\ c \/ b /\ c]])
  let taut3 ← ExceptT.mk (TAUT [[(a ==> (b <=> c)) ==> (a ==> b <=> a ==> c)]])
  let taut4 ← ExceptT.mk (TAUT [[(~c <=> d) ==> (a \/ ~b \/ c <=> d ==> b ==> a)]])
  let taut5 ← ExceptT.mk (TAUT
    [[a /\ (x <=> b) /\ (y <=> c) /\ (d <=> e)
      ==> x ==> y ==> (a ==> b ==> c ==> d) ==> e]])
  prove ([[!M L. ~(Dom M :A->bool = {})
           ==> (M satisfies (IMAGE interp (Eqclauses L)) <=>
                M satisfies (Eqaxioms L))]])
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [Eqclauses_DEF, Eqaxioms_DEF, IMAGE_CLAUSES, IMAGE_UNION] THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV o HolLight.RAND_CONV) [lemma] THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV) [lemma] THEN
    REWRITE_TAC [SATISFIES_UNION] THEN
    MATCH_MP_TAC taut1 THEN
    CONJ_TAC THENL
     [REWRITE_TAC [SATISFIES_1] THEN ASM_REWRITE_TAC [HOLDS_UCLOSE] THEN
      SIMP_TAC [HOLDS_INTERP, FINITE_RULES] THEN
      REWRITE_TAC [IN_SING] THEN MESON_TAC [],
      ALL_TAC] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC taut1 THEN
    CONJ_TAC THENL
     [REWRITE_TAC [SATISFIES_1] THEN ASM_REWRITE_TAC [HOLDS_UCLOSE] THEN
      SIMP_TAC [HOLDS_INTERP, FINITE_INSERT, FINITE_EMPTY] THEN
      REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY, HOLDS] THEN
      REWRITE_TAC [taut2] THEN
      REWRITE_TAC [EXISTS_OR_THM, UNWIND_THM2] THEN
      REWRITE_TAC [HOLDS] THEN AP_TERM_TAC THEN ABS_TAC THEN
      CONV_TAC TAUT, ALL_TAC] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC taut1 THEN
    CONJ_TAC THENL
     [REWRITE_TAC [SATISFIES_IMAGE] THEN
      REWRITE_TAC [satisfies, IN_ELIM_THM] THEN
      SIMP_TAC [RIGHT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM] THEN
      FIRST_ASSUM (MP_TAC oTIO HolLight.MATCH_MP EQCLAUSE_EQAXIOM_FUNC) THEN
      REWRITE_TAC [SATISFIES_1] THEN
      ONCE_REWRITE_TAC [FORALL_PAIR_THM] THEN MESON_TAC [], ALL_TAC] THEN
    DISCH_TAC THEN
    REWRITE_TAC [SATISFIES_IMAGE] THEN
    REWRITE_TAC [satisfies, IN_ELIM_THM] THEN
    ONCE_REWRITE_TAC [EXISTS_PAIR_THM] THEN
    SUBGOAL_THEN
     ([[!p n. (!v:num->A. valuation M v
                        ==> holds M v (interp(Eqclause_Pred(p,n)))) <=>
            (!v:num->A. valuation M v
                        ==> holds M v (Eqaxiom_Pred(p,n)))]])
     (fun th => MESON_TAC [th]) THEN
    GEN_TAC THEN GEN_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     [[!v:num->A. valuation M v ==> holds M v (Eqaxiom_Pred_imp(p,n))]] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [Eqclause_Pred, Eqaxiom_Pred_imp] THEN
      ASM_SIMP_TAC [HOLDS_UCLOSE_ALL_EQ] THEN
      SIMP_TAC [HOLDS_INTERP, FINITE_SET_OF_LIST] THEN
      REWRITE_TAC [set_of_list, IN_INSERT, HOLDS] THEN
      REWRITE_TAC [taut2, EXISTS_OR_THM] THEN
      REWRITE_TAC [UNWIND_THM2] THEN
      AP_TERM_TAC THEN HolLight.GEN_REWRITE_TAC HolCore.Lib.I [FUN_EQ_THM] THEN
      X_GEN_TAC [[v:num->A]] THEN REWRITE_TAC [] THEN
      MATCH_MP_TAC taut3 THEN
      DISCH_TAC THEN REWRITE_TAC [HOLDS] THEN
      MATCH_MP_TAC taut4 THEN
      SPEC_TAC ([[Varpairs n]], [[l:(term#term)list]]) THEN
      ONCE_REWRITE_TAC [CONJ_SYM] THEN
      REWRITE_TAC [EX_MEM, IN_SET_OF_LIST] THEN
      REWRITE_TAC [NOT_EX, ALL_MAP, o_THM] THEN
      MATCH_MP_TAC list_INDUCT THEN
      REWRITE_TAC [ALL, ITLIST, HOLDS, MAP] THEN SIMP_TAC [] THEN
      HolLight.GEN_REWRITE_TAC HolCore.Lib.I [FORALL_PAIR_THM] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC [o_THM] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC [HOLDS],
      ALL_TAC] THEN
    REWRITE_TAC [Eqaxiom_Pred_imp, Eqaxiom_Pred, HOLDS] THEN
    ASM_SIMP_TAC [HOLDS_UCLOSE_ALL_EQ, HOLDS] THEN
    EQ_TAC THEN SIMP_TAC [] THEN DISCH_TAC THEN X_GEN_TAC [[v:num->A]] THEN
    DISCH_TAC THEN DISCH_TAC THEN EQ_TAC THEN ASM_SIMP_TAC [] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC
     [[\x. if EVEN(x) then v(x + 1):A else v(x - 1)]]) THEN
    REWRITE_TAC [(← HolLight.GSYM MAP_o)] THEN
    MAP_EVERY UNDISCH_TAC
     [ [[Pred M p (MAP (termval M (v:num->A)) (MAP SND (Varpairs n)))]],
      [[holds M (v:num->A)
               (ITLIST (&&) (MAP (\(s,t). s === t) (Varpairs n)) True)]] ] THEN
    MATCH_MP_TAC taut5 THEN
    CONJ_TAC THENL
     [REWRITE_TAC [valuation] THEN GEN_TAC THEN COND_CASES_TAC THEN
      ASM_MESON_TAC [valuation], ALL_TAC] THEN
    SUBGOAL_THEN
     ([[!v:num->A x y. valuation M v
                     ==> (holds M v (V x === V y) <=> holds M v (V y === V x))]])
    ASSUME_TAC THENL
     [X_GEN_TAC [[w:num->A]] THEN REPEAT STRIP_TAC THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC oTIO HolLight.GEN_REWRITE_RULE HolCore.Lib.I [SATISFIES_1])) THEN
      ASM_REWRITE_TAC [HOLDS_UCLOSE] THEN
      REWRITE_TAC [IMP_IMP] THEN
      REWRITE_TAC [AND_FORALL_THM] THEN
      DISCH_THEN (fun th => HolLight.tactic_of do
        let t1 ← HolLight.SPEC ([[\n. if n = 2 then (w:num->A)(y) else w(x)]]) th
        let t2 ← HolLight.SPEC ([[\n. if n = 2 then (w:num->A)(x) else w(y)]]) th
        pure (MP_TAC t1 THEN MP_TAC t2)) THEN
      REWRITE_TAC [HOLDS, Equal_DEF, MAP, termval, ARITH_EQ, valuation] THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [valuation]) THEN
      ONCE_REWRITE_TAC [COND_RAND] THEN ONCE_REWRITE_TAC [COND_RATOR] THEN
      ASM_REWRITE_TAC [COND_ID] THEN CONV_TAC TAUT, ALL_TAC] THEN
    CONJ_TAC THENL
     [SPEC_TAC ([[n:num]], [[n:num]]) THEN
      INDUCT_TAC THEN ASM_REWRITE_TAC [Varpairs_DEF, MAP, ITLIST, HOLDS] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC [[holds M (v:num->A) (V(2 * n + 1) === V(2 * n))]] THEN
      CONJ_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN
      REWRITE_TAC [HOLDS, Equal_DEF, MAP, termval, ARITH_EQ] THEN
      REWRITE_TAC [EVEN_ADD, EVEN_MULT, ARITH] THEN REWRITE_TAC [ADD_SUB],
      ALL_TAC] THEN
    CONJ_TAC THEN
    (AP_TERM_TAC THEN SPEC_TAC ([[n:num]], [[n:num]]) THEN
     INDUCT_TAC THEN ASM_REWRITE_TAC [Varpairs_DEF, MAP] THEN
     REWRITE_TAC [CONS_11] THEN
     REWRITE_TAC [ADD_SUB, o_THM, termval, EVEN_ADD, EVEN_MULT, ARITH]))
  : ExceptT String IO thm).run
#eval EQCLAUSES_EQAXIOMS

#eval phrase 49
unsafe def FUNCTIONS_VAREQLIST : thm := keep "FUNCTIONS_VAREQLIST" fun _ => (do
  prove ([[!n. functions(set_of_list (MAP (\(s,t). Not(s === t)) (Varpairs n))) = {}]])
   (INDUCT_TAC THEN REWRITE_TAC [Varpairs_DEF, MAP, set_of_list] THENL
     [REWRITE_TAC [functions, NOT_IN_EMPTY, IN_ELIM_THM, EXTENSION, IN_UNIONS],
      ASM_REWRITE_TAC [FUNCTIONS_INSERT, UNION_EMPTY] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC [Equal_DEF, functions_form, Not_DEF, MAP, functions_term] THEN
      REWRITE_TAC [LIST_UNION, UNION_EMPTY]])
  : ExceptT String IO thm).run
#eval FUNCTIONS_VAREQLIST

#eval phrase 50
unsafe def FUNCTIONS_TERM_FN_VARPAIRS : thm := keep "FUNCTIONS_TERM_FN_VARPAIRS" fun _ => (do
  prove ([[(!f n. functions_term(Fn f (MAP FST (Varpairs n))) = {(f,n)}) /\
     (!f n. functions_term(Fn f (MAP SND (Varpairs n))) = {(f,n)})]])
   (REWRITE_TAC [functions_term, LENGTH_VARPAIRS, LENGTH_MAP] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     ([[(LIST_UNION (MAP functions_term (MAP FST (Varpairs n))) = {}) /\
        (LIST_UNION (MAP functions_term (MAP SND (Varpairs n))) = {})]])
     (fun th => REWRITE_TAC [th]) THEN
    SPEC_TAC ([[n:num]], [[n:num]]) THEN
    INDUCT_TAC THEN REWRITE_TAC [Varpairs_DEF, MAP, LIST_UNION, functions_term] THEN
    ASM_REWRITE_TAC [UNION_EMPTY])
  : ExceptT String IO thm).run
#eval FUNCTIONS_TERM_FN_VARPAIRS

#eval phrase 51
unsafe def FUNCTIONS_FORM_PRED_VARPAIRS : thm := keep "FUNCTIONS_FORM_PRED_VARPAIRS" fun _ => (do
  prove ([[(!p n. functions_form(Atom p (MAP FST (Varpairs n))) = {}) /\
     (!p n. functions_form(Atom p (MAP SND (Varpairs n))) = {})]])
   (REWRITE_TAC [functions_form, LENGTH_VARPAIRS, LENGTH_MAP] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     ([[(LIST_UNION (MAP functions_term (MAP FST (Varpairs n))) = {}) /\
        (LIST_UNION (MAP functions_term (MAP SND (Varpairs n))) = {})]])
     (fun th => REWRITE_TAC [th]) THEN
    SPEC_TAC ([[n:num]], [[n:num]]) THEN
    INDUCT_TAC THEN REWRITE_TAC [Varpairs_DEF, MAP, LIST_UNION, functions_term] THEN
    ASM_REWRITE_TAC [UNION_EMPTY])
  : ExceptT String IO thm).run
#eval FUNCTIONS_FORM_PRED_VARPAIRS

#eval phrase 52
unsafe def FUNCTIONS_FORM_EQCLAUSE_FUNC : thm := keep "FUNCTIONS_FORM_EQCLAUSE_FUNC" fun _ => (do
  prove ([[!fn. functions_form(interp(Eqclause_Func fn)) = {fn}]])
   (HolLight.GEN_REWRITE_TAC HolCore.Lib.I [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[f:num]], [[n:num]] ] THEN
    REWRITE_TAC [Eqclause_Func] THEN
    SIMP_TAC [FUNCTIONS_FORM_INTERP, FINITE_SET_OF_LIST] THEN
    REWRITE_TAC [set_of_list, FUNCTIONS_INSERT, FUNCTIONS_UNION] THEN
    REWRITE_TAC [functions_form, Equal_DEF, MAP, FUNCTIONS_TERM_FN_VARPAIRS] THEN
    REWRITE_TAC [(← HolLight.GSYM Equal_DEF), FUNCTIONS_VAREQLIST] THEN
    REWRITE_TAC [LIST_UNION, UNION_EMPTY, UNION_ACI])
  : ExceptT String IO thm).run
#eval FUNCTIONS_FORM_EQCLAUSE_FUNC

#eval phrase 53
unsafe def FUNCTIONS_FORM_EQCLAUSE_PRED : thm := keep "FUNCTIONS_FORM_EQCLAUSE_PRED" fun _ => (do
  prove ([[!pn. functions_form(interp(Eqclause_Pred pn)) = {}]])
   (HolLight.GEN_REWRITE_TAC HolCore.Lib.I [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[p:num]], [[n:num]] ] THEN
    REWRITE_TAC [Eqclause_Pred] THEN
    SIMP_TAC [FUNCTIONS_FORM_INTERP, FINITE_SET_OF_LIST] THEN
    REWRITE_TAC [set_of_list, FUNCTIONS_INSERT, FUNCTIONS_UNION] THEN
    REWRITE_TAC [FUNCTIONS_VAREQLIST, UNION_EMPTY] THEN
    REWRITE_TAC [Not_DEF, FUNCTIONS_FORM_PRED_VARPAIRS] THEN
    ONCE_REWRITE_TAC [functions_form] THEN
    REWRITE_TAC [FUNCTIONS_FORM_PRED_VARPAIRS] THEN
    REWRITE_TAC [functions_form, UNION_EMPTY])
  : ExceptT String IO thm).run
#eval FUNCTIONS_FORM_EQCLAUSE_PRED

#eval phrase 54
unsafe def FUNCTIONS_EQCLAUSES : thm := keep "FUNCTIONS_EQCLAUSES" fun _ => (do
  let taut1 ← ExceptT.mk (TAUT [[(a \/ b) /\ c <=> a /\ c \/ b /\ c]])
  let taut2 ← ExceptT.mk (TAUT [[a /\ b <=> ~(a ==> ~b)]])
  let taut3 ← ExceptT.mk (TAUT [[(a /\ b) /\ c /\ d <=> b /\ a /\ c /\ d]])
  let taut4 ← ExceptT.mk (TAUT [[a /\ b /\ c <=> a /\ ~(b ==> ~c)]])
  prove ([[functions(IMAGE interp (Eqclauses(language s))) = functions s]])
   (REWRITE_TAC [functions, Eqclauses_DEF] THEN
    HolLight.GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN
    REWRITE_TAC [IN_ELIM_THM, IN_IMAGE, IN_UNIONS] THEN
    HolLight.GEN_REWRITE_TAC HolCore.Lib.I [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[f:num]], [[n:num]] ] THEN
    REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.BINDER_CONV) [SWAP_EXISTS_THM] THEN
    REWRITE_TAC [(← HolLight.GSYM CONJ_ASSOC)] THEN REWRITE_TAC [UNWIND_THM2] THEN
    REWRITE_TAC [IN_INSERT, IN_UNION, NOT_IN_EMPTY, IN_ELIM_THM] THEN
    REWRITE_TAC [taut1] THEN
    REWRITE_TAC [EXISTS_OR_THM] THEN REWRITE_TAC [UNWIND_THM2] THEN
    SIMP_TAC [FUNCTIONS_FORM_INTERP, FINITE_INSERT, FINITE_EMPTY] THEN
    REWRITE_TAC [functions, IN_UNIONS, IN_ELIM_THM, IN_INSERT, NOT_IN_EMPTY] THEN
    REWRITE_TAC [UNWIND_THM2] THEN
    REWRITE_TAC [taut1] THEN
    REWRITE_TAC [EXISTS_OR_THM, UNWIND_THM2] THEN
    REWRITE_TAC [functions_form, Not_DEF, Equal_DEF, MAP, functions_term] THEN
    REWRITE_TAC [LIST_UNION, UNION_EMPTY] THEN
    REWRITE_TAC [UNWIND_THM2, NOT_IN_EMPTY] THEN
    ONCE_REWRITE_TAC [taut2] THEN SIMP_TAC [] THEN
    REWRITE_TAC [NOT_IMP] THEN REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.BINOP_CONV o HolLight.BINDER_CONV) [SWAP_EXISTS_THM] THEN
    ONCE_REWRITE_TAC [taut3] THEN
    REWRITE_TAC [UNWIND_THM2] THEN
    ONCE_REWRITE_TAC [EXISTS_PAIR_THM] THEN
    REWRITE_TAC [Eqclause_Func, Eqclause_Pred, FINITE_SET_OF_LIST,
                FUNCTIONS_FORM_INTERP] THEN
    REWRITE_TAC [(← HolLight.GSYM Eqclause_Func), (← HolLight.GSYM Eqclause_Pred)] THEN
    REWRITE_TAC [FUNCTIONS_FORM_EQCLAUSE_PRED, FUNCTIONS_FORM_EQCLAUSE_FUNC] THEN
    ONCE_REWRITE_TAC [taut4] THEN
    SIMP_TAC [IN_INSERT, NOT_IN_EMPTY] THEN REWRITE_TAC [language] THEN
    REWRITE_TAC [functions, IN_UNIONS, IN_ELIM_THM] THEN
    REWRITE_TAC [PAIR_EQ, NOT_IMP] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval FUNCTIONS_EQCLAUSES

#eval phrase 55
unsafe def FUNCTIONS_FORM_NOT_UCLOSE : thm := keep "FUNCTIONS_FORM_NOT_UCLOSE" fun _ => (do
  prove ([[functions_form(Not(uclose p)) = functions_form p]])
   (REWRITE_TAC [Not_DEF, functions_form, FUNCTIONS_FORM_UCLOSE, UNION_EMPTY])
  : ExceptT String IO thm).run
#eval FUNCTIONS_FORM_NOT_UCLOSE

#eval phrase 56
unsafe def PREDICATES_FORM_NOT_UCLOSE : thm := keep "PREDICATES_FORM_NOT_UCLOSE" fun _ => (do
  prove ([[predicates_form(Not(uclose p)) = predicates_form p]])
   (REWRITE_TAC [Not_DEF, predicates_form, PREDICATES_FORM_UCLOSE, UNION_EMPTY])
  : ExceptT String IO thm).run
#eval PREDICATES_FORM_NOT_UCLOSE

#eval phrase 57
unsafe def FUNCTIONS_INSERT_NOT_UCLOSE : thm := keep "FUNCTIONS_INSERT_NOT_UCLOSE" fun _ => (do
  prove ([[functions(p INSERT s) = functions(Not(uclose p) INSERT s)]])
   (ONCE_REWRITE_TAC [EXTENSION] THEN
    REWRITE_TAC [functions, IN_UNIONS, IN_ELIM_THM] THEN
    REWRITE_TAC [IN_INSERT] THEN MESON_TAC [FUNCTIONS_FORM_NOT_UCLOSE])
  : ExceptT String IO thm).run
#eval FUNCTIONS_INSERT_NOT_UCLOSE

#eval phrase 58
unsafe def PREDICATES_INSERT_NOT_UCLOSE : thm := keep "PREDICATES_INSERT_NOT_UCLOSE" fun _ => (do
  prove ([[predicates(p INSERT s) = predicates(Not(uclose p) INSERT s)]])
   (ONCE_REWRITE_TAC [EXTENSION] THEN
    REWRITE_TAC [predicates, IN_UNIONS, IN_ELIM_THM] THEN
    REWRITE_TAC [IN_INSERT] THEN MESON_TAC [PREDICATES_FORM_NOT_UCLOSE])
  : ExceptT String IO thm).run
#eval PREDICATES_INSERT_NOT_UCLOSE

#eval phrase 59
unsafe def LANGUAGE_INSERT_NOT_UCLOSE : thm := keep "LANGUAGE_INSERT_NOT_UCLOSE" fun _ => (do
  prove ([[language(p INSERT s) = language (Not(uclose p) INSERT s)]])
   (REWRITE_TAC [language, (← HolLight.GSYM FUNCTIONS_INSERT_NOT_UCLOSE),
                (← HolLight.GSYM PREDICATES_INSERT_NOT_UCLOSE)])
  : ExceptT String IO thm).run
#eval LANGUAGE_INSERT_NOT_UCLOSE

#eval phrase 60
unsafe def lemma1 : thm := keep "lemma1" fun _ => (do
  prove ([[(!m. p m /\ q m /\ r m /\ s m ==> t m) <=>
    ~(?m. p m /\ q m /\ r m /\ s m /\ ~(t m))]])
   (MESON_TAC [])
  : ExceptT String IO thm).run
#eval lemma1

#eval phrase 61
unsafe def lemma2 : thm := keep "lemma2" fun _ => (do
  prove ([[(x INSERT s) UNION t = x INSERT (s UNION t)]])
   (SET_TAC [])
  : ExceptT String IO thm).run
#eval lemma2

#eval phrase 62
unsafe def EQCLAUSES_DEFINITE : thm := keep "EQCLAUSES_DEFINITE" fun _ => (do
  let taut1 ← ExceptT.mk (TAUT [[(a ==> c) /\ (b ==> ~c) ==> ((a \/ b) /\ c <=> a)]])
  let taut2 ← ExceptT.mk (TAUT
    [[(a ==> c) /\ (b ==> ~c) /\ (d ==> ~c)
      ==> ((a \/ b \/ d) /\ c <=> a)]])
  prove ([[!L cl. cl IN Eqclauses L ==> definite cl]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [Eqclauses_DEF] THEN
    REWRITE_TAC [IN_INSERT, IN_UNION, IN_ELIM_THM] THEN
    ONCE_REWRITE_TAC [EXISTS_PAIR_THM] THEN
    DISCH_THEN (DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THENL
     [REWRITE_TAC [definite, IN_SING] THEN
      SUBGOAL_THEN ([[{p | (p = V 0 === V 0) /\ positive p} = {(V 0 === V 0)}]])
      SUBST1_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_SING,
                    positive, negative, Equal_DEF, Not_DEF] THEN
        MESON_TAC [form_DISTINCT], ALL_TAC] THEN
      SIMP_TAC [clause, FINITE_INSERT, CARD_CLAUSES, FINITE_EMPTY] THEN
      REWRITE_TAC [NOT_IN_EMPTY, ARITH, IN_SING] THEN
      SIMP_TAC [Equal_DEF] THEN MESON_TAC [LITERAL],
      ALL_TAC] THEN
    DISCH_THEN (DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THENL
     [REWRITE_TAC [definite, IN_SING] THEN
      SUBGOAL_THEN
       ([[{p | p IN {(Not (V 0 === V 1)), (Not (V 2 === V 1)), (V 0 === V 2)} /\
             positive p} = {(V 0 === V 2)}]])
      SUBST1_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_INSERT, NOT_IN_EMPTY] THEN
        REWRITE_TAC [Equal_DEF, positive, negative] THEN
        MESON_TAC [Not_DEF, form_DISTINCT], ALL_TAC] THEN
      SIMP_TAC [clause, FINITE_INSERT, CARD_CLAUSES, FINITE_EMPTY] THEN
      REWRITE_TAC [NOT_IN_EMPTY, ARITH, IN_INSERT] THEN
      SIMP_TAC [Equal_DEF] THEN MESON_TAC [LITERAL],
      ALL_TAC] THEN
    DISCH_THEN (DISJ_CASES_THEN MP_TAC) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[f:num]], [[n:num]] ] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [Eqclause_Pred, Eqclause_Func, definite, set_of_list] THENL
     [SUBGOAL_THEN
       ([[{p | p IN
         (Fn f (MAP FST (Varpairs n)) === Fn f (MAP SND (Varpairs n))) INSERT
         set_of_list (MAP (\(s,t). Not (s === t)) (Varpairs n)) /\
         positive p} =
        {(Fn f (MAP FST (Varpairs n)) === Fn f (MAP SND (Varpairs n)))}]])
      SUBST1_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_INSERT] THEN GEN_TAC THEN
        REWRITE_TAC [NOT_IN_EMPTY] THEN
        MATCH_MP_TAC taut1 THEN
        CONJ_TAC THEN SIMP_TAC [] THENL
         [DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN
          REWRITE_TAC [positive, negative, Equal_DEF, Not_DEF, form_DISTINCT],
          ALL_TAC] THEN
        REWRITE_TAC [IN_SET_OF_LIST, MEM_MAP, EXISTS_PAIR_THM] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
        CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
        REWRITE_TAC [positive, negative] THEN MESON_TAC [],
        ALL_TAC] THEN
      SIMP_TAC [clause, CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY,
               NOT_IN_EMPTY, ARITH, FINITE_SET_OF_LIST] THEN
      REWRITE_TAC [IN_INSERT, IN_SET_OF_LIST, MEM_MAP, EXISTS_PAIR_THM] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      ASM_REWRITE_TAC [LITERAL, Equal_DEF], ALL_TAC] THEN
    SUBGOAL_THEN
     ([[{p | p IN
       Atom f (MAP SND (Varpairs n)) INSERT
         Not (Atom f (MAP FST (Varpairs n))) INSERT
         set_of_list (MAP (\(s,t). Not (s === t)) (Varpairs n)) /\
         positive p} =
      {(Atom f (MAP SND (Varpairs n)))}]])
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_INSERT] THEN GEN_TAC THEN
      REWRITE_TAC [NOT_IN_EMPTY] THEN
      MATCH_MP_TAC taut2 THEN
      CONJ_TAC THEN SIMP_TAC [] THENL
       [DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN
        REWRITE_TAC [positive, negative, Equal_DEF, Not_DEF, form_DISTINCT],
        ALL_TAC] THEN
      CONJ_TAC THENL [MESON_TAC [positive, negative], ALL_TAC] THEN
      REWRITE_TAC [IN_SET_OF_LIST, MEM_MAP, EXISTS_PAIR_THM] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC [positive, negative] THEN MESON_TAC [],
      ALL_TAC] THEN
    SIMP_TAC [clause, CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY,
             NOT_IN_EMPTY, ARITH, FINITE_SET_OF_LIST] THEN
    REWRITE_TAC [IN_INSERT, IN_SET_OF_LIST, MEM_MAP, EXISTS_PAIR_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    ASM_REWRITE_TAC [LITERAL, Equal_DEF])
  : ExceptT String IO thm).run
#eval EQCLAUSES_DEFINITE

#eval phrase 63
unsafe def EQLOGIC_COMPLETE : thm := keep "EQLOGIC_COMPLETE" fun _ => (do
  let pr ← ExceptT.mk (HolLight.SPEC_ALL provable_RULES)
  let pr4 ← liftExcept (HolCore.Lib.el 4 (Session.CONJUNCTS pr))
  let taut_nd ← ExceptT.mk (TAUT [[a /\ b /\ c /\ d <=> a /\ b /\ c /\ (b ==> d)]])
  let taut_bd ← ExceptT.mk (TAUT [[a /\ b /\ c /\ (b ==> d) <=> a /\ b /\ c /\ d]])
  let taut_abc ← ExceptT.mk (TAUT [[a /\ b /\ c <=> a /\ b /\ (b ==> c)]])
  let taut_bc ← ExceptT.mk (TAUT [[a /\ b /\ (b ==> c) <=> a /\ b /\ c]])
  let taut_minimal ← ExceptT.mk (TAUT [[b /\ c /\ a ==> (a /\ b ==> (c <=> d)) ==> d]])
  let taut_big ← ExceptT.mk (TAUT
    [[(w /\ x ==> a1) /\ (w ==> b1) /\
      (w ==> b1 ==> y ==> c1 /\ d1) /\ (w ==> e1 ==> z)
      ==> (a1 /\ b1 /\ c1 /\ d1 ==> e1) ==> w /\ x /\ y ==> z]])
  let taut_ab ← ExceptT.mk (TAUT [[(a /\ c ==> d) ==> a /\ b /\ c ==> d]])
  let taut_bba ← ExceptT.mk (TAUT [[b /\ (b ==> a) ==> a /\ b]])
  let num2 ← ExceptT.mk (Session.num_CONV [[2]])
  let num1 ← ExceptT.mk (Session.num_CONV [[1]])
  prove ([[!E s t. (!e. e IN E ==> ?s t. e = (s === t)) /\
             (!M. interpretation (language((s === t) INSERT E)) M /\
                  ~(Dom M :term->bool = {}) /\
                  normal (functions ((s === t) INSERT E)) M /\
                  M satisfies E
                  ==> M satisfies {(s === t)})
             ==> E |- s === t]])
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ONCE_REWRITE_TAC [lemma1] THEN
    ONCE_REWRITE_TAC [taut_nd] THEN
    SIMP_TAC [SATISFIES_NOT] THEN
    REWRITE_TAC [taut_bd] THEN
    ONCE_REWRITE_TAC [FUNCTIONS_INSERT_NOT_UCLOSE, LANGUAGE_INSERT_NOT_UCLOSE] THEN
    REWRITE_TAC [NORMAL_THM] THEN
    ONCE_REWRITE_TAC [taut_abc] THEN
    REWRITE_TAC [lemma2] THEN SIMP_TAC [(← HolLight.GSYM SATISFIES_NOT)] THEN
    REWRITE_TAC [taut_bc] THEN
    REWRITE_TAC [SATISFIES_UNION, (← HolLight.GSYM CONJ_ASSOC), (← HolLight.GSYM lemma1)] THEN
    REWRITE_TAC [(← HolLight.GSYM FUNCTIONS_INSERT_NOT_UCLOSE),
                (← HolLight.GSYM LANGUAGE_INSERT_NOT_UCLOSE)] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     ([[?n. ibackchain ({{e} | e IN E} UNION
                      Eqclauses(language ((s === t) INSERT E)))
                     n (s === t)]])
    MP_TAC THENL
     [MP_TAC (← ExceptT.mk (HolLight.SPECL
       [ [[{{e} | e IN E} UNION
         Eqclauses(language ((s === t) INSERT E))]],
        [[s === t]] ] IBACKCHAIN_MINIMAL)) THEN
      MATCH_MP_TAC taut_minimal THEN
      CONJ_TAC THENL [REWRITE_TAC [Equal_DEF, atom], ALL_TAC] THEN
      SUBGOAL_THEN ([[functions (IMAGE interp {{e} | e IN E}) = functions E]])
      ASSUME_TAC THENL
       [MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC [[UNIONS {functions p | p IN {{e} | e IN E}}]] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC FUNCTIONS_IMAGE_INTERP THEN
          SIMP_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM, FINITE_RULES],
          ALL_TAC] THEN
        GEN_REWRITE_TAC HolLight.RAND_CONV [functions] THEN
        HolLight.GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN
        REWRITE_TAC [IN_UNIONS, functions, IN_ELIM_THM] THEN
        GEN_TAC THEN ONCE_REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN
        GEN_REWRITE_TAC HolLight.LAND_CONV [SWAP_EXISTS_THM] THEN
        ONCE_REWRITE_TAC [(← ExceptT.mk (TAUT [[(a /\ b) /\ c <=> b /\ a /\ c]]))] THEN
        REWRITE_TAC [UNWIND_THM2] THEN
        ONCE_REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN
        GEN_REWRITE_TAC HolLight.LAND_CONV [SWAP_EXISTS_THM] THEN
        ONCE_REWRITE_TAC [(← ExceptT.mk (TAUT [[(a /\ b) /\ c <=> b /\ a /\ c]]))] THEN
        REWRITE_TAC [UNWIND_THM2] THEN
        REWRITE_TAC [IN_UNIONS, IN_SING, IN_ELIM_THM] THEN MESON_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN
       ([[functions(IMAGE interp
             ({{e} | e IN E} UNION Eqclauses (language ((s === t) INSERT E)))) =
        functions((s === t) INSERT E)]])
      ASSUME_TAC THENL
       [REWRITE_TAC [IMAGE_UNION, FUNCTIONS_UNION, FUNCTIONS_EQCLAUSES] THEN
        REWRITE_TAC [FUNCTIONS_INSERT] THEN
        ASM_REWRITE_TAC [FUNCTIONS_INSERT, UNION_ACI], ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [X_GEN_TAC [[v:num->term]] THEN DISCH_TAC THEN
        SUBGOAL_THEN ([[atom(s === t)]]) MP_TAC THENL
         [REWRITE_TAC [atom, Equal_DEF], ALL_TAC] THEN
        DISCH_THEN (fun th => HolLight.tactic_of do
           let m ← HolLight.MATCH_MP IMINMODEL_MINIMAL th
           pure (ONCE_REWRITE_TAC [m])) THEN
        FIRST_X_ASSUM (fun th => MP_TAC th THEN MATCH_MP_TAC MONO_FORALL) THEN
        X_GEN_TAC
          [[C:(term->bool)#
             ((num->((term)list->term))#(num->((term)list->bool)))]] THEN
        ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC taut_big THEN
        CONJ_TAC THENL
         [SIMP_TAC [interpretation, language, Dom_DEF] THEN
          DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN
          REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
          REWRITE_TAC [IN] THEN CONV_TAC (HolLight.ONCE_DEPTH_CONV (fun t => pure (ETA_CONV t))) THEN
          STRIP_TAC THEN
          MATCH_MP_TAC (← liftExcept (Session.CONJUNCT2 (← ExceptT.mk (HolLight.SPEC_ALL terms_RULES)))) THEN
          ASM_REWRITE_TAC [] THEN REWRITE_TAC [(← HolLight.GSYM language)] THEN
          REWRITE_TAC [FUNCTIONS_UNION, FUNCTIONS_EQAXIOM] THEN
          ASM_REWRITE_TAC [IN_UNION], ALL_TAC] THEN
        CONJ_TAC THENL
         [DISCH_THEN SUBST1_TAC THEN
          REWRITE_TAC [EXTENSION, NOT_IN_EMPTY, NOT_FORALL_THM] THEN
          EXISTS_TAC [[V 0]] THEN REWRITE_TAC [IN, terms_RULES], ALL_TAC] THEN
        CONJ_TAC THENL
         [DISCH_TAC THEN SIMP_TAC [IMAGE_UNION, (← HolLight.GSYM EQCLAUSES_EQAXIOMS)] THEN
          DISCH_TAC THEN ASM_REWRITE_TAC [satisfies, valuation] THEN
          REWRITE_TAC [IN_UNION, (← ExceptT.mk (TAUT [[(a \/ b) /\ c <=> a /\ c \/ b /\ c]]))] THEN
          REWRITE_TAC [(← ExceptT.mk (TAUT [[(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)]]))] THEN
          REWRITE_TAC [FORALL_AND_THM] THEN SIMP_TAC [] THEN
          DISCH_THEN (MP_TAC oT Session.CONJUNCT1) THEN
          REWRITE_TAC [IN_IMAGE, IN_ELIM_THM, IN_SING] THEN
          SIMP_TAC [LEFT_IMP_EXISTS_THM, LEFT_AND_EXISTS_THM,
                   RIGHT_AND_EXISTS_THM] THEN
          SIMP_TAC [HOLDS_INTERP, FINITE_RULES] THEN
          REWRITE_TAC [IN_SING, UNWIND_THM2] THEN MESON_TAC [],
          ALL_TAC] THEN
        SIMP_TAC [satisfies, valuation, IN_SING] THEN ASM_MESON_TAC [],
        ALL_TAC] THEN
      REWRITE_TAC [IN_UNION, (← ExceptT.mk (TAUT [[(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)]]))] THEN
      REWRITE_TAC [EQCLAUSES_DEFINITE] THEN
      SIMP_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
      GEN_TAC THEN X_GEN_TAC [[e:form]] THEN
      DISCH_THEN (fun th => HolLight.tactic_of do
        let c1 ← liftExcept (Session.CONJUNCT1 th)
        pure (FIRST_ASSUM (MP_TAC oTIO HolCore.Lib.C HolLight.MATCH_MP c1))) THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [ [[u:term]], [[v:term]] ] THEN DISCH_THEN SUBST1_TAC THEN
      SIMP_TAC [FINITE_RULES, definite, clause, IN_SING, LITERAL, Equal_DEF] THEN
      REWRITE_TAC [(← HolLight.GSYM Equal_DEF)] THEN
      SUBGOAL_THEN ([[{p | (p = u === v) /\ positive p} = {(u === v)}]]) SUBST1_TAC
      THENL
       [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_SING] THEN
        MESON_TAC [Equal_DEF, positive, negative, Not_DEF, form_DISTINCT],
        ALL_TAC] THEN
      SIMP_TAC [CARD_CLAUSES, FINITE_RULES, ARITH, NOT_IN_EMPTY],
      ALL_TAC] THEN
    SUBGOAL_THEN
     ([[!n p. ibackchain
                  ({{e} | e IN E} UNION Eqclauses (language ((s === t) INSERT E)))
                  n p
            ==> !s t. (p = (s === t)) ==> E |- s === t]])
    MP_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
      GEN_TAC THEN DISCH_THEN (MP_TAC o HolLight.SPEC [[s === t]]) THEN
      DISCH_THEN (fun th => DISCH_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC [] THEN
      MESON_TAC []] THEN
    MATCH_MP_TAC ibackchain_INDUCT THEN
    MAP_EVERY X_GEN_TAC
     [ [[cl:form->bool]], [[i:num->term]], [[ns:num list]] ] THEN
    MATCH_MP_TAC taut_ab THEN
    STRIP_TAC THEN MAP_EVERY X_GEN_TAC [ [[si:term]], [[ti:term]] ] THEN
    DISCH_TAC THEN
    UNDISCH_TAC
     [[cl IN {{e} | e IN E} UNION Eqclauses (language ((s === t) INSERT E))]] THEN
    REWRITE_TAC [IN_UNION, IN_INSERT, (← HolLight.GSYM DISJ_ASSOC)] THEN
    DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL
     [SIMP_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC [[e:form]] THEN STRIP_TAC THEN
      UNDISCH_TAC [[formsubst i (conclusion cl) = si === ti]] THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[e:form]]) THEN
      ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [ [[s0:term]], [[t0:term]] ] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      SUBGOAL_THEN ([[conclusion {(s0 === t0)} = (s0 === t0)]]) SUBST1_TAC THENL
       [MATCH_MP_TAC CONCLUSION_DEFINITE THEN
        REWRITE_TAC [definite, IN_SING] THEN
        MATCH_MP_TAC taut_bba THEN CONJ_TAC THENL
         [REWRITE_TAC [positive, negative, Equal_DEF, Not_DEF] THEN
          MESON_TAC [form_DISTINCT],
          ALL_TAC] THEN
        DISCH_TAC THEN REWRITE_TAC [clause] THEN
        SIMP_TAC [FINITE_INSERT, FINITE_EMPTY, IN_SING] THEN
        SUBGOAL_THEN
         ([[{p | (p = s0 === t0) /\ positive p} = {(s0 === t0)}]])
        SUBST1_TAC THENL
         [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_SING] THEN ASM_MESON_TAC [],
          ALL_TAC] THEN
        SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY] THEN
        REWRITE_TAC [Equal_DEF, NOT_IN_EMPTY, ARITH, LITERAL],
        ALL_TAC] THEN
      DISCH_THEN (SUBST_ALL_TAC oTIO HolLight.SYM) THEN
      ASM_MESON_TAC [provable_RULES],
      ALL_TAC] THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
      let m ← HolLight.MATCH_MP EQCLAUSES_DEFINITE th
      pure (ASSUME_TAC m THEN MP_TAC th)) THEN
    REWRITE_TAC [Eqclauses_DEF, IN_UNION, IN_INSERT, (← HolLight.GSYM DISJ_ASSOC)] THEN
    DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC MP_TAC) THENL
     [SUBGOAL_THEN ([[conclusion {(V 0 === V 0)} = (V 0 === V 0)]])
      SUBST_ALL_TAC THENL
       [MATCH_MP_TAC CONCLUSION_DEFINITE THEN ASM_REWRITE_TAC [IN_SING] THEN
        REWRITE_TAC [positive, Equal_DEF, negative, Not_DEF, form_DISTINCT],
        ALL_TAC] THEN
      FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        let st ← HolLight.SYM th
        pure (GEN_REWRITE_TAC HolLight.RAND_CONV [st])) THEN
      ASM_MESON_TAC [provable_RULES],
      ALL_TAC] THEN
    DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC MP_TAC) THENL
     [SUBGOAL_THEN
       ([[conclusion {(Not (V 0 === V 1)), (Not(V 2 === V 1)), (V 0 === V 2)} =
          (V 0 === V 2)]])
      (fun th => SUBST_ALL_TAC th THEN ASSUME_TAC th) THENL
       [MATCH_MP_TAC CONCLUSION_DEFINITE_ALT THEN
        ASM_REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
        REWRITE_TAC [clause, FINITE_INSERT, FINITE_RULES] THEN
        SIMP_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
        REWRITE_TAC [(← ExceptT.mk (TAUT [[(a \/ b) /\ c <=> a /\ c \/ b /\ c]]))] THEN
        REWRITE_TAC [(← ExceptT.mk (TAUT [[(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)]]))] THEN
        SIMP_TAC [Equal_DEF, LITERAL] THEN
        REWRITE_TAC [positive, negative] THEN
        MESON_TAC [Not_DEF, form_DISTINCT],
        ALL_TAC] THEN
      FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        let st ← HolLight.SYM th
        pure (GEN_REWRITE_TAC HolLight.RAND_CONV [st])) THEN
      FIRST_X_ASSUM (MP_TAC oTIO HolLight.GEN_REWRITE_RULE HolCore.Lib.I [ALL2_TRIV]) THEN
      DISCH_THEN (MP_TAC oT Session.CONJUNCT2) THEN REWRITE_TAC [ALL_MAP] THEN
      REWRITE_TAC [(← HolLight.GSYM ALL_MEM)] THEN REWRITE_TAC [(← HolLight.GSYM IN_SET_OF_LIST)] THEN
      ASM_SIMP_TAC [HYPOTHESES_CONCLUSION] THEN
      SUBGOAL_THEN
        ([[IMAGE ~~
           ({(Not(V 0 === V 1)), (Not(V 2 === V 1)), (V 0 === V 2)}
            DELETE (V 0 === V 2)) =
          {(V 0 === V 1), (V 2 === V 1)}]])
      SUBST1_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_DELETE, IN_INSERT, NOT_IN_EMPTY] THEN
        REWRITE_TAC [Equal_DEF] THEN
        MESON_TAC [NEGATE_NEG, NEGATE_ATOM, atom, NEGATE_NEGATE, literal,
                  Not_DEF, form_DISTINCT],
        ALL_TAC] THEN
      REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
      REWRITE_TAC [(← ExceptT.mk (TAUT [[(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)]]))] THEN
      SIMP_TAC [o_THM] THEN
      REWRITE_TAC [FORALL_AND_THM, LEFT_FORALL_IMP_THM, EXISTS_REFL] THEN
      ASM_MESON_TAC [provable_RULES, FORMSUBST_EQ],
      ALL_TAC] THEN
    DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL
     [ALL_TAC,
      REWRITE_TAC [IN_ELIM_THM, EXISTS_PAIR_THM, Eqclause_Pred] THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [ [[p:num]], [[n:num]] ] THEN
      DISCH_THEN (STRIP_ASSUME_TAC oTIO HolLight.GSYM) THEN
      SUBGOAL_THEN ([[conclusion cl = Atom p (MAP SND (Varpairs n))]])
      (fun th => SUBST_ALL_TAC th THEN ASSUME_TAC th) THENL
       [MATCH_MP_TAC CONCLUSION_DEFINITE THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [positive, negative, form_DISTINCT, Not_DEF] THEN
        Fol.EXPAND_TAC "cl" THEN REWRITE_TAC [IN_SET_OF_LIST, MEM],
        ALL_TAC] THEN
      MP_TAC (← ExceptT.mk (HolLight.ASSUME
       [[formsubst i (Atom p (MAP SND (Varpairs n))) = si === ti]])) THEN
      REWRITE_TAC [Equal_DEF, formsubst, form_INJ] THEN
      ASM_CASES_TAC [[n = 2]] THENL
       [ALL_TAC,
        DISCH_THEN (fun th => HolLight.tactic_of do
          let c2 ← liftExcept (Session.CONJUNCT2 th)
          let ap ← HolLight.AP_TERM ([[LENGTH:(term)list->num]]) c2
          pure (MP_TAC ap)) THEN
        ASM_REWRITE_TAC [LENGTH, LENGTH_MAP, LENGTH_VARPAIRS, ARITH]] THEN
      UNDISCH_THEN ([[n = 2]]) SUBST_ALL_TAC THEN
      DISCH_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
      ASM_REWRITE_TAC [Varpairs_DEF, num2, num1] THEN
      REWRITE_TAC [ARITH, MAP, CONS_11] THEN
      DISCH_THEN (CONJUNCTS_THEN (SUBST_ALL_TAC oTIO HolLight.SYM)) THEN
      FIRST_X_ASSUM (MP_TAC oTIO HolLight.GEN_REWRITE_RULE HolCore.Lib.I [ALL2_TRIV]) THEN
      DISCH_THEN (MP_TAC oT Session.CONJUNCT2) THEN REWRITE_TAC [ALL_MAP] THEN
      REWRITE_TAC [(← HolLight.GSYM ALL_MEM)] THEN REWRITE_TAC [(← HolLight.GSYM IN_SET_OF_LIST)] THEN
      ASM_SIMP_TAC [HYPOTHESES_CONCLUSION] THEN
      SUBGOAL_THEN
        ([[IMAGE (~~) (cl DELETE (Atom 0 (MAP SND (Varpairs 2)))) =
         {(V 2 === V 0), (V 2 === V 3), (V 0 === V 1)}]])
      SUBST1_TAC THENL
       [Fol.EXPAND_TAC "cl" THEN
        REWRITE_TAC [EXTENSION, set_of_list, IN_SET_OF_LIST, MAP, MEM_MAP,
                    IN_IMAGE, IN_DELETE, IN_INSERT, NOT_IN_EMPTY] THEN
        REWRITE_TAC [num2, num1, Varpairs_DEF] THEN
        CONV_TAC Session.NUM_REDUCE_CONV THEN REWRITE_TAC [MAP, (← HolLight.GSYM Equal_DEF)] THEN
        REWRITE_TAC [MEM, (← ExceptT.mk (TAUT [[(a \/ b) /\ c <=> a /\ c \/ b /\ c]]))] THEN
        REWRITE_TAC [EXISTS_PAIR_THM] THEN
        CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
        REWRITE_TAC [PAIR_EQ, (← HolLight.GSYM CONJ_ASSOC)] THEN
        ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
        REWRITE_TAC [EXISTS_OR_THM, UNWIND_THM2, (← ExceptT.mk (TAUT [[~(p /\ ~p)]]))] THEN
        REWRITE_TAC [Equal_DEF] THEN
        MESON_TAC [NEGATE_NEG, NEGATE_ATOM, atom, NEGATE_NEGATE, literal,
                  Not_DEF, form_DISTINCT],
        ALL_TAC] THEN
      REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
      REWRITE_TAC [(← ExceptT.mk (TAUT [[(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)]]))] THEN
      SIMP_TAC [o_THM] THEN
      REWRITE_TAC [FORALL_AND_THM, LEFT_FORALL_IMP_THM, EXISTS_REFL] THEN
      REWRITE_TAC [(← HolLight.GSYM Equal_DEF)] THEN REWRITE_TAC [FORMSUBST_EQ] THEN
      ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
      SIMP_TAC [LEFT_IMP_EXISTS_THM] THEN
      ASM_MESON_TAC [provable_RULES, FORMSUBST_EQ]] THEN
    REWRITE_TAC [IN_ELIM_THM, EXISTS_PAIR_THM, Eqclause_Func] THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[f:num]], [[n:num]] ] THEN
    DISCH_THEN (STRIP_ASSUME_TAC oTIO HolLight.GSYM) THEN
    SUBGOAL_THEN
     ([[conclusion cl = (Fn f (MAP FST (Varpairs n)) ===
                       Fn f (MAP SND (Varpairs n)))]])
    (fun th => SUBST_ALL_TAC th THEN ASSUME_TAC th) THENL
     [MATCH_MP_TAC CONCLUSION_DEFINITE THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [positive, negative, form_DISTINCT, Not_DEF] THEN
      Fol.EXPAND_TAC "cl" THEN REWRITE_TAC [IN_SET_OF_LIST, MEM] THEN
      REWRITE_TAC [Equal_DEF, form_DISTINCT],
      ALL_TAC] THEN
    FIRST_X_ASSUM (fun th => HolLight.tactic_of do
      let gst ← HolLight.GSYM th
      pure (GEN_REWRITE_TAC HolLight.RAND_CONV [gst])) THEN
    FIRST_X_ASSUM (MP_TAC oTIO HolLight.GEN_REWRITE_RULE HolCore.Lib.I [ALL2_TRIV]) THEN
    DISCH_THEN (MP_TAC oT Session.CONJUNCT2) THEN REWRITE_TAC [ALL_MAP] THEN
    REWRITE_TAC [(← HolLight.GSYM ALL_MEM)] THEN REWRITE_TAC [(← HolLight.GSYM IN_SET_OF_LIST)] THEN
    ASM_SIMP_TAC [HYPOTHESES_CONCLUSION] THEN
    SUBGOAL_THEN
      ([[IMAGE (~~) (cl DELETE
          (Fn f (MAP FST (Varpairs n)) === Fn f (MAP SND (Varpairs n)))) =
       {(s === t) | MEM (s,t) (Varpairs n)}]])
    SUBST1_TAC THENL
     [Fol.EXPAND_TAC "cl" THEN
      REWRITE_TAC [EXTENSION, set_of_list, IN_SET_OF_LIST, MAP, MEM_MAP,
                  IN_IMAGE, IN_DELETE, IN_INSERT, NOT_IN_EMPTY] THEN
      REWRITE_TAC [MEM, (← ExceptT.mk (TAUT [[(a \/ b) /\ c <=> a /\ c \/ b /\ c]]))] THEN
      REWRITE_TAC [(← ExceptT.mk (TAUT [[~(p /\ ~p)]])), IN_ELIM_THM] THEN
      REWRITE_TAC [MEM_MAP, EXISTS_PAIR_THM] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC [Equal_DEF] THEN
      MESON_TAC [NEGATE_NEG, NEGATE_ATOM, atom, NEGATE_NEGATE, literal,
                Not_DEF, form_DISTINCT],
      ALL_TAC] THEN
    SIMP_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [o_THM, FORMSUBST_EQ] THEN
    REWRITE_TAC [Equal_DEF, form_INJ, CONS_11] THEN
    REWRITE_TAC [(← HolLight.GSYM Equal_DEF)] THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
    SIMP_TAC [LEFT_FORALL_IMP_THM, LEFT_EXISTS_AND_THM, RIGHT_EXISTS_AND_THM] THEN
    REWRITE_TAC [EXISTS_REFL] THEN
    REWRITE_TAC [termsubst, (← HolLight.GSYM MAP_o)] THEN
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
    ONCE_REWRITE_TAC [IMP_CONJ_ALT] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [SWAP_FORALL_THM] THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.BINDER_CONV) [SWAP_FORALL_THM] THEN
    REWRITE_TAC [LEFT_FORALL_IMP_THM, EXISTS_REFL] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC pr4 THEN
    REWRITE_TAC [ALL2_MAP2] THEN REWRITE_TAC [ALL2_ALL] THEN
    ASM_REWRITE_TAC [(← HolLight.GSYM ALL_MEM), FORALL_PAIR_THM, o_THM])
  : ExceptT String IO thm).run
#eval EQLOGIC_COMPLETE

#eval phrase 64
unsafe def EQLOGIC_SOUND : thm := keep "EQLOGIC_SOUND" fun _ => (do
  prove ([[!E s t. E |- s === t
             ==> !M:(A->bool)#(num->((A)list->A))#(num->((A)list->bool)).
                          normal UNIV (M) /\ interpretation (UNIV,UNIV) (M) /\
                          M satisfies E
                          ==> M satisfies {(s === t)}]])
   (GEN_TAC THEN REWRITE_TAC [satisfies] THEN
    SIMP_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
    REWRITE_TAC [LEFT_FORALL_IMP_THM, RIGHT_EXISTS_AND_THM, EXISTS_REFL] THEN
    SUBGOAL_THEN
     ([[!M:(A->bool)#(num->((A)list->A))#(num->((A)list->bool)).
          normal UNIV (M) /\ interpretation (UNIV,UNIV) (M) /\
          (!v p. valuation M v /\ p IN E ==> holds M v p)
          ==> !a. E |- a
                  ==> !s t. (a = (s === t))
                            ==> !v. valuation M v ==> holds M v (s === t)]])
     (fun th => MESON_TAC [th]) THEN
    GEN_TAC THEN REWRITE_TAC [normal, satisfies, TERMS_UNIV, IN_UNIV] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC provable_INDUCT THEN
    SIMP_TAC [EQUAL_INJ_ALT, LEFT_FORALL_IMP_THM,
             RIGHT_EXISTS_AND_THM, LEFT_EXISTS_AND_THM, EXISTS_REFL] THEN
    ASM_SIMP_TAC [] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC [],
      REPEAT STRIP_TAC THEN REWRITE_TAC [termval] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ_ALL2 THEN
      UNDISCH_TAC
       [[ALL2 (\l r. !v:num->A. valuation M v
                               ==> (termval M v l = termval M v r)) a b]] THEN
      MATCH_MP_TAC MONO_ALL2 THEN ASM_SIMP_TAC [],
      REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [FORMSUBST_EQ] THEN
      REWRITE_TAC [Equal_DEF, form_INJ, CONS_11] THEN
      REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN (SUBST_ALL_TAC oTIO HolLight.SYM)) THEN
      REWRITE_TAC [TERMVAL_TERMSUBST] THEN REPEAT GEN_TAC THEN
      DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC [o_THM, valuation] THEN
      GEN_TAC THEN MATCH_MP_TAC INTERPRETATION_TERMVAL THEN
      EXISTS_TAC [[UNIV:(num#num)->bool]] THEN ASM_REWRITE_TAC [] THEN
      FIRST_ASSUM (fun th => MP_TAC th THEN
                            MATCH_MP_TAC INTERPRETATION_SUBLANGUAGE) THEN
      REWRITE_TAC [SUBSET_UNIV]])
  : ExceptT String IO thm).run
#eval EQLOGIC_SOUND

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py from the `#eval`s above. -/
unsafe def ensure : IO Unit := once "HolLogicArith.Birkhoff" do
  replay (
          HolLogicArith.Positive.ensure)
  replay (
          HolLogicArith.Prolog.ensure)
  replay (
          ALL2_SYM)
  replay (
          MAP_EQ_ALL2)
  replay (
          FORMSUBST_EQ)
  replay (
          TERMS_UNIV)
  replay (
          FUNCTIONS_UNIV)
  replay (
          PREDICATES_UNIV)
  replay (
          LANGUAGE_UNIV)
  replay (
          EQUAL_INJ)
  replay (
          EQUAL_INJ_ALT)
  replay (
          parse_as_infix ("|-", (11, "right")))
  replay (
          do IO.println provable_RULES; IO.println provable_INDUCT; IO.println provable_CASES)
  replay (
          parse_as_infix ("|--", (11, "right")))
  replay (
          do IO.println wcprovable_RULES; IO.println wcprovable_INDUCT; IO.println wcprovable_CASES)
  replay (
          WCPROVABLE_SYM)
  replay (
          WCPROVABLE_INST)
  replay (
          WCPROVABLE_PROVABLE)
  replay (
          parse_as_infix ("|---", (11, "right")))
  replay (
          parse_as_infix ("|--_axiom", (11, "right")))
  replay (
          parse_as_infix ("|--_cong", (11, "right")))
  replay (
          parse_as_infix ("|--_achain", (11, "right")))
  replay (
          parse_as_infix ("|--_cchain", (11, "right")))
  replay (
          do IO.println aprovable_RULES; IO.println aprovable_INDUCT; IO.println aprovable_CASES)
  replay (
          do IO.println cprovable_RULES; IO.println cprovable_INDUCT; IO.println cprovable_CASES)
  replay (
          CPROVABLE_PROVABLE_LEMMA)
  replay (
          CPROVABLE_PROVABLE)
  replay (
          subterms)
  replay (
          subtermsa)
  replay (
          subtermss)
  replay (
          SUBTERMS_REFL)
  replay (
          esubterms)
  replay (
          parse_as_infix ("|----", (11, "right")))
  replay (
          parse_as_infix ("|--_scong", (11, "right")))
  replay (
          parse_as_infix ("|--_sachain", (11, "right")))
  replay (
          parse_as_infix ("|--_scchain", (11, "right")))
  replay (
          do IO.println scprovable_RULES; IO.println scprovable_INDUCT; IO.println scprovable_CASES)
  replay (
          ESUBTERMS_TRIVIAL_L)
  replay (
          ESUBTERMS_TRIVIAL_R)
  replay (
          SCPROVABLE_SUBTERMS)
  replay (
          SCPROVABLE_CPROVABLE_LEMMA)
  replay (
          SCPROVABLE_CPROVABLE)
  replay (
          SCPROVABLE_PROVABLE)
  replay (
          Eqclause_Func)
  replay (
          Eqclause_Pred)
  replay (
          Eqclauses_DEF)
  replay (
          EQCLAUSE_EQAXIOM_FUNC)
  replay (
          Eqaxiom_Pred_imp)
  replay (
          lemma)
  replay (
          EQCLAUSES_EQAXIOMS)
  replay (
          FUNCTIONS_VAREQLIST)
  replay (
          FUNCTIONS_TERM_FN_VARPAIRS)
  replay (
          FUNCTIONS_FORM_PRED_VARPAIRS)
  replay (
          FUNCTIONS_FORM_EQCLAUSE_FUNC)
  replay (
          FUNCTIONS_FORM_EQCLAUSE_PRED)
  replay (
          FUNCTIONS_EQCLAUSES)
  replay (
          FUNCTIONS_FORM_NOT_UCLOSE)
  replay (
          PREDICATES_FORM_NOT_UCLOSE)
  replay (
          FUNCTIONS_INSERT_NOT_UCLOSE)
  replay (
          PREDICATES_INSERT_NOT_UCLOSE)
  replay (
          LANGUAGE_INSERT_NOT_UCLOSE)
  replay (
          lemma1)
  replay (
          lemma2)
  replay (
          EQCLAUSES_DEFINITE)
  replay (
          EQLOGIC_COMPLETE)
  replay (
          EQLOGIC_SOUND)
-- @@ENSURE END

end HolLogicArith.Birkhoff
