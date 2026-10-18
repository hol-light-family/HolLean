/- File: HolLogicArith/Prenex.lean
Translation of HOL Light's Logic/prenex.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolLogicArith.Fol
open HolCore.Kernel Session HolLight.Syntax HolLogicArith
open scoped HolLight
open HolLogicArith.Fol

namespace HolLogicArith.Prenex

#eval HolLogicArith.Fol.ensure

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

/- `new_specification` lifted into `ExceptT String IO`. -/
private unsafe def newSpec (names : List String) (th : thm) : ExceptT String IO thm :=
  ExceptT.mk (Session.new_specification names th)

#eval phrase 1
unsafe def qfree : thm := keep "qfree" fun _ => (do
  newRec form_RECURSION
    [[(qfree False <=> T) /\
      (qfree (Atom n l) <=> T) /\
      (qfree (p --> q) <=> qfree p /\ qfree q) /\
      (qfree (!!x p) <=> F)]]
  : ExceptT String IO thm).run
#eval qfree

#eval phrase 2
unsafe def QFREE : thm := keep "QFREE" fun _ => (do
  prove ([[(qfree False <=> T) /\
   (qfree True <=> T) /\
   (!a l. qfree (Atom a l) <=> T) /\
   (!p. qfree (Not p) <=> qfree p) /\
   (!p q. qfree (p || q) <=> qfree p /\ qfree q) /\
   (!p q. qfree (p && q) <=> qfree p /\ qfree q) /\
   (!p q. qfree (p --> q) <=> qfree p /\ qfree q) /\
   (!p q. qfree (p <-> q) <=> qfree p /\ qfree q) /\
   (!x p. qfree (!! x p) <=> F) /\
   (!x p. qfree (?? x p) <=> F)]])
   (REWRITE_TAC [Not_DEF, True_DEF, Or_DEF, And_DEF,
                Iff_DEF, Exists_DEF, qfree, CONJ_ACI])
  : ExceptT String IO thm).run
#eval QFREE

#eval phrase 3
unsafe def QFREE_FORMSUBST : thm := keep "QFREE_FORMSUBST" fun _ => (do
  prove ([[!p v. qfree (formsubst v p) <=> qfree p]])
   (MATCH_MP_TAC form_INDUCTION THEN
    ASM_REWRITE_TAC [formsubst, qfree, LET_DEF, LET_END_DEF] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval QFREE_FORMSUBST

#eval phrase 4
unsafe def QFREE_BV_EMPTY : thm := keep "QFREE_BV_EMPTY" fun _ => (do
  prove ([[!p. qfree(p) <=> (BV(p) = EMPTY)]])
   (MATCH_MP_TAC form_INDUCTION THEN REWRITE_TAC [qfree, BV] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [EMPTY_UNION] THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [EXTENSION, IN_INSERT, NOT_IN_EMPTY]) THEN
    ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval QFREE_BV_EMPTY

#eval phrase 5
unsafe def prenex_triple : thm × thm × thm := keep "prenex_triple" fun _ =>
  newInductive
    [[(!p. qfree p ==> prenex p) /\
      (!x p. prenex p ==> prenex (!!x p)) /\
      (!x p. prenex p ==> prenex (??x p))]]
unsafe def prenex_RULES : thm := prenex_triple.1
unsafe def prenex_INDUCT : thm := prenex_triple.2.1
unsafe def prenex_CASES : thm := prenex_triple.2.2
#eval do IO.println prenex_RULES; IO.println prenex_INDUCT; IO.println prenex_CASES

#eval phrase 6
unsafe def universal_triple : thm × thm × thm := keep "universal_triple" fun _ =>
  newInductive
    [[(!p. qfree p ==> universal p) /\
      (!x p. universal p ==> universal (!!x p))]]
unsafe def universal_RULES : thm := universal_triple.1
unsafe def universal_INDUCT : thm := universal_triple.2.1
unsafe def universal_CASES : thm := universal_triple.2.2
#eval do IO.println universal_RULES; IO.println universal_INDUCT; IO.println universal_CASES

#eval phrase 7
unsafe def prenex_INDUCT_NOT : thm := keep "prenex_INDUCT_NOT" fun _ => (do
  prove ([[!P. (!p. qfree p ==> P p) /\
       (!x p. P p ==> P (!! x p)) /\
       (!x p. P p ==> P (Not p))
       ==> !a. prenex a ==> P a]])
   (GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC prenex_INDUCT THEN
    REWRITE_TAC [Exists_DEF] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval prenex_INDUCT_NOT

#eval phrase 8
unsafe def PRENEX : thm := keep "PRENEX" fun _ => (do
  prove ([[(prenex False <=> T) /\
   (prenex True <=> T) /\
   (!a l. prenex (Atom a l) <=> T) /\
   (!p. prenex (Not p) <=> qfree p \/ (?q x. (Not p = ??x q) /\ prenex q)) /\
   (!p q. prenex (p || q) <=> qfree p /\ qfree q) /\
   (!p q. prenex (p && q) <=> qfree p /\ qfree q) /\
   (!p q. prenex (p --> q) <=> qfree p /\ qfree q \/
                             (?r x. (p --> q = ??x r) /\ prenex r)) /\
   (!p q. prenex (p <-> q) <=> qfree p /\ qfree q) /\
   (!x p. prenex (!! x p) <=> prenex p) /\
   (!x p. prenex (?? x p) <=> prenex p)]])
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC HolLight.LAND_CONV [prenex_CASES] THEN
    REWRITE_TAC [True_DEF, Not_DEF, Or_DEF, And_DEF, Iff_DEF, Exists_DEF] THEN
    REWRITE_TAC [form_DISTINCT, form_INJ, QFREE, CONJ_ACI] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval PRENEX

#eval phrase 9
unsafe def FORMSUBST_STRUCTURE_LEMMA : thm := keep "FORMSUBST_STRUCTURE_LEMMA" fun _ => (do
  prove ([[!p i. ((formsubst i p = False) <=> (p = False)) /\
         ((?a l. formsubst i p = Atom a l) <=> (?a l. p = Atom a l)) /\
         ((?q r. formsubst i p = q --> r) <=> (?q r. p = q --> r)) /\
         ((?x q. formsubst i p = !!x q) <=> (?x q. p = !!x q))]])
   (MATCH_MP_TAC form_INDUCTION THEN
    REWRITE_TAC [formsubst, LET_DEF, LET_END_DEF] THEN
    REWRITE_TAC [form_DISTINCT, form_INJ] THEN REPEAT STRIP_TAC THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval FORMSUBST_STRUCTURE_LEMMA

#eval phrase 10
unsafe def FORMSUBST_STRUCTURE_NOT : thm := keep "FORMSUBST_STRUCTURE_NOT" fun _ => (do
  prove ([[!p i. (?q. formsubst i p = Not q) <=> (?q. p = Not q)]])
   (HolLight.tactic_of do
     let th2 ← liftExcept (HolCore.Lib.el 2 (HolLight.CONJUNCTS (← HolLight.SPEC_ALL FORMSUBST_STRUCTURE_LEMMA)))
     pure
      (REWRITE_TAC [Not_DEF, FORMSUBST_STRUCTURE_LEMMA] THEN
       REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_THEN (X_CHOOSE_TAC [[q:form]]) THENL
        [MP_TAC th2 THEN
         DISCH_THEN (MP_TAC oTIO (fun th => (do let (a, _) ← HolLight.EQ_IMP_RULE th; pure a : ExceptT String IO thm).run)) THEN
         REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
         DISCH_THEN (MP_TAC oTIO HolLight.SPECL [ [[q:form]], [[False]] ]) THEN
         ASM_REWRITE_TAC [] THEN
         DISCH_THEN (HolLight.REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
         POP_ASSUM MP_TAC THEN
         REWRITE_TAC [formsubst, FORMSUBST_STRUCTURE_LEMMA, form_INJ] THEN
         MESON_TAC [],
         ASM_REWRITE_TAC [formsubst] THEN MESON_TAC []]))
  : ExceptT String IO thm).run
#eval FORMSUBST_STRUCTURE_NOT

#eval phrase 11
unsafe def FORMSUBST_STRUCTURE_EXISTS : thm := keep "FORMSUBST_STRUCTURE_EXISTS" fun _ => (do
  prove ([[!p i. (?x q. formsubst i p = ??x q) <=> (?x q. p = ??x q)]])
   (HolLight.tactic_of do
     let mp1 ← do let (a, _) ← HolLight.EQ_IMP_RULE (← HolLight.SPEC_ALL FORMSUBST_STRUCTURE_NOT); pure a
     pure
      (REPEAT GEN_TAC THEN REWRITE_TAC [Exists_DEF] THEN EQ_TAC THEN STRIP_TAC THENL
        [ALL_TAC, ASM_REWRITE_TAC [Not_DEF, formsubst, LET_DEF, LET_END_DEF] THEN
                  MESON_TAC []] THEN
       MP_TAC mp1 THEN
       REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
       DISCH_THEN (MP_TAC oTIO HolLight.SPEC [[!! x (Not q)]]) THEN
       ASM_REWRITE_TAC [] THEN
       DISCH_THEN (X_CHOOSE_THEN ([[r:form]]) SUBST_ALL_TAC) THEN
       POP_ASSUM MP_TAC THEN
       REWRITE_TAC [formsubst, Not_DEF, form_INJ, LET_DEF, LET_END_DEF] THEN
       REWRITE_TAC [(← HolLight.GSYM Not_DEF)] THEN DISCH_TAC THEN
       (HolLight.tactic_of do
         let mp2 ← do
           let (a, _) ← HolLight.EQ_IMP_RULE (← liftExcept (HolCore.Lib.last (HolLight.CONJUNCTS (← HolLight.SPEC_ALL (← HolLight.SPEC ([[r:form]]) FORMSUBST_STRUCTURE_LEMMA)))))
           pure a
         pure (MP_TAC mp2)) THEN
       REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
       DISCH_THEN (MP_TAC oTIO HolLight.SPECL [ [[x:num]], [[Not q]] ]) THEN
       ASM_REWRITE_TAC [] THEN
       DISCH_THEN (X_CHOOSE_THEN ([[y:num]]) (X_CHOOSE_THEN ([[s:form]]) SUBST_ALL_TAC)) THEN
       POP_ASSUM MP_TAC THEN
       REWRITE_TAC [formsubst, Not_DEF, form_INJ, LET_DEF, LET_END_DEF] THEN
       COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
       REWRITE_TAC [(← HolLight.GSYM Not_DEF)] THEN MESON_TAC [FORMSUBST_STRUCTURE_NOT]))
  : ExceptT String IO thm).run
#eval FORMSUBST_STRUCTURE_EXISTS

#eval phrase 12
unsafe def PRENEX_FORMSUBST_LEMMA : thm := keep "PRENEX_FORMSUBST_LEMMA" fun _ => (do
  prove ([[!p. prenex p ==> !i q. (p = formsubst i q) ==> prenex q]])
   (MATCH_MP_TAC prenex_INDUCT THEN REPEAT CONJ_TAC THENL
     [MESON_TAC [QFREE_FORMSUBST, prenex_RULES],
      REPEAT STRIP_TAC THEN
      MP_TAC (← ExceptT.mk (HolLight.SPECL [ [[q:form]], [[i:num->term]] ] FORMSUBST_STRUCTURE_LEMMA)) THEN
      DISCH_THEN (MP_TAC oTIO (fun th => (do let (a, _) ← HolLight.EQ_IMP_RULE (← liftExcept (HolCore.Lib.last (HolLight.CONJUNCTS th))); pure a : ExceptT String IO thm).run)) THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      DISCH_THEN (MP_TAC oTIO HolLight.SPECL [ [[x:num]], [[p:form]] ]) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN
       (X_CHOOSE_THEN ([[y:num]]) (X_CHOOSE_THEN ([[r:form]]) SUBST_ALL_TAC)) THEN
      UNDISCH_TAC [[!! x p = formsubst i (!! y r)]] THEN
      REWRITE_TAC [formsubst, form_INJ, PRENEX, LET_DEF, LET_END_DEF] THEN
      ASM_MESON_TAC [],
      REPEAT STRIP_TAC THEN
      MP_TAC (← ExceptT.mk (HolLight.SPECL [ [[q:form]], [[i:num->term]] ] FORMSUBST_STRUCTURE_EXISTS)) THEN
      DISCH_THEN (MP_TAC oTIO (fun th => (do let (a, _) ← HolLight.EQ_IMP_RULE (← liftExcept (HolCore.Lib.last (HolLight.CONJUNCTS th))); pure a : ExceptT String IO thm).run)) THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      DISCH_THEN (MP_TAC oTIO HolLight.SPECL [ [[x:num]], [[p:form]] ]) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN
       (X_CHOOSE_THEN ([[y:num]]) (X_CHOOSE_THEN ([[r:form]]) SUBST_ALL_TAC)) THEN
      UNDISCH_TAC [[?? x p = formsubst i (?? y r)]] THEN
      REWRITE_TAC [PRENEX] THEN
      REWRITE_TAC [Exists_DEF, Not_DEF, formsubst, form_INJ, LET_DEF, LET_END_DEF] THEN
      ASM_MESON_TAC []])
  : ExceptT String IO thm).run
#eval PRENEX_FORMSUBST_LEMMA

#eval phrase 13
unsafe def PRENEX_FORMSUBST : thm := keep "PRENEX_FORMSUBST" fun _ => (do
  prove ([[!p i. prenex(formsubst i p) = prenex p]])
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [MESON_TAC [PRENEX_FORMSUBST_LEMMA],
      SPEC_TAC ([[i:num->term]], [[i:num->term]]) THEN
      REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
      SPEC_TAC ([[p:form]], [[p:form]]) THEN
      MATCH_MP_TAC prenex_INDUCT THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [formsubst, LET_DEF, LET_END_DEF] THENL
       [ASM_MESON_TAC [QFREE_FORMSUBST, prenex_RULES],
        ASM_REWRITE_TAC [PRENEX],
        REWRITE_TAC [formsubst, Not_DEF, Exists_DEF, LET_DEF, LET_END_DEF] THEN
        REWRITE_TAC [(← HolLight.GSYM Not_DEF), (← HolLight.GSYM Exists_DEF)] THEN
        ASM_REWRITE_TAC [PRENEX]]])
  : ExceptT String IO thm).run
#eval PRENEX_FORMSUBST

#eval phrase 14
unsafe def size : thm := keep "size" fun _ => (do
  newRec form_RECURSION
    [[(size False = 1) /\
      (size (Atom p l) = 1) /\
      (size (q --> r) = size q + size r) /\
      (size (!!x q) = 1 + size q)]]
  : ExceptT String IO thm).run
#eval size

#eval phrase 15
unsafe def SIZE : thm := keep "SIZE" fun _ => (do
  prove ([[(size False = 1) /\
   (size True = 2) /\
   (!a l. size (Atom a l) = 1) /\
   (!p. size (Not p) = 1 + size p) /\
   (!p q. size (p || q) = size p + 2 * size q) /\
   (!p q. size (p && q) = size p + 2 * size q + 4) /\
   (!p q. size (p --> q) = size p + size q) /\
   (!p q. size (p <-> q) = 3 * size p + 3 * size q + 4) /\
   (!x p.size (!! x p) = 1 + size p) /\
   (!x p. size (?? x p) = 3 + size p)]])
   (REWRITE_TAC [True_DEF, Not_DEF, Or_DEF, And_DEF, Iff_DEF, Exists_DEF, size] THEN
    REPEAT STRIP_TAC THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval SIZE

#eval phrase 16
unsafe def SIZE_FORMSUBST : thm := keep "SIZE_FORMSUBST" fun _ => (do
  prove ([[!p i. size (formsubst i p) = size p]])
   (MATCH_MP_TAC form_INDUCTION THEN
    ASM_REWRITE_TAC [formsubst, size, LET_END_DEF, LET_DEF] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval SIZE_FORMSUBST

#eval phrase 17
unsafe def PPAT_DEF : thm := keep "PPAT_DEF" fun _ => new_definition
  [[PPAT A B C r =
     if ?x p. r = !!x p then
                    A (@x. ?p. r = !!x p)
                      (@p. r = !!(@x. ?p. r = !!x p) p)
                  else if ?x p. r = ??x p then
                    B (@x. ?p. r = ??x p)
                      (@p. r = ??(@x. ?p. r = ??x p) p)
                  else C r]]
#eval PPAT_DEF

#eval phrase 18
unsafe def PRENEX_DISTINCT : thm := keep "PRENEX_DISTINCT" fun _ => (do
  prove ([[!x y p q. ((!!x p = !!y q) <=> (x = y) /\ (p = q)) /\
             ((??x p = ??y q) <=> (x = y) /\ (p = q)) /\
             ~(!!x p = ??y q)]])
   (REWRITE_TAC [Exists_DEF, Not_DEF, form_DISTINCT, form_INJ])
  : ExceptT String IO thm).run
#eval PRENEX_DISTINCT

#eval phrase 19
unsafe def PPAT : thm := keep "PPAT" fun _ => (do
  prove ([[!A B C. (!x p. PPAT A B C (!!x p) = A x p :A) /\
           (!x p. PPAT A B C (??x p) = B x p) /\
           !r. ~(?x p. r = !!x p) /\ ~(?x p. r = ??x p)
               ==> (PPAT A B C  r = C r)]])
   (HolLight.tactic_of do
     let selsym ← HolLight.CONV_RULE (HolLight.LAND_CONV (HolLight.ONCE_DEPTH_CONV HolLight.SYM_CONV)) (← HolLight.SPEC_ALL SELECT_REFL)
     pure
      (REPEAT GEN_TAC THEN REWRITE_TAC [PPAT_DEF] THEN REPEAT STRIP_TAC THEN
       ASM_REWRITE_TAC [PRENEX_DISTINCT] THEN
       (COND_CASES_TAC THENL [ALL_TAC, ASM_MESON_TAC []]) THEN
       REWRITE_TAC [RIGHT_EXISTS_AND_THM, EXISTS_REFL, (← HolLight.GSYM EXISTS_REFL),
                   SELECT_REFL, selsym]))
  : ExceptT String IO thm).run
#eval PPAT

#eval phrase 20
unsafe def SIZE_REC : thm := keep "SIZE_REC" fun _ => (do
  prove ([[!H. (!f g x. (!z. size z < size x ==> (f z = g z)) ==> (H f x = H g x))
       ==> (?f. !x. f x = H f x)]])
   (MATCH_MP_TAC WF_REC THEN
    REWRITE_TAC [(← HolLight.REWRITE_RULE [MEASURE] WF_MEASURE)])
  : ExceptT String IO thm).run
#eval SIZE_REC

#eval phrase 21
unsafe def PRENEX_RIGHT_EXISTENCE : thm := keep "PRENEX_RIGHT_EXISTENCE" fun _ => (do
  prove ([[?Prenex_right.
        (!p x q. Prenex_right p (!!x q) =
                   let y = VARIANT(FV(p) UNION FV(!!x q)) in
                   !!y (Prenex_right p (formsubst (valmod (x,V y) V) q))) /\
        (!p x q. Prenex_right p (??x q) =
                   let y = VARIANT(FV(p) UNION FV(??x q)) in
                   ??y (Prenex_right p (formsubst (valmod (x,V y) V) q))) /\
        (!p q. qfree q ==> (Prenex_right p q = p --> q))]])
   (HolLight.tactic_of do
     let selsym ← HolLight.CONV_RULE (HolLight.LAND_CONV (HolLight.ONCE_DEPTH_CONV HolLight.SYM_CONV)) (← HolLight.SPEC_ALL SELECT_REFL)
     pure
      (SUBGOAL_THEN
        ([[!p. ?Prenex_right. !r. Prenex_right r =
           PPAT (\x q. let y = VARIANT(FV(p) UNION FV(!!x q)) in
                 !!y (Prenex_right (formsubst (valmod (x,V y) V) q)))
                (\x q. let y = VARIANT(FV(p) UNION FV(??x q)) in
                 ??y (Prenex_right (formsubst (valmod (x,V y) V) q)))
                (\q. p --> q) r]])
       MP_TAC THENL
        [GEN_TAC THEN MATCH_MP_TAC SIZE_REC THEN
         REPEAT STRIP_TAC THEN REWRITE_TAC [PPAT_DEF] THEN
         ASM_CASES_TAC [[?x p. r = !!x p]] THEN ASM_REWRITE_TAC [] THENL
          [FIRST_X_ASSUM (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC)) THEN
           REWRITE_TAC [form_DISTINCT, form_INJ] THEN
           REWRITE_TAC [RIGHT_EXISTS_AND_THM, EXISTS_REFL, (← HolLight.GSYM EXISTS_REFL),
                   SELECT_REFL, selsym] THEN
           REWRITE_TAC [LET_DEF, LET_END_DEF] THEN
           AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
           REWRITE_TAC [SIZE_FORMSUBST, SIZE] THEN ARITH_TAC, ALL_TAC] THEN
         COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
         FIRST_X_ASSUM (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC)) THEN
         REWRITE_TAC [PRENEX_DISTINCT] THEN
         REWRITE_TAC [RIGHT_EXISTS_AND_THM, EXISTS_REFL, (← HolLight.GSYM EXISTS_REFL),
                   SELECT_REFL, selsym] THEN
         REWRITE_TAC [LET_DEF, LET_END_DEF] THEN
         AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
         REWRITE_TAC [SIZE_FORMSUBST, SIZE] THEN ARITH_TAC, ALL_TAC] THEN
       DISCH_THEN (MP_TAC oTIO HolLight.GEN_REWRITE_RULE HolCore.Lib.I [SKOLEM_THM]) THEN
       DISCH_THEN (X_CHOOSE_TAC [[Prenex_right:form->form->form]]) THEN
       EXISTS_TAC [[Prenex_right:form->form->form]] THEN
       REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY DISCH_TAC THEN
       FIRST_ASSUM (fun th => GEN_REWRITE_TAC HolLight.LAND_CONV [th]) THEN
       REWRITE_TAC [PPAT] THEN
       UNDISCH_TAC [[qfree q]] THEN REWRITE_TAC [PPAT_DEF] THEN
       POP_ASSUM_LIST (HolCore.Lib.K ALL_TAC) THEN
       COND_CASES_TAC THENL [POP_ASSUM (STRIP_ASSUME_TAC) THEN
                             ASM_REWRITE_TAC [QFREE], ALL_TAC] THEN
       COND_CASES_TAC THENL [POP_ASSUM (STRIP_ASSUME_TAC) THEN
                             ASM_REWRITE_TAC [QFREE], ALL_TAC] THEN
       REWRITE_TAC []))
  : ExceptT String IO thm).run
#eval PRENEX_RIGHT_EXISTENCE

#eval phrase 22
unsafe def PRENEX_RIGHT : thm := keep "PRENEX_RIGHT" fun _ =>
  (newSpec ["Prenex_right"] PRENEX_RIGHT_EXISTENCE : ExceptT String IO thm).run
#eval PRENEX_RIGHT

#eval phrase 23
unsafe def PRENEX_LEFT_EXISTENCE : thm := keep "PRENEX_LEFT_EXISTENCE" fun _ => (do
  prove ([[?Prenex_left.
        (!p x q. Prenex_left (!!x q) p =
                   let y = VARIANT(FV(!!x q) UNION FV(p)) in
                   ??y (Prenex_left (formsubst (valmod (x,V y) V) q) p)) /\
        (!p x q. Prenex_left (??x q) p =
                   let y = VARIANT(FV(??x q) UNION FV(p)) in
                   !!y (Prenex_left (formsubst (valmod (x,V y) V) q) p)) /\
        (!p q. qfree q ==> (Prenex_left q p = Prenex_right q p))]])
   (HolLight.tactic_of do
     let selsym ← HolLight.CONV_RULE (HolLight.LAND_CONV (HolLight.ONCE_DEPTH_CONV HolLight.SYM_CONV)) (← HolLight.SPEC_ALL SELECT_REFL)
     pure
      (SUBGOAL_THEN
        ([[!p. ?Prenex_left. !r. Prenex_left r =
           PPAT (\x q. let y = VARIANT(FV(!!x q) UNION FV(p)) in
                 ??y (Prenex_left (formsubst (valmod (x,V y) V) q)))
                (\x q. let y = VARIANT(FV(??x q) UNION FV(p)) in
                 !!y (Prenex_left (formsubst (valmod (x,V y) V) q)))
                (\q. Prenex_right q p) r]])
       MP_TAC THENL
        [GEN_TAC THEN MATCH_MP_TAC SIZE_REC THEN
         REPEAT STRIP_TAC THEN REWRITE_TAC [PPAT_DEF] THEN
         ASM_CASES_TAC [[?x p. r = !!x p]] THEN ASM_REWRITE_TAC [] THENL
          [FIRST_X_ASSUM (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC)) THEN
           REWRITE_TAC [form_DISTINCT, form_INJ] THEN
           REWRITE_TAC [RIGHT_EXISTS_AND_THM, EXISTS_REFL, (← HolLight.GSYM EXISTS_REFL),
                   SELECT_REFL, selsym] THEN
           REWRITE_TAC [LET_DEF, LET_END_DEF] THEN
           AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
           REWRITE_TAC [SIZE_FORMSUBST, SIZE] THEN ARITH_TAC, ALL_TAC] THEN
         COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
         FIRST_X_ASSUM (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC)) THEN
         REWRITE_TAC [PRENEX_DISTINCT] THEN
         REWRITE_TAC [RIGHT_EXISTS_AND_THM, EXISTS_REFL, (← HolLight.GSYM EXISTS_REFL),
                   SELECT_REFL, selsym] THEN
         REWRITE_TAC [LET_DEF, LET_END_DEF] THEN
         AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
         REWRITE_TAC [SIZE_FORMSUBST, SIZE] THEN ARITH_TAC, ALL_TAC] THEN
       DISCH_THEN (MP_TAC oTIO HolLight.GEN_REWRITE_RULE HolCore.Lib.I [SKOLEM_THM]) THEN
       DISCH_THEN (X_CHOOSE_TAC [[Prenex_left:form->form->form]]) THEN
       EXISTS_TAC [[\q p. (Prenex_left:form->form->form) p q]] THEN
       REWRITE_TAC [] THEN
       REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY DISCH_TAC THEN
       FIRST_ASSUM (fun th => GEN_REWRITE_TAC HolLight.LAND_CONV [th]) THEN
       REWRITE_TAC [PPAT] THEN
       UNDISCH_TAC [[qfree q]] THEN REWRITE_TAC [PPAT_DEF] THEN
       POP_ASSUM_LIST (HolCore.Lib.K ALL_TAC) THEN
       COND_CASES_TAC THENL [POP_ASSUM (STRIP_ASSUME_TAC) THEN
                             ASM_REWRITE_TAC [QFREE], ALL_TAC] THEN
       COND_CASES_TAC THENL [POP_ASSUM (STRIP_ASSUME_TAC) THEN
                             ASM_REWRITE_TAC [QFREE], ALL_TAC] THEN
       REWRITE_TAC []))
  : ExceptT String IO thm).run
#eval PRENEX_LEFT_EXISTENCE

#eval phrase 24
unsafe def PRENEX_LEFT : thm := keep "PRENEX_LEFT" fun _ =>
  (newSpec ["Prenex_left"] PRENEX_LEFT_EXISTENCE : ExceptT String IO thm).run
#eval PRENEX_LEFT

#eval phrase 25
unsafe def Prenex_DEF : thm := keep "Prenex_DEF" fun _ => (do
  newRec form_RECURSION
    [[(Prenex False = False) /\
      (Prenex (Atom a l) = Atom a l) /\
      (Prenex (p --> q) = Prenex_left (Prenex p) (Prenex q)) /\
      (Prenex (!!x p) = !!x (Prenex p))]]
  : ExceptT String IO thm).run
#eval Prenex_DEF

#eval phrase 26
unsafe def PRENEX_RIGHT_FORALL : thm := keep "PRENEX_RIGHT_FORALL" fun _ => (do
  prove ([[~(Dom M :A->bool = EMPTY)
   ==> (holds M v (p --> !!x q) <=>
        holds M v (!! (VARIANT (FV(p) UNION FV(!!x q)))
                      (p --> formsubst (valmod
                               (x,V(VARIANT (FV(p) UNION FV(!!x q)))) V) q)))]])
   (DISCH_TAC THEN
    ABBREV_TAC [[y = VARIANT (FV(p) UNION FV(!!x q))]] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC [[holds M (v:num->A)
                    (p --> !!y (formsubst (valmod (x,V y) V) q))]] THEN
    SUBGOAL_THEN ([[~(y IN FV(p)) /\ ~(y IN FV(!!x q))]]) STRIP_ASSUME_TAC THENL
     [REWRITE_TAC [(← HolLight.GSYM DE_MORGAN_THM), (← HolLight.GSYM IN_UNION)] THEN
      Fol.EXPAND_TAC "y" THEN REWRITE_TAC [VARIANT_THM, (← HolLight.GSYM FV)], ALL_TAC] THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC [holds] THEN
      MATCH_MP_TAC (← ExceptT.mk (TAUT [[(a ==> (b <=> c)) ==> ((a ==> b) <=> (a ==> c))]])) THEN
      DISCH_TAC THEN REWRITE_TAC [HOLDS, HOLDS_FORMSUBST] THEN
      AP_TERM_TAC THEN ABS_TAC THEN
      MATCH_MP_TAC (← ExceptT.mk (TAUT [[(a ==> (b <=> c)) ==> ((a ==> b) <=> (a ==> c))]])) THEN
      DISCH_TAC THEN MATCH_MP_TAC HOLDS_VALUATION THEN
      X_GEN_TAC [[z:num]] THEN DISCH_TAC THEN
      REWRITE_TAC [valmod, o_THM] THEN
      COND_CASES_TAC THEN REWRITE_TAC [termval] THEN
      COND_CASES_TAC THEN REWRITE_TAC [] THEN
      UNDISCH_TAC [[~(y IN FV(!!x q))]] THEN
      ASM_REWRITE_TAC [FV, IN_DELETE] THEN ASM_MESON_TAC [],
      REWRITE_TAC [HOLDS] THEN
      SUBGOAL_THEN ([[!v a:A. holds M (valmod (y,a) v) p = holds M v p]])
      (fun th => REWRITE_TAC [th]) THENL
      [ALL_TAC, ASM_CASES_TAC [[holds M (v:num->A) p]] THEN ASM_REWRITE_TAC []] THEN
      REPEAT GEN_TAC THEN MATCH_MP_TAC HOLDS_VALUATION THEN
      GEN_TAC THEN REWRITE_TAC [valmod] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC []])
  : ExceptT String IO thm).run
#eval PRENEX_RIGHT_FORALL

#eval phrase 27
unsafe def PRENEX_RIGHT_EXISTS : thm := keep "PRENEX_RIGHT_EXISTS" fun _ => (do
  prove ([[~(Dom M :A->bool = EMPTY)
   ==> (holds M v (p --> ??x q) <=>
        holds M v (?? (VARIANT (FV(p) UNION FV(??x q)))
                      (p --> formsubst (valmod
                               (x,V(VARIANT (FV(p) UNION FV(??x q)))) V) q)))]])
   (DISCH_TAC THEN
    ABBREV_TAC [[y = VARIANT (FV(p) UNION FV(??x q))]] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC [[holds M (v:num->A)
                    (p --> ??y (formsubst (valmod (x,V y) V) q))]] THEN
    SUBGOAL_THEN ([[~(y IN FV(p)) /\ ~(y IN FV(??x q))]]) STRIP_ASSUME_TAC THENL
     [REWRITE_TAC [(← HolLight.GSYM DE_MORGAN_THM), (← HolLight.GSYM IN_UNION)] THEN
      Fol.EXPAND_TAC "y" THEN REWRITE_TAC [VARIANT_THM, (← HolLight.GSYM FV)], ALL_TAC] THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC [holds] THEN
      MATCH_MP_TAC (← ExceptT.mk (TAUT [[(a ==> (b <=> c)) ==> ((a ==> b) <=> (a ==> c))]])) THEN
      DISCH_TAC THEN REWRITE_TAC [HOLDS, HOLDS_FORMSUBST] THEN
      AP_TERM_TAC THEN ABS_TAC THEN
      MATCH_MP_TAC (← ExceptT.mk (TAUT [[(a ==> (b <=> c)) ==> ((a /\ b) <=> (a /\ c))]])) THEN
      DISCH_TAC THEN MATCH_MP_TAC HOLDS_VALUATION THEN
      X_GEN_TAC [[z:num]] THEN DISCH_TAC THEN
      REWRITE_TAC [valmod, o_THM] THEN
      COND_CASES_TAC THEN REWRITE_TAC [termval] THEN
      COND_CASES_TAC THEN REWRITE_TAC [] THEN
      UNDISCH_TAC [[~(y IN FV(??x q))]] THEN
      ASM_REWRITE_TAC [FV, Not_DEF, Exists_DEF, UNION_EMPTY, IN_DELETE] THEN
      ASM_MESON_TAC [],
      REWRITE_TAC [HOLDS] THEN
      SUBGOAL_THEN ([[!v a:A. holds M (valmod (y,a) v) p = holds M v p]])
      (fun th => REWRITE_TAC [th]) THENL
       [REPEAT GEN_TAC THEN MATCH_MP_TAC HOLDS_VALUATION THEN
        GEN_TAC THEN REWRITE_TAC [valmod] THEN COND_CASES_TAC THEN
        ASM_REWRITE_TAC [],
        ASM_CASES_TAC [[holds M (v:num->A) p]] THEN ASM_REWRITE_TAC [] THEN
        ASM_REWRITE_TAC [MEMBER_NOT_EMPTY]]])
  : ExceptT String IO thm).run
#eval PRENEX_RIGHT_EXISTS

#eval phrase 28
unsafe def PRENEX_DUALITY_LEMMAS : thm := keep "PRENEX_DUALITY_LEMMAS" fun _ => (do
  prove ([[(holds M v (??x p --> q) <=> holds M v (Not q --> !!x (Not p))) /\
   (holds M v (!!x p --> q) <=> holds M v (Not q --> ??x (Not p)))]])
   (REWRITE_TAC [HOLDS] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval PRENEX_DUALITY_LEMMAS

#eval phrase 29
unsafe def PRENEX_LEFT_FORALL : thm := keep "PRENEX_LEFT_FORALL" fun _ => (do
  prove ([[~(Dom M :A->bool = EMPTY)
   ==> (holds M v (!!x p --> q) <=>
        holds M v (?? (VARIANT (FV(!!x p) UNION FV(q)))
                      (formsubst (valmod
                        (x,V(VARIANT (FV(!!x p) UNION FV(q)))) V) p --> q)))]])
   (DISCH_TAC THEN REWRITE_TAC [PRENEX_DUALITY_LEMMAS] THEN
    FIRST_ASSUM (fun th => HolLight.tactic_of do
      let r ← ExceptT.mk (HolLight.MATCH_MP PRENEX_RIGHT_EXISTS th); pure (REWRITE_TAC [r])) THEN
    REWRITE_TAC [Exists_DEF, Not_DEF, FV, UNION_EMPTY, UNION_COMM] THEN
    REWRITE_TAC [holds, formsubst, (← ExceptT.mk (TAUT [[(~a ==> ~b) <=> (b ==> a)]]))])
  : ExceptT String IO thm).run
#eval PRENEX_LEFT_FORALL

#eval phrase 30
unsafe def PRENEX_LEFT_EXISTS : thm := keep "PRENEX_LEFT_EXISTS" fun _ => (do
  prove ([[~(Dom M :A->bool = EMPTY)
   ==> (holds M v (??x p --> q) <=>
        holds M v (!! (VARIANT (FV(??x p) UNION FV(q)))
                      (formsubst (valmod
                        (x,V(VARIANT (FV(??x p) UNION FV(q)))) V) p --> q)))]])
   (DISCH_TAC THEN REWRITE_TAC [PRENEX_DUALITY_LEMMAS] THEN
    FIRST_ASSUM (fun th => HolLight.tactic_of do
      let r ← ExceptT.mk (HolLight.MATCH_MP PRENEX_RIGHT_FORALL th); pure (REWRITE_TAC [r])) THEN
    REWRITE_TAC [Exists_DEF, Not_DEF, FV, UNION_EMPTY, UNION_COMM] THEN
    REWRITE_TAC [holds, formsubst, (← ExceptT.mk (TAUT [[(~a ==> ~b) <=> (b ==> a)]]))])
  : ExceptT String IO thm).run
#eval PRENEX_LEFT_EXISTS

#eval phrase 31
unsafe def PRENEX_RIGHT_FORALL_FV : thm := keep "PRENEX_RIGHT_FORALL_FV" fun _ => (do
  prove ([[FV(p --> !!x q) = FV(!! (VARIANT (FV(p) UNION FV(!!x q)))
                           (p --> formsubst (valmod
                              (x,V(VARIANT (FV(p) UNION FV(!!x q)))) V) q))]])
   (HolLight.tactic_of do
     let lemma ← prove
      ([[(s UNION t) DELETE x = (s DELETE x) UNION (t DELETE x)]]) (SET_TAC [])
     pure
      (REWRITE_TAC [FV, FORMSUBST_RENAME, lemma] THEN
       MP_TAC (← ExceptT.mk (HolLight.SPEC ([[p --> !!x q]]) VARIANT_THM)) THEN
       REWRITE_TAC [EXTENSION, FV, IN_UNION, IN_DELETE] THEN MESON_TAC []))
  : ExceptT String IO thm).run
#eval PRENEX_RIGHT_FORALL_FV

#eval phrase 32
unsafe def PRENEX_RIGHT_EXISTS_FV : thm := keep "PRENEX_RIGHT_EXISTS_FV" fun _ => (do
  prove ([[FV(p --> ??x q) =
   FV(?? (VARIANT (FV(p) UNION FV(??x q)))
           (p --> formsubst (valmod
                   (x,V(VARIANT (FV(p) UNION FV(??x q)))) V) q))]])
   (HolLight.tactic_of do
     let lemma ← prove
      ([[(s UNION t) DELETE x = (s DELETE x) UNION (t DELETE x)]]) (SET_TAC [])
     pure
      (REWRITE_TAC [FV, FV_EXISTS, FORMSUBST_RENAME, lemma] THEN
       MP_TAC (← ExceptT.mk (HolLight.SPEC ([[p --> ??x q]]) VARIANT_THM)) THEN
       REWRITE_TAC [EXTENSION, FV, FV_EXISTS, IN_UNION, IN_DELETE] THEN
       MESON_TAC []))
  : ExceptT String IO thm).run
#eval PRENEX_RIGHT_EXISTS_FV

#eval phrase 33
unsafe def PRENEX_LEFT_FORALL_FV : thm := keep "PRENEX_LEFT_FORALL_FV" fun _ => (do
  prove ([[FV(!!x p --> q) =
   FV(?? (VARIANT (FV(!!x p) UNION FV(q)))
                      (formsubst (valmod
                        (x,V(VARIANT (FV(!!x p) UNION FV(q)))) V) p --> q))]])
   (HolLight.tactic_of do
     let lemma ← prove
      ([[(s UNION t) DELETE x = (s DELETE x) UNION (t DELETE x)]]) (SET_TAC [])
     pure
      (REWRITE_TAC [FV, FV_EXISTS, FORMSUBST_RENAME, lemma] THEN
       MP_TAC (← ExceptT.mk (HolLight.SPEC ([[!!x p --> q]]) VARIANT_THM)) THEN
       REWRITE_TAC [EXTENSION, FV, FV_EXISTS, IN_UNION, IN_DELETE] THEN
       MESON_TAC []))
  : ExceptT String IO thm).run
#eval PRENEX_LEFT_FORALL_FV

#eval phrase 34
unsafe def PRENEX_LEFT_EXISTS_FV : thm := keep "PRENEX_LEFT_EXISTS_FV" fun _ => (do
  prove ([[FV(??x p --> q) =
   FV(!! (VARIANT (FV(??x p) UNION FV(q)))
                      (formsubst (valmod
                        (x,V(VARIANT (FV(??x p) UNION FV(q)))) V) p --> q))]])
   (HolLight.tactic_of do
     let lemma ← prove
      ([[(s UNION t) DELETE x = (s DELETE x) UNION (t DELETE x)]]) (SET_TAC [])
     pure
      (REWRITE_TAC [FV, FV_EXISTS, FORMSUBST_RENAME, lemma] THEN
       MP_TAC (← ExceptT.mk (HolLight.SPEC ([[??x p --> q]]) VARIANT_THM)) THEN
       REWRITE_TAC [EXTENSION, FV, FV_EXISTS, IN_UNION, IN_DELETE] THEN
       MESON_TAC []))
  : ExceptT String IO thm).run
#eval PRENEX_LEFT_EXISTS_FV

#eval phrase 35
unsafe def PRENEX_RIGHT_FORALL_LANGUAGE : thm := keep "PRENEX_RIGHT_FORALL_LANGUAGE" fun _ => (do
  prove ([[language {(p --> !!x q)} = language {(!! (VARIANT (FV(p) UNION FV(!!x q)))
                           (p --> formsubst (valmod
                              (x,V(VARIANT (FV(p) UNION FV(!!x q)))) V) q))}]])
   (REWRITE_TAC [LANGUAGE_1, functions_form, predicates_form] THEN
    REWRITE_TAC [(← HolLight.REWRITE_RULE [PAIR_EQ, LANGUAGE_1] FORMSUBST_LANGUAGE_RENAME)])
  : ExceptT String IO thm).run
#eval PRENEX_RIGHT_FORALL_LANGUAGE

#eval phrase 36
unsafe def PRENEX_RIGHT_EXISTS_LANGUAGE : thm := keep "PRENEX_RIGHT_EXISTS_LANGUAGE" fun _ => (do
  prove ([[language {(p --> ??x q)} =
   language {(?? (VARIANT (FV(p) UNION FV(??x q)))
           (p --> formsubst (valmod
                   (x,V(VARIANT (FV(p) UNION FV(??x q)))) V) q))}]])
   (REWRITE_TAC [LANGUAGE_1, functions_form, predicates_form,
                Exists_DEF, Not_DEF, UNION_EMPTY] THEN
    REWRITE_TAC [(← HolLight.REWRITE_RULE [PAIR_EQ, LANGUAGE_1] FORMSUBST_LANGUAGE_RENAME)])
  : ExceptT String IO thm).run
#eval PRENEX_RIGHT_EXISTS_LANGUAGE

#eval phrase 37
unsafe def PRENEX_LEFT_FORALL_LANGUAGE : thm := keep "PRENEX_LEFT_FORALL_LANGUAGE" fun _ => (do
  prove ([[language {(!!x p --> q)} =
   language {(?? (VARIANT (FV(!!x p) UNION FV(q)))
                      (formsubst (valmod
                        (x,V(VARIANT (FV(!!x p) UNION FV(q)))) V) p --> q))}]])
   (REWRITE_TAC [LANGUAGE_1, functions_form, predicates_form,
                Exists_DEF, Not_DEF, UNION_EMPTY] THEN
    REWRITE_TAC [(← HolLight.REWRITE_RULE [PAIR_EQ, LANGUAGE_1] FORMSUBST_LANGUAGE_RENAME)])
  : ExceptT String IO thm).run
#eval PRENEX_LEFT_FORALL_LANGUAGE

#eval phrase 38
unsafe def PRENEX_LEFT_EXISTS_LANGUAGE : thm := keep "PRENEX_LEFT_EXISTS_LANGUAGE" fun _ => (do
  prove ([[language {(??x p --> q)} =
   language {(!! (VARIANT (FV(??x p) UNION FV(q)))
                      (formsubst (valmod
                        (x,V(VARIANT (FV(??x p) UNION FV(q)))) V) p --> q))}]])
   (REWRITE_TAC [LANGUAGE_1, functions_form, predicates_form,
                Exists_DEF, Not_DEF, UNION_EMPTY] THEN
    REWRITE_TAC [(← HolLight.REWRITE_RULE [PAIR_EQ, LANGUAGE_1] FORMSUBST_LANGUAGE_RENAME)])
  : ExceptT String IO thm).run
#eval PRENEX_LEFT_EXISTS_LANGUAGE

#eval phrase 39
unsafe def PRENEX_LEMMA_FORALL : thm := keep "PRENEX_LEMMA_FORALL" fun _ => (do
  prove ([[P /\
   (FV r1 = FV r2) /\
   (language {r1} = language {r2}) /\
   (!M v. ~(Dom M :A->bool = EMPTY) ==> (holds M v p <=> holds M v q))
   ==> P /\
       (FV(!!z r1) = FV(!!z r2)) /\
       (language {(!!z r1)} = language {(!!z r2)}) /\
       !M v. ~(Dom M :A->bool = EMPTY)
               ==> (holds M v (!!x p) <=> holds M v (!!x q))]])
   (REWRITE_TAC [LANGUAGE_1, PAIR_EQ] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [FV, functions_form, predicates_form] THEN
    ASM_SIMP_TAC [HOLDS])
  : ExceptT String IO thm).run
#eval PRENEX_LEMMA_FORALL

#eval phrase 40
unsafe def PRENEX_LEMMA_EXISTS : thm := keep "PRENEX_LEMMA_EXISTS" fun _ => (do
  prove ([[P /\
   (FV r1 = FV r2) /\
   (language {r1} = language {r2}) /\
   (!M v. ~(Dom M :A->bool = EMPTY) ==> (holds M v p <=> holds M v q))
   ==> P /\
       (FV(??z r1) = FV(??z r2)) /\
       (language {(??z r1)} = language {(??z r2)}) /\
       !M v. ~(Dom M :A->bool = EMPTY)
               ==> (holds M v (??x p) <=> holds M v (??x q))]])
   (REWRITE_TAC [LANGUAGE_1, PAIR_EQ] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [FV, FV_EXISTS] THEN
    ASM_SIMP_TAC [HOLDS] THEN
    ASM_REWRITE_TAC [Exists_DEF, Not_DEF, functions_form, predicates_form])
  : ExceptT String IO thm).run
#eval PRENEX_LEMMA_EXISTS

#eval phrase 41
unsafe def PRENEX_RIGHT_THM : thm := keep "PRENEX_RIGHT_THM" fun _ => (do
  prove ([[!p q. qfree p /\ prenex q
         ==> prenex (Prenex_right p q) /\
             (FV(Prenex_right p q) = FV(p --> q)) /\
             (language {(Prenex_right p q)} = language {(p --> q)}) /\
             (!M v. ~(Dom M :A->bool = EMPTY)
                    ==> (holds M v (Prenex_right p q) <=>
                         holds M v (p --> q)))]])
   (SUBGOAL_THEN
     ([[!p. qfree p
        ==> !n q. prenex(q) /\ (size(q) = n)
                  ==> prenex (Prenex_right p q) /\
                      (FV(Prenex_right p q) = FV(p --> q)) /\
                      (language {(Prenex_right p q)} = language {(p --> q)}) /\
                      (!M v. ~(Dom M :A->bool = EMPTY)
                              ==> (holds M v (Prenex_right p q) <=>
                                   holds M v (p --> q)))]])
    (fun th => MESON_TAC [th]) THEN
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC num_WF THEN
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM (STRIP_ASSUME_TAC oTIO HolLight.GEN_REWRITE_RULE HolCore.Lib.I [prenex_CASES]) THENL
     [ASM_SIMP_TAC [PRENEX_RIGHT, PRENEX], ALL_TAC, ALL_TAC] THEN
    ASM_REWRITE_TAC [PRENEX_RIGHT] THEN
    REWRITE_TAC [LET_DEF, LET_END_DEF, PRENEX] THEN
    SIMP_TAC [PRENEX_RIGHT_FORALL, PRENEX_RIGHT_EXISTS] THEN
    REWRITE_TAC [PRENEX_RIGHT_FORALL_FV, PRENEX_RIGHT_FORALL_LANGUAGE] THEN
    REWRITE_TAC [PRENEX_RIGHT_EXISTS_FV, PRENEX_RIGHT_EXISTS_LANGUAGE] THENL
     [MATCH_MP_TAC PRENEX_LEMMA_FORALL, MATCH_MP_TAC PRENEX_LEMMA_EXISTS] THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [RIGHT_IMP_FORALL_THM,
                                IMP_IMP]) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC [[size p']] THEN
    REWRITE_TAC [PRENEX_FORMSUBST, SIZE_FORMSUBST] THEN
    UNDISCH_TAC [[size q = n]] THEN DISCH_THEN (SUBST_ALL_TAC oTIO HolLight.SYM) THEN
    ASM_REWRITE_TAC [SIZE] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval PRENEX_RIGHT_THM

#eval phrase 42
unsafe def PRENEX_LEFT_THM : thm := keep "PRENEX_LEFT_THM" fun _ => (do
  prove ([[!p q. prenex p /\ prenex q
         ==> prenex (Prenex_left p q) /\
             (FV(Prenex_left p q) = FV(p --> q)) /\
             (language {(Prenex_left p q)} = language {(p --> q)}) /\
             (!M v. ~(Dom M :A->bool = EMPTY)
                    ==> (holds M v (Prenex_left p q) <=> holds M v (p --> q)))]])
   (SUBGOAL_THEN
     ([[!q. prenex(q)
        ==> !n p. prenex(p) /\ (size(p) = n)
                  ==> prenex (Prenex_left p q) /\
                      (FV(Prenex_left p q) = FV(p --> q)) /\
                      (language {(Prenex_left p q)} = language {(p --> q)}) /\
                      (!M v. ~(Dom M :A->bool = EMPTY)
                              ==> (holds M v (Prenex_left p q) <=>
                                   holds M v (p --> q)))]])
    (fun th => MESON_TAC [th]) THEN
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC num_WF THEN
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM (STRIP_ASSUME_TAC oTIO HolLight.GEN_REWRITE_RULE HolCore.Lib.I [prenex_CASES]) THENL
     [ASM_SIMP_TAC [PRENEX_LEFT, PRENEX] THEN
      MATCH_MP_TAC PRENEX_RIGHT_THM THEN ASM_REWRITE_TAC [],
      ALL_TAC, ALL_TAC] THEN
    ASM_REWRITE_TAC [PRENEX_LEFT] THEN
    REWRITE_TAC [LET_DEF, LET_END_DEF, PRENEX] THEN
    SIMP_TAC [PRENEX_LEFT_FORALL, PRENEX_LEFT_EXISTS] THEN
    REWRITE_TAC [PRENEX_LEFT_FORALL_FV, PRENEX_LEFT_FORALL_LANGUAGE] THEN
    REWRITE_TAC [PRENEX_LEFT_EXISTS_FV, PRENEX_LEFT_EXISTS_LANGUAGE] THENL
     [MATCH_MP_TAC PRENEX_LEMMA_EXISTS, MATCH_MP_TAC PRENEX_LEMMA_FORALL] THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [RIGHT_IMP_FORALL_THM,
                                IMP_IMP]) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC [[size p']] THEN
    REWRITE_TAC [PRENEX_FORMSUBST, SIZE_FORMSUBST] THEN
    UNDISCH_TAC [[size p = n]] THEN DISCH_THEN (SUBST_ALL_TAC oTIO HolLight.SYM) THEN
    ASM_REWRITE_TAC [SIZE] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval PRENEX_LEFT_THM

#eval phrase 43
unsafe def PRENEX_THM : thm := keep "PRENEX_THM" fun _ => (do
  prove ([[!p. prenex(Prenex p) /\
       (FV(Prenex p) = FV(p)) /\
       (language {(Prenex p)} = language {p}) /\
       !M v. ~(Dom M = EMPTY)
             ==> (holds M (v:num->A) (Prenex p) <=> holds M v p)]])
   (MATCH_MP_TAC form_INDUCTION THEN
    REWRITE_TAC [PRENEX, Prenex_DEF] THEN REWRITE_TAC [HOLDS] THEN
    MP_TAC PRENEX_LEFT_THM THEN
    REWRITE_TAC [HOLDS, FV, LANGUAGE_1, PAIR_EQ] THEN
    REWRITE_TAC [functions_form, predicates_form] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval PRENEX_THM

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py from the `#eval`s above. -/
unsafe def ensure : IO Unit := once "HolLogicArith.Prenex" do
  replay (
          HolLogicArith.Fol.ensure)
  replay (
          qfree)
  replay (
          QFREE)
  replay (
          QFREE_FORMSUBST)
  replay (
          QFREE_BV_EMPTY)
  replay (
          do IO.println prenex_RULES; IO.println prenex_INDUCT; IO.println prenex_CASES)
  replay (
          do IO.println universal_RULES; IO.println universal_INDUCT; IO.println universal_CASES)
  replay (
          prenex_INDUCT_NOT)
  replay (
          PRENEX)
  replay (
          FORMSUBST_STRUCTURE_LEMMA)
  replay (
          FORMSUBST_STRUCTURE_NOT)
  replay (
          FORMSUBST_STRUCTURE_EXISTS)
  replay (
          PRENEX_FORMSUBST_LEMMA)
  replay (
          PRENEX_FORMSUBST)
  replay (
          size)
  replay (
          SIZE)
  replay (
          SIZE_FORMSUBST)
  replay (
          PPAT_DEF)
  replay (
          PRENEX_DISTINCT)
  replay (
          PPAT)
  replay (
          SIZE_REC)
  replay (
          PRENEX_RIGHT_EXISTENCE)
  replay (
          PRENEX_RIGHT)
  replay (
          PRENEX_LEFT_EXISTENCE)
  replay (
          PRENEX_LEFT)
  replay (
          Prenex_DEF)
  replay (
          PRENEX_RIGHT_FORALL)
  replay (
          PRENEX_RIGHT_EXISTS)
  replay (
          PRENEX_DUALITY_LEMMAS)
  replay (
          PRENEX_LEFT_FORALL)
  replay (
          PRENEX_LEFT_EXISTS)
  replay (
          PRENEX_RIGHT_FORALL_FV)
  replay (
          PRENEX_RIGHT_EXISTS_FV)
  replay (
          PRENEX_LEFT_FORALL_FV)
  replay (
          PRENEX_LEFT_EXISTS_FV)
  replay (
          PRENEX_RIGHT_FORALL_LANGUAGE)
  replay (
          PRENEX_RIGHT_EXISTS_LANGUAGE)
  replay (
          PRENEX_LEFT_FORALL_LANGUAGE)
  replay (
          PRENEX_LEFT_EXISTS_LANGUAGE)
  replay (
          PRENEX_LEMMA_FORALL)
  replay (
          PRENEX_LEMMA_EXISTS)
  replay (
          PRENEX_RIGHT_THM)
  replay (
          PRENEX_LEFT_THM)
  replay (
          PRENEX_THM)
-- @@ENSURE END

end HolLogicArith.Prenex
