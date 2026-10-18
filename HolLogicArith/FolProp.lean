/- File: HolLogicArith/FolProp.lean
Translation of HOL Light's Logic/fol_prop.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolLogicArith.Fol
open HolCore.Kernel Session HolLight.Syntax HolLogicArith
open scoped HolLight
-- Names from fol.ml that we reuse here (fol_prop.ml uses the latest binding).
open HolLogicArith.Fol (entails form_INDUCTION form_INJ form_RECURSION
  Not_DEF True_DEF Or_DEF And_DEF Iff_DEF Exists_DEF)

namespace HolLogicArith.FolProp

/- List definitions/theorems used below are exposed by Session as fields of
   the `listDefs`/`listThms1` bundles; alias the ones we need. -/
private unsafe def ALL : thm := Session.listDefs.ALL
private unsafe def ITLIST : thm := Session.listDefs.ITLIST
private unsafe def ALL_IMP : thm := Session.listThms1.ALL_IMP

/- Zorn's lemma and poset/chain machinery come from Library/wo.ml, exposed by
   SessionLibrary.Wo (replayed as part of Fol's prelude). -/
private unsafe def ZL : thm := SessionLibrary.Wo.ZL
private unsafe def poset : thm := SessionLibrary.Wo.poset
private unsafe def fld : thm := SessionLibrary.Wo.fld
private unsafe def chain : thm := SessionLibrary.Wo.chain
private unsafe def PBETA_TAC : HolCore.Tactics.tactic := SessionLibrary.Wo.PBETA_TAC

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- `new_recursive_definition` lifted into `ExceptT String IO`. -/
private unsafe def newRec (ax : thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (Session.new_recursive_definition ax tm)

#eval HolLogicArith.Fol.ensure

/- Library/wo.ml is loaded by make.ml BEFORE fol_prop.ml, so HOL Light runs
   ZL/poset/chain's proofs in the prelude.  HolLean builds the Wo bundles
   lazily on first use; force them here (in the prelude, whose output is not
   compared) so their traces don't surface inside phrase 11 (FINSAT_MAX). -/
#eval show IO Unit from do
  let _ ← IO.mkRef ZL
  let _ ← IO.mkRef poset
  let _ ← IO.mkRef fld
  let _ ← IO.mkRef chain
  pure ()

#eval phrase 1
unsafe def pholds : thm := keep "pholds" fun _ => (do
  newRec form_RECURSION
    [[(pholds v False <=> F) /\
      (pholds v (Atom p l) <=> v (Atom p l)) /\
      (pholds v (q --> r) <=> pholds v q ==> pholds v r) /\
      (pholds v (!!x q) <=> v (!!x q))]]
  : ExceptT String IO thm).run
#eval pholds

#eval phrase 2
unsafe def PHOLDS : thm := keep "PHOLDS" fun _ => (do
  prove ([[(pholds v False <=> F) /\
   (pholds v True <=> T) /\
   (pholds v (Atom p l) <=> v (Atom p l)) /\
   (pholds v (Not q) <=> ~(pholds v q)) /\
   (pholds v (q || r) <=> pholds v q \/ pholds v r) /\
   (pholds v (q && r) <=> pholds v q /\ pholds v r) /\
   (pholds v (q --> r) <=> pholds v q ==> pholds v r) /\
   (pholds v (q <-> r) <=> (pholds v q = pholds v r))]])
   (REWRITE_TAC
     [True_DEF, Not_DEF, Or_DEF, And_DEF, Iff_DEF, Exists_DEF, pholds] THEN
    CONV_TAC TAUT)
  : ExceptT String IO thm).run
#eval PHOLDS

#eval phrase 3
#eval parse_as_infix ("psatisfies", (10, "right"))

#eval phrase 4
unsafe def psatisfies : thm := keep "psatisfies" fun _ => new_definition
  [[v psatisfies s <=> !p. p IN s ==> pholds v p]]
#eval psatisfies

#eval phrase 5
unsafe def psatisfiable : thm := keep "psatisfiable" fun _ => new_definition
  [[psatisfiable s <=> ?v. !p. p IN s ==> pholds v p]]
#eval psatisfiable

#eval phrase 6
unsafe def PSATISFIABLE_MONO : thm := keep "PSATISFIABLE_MONO" fun _ => (do
  prove ([[!A B. psatisfiable A /\ B SUBSET A ==> psatisfiable B]])
   (REWRITE_TAC [psatisfiable] THEN MESON_TAC [SUBSET])
  : ExceptT String IO thm).run
#eval PSATISFIABLE_MONO

#eval phrase 7
unsafe def finsat : thm := keep "finsat" fun _ => new_definition
  [[finsat A <=> !B. B SUBSET A /\ FINITE(B) ==> psatisfiable B]]
#eval finsat

#eval phrase 8
unsafe def FINSAT_MONO : thm := keep "FINSAT_MONO" fun _ => (do
  prove ([[!A B. finsat A /\ B SUBSET A ==> finsat B]])
   (REWRITE_TAC [finsat] THEN MESON_TAC [SUBSET_TRANS, FINITE_SUBSET])
  : ExceptT String IO thm).run
#eval FINSAT_MONO

#eval phrase 9
unsafe def SATISFIABLE_MONO : thm := keep "SATISFIABLE_MONO" fun _ => (do
  prove ([[!A B. psatisfiable A /\ B SUBSET A ==> psatisfiable B]])
   (REWRITE_TAC [psatisfiable] THEN MESON_TAC [SUBSET])
  : ExceptT String IO thm).run
#eval SATISFIABLE_MONO

#eval phrase 10
unsafe def FINSAT_SATISFIABLE : thm := keep "FINSAT_SATISFIABLE" fun _ => (do
  prove ([[psatisfiable B ==> finsat B]])
   (REWRITE_TAC [finsat] THEN
    MESON_TAC [SATISFIABLE_MONO, SUBSET_TRANS, FINITE_SUBSET])
  : ExceptT String IO thm).run
#eval FINSAT_SATISFIABLE

#eval phrase 11
unsafe def FINSAT_MAX : thm := keep "FINSAT_MAX" fun _ => (do
  prove ([[!A. finsat(A) ==> ?B. A SUBSET B /\ finsat(B) /\
                         !C. B SUBSET C /\ finsat(C) ==> (C = B)]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ExceptT.mk (HolLight.ISPEC ([[\B C. A SUBSET B /\ B SUBSET C /\ finsat(C)]]) ZL)) THEN
    PBETA_TAC THEN REWRITE_TAC [] THEN
    SUBGOAL_THEN ([[poset (\B C. A SUBSET B /\ B SUBSET C /\ finsat(C))]])
    ASSUME_TAC THENL
     [REWRITE_TAC [poset, fld, IN_ELIM_THM] THEN
      MESON_TAC [SUBSET_TRANS, SUBSET_REFL, FINSAT_MONO, SUBSET_ANTISYM],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN ([[fld(\B C. A SUBSET B /\ B SUBSET C /\ finsat(C)) =
                 \B. A SUBSET B /\ finsat(B)]])
    ASSUME_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM, fld, IN_ELIM_THM] THEN
      MESON_TAC [SUBSET_TRANS, FINSAT_MONO, SUBSET_REFL], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    HolCore.Lib.W (fun g => HolLight.tactic_of do
        let tm ← liftExcept (HolCore.Equal.lhand (← HolCore.Equal.lhand (HolLight.snd g)))
        pure (SUBGOAL_THEN tm (fun th => REWRITE_TAC [th]))) THENL
     [ALL_TAC, MESON_TAC [SUBSET_TRANS]] THEN
    X_GEN_TAC [[C:(form->bool)->bool]] THEN
    REWRITE_TAC [chain] THEN REWRITE_TAC [IN] THEN DISCH_TAC THEN
    ASM_CASES_TAC [[C:(form->bool)->bool = EMPTY]] THENL
     [EXISTS_TAC [[A:form->bool]] THEN ASM_REWRITE_TAC [EMPTY, SUBSET_REFL],
      ALL_TAC] THEN
    EXISTS_TAC [[UNIONS (C:(form->bool)->bool)]] THEN
    FIRST_ASSUM (X_CHOOSE_THEN ([[u:form->bool]]) MP_TAC o
      HolLight.REWRITE_RULE [(← HolLight.GSYM MEMBER_NOT_EMPTY)]) THEN REWRITE_TAC [IN] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN ([[A:form->bool SUBSET (UNIONS C)]]) ASSUME_TAC THENL
     [REWRITE_TAC [UNIONS, SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC [SUBSET, IN],
      ASM_REWRITE_TAC []] THEN
    SUBGOAL_THEN ([[!B:form->bool. FINITE B ==> B SUBSET (UNIONS C)
                               ==> ?U. U IN C /\ B SUBSET U]])
    ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_INDUCT THEN CONJ_TAC THENL
       [REWRITE_TAC [EMPTY_SUBSET] THEN ASM_MESON_TAC [IN], ALL_TAC] THEN
      X_GEN_TAC [[p:form]] THEN X_GEN_TAC [[W:form->bool]] THEN
      ASM_CASES_TAC [[(p:form INSERT W) SUBSET (UNIONS C)]] THEN
      ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN ([[W:form->bool SUBSET (UNIONS C)]]) ASSUME_TAC THENL
       [ASM_MESON_TAC [SUBSET, IN_INSERT, IN], ASM_REWRITE_TAC []] THEN
      REWRITE_TAC [IN, SUBSET, INSERT, IN_ELIM_THM] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[v1:form->bool]]) STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC [[p:form INSERT W SUBSET UNIONS C]] THEN
      REWRITE_TAC [IN_INSERT, SUBSET, UNIONS, IN_ELIM_THM] THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC [[p:form]]) THEN REWRITE_TAC [] THEN
      REWRITE_TAC [IN] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[v2:form->bool]]) STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [ [[v1:form->bool]], [[v2:form->bool]] ]) THEN
      ASM_REWRITE_TAC [] THEN STRIP_TAC THENL
       [EXISTS_TAC [[v2:form->bool]] THEN ASM_REWRITE_TAC [] THEN
        RULE_ASSUM_TAC (HolLight.REWRITE_RULE [SUBSET, IN]) THEN ASM_MESON_TAC [],
        EXISTS_TAC [[v1:form->bool]] THEN ASM_REWRITE_TAC [] THEN
        RULE_ASSUM_TAC (HolLight.REWRITE_RULE [SUBSET, IN]) THEN ASM_MESON_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[finsat (UNIONS C :form->bool)]]) ASSUME_TAC THENL
     [REWRITE_TAC [finsat] THEN X_GEN_TAC [[B:form->bool]] THEN
      STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[B:form->bool]]) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[v:form->bool]]) STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [ [[v:form->bool]], [[v:form->bool]] ]) THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [IN]) THEN
      ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [finsat],
      ASM_REWRITE_TAC [] THEN X_GEN_TAC [[v:form->bool]] THEN DISCH_TAC THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC [],
        REWRITE_TAC [SUBSET, UNIONS, IN_ELIM_THM, IN] THEN
        ASM_MESON_TAC []]])
  : ExceptT String IO thm).run
#eval FINSAT_MAX

#eval phrase 12
unsafe def FINSAT_EXTEND : thm := keep "FINSAT_EXTEND" fun _ => (do
  prove ([[finsat(B) ==> finsat(p INSERT B) \/ finsat(Not p INSERT B)]])
   (HolLight.tactic_of do
     let taut1 ← ExceptT.mk (TAUT [[p <=> ~ ~ p]])
     pure
      (REWRITE_TAC [finsat] THEN DISCH_TAC THEN
       HolLight.GEN_REWRITE_TAC HolCore.Lib.I [taut1] THEN DISCH_THEN
        (MP_TAC o HolLight.REWRITE_RULE [DE_MORGAN_THM, NOT_FORALL_THM, NOT_IMP]) THEN
       DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN ([[C:form->bool]]) STRIP_ASSUME_TAC)
           (X_CHOOSE_THEN ([[D:form->bool]]) STRIP_ASSUME_TAC)) THEN
       FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[(C DELETE p) UNION (D DELETE Not p)]]) THEN
       ASM_REWRITE_TAC [NOT_IMP, FINITE_UNION, FINITE_DELETE] THEN CONJ_TAC THENL
        [ASSUM_LIST SET_TAC,
         UNDISCH_TAC [[~(psatisfiable C)]] THEN UNDISCH_TAC [[~(psatisfiable D)]] THEN
         REWRITE_TAC [psatisfiable, IN_DELETE, IN_UNION] THEN
         REWRITE_TAC [NOT_EXISTS_THM, NOT_FORALL_THM, NOT_IMP] THEN
         REPEAT DISCH_TAC THEN X_GEN_TAC [[v:form->bool]] THEN
         UNDISCH_TAC [[!v. ?p. p IN C /\ ~pholds v p]] THEN
         DISCH_THEN (MP_TAC o HolLight.SPEC [[v:form->bool]]) THEN
         DISCH_THEN (X_CHOOSE_THEN ([[q:form]]) STRIP_ASSUME_TAC) THEN
         ASM_CASES_TAC [[p:form = q]] THENL
          [ALL_TAC, ASM_MESON_TAC []] THEN
         FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[v:form->bool]]) THEN
         DISCH_THEN (X_CHOOSE_THEN ([[r:form]]) STRIP_ASSUME_TAC) THEN
         EXISTS_TAC [[r:form]] THEN ASM_REWRITE_TAC [] THEN DISJ2_TAC THEN
         DISCH_THEN SUBST_ALL_TAC THEN
         UNDISCH_TAC [[~pholds v (Not q)]] THEN ASM_REWRITE_TAC [PHOLDS]]))
  : ExceptT String IO thm).run
#eval FINSAT_EXTEND

#eval phrase 13
unsafe def FINSAT_MAX_COMPLETE : thm := keep "FINSAT_MAX_COMPLETE" fun _ => (do
  prove ([[finsat(B) /\ (!C. B SUBSET C /\ finsat(C) ==> (C = B))
   ==> !p. p IN B \/ Not(p) IN B]])
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (DISJ_CASES_TAC o HolLight.MATCH_MP FINSAT_EXTEND) THENL
     [DISJ1_TAC, DISJ2_TAC] THEN
    REWRITE_TAC [ABSORPTION] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [] THEN SET_TAC [])
  : ExceptT String IO thm).run
#eval FINSAT_MAX_COMPLETE

#eval phrase 14
unsafe def FINSAT_MAX_COMPLETE_STRONG : thm := keep "FINSAT_MAX_COMPLETE_STRONG" fun _ => (do
  prove ([[finsat(B) /\ (!C. B SUBSET C /\ finsat(C) ==> (C = B))
   ==> !p. Not(p) IN B <=> ~(p IN B)]])
   (HolLight.tactic_of do
     let taut1 ← ExceptT.mk (TAUT [[(a \/ b) /\ ~(a /\ b) ==> (b <=> ~a)]])
     let taut2 ← ExceptT.mk (TAUT [[(a \/ b) /\ c <=> a /\ c \/ b /\ c]])
     pure
      (REPEAT STRIP_TAC THEN
       MATCH_MP_TAC taut1 THEN
       CONJ_TAC THENL [ASM_MESON_TAC [FINSAT_MAX_COMPLETE], ALL_TAC] THEN
       DISCH_TAC THEN UNDISCH_TAC [[finsat B]] THEN
       REWRITE_TAC [finsat] THEN
       DISCH_THEN (MP_TAC o HolLight.SPEC [[{p,(Not p)}]]) THEN
       REWRITE_TAC [FINITE_INSERT, FINITE_RULES] THEN
       REWRITE_TAC [psatisfiable, IN_INSERT, SUBSET, NOT_IN_EMPTY] THEN
       REWRITE_TAC [NOT_IMP] THEN CONJ_TAC THENL
        [ASM_MESON_TAC [], ALL_TAC] THEN
       DISCH_THEN (CHOOSE_THEN MP_TAC) THEN
       REWRITE_TAC [NOT_FORALL_THM, NOT_IMP, DE_MORGAN_THM] THEN
       REWRITE_TAC [taut2] THEN
       REWRITE_TAC [EXISTS_OR_THM, UNWIND_THM2, PHOLDS] THEN
       CONV_TAC TAUT))
  : ExceptT String IO thm).run
#eval FINSAT_MAX_COMPLETE_STRONG

#eval phrase 15
unsafe def FINSAT_DEDUCTION : thm := keep "FINSAT_DEDUCTION" fun _ => (do
  prove ([[finsat(B) /\ (!C. B SUBSET C /\ finsat(C) ==> (C = B))
   ==> !p. p IN B <=> ?A. FINITE(A) /\ A SUBSET B /\
                        !v. (!q. q IN A ==> pholds v q) ==> pholds v p]])
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC [[{p:form}]] THEN
      REWRITE_TAC [FINITE_INSERT, FINITE_RULES] THEN
      REWRITE_TAC [SUBSET, IN_INSERT, NOT_IN_EMPTY] THEN
      ASM_MESON_TAC [],
      STRIP_TAC THEN REWRITE_TAC [ABSORPTION] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN
      UNDISCH_TAC [[finsat B]] THEN CONV_TAC HolLight.CONTRAPOS_CONV THEN
      REWRITE_TAC [finsat, NOT_FORALL_THM, NOT_IMP] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[A1:form->bool]]) STRIP_ASSUME_TAC) THEN
      EXISTS_TAC [[(A:form->bool) UNION (A1 DELETE p)]] THEN
      ASM_REWRITE_TAC [FINITE_UNION, FINITE_DELETE] THEN
      CONJ_TAC THENL [ASSUM_LIST SET_TAC, ALL_TAC] THEN
      UNDISCH_TAC [[!v. (!q. q IN A ==> pholds v q) ==> pholds v p]] THEN
      UNDISCH_TAC [[~(psatisfiable A1)]] THEN
      REWRITE_TAC [psatisfiable, IN_UNION, IN_DELETE] THEN
      MESON_TAC []])
  : ExceptT String IO thm).run
#eval FINSAT_DEDUCTION

#eval phrase 16
unsafe def FINSAT_MAX_CONSISTENT : thm := keep "FINSAT_MAX_CONSISTENT" fun _ => (do
  prove ([[finsat(B) /\ (!C. B SUBSET C /\ finsat(C) ==> (C = B))
   ==> ~(False IN B)]])
   (DISCH_THEN (MP_TAC o CONJUNCT1) THEN
    CONV_TAC HolLight.CONTRAPOS_CONV THEN REWRITE_TAC [] THEN
    DISCH_TAC THEN REWRITE_TAC [finsat] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[{False}]]) THEN
    ASM_REWRITE_TAC [FINITE_INSERT, FINITE_RULES, psatisfiable] THEN
    REWRITE_TAC [SUBSET, IN_INSERT, NOT_IN_EMPTY] THEN
    REWRITE_TAC [NOT_IMP, NOT_FORALL_THM, NOT_EXISTS_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MESON_TAC [PHOLDS])
  : ExceptT String IO thm).run
#eval FINSAT_MAX_CONSISTENT

#eval phrase 17
unsafe def FINSAT_MAX_HOMO : thm := keep "FINSAT_MAX_HOMO" fun _ => (do
  prove ([[finsat(B) /\ (!C. B SUBSET C /\ finsat(C) ==> (C = B))
   ==> !p q. (p --> q) IN B <=> p IN B ==> q IN B]])
   (DISCH_TAC THEN REPEAT GEN_TAC THEN EQ_TAC THENL
     [FIRST_ASSUM (fun th => HolLight.tactic_of do
        let mth ← HolLight.MATCH_MP FINSAT_DEDUCTION th
        pure (REWRITE_TAC [mth])) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[A1:form->bool]]) STRIP_ASSUME_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[A2:form->bool]]) STRIP_ASSUME_TAC) THEN
      EXISTS_TAC [[(A1:form->bool) UNION A2]] THEN
      ASM_REWRITE_TAC [FINITE_UNION] THEN
      CONJ_TAC THENL [ASSUM_LIST SET_TAC, ALL_TAC] THEN
      UNDISCH_TAC [[!v. (!q. q IN A2 ==> pholds v q) ==> pholds v p]] THEN
      UNDISCH_TAC [[!v. (!q. q IN A1 ==> pholds v q) ==> pholds v (p --> q)]] THEN
      REWRITE_TAC [entails, IN_UNION, PHOLDS] THEN MESON_TAC [],
      HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [(← ExceptT.mk (TAUT [[p ==> q <=> ~p \/ q]]))] THEN
      FIRST_ASSUM (fun th => HolLight.tactic_of do
        let mth ← HolLight.MATCH_MP FINSAT_MAX_COMPLETE_STRONG th
        let gth ← HolLight.GSYM mth
        pure (REWRITE_TAC [gth])) THEN
      FIRST_ASSUM (fun th => HolLight.tactic_of do
        let mth ← HolLight.MATCH_MP FINSAT_DEDUCTION th
        pure (REWRITE_TAC [mth])) THEN
      STRIP_TAC THEN EXISTS_TAC [[A:form->bool]] THEN ASM_REWRITE_TAC [] THEN
      FIRST_ASSUM (fun th => HolLight.tactic_of do
        let tm ← liftExcept (HolCore.Lib.check HolCore.Basics.is_forall (concl th))
        pure (UNDISCH_TAC tm)) THEN
      REWRITE_TAC [PHOLDS] THEN MESON_TAC []])
  : ExceptT String IO thm).run
#eval FINSAT_MAX_HOMO

#eval phrase 18
unsafe def COMPACT_PROP : thm := keep "COMPACT_PROP" fun _ => (do
  prove ([[(!B. FINITE(B) /\ B SUBSET A
        ==> ?d. !r. r IN B ==> pholds(d) r)
   ==> ?d. !r. r IN A ==> pholds(d) r]])
   (STRIP_TAC THEN
    SUBGOAL_THEN ([[finsat(A)]]) (fun th => HolLight.tactic_of do
        let mth ← HolLight.MATCH_MP FINSAT_MAX th
        pure (MP_TAC mth)) THENL
     [REWRITE_TAC [finsat, psatisfiable] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[B:form->bool]]) MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC) THEN
    EXISTS_TAC [[\p:form. p IN B]] THEN
    SUBGOAL_THEN ([[!r. pholds (\p. p IN B) r <=> r IN B]])
     (fun th => ASM_MESON_TAC [th, SUBSET]) THEN
    MATCH_MP_TAC form_INDUCTION THEN REWRITE_TAC [pholds] THEN
    FIRST_ASSUM (fun th => HolLight.tactic_of do
        let mth ← HolLight.MATCH_MP FINSAT_MAX_CONSISTENT th
        pure (REWRITE_TAC [mth])) THEN
    FIRST_ASSUM (fun th => HolLight.tactic_of do
        let mth ← HolLight.MATCH_MP FINSAT_MAX_HOMO th
        pure (REWRITE_TAC [mth])) THEN
    SIMP_TAC [])
  : ExceptT String IO thm).run
#eval COMPACT_PROP

#eval phrase 19
unsafe def COMPACT_PROP_ALT : thm := keep "COMPACT_PROP_ALT" fun _ => (do
  prove ([[!A. (!d. ?p. p IN A /\ pholds d p)
       ==> ?B. FINITE(B) /\ B SUBSET A /\ (!d. ?p. p IN B /\ pholds d p)]])
   (HolLight.tactic_of do
     let compactContra ← (do
       let g ← HolLight.GSYM CONTRAPOS_THM
       HolLight.GEN_REWRITE_RULE HolCore.Lib.I [g] COMPACT_PROP)
     let phlds3 ← liftExcept (HolCore.Lib.el 3 (Session.CONJUNCTS PHOLDS))
     pure
      (GEN_TAC THEN STRIP_TAC THEN
       SUBGOAL_THEN ([[~(?d. !r. r IN {Not q | q IN A} ==> pholds(d) r)]])
       MP_TAC THENL
        [REWRITE_TAC [NOT_FORALL_THM, NOT_EXISTS_THM, NOT_IMP] THEN
         REWRITE_TAC [IN_ELIM_THM, Not_DEF] THEN ASM_MESON_TAC [pholds], ALL_TAC] THEN
       DISCH_THEN (MP_TAC o HolLight.MATCH_MP compactContra) THEN
       REWRITE_TAC [NOT_FORALL_THM, NOT_EXISTS_THM, NOT_IMP] THEN
       DISCH_THEN (X_CHOOSE_THEN ([[B:form->bool]]) STRIP_ASSUME_TAC) THEN
       EXISTS_TAC [[{r | Not r IN B}]] THEN ASM_REWRITE_TAC [] THEN
       CONJ_TAC THENL
        [MATCH_MP_TAC FINITE_IMAGE_INJ THEN
         ASM_REWRITE_TAC [IN_ELIM_THM] THEN
         REWRITE_TAC [Not_DEF, form_INJ],
         UNDISCH_TAC [[B SUBSET {Not q | q IN A}]] THEN
         REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN
         DISCH_TAC THEN CONJ_TAC THENL
          [GEN_TAC THEN DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN
           REWRITE_TAC [Not_DEF, form_INJ] THEN MESON_TAC [],
           ASM_MESON_TAC [phlds3]]]))
  : ExceptT String IO thm).run
#eval COMPACT_PROP_ALT

#eval phrase 20
unsafe def FINITE_DISJ_LEMMA : thm := keep "FINITE_DISJ_LEMMA" fun _ => (do
  prove ([[!A. FINITE(A) ==> ?ps. ALL (\p. p IN A) ps /\
                          !d. pholds(d) (ITLIST (||) ps False) <=>
                              ?p. p IN A /\ pholds d p]])
   (MATCH_MP_TAC FINITE_INDUCT THEN CONJ_TAC THENL
     [EXISTS_TAC [[[] :form list]] THEN REWRITE_TAC [ALL, ITLIST] THEN
      REWRITE_TAC [pholds, NOT_IN_EMPTY],
      X_GEN_TAC [[q:form]] THEN X_GEN_TAC [[s:form->bool]] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[ps:form list]]) STRIP_ASSUME_TAC) THEN
      EXISTS_TAC [[CONS (q:form) ps]] THEN REWRITE_TAC [ALL, ITLIST] THEN
      ASM_REWRITE_TAC [PHOLDS, IN_INSERT] THEN CONJ_TAC THENL
       [MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC [[\p:form. p IN s]] THEN
        ASM_REWRITE_TAC [] THEN MESON_TAC [],
        MESON_TAC []]])
  : ExceptT String IO thm).run
#eval FINITE_DISJ_LEMMA

#eval phrase 21
unsafe def COMPACT_DISJ : thm := keep "COMPACT_DISJ" fun _ => (do
  prove ([[!A. (!d. ?p. p IN A /\ pholds d p)
       ==> ?ps. ALL (\p. p IN A) ps /\
                !d. pholds(d) (ITLIST (||) ps False)]])
   (GEN_TAC THEN DISCH_THEN (MP_TAC o HolLight.MATCH_MP COMPACT_PROP_ALT) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[B:form->bool]]) MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[ps:form list]]) STRIP_ASSUME_TAC o
      HolLight.MATCH_MP FINITE_DISJ_LEMMA) THEN
    EXISTS_TAC [[ps:form list]] THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC [[\p:form. p IN B]] THEN
    ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [SUBSET])
  : ExceptT String IO thm).run
#eval COMPACT_DISJ

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py from the `#eval`s above. -/
unsafe def ensure : IO Unit := once "HolLogicArith.FolProp" do
  replay (
          HolLogicArith.Fol.ensure)
  replay (
          show IO Unit from do
      let _ ← IO.mkRef ZL
      let _ ← IO.mkRef poset
      let _ ← IO.mkRef fld
      let _ ← IO.mkRef chain
      pure ())
  replay (
          pholds)
  replay (
          PHOLDS)
  replay (
          parse_as_infix ("psatisfies", (10, "right")))
  replay (
          psatisfies)
  replay (
          psatisfiable)
  replay (
          PSATISFIABLE_MONO)
  replay (
          finsat)
  replay (
          FINSAT_MONO)
  replay (
          SATISFIABLE_MONO)
  replay (
          FINSAT_SATISFIABLE)
  replay (
          FINSAT_MAX)
  replay (
          FINSAT_EXTEND)
  replay (
          FINSAT_MAX_COMPLETE)
  replay (
          FINSAT_MAX_COMPLETE_STRONG)
  replay (
          FINSAT_DEDUCTION)
  replay (
          FINSAT_MAX_CONSISTENT)
  replay (
          FINSAT_MAX_HOMO)
  replay (
          COMPACT_PROP)
  replay (
          COMPACT_PROP_ALT)
  replay (
          FINITE_DISJ_LEMMA)
  replay (
          COMPACT_DISJ)
-- @@ENSURE END

end HolLogicArith.FolProp
