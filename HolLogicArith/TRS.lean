/- File: HolLogicArith/TRS.lean
Translation of HOL Light's Logic/trs.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolLogicArith.Given
open HolCore.Kernel Session HolLight.Syntax HolLogicArith
open scoped HolLight
open HolExamples.Reduct
open SessionLibrary.RSTC

namespace HolLogicArith.TRS

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

-- =========================================================================
-- Basic definitions for and theorems about term rewriting.
-- =========================================================================

#eval phrase 1
unsafe def TRS_triple : thm × thm × thm := keep "TRS_triple" fun _ =>
  newInductive
    [[(!i l r.
           (l,r) IN rws ==> TRS rws (termsubst i l) (termsubst i r)) /\
      (!s t f largs rargs.
           TRS rws s t ==> TRS rws (Fn f (APPEND largs (CONS s rargs)))
                                   (Fn f (APPEND largs (CONS t rargs))))]]
unsafe def TRS_RULES : thm := TRS_triple.1
unsafe def TRS_INDUCT : thm := TRS_triple.2.1
unsafe def TRS_CASES : thm := TRS_triple.2.2
#eval do IO.println TRS_RULES; IO.println TRS_INDUCT; IO.println TRS_CASES

-- -------------------------------------------------------------------------
-- Nice general result justfying both deletion and right-simplification.
-- -------------------------------------------------------------------------

#eval phrase 2
unsafe def CONVERGENT_MODIFY_LEMMA : thm := keep "CONVERGENT_MODIFY_LEMMA" fun _ => (do
  prove
   ([[!R S. SN R /\
         CR(RTC R) /\
         (!x y. S x y ==> TC R x y) /\
         (!x y. R x y ==> ?y'. S x y')
         ==> !y:A. NORMAL(R) y ==> !x. RTC R x y ==> RTC S x y]])
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [(← HolLight.GSYM SN_TC)] THEN
    REWRITE_TAC [SN_NOETHERIAN] THEN STRIP_TAC THEN
    GEN_TAC THEN REWRITE_TAC [NORMAL, NOT_EXISTS_THM] THEN DISCH_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN X_GEN_TAC [[x:A]] THEN DISCH_TAC THEN
    HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [RTC_CASES_R] THEN
    DISCH_THEN (DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THEN
    REWRITE_TAC [RTC_REFL] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[u:A]]) STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC [[!x:A y:A. R x y ==> (?y':A. S x y')]] THEN
    DISCH_THEN (MP_TAC oTIO HolLight.SPECL [ [[x:A]], [[u:A]] ]) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC ([[v:A]])) THEN
    FIRST_X_ASSUM (MP_TAC oTIO HolLight.SPECL [ [[x:A]], [[v:A]] ]) THEN ASM_REWRITE_TAC [] THEN
    DISCH_TAC THEN FIRST_ASSUM (MP_TAC oTIO HolLight.GEN_REWRITE_RULE HolCore.Lib.I [CR]) THEN
    DISCH_THEN (MP_TAC oTIO HolLight.SPECL [ [[x:A]], [[y:A]], [[v:A]] ]) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [ASM_MESON_TAC [RTC_CASES_R, TC_RTC_CASES_R], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[z:A]]) STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN ([[z:A = y]]) SUBST_ALL_TAC THEN ASM_MESON_TAC [RTC_CASES_R])
  : ExceptT String IO thm).run
#eval CONVERGENT_MODIFY_LEMMA

#eval phrase 3
unsafe def CONVERGENT_MODIFY : thm := keep "CONVERGENT_MODIFY" fun _ => (do
  prove
   ([[!R S. SN R /\
         CR(RTC R) /\
         (!x:A y. S x y ==> TC R x y) /\
         (!x:A y. R x y ==> ?y'. S x y')
         ==> SN(S) /\ CR(RTC S)]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[a /\ (a ==> b) ==> a /\ b]])) THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC [SN_WF] THEN MATCH_MP_TAC WF_SUBSET THEN
      EXISTS_TAC [[INV(TC(R:A->A->bool))]] THEN ASM_REWRITE_TAC [INV] THEN
      REWRITE_TAC [(← HolLight.GSYM TC_INV), WF_TC] THEN ASM_REWRITE_TAC [(← HolLight.GSYM SN_WF)],
      ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC NEWMAN_LEMMA THEN ASM_REWRITE_TAC [WCR] THEN
    MAP_EVERY X_GEN_TAC [ [[x:A]], [[y1:A]], [[y2:A]] ] THEN STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC oTIO HolLight.GEN_REWRITE_RULE HolCore.Lib.I [CR]) THEN
    DISCH_THEN (MP_TAC oTIO HolLight.SPECL [ [[x:A]], [[y1:A]], [[y2:A]] ]) THEN ANTS_TAC THENL
     [ASM_MESON_TAC [RTC_INC_TC], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[z0:A]]) STRIP_ASSUME_TAC) THEN
    MP_TAC (← HolLight.MATCH_MP SN_WN (← HolLight.ASSUME [[SN(R:A->A->bool)]])) THEN
    REWRITE_TAC [WN] THEN DISCH_THEN (MP_TAC oTIO HolLight.SPEC [[z0:A]]) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[z:A]]) STRIP_ASSUME_TAC) THEN
    MP_TAC (← HolLight.SPECL [ [[R:A->A->bool]], [[S:A->A->bool]] ] CONVERGENT_MODIFY_LEMMA) THEN
    ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [RTC_TRANS])
  : ExceptT String IO thm).run
#eval CONVERGENT_MODIFY

#eval phrase 4
unsafe def EQUIVALENT_JOINABLE_MODIFY : thm := keep "EQUIVALENT_JOINABLE_MODIFY" fun _ => (do
  prove
   ([[!R S. SN R /\
         CR(RTC R) /\
         (!x y. S x y ==> TC R x y) /\
         (!x y. R x y ==> ?y'. S x y')
         ==> (!x:A y. JOINABLE S x y = JOINABLE R x y)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [JOINABLE] THEN EQ_TAC THEN
    DISCH_THEN (X_CHOOSE_THEN ([[z:A]]) STRIP_ASSUME_TAC) THENL
     [SUBGOAL_THEN ([[!x:A y. RTC S x y ==> RTC R x y]])
       (fun th => ASM_MESON_TAC [th]) THEN
      REWRITE_TAC [RTC, RC_CASES] THEN
      SUBGOAL_THEN ([[!x:A y. TC S x y ==> TC R x y]])
       (fun th => ASM_MESON_TAC [th]) THEN
      HolLight.GEN_REWRITE_TAC (HolCore.Lib.funpow 2 HolLight.BINDER_CONV o HolLight.RAND_CONV o HolLight.ONCE_DEPTH_CONV)
       [(← HolLight.GSYM TC_IDEMP)] THEN
      MATCH_MP_TAC TC_MONO THEN ASM_REWRITE_TAC [],
      FIRST_ASSUM (MP_TAC oTIO HolLight.MATCH_MP SN_WN) THEN REWRITE_TAC [WN] THEN
      DISCH_THEN (MP_TAC oTIO HolLight.SPEC [[z:A]]) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[w:A]]) STRIP_ASSUME_TAC) THEN
      MP_TAC (← HolLight.SPECL [ [[R:A->A->bool]], [[S:A->A->bool]] ] CONVERGENT_MODIFY_LEMMA) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (MP_TAC oTIO HolLight.SPEC [[w:A]]) THEN ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC [RTC_TRANS]])
  : ExceptT String IO thm).run
#eval EQUIVALENT_JOINABLE_MODIFY

#eval phrase 5
unsafe def EQUIVALENT_RSTC_MODIFY : thm := keep "EQUIVALENT_RSTC_MODIFY" fun _ => (do
  prove
   ([[!R S. SN R /\
         CR(RTC R) /\
         (!x y. S x y ==> TC R x y) /\
         (!x y. R x y ==> ?y'. S x y')
         ==> (!x:A y. RSTC S x y = RSTC R x y)]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [ [[R:A->A->bool]], [[S:A->A->bool]] ] CONVERGENT_MODIFY) THEN
    ASM_REWRITE_TAC [] THEN
    MP_TAC (← HolLight.SPECL [ [[R:A->A->bool]], [[S:A->A->bool]] ]
                 EQUIVALENT_JOINABLE_MODIFY) THEN
    ASM_SIMP_TAC [CR_RSTC_JOINABLE] THEN
    ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [])
  : ExceptT String IO thm).run
#eval EQUIVALENT_RSTC_MODIFY

#eval phrase 6
unsafe def EQUIVALENT_MODIFY : thm := keep "EQUIVALENT_MODIFY" fun _ => (do
  prove
   ([[!R S. SN R /\
         CR(RTC R) /\
         (!x y. S x y ==> TC R x y) /\
         (!x y. R x y ==> ?y'. S x y')
         ==> SN(S) /\ CR(RTC S) /\ (!x:A y. RSTC S x y = RSTC R x y)]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC [CONJ_ASSOC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONVERGENT_MODIFY THEN EXISTS_TAC [[R:A->A->bool]],
      MATCH_MP_TAC EQUIVALENT_RSTC_MODIFY] THEN
    ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval EQUIVALENT_MODIFY

-- -------------------------------------------------------------------------
-- Special case of right simplification of rules.
-- -------------------------------------------------------------------------

#eval phrase 7
unsafe def EQUIVALENT_MODIFY_RIGHT : thm := keep "EQUIVALENT_MODIFY_RIGHT" fun _ => (do
  prove
   ([[!R S S'.
        SN(\x y. R x y \/ S x y) /\
        CR(RTC(\x y. R x y \/ S x y)) /\
        (!s:A t. S s t ==> ?t'. S' s t') /\
        (!s t. S' s t ==> ?u. S s u /\ RTC (\x y. R x y \/ S x y) u t)
        ==> SN(\x y. R x y \/ S' x y) /\
            CR(RTC(\x y. R x y \/ S' x y)) /\
            (!x y. RSTC(\x y. R x y \/ S' x y) x y =
                   RSTC(\x y. R x y \/ S x y) x y)]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC EQUIVALENT_MODIFY THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THEN
    MAP_EVERY X_GEN_TAC [ [[x:A]], [[y:A]] ] THEN STRIP_TAC THENL
     [MATCH_MP_TAC TC_INC THEN ASM_REWRITE_TAC [],
      FIRST_ASSUM (MP_TAC oTIO (HolCore.Lib.C HolLight.MATCH_MP (← HolLight.ASSUME [[(S':A->A->bool) x y]]))) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[u:A]]) STRIP_ASSUME_TAC) THEN
      HolLight.GEN_REWRITE_TAC HolCore.Lib.I [TC_RTC_CASES_R] THEN
      EXISTS_TAC [[u:A]] THEN ASM_REWRITE_TAC [],
      ASM_MESON_TAC [],
      ASM_MESON_TAC []])
  : ExceptT String IO thm).run
#eval EQUIVALENT_MODIFY_RIGHT

-- -------------------------------------------------------------------------
-- And of deletion of joinable ones.
-- -------------------------------------------------------------------------

#eval phrase 8
unsafe def CONVERGENT_DELETE_LEFT : thm := keep "CONVERGENT_DELETE_LEFT" fun _ => (do
  prove
   ([[!R S. SN(\x y. R x y \/ S x y) /\
         CR(RTC(\x y. R x y \/ S x y)) /\
         (!x:A y. S x y ==> ?z. R x z)
         ==> SN(R) /\ CR(RTC R) /\
             (!x y. RSTC(R) x y = RSTC(\x y. R x y \/ S x y) x y)]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC EQUIVALENT_MODIFY THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THEN
    MAP_EVERY X_GEN_TAC [ [[x:A]], [[y:A]] ] THEN DISCH_TAC THEN
    ASM_SIMP_TAC [TC_INC] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval CONVERGENT_DELETE_LEFT

-- -------------------------------------------------------------------------
-- The case of left-simplification is harder; this lemma isn't enough.
-- But given the deletion result above, we don't need this anyway!
-- -------------------------------------------------------------------------

#eval phrase 9
unsafe def CONVERGENT_MODIFY_LEMMA_2 : thm := keep "CONVERGENT_MODIFY_LEMMA_2" fun _ => (do
  prove
   ([[!R S S' t.
        SN(\x y. R x y \/ S x y \/ S' x y) /\
        CR(RTC(\x y. R x y \/ S x y)) /\
        (!s t. S s t
               ==> ?s' t'. RTC R s s' /\ RTC R t t' /\
                           (S' s' t' \/ S' t' s')) /\
        NORMAL(\x y. R x y \/ S x y) t
        ==> !s:A. RTC (\x y. R x y \/ S x y) s t
                  ==> RTC (\x y. R x y \/ S' x y) s t]])
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [(← HolLight.GSYM SN_TC)] THEN
    REWRITE_TAC [SN_NOETHERIAN] THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    X_GEN_TAC [[s:A]] THEN DISCH_TAC THEN
    HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [RTC_CASES_R] THEN
    DISCH_THEN (DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THEN
    REWRITE_TAC [RTC_REFL] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[u:A]]) STRIP_ASSUME_TAC) THENL
     [FIRST_ASSUM (fun th => HolLight.tactic_of do
        let sp ← HolLight.SPEC ([[u:A]]) th
        pure (MP_TAC sp THEN ANTS_TAC)) THENL
       [ONCE_REWRITE_TAC [TC_CASES_R] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ONCE_REWRITE_TAC [RTC_CASES_R] THEN
      DISJ2_TAC THEN EXISTS_TAC [[u:A]] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC oTIO HolLight.SPECL [ [[s:A]], [[u:A]] ]) THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[s':A]], [[u':A]] ] THEN STRIP_TAC THENL
     [FIRST_ASSUM (MP_TAC oTIO HolLight.SPEC [[u':A]]) THEN ANTS_TAC THENL
       [ONCE_REWRITE_TAC [TC_RTC_CASES_R] THEN EXISTS_TAC [[u:A]] THEN
        ASM_REWRITE_TAC [] THEN UNDISCH_TAC [[RTC R (u:A) u']] THEN
        MAP_EVERY (fun s => SPEC_TAC (s, s)) [ [[u':A]], [[u:A]] ] THEN
        MATCH_MP_TAC RTC_MONO THEN SIMP_TAC [], ALL_TAC] THEN
      FIRST_ASSUM (MP_TAC oTIO HolLight.GEN_REWRITE_RULE HolCore.Lib.I [CR]) THEN
      DISCH_THEN (MP_TAC oTIO HolLight.SPECL [ [[s:A]], [[u':A]], [[t:A]] ]) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [ONCE_REWRITE_TAC [RTC_CASES_R] THEN DISJ2_TAC THEN EXISTS_TAC [[u:A]] THEN
          ASM_REWRITE_TAC [] THEN
          UNDISCH_TAC [[RTC R (u:A) u']] THEN
          MAP_EVERY (fun s => SPEC_TAC (s, s)) [ [[u':A]], [[u:A]] ] THEN
          MATCH_MP_TAC RTC_MONO THEN SIMP_TAC [],
          ALL_TAC] THEN
        ONCE_REWRITE_TAC [RTC_CASES_R] THEN DISJ2_TAC THEN EXISTS_TAC [[u:A]] THEN
        ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[z:A]]) STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN ([[z:A = t]]) SUBST_ALL_TAC THENL
       [UNDISCH_TAC [[RTC (\x y. R x y \/ S x y) t (z:A)]] THEN
        ONCE_REWRITE_TAC [RTC_CASES_R] THEN
        ASM_CASES_TAC [[z:A = t]] THEN ASM_REWRITE_TAC [] THEN
        FIRST_ASSUM (MP_TAC oTIO HolLight.GEN_REWRITE_RULE HolCore.Lib.I [NORMAL]) THEN
        REWRITE_TAC [] THEN MESON_TAC [], ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
      ONCE_REWRITE_TAC [RTC_CASES] THEN DISJ2_TAC THEN
      EXISTS_TAC [[u':A]] THEN ASM_REWRITE_TAC [] THEN
      ONCE_REWRITE_TAC [RTC_CASES_L] THEN DISJ2_TAC THEN
      EXISTS_TAC [[s':A]] THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC [[RTC R (s:A) s']] THEN
      MAP_EVERY (fun s => SPEC_TAC (s, s)) [ [[s':A]], [[s:A]] ] THEN
      MATCH_MP_TAC RTC_MONO THEN SIMP_TAC [], ALL_TAC] THEN
    ASM_CASES_TAC [[s':A = s]] THENL
     [RULE_ASSUM_TAC (HolLight.REWRITE_RULE [(← HolLight.GSYM SN_NOETHERIAN), SN_WF]) THEN
      FIRST_ASSUM (MP_TAC oTIO HolLight.MATCH_MP WF_REFL) THEN
      DISCH_THEN (MP_TAC oTIO HolLight.SPEC [[s:A]]) THEN REWRITE_TAC [INV] THEN
      MATCH_MP_TAC (← ExceptT.mk (TAUT [[a ==> ~a ==> b]])) THEN
      ONCE_REWRITE_TAC [TC_RTC_CASES_R] THEN EXISTS_TAC [[u:A]] THEN
      ASM_REWRITE_TAC [] THEN
      ONCE_REWRITE_TAC [RTC_CASES_L] THEN DISJ2_TAC THEN EXISTS_TAC [[u':A]] THEN
      UNDISCH_THEN ([[s':A = s]]) SUBST_ALL_TAC THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC [[RTC R (u:A) u']] THEN
      MAP_EVERY (fun s => SPEC_TAC (s, s)) [ [[u':A]], [[u:A]] ] THEN
      MATCH_MP_TAC RTC_MONO THEN SIMP_TAC [], ALL_TAC] THEN
    FIRST_ASSUM (MP_TAC oTIO HolLight.SPEC [[s':A]]) THEN ANTS_TAC THENL
     [MATCH_MP_TAC RTC_NE_IMP_TC THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC [[RTC R (s:A) s']] THEN
      MAP_EVERY (fun s => SPEC_TAC (s, s)) [ [[s':A]], [[s:A]] ] THEN
      MATCH_MP_TAC RTC_MONO THEN SIMP_TAC [], ALL_TAC] THEN
    FIRST_ASSUM (MP_TAC oTIO HolLight.GEN_REWRITE_RULE HolCore.Lib.I [CR]) THEN
    DISCH_THEN (MP_TAC oTIO HolLight.SPECL [ [[s:A]], [[s':A]], [[t:A]] ]) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC [[RTC R (s:A) s']] THEN
        MAP_EVERY (fun s => SPEC_TAC (s, s)) [ [[s':A]], [[s:A]] ] THEN
        MATCH_MP_TAC RTC_MONO THEN SIMP_TAC [],
        ONCE_REWRITE_TAC [RTC_CASES_R] THEN DISJ2_TAC THEN EXISTS_TAC [[u:A]] THEN
        ASM_REWRITE_TAC []],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[z:A]]) STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN ([[z:A = t]]) SUBST_ALL_TAC THENL
     [UNDISCH_TAC [[RTC (\x y. R x y \/ S x y) t (z:A)]] THEN
      ONCE_REWRITE_TAC [RTC_CASES_R] THEN
      ASM_CASES_TAC [[z:A = t]] THEN ASM_REWRITE_TAC [] THEN
      FIRST_ASSUM (MP_TAC oTIO HolLight.GEN_REWRITE_RULE HolCore.Lib.I [NORMAL]) THEN
      REWRITE_TAC [] THEN MESON_TAC [], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC [RTC_CASES] THEN DISJ2_TAC THEN
    EXISTS_TAC [[s':A]] THEN ASM_REWRITE_TAC [] THEN
    UNDISCH_TAC [[RTC R (s:A) s']] THEN
    MAP_EVERY (fun s => SPEC_TAC (s, s)) [ [[s':A]], [[s:A]] ] THEN
    MATCH_MP_TAC RTC_MONO THEN SIMP_TAC [])
  : ExceptT String IO thm).run
#eval CONVERGENT_MODIFY_LEMMA_2

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py from the `#eval`s above. -/
unsafe def ensure : IO Unit := once "HolLogicArith.TRS" do
  replay (
          HolLogicArith.Given.ensure)
  replay (
          do IO.println TRS_RULES; IO.println TRS_INDUCT; IO.println TRS_CASES)
  replay (
          CONVERGENT_MODIFY_LEMMA)
  replay (
          CONVERGENT_MODIFY)
  replay (
          EQUIVALENT_JOINABLE_MODIFY)
  replay (
          EQUIVALENT_RSTC_MODIFY)
  replay (
          EQUIVALENT_MODIFY)
  replay (
          EQUIVALENT_MODIFY_RIGHT)
  replay (
          CONVERGENT_DELETE_LEFT)
  replay (
          CONVERGENT_MODIFY_LEMMA_2)
-- @@ENSURE END

end HolLogicArith.TRS
