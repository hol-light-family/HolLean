/- File: Hol100/Lagrange.lean
Translation of HOL Light's 100/lagrange.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionLibrary.Prime
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Prime
namespace Hol100.Lagrange

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)

/- ========================================================================= -/
/- Very trivial group theory, just to reach Lagrange theorem.                -/
/- NB: "Library/grouptheory.ml" has a more serious development of groups.    -/
/- ========================================================================= -/

#eval phrase 1
-- loadt "Library/prime.ml";;
#eval SessionLibrary.Prime.ensurePrime

/- ------------------------------------------------------------------------- -/
/- Definition of what a group is.                                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 2
def group : thm := keep "group" fun _ => new_definition
 [[group(g,( ** ),i,(e:A)) <=>
    (e IN g) /\ (!x. x IN g ==> i(x) IN g) /\
    (!x y. x IN g /\ y IN g ==> (x ** y) IN g) /\
    (!x y z. x IN g /\ y IN g /\ z IN g ==> (x ** (y ** z) = (x ** y) ** z)) /\
    (!x. x IN g ==> (x ** e = x) /\ (e ** x = x)) /\
    (!x. x IN g ==> (x ** i(x) = e) /\ (i(x) ** x = e))]]
#eval group

/- ------------------------------------------------------------------------- -/
/- Notion of a subgroup.                                                     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 3
def subgroup : thm := keep "subgroup" fun _ => new_definition
 [[subgroup h (g,( ** ),i,(e:A)) <=> h SUBSET g /\ group(h,( ** ),i,e)]]
#eval subgroup

/- ------------------------------------------------------------------------- -/
/- Lagrange theorem, introducing the coset representatives.                  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 4
def GROUP_LAGRANGE_COSETS : thm := keep "GROUP_LAGRANGE_COSETS" fun _ => (do
  let h4 ← tt (← ExceptT.mk [[(a ==> b) /\ a ==> a /\ b]])
  let h3 ← tt (← ExceptT.mk [[(c ==> a /\ b ==> d) ==> a /\ b /\ c ==> d]])
  let h2 ← tt (← ExceptT.mk [[a /\ (a ==> b) ==> b /\ a]])
  let h1 ← tt (← ExceptT.mk [[(a /\ b) /\ (a /\ c) <=> a /\ b /\ c]])
  prove ([[!g h ( ** ) i e.
        group (g,( ** ),i,e:A) /\ subgroup h (g,( ** ),i,e) /\ FINITE g
        ==> ?q. (CARD(g) = CARD(q) * CARD(h)) /\
                (!b. b IN g ==> ?a x. a IN q /\ x IN h /\ (b = a ** x))]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [group, subgroup, SUBSET] THEN STRIP_TAC THEN
    ABBREV_TAC ([[coset = \a:A. {b:A | b IN g /\ (?x:A. x IN h /\ (b = a ** x))}]]) THEN
    SUBGOAL_THEN ([[!a:A. a IN g ==> a IN (coset a)]]) ASSUME_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "coset" THEN
      ASM_SIMP_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[FINITE(h:A->bool)]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [FINITE_SUBSET, SUBSET], ALL_TAC] THEN
    SUBGOAL_THEN ([[!a. FINITE((coset:A->A->bool) a)]]) ASSUME_TAC THENL
     [GEN_TAC THEN EXPAND_TAC "coset" THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC ([[g:A->bool]]) THEN
      ASM_SIMP_TAC [IN_ELIM_THM, SUBSET],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!a:A x:A y. a IN g /\ x IN g /\ y IN g /\ ((a ** x) :A = a ** y)
                ==> (x = y)]]) ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN ([[(e:A ** x:A):A = e ** y]]) (fun th => ASM_MESON_TAC [th]) THEN
      SUBGOAL_THEN ([[((i(a):A ** a:A) ** x) = (i(a) ** a) ** y]]) (fun th => ASM_MESON_TAC [th]) THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!a:A. a IN g ==> (CARD(coset a :A->bool) = CARD(h:A->bool))]]) ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN ([[(coset:A->A->bool) (a:A) = IMAGE (\x. a ** x) (h:A->bool)]]) SUBST1_TAC THENL
       [EXPAND_TAC "coset" THEN
        REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_IMAGE, IN_ELIM_THM] THEN
        ASM_MESON_TAC [],
        ALL_TAC] THEN
      MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!x:A y. x IN g /\ y IN g ==> (i(x ** y) = i(y) ** i(x))]]) ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC ([[(x:A ** y:A) :A]]) THEN ASM_SIMP_TAC [] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC ([[(x:A ** (y ** i(y))) ** i(x)]]) THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!x:A. x IN g ==> (i(i(x)) = x)]]) ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC ([[(i:A->A)(x)]]) THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!a b. a IN g /\ b IN g
          ==> ((coset:A->A->bool) a = coset b) \/
              ((coset a) INTER (coset b) = {})]]) ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      ASM_CASES_TAC ([[((i:A->A)(b) ** a:A) IN (h:A->bool)]]) THENL
       [DISJ1_TAC THEN EXPAND_TAC "coset" THEN
        REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
        GEN_TAC THEN AP_TERM_TAC THEN
        SUBGOAL_THEN ([[!x:A. x IN h ==> (b ** (i(b) ** a:A) ** x = a ** x) /\
                         (a ** i(i(b) ** a) ** x = b ** x)]]) (fun th => EQ_TAC THEN REPEAT STRIP_TAC THEN
            ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [th]) THEN
        ASM_SIMP_TAC [],
        ALL_TAC] THEN
      DISJ2_TAC THEN REWRITE_TAC [EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN
      X_GEN_TAC ([[x:A]]) THEN EXPAND_TAC "coset" THEN REWRITE_TAC [IN_ELIM_THM] THEN
      REWRITE_TAC [h1] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN ([[y:A]]) STRIP_ASSUME_TAC) (X_CHOOSE_THEN ([[z:A]]) STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN ([[(i(b:A) ** a ** y):A = i(b) ** b ** z]]) ASSUME_TAC THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN ([[(i(b:A) ** a:A ** y):A = e ** z]]) ASSUME_TAC THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN ([[(i(b:A) ** a:A ** y):A = z]]) ASSUME_TAC THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN ([[((i(b:A) ** a:A) ** y):A = z]]) ASSUME_TAC THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN ([[((i(b:A) ** a:A) ** y) ** i(y) = z ** i(y)]]) ASSUME_TAC THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN ([[(i(b:A) ** a:A) ** (y ** i(y)) = z ** i(y)]]) ASSUME_TAC THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN ([[(i(b:A) ** a:A) ** e = z ** i(y)]]) ASSUME_TAC THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN ([[(i(b:A) ** a:A):A = z ** i(y)]]) ASSUME_TAC THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    EXISTS_TAC ([[{c:A | ?a:A. a IN g /\ (c = (@)(coset a))}]]) THEN
    MATCH_MP_TAC h2 THEN CONJ_TAC THENL
     [X_GEN_TAC ([[b:A]]) THEN DISCH_TAC THEN
      EXISTS_TAC ([[(@)((coset:A->A->bool) b)]]) THEN
      REWRITE_TAC [RIGHT_EXISTS_AND_THM] THEN CONJ_TAC THENL
       [REWRITE_TAC [IN_ELIM_THM] THEN EXISTS_TAC ([[b:A]]) THEN
        ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[(@)((coset:A->A->bool) b) IN (coset b)]]) MP_TAC THENL
       [REWRITE_TAC [IN] THEN MATCH_MP_TAC SELECT_AX THEN
        ASM_MESON_TAC [IN],
        ALL_TAC] THEN
      FIRST_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV o HolLight.RATOR_CONV) [(← HolLight.SYM th)])) THEN
      REWRITE_TAC [] THEN
      ABBREV_TAC ([[C = (@)((coset:A->A->bool) b)]]) THEN
      REWRITE_TAC [IN_ELIM_THM] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN ([[c:A]]) STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC ([[(i:A->A)(c)]]) THEN ASM_SIMP_TAC [] THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    ABBREV_TAC ([[q = {c:A | ?a:A. a IN g /\ (c = (@)(coset a))}]]) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN ([[!a:A b. a IN g /\ b IN g /\ a IN coset(b) ==> b IN coset(a)]]) ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN EXPAND_TAC "coset" THEN
      REWRITE_TAC [IN_ELIM_THM] THEN REWRITE_TAC [(← HolLight.GSYM CONJ_ASSOC)] THEN
      REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[c:A]]) STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC [] THEN EXISTS_TAC ([[(i:A->A) c]]) THEN
      ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!a:A b c. a IN coset(b) /\ b IN coset(c) /\ c IN g ==> a IN coset(c)]]) ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN EXPAND_TAC "coset" THEN
      REWRITE_TAC [IN_ELIM_THM] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!a:A b:A. a IN coset(b) ==> a IN g]]) ASSUME_TAC THENL
     [EXPAND_TAC "coset" THEN REWRITE_TAC [IN_ELIM_THM] THEN MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!a:A b. a IN coset(b) /\ b IN g ==> (coset a = coset b)]]) ASSUME_TAC THENL
     [REWRITE_TAC [EXTENSION] THEN
      MAP_EVERY UNDISCH_TAC [([[!a:A b:A. a IN coset(b) ==> a IN g]]),
        ([[!a:A b c. a IN coset(b) /\ b IN coset(c) /\ c IN g ==> a IN coset(c)]]),
        ([[!a:A b. a IN g /\ b IN g /\ a IN coset(b) ==> b IN coset(a)]])] THEN
      MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!a:A. a IN g ==> (@)(coset a):A IN (coset a)]]) ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN UNDISCH_TAC ([[!a:A. a IN g ==> a IN coset a]]) THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC ([[a:A]])) THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [IN, SELECT_AX],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!a:A. a IN q ==> a IN g]]) ASSUME_TAC THENL
     [GEN_TAC THEN EXPAND_TAC "q" THEN REWRITE_TAC [IN_ELIM_THM] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!a:A x:A a' x'. a IN q /\ a' IN q /\ x IN h /\ x' IN h /\
                    ((a' ** x') :A = a ** x) ==> (a' = a) /\ (x' = x)]]) ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN EXPAND_TAC "q" THEN REWRITE_TAC [IN_ELIM_THM] THEN
      MATCH_MP_TAC h3 THEN
      STRIP_TAC THEN
      DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN ([[a1:A]]) STRIP_ASSUME_TAC) (X_CHOOSE_THEN ([[a2:A]]) STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN ([[a:A IN g /\ a' IN g]]) STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN
      MATCH_MP_TAC h4 THEN
      CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN ([[((coset:A->A->bool) a1 = coset a) /\ (coset a2 = coset a')]]) MP_TAC THENL
       [CONJ_TAC THEN CONV_TAC HolLight.SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_SIMP_TAC [],
        ALL_TAC] THEN
      DISCH_THEN (CONJUNCTS_THEN SUBST_ALL_TAC) THEN
      ONCE_ASM_REWRITE_TAC [] THEN AP_TERM_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
      EXPAND_TAC "coset" THEN REWRITE_TAC [IN_ELIM_THM] THEN
      ASM_REWRITE_TAC [] THEN EXISTS_TAC ([[(x:A ** (i:A->A)(x')):A]]) THEN
      ASM_SIMP_TAC [] THEN UNDISCH_TAC ([[(a':A ** x':A):A = a ** x]]) THEN
      DISCH_THEN (MP_TAC o HolCore.Lib.C HolLight.AP_THM ([[(i:A->A) x']]) o HolLight.AP_TERM ([[(**):A->A->A]])) THEN
      DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[g = IMAGE (\(a:A,x:A). (a ** x):A) {(a,x) | a IN q /\ x IN h}]]) SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN
      REWRITE_TAC [EXISTS_PAIR_THM] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC [PAIR_EQ] THEN
      REWRITE_TAC [CONJ_ASSOC, (← HolLight.ONCE_REWRITE_RULE [CONJ_SYM] UNWIND_THM1)] THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC ([[CARD {(a:A,x:A) | a IN q /\ x IN h}]]) THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
       [REWRITE_TAC [FORALL_PAIR_THM, IN_ELIM_THM] THEN
        CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
        REWRITE_TAC [PAIR_EQ] THEN REPEAT GEN_TAC THEN
        REPEAT (DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
        ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [],
        ALL_TAC] THEN
      MATCH_MP_TAC FINITE_PRODUCT THEN CONJ_TAC THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC ([[g:A->bool]]) THEN
      ASM_REWRITE_TAC [SUBSET],
      ALL_TAC] THEN
    MATCH_MP_TAC CARD_PRODUCT THEN CONJ_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC ([[g:A->bool]]) THEN
    ASM_REWRITE_TAC [SUBSET])
  : ExceptT String IO thm).run
#eval GROUP_LAGRANGE_COSETS

/- ------------------------------------------------------------------------- -/
/- Traditional statement is only part of this.                               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 5
def GROUP_LAGRANGE : thm := keep "GROUP_LAGRANGE" fun _ => (do
  prove ([[!g h ( ** ) i e.
        group (g,( ** ),i,e:A) /\ subgroup h (g,( ** ),i,e) /\ FINITE g
        ==> (CARD h) divides (CARD g)]])
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o HolLight.MATCH_MP GROUP_LAGRANGE_COSETS) THEN
    MESON_TAC [DIVIDES_LMUL, DIVIDES_REFL])
  : ExceptT String IO thm).run
#eval GROUP_LAGRANGE

end Hol100.Lagrange
