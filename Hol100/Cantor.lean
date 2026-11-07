/- File: Hol100/Cantor.lean
Translation of HOL Light's 100/cantor.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
open HolCore.Kernel Session HolLight.Syntax HolExamples
namespace Hol100.Cantor

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- ========================================================================= -/
/- Cantor's theorem.                                                         -/
/- ========================================================================= -/

/- ------------------------------------------------------------------------- -/
/- Ad hoc version for whole type.                                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 1
def CANTOR_THM_INJ : thm := keep "CANTOR_THM_INJ" fun _ => (do
  prove ([[~(?f:(A->bool)->A. (!x y. f(x) = f(y) ==> x = y))]])
   (REWRITE_TAC [INJECTIVE_LEFT_INVERSE, NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [([[f:(A->bool)->A]]), ([[g:A->(A->bool)]])] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[\x:A. ~(g x x)]])) THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval CANTOR_THM_INJ

#eval phrase 2
def CANTOR_THM_SURJ : thm := keep "CANTOR_THM_SURJ" fun _ => (do
  prove ([[~(?f:A->(A->bool). !s. ?x. f x = s)]])
   (REWRITE_TAC [SURJECTIVE_RIGHT_INVERSE, NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [([[g:A->(A->bool)]]), ([[f:(A->bool)->A]])] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[\x:A. ~(g x x)]])) THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval CANTOR_THM_SURJ

/- ------------------------------------------------------------------------- -/
/- Proper version for any set, in terms of cardinality operators.            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 3
def CANTOR : thm := keep "CANTOR" fun _ => (do
  prove ([[!s:A->bool. s <_c {t | t SUBSET s}]])
   (GEN_TAC THEN REWRITE_TAC [lt_c] THEN CONJ_TAC THENL
     [REWRITE_TAC [le_c] THEN EXISTS_TAC ([[(=):A->A->bool]]) THEN
      REWRITE_TAC [FUN_EQ_THM, IN_ELIM_THM, SUBSET, IN] THEN MESON_TAC [],
      REWRITE_TAC [LE_C, IN_ELIM_THM, SURJECTIVE_RIGHT_INVERSE] THEN
      REWRITE_TAC [NOT_EXISTS_THM] THEN X_GEN_TAC ([[g:A->(A->bool)]]) THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC ([[\x:A. s(x) /\ ~(g x x)]])) THEN
      REWRITE_TAC [SUBSET, IN, FUN_EQ_THM] THEN MESON_TAC []])
  : ExceptT String IO thm).run
#eval CANTOR

/- ------------------------------------------------------------------------- -/
/- More explicit "injective" version as in Paul Taylor's book.               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 4
def CANTOR_THM_INJ' : thm := keep "CANTOR_THM_INJ'" fun _ => (do
  prove ([[~(?f:(A->bool)->A. (!x y. f(x) = f(y) ==> x = y))]])
   (STRIP_TAC THEN
    ABBREV_TAC ([[(g:A->A->bool) = \a. { b | !s. f(s) = a ==> b IN s}]]) THEN
    MP_TAC (← HolLight.ISPEC ([[g:A->A->bool]])
     (← HolLight.REWRITE_RULE [NOT_EXISTS_THM] CANTOR_THM_SURJ)) THEN
    FIRST_X_ASSUM (SUBST_ALL_TAC o HolLight.SYM) THEN
    ASM_REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
    ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval CANTOR_THM_INJ'

/- ------------------------------------------------------------------------- -/
/- Another sequence of versions (Lawvere, Cantor, Taylor) taken from         -/
/- http://ncatlab.org/nlab/show/Cantor%27s+theorem.                          -/
/- ------------------------------------------------------------------------- -/

#eval phrase 5
def CANTOR_LAWVERE : thm := keep "CANTOR_LAWVERE" fun _ => (do
  prove ([[!h:A->(A->B).
        (!f:A->B. ?x:A. h(x) = f) ==> !n:B->B. ?x. n(x) = x]])
   (REPEAT STRIP_TAC THEN
    ABBREV_TAC ([[g:A->B = \a. (n:B->B) (h a a)]]) THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [FUN_EQ_THM]) THEN
    ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval CANTOR_LAWVERE

#eval phrase 6
-- let CANTOR = ... (rebinds CANTOR)
def CANTOR' : thm := keep "CANTOR'" fun _ => (do
  prove ([[!f:A->(A->bool). ~(!s. ?x. f x = s)]])
   (GEN_TAC THEN DISCH_THEN (MP_TAC o HolLight.MATCH_MP CANTOR_LAWVERE) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[(~)]])) THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval CANTOR'

#eval phrase 7
def CANTOR_TAYLOR : thm := keep "CANTOR_TAYLOR" fun _ => (do
  prove ([[!f:(A->bool)->A. ~(!x y. f(x) = f(y) ==> x = y)]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPEC ([[\a:A.  { b:A | !s. f(s) = a ==> b IN s}]])
     (← HolLight.REWRITE_RULE [NOT_EXISTS_THM] CANTOR')) THEN
    REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
    ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval CANTOR_TAYLOR

#eval phrase 8
def SURJECTIVE_COMPOSE : thm := keep "SURJECTIVE_COMPOSE" fun _ => (do
  prove ([[(!y. ?x. f(x) = y) /\ (!z. ?y. g(y) = z)
   ==> (!z. ?x. (g o f) x = z)]])
   (MESON_TAC [o_THM])
  : ExceptT String IO thm).run
#eval SURJECTIVE_COMPOSE

#eval phrase 9
def INJECTIVE_SURJECTIVE_PREIMAGE : thm := keep "INJECTIVE_SURJECTIVE_PREIMAGE" fun _ => (do
  prove ([[!f:A->B. (!x y. f(x) = f(y) ==> x = y) ==> !t. ?s. {x | f(x) IN s} = t]])
   (REPEAT STRIP_TAC THEN
    EXISTS_TAC ([[IMAGE (f:A->B) t]]) THEN
    REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_IMAGE] THEN
    ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval INJECTIVE_SURJECTIVE_PREIMAGE

#eval phrase 10
def CANTOR_JOHNSTONE : thm := keep "CANTOR_JOHNSTONE" fun _ => (do
  prove ([[!i:B->S f:B->S->bool.
        ~((!x y. i(x) = i(y) ==> x = y) /\ (!s. ?z. f(z) = s))]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPEC
     ([[(IMAGE (f:B->S->bool)) o (\s:S->bool. {x | i(x) IN s})]])
      (← HolLight.REWRITE_RULE [NOT_EXISTS_THM] CANTOR')) THEN
    REWRITE_TAC [] THEN MATCH_MP_TAC SURJECTIVE_COMPOSE THEN
    ASM_REWRITE_TAC [SURJECTIVE_IMAGE] THEN
    MATCH_MP_TAC INJECTIVE_SURJECTIVE_PREIMAGE THEN
    ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval CANTOR_JOHNSTONE

end Hol100.Cantor
