/- File: Hol100/RatCountable.lean
Translation of HOL Light's 100/ratcountable.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionLibrary.Card
open HolCore.Kernel Session HolLight.Syntax HolExamples
open SessionLibrary.Card
namespace Hol100.RatCountable

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)

/- ========================================================================= -/
/- Theorem 3: countability of rational numbers.                              -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Library/card.ml";;
#eval SessionLibrary.Card.ensureCard

#eval phrase 2
#eval Session.prioritize_real

/- ------------------------------------------------------------------------- -/
/- Definition of rational and countable.                                     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 3
def rational : thm := keep "rational" fun _ => new_definition
  [[rational(r) <=> ?p q. ~(q = 0) /\ (abs(r) = &p / &q)]]
#eval rational

#eval phrase 4
def countable : thm := keep "countable" fun _ => new_definition
  [[countable s <=> s <=_c (UNIV:num->bool)]]
#eval countable

/- ------------------------------------------------------------------------- -/
/- Proof of the main result.                                                 -/
/- ------------------------------------------------------------------------- -/

#eval phrase 5
def COUNTABLE_RATIONALS : thm := keep "COUNTABLE_RATIONALS" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[(abs(x) = a) ==> (x = a) \/ x = --a]])
  prove ([[countable { x:real | rational(x)}]])
   (REWRITE_TAC [countable] THEN TRANS_TAC CARD_LE_TRANS
     ([[{ x:real | ?p q. x = &p / &q } *_c (UNIV:num->bool)]]) THEN
    CONJ_TAC THENL
     [REWRITE_TAC [LE_C, EXISTS_PAIR_THM, mul_c] THEN
      EXISTS_TAC ([[\(x,b). if b = 0 then x else --x]]) THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC [IN_ELIM_THM, rational, IN_UNIV, PAIR_EQ] THEN
      MESON_TAC [h1],
      ALL_TAC] THEN
    MATCH_MP_TAC CARD_MUL_ABSORB_LE THEN REWRITE_TAC [num_INFINITE] THEN
    TRANS_TAC CARD_LE_TRANS ([[(UNIV *_c UNIV):num#num->bool]]) THEN CONJ_TAC THENL
     [REWRITE_TAC [LE_C, EXISTS_PAIR_THM, mul_c, IN_UNIV] THEN
      EXISTS_TAC ([[\(p,q). &p / &q]]) THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC [IN_ELIM_THM, rational] THEN MESON_TAC [],
      MESON_TAC [CARD_MUL_ABSORB_LE, CARD_LE_REFL, num_INFINITE]])
  : ExceptT String IO thm).run
#eval COUNTABLE_RATIONALS

/- ------------------------------------------------------------------------- -/
/- Maybe I should actually prove equality?                                   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 6
def denumerable : thm := keep "denumerable" fun _ => new_definition
  [[denumerable s <=> s =_c (UNIV:num->bool)]]
#eval denumerable

#eval phrase 7
def DENUMERABLE_RATIONALS : thm := keep "DENUMERABLE_RATIONALS" fun _ => (do
  prove ([[denumerable { x:real | rational(x)}]])
   (REWRITE_TAC [denumerable, (← HolLight.GSYM CARD_LE_ANTISYM)] THEN
    REWRITE_TAC [(← HolLight.GSYM countable), COUNTABLE_RATIONALS] THEN
    REWRITE_TAC [le_c] THEN EXISTS_TAC ([[&]]) THEN
    SIMP_TAC [IN_ELIM_THM, IN_UNIV, REAL_OF_NUM_EQ, rational] THEN
    X_GEN_TAC ([[p:num]]) THEN MAP_EVERY EXISTS_TAC [([[p:num]]), ([[1]])] THEN
    REWRITE_TAC [REAL_DIV_1, REAL_ABS_NUM, ARITH_EQ])
  : ExceptT String IO thm).run
#eval DENUMERABLE_RATIONALS

/- ------------------------------------------------------------------------- -/
/- Expand out the cardinal comparison definitions for explicitness.          -/
/- ------------------------------------------------------------------------- -/

#eval phrase 8
def DENUMERABLE_RATIONALS_EXPAND : thm := keep "DENUMERABLE_RATIONALS_EXPAND" fun _ => (do
  prove ([[?rat:num->real. (!n. rational(rat n)) /\
                   (!x. rational x ==> ?!n. x = rat n)]])
   (MP_TAC DENUMERABLE_RATIONALS THEN REWRITE_TAC [denumerable] THEN
    ONCE_REWRITE_TAC [CARD_EQ_SYM] THEN REWRITE_TAC [eq_c] THEN
    REWRITE_TAC [IN_UNIV, IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval DENUMERABLE_RATIONALS_EXPAND

end Hol100.RatCountable
