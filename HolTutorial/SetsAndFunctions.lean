/- File: HolTutorial/SetsAndFunctions.lean
Translation of HOL Light's Tutorial/Sets_and_functions.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/

import HolTutorial.Common

open HolCore.Kernel Session HolLight.Syntax HolTutorial

namespace HolTutorial.SetsAndFunctions

/- Helpers: the session's `prove` and `MESON` lifted into `ExceptT String IO`,
   so a `let lemma = MESON[] `...`` inside a proof reads as the OCaml does. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private unsafe def meson (ths : List thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (Session.MESON ths tm)

#eval phrase 1
unsafe def SURJECTIVE_IFF_RIGHT_INVERSE : thm := keep "SURJECTIVE_IFF_RIGHT_INVERSE" fun _ => (do
  prove ([[(!y. ?x. g x = y) <=> (?f. g o f = I)]])
   (REWRITE_TAC [FUN_EQ_THM, o_DEF, I_DEF] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval SURJECTIVE_IFF_RIGHT_INVERSE

#eval phrase 2
unsafe def INJECTIVE_IFF_LEFT_INVERSE : thm := keep "INJECTIVE_IFF_LEFT_INVERSE" fun _ => (do
  let lemma ← meson []
    [[(!x x'. f x = f x' ==> x = x') <=> (!y:B. ?u:A. !x. f x = y ==> u = x)]]
  prove ([[(!x y. f x = f y ==> x = y) <=> (?g. g o f = I)]])
   (REWRITE_TAC [lemma, FUN_EQ_THM, o_DEF, I_DEF] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval INJECTIVE_IFF_LEFT_INVERSE

#eval phrase 3
unsafe def cantor : thm := keep "cantor" fun _ =>
  new_definition
   [[cantor(x,y) = ((x + y) EXP 2 + 3 * x + y) DIV 2]]
#eval cantor

-- Phrases 4 onwards (CANTOR_LEMMA via SOS, and the rest) wait for the file
-- named in tools/tutorialdiff/Sets_and_functions/stop: Examples/sos.ml is not
-- translated.

end HolTutorial.SetsAndFunctions
