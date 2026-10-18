/- File: HolExamples/SafetyLiveness.lean
Translation of HOL Light's Examples/safetyliveness.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolExamples.Common
open HolCore.Kernel Session HolLight.Syntax HolExamples
open scoped HolLight
namespace HolExamples.SafetyLiveness

private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

-- ========================================================================= --
-- Formal definition of "safety" and "liveness" for properties of traces.    --
-- Proof that any property of traces can be decomposed into the conjunction  --
-- of a safety and a liveness property, following Fred Schneider's paper     --
-- "Decomposing Properties into Safety and Liveness using Predicate Logic".  --
--                                                                           --
--         https://apps.dtic.mil/dtic/tr/fulltext/u2/a187556.pdf             --
-- ========================================================================= --

#eval phrase 1
unsafe def safety : thm := keep "safety" fun _ => new_definition
  [[safety (p:(num->S)->bool) <=>
        !s. ~(p s) ==> ?n. !s'. (!m. m <= n ==> s(m) = s'(m)) ==> ~(p s')]]
#eval safety

#eval phrase 2
unsafe def liveness : thm := keep "liveness" fun _ => new_definition
  [[liveness (p:(num->S)->bool) <=>
        !s n. ?s'. (!m. m <= n ==> s(m) = s'(m)) /\ p s']]
#eval liveness

-- ------------------------------------------------------------------------- --
-- It doesn't matter whether we take strict or non-strict subsequences.      --
-- ------------------------------------------------------------------------- --

#eval phrase 3
unsafe def SAFETY : thm := keep "SAFETY" fun _ => (do
  prove ([[!p:(num->S)->bool.
        safety p <=>
        !s. ~(p s) ==> ?n. !s'. (!m. m < n ==> s(m) = s'(m)) ==> ~(p s')]])
   (GEN_TAC THEN REWRITE_TAC [safety, (← HolLight.GSYM LT_SUC_LE)] THEN
    MESON_TAC [ARITH_RULE [[m < n ==> m < SUC n]]])
  : ExceptT String IO thm).run
#eval SAFETY

#eval phrase 4
unsafe def LIVENESS : thm := keep "LIVENESS" fun _ => (do
  prove ([[!p:(num->S)->bool.
        liveness p <=>
        !s n. ?s'. (!m. m < n ==> s(m) = s'(m)) /\ p s']])
   (GEN_TAC THEN REWRITE_TAC [liveness, (← HolLight.GSYM LT_SUC_LE)] THEN
    MESON_TAC [ARITH_RULE [[m < n ==> m < SUC n]]])
  : ExceptT String IO thm).run
#eval LIVENESS

-- ------------------------------------------------------------------------- --
-- Decomposition theorem (following top level of Schneider's proof).         --
-- ------------------------------------------------------------------------- --

#eval phrase 5
unsafe def SAFETY_LIVENESS_DECOMPOSITION : thm := keep "SAFETY_LIVENESS_DECOMPOSITION" fun _ => (do
  prove ([[!P:(num->S)->bool.
      ?S L. safety S /\ liveness L /\ (!x. S x /\ L x <=> P x)]])
   (REPEAT GEN_TAC THEN
    ABBREV_TAC [[Q = \s:num->S. !i. ?b. (!j. j <= i ==> b j = s j) /\ P b]] THEN
    MAP_EVERY EXISTS_TAC [ [[\s:num->S. P s \/ Q s]], [[\s:num->S. P s \/ ~Q s]] ] THEN
    REWRITE_TAC [CONJ_ASSOC] THEN CONJ_TAC THENL
     [EXPAND_TAC "Q" THEN REWRITE_TAC [safety, liveness], MESON_TAC []] THEN
    REWRITE_TAC [DE_MORGAN_THM, IMP_CONJ, NOT_FORALL_THM] THEN CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC [],
      MESON_TAC []])
  : ExceptT String IO thm).run
#eval SAFETY_LIVENESS_DECOMPOSITION

end HolExamples.SafetyLiveness
