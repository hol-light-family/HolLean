/- File: Hol100/Arithmetic.lean
Translation of HOL Light's 100/arithmetic.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
open HolCore.Kernel Session HolLight.Syntax HolExamples
namespace Hol100.Arithmetic

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- ========================================================================= -/
/- Sum of an arithmetic series.                                              -/
/- ========================================================================= -/

#eval phrase 1
def ARITHMETIC_PROGRESSION_LEMMA : thm := keep "ARITHMETIC_PROGRESSION_LEMMA" fun _ => (do
  prove ([[!n. nsum(0..n) (\i. a + d * i) = ((n + 1) * (2 * a + n * d)) DIV 2]])
   (INDUCT_TAC THEN ASM_REWRITE_TAC [NSUM_CLAUSES_NUMSEG] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval ARITHMETIC_PROGRESSION_LEMMA

#eval phrase 2
def ARITHMETIC_PROGRESSION : thm := keep "ARITHMETIC_PROGRESSION" fun _ => (do
  prove ([[!n. 1 <= n
       ==> nsum(0..n-1) (\i. a + d * i) = (n * (2 * a + (n - 1) * d)) DIV 2]])
   (INDUCT_TAC THEN REWRITE_TAC [ARITHMETIC_PROGRESSION_LEMMA, SUC_SUB1] THEN
    ARITH_TAC)
  : ExceptT String IO thm).run
#eval ARITHMETIC_PROGRESSION

end Hol100.Arithmetic
