/- File: Hol100/Div3.lean
Translation of HOL Light's 100/div3.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionLibrary.Pocklington
open HolCore.Kernel Session HolLight.Syntax HolExamples
open SessionLibrary.Prime SessionLibrary.Pocklington
namespace Hol100.Div3

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)

/- ========================================================================= -/
/- #85: divisibility by 3 rule                                               -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Library/prime.ml";;
#eval SessionLibrary.Prime.ensurePrime

#eval phrase 2
-- needs "Library/pocklington.ml";;
#eval SessionLibrary.Pocklington.ensurePocklington

#eval phrase 3
def EXP_10_CONG_3 : thm := keep "EXP_10_CONG_3" fun _ => (do
  prove ([[!n. (10 EXP n == 1) (mod 3)]])
   (INDUCT_TAC THEN REWRITE_TAC [EXP, CONG_REFL] THEN
    MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC ([[10 * 1]]) THEN CONJ_TAC THEN
    ASM_SIMP_TAC [CONG_MULT, CONG_REFL] THEN
    SIMP_TAC [CONG, ARITH] THEN CONV_TAC NUM_REDUCE_CONV)
  : ExceptT String IO thm).run
#eval EXP_10_CONG_3

#eval phrase 4
def SUM_CONG_3 : thm := keep "SUM_CONG_3" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[d = 1 * d]])
  prove ([[!d n. (nsum(0..n) (\i. 10 EXP i * d(i)) == nsum(0..n) (\i. d i)) (mod 3)]])
   (GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [NSUM_CLAUSES_NUMSEG] THENL
     [REWRITE_TAC [EXP, MULT_CLAUSES, CONG_REFL], ALL_TAC] THEN
    REWRITE_TAC [LE_0] THEN MATCH_MP_TAC CONG_ADD THEN
    ASM_REWRITE_TAC [] THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV) [h1] THEN
    MATCH_MP_TAC CONG_MULT THEN REWRITE_TAC [CONG_REFL, EXP_10_CONG_3])
  : ExceptT String IO thm).run
#eval SUM_CONG_3

#eval phrase 5
def DIVISIBILITY_BY_3 : thm := keep "DIVISIBILITY_BY_3" fun _ => (do
  prove ([[3 divides (nsum(0..n) (\i. 10 EXP i * d(i))) <=>
   3 divides (nsum(0..n) (\i. d i))]])
   (MATCH_MP_TAC CONG_DIVIDES THEN REWRITE_TAC [SUM_CONG_3])
  : ExceptT String IO thm).run
#eval DIVISIBILITY_BY_3

end Hol100.Div3
