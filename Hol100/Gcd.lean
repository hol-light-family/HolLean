/- File: Hol100/Gcd.lean
Translation of HOL Light's 100/gcd.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionLibrary.Prime
open HolCore.Kernel Session HolLight.Syntax HolExamples
open SessionLibrary.Prime
namespace Hol100.Gcd

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ec {α : Type} (x : Except String α) : ExceptT String IO α := ExceptT.mk (pure x)

/- ========================================================================= -/
/- Euclidean GCD algorithm.                                                  -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Library/prime.ml";;
#eval SessionLibrary.Prime.ensurePrime

#eval phrase 2
def egcd : thm := keep "egcd" fun _ => define
 [[egcd(m,n) = if m = 0 then n
              else if n = 0 then m
              else if m <= n then egcd(m,n - m)
              else egcd(m - n,n)]]
#eval egcd

/- ------------------------------------------------------------------------- -/
/- Main theorems.                                                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 3
def EGCD_INVARIANT : thm := keep "EGCD_INVARIANT" fun _ => (do
  prove ([[!m n d. d divides egcd(m,n) <=> d divides m /\ d divides n]])
   (GEN_TAC THEN GEN_TAC THEN WF_INDUCT_TAC ([[m + n]]) THEN
    GEN_TAC THEN ONCE_REWRITE_TAC [egcd] THEN
    ASM_CASES_TAC ([[m = 0]]) THEN ASM_REWRITE_TAC [DIVIDES_0] THEN
    ASM_CASES_TAC ([[n = 0]]) THEN ASM_REWRITE_TAC [DIVIDES_0] THEN
    COND_CASES_TAC THEN
    (HolCore.Lib.W (fun g => FIRST_X_ASSUM (fun th => HolLight.tactic_of do
       let pm ← Session.PART_MATCH
         (fun t => do
           let (_, b) ← HolCore.Basics.dest_forall (← rand t)
           HolCore.Equal.lhs b)
         th (← ec (HolCore.Equal.lhand (HolLight.snd g)))
       pure (MP_TAC pm))) THEN
     ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC]) THEN
    ASM_MESON_TAC [DIVIDES_SUB, DIVIDES_ADD, SUB_ADD, LE_CASES])
  : ExceptT String IO thm).run
#eval EGCD_INVARIANT

/- ------------------------------------------------------------------------- -/
/- Hence we get the proper behaviour, and it's equal to the real GCD.        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 4
def EGCD_GCD : thm := keep "EGCD_GCD" fun _ => (do
  prove ([[!m n. egcd(m,n) = gcd(m,n)]])
   (ONCE_REWRITE_TAC [(← HolLight.GSYM GCD_UNIQUE)] THEN
    MESON_TAC [EGCD_INVARIANT, DIVIDES_REFL])
  : ExceptT String IO thm).run
#eval EGCD_GCD

#eval phrase 5
def EGCD : thm := keep "EGCD" fun _ => (do
  prove ([[!a b. (egcd (a,b) divides a /\ egcd (a,b) divides b) /\
         (!e. e divides a /\ e divides b ==> e divides egcd (a,b))]])
   (REWRITE_TAC [EGCD_GCD, GCD])
  : ExceptT String IO thm).run
#eval EGCD

end Hol100.Gcd
