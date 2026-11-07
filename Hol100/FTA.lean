/- File: Hol100/FTA.lean
Translation of HOL Light's 100/fta.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionLibrary.Prime
open HolCore.Kernel Session HolLight.Syntax HolExamples
open SessionLibrary.Prime
namespace Hol100.FTA

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)
private def sr (tm : term) : ExceptT String IO thm := ExceptT.mk (SET_RULE tm)
private def ms (ths : List thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (MESON ths tm)

/- ========================================================================= -/
/- The fundamental theorem of arithmetic (unique prime factorization).       -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Library/prime.ml";;
#eval SessionLibrary.Prime.ensurePrime

#eval phrase 2
#eval Session.prioritize_num

/- ------------------------------------------------------------------------- -/
/- Definition of iterated product.                                           -/
/- ------------------------------------------------------------------------- -/

#eval phrase 3
def nproduct : thm := keep "nproduct" fun _ => new_definition [[nproduct = iterate ( * )]]
#eval nproduct

#eval phrase 4
def NPRODUCT_CLAUSES : thm := keep "NPRODUCT_CLAUSES" fun _ => (do
  prove ([[(!f. nproduct {} f = 1) /\
   (!x f s. FINITE(s)
            ==> (nproduct (x INSERT s) f =
                 if x IN s then nproduct s f else f(x) * nproduct s f))]])
   (REWRITE_TAC [nproduct, (← HolLight.GSYM NEUTRAL_MUL)] THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    MATCH_MP_TAC ITERATE_CLAUSES THEN REWRITE_TAC [MONOIDAL_MUL])
  : ExceptT String IO thm).run
#eval NPRODUCT_CLAUSES

#eval phrase 5
def NPRODUCT_EQ_1_EQ : thm := keep "NPRODUCT_EQ_1_EQ" fun _ => (do
  prove ([[!s f. FINITE s ==> (nproduct s f = 1 <=> !x. x IN s ==> f(x) = 1)]])
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC [NPRODUCT_CLAUSES, IN_INSERT, MULT_EQ_1, NOT_IN_EMPTY] THEN
    ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval NPRODUCT_EQ_1_EQ

#eval phrase 6
def NPRODUCT_SPLITOFF : thm := keep "NPRODUCT_SPLITOFF" fun _ => (do
  let h1 ← sr (← ExceptT.mk [[~(x IN s) ==> s DELETE x = s]])
  prove ([[!x:A f s. FINITE s
             ==> nproduct s f =
                 (if x IN s then f(x) else 1) * nproduct (s DELETE x) f]])
   (REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [MULT_CLAUSES, h1] THEN
    SUBGOAL_THEN ([[s = (x:A) INSERT (s DELETE x)]])
     (fun th => GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.LAND_CONV) [th] THEN
                ASM_SIMP_TAC [NPRODUCT_CLAUSES, FINITE_DELETE, IN_DELETE]) THEN
    REPEAT (POP_ASSUM MP_TAC) THEN SET_TAC [])
  : ExceptT String IO thm).run
#eval NPRODUCT_SPLITOFF

#eval phrase 7
def NPRODUCT_SPLITOFF_HACK : thm := keep "NPRODUCT_SPLITOFF_HACK" fun _ => (do
  prove ([[!x:A f s. nproduct s f =
             if FINITE s then
               (if x IN s then f(x) else 1) * nproduct (s DELETE x) f
             else nproduct s f]])
   (REPEAT STRIP_TAC THEN MESON_TAC [NPRODUCT_SPLITOFF])
  : ExceptT String IO thm).run
#eval NPRODUCT_SPLITOFF_HACK

#eval phrase 8
def NPRODUCT_EQ : thm := keep "NPRODUCT_EQ" fun _ => (do
  prove ([[!f g s. FINITE s /\ (!x. x IN s ==> f x = g x)
           ==> nproduct s f = nproduct s g]])
   (GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [NPRODUCT_CLAUSES, IN_INSERT])
  : ExceptT String IO thm).run
#eval NPRODUCT_EQ

#eval phrase 9
def NPRODUCT_EQ_GEN : thm := keep "NPRODUCT_EQ_GEN" fun _ => (do
  prove ([[!f g s t. FINITE s /\ s = t /\ (!x. x IN s ==> f x = g x)
             ==> nproduct s f = nproduct t g]])
   (MESON_TAC [NPRODUCT_EQ])
  : ExceptT String IO thm).run
#eval NPRODUCT_EQ_GEN

#eval phrase 10
def PRIME_DIVIDES_NPRODUCT : thm := keep "PRIME_DIVIDES_NPRODUCT" fun _ => (do
  prove ([[!p s f. prime p /\ FINITE s /\ p divides (nproduct s f)
           ==> ?x. x IN s /\ p divides (f x)]])
   (GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [NPRODUCT_CLAUSES, IN_INSERT, NOT_IN_EMPTY] THEN
    ASM_MESON_TAC [PRIME_DIVPROD, DIVIDES_ONE, PRIME_1])
  : ExceptT String IO thm).run
#eval PRIME_DIVIDES_NPRODUCT

#eval phrase 11
def NPRODUCT_CANCEL_PRIME : thm := keep "NPRODUCT_CANCEL_PRIME" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[~(j = 0) ==> j = SUC(j - 1)]])
  prove ([[!s p m f j.
        p EXP j * nproduct (s DELETE p) (\p. p EXP (f p)) = p * m
        ==> prime p /\ FINITE s /\ (!x. x IN s ==> prime x)
            ==> ~(j = 0) /\
                p EXP (j - 1) * nproduct (s DELETE p) (\p. p EXP (f p)) = m]])
   (REPEAT GEN_TAC THEN ASM_CASES_TAC ([[j = 0]]) THEN ASM_REWRITE_TAC [] THENL
     [ALL_TAC,
      FIRST_X_ASSUM (SUBST1_TAC o HolLight.MATCH_MP h1) THEN
      REWRITE_TAC [SUC_SUB1, EXP, (← HolLight.GSYM MULT_ASSOC), EQ_MULT_LCANCEL] THEN
      MESON_TAC [PRIME_0]] THEN
    ONCE_REWRITE_TAC [(← HolLight.GSYM CONTRAPOS_THM)] THEN
    REWRITE_TAC [EXP, MULT_CLAUSES] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[p:num]]), ([[s DELETE (p:num)]]), ([[\p. p EXP (f p)]])]
                   PRIME_DIVIDES_NPRODUCT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [divides, FINITE_DELETE], ALL_TAC] THEN
    REWRITE_TAC [IN_DELETE] THEN ASM_MESON_TAC [PRIME_1, prime, PRIME_DIVEXP])
  : ExceptT String IO thm).run
#eval NPRODUCT_CANCEL_PRIME

/- ------------------------------------------------------------------------- -/
/- Fundamental Theorem of Arithmetic.                                        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 12
def FTA : thm := keep "FTA" fun _ => (do
  let h7 ← sr (← ExceptT.mk [[!j k. {q | ~((if q = p then j q else k q) = 0)} DELETE p =
          {q | ~(k q = 0)} DELETE p]])
  let h6 ← ms [EXP] (← ExceptT.mk [[(if ~(x = 0) then p EXP x else 1) = p EXP x]])
  let h5 ← tt (← ExceptT.mk [[p /\ q /\ ((if p then x else y) = z) <=> p /\ q /\ x = z]])
  let h4 ← tt (← ExceptT.mk [[a /\ (a ==> b) ==> a /\ b]])
  let h3 ← sr (← ExceptT.mk [[{p | F} = {}]])
  let h2 ← tt (← ExceptT.mk [[a /\ b <=> ~(a ==> ~b)]])
  let h1 ← ar (← ExceptT.mk [[n = nproduct s f <=> nproduct s f = n]])
  prove ([[!n. ~(n = 0)
       ==> ?!i. FINITE {p | ~(i p = 0)} /\
                (!p. ~(i p = 0) ==> prime p) /\
                n = nproduct {p | ~(i p = 0)} (\p. p EXP (i p))]])
   (ONCE_REWRITE_TAC [h1] THEN
    REWRITE_TAC [EXISTS_UNIQUE_THM] THEN
    MATCH_MP_TAC num_WF THEN X_GEN_TAC ([[n:num]]) THEN REPEAT DISCH_TAC THEN
    ASM_CASES_TAC ([[n = 1]]) THENL
     [ASM_REWRITE_TAC [h2] THEN
      SIMP_TAC [NPRODUCT_EQ_1_EQ, EXP_EQ_1, IN_ELIM_THM] THEN
      REWRITE_TAC [FUN_EQ_THM, NOT_IMP, (← HolLight.GSYM CONJ_ASSOC)] THEN CONJ_TAC THENL
       [EXISTS_TAC ([[\n:num. 0]]) THEN
        REWRITE_TAC [h3, FINITE_RULES],
        REPEAT GEN_TAC THEN STRIP_TAC THEN
        X_GEN_TAC ([[q:num]]) THEN ASM_CASES_TAC ([[q = 1]]) THEN
        ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [PRIME_1]],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP PRIME_FACTOR) THEN
    REWRITE_TAC [divides, RIGHT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [([[p:num]]), ([[m:num]])] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[m:num]])) THEN ANTS_TAC THENL
     [ASM_MESON_TAC [PRIME_FACTOR_LT], ALL_TAC] THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [MULT_EQ_0, DE_MORGAN_THM]) THEN
    FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [DISCH_THEN (X_CHOOSE_THEN ([[i:num->num]]) STRIP_ASSUME_TAC) THEN
      EXISTS_TAC ([[\q:num. if q = p then i(q) + 1 else i(q)]]) THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC h4 THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC ([[p INSERT {p:num | ~(i p = 0)}]]) THEN
        ASM_SIMP_TAC [SUBSET, FINITE_INSERT, IN_INSERT, IN_ELIM_THM] THEN
        MESON_TAC [],
        ALL_TAC] THEN
      DISCH_TAC THEN CONJ_TAC THEN ASM_REWRITE_TAC [] THENL
       [ASM_MESON_TAC [ADD_EQ_0, ARITH_EQ], ALL_TAC] THEN
      FIRST_X_ASSUM (SUBST_ALL_TAC o HolLight.SYM) THEN
      MP_TAC (← HolLight.ISPEC ([[p:num]]) NPRODUCT_SPLITOFF_HACK) THEN
      DISCH_THEN (fun th => ONCE_REWRITE_TAC [th]) THEN
      ASM_REWRITE_TAC [IN_ELIM_THM, ADD_EQ_0, ARITH] THEN
      REWRITE_TAC [MULT_ASSOC] THEN BINOP_TAC THENL
       [ASM_CASES_TAC ([[(i:num->num) p = 0]]) THEN
        ASM_REWRITE_TAC [EXP_ADD, EXP_1, EXP, MULT_AC],
        ALL_TAC] THEN
      MATCH_MP_TAC NPRODUCT_EQ_GEN THEN RULE_ASSUM_TAC (fun th => (ExceptT.mk (Session.SIMP_RULE [] th) : ExceptT String IO thm)) THEN
      ASM_SIMP_TAC [FINITE_DELETE, IN_DELETE, EXTENSION, IN_ELIM_THM] THEN
      ONCE_REWRITE_TAC [COND_RAND] THEN ONCE_REWRITE_TAC [COND_RATOR] THEN
      REWRITE_TAC [ADD_EQ_0, ARITH] THEN MESON_TAC [],
      ALL_TAC] THEN
    MP_TAC (← HolLight.ISPEC ([[p:num]]) NPRODUCT_SPLITOFF_HACK) THEN
    DISCH_THEN (fun th => ONCE_REWRITE_TAC [th]) THEN
    REWRITE_TAC [h5] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN
    REWRITE_TAC [h6] THEN
    REWRITE_TAC [FUN_EQ_THM] THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [([[j:num->num]]), ([[k:num->num]])] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPECL
     [([[\i:num. if i = p then j(i) - 1 else j(i)]]),
      ([[\i:num. if i = p then k(i) - 1 else k(i)]])]) THEN
    REWRITE_TAC [] THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP NPRODUCT_CANCEL_PRIME)) THEN
    ASM_REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN STRIP_TAC THEN
    REWRITE_TAC [h7] THEN
    ANTS_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC [] THEN MAP_EVERY UNDISCH_TAC
       [([[~(j(p:num) = 0)]]), ([[~(k(p:num) = 0)]])] THEN ARITH_TAC] THEN
    ONCE_REWRITE_TAC [COND_RAND] THEN ONCE_REWRITE_TAC [COND_RATOR] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC ([[{p:num | ~(j p = 0)}]]) THEN
      ASM_REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ARITH_TAC,
      ASM_MESON_TAC [SUB_0],
      FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (SUBST1_TAC (← HolLight.SYM th) THEN AP_TERM_TAC)) THEN
      MATCH_MP_TAC NPRODUCT_EQ_GEN THEN ASM_REWRITE_TAC [FINITE_DELETE] THEN
      SIMP_TAC [IN_DELETE, IN_ELIM_THM],
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC ([[{p:num | ~(k p = 0)}]]) THEN
      ASM_REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ARITH_TAC,
      ASM_MESON_TAC [SUB_0],
      FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (SUBST1_TAC (← HolLight.SYM th) THEN AP_TERM_TAC)) THEN
      MATCH_MP_TAC NPRODUCT_EQ_GEN THEN ASM_REWRITE_TAC [FINITE_DELETE] THEN
      SIMP_TAC [IN_DELETE, IN_ELIM_THM]])
  : ExceptT String IO thm).run
#eval FTA

end Hol100.FTA
