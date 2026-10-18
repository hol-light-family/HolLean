/- File: HolExamples/HarmonicSum.lean
Translation of HOL Light's Examples/harmonicsum.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolExamples.Common
open HolCore.Kernel Session HolLight.Syntax HolExamples
open scoped HolLight
open SessionLibrary.Prime SessionLibrary.Products SessionLibrary.Floor
namespace HolExamples.HarmonicSum

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- ========================================================================= -/
/- Nice little result that harmonic sum never gives an integer.              -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Library/prime.ml";;
#eval SessionLibrary.Prime.ensurePrime

#eval phrase 2
-- needs "Library/products.ml";;
#eval SessionLibrary.Products.ensureProducts

#eval phrase 3
-- needs "Library/floor.ml";;
#eval SessionLibrary.Floor.ensureFloor

/- ------------------------------------------------------------------------- -/
/- In any contiguous range, index (order) of 2 has a strict maximum.         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 4
unsafe def NUMSEG_MAXIMAL_INDEX_2 : thm := keep "NUMSEG_MAXIMAL_INDEX_2" fun _ => (do
  prove ([[!m n. 1 <= m /\ m <= n
         ==> ?k. k IN m..n /\
                 !l. l IN m..n /\ ~(l = k) ==> index 2 l < index 2 k]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ExceptT.mk (HolLight.ISPEC ([[\x. x IN IMAGE (index 2) (m..n)]]) num_MAX)) THEN
    REWRITE_TAC [FORALL_IN_IMAGE, EXISTS_IN_IMAGE, IN_NUMSEG] THEN
    ASM_REWRITE_TAC [MEMBER_NOT_EMPTY, IMAGE_EQ_EMPTY, NUMSEG_EMPTY, NOT_LT] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[p /\ (q ==> r) ==> (p <=> q) ==> r]])) THEN
    CONJ_TAC THENL [MESON_TAC [INDEX_TRIVIAL_BOUND, LE_TRANS], ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[k:num]] THEN
    STRIP_TAC THEN ASM_SIMP_TAC [LT_LE] THEN X_GEN_TAC [[l:num]] THEN STRIP_TAC THEN
    MP_TAC (← ExceptT.mk (HolLight.SPECL [ [[l:num]], [[(2:num)]] ] INDEX_DECOMPOSITION_PRIME)) THEN
    MP_TAC (← ExceptT.mk (HolLight.SPECL [ [[k:num]], [[(2:num)]] ] INDEX_DECOMPOSITION_PRIME)) THEN
    REWRITE_TAC [PRIME_2, LEFT_IMP_EXISTS_THM, COPRIME_2] THEN
    ASM_CASES_TAC [[k = 0]] THENL [ASM_ARITH_TAC, ASM_REWRITE_TAC []] THEN
    ASM_CASES_TAC [[l = 0]] THENL [ASM_ARITH_TAC, ASM_REWRITE_TAC []] THEN
    X_GEN_TAC [[p:num]] THEN STRIP_TAC THEN X_GEN_TAC [[q:num]] THEN STRIP_TAC THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC (← ExceptT.mk (ARITH_RULE [[~(l:num = k) ==> l < k \/ k < l]])) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (DISJ_CASES_THEN MP_TAC) THEN
    MAP_EVERY EXPAND_TAC ["k", "l"] THEN
    REWRITE_TAC [LT_MULT_LCANCEL, EXP_EQ_0, ARITH_EQ] THEN DISCH_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[2 EXP index 2 k * (q + 1)]]),
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[2 EXP index 2 k * (p + 1)]])] THEN
    ASM_SIMP_TAC [INDEX_MUL, PRIME_2, EXP_EQ_0, ADD_EQ_0, ARITH, NOT_IMP,
                 INDEX_EXP, INDEX_REFL] THEN
    REWRITE_TAC [(← ExceptT.mk (ARITH_RULE [[n * 1 + k <= n <=> k = 0]])), INDEX_EQ_0] THEN
    ASM_REWRITE_TAC [ADD_EQ_0, ARITH, DIVIDES_2, EVEN_ADD, NOT_EVEN] THEN
    MATCH_MP_TAC (← ExceptT.mk (ARITH_RULE
     [[!p. m <= e * q /\ e * (q + 1) <= e * p /\ e * p <= n
         ==> m <= e * (q + 1) /\ e * (q + 1) <= n]]))
    THENL [EXISTS_TAC [[p:num]], EXISTS_TAC [[q:num]]] THEN
    REWRITE_TAC [LE_MULT_LCANCEL] THEN ASM_REWRITE_TAC [] THEN
    ASM_ARITH_TAC)
  : ExceptT String IO thm).run
#eval NUMSEG_MAXIMAL_INDEX_2

/- ------------------------------------------------------------------------- -/
/- Hence the result.                                                         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 5
unsafe def NONINTEGER_HARMONIC : thm := keep "NONINTEGER_HARMONIC" fun _ => (do
  let lemma ← prove
   ([[!m n. 1 <= m
           ==> sum(m..n) (\k. inv(&k)) =
               (sum(m..n) (\k. product ((m..n) DELETE k) (\i. &i))) /
               product(m..n) (\i. &i)]])
    (REPEAT STRIP_TAC THEN REWRITE_TAC [real_div, (← ExceptT.mk (HolLight.GSYM SUM_RMUL))] THEN
     MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC [[k:num]] THEN STRIP_TAC THEN
     REWRITE_TAC [] THEN MATCH_MP_TAC (← ExceptT.mk (REAL_FIELD
      [[~(x = &0) /\ ~(z = &0) /\ x * y = z
      ==> inv x = y * inv z]])) THEN
     ASM_SIMP_TAC [PRODUCT_EQ_0, FINITE_NUMSEG, IN_NUMSEG, REAL_OF_NUM_EQ] THEN
     REPEAT (CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC]) THEN
     MP_TAC (← ExceptT.mk (HolLight.ISPECL [ [[\i. &i]], [[m..n]], [[k:num]] ] PRODUCT_DELETE)) THEN
     ASM_REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG])
  prove ([[!m n. 1 <= m /\ 1 < n /\ m <= n ==> ~(integer (sum(m..n) (\k. inv(&k))))]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC [[n:num = m]] THENL
     [ASM_REWRITE_TAC [SUM_SING_NUMSEG] THEN
      REWRITE_TAC [(← ExceptT.mk (REAL_ARITH3 [[inv x = &1 / x]])), INTEGER_DIV, DIVIDES_ONE] THEN
      ASM_ARITH_TAC,
      ALL_TAC] THEN
    ASM_SIMP_TAC [lemma] THEN
    SIMP_TAC [(← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_NPRODUCT)), FINITE_NUMSEG,
             (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_SUM)),
             FINITE_DELETE, INTEGER_DIV] THEN
    SIMP_TAC [NPRODUCT_EQ_0, FINITE_NUMSEG, IN_NUMSEG, DE_MORGAN_THM] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
    MP_TAC (← ExceptT.mk (HolLight.SPECL [ [[m:num]], [[n:num]] ] NUMSEG_MAXIMAL_INDEX_2)) THEN
    ASM_REWRITE_TAC [IN_NUMSEG] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[k:num]]) STRIP_ASSUME_TAC) THEN
    MP_TAC (← ExceptT.mk (HolLight.ISPECL [ [[\i. nproduct((m..n) DELETE i) (\j. j)]], [[m..n]], [[k:num]] ]
       NSUM_DELETE)) THEN
    ASM_REWRITE_TAC [IN_NUMSEG, FINITE_NUMSEG] THEN
    DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN
    ABBREV_TAC [[i = index 2 (nproduct ((m..n) DELETE k) (\j. j))]] THEN
    MATCH_MP_TAC (← HolLight.EQT_ELIM
     (← ExceptT.mk (((HolLight.REWRITE_CONV [IMP_CONJ, CONTRAPOS_THM]) THENC
         (fun t => (do HolLight.EQT_INTRO (← ExceptT.mk (NUMBER_RULE t)) : ExceptT String IO thm).run))
       [[!p. p divides r /\ p divides n /\ ~(p divides m)
       ==> ~(r divides (m + n))]]))) THEN
    EXISTS_TAC [[2 EXP (i + 1)]] THEN REPEAT CONJ_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC DIVIDES_NSUM THEN
      REWRITE_TAC [FINITE_NUMSEG, FINITE_DELETE, IN_NUMSEG, IN_DELETE] THEN
      X_GEN_TAC [[l:num]] THEN STRIP_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [PRIMEPOW_DIVIDES_INDEX] THEN
    SIMP_TAC [ARITH, DE_MORGAN_THM, NPRODUCT_EQ_0, FINITE_NUMSEG, FINITE_DELETE,
             IN_NUMSEG, IN_DELETE]
    THENL
     [DISJ2_TAC THEN
      MP_TAC (← ExceptT.mk (HolLight.ISPECL [ [[\i:num. i]], [[m..n]], [[k:num]] ] NPRODUCT_DELETE)) THEN
      ASM_REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG] THEN
      DISCH_THEN (MP_TAC o HolLight.AP_TERM [[index 2]]) THEN IMP_REWRITE_TAC [INDEX_MUL] THEN
      SIMP_TAC [NPRODUCT_EQ_0, FINITE_NUMSEG, FINITE_DELETE, PRIME_2] THEN
      REWRITE_TAC [IN_DELETE, IN_NUMSEG] THEN
      ANTS_TAC THENL [ASM_ARITH_TAC, DISCH_THEN (SUBST1_TAC o HolLight.SYM)] THEN
      FIRST_X_ASSUM (fun th => HolLight.tactic_of do
       let a ← HolLight.SPEC ([[m:num]]) th
       let b ← HolLight.SPEC ([[n:num]]) th
       pure (MP_TAC a THEN MP_TAC b)) THEN
      ASM_ARITH_TAC,
      DISJ2_TAC THEN
      MP_TAC (← ExceptT.mk (HolLight.ISPECL [ [[\i:num. i]], [[m..n]], [[l:num]] ] NPRODUCT_DELETE)) THEN
      MP_TAC (← ExceptT.mk (HolLight.ISPECL [ [[\i:num. i]], [[m..n]], [[k:num]] ] NPRODUCT_DELETE)) THEN
      ASM_REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG, IMP_IMP] THEN
      DISCH_THEN (CONJUNCTS_THEN (MP_TAC o HolLight.AP_TERM [[index 2]])) THEN
      IMP_REWRITE_TAC [INDEX_MUL] THEN
      SIMP_TAC [NPRODUCT_EQ_0, FINITE_NUMSEG, FINITE_DELETE, PRIME_2] THEN
      REWRITE_TAC [IN_DELETE, IN_NUMSEG] THEN
      ANTS_TAC THENL [ASM_ARITH_TAC, DISCH_TAC] THEN
      ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      FIRST_X_ASSUM (SUBST1_TAC o HolLight.SYM) THEN ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[l:num]]) THEN ASM_ARITH_TAC,
      ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC])
  : ExceptT String IO thm).run
#eval NONINTEGER_HARMONIC

end HolExamples.HarmonicSum
