/- File: Hol100/Liouville.lean
Translation of HOL Light's 100/liouville.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionLibrary.Floor
import SessionLibrary.Poly
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Floor SessionLibrary.Analysis SessionLibrary.Poly
namespace Hol100.Liouville

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def nc (tm : term) : ExceptT String IO thm := ExceptT.mk (num_CONV tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)

/- ========================================================================= -/
/- Liouville approximation theorem.                                          -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Library/floor.ml";;
#eval SessionLibrary.Floor.ensureFloor

#eval phrase 2
-- needs "Library/poly.ml";;
#eval SessionLibrary.Poly.ensurePoly

/- ------------------------------------------------------------------------- -/
/- Definition of algebraic and transcendental.                               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 3
def algebraic : thm := keep "algebraic" fun _ => new_definition
 [[algebraic(x) <=> ?p. ALL integer p /\ ~(poly p = poly []) /\ poly p x = &0]]
#eval algebraic

#eval phrase 4
def transcendental : thm := keep "transcendental" fun _ => new_definition
 [[transcendental(x) <=> ~(algebraic x)]]
#eval transcendental

/- ------------------------------------------------------------------------- -/
/- Some trivialities.                                                        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 5
def REAL_INTEGER_EQ_0 : thm := keep "REAL_INTEGER_EQ_0" fun _ => (do
  prove ([[!x. integer x /\ abs(x) < &1 ==> x = &0]])
   (MESON_TAC [REAL_ABS_INTEGER_LEMMA, SessionLibrary.Analysis.REAL_NOT_LE])
  : ExceptT String IO thm).run
#eval REAL_INTEGER_EQ_0

#eval phrase 6
def FACT_LE_REFL : thm := keep "FACT_LE_REFL" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[1 <= n <=> 0 < n]])
  let h1 ← ar (← ExceptT.mk [[x * 1 <= a ==> x <= a]])
  prove ([[!n. n <= FACT n]])
   (INDUCT_TAC THEN REWRITE_TAC [FACT, ARITH] THEN
    MATCH_MP_TAC h1 THEN
    REWRITE_TAC [LE_MULT_LCANCEL, NOT_SUC, FACT_LT,
                h2])
  : ExceptT String IO thm).run
#eval FACT_LE_REFL

#eval phrase 7
def EXP_LE_REFL : thm := keep "EXP_LE_REFL" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[n <= x ==> 1 * x < y ==> SUC n <= y]])
  prove ([[!a. 1 < a ==> !n. n <= a EXP n]])
   (GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC [EXP, ARITH] THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h1) THEN
    REWRITE_TAC [LT_MULT_RCANCEL, EXP_EQ_0] THEN
    POP_ASSUM MP_TAC THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval EXP_LE_REFL

/- ------------------------------------------------------------------------- -/
/- Inequality variant of mean value theorem.                                 -/
/- ------------------------------------------------------------------------- -/

#eval phrase 8
def MVT_INEQ : thm := keep "MVT_INEQ" fun _ => (do
  let h2 ← rr (← ExceptT.mk [[x = a \/ x < a \/ a < x]])
  let h1 ← tt (← ExceptT.mk [[a ==> b /\ c <=> (a ==> b) /\ (a ==> c)]])
  prove ([[!f f' a d M.
        &0 < M /\ &0 < d /\
        (!x. abs(x - a) <= d ==> (f diffl f'(x)) x /\ abs(f' x) < M)
        ==> !x. abs(x - a) <= d ==> abs(f x - f a) < M * d]])
   (REWRITE_TAC [h1] THEN
    REWRITE_TAC [FORALL_AND_THM] THEN
    REPEAT STRIP_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC h2 THENL
     [ASM_SIMP_TAC [SessionLibrary.Analysis.REAL_SUB_REFL, REAL_ABS_NUM, REAL_LT_MUL],
      MP_TAC (← HolLight.SPECL [([[f:real->real]]), ([[f':real->real]]), ([[x:real]]), ([[a:real]])] MVT_ALT),
      MP_TAC (← HolLight.SPECL [([[f:real->real]]), ([[f':real->real]]), ([[a:real]]), ([[x:real]])] MVT_ALT)] THEN
    (ANTS_TAC THENL
      [ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist HolLight.CONJ) THEN REAL_ARITH_TAC2,
       ALL_TAC]) THEN
    STRIP_TAC THENL
     [ONCE_REWRITE_TAC [REAL_ABS_SUB], ALL_TAC] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN ASM_REWRITE_TAC [REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC ([[d * abs(f'(z:real))]]) THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_RMUL,
       MATCH_MP_TAC REAL_LT_LMUL THEN
       ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC]) THEN
    POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist HolLight.CONJ) THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval MVT_INEQ

/- ------------------------------------------------------------------------- -/
/- Appropriate multiple of poly on rational is an integer.                   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 9
def POLY_MULTIPLE_INTEGER : thm := keep "POLY_MULTIPLE_INTEGER" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[(q * qp) * (h + pq * pol) = q * h * qp + (q * pq) * (qp * pol)]])
  prove ([[!p q l. ALL integer l ==> integer(&q pow (LENGTH l) * poly l (&p / &q))]])
   (GEN_TAC THEN GEN_TAC THEN ASM_CASES_TAC ([[q = 0]]) THENL
     [LIST_INDUCT_TAC THEN REWRITE_TAC [poly, SessionLibrary.Analysis.REAL_MUL_RZERO, INTEGER_CLOSED] THEN
      ASM_REWRITE_TAC [Session.listDefs.LENGTH, real_pow, SessionLibrary.Analysis.REAL_MUL_LZERO, INTEGER_CLOSED],
      ALL_TAC] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [poly, SessionLibrary.Analysis.REAL_MUL_RZERO, INTEGER_CLOSED] THEN
    REWRITE_TAC [Session.listDefs.LENGTH, real_pow, Session.listDefs.ALL] THEN DISCH_TAC THEN
    REWRITE_TAC [h1] THEN
    ASM_SIMP_TAC [REAL_DIV_LMUL, REAL_OF_NUM_EQ] THEN
    MATCH_MP_TAC (← ec (HolCore.Lib.el 1 (HolLight.CONJUNCTS INTEGER_CLOSED))) THEN
    ASM_SIMP_TAC [INTEGER_CLOSED])
  : ExceptT String IO thm).run
#eval POLY_MULTIPLE_INTEGER

/- ------------------------------------------------------------------------- -/
/- First show any root is surrounded by an other-root-free zone.             -/
/- ------------------------------------------------------------------------- -/

#eval phrase 10
def SEPARATE_FINITE_SET : thm := keep "SEPARATE_FINITE_SET" fun _ => (do
  prove ([[!a s. FINITE s
         ==> ~(a IN s) ==> ?d. &0 < d /\ !x. x IN s ==> d <= abs(x - a)]])
   (GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY, DE_MORGAN_THM] THEN
    CONJ_TAC THENL [MESON_TAC [SessionLibrary.Analysis.REAL_LT_01], ALL_TAC] THEN
    REPEAT GEN_TAC THEN DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    EXISTS_TAC ([[min d (abs(x - a))]]) THEN
    ASM_REWRITE_TAC [REAL_MIN_LE, REAL_LT_MIN, (← HolLight.GSYM REAL_ABS_NZ), SessionLibrary.Analysis.REAL_SUB_0] THEN
    ASM_MESON_TAC [SessionLibrary.Analysis.REAL_LE_REFL])
  : ExceptT String IO thm).run
#eval SEPARATE_FINITE_SET

#eval phrase 11
def POLY_ROOT_SEPARATE_LE : thm := keep "POLY_ROOT_SEPARATE_LE" fun _ => (do
  prove ([[!p x. poly p x = &0 /\ ~(poly p = poly [])
         ==> ?d. &0 < d /\
                 !x'. &0 < abs(x' - x) /\ abs(x' - x) < d
                      ==> ~(poly p x' = &0)]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [([[x:real]]), ([[{x | poly p x = &0} DELETE x]])] SEPARATE_FINITE_SET) THEN
    ASM_SIMP_TAC [POLY_ROOTS_FINITE_SET, FINITE_DELETE, IN_DELETE] THEN
    MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC [IN_ELIM_THM] THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_ABS_NZ), SessionLibrary.Analysis.REAL_SUB_0] THEN MESON_TAC [SessionLibrary.Analysis.REAL_NOT_LT])
  : ExceptT String IO thm).run
#eval POLY_ROOT_SEPARATE_LE

#eval phrase 12
def POLY_ROOT_SEPARATE_LT : thm := keep "POLY_ROOT_SEPARATE_LT" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[&0 < d ==> &0 < d / &2 /\ (x <= d / &2 ==> x < d)]])
  prove ([[!p x. poly p x = &0 /\ ~(poly p = poly [])
         ==> ?d. &0 < d /\
                 !x'. &0 < abs(x' - x) /\ abs(x' - x) <= d
                      ==> ~(poly p x' = &0)]])
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o HolLight.MATCH_MP POLY_ROOT_SEPARATE_LE) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[d:real]]) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC ([[d / &2]]) THEN ASM_MESON_TAC [h1])
  : ExceptT String IO thm).run
#eval POLY_ROOT_SEPARATE_LT

/- ------------------------------------------------------------------------- -/
/- And also there is a positive bound on a polynomial in an interval.        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 13
def POLY_BOUND_INTERVAL : thm := keep "POLY_BOUND_INTERVAL" fun _ => (do
  prove ([[!p d x. ?M. &0 < M /\ !x'. abs(x' - x) <= d ==> abs(poly p x') < M]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [([[poly p]]), ([[x - d]]), ([[x + d]])] CONT_BOUNDED_ABS) THEN
    REWRITE_TAC [(← HolLight.REWRITE_RULE [ETA_AX] (← HolLight.SPEC_ALL POLY_CONT))] THEN
    DISCH_THEN (X_CHOOSE_TAC ([[M:real]])) THEN EXISTS_TAC ([[&1 + abs M]]) THEN
    CONJ_TAC THENL [REAL_ARITH_TAC2, ALL_TAC] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC ([[M:real]]) THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN POP_ASSUM MP_TAC, ALL_TAC] THEN
    REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval POLY_BOUND_INTERVAL

/- ------------------------------------------------------------------------- -/
/- Now put these together to get the interval we need.                       -/
/- ------------------------------------------------------------------------- -/

#eval phrase 14
def LIOUVILLE_INTERVAL : thm := keep "LIOUVILLE_INTERVAL" fun _ => (do
  prove ([[!p x. poly p x = &0 /\ ~(poly p = poly [])
         ==> ?c. &0 < c /\
                 (!x'. abs(x' - x) <= c
                       ==> abs(poly(poly_diff p) x') < &1 / c) /\
                 (!x'. &0 < abs(x' - x) /\ abs(x' - x) <= c
                       ==> ~(poly p x' = &0))]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [([[p:real list]]), ([[x:real]])] POLY_ROOT_SEPARATE_LT) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[d:real]]) STRIP_ASSUME_TAC) THEN
    MP_TAC (← HolLight.SPECL [([[poly_diff p]]), ([[d:real]]), ([[x:real]])] POLY_BOUND_INTERVAL) THEN
    DISCH_THEN (X_CHOOSE_TAC ([[M:real]])) THEN EXISTS_TAC ([[min d (inv M)]]) THEN
    ASM_SIMP_TAC [REAL_LT_MIN, REAL_LE_MIN, REAL_LT_INV_EQ] THEN
    X_GEN_TAC ([[y:real]]) THEN STRIP_TAC THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LTE_TRANS THEN EXISTS_TAC ([[M:real]]) THEN
    ASM_SIMP_TAC [] THEN GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM REAL_INV_INV)] THEN
    REWRITE_TAC [real_div, REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC [REAL_MIN_LE, REAL_LT_MIN] THEN
    ASM_REWRITE_TAC [REAL_LT_INV_EQ, SessionLibrary.Analysis.REAL_LE_REFL])
  : ExceptT String IO thm).run
#eval LIOUVILLE_INTERVAL

/- ------------------------------------------------------------------------- -/
/- Liouville's approximation theorem.                                        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 15
def LIOUVILLE : thm := keep "LIOUVILLE" fun _ => (do
  let h2 ← rr (← ExceptT.mk [[x <= d ==> d <= e ==> x <= e]])
  let h1 ← rr (← ExceptT.mk [[abs(x - y) <= d ==> d <= e ==> abs(y - x) <= e]])
  prove ([[!x. algebraic x
       ==> ?n c. c > &0 /\
                 !p q. ~(q = 0) ==> &p / &q = x \/
                                    abs(x - &p / &q) > c / &q pow n]])
   (GEN_TAC THEN REWRITE_TAC [algebraic, real_gt] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[l:real list]]) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC ([[LENGTH(l:real list)]]) THEN
    MP_TAC (← HolLight.SPECL [([[l:real list]]), ([[x:real]])] LIOUVILLE_INTERVAL) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[c:real]]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [(← HolLight.GSYM SessionLibrary.Analysis.REAL_NOT_LE)] THEN
    MAP_EVERY X_GEN_TAC [([[p:num]]), ([[q:num]])] THEN DISCH_TAC THEN
    ASM_CASES_TAC ([[&p / &q = x]]) THEN ASM_REWRITE_TAC [] THEN
    REPEAT STRIP_TAC THEN UNDISCH_TAC ([[!x'. &0 < abs(x' - x) /\ abs(x' - x) <= c ==> ~(poly l x' = &0)]]) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[&p / &q]])) THEN REWRITE_TAC [NOT_IMP] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC [(← HolLight.GSYM REAL_ABS_NZ), SessionLibrary.Analysis.REAL_SUB_0],
      FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h1) THEN
      ASM_SIMP_TAC [REAL_POW_LT, REAL_OF_NUM_LT, REAL_LE_LDIV_EQ, LT_NZ] THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM SessionLibrary.Analysis.REAL_MUL_RID)] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC [SessionLibrary.Analysis.REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_POW_LE_1 THEN REWRITE_TAC [REAL_OF_NUM_LE] THEN
      UNDISCH_TAC ([[~(q = 0)]]) THEN ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[&q pow (LENGTH(l:real list)) * poly l (&p / &q) = &0]]) MP_TAC THENL
     [ALL_TAC, ASM_REWRITE_TAC [REAL_ENTIRE, REAL_POW_EQ_0, REAL_OF_NUM_EQ]] THEN
    MATCH_MP_TAC REAL_INTEGER_EQ_0 THEN
    ASM_SIMP_TAC [POLY_MULTIPLE_INTEGER] THEN
    MP_TAC (← HolLight.SPECL [([[poly l]]), ([[poly(poly_diff l)]]), ([[x:real]]),
                  ([[c / &q pow (LENGTH(l:real list))]]), ([[&1 / c]])] MVT_INEQ) THEN
    ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH, LT_NZ, REAL_POW_LT] THEN
    ANTS_TAC THENL
     [REWRITE_TAC [(← HolLight.REWRITE_RULE [ETA_AX] (← HolLight.SPEC_ALL POLY_DIFF))] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h2) THEN
      ASM_SIMP_TAC [REAL_POW_LT, REAL_OF_NUM_LT, REAL_LE_LDIV_EQ, LT_NZ] THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM SessionLibrary.Analysis.REAL_MUL_RID)] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC [SessionLibrary.Analysis.REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_POW_LE_1 THEN REWRITE_TAC [REAL_OF_NUM_LE] THEN
      UNDISCH_TAC ([[~(q = 0)]]) THEN ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [real_div, REAL_MUL_ASSOC, REAL_MUL_LID] THEN
    ASM_SIMP_TAC [REAL_MUL_LINV, SessionLibrary.Analysis.REAL_LT_IMP_NZ] THEN
    REWRITE_TAC [(← HolLight.GSYM real_div)] THEN DISCH_THEN (MP_TAC o HolLight.SPEC ([[&p / &q]])) THEN
    REWRITE_TAC [SessionLibrary.Analysis.REAL_SUB_RZERO] THEN ONCE_REWRITE_TAC [REAL_ABS_SUB] THEN
    ASM_REWRITE_TAC [] THEN
    ASM_SIMP_TAC [REAL_POW_LT, REAL_OF_NUM_LT, REAL_LT_RDIV_EQ, LT_NZ] THEN
    REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_POW, REAL_ABS_NUM] THEN
    REWRITE_TAC [REAL_MUL_AC])
  : ExceptT String IO thm).run
#eval LIOUVILLE

/- ------------------------------------------------------------------------- -/
/- Corollary for algebraic irrationals.                                      -/
/- ------------------------------------------------------------------------- -/

#eval phrase 16
def LIOUVILLE_IRRATIONAL : thm := keep "LIOUVILLE_IRRATIONAL" fun _ => (do
  prove ([[!x. algebraic x /\ ~rational x
       ==> ?n c. c > &0 /\ !p q. ~(q = 0) ==> abs(x - &p / &q) > c / &q pow n]])
   (REWRITE_TAC [RATIONAL_ALT] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP LIOUVILLE) THEN
    REPEAT (MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC [] THEN
    REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    ASM_MESON_TAC [LIOUVILLE, REAL_ABS_DIV, REAL_ABS_NUM])
  : ExceptT String IO thm).run
#eval LIOUVILLE_IRRATIONAL

/- ------------------------------------------------------------------------- -/
/- Liouville's constant.                                                     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 17
def liouville : thm := keep "liouville" fun _ => new_definition
 [[liouville = suminf (\n. &1 / &10 pow (FACT n))]]
#eval liouville

/- ------------------------------------------------------------------------- -/
/- Some bounds on the partial sums and hence convergence.                    -/
/- ------------------------------------------------------------------------- -/

#eval phrase 18
def LIOUVILLE_SUM_BOUND : thm := keep "LIOUVILLE_SUM_BOUND" fun _ => (do
  let h4 ← ar (← ExceptT.mk [[1 * x <= SUC n * x /\ ~(n * x = 0) ==> 1 <= SUC n * x - x]])
  let h3 ← rr (← ExceptT.mk [[a <= b ==> x <= a ==> x <= b]])
  let h2 ← ar (← ExceptT.mk [[n + SUC d = (n + 1) + d]])
  let h1 ← rr (← ExceptT.mk [[y <= x ==> &1 * x + y <= &2 * x]])
  prove ([[!d n. ~(n = 0)
         ==> sum(n..n+d) (\k. &1 / &10 pow FACT k) <= &2 / &10 pow (FACT n)]])
   (INDUCT_TAC THEN GEN_TAC THEN DISCH_TAC THENL
     [REWRITE_TAC [ADD_CLAUSES, SUM_SING_NUMSEG, real_div] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      SIMP_TAC [REAL_LE_INV_EQ, REAL_POW_LE, REAL_OF_NUM_LE, ARITH],
      ALL_TAC] THEN
    SIMP_TAC [SUM_CLAUSES_LEFT, LE_ADD] THEN REWRITE_TAC [real_div] THEN
    MATCH_MP_TAC h1 THEN
    REWRITE_TAC [h2, (← HolLight.GSYM real_div)] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[n + 1]])) THEN REWRITE_TAC [ADD_EQ_0, ARITH] THEN
    MATCH_MP_TAC h3 THEN
    SIMP_TAC [REAL_LE_LDIV_EQ, REAL_POW_LT, REAL_OF_NUM_LT, ARITH] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REWRITE_TAC [(← HolLight.GSYM real_div)] THEN
    SIMP_TAC [(← HolLight.GSYM REAL_POW_SUB), REAL_OF_NUM_EQ, ARITH, FACT_MONO, LE_ADD] THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN EXISTS_TAC ([[&10 pow 1]]) THEN
    CONJ_TAC THENL [ALL_TAC, MATCH_MP_TAC REAL_POW_MONO] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [(← HolLight.GSYM ADD1), FACT] THEN
    MATCH_MP_TAC h4 THEN
    ASM_SIMP_TAC [LE_MULT_RCANCEL, MULT_EQ_0] THEN
    REWRITE_TAC [(← HolLight.GSYM LT_NZ), FACT_LT] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval LIOUVILLE_SUM_BOUND

#eval phrase 19
def LIOUVILLE_PSUM_BOUND : thm := keep "LIOUVILLE_PSUM_BOUND" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[~(d = 0) ==> (n + d) - 1 = n + (d - 1)]])
  prove ([[!n d. ~(n = 0)
         ==> sum(n,d) (\k. &1 / &10 pow FACT k) <= &2 / &10 pow (FACT n)]])
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC ([[d = 0]]) THEN
    ASM_SIMP_TAC [SessionLibrary.Analysis.sum, REAL_LE_DIV, REAL_POW_LE, SessionLibrary.Analysis.REAL_POS] THEN
    ASM_SIMP_TAC [PSUM_SUM_NUMSEG] THEN
    ASM_SIMP_TAC [h1] THEN
    ASM_SIMP_TAC [LIOUVILLE_SUM_BOUND])
  : ExceptT String IO thm).run
#eval LIOUVILLE_PSUM_BOUND

#eval phrase 20
def LIOUVILLE_SUMS : thm := keep "LIOUVILLE_SUMS" fun _ => (do
  let h2 ← rr (← ExceptT.mk [[&1 < (n + &1 / &2) * e ==> &2 < e * (&2 * n + &1)]])
  let h1 ← rr (← ExceptT.mk [[&0 <= x /\ x <= a ==> abs x <= a]])
  prove ([[(\k. &1 / &10 pow FACT k) sums liouville]])
   (REWRITE_TAC [liouville] THEN MATCH_MP_TAC SUMMABLE_SUM THEN
    REWRITE_TAC [SER_CAUCHY] THEN X_GEN_TAC ([[e:real]]) THEN DISCH_TAC THEN
    MP_TAC (← HolLight.SPEC ([[inv(e)]]) SessionLibrary.Analysis.REAL_ARCH_SIMPLE) THEN
    DISCH_THEN (X_CHOOSE_TAC ([[N:num]])) THEN EXISTS_TAC ([[2 * N + 1]]) THEN
    REWRITE_TAC [GE] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC ([[&2 / &10 pow (FACT m)]]) THEN CONJ_TAC THENL
     [MATCH_MP_TAC h1 THEN
      ASM_SIMP_TAC [SUM_POS, REAL_LE_DIV, REAL_POW_LE, SessionLibrary.Analysis.REAL_POS] THEN
      MATCH_MP_TAC LIOUVILLE_PSUM_BOUND THEN
      UNDISCH_TAC ([[2 * N + 1 <= m]]) THEN ARITH_TAC,
      ALL_TAC] THEN
    SIMP_TAC [REAL_LT_LDIV_EQ, REAL_POW_LT, REAL_OF_NUM_LT, ARITH] THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LTE_TRANS THEN EXISTS_TAC ([[e * &(2 * N + 1)]]) THEN
    CONJ_TAC THENL
     [REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_ADD), (← HolLight.GSYM REAL_OF_NUM_MUL)] THEN
      MATCH_MP_TAC h2 THEN
      ASM_SIMP_TAC [(← HolLight.GSYM REAL_LT_LDIV_EQ), real_div, REAL_MUL_LID] THEN
      UNDISCH_TAC ([[inv(e) <= &N]]) THEN REAL_ARITH_TAC2,
      ALL_TAC] THEN
    ASM_SIMP_TAC [REAL_LE_LMUL_EQ] THEN
    REWRITE_TAC [REAL_OF_NUM_POW, REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC ([[m:num]]) THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC ([[10 EXP m]]) THEN
    REWRITE_TAC [FACT_LE_REFL, LE_EXP, ARITH] THEN SIMP_TAC [EXP_LE_REFL, ARITH])
  : ExceptT String IO thm).run
#eval LIOUVILLE_SUMS

#eval phrase 21
def LIOUVILLE_PSUM_LE : thm := keep "LIOUVILLE_PSUM_LE" fun _ => (do
  prove ([[!n. sum(0,n) (\k. &1 / &10 pow FACT k) <= liouville]])
   (GEN_TAC THEN REWRITE_TAC [suminf] THEN MATCH_MP_TAC SEQ_LE THEN
    EXISTS_TAC ([[\j:num. sum(0,n) (\k. &1 / &10 pow FACT k)]]) THEN
    EXISTS_TAC ([[\n:num. sum(0,n) (\k. &1 / &10 pow FACT k)]]) THEN
    REWRITE_TAC [SEQ_CONST, (← HolLight.GSYM sums), LIOUVILLE_SUMS] THEN
    EXISTS_TAC ([[n:num]]) THEN X_GEN_TAC ([[m:num]]) THEN SIMP_TAC [GE, LE_EXISTS] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[d:num]]) SUBST_ALL_TAC) THEN
    REWRITE_TAC [(← HolLight.GSYM SUM_SPLIT), ADD_CLAUSES, REAL_LE_ADDR] THEN
    SIMP_TAC [SUM_POS, REAL_LE_DIV, REAL_POW_LE, SessionLibrary.Analysis.REAL_POS])
  : ExceptT String IO thm).run
#eval LIOUVILLE_PSUM_LE

#eval phrase 22
def LIOUVILLE_PSUM_LT : thm := keep "LIOUVILLE_PSUM_LT" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[&0 < e ==> x + e <= y ==> x < y]])
  prove ([[!n. sum(0,n) (\k. &1 / &10 pow FACT k) < liouville]])
   (GEN_TAC THEN MP_TAC (← HolLight.SPEC ([[SUC n]]) LIOUVILLE_PSUM_LE) THEN SIMP_TAC [SessionLibrary.Analysis.sum] THEN
    MATCH_MP_TAC h1 THEN
    SIMP_TAC [REAL_LT_DIV, REAL_POW_LT, REAL_OF_NUM_LT, ARITH])
  : ExceptT String IO thm).run
#eval LIOUVILLE_PSUM_LT

#eval phrase 23
def LIOVILLE_PSUM_DIFF : thm := keep "LIOVILLE_PSUM_DIFF" fun _ => (do
  prove ([[!n. ~(n = 0)
       ==> liouville
             <= sum(0,n) (\k. &1 / &10 pow FACT k) + &2 / &10 pow (FACT n)]])
   (GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SEQ_LE THEN
    EXISTS_TAC ([[\n. sum(0,n) (\k. &1 / &10 pow FACT k)]]) THEN
    EXISTS_TAC ([[\j:num. sum (0,n) (\k. &1 / &10 pow FACT k) + &2 / &10 pow FACT n]]) THEN
    REWRITE_TAC [SEQ_CONST, (← HolLight.GSYM sums), LIOUVILLE_SUMS] THEN
    EXISTS_TAC ([[n:num]]) THEN X_GEN_TAC ([[m:num]]) THEN SIMP_TAC [GE, LE_EXISTS] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[d:num]]) SUBST_ALL_TAC) THEN
    REWRITE_TAC [(← HolLight.GSYM SUM_SPLIT), SessionLibrary.Analysis.REAL_LE_LADD] THEN
    ASM_SIMP_TAC [ADD_CLAUSES, LIOUVILLE_PSUM_BOUND])
  : ExceptT String IO thm).run
#eval LIOVILLE_PSUM_DIFF

/- ------------------------------------------------------------------------- -/
/- Main proof.                                                               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 24
def TRANSCENDENTAL_LIOUVILLE : thm := keep "TRANSCENDENTAL_LIOUVILLE" fun _ => (do
  let h7 ← ar (← ExceptT.mk [[1 <= x <=> 0 < x]])
  let h6 ← ar (← ExceptT.mk [[k = k * 1]])
  let h5 ← ar (← ExceptT.mk [[k + f * m <= SUC(m + k) * f <=> k <= (k + 1) * f]])
  let h4 ← nc (← ExceptT.mk [[1]])
  let h3 ← ar (← ExceptT.mk [[(m + k + 1) - 1 = m + k]])
  let h2 ← rr (← ExceptT.mk [[&0 <= x /\ x <= y ==> abs x <= y]])
  let h1 ← tt (← ExceptT.mk [[~(a /\ b) <=> a ==> ~b]])
  prove ([[transcendental(liouville)]])
   (REWRITE_TAC [transcendental] THEN DISCH_THEN (MP_TAC o HolLight.MATCH_MP LIOUVILLE) THEN
    REWRITE_TAC [NOT_EXISTS_THM, h1] THEN
    REWRITE_TAC [NOT_FORALL_THM, NOT_IMP] THEN
    MAP_EVERY X_GEN_TAC [([[m:num]]), ([[c:real]])] THEN
    REWRITE_TAC [DE_MORGAN_THM, real_gt, SessionLibrary.Analysis.REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC (← HolLight.SPECL [([[&10]]), ([[&2 / c]])] SessionLibrary.Analysis.REAL_ARCH_POW) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_THEN (X_CHOOSE_TAC ([[k:num]])) THEN
    ABBREV_TAC ([[n = m + k + 1]]) THEN
    EXISTS_TAC ([[nsum(0..n-1) (\i. 10 EXP (FACT(n-1) - FACT i))]]) THEN
    EXISTS_TAC ([[10 EXP (FACT(n-1))]]) THEN REWRITE_TAC [EXP_EQ_0, ARITH] THEN
    SUBGOAL_THEN ([[&(nsum(0..n-1) (\i. 10 EXP (FACT(n-1) - FACT i))) / &(10 EXP (FACT(n-1))) =
    sum(0..n-1) (\k. &1 / &10 pow (FACT k))]]) SUBST1_TAC THENL
     [REWRITE_TAC [real_div] THEN GEN_REWRITE_TAC HolLight.LAND_CONV [REAL_MUL_SYM] THEN
      REWRITE_TAC [REAL_OF_NUM_SUM_NUMSEG, (← HolLight.GSYM SUM_LMUL)] THEN
      SIMP_TAC [(← HolLight.GSYM REAL_OF_NUM_POW), REAL_POW_SUB, REAL_OF_NUM_EQ, ARITH,
               FACT_MONO, real_div, REAL_MUL_ASSOC] THEN
      SIMP_TAC [REAL_MUL_LINV, REAL_OF_NUM_EQ, REAL_POW_EQ_0, ARITH] THEN
      REWRITE_TAC [REAL_MUL_LID],
      ALL_TAC] THEN
    MP_TAC (← HolLight.GEN ([[f:num->real]]) (← HolLight.SPECL [([[f:num->real]]), ([[0]]), ([[m + k + 1]])] PSUM_SUM_NUMSEG)) THEN
    REWRITE_TAC [ADD_EQ_0, ARITH, ADD_CLAUSES] THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
        pure (REWRITE_TAC [(← HolLight.GSYM th)])) THEN
    SIMP_TAC [LIOUVILLE_PSUM_LT, SessionLibrary.Analysis.REAL_LT_IMP_NE] THEN
    MATCH_MP_TAC h2 THEN
    REWRITE_TAC [SessionLibrary.Analysis.REAL_SUB_LE, LIOUVILLE_PSUM_LE] THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN EXISTS_TAC ([[&2 / &10 pow (FACT n)]]) THEN
    REWRITE_TAC [SessionLibrary.Analysis.REAL_LE_SUB_RADD] THEN ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LIOVILLE_PSUM_DIFF THEN SessionLibrary.Analysis.EXPAND_TAC "n" THEN ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [LIOVILLE_PSUM_DIFF] THEN
    REWRITE_TAC [REAL_OF_NUM_POW, (← HolLight.GSYM EXP_MULT)] THEN
    SIMP_TAC [REAL_LE_LDIV_EQ, REAL_OF_NUM_LT, LT_NZ, EXP_EQ_0, ARITH] THEN
    REWRITE_TAC [real_div, (← HolLight.GSYM REAL_MUL_ASSOC)] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN ASM_SIMP_TAC [(← HolLight.GSYM REAL_LE_LDIV_EQ)] THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN EXISTS_TAC ([[&10 pow k]]) THEN
    ASM_SIMP_TAC [SessionLibrary.Analysis.REAL_LT_IMP_LE] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REWRITE_TAC [(← HolLight.GSYM real_div)] THEN
    SIMP_TAC [REAL_LE_RDIV_EQ, REAL_OF_NUM_LT, LT_NZ, EXP_EQ_0, ARITH] THEN
    REWRITE_TAC [REAL_OF_NUM_POW, REAL_OF_NUM_MUL, REAL_OF_NUM_LE] THEN
    REWRITE_TAC [(← HolLight.GSYM EXP_ADD), LE_EXP, ARITH_EQ] THEN SessionLibrary.Analysis.EXPAND_TAC "n" THEN
    REWRITE_TAC [h3] THEN
    REWRITE_TAC [h4, ADD_CLAUSES, FACT] THEN
    REWRITE_TAC [h5] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [h6] THEN
    MATCH_MP_TAC LE_MULT2 THEN REWRITE_TAC [LE_ADD] THEN
    REWRITE_TAC [FACT_LT, h7])
  : ExceptT String IO thm).run
#eval TRANSCENDENTAL_LIOUVILLE

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py; keep it in step with the `#eval`s above. -/
def ensure : IO Unit := once "Hol100.Liouville" do
  replay (
          SessionLibrary.Floor.ensureFloor)
  replay (
          SessionLibrary.Poly.ensurePoly)
  replay (
          algebraic)
  replay (
          transcendental)
  replay (
          REAL_INTEGER_EQ_0)
  replay (
          FACT_LE_REFL)
  replay (
          EXP_LE_REFL)
  replay (
          MVT_INEQ)
  replay (
          POLY_MULTIPLE_INTEGER)
  replay (
          SEPARATE_FINITE_SET)
  replay (
          POLY_ROOT_SEPARATE_LE)
  replay (
          POLY_ROOT_SEPARATE_LT)
  replay (
          POLY_BOUND_INTERVAL)
  replay (
          LIOUVILLE_INTERVAL)
  replay (
          LIOUVILLE)
  replay (
          LIOUVILLE_IRRATIONAL)
  replay (
          liouville)
  replay (
          LIOUVILLE_SUM_BOUND)
  replay (
          LIOUVILLE_PSUM_BOUND)
  replay (
          LIOUVILLE_SUMS)
  replay (
          LIOUVILLE_PSUM_LE)
  replay (
          LIOUVILLE_PSUM_LT)
  replay (
          LIOVILLE_PSUM_DIFF)
  replay (
          TRANSCENDENTAL_LIOUVILLE)
-- @@ENSURE END

end Hol100.Liouville
