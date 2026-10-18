/- File: HolExamples/Pell.lean
Translation of HOL Light's Examples/pell.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolExamples.Common
open HolCore.Kernel Session HolLight.Syntax HolExamples
open SessionLibrary.Prime
namespace HolExamples.Pell

/- Helpers: the session's `prove` lifted into `ExceptT String IO`, so tactic
   scripts read as the OCaml does. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private unsafe def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private unsafe def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)
private unsafe def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)
private def ec {α : Type} (x : Except String α) : ExceptT String IO α := ExceptT.mk (pure x)

-- ========================================================================= --
-- Analysis of solutions to Pell equation                                    --
-- ========================================================================= --

#eval phrase 1
-- needs "Library/analysis.ml";;
#eval SessionLibrary.Analysis.ensureAnalysis

#eval phrase 2
-- needs "Library/transc.ml";;
#eval SessionLibrary.Transc.ensureTransc

#eval phrase 3
-- needs "Library/prime.ml";;
#eval SessionLibrary.Prime.ensurePrime

#eval phrase 4
-- prioritize_real();;
#eval Session.prioritize_real

#eval phrase 5
unsafe def PELL_INDUCTION : thm := keep "PELL_INDUCTION" fun _ => (do
  prove ([[P 0 /\ P 1 /\ (!n. P n /\ P (n + 1) ==> P(n + 2)) ==> !n. P n]])
   (STRIP_TAC THEN
    SUBGOAL_THEN ([[!n. P n /\ P(n + 1)]]) (fun th => REWRITE_TAC [th]) THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC [ADD_CLAUSES] THEN
    ASM_SIMP_TAC [ADD1, (← ExceptT.mk (ARITH_RULE [[SUC(n + 1) = n + 2]]))])
  : ExceptT String IO thm).run
#eval PELL_INDUCTION

-- ------------------------------------------------------------------------- --
-- Useful number-theoretic basics                                            --
-- ------------------------------------------------------------------------- --

#eval phrase 6
unsafe def ROOT_NONPOWER : thm := keep "ROOT_NONPOWER" fun _ => (do
  prove ([[!p q d n. ~(q = 0) /\ (p EXP n = d * q EXP n) ==> ?a. d = a EXP n]])
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC [[n = 0]] THEN ASM_SIMP_TAC [EXP, MULT_CLAUSES] THEN
    STRIP_TAC THEN
    MP_TAC (SPECL [ [[n:num]], [[q:num]], [[p:num]] ] DIVIDES_EXP2_REV) THEN
    ASM_REWRITE_TAC [divides, LEFT_IMP_EXISTS_THM] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[d:num]]) THEN
    REWRITE_TAC [(← ec (EQT_INTRO (← ExceptT.mk (HolLight.SPEC_ALL MULT_SYM))))] THEN
    ONCE_REWRITE_TAC [MULT_SYM] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[a:num]]) SUBST_ALL_TAC) THEN
    EXISTS_TAC [[a:num]] THEN
    UNDISCH_TAC [[(a * q) EXP n = d * q EXP n]] THEN
    ASM_SIMP_TAC [MULT_EXP, EQ_MULT_RCANCEL, EXP_EQ_0])
  : ExceptT String IO thm).run
#eval ROOT_NONPOWER

#eval phrase 7
unsafe def INTEGER_SUB_LEMMA : thm := keep "INTEGER_SUB_LEMMA" fun _ => (do
  prove ([[!x y. ?n. (&x - &y) pow 2 = &n pow 2]])
   (REPEAT STRIP_TAC THEN
    DISJ_CASES_THEN MP_TAC (SPECL [ [[&x]], [[&y]] ] Session.REAL_LE_TOTAL) THEN
    REWRITE_TAC [REAL_OF_NUM_LE] THEN DISCH_TAC THENL
     [EXISTS_TAC [[y - x:num]], EXISTS_TAC [[x - y:num]]] THEN
    ASM_SIMP_TAC [(← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_SUB))] THEN
    REWRITE_TAC [REAL_POW_2] THEN REAL_ARITH_TAC)
  : ExceptT String IO thm).run
#eval INTEGER_SUB_LEMMA

#eval phrase 8
unsafe def SQRT_LINEAR_EQ : thm := keep "SQRT_LINEAR_EQ" fun _ => (do
  prove ([[!a u v x y.
       2 <= a
       ==> ((&u + &v * sqrt(&a pow 2 - &1) = &x + &y * sqrt(&a pow 2 - &1)) <=>
            (u = x) /\ (v = y))]])
   (REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC [] THEN
    REWRITE_TAC [(← ExceptT.mk (Session.REAL_ARITH3 [[(a + b = c + d) <=> (a - c = d - b)]]))] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_SUB_RDISTRIB))] THEN
    DISCH_THEN (MP_TAC o HolCore.Lib.C HolLight.AP_THM [[2]] o HolLight.AP_TERM [[(pow)]]) THEN
    REWRITE_TAC [REAL_POW_MUL] THEN
    ASM_SIMP_TAC [SQRT_POW_2, REAL_SUB_LE, REAL_POW_LE_1, REAL_OF_NUM_LE,
                 (← ExceptT.mk (ARITH_RULE [[2 <= a ==> 1 <= a]]))] THEN
    X_CHOOSE_TAC ([[p:num]]) (SPECL [ [[u:num]], [[x:num]] ] INTEGER_SUB_LEMMA) THEN
    X_CHOOSE_TAC ([[q:num]]) (SPECL [ [[y:num]], [[v:num]] ] INTEGER_SUB_LEMMA) THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN ([[&a pow 2 - &1 = &(a EXP 2 - 1)]]) SUBST1_TAC THENL
     [REWRITE_TAC [REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_LE)), (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_POW))] THEN
      ASM_SIMP_TAC [REAL_POW_LE_1, REAL_OF_NUM_LE,
                   (← ExceptT.mk (ARITH_RULE [[2 <= a ==> 1 <= a]]))], ALL_TAC] THEN
    REWRITE_TAC [REAL_OF_NUM_POW, REAL_OF_NUM_MUL, REAL_OF_NUM_EQ] THEN
    DISCH_TAC THEN
    MP_TAC (SPECL [ [[p:num]], [[q:num]], [[a EXP 2 - 1]], [[2]] ] ROOT_NONPOWER) THEN
    ASM_REWRITE_TAC [(← ec (EQT_INTRO (← ExceptT.mk (HolLight.SPEC_ALL MULT_SYM))))] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[~b /\ (a ==> c) ==> ((~a ==> b) ==> c)]])) THEN
    CONJ_TAC THENL
     [DISCH_THEN (X_CHOOSE_THEN ([[b:num]]) MP_TAC) THEN
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP
       (← ExceptT.mk (ARITH_RULE [[(a - 1 = b) ==> 1 < a ==> (a - b = 1)]]))) THEN
      SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← ExceptT.mk (HolLight.SPEC ([[a:num]]) (CONJUNCT1 EXP))))) THEN
      ASM_REWRITE_TAC [LT_EXP, ARITH_LE, ARITH_LT] THEN
      REWRITE_TAC [EXP] THEN
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← ExceptT.mk (ARITH_RULE
        [[(a - b = 1) ==> (a = b + 1)]]))) THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_EQ)), (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_ADD)),
                  (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_POW))] THEN
      REWRITE_TAC [REAL_POW_2] THEN
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP
       (← ExceptT.mk (Session.REAL_ARITH3 [[(a * a = b * b + &1) ==> ((a + b) * (a - b) = &1)]]))) THEN
      DISCH_THEN (MP_TAC o HolCore.Lib.C HolLight.AP_THM [[2]] o HolLight.AP_TERM [[(pow)]]) THEN
      REWRITE_TAC [REAL_POW_MUL] THEN
      X_CHOOSE_TAC ([[c:num]]) (SPECL [ [[a:num]], [[b:num]] ] INTEGER_SUB_LEMMA) THEN
      ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_POW_MUL))] THEN
      REWRITE_TAC [REAL_OF_NUM_POW, REAL_OF_NUM_MUL, REAL_OF_NUM_ADD] THEN
      REWRITE_TAC [REAL_OF_NUM_EQ, EXP_ONE, EXP_EQ_1, MULT_EQ_1, ARITH_EQ] THEN
      UNDISCH_TAC [[2 <= a]] THEN ARITH_TAC,
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC [[p EXP 2 = 0 EXP 2 * (a EXP 2 - 1)]] THEN
      REWRITE_TAC [ARITH, MULT_CLAUSES, EXP_EQ_0] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC [[(&u - &x) pow 2 = &0 pow 2]] THEN
      UNDISCH_TAC [[(&y - &v) pow 2 = &0 pow 2]] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC [REAL_POW_EQ_0, ARITH_EQ, REAL_SUB_0] THEN
      SIMP_TAC [REAL_OF_NUM_EQ]])
  : ExceptT String IO thm).run
#eval SQRT_LINEAR_EQ

-- ------------------------------------------------------------------------- --
-- Recurrence defining the solutions.                                        --
-- ------------------------------------------------------------------------- --

#eval phrase 9
unsafe def X_DEF : thm := keep "X_DEF" fun _ => (do
  let th ← prove ([[!a. ?X. !n. X n = if n = 0 then 1
                       else if n = 1 then a
                       else 2 * a * X(n-1) - X(n-2)]])
   (GEN_TAC THEN MATCH_MP_TAC (← ExceptT.mk (HolLight.MATCH_MP WF_REC WF_num)) THEN
    REPEAT STRIP_TAC THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    BINOP_TAC THEN
    ASM_SIMP_TAC [(← ar [[n - m < n <=> ~(m = 0) /\ ~(n = 0)]]), ARITH_EQ])
  ExceptT.mk (new_specification ["X"] (← ExceptT.mk (REWRITE_RULE [SKOLEM_THM] th)))
  : ExceptT String IO thm).run
#eval X_DEF

#eval phrase 10
unsafe def X_CLAUSES : thm := keep "X_CLAUSES" fun _ => (do
  prove ([[(!a. X a 0 = 1) /\
   (!a. X a 1 = a) /\
   (!a n. X a (n + 2) = 2 * a * X a (n + 1) - X a (n))]])
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC HolLight.LAND_CONV [X_DEF] THEN
    REWRITE_TAC [ARITH_EQ, ADD_EQ_0, (← ar [[~(n + 2 = 1)]])] THEN
    REWRITE_TAC [(← ar [[((n + 2) - 2 = n) /\ ((n + 2) - 1 = n + 1)]])])
  : ExceptT String IO thm).run
#eval X_CLAUSES

#eval phrase 11
unsafe def Y_DEF : thm := keep "Y_DEF" fun _ => (do
  let th ← prove ([[!a. ?Y. !n. Y n = if n = 0 then 0
                       else if n = 1 then 1
                       else 2 * a * Y(n-1) - Y(n-2)]])
   (GEN_TAC THEN MATCH_MP_TAC (← ExceptT.mk (HolLight.MATCH_MP WF_REC WF_num)) THEN
    REPEAT STRIP_TAC THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    BINOP_TAC THEN
    ASM_SIMP_TAC [(← ar [[n - m < n <=> ~(m = 0) /\ ~(n = 0)]]), ARITH_EQ])
  ExceptT.mk (new_specification ["Y"] (← ExceptT.mk (REWRITE_RULE [SKOLEM_THM] th)))
  : ExceptT String IO thm).run
#eval Y_DEF

#eval phrase 12
unsafe def Y_CLAUSES : thm := keep "Y_CLAUSES" fun _ => (do
  prove ([[(!a. Y a 0 = 0) /\
   (!a. Y a 1 = 1) /\
   (!a n. Y a (n + 2) = 2 * a * Y a (n + 1) - Y a (n))]])
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC HolLight.LAND_CONV [Y_DEF] THEN
    REWRITE_TAC [ARITH_EQ, ADD_EQ_0, (← ar [[~(n + 2 = 1)]])] THEN
    REWRITE_TAC [(← ar [[((n + 2) - 2 = n) /\ ((n + 2) - 1 = n + 1)]])])
  : ExceptT String IO thm).run
#eval Y_CLAUSES

-- ------------------------------------------------------------------------- --
-- An obvious but tiresome lemma: the Xs and Ys increase.                    --
-- ------------------------------------------------------------------------- --

#eval phrase 13
unsafe def X_INCREASES : thm := keep "X_INCREASES" fun _ => (do
  prove ([[!a n. ~(a = 0) ==> X a n <= X a (n + 1)]])
   (GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC num_WF THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC [[n = 0]] THEN
    ASM_REWRITE_TAC [X_CLAUSES, ADD_CLAUSES,
      (← ar [[1 <= a <=> ~(a = 0)]])] THEN
    GEN_REWRITE_TAC HolLight.RAND_CONV [X_DEF] THEN
    ASM_REWRITE_TAC [ADD_EQ_0, ARITH_EQ,
      (← ar [[(n + 1 = 1) <=> (n = 0)]])] THEN
    REWRITE_TAC [ADD_SUB] THEN
    MATCH_MP_TAC (← ar [[a + b <= c ==> a <= c - b:num]]) THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC [[2 * X a n]] THEN CONJ_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [LE_MULT_LCANCEL, ARITH_EQ] THEN
      UNDISCH_TAC [[~(a = 0)]] THEN SPEC_TAC ([[a:num]], [[a:num]]) THEN
      INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES, MULT_CLAUSES] THEN
      REWRITE_TAC [(← ar [[a <= b + a:num]])]] THEN
    MATCH_MP_TAC (← ar [[b <= a ==> a + b <= 2 * a]]) THEN
    SUBGOAL_THEN ([[n = (n - 1) + 1]]) SUBST1_TAC THENL
     [UNDISCH_TAC [[~(n = 0)]] THEN ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [(← ar [[((n + 1) + 1) - 2 = n]])] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC [[~(n = 0)]] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval X_INCREASES

#eval phrase 14
unsafe def Y_INCREASES : thm := keep "Y_INCREASES" fun _ => (do
  prove ([[!a n. ~(a = 0) ==> Y a n <= Y a (n + 1)]])
   (GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC num_WF THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC [[n = 0]] THEN
    ASM_REWRITE_TAC [Y_CLAUSES, ADD_CLAUSES, LE_0] THEN
    GEN_REWRITE_TAC HolLight.RAND_CONV [Y_DEF] THEN
    ASM_REWRITE_TAC [ADD_EQ_0, ARITH_EQ,
      (← ar [[(n + 1 = 1) <=> (n = 0)]])] THEN
    REWRITE_TAC [ADD_SUB] THEN
    MATCH_MP_TAC (← ar [[a + b <= c ==> a <= c - b:num]]) THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC [[2 * Y a n]] THEN CONJ_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [LE_MULT_LCANCEL, ARITH_EQ] THEN
      UNDISCH_TAC [[~(a = 0)]] THEN SPEC_TAC ([[a:num]], [[a:num]]) THEN
      INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES, MULT_CLAUSES] THEN
      REWRITE_TAC [(← ar [[a <= b + a:num]])]] THEN
    MATCH_MP_TAC (← ar [[b <= a ==> a + b <= 2 * a]]) THEN
    SUBGOAL_THEN ([[n = (n - 1) + 1]]) SUBST1_TAC THENL
     [UNDISCH_TAC [[~(n = 0)]] THEN ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [(← ar [[((n + 1) + 1) - 2 = n]])] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC [[~(n = 0)]] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval Y_INCREASES

-- ------------------------------------------------------------------------- --
-- Show that the expression is a power of the basis.                         --
-- ------------------------------------------------------------------------- --

#eval phrase 15
unsafe def XY_POWER_POS : thm := keep "XY_POWER_POS" fun _ => (do
  prove ([[!a n. ~(a = 0) ==> (&(X a n) + &(Y a n) * sqrt(&a pow 2 - &1) =
                       (&a + sqrt(&a pow 2 - &1)) pow n)]])
   (GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC num_WF THEN GEN_TAC THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC [X_DEF, Y_DEF] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [ARITH_EQ] THEN
    REWRITE_TAC [REAL_MUL_LZERO, REAL_ADD_RID, real_pow] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_POW_1, REAL_MUL_LID] THEN
    REWRITE_TAC [REAL_OF_NUM_ADD] THEN
    SUBGOAL_THEN
     ([[(&(2 * a * X a (n - 1) - X a (n - 2)) =
     &(2 * a * X a (n - 1)) - &(X a (n - 2))) /\
    (&(2 * a * Y a (n - 1) - Y a (n - 2)) =
     &(2 * a * Y a (n - 1)) - &(Y a (n - 2)))]])
     (CONJUNCTS_THEN SUBST1_TAC)
    THENL
     [CONJ_TAC THEN MATCH_MP_TAC (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_SUB)) THEN
      MATCH_MP_TAC (← ar
       [[x <= y /\ y <= 2 * a * y ==> x <= 2 * a * y]]) THEN
      ASM_SIMP_TAC [(← ar
       [[~(n = 0) /\ ~(n = 1) ==> (n - 1 = (n - 2) + 1)]])] THEN
      ASM_SIMP_TAC [X_INCREASES, Y_INCREASES] THEN
      REWRITE_TAC [MULT_ASSOC] THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [(← ar [[n = 1 * n]])] THEN
      REWRITE_TAC [LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
      UNDISCH_TAC [[~(a = 0)]] THEN ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [(← rr
     [[(x1 - x2) + (y1 - y2) * a = (x1 + y1 * a) - (x2 + y2 * a)]])] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_MUL))] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_MUL_ASSOC)), (← ExceptT.mk (HolLight.GSYM REAL_ADD_LDISTRIB))] THEN
    ASM_SIMP_TAC [(← ar
     [[~(n = 0) /\ ~(n = 1) ==> n - 2 < n /\ n - 1 < n]])] THEN
    ASM_SIMP_TAC [(← ar
       [[~(n = 0) /\ ~(n = 1) ==> (n - 1 = 1 + (n - 2))]])] THEN
    REWRITE_TAC [REAL_POW_ADD, REAL_MUL_ASSOC, REAL_POW_1] THEN
    REWRITE_TAC [(← rr [[a * b - b = (a - &1) * b]])] THEN
    SUBGOAL_THEN ([[n = 2 + (n - 2)]])
      (fun th => GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.RAND_CONV) [th])
    THENL
     [MAP_EVERY UNDISCH_TAC [ [[~(n = 0)]], [[~(n = 1)]] ] THEN ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [REAL_POW_ADD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [REAL_POW_2, REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_POW_2))] THEN
    ASM_SIMP_TAC [(← ExceptT.mk (HolLight.GSYM REAL_POW_2)), SQRT_POW_2, REAL_SUB_LE,
                 REAL_POW_LE_1, REAL_OF_NUM_LE,
                 (← ar [[1 <= a <=> ~(a = 0)]])] THEN
    REWRITE_TAC [REAL_POW_2] THEN REAL_ARITH_TAC)
  : ExceptT String IO thm).run
#eval XY_POWER_POS

#eval phrase 16
unsafe def XY_POWER_NEG : thm := keep "XY_POWER_NEG" fun _ => (do
  prove ([[!a n. ~(a = 0) ==> (&(X a n) - &(Y a n) * sqrt(&a pow 2 - &1) =
                       (&a - sqrt(&a pow 2 - &1)) pow n)]])
   (GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC num_WF THEN GEN_TAC THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC [X_DEF, Y_DEF] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [ARITH_EQ] THEN
    REWRITE_TAC [REAL_MUL_LZERO, REAL_SUB_RZERO, real_pow] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_POW_1, REAL_MUL_LID] THEN
    REWRITE_TAC [REAL_OF_NUM_ADD] THEN
    SUBGOAL_THEN
     ([[(&(2 * a * X a (n - 1) - X a (n - 2)) =
     &(2 * a * X a (n - 1)) - &(X a (n - 2))) /\
    (&(2 * a * Y a (n - 1) - Y a (n - 2)) =
     &(2 * a * Y a (n - 1)) - &(Y a (n - 2)))]])
     (CONJUNCTS_THEN SUBST1_TAC)
    THENL
     [CONJ_TAC THEN MATCH_MP_TAC (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_SUB)) THEN
      MATCH_MP_TAC (← ar
       [[x <= y /\ y <= 2 * a * y ==> x <= 2 * a * y]]) THEN
      ASM_SIMP_TAC [(← ar
       [[~(n = 0) /\ ~(n = 1) ==> (n - 1 = (n - 2) + 1)]])] THEN
      ASM_SIMP_TAC [X_INCREASES, Y_INCREASES] THEN
      REWRITE_TAC [MULT_ASSOC] THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [(← ar [[n = 1 * n]])] THEN
      REWRITE_TAC [LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
      UNDISCH_TAC [[~(a = 0)]] THEN ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [(← rr
     [[(x1 - x2) - (y1 - y2) * a = (x1 - y1 * a) - (x2 - y2 * a)]])] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_MUL))] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_MUL_ASSOC)), (← ExceptT.mk (HolLight.GSYM REAL_SUB_LDISTRIB))] THEN
    ASM_SIMP_TAC [(← ar
     [[~(n = 0) /\ ~(n = 1) ==> n - 2 < n /\ n - 1 < n]])] THEN
    ASM_SIMP_TAC [(← ar
       [[~(n = 0) /\ ~(n = 1) ==> (n - 1 = 1 + (n - 2))]])] THEN
    REWRITE_TAC [REAL_POW_ADD, REAL_MUL_ASSOC, REAL_POW_1] THEN
    REWRITE_TAC [(← rr [[a * b - b = (a - &1) * b]])] THEN
    SUBGOAL_THEN ([[n = 2 + (n - 2)]])
      (fun th => GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.RAND_CONV) [th])
    THENL
     [MAP_EVERY UNDISCH_TAC [ [[~(n = 0)]], [[~(n = 1)]] ] THEN ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [REAL_POW_ADD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [REAL_POW_2, REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_POW_2))] THEN
    ASM_SIMP_TAC [(← ExceptT.mk (HolLight.GSYM REAL_POW_2)), SQRT_POW_2, REAL_SUB_LE,
                 REAL_POW_LE_1, REAL_OF_NUM_LE,
                 (← ar [[1 <= a <=> ~(a = 0)]])] THEN
    REWRITE_TAC [REAL_POW_2] THEN REAL_ARITH_TAC)
  : ExceptT String IO thm).run
#eval XY_POWER_NEG

-- ------------------------------------------------------------------------- --
-- Hence all members of recurrence relations are Pell solutions.             --
-- ------------------------------------------------------------------------- --

#eval phrase 17
unsafe def XY_ARE_SOLUTIONS : thm := keep "XY_ARE_SOLUTIONS" fun _ => (do
  prove ([[!a n. ~(a = 0)
         ==> ((X a n) EXP 2 = (a EXP 2 - 1) * (Y a n) EXP 2 + 1)]])
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o HolLight.SPEC ([[n:num]]) o HolLight.MATCH_MP XY_POWER_NEG) THEN
    FIRST_ASSUM (MP_TAC o HolLight.SPEC ([[n:num]]) o HolLight.MATCH_MP XY_POWER_POS) THEN
    REWRITE_TAC [IMP_IMP] THEN
    DISCH_THEN (fun th =>
     MP_TAC (HolCore.Kernel.MK_COMB (HolCore.Equal.AP_TERM ([[( * )]]) (CONJUNCT1 th)) (CONJUNCT2 th))) THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_POW_MUL))] THEN
    REWRITE_TAC [(← rr [[(x + y) * (x - y) = x * x - y * y]])] THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (AC REAL_MUL_AC
      [[(a * b) * (c * d) = (a * c) * (b * d)]]))] THEN
    ASM_SIMP_TAC [(← ExceptT.mk (HolLight.GSYM REAL_POW_2)), SQRT_POW_2, REAL_SUB_LE,
                 REAL_POW_LE_1, REAL_OF_NUM_LE,
                 (← ar [[1 <= a <=> ~(a = 0)]])] THEN
    REWRITE_TAC [(← rr [[a - (a - &1) = &1]]), REAL_POW_ONE] THEN
    REWRITE_TAC [REAL_EQ_SUB_RADD] THEN
    SUBGOAL_THEN ([[&a pow 2 - &1 = &(a EXP 2 - 1)]]) SUBST1_TAC THENL
     [REWRITE_TAC [REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_LE)), (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_POW))] THEN
      ASM_SIMP_TAC [REAL_POW_LE_1, REAL_OF_NUM_LE,
                   (← ar [[1 <= a <=> ~(a = 0)]])],
      REWRITE_TAC [REAL_OF_NUM_ADD, REAL_OF_NUM_MUL, REAL_OF_NUM_EQ,
                  REAL_OF_NUM_POW] THEN
      REWRITE_TAC [MULT_AC, ADD_AC]])
  : ExceptT String IO thm).run
#eval XY_ARE_SOLUTIONS

-- ------------------------------------------------------------------------- --
-- And they are all solutions.                                               --
-- ------------------------------------------------------------------------- --

#eval phrase 18
unsafe def X_DEGENERATE : thm := keep "X_DEGENERATE" fun _ => (do
  prove ([[!n. X 1 n = 1]])
   (MATCH_MP_TAC PELL_INDUCTION THEN SIMP_TAC [X_CLAUSES, ARITH])
  : ExceptT String IO thm).run
#eval X_DEGENERATE

#eval phrase 19
unsafe def Y_DEGENERATE : thm := keep "Y_DEGENERATE" fun _ => (do
  prove ([[!n. Y 1 n = n]])
   (MATCH_MP_TAC PELL_INDUCTION THEN SIMP_TAC [Y_CLAUSES] THEN
    REPEAT STRIP_TAC THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval Y_DEGENERATE

#eval phrase 20
unsafe def REAL_ARCH_POW_MINIMAL : thm := keep "REAL_ARCH_POW_MINIMAL" fun _ => (do
  prove ([[!x y. &1 < x /\ &1 < y
         ==> ?n. x pow n <= y /\ y < x pow (SUC n)]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (SPEC ([[ln(x)]]) SessionLibrary.Analysis.REAL_ARCH_LEAST) THEN
    ASM_SIMP_TAC [SessionLibrary.Transc.LN_POS_LT] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[ln(y)]]) THEN
    ASM_SIMP_TAC [SessionLibrary.Transc.LN_POS_LT, REAL_LT_IMP_LE] THEN
    ASM_SIMP_TAC [(← ExceptT.mk (HolLight.GSYM SessionLibrary.Transc.LN_POW)), (← rr [[&1 < x ==> &0 < x]]),
                 REAL_POW_LT, SessionLibrary.Transc.LN_MONO_LT, SessionLibrary.Transc.LN_MONO_LE])
  : ExceptT String IO thm).run
#eval REAL_ARCH_POW_MINIMAL

#eval phrase 21
unsafe def SOLUTIONS_INDUCTION : thm := keep "SOLUTIONS_INDUCTION" fun _ => (do
  prove ([[!a x y.
        ~(a = 0) /\ ~(a = 1) /\ ~(y = 0) /\
        (x EXP 2 = (a EXP 2 - 1) * y EXP 2 + 1)
        ==> ?x' y'. x' < x /\ y' < y /\
                    (x' EXP 2 = (a EXP 2 - 1) * y' EXP 2 + 1) /\
                    (&x + &y * sqrt(&a pow 2 - &1) =
                     (&x' + &y' * sqrt(&a pow 2 - &1)) *
                     (&a + sqrt(&a pow 2 - &1)))]])
   (REPEAT STRIP_TAC THEN
    EXISTS_TAC [[a * x - (a EXP 2 - 1) * y]] THEN
    EXISTS_TAC [[a * y - x:num]] THEN
    SUBGOAL_THEN ([[x <= a * y:num]]) ASSUME_TAC THENL
     [ONCE_REWRITE_TAC [(← ExceptT.mk (HolLight.SYM (← ExceptT.mk (REWRITE_RULE [NOT_SUC]
        (← ExceptT.mk (HolLight.SPECL [ [[x:num]], [[y:num]], [[SUC 1]] ] EXP_MONO_LE))))))] THEN
      ASM_REWRITE_TAC [ARITH_SUC] THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM ADD1)), LE_SUC_LT] THEN
      REWRITE_TAC [MULT_EXP, LT_MULT_RCANCEL] THEN
      REWRITE_TAC [(← ar [[a - 1 < a <=> ~(a = 0)]])] THEN
      ASM_REWRITE_TAC [EXP_EQ_0], ALL_TAC] THEN
    SUBGOAL_THEN ([[(a EXP 2 - 1) * y <= a * x:num]]) ASSUME_TAC THENL
     [SUBGOAL_THEN ([[(a EXP 2 - 1) * y EXP 2 < a * x * y]]) MP_TAC THENL
       [ALL_TAC,
        ASM_SIMP_TAC [MULT_ASSOC, EXP_2, LT_MULT_RCANCEL, LT_IMP_LE]] THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM LE_SUC_LT)), ADD1] THEN
      FIRST_ASSUM (fun th => HolLight.tactic_of do
        let s ← HolLight.SYM th
        pure (GEN_REWRITE_TAC HolLight.LAND_CONV [s])) THEN
      GEN_REWRITE_TAC HolLight.RAND_CONV [MULT_SYM] THEN
      REWRITE_TAC [EXP_2, (← ExceptT.mk (HolLight.GSYM MULT_ASSOC)), LE_MULT_LCANCEL] THEN
      DISJ2_TAC THEN ONCE_REWRITE_TAC [MULT_SYM] THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    MATCH_MP_TAC (← tt [[d /\ (d ==> a /\ b /\ c)
                     ==> a /\ b /\ c /\ d]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_RCANCEL_IMP THEN
      EXISTS_TAC [[&a - sqrt(&a pow 2 - &1)]] THEN CONJ_TAC THENL
       [REWRITE_TAC [REAL_SUB_0] THEN
        DISCH_THEN (MP_TAC o HolCore.Lib.C HolLight.AP_THM [[2]] o HolLight.AP_TERM ([[(pow)]])) THEN
        ASM_SIMP_TAC [SQRT_POW_2, REAL_SUB_LE, REAL_POW_LE_1, REAL_OF_NUM_LE,
                     (← ar [[~(a = 0) ==> 1 <= a]])] THEN
        REAL_ARITH_TAC, ALL_TAC] THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_MUL_ASSOC))] THEN
      REWRITE_TAC [(← rr [[(a + b) * (a - b) = a * a - b * b]])] THEN
      ASM_SIMP_TAC [(← ExceptT.mk (HolLight.GSYM REAL_POW_2)), SQRT_POW_2, REAL_SUB_LE, REAL_POW_LE_1,
                   REAL_OF_NUM_LE, (← ar [[~(a = 0) ==> 1 <= a]])] THEN
      REWRITE_TAC [(← rr [[a - (a - b) = b]]), REAL_MUL_RID] THEN
      ASM_SIMP_TAC [(← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_SUB))] THEN
      REWRITE_TAC [(← rr
       [[(x + y * s) * (a - s) = (a * x - (s * s) * y) + (a * y - x) * s]])] THEN
      ASM_SIMP_TAC [(← ExceptT.mk (HolLight.GSYM REAL_POW_2)), SQRT_POW_2, REAL_SUB_LE, REAL_POW_LE_1,
                   REAL_OF_NUM_LE, (← ar [[~(a = 0) ==> 1 <= a]])] THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_MUL))] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC [REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_LE)), (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_POW))] THEN
      ASM_SIMP_TAC [REAL_POW_LE_1, REAL_OF_NUM_LE,
                   (← ar [[~(a = 0) ==> 1 <= a]])], ALL_TAC] THEN
    DISCH_THEN (fun th => ASSUME_TAC th THEN MP_TAC th) THEN
    SUBGOAL_THEN
     ([[(&x - &y * sqrt(&a pow 2 - &1)) =
    (&(a * x - (a EXP 2 - 1) * y) - &(a * y - x) * sqrt (&a pow 2 - &1)) *
    (&a - sqrt(&a pow 2 - &1))]])
    MP_TAC THENL
     [MATCH_MP_TAC REAL_EQ_RCANCEL_IMP THEN
      EXISTS_TAC [[&a + sqrt(&a pow 2 - &1)]] THEN CONJ_TAC THENL
       [MATCH_MP_TAC (← rr [[~(a = --b) ==> ~(a + b = &0)]]) THEN
        DISCH_THEN (MP_TAC o HolCore.Lib.C HolLight.AP_THM [[2]] o HolLight.AP_TERM ([[(pow)]])) THEN
        REWRITE_TAC [REAL_POW_NEG, ARITH] THEN
        ASM_SIMP_TAC [SQRT_POW_2, REAL_SUB_LE, REAL_POW_LE_1, REAL_OF_NUM_LE,
                     (← ar [[~(a = 0) ==> 1 <= a]])] THEN
        REAL_ARITH_TAC, ALL_TAC] THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_MUL_ASSOC))] THEN
      REWRITE_TAC [(← rr [[(a - b) * (a + b) = a * a - b * b]])] THEN
      ASM_SIMP_TAC [(← ExceptT.mk (HolLight.GSYM REAL_POW_2)), SQRT_POW_2, REAL_SUB_LE, REAL_POW_LE_1,
                   REAL_OF_NUM_LE, (← ar [[~(a = 0) ==> 1 <= a]])] THEN
      REWRITE_TAC [(← rr [[a - (a - b) = b]]), REAL_MUL_RID] THEN
      ASM_SIMP_TAC [(← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_SUB))] THEN
      REWRITE_TAC [(← rr
       [[(x - y * s) * (a + s) = (a * x - (s * s) * y) - (a * y - x) * s]])] THEN
      ASM_SIMP_TAC [(← ExceptT.mk (HolLight.GSYM REAL_POW_2)), SQRT_POW_2, REAL_SUB_LE, REAL_POW_LE_1,
                   REAL_OF_NUM_LE, (← ar [[~(a = 0) ==> 1 <= a]])] THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_MUL))] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC [REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_LE)), (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_POW))] THEN
      ASM_SIMP_TAC [REAL_POW_LE_1, REAL_OF_NUM_LE,
                   (← ar [[~(a = 0) ==> 1 <= a]])], ALL_TAC] THEN
    DISCH_THEN (fun th1 => DISCH_THEN (fun th2 =>
     MP_TAC (HolCore.Kernel.MK_COMB (HolCore.Equal.AP_TERM ([[( * )]]) th1) th2))) THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (AC REAL_MUL_AC
     [[(a * b) * (c * d) = (c * a) * (d * b)]]))] THEN
    REWRITE_TAC [(← rr [[(a + b) * (a - b) = a * a - b * b]])] THEN
    REWRITE_TAC [(← rr [[(a - b) * (a + b) = a * a - b * b]])] THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (AC REAL_MUL_AC
     [[(a * b) * (c * b) = (c * a) * (b * b)]]))] THEN
    ASM_SIMP_TAC [(← ExceptT.mk (HolLight.GSYM REAL_POW_2)), SQRT_POW_2, REAL_SUB_LE, REAL_POW_LE_1,
                 REAL_OF_NUM_LE, (← ar [[~(a = 0) ==> 1 <= a]])] THEN
    REWRITE_TAC [(← rr [[a - (a - b) = b]]), REAL_MUL_RID] THEN
    ASM_REWRITE_TAC [REAL_OF_NUM_POW] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_POW)), (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_ADD)),
                (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_MUL))] THEN
    SUBGOAL_THEN ([[&a pow 2 - &1 = &(a EXP 2 - 1)]]) (SUBST1_TAC o HolLight.SYM) THENL
     [REWRITE_TAC [REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_LE)), (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_POW))] THEN
      ASM_SIMP_TAC [REAL_POW_LE_1, REAL_OF_NUM_LE,
                   (← ar [[~(a = 0) ==> 1 <= a]])], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← rr
     [[((a * b + &1) - b * a = x - y) ==> (x = y + &1)]])) THEN
    SUBGOAL_THEN ([[&a pow 2 - &1 = &(a EXP 2 - 1)]]) SUBST1_TAC THENL
     [REWRITE_TAC [REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_LE)), (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_POW))] THEN
      ASM_SIMP_TAC [REAL_POW_LE_1, REAL_OF_NUM_LE,
                   (← ar [[~(a = 0) ==> 1 <= a]])], ALL_TAC] THEN
    ASM_SIMP_TAC [REAL_OF_NUM_SUB, REAL_OF_NUM_ADD, REAL_OF_NUM_EQ,
                 REAL_OF_NUM_POW, REAL_OF_NUM_MUL] THEN
    ABBREV_TAC [[u = a * x - (a EXP 2 - 1) * y]] THEN
    ABBREV_TAC [[v = a * y - x:num]] THEN
    DISCH_THEN (ASSUME_TAC o HolLight.ONCE_REWRITE_RULE [MULT_SYM]) THEN
    REWRITE_TAC [MULT_AC] THEN
    MATCH_MP_TAC (← tt [[(a <=> b) /\ (~a /\ ~b ==> F) ==> a /\ b]]) THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC HolLight.LAND_CONV
       [(← ExceptT.mk (HolLight.SYM (← ExceptT.mk (REWRITE_RULE [NOT_SUC]
        (← ExceptT.mk (HolLight.SPECL [ [[x:num]], [[y:num]], [[SUC 1]] ] EXP_MONO_LT))))))] THEN
      ASM_REWRITE_TAC [ARITH_SUC] THEN
      REWRITE_TAC [LT_ADD_RCANCEL, LT_MULT_LCANCEL] THEN
      REWRITE_TAC [(← ExceptT.mk (num_CONV [[2]])), EXP_MONO_LT, NOT_SUC] THEN
      MATCH_MP_TAC (← tt [[a ==> (a /\ b <=> b)]]) THEN
      REWRITE_TAC [SUB_EQ_0, ARITH_SUC, NOT_LE] THEN
      SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← ExceptT.mk (HolLight.SPEC ([[a:num]]) (CONJUNCT1 EXP))))) THEN
      REWRITE_TAC [LT_EXP] THEN REWRITE_TAC [ARITH] THEN
      MATCH_MP_TAC (← ar [[~(a = 0) /\ ~(a = 1) ==> 2 <= a]]) THEN
      ASM_REWRITE_TAC [], ALL_TAC] THEN
    REWRITE_TAC [NOT_LT] THEN STRIP_TAC THEN
    UNDISCH_TAC
     [[&x + &y * sqrt (&a pow 2 - &1) =
    (&u + &v * sqrt (&a pow 2 - &1)) * (&a + sqrt (&a pow 2 - &1))]] THEN
    REWRITE_TAC [] THEN
    MATCH_MP_TAC (← rr [[a < b ==> ~(a = b)]]) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC [[(&u + &v * sqrt (&a pow 2 - &1)) * &1]] THEN CONJ_TAC THENL
     [REWRITE_TAC [REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
      ASM_REWRITE_TAC [REAL_OF_NUM_LE] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC [REAL_OF_NUM_LE, SQRT_POS_LE, REAL_POW_LE_1,
                   REAL_SUB_LE, (← ar [[~(a = 0) ==> 1 <= a]])],
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
       [REWRITE_TAC [REAL_OF_NUM_LT, LT_NZ] THEN DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC [[0 EXP 2 = (a EXP 2 - 1) * v EXP 2 + 1]] THEN
        DISCH_THEN (MP_TAC o HolLight.SYM) THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC [ADD_EQ_0, ARITH_EQ], ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC [REAL_POS] THEN
      ASM_SIMP_TAC [REAL_OF_NUM_LE, SQRT_POS_LE, REAL_POW_LE_1,
                   REAL_SUB_LE, (← ar [[~(a = 0) ==> 1 <= a]])],
      ALL_TAC] THEN
    MATCH_MP_TAC (← rr [[&1 < x /\ &0 <= y ==> &1 < x + y]]) THEN
    ASM_SIMP_TAC [REAL_OF_NUM_LE, SQRT_POS_LE, REAL_POW_LE_1,
                 REAL_SUB_LE, (← ar [[~(a = 0) ==> 1 <= a]])] THEN
    REWRITE_TAC [REAL_OF_NUM_LT] THEN
    MATCH_MP_TAC (← ar [[~(a = 0) /\ ~(a = 1) ==> 1 < a]]) THEN
    ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval SOLUTIONS_INDUCTION

#eval phrase 22
unsafe def SOLUTIONS_ARE_XY : thm := keep "SOLUTIONS_ARE_XY" fun _ => (do
  prove ([[!a x y.
    ~(a = 0) /\
    (x EXP 2 = (a EXP 2 - 1) * y EXP 2 + 1)
    ==> ?n. (x = X a n) /\ (y = Y a n)]])
   (REPEAT GEN_TAC THEN ASM_CASES_TAC [[a = 1]] THENL
     [ASM_REWRITE_TAC [ARITH, MULT_CLAUSES, ADD_CLAUSES, EXP_2] THEN
      SIMP_TAC [MULT_EQ_1, X_DEGENERATE, Y_DEGENERATE, (← ExceptT.mk (HolLight.GSYM EXISTS_REFL))],
      ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN ([[?n. &x + &y * sqrt(&a pow 2 - &1) =
                    (&a + sqrt(&a pow 2 - &1)) pow n]])
    MP_TAC THENL
     [UNDISCH_TAC [[x EXP 2 = (a EXP 2 - 1) * y EXP 2 + 1]] THEN
      SPEC_TAC ([[x:num]], [[x:num]]) THEN SPEC_TAC ([[y:num]], [[y:num]]) THEN
      MATCH_MP_TAC num_WF THEN X_GEN_TAC [[y0:num]] THEN DISCH_TAC THEN
      X_GEN_TAC [[x0:num]] THEN
      ASM_CASES_TAC [[y0 = 0]] THENL
       [ASM_REWRITE_TAC [EXP_2, MULT_CLAUSES, ADD_CLAUSES, MULT_EQ_1] THEN
        DISCH_THEN SUBST1_TAC THEN EXISTS_TAC [[0]] THEN
        REWRITE_TAC [REAL_MUL_LZERO, REAL_ADD_RID, real_pow], ALL_TAC] THEN
      DISCH_TAC THEN
      MP_TAC (SPECL [ [[a:num]], [[x0:num]], [[y0:num]] ] SOLUTIONS_INDUCTION) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[x1:num]]) (X_CHOOSE_THEN ([[y1:num]])
          STRIP_ASSUME_TAC)) THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[y1:num]]) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC [[x1:num]]) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[n:num]]) SUBST1_TAC) THEN
      EXISTS_TAC [[SUC n]] THEN REWRITE_TAC [real_pow, REAL_MUL_AC], ALL_TAC] THEN
    ASM_SIMP_TAC [(← ExceptT.mk (HolLight.GSYM XY_POWER_POS))] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC [[n:num]] THEN
    ASM_SIMP_TAC [SQRT_LINEAR_EQ,
                 (← ar [[~(a = 0) /\ ~(a = 1) ==> 2 <= a]])])
  : ExceptT String IO thm).run
#eval SOLUTIONS_ARE_XY

-- ------------------------------------------------------------------------- --
-- Addition formulas.                                                        --
-- ------------------------------------------------------------------------- --

#eval phrase 23
unsafe def ADDITION_FORMULA_POS : thm := keep "ADDITION_FORMULA_POS" fun _ => (do
  prove ([[!a m n.
     ~(a = 0)
     ==> ((X a (m + n) = X a m * X a n + (a EXP 2 - 1) * Y a m * Y a n) /\
          (Y a (m + n) = X a m * Y a n + X a n * Y a m))]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC [[a = 1]] THENL
     [ASM_REWRITE_TAC [X_DEGENERATE, Y_DEGENERATE] THEN
      REWRITE_TAC [ARITH, MULT_CLAUSES] THEN REWRITE_TAC [ADD_AC], ALL_TAC] THEN
    MP_TAC (SPECL [ [[a:num]], [[m + n:num]] ] XY_POWER_POS) THEN
    MP_TAC (SPECL [ [[a:num]], [[m:num]] ] XY_POWER_POS) THEN
    MP_TAC (SPECL [ [[a:num]], [[n:num]] ] XY_POWER_POS) THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [REAL_POW_ADD] THEN
    DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN
    REWRITE_TAC [(← rr
     [[(a + b * s) * (c + d * s) = (a  * c + (s * s) * b * d) +
                                (a * d + b * c) * s]])] THEN
    ASM_SIMP_TAC [(← ExceptT.mk (HolLight.GSYM REAL_POW_2)), SQRT_POW_2, REAL_SUB_LE, REAL_POW_LE_1,
                 REAL_OF_NUM_LE, (← ar [[~(a = 0) ==> 1 <= a]])] THEN
    SUBGOAL_THEN ([[&a pow 2 - &1 = &(a EXP 2 - 1)]]) SUBST1_TAC THENL
     [REWRITE_TAC [REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_LE)), (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_POW))] THEN
      ASM_SIMP_TAC [REAL_POW_LE_1, REAL_OF_NUM_LE,
                   (← ar [[~(a = 0) ==> 1 <= a]])], ALL_TAC] THEN
    REWRITE_TAC [REAL_OF_NUM_MUL, REAL_OF_NUM_ADD] THEN
    SUBGOAL_THEN ([[&a pow 2 - &1 = &(a EXP 2 - 1)]]) (SUBST1_TAC o HolLight.SYM) THENL
     [REWRITE_TAC [REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_LE)), (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_POW))] THEN
      ASM_SIMP_TAC [REAL_POW_LE_1, REAL_OF_NUM_LE,
                   (← ar [[~(a = 0) ==> 1 <= a]])], ALL_TAC] THEN
    ASM_SIMP_TAC [SQRT_LINEAR_EQ,
                 (← ar [[~(a = 0) /\ ~(a = 1) ==> 2 <= a]])] THEN
    REWRITE_TAC [MULT_AC])
  : ExceptT String IO thm).run
#eval ADDITION_FORMULA_POS

#eval phrase 24
unsafe def ADDITION_FORMULA_NEG : thm := keep "ADDITION_FORMULA_NEG" fun _ => (do
  prove ([[!a m n.
     ~(a = 0) /\ m <= n
     ==> ((X a (n - m) = X a m * X a n - (a EXP 2 - 1) * Y a m * Y a n) /\
          (Y a (n - m) = X a m * Y a n - X a n * Y a m))]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC [[a = 1]] THENL
     [ASM_REWRITE_TAC [X_DEGENERATE, Y_DEGENERATE] THEN
      REWRITE_TAC [ARITH, MULT_CLAUSES], ALL_TAC] THEN
    MP_TAC (SPECL [ [[a:num]], [[n - m:num]] ] XY_POWER_POS) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o HolLight.AP_TERM
     [[( * ) (((&a - sqrt (&a pow 2 - &1)) *
            (&a + sqrt (&a pow 2 - &1))) pow m)]]) THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV)
     [(← rr [[(x - y) * (x + y) = x * x - y * y]])] THEN
    ASM_SIMP_TAC [(← ExceptT.mk (HolLight.GSYM REAL_POW_2)), SQRT_POW_2, REAL_SUB_LE,
                 REAL_POW_LE_1, REAL_OF_NUM_LE,
                 (← ar [[~(a = 0) ==> 1 <= a]])] THEN
    REWRITE_TAC [(← rr [[x - (x - &1) = &1]])] THEN
    REWRITE_TAC [REAL_POW_MUL, REAL_POW_ONE, REAL_MUL_LID] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_MUL_ASSOC))] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_POW_ADD))] THEN
    ASM_SIMP_TAC [(← ar [[m <= n ==> (m + (n - m) = n:num)]])] THEN
    MP_TAC (SPECL [ [[a:num]], [[m:num]] ] XY_POWER_NEG) THEN
    MP_TAC (SPECL [ [[a:num]], [[n:num]] ] XY_POWER_POS) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN
    REWRITE_TAC [(← rr
     [[(a - b * s) * (c + d * s) = (a * c - (s * s) * b * d) +
                                (a * d - b * c) * s]])] THEN
    ASM_SIMP_TAC [(← ExceptT.mk (HolLight.GSYM REAL_POW_2)), SQRT_POW_2, REAL_SUB_LE, REAL_POW_LE_1,
                 REAL_OF_NUM_LE, (← ar [[~(a = 0) ==> 1 <= a]])] THEN
    ONCE_REWRITE_TAC [(← rr
     [[(a + b * s = (x1 - x2) + (y1 - y2) * s) =
    ((a + x2) + (b + y2) * s = x1 + y1 * s)]])] THEN
    SUBGOAL_THEN ([[&a pow 2 - &1 = &(a EXP 2 - 1)]]) SUBST1_TAC THENL
     [REWRITE_TAC [REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_LE)), (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_POW))] THEN
      ASM_SIMP_TAC [REAL_POW_LE_1, REAL_OF_NUM_LE,
                   (← ar [[~(a = 0) ==> 1 <= a]])], ALL_TAC] THEN
    REWRITE_TAC [REAL_OF_NUM_MUL, REAL_OF_NUM_ADD] THEN
    SUBGOAL_THEN ([[&a pow 2 - &1 = &(a EXP 2 - 1)]]) (SUBST1_TAC o HolLight.SYM) THENL
     [REWRITE_TAC [REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_LE)), (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_POW))] THEN
      ASM_SIMP_TAC [REAL_POW_LE_1, REAL_OF_NUM_LE,
                   (← ar [[~(a = 0) ==> 1 <= a]])], ALL_TAC] THEN
    ASM_SIMP_TAC [SQRT_LINEAR_EQ,
                 (← ar [[~(a = 0) /\ ~(a = 1) ==> 2 <= a]])] THEN
    DISCH_THEN (CONJUNCTS_THEN (SUBST1_TAC o HolLight.SYM)) THEN
    REWRITE_TAC [MULT_AC] THEN REWRITE_TAC [ADD_SUB])
  : ExceptT String IO thm).run
#eval ADDITION_FORMULA_NEG

-- ------------------------------------------------------------------------- --
-- Some stronger monotonicity theorems for Y.                                --
-- ------------------------------------------------------------------------- --

#eval phrase 25
unsafe def Y_INCREASES_SUC : thm := keep "Y_INCREASES_SUC" fun _ => (do
  prove ([[!a n. ~(a = 0) ==> Y a n < Y a (SUC n)]])
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [ADD1, ADDITION_FORMULA_POS] THEN
    REWRITE_TAC [X_CLAUSES, Y_CLAUSES] THEN
    MATCH_MP_TAC (← ar [[1 * y <= ay /\ ~(x = 0) ==> y < x * 1 + ay]]) THEN
    ASM_SIMP_TAC [LE_MULT_RCANCEL, (← ar [[1 <= a <=> ~(a = 0)]])] THEN
    MATCH_MP_TAC (← ar
      [[!n. (n = 1) /\ n <= m ==> ~(m = 0)]]) THEN
    EXISTS_TAC [[X a 0]] THEN CONJ_TAC THENL
     [REWRITE_TAC [X_CLAUSES], ALL_TAC] THEN
    SPEC_TAC ([[n:num]], [[n:num]]) THEN
    INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES, LE_REFL] THEN
    REWRITE_TAC [ADD1] THEN ASM_MESON_TAC [LE_TRANS, X_INCREASES])
  : ExceptT String IO thm).run
#eval Y_INCREASES_SUC

#eval phrase 26
unsafe def Y_INCREASES_LT : thm := keep "Y_INCREASES_LT" fun _ => (do
  prove ([[!a m n. ~(a = 0) /\ m < n ==> Y a m < Y a n]])
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [LT_EXISTS] THEN
    SIMP_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC [[d:num]] THEN DISCH_TAC THEN
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC [[Y a (SUC m)]] THEN
    ASM_SIMP_TAC [Y_INCREASES_SUC] THEN
    REWRITE_TAC [(← ar [[m + SUC d = SUC m + d]])] THEN
    SPEC_TAC ([[d:num]], [[d:num]]) THEN
    INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES, LE_REFL] THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [ADD_CLAUSES]) THEN
    ASM_MESON_TAC [ADD1, LE_TRANS, Y_INCREASES])
  : ExceptT String IO thm).run
#eval Y_INCREASES_LT

#eval phrase 27
unsafe def Y_INCREASES_LE : thm := keep "Y_INCREASES_LE" fun _ => (do
  prove ([[!a m n. ~(a = 0) /\ m <= n ==> Y a m <= Y a n]])
   (REWRITE_TAC [LE_LT] THEN MESON_TAC [LE_REFL, Y_INCREASES_LT])
  : ExceptT String IO thm).run
#eval Y_INCREASES_LE

#eval phrase 28
unsafe def Y_INJ : thm := keep "Y_INJ" fun _ => (do
  prove ([[!a m n. ~(a = 0) ==> ((Y a m = Y a n) <=> (m = n))]])
   (REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC [] THEN
    MP_TAC (SPEC ([[a:num]]) Y_INCREASES_LT) THEN ASM_REWRITE_TAC [] THEN
    MESON_TAC [LT_CASES, LT_REFL])
  : ExceptT String IO thm).run
#eval Y_INJ

-- ------------------------------------------------------------------------- --
-- One for X (to get the same as Y, need a /= 1).                            --
-- ------------------------------------------------------------------------- --

#eval phrase 29
unsafe def X_INCREASES_LE : thm := keep "X_INCREASES_LE" fun _ => (do
  prove ([[!a m n. ~(a = 0) /\ m <= n ==> X a m <= X a n]])
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [LE_EXISTS] THEN
    SIMP_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC [[d:num]] THEN
    DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN SPEC_TAC ([[d:num]], [[d:num]]) THEN
    INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES, LE_REFL] THEN
    REWRITE_TAC [ADD1] THEN ASM_MESON_TAC [LE_TRANS, X_INCREASES])
  : ExceptT String IO thm).run
#eval X_INCREASES_LE

#eval phrase 30
unsafe def X_INCREASES_LT : thm := keep "X_INCREASES_LT" fun _ => (do
  prove ([[!a m n. ~(a = 0) /\ ~(a = 1) /\ m < n ==> X a m < X a n]])
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [(← ExceptT.mk (HolLight.GSYM LE_SUC_LT))] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC [[X a (SUC m)]] THEN
    ASM_SIMP_TAC [X_INCREASES_LE] THEN
    SPEC_TAC ([[m:num]], [[p:num]]) THEN
    INDUCT_TAC THEN ASM_SIMP_TAC [ARITH, X_CLAUSES, (← ar
     [[~(a = 0) /\ ~(a = 1) ==> 1 < a]])] THEN
    REWRITE_TAC [(← ar [[SUC(SUC p) = p + 2]])] THEN
    REWRITE_TAC [X_CLAUSES, ADD1] THEN
    MATCH_MP_TAC (← ar [[a <= b /\ c < b ==> a < 2 * b - c]]) THEN
    CONJ_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC [[X a (SUC p)]] THEN
      ASM_REWRITE_TAC []] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [(← ar [[a = 1 * a]])] THEN
    REWRITE_TAC [LE_MULT_RCANCEL, ADD1] THEN DISJ1_TAC THEN
    MAP_EVERY UNDISCH_TAC [ [[~(a = 0)]], [[~(a = 1)]] ] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval X_INCREASES_LT

#eval phrase 31
unsafe def X_INCREASES_SUC : thm := keep "X_INCREASES_SUC" fun _ => (do
  prove ([[!a n. ~(a = 0) /\ ~(a = 1) ==> X a n < X a (SUC n)]])
   (SIMP_TAC [X_INCREASES_LT, LT])
  : ExceptT String IO thm).run
#eval X_INCREASES_SUC

#eval phrase 32
unsafe def X_INJ : thm := keep "X_INJ" fun _ => (do
  prove ([[!a m n. ~(a = 0) /\ ~(a = 1) ==> ((X a m = X a n) <=> (m = n))]])
   (REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC [] THEN
    MP_TAC (SPEC ([[a:num]]) X_INCREASES_LT) THEN ASM_REWRITE_TAC [] THEN
    MESON_TAC [LT_CASES, LT_REFL])
  : ExceptT String IO thm).run
#eval X_INJ

-- ------------------------------------------------------------------------- --
-- Coprimality of "X a n" and "Y a n".                                       --
-- ------------------------------------------------------------------------- --

#eval phrase 33
unsafe def XY_COPRIME : thm := keep "XY_COPRIME" fun _ => (do
  prove ([[!a n. ~(a = 0) ==> coprime(X a n,Y a n)]])
   (REPEAT GEN_TAC THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[n:num]]) o HolLight.MATCH_MP XY_ARE_SOLUTIONS) THEN
    ONCE_REWRITE_TAC [(← tt [[a ==> b <=> ~b ==> ~a]])] THEN
    REWRITE_TAC [coprime, NOT_FORALL_THM, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC [[d:num]] THEN REWRITE_TAC [NOT_IMP] THEN
    REWRITE_TAC [divides] THEN STRIP_TAC THEN ASM_REWRITE_TAC [EXP_2] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM MULT_ASSOC))] THEN
    GEN_REWRITE_TAC (HolCore.Lib.funpow 2 HolLight.RAND_CONV o HolLight.LAND_CONV)
     [(← ExceptT.mk (AC MULT_AC [[a * d * x * d * x = d * d * a * x * x:num]]))] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← ar
     [[(a = b + 1) ==> (a - b = 1)]])) THEN
    ASM_REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM LEFT_SUB_DISTRIB)), MULT_EQ_1])
  : ExceptT String IO thm).run
#eval XY_COPRIME

-- ------------------------------------------------------------------------- --
-- Divisibility properties.                                                  --
-- ------------------------------------------------------------------------- --

#eval phrase 34
unsafe def Y_DIVIDES_LEMMA : thm := keep "Y_DIVIDES_LEMMA" fun _ => (do
  prove ([[!a k n. ~(a = 0) ==> (Y a n) divides (Y a (n * k))]])
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN GEN_TAC THEN
    INDUCT_TAC THEN REWRITE_TAC [MULT_CLAUSES] THEN
    REWRITE_TAC [Y_CLAUSES, DIVIDES_0] THEN
    ASM_SIMP_TAC [ADDITION_FORMULA_POS] THEN
    UNDISCH_TAC [[Y a n divides Y a (n * k)]] THEN
    SIMP_TAC [divides, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC [[d:num]] THEN DISCH_TAC THEN
    EXISTS_TAC [[X a n * d + X a (n * k)]] THEN
    REWRITE_TAC [LEFT_ADD_DISTRIB] THEN REWRITE_TAC [MULT_AC, ADD_AC])
  : ExceptT String IO thm).run
#eval Y_DIVIDES_LEMMA

#eval phrase 35
unsafe def Y_DIVIDES : thm := keep "Y_DIVIDES" fun _ => (do
  prove ([[!a m n. ~(a = 0) ==> ((Y a m) divides (Y a n) <=> m divides n)]])
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [ALL_TAC,
      GEN_REWRITE_TAC HolLight.LAND_CONV [divides] THEN
      ASM_SIMP_TAC [LEFT_IMP_EXISTS_THM, Y_DIVIDES_LEMMA]] THEN
    ONCE_REWRITE_TAC [(← tt [[a ==> b <=> ~b ==> ~a]])] THEN
    ASM_CASES_TAC [[n = 0]] THEN ASM_REWRITE_TAC [DIVIDES_0] THEN
    ASM_CASES_TAC [[m = 0]] THENL
     [ASM_REWRITE_TAC [Y_CLAUSES, DIVIDES_ZERO] THEN
      MATCH_MP_TAC (← ar
        [[!n. (n = 1) /\ n <= m ==> ~(m = 0)]]) THEN
      EXISTS_TAC [[Y a 1]] THEN CONJ_TAC THENL
       [REWRITE_TAC [Y_CLAUSES], ALL_TAC] THEN
      ASM_SIMP_TAC [Y_INCREASES_LE, (← ar [[1 <= n <=> ~(n = 0)]])],
      ALL_TAC] THEN
    MP_TAC (SPECL [ [[n:num]], [[m:num]] ] DIVISION) THEN
    ASM_REWRITE_TAC [] THEN
    ABBREV_TAC [[q = n DIV m]] THEN ABBREV_TAC [[r = n MOD m]] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC [[r = 0]] THEN
    ASM_SIMP_TAC [ADD_CLAUSES, DIVIDES_LMUL, DIVIDES_REFL] THEN
    DISCH_TAC THEN
    ASM_SIMP_TAC [ADDITION_FORMULA_POS] THEN
    SUBGOAL_THEN ([[~((Y a m) divides (X a (q * m) * Y a r))]]) MP_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [(← tt [[~a ==> ~b <=> b ==> a]])] THEN DISCH_TAC THEN
      MATCH_MP_TAC DIVIDES_ADD_REVL THEN
      EXISTS_TAC [[X a r * Y a (q * m)]] THEN
      ASM_REWRITE_TAC [] THEN
      GEN_REWRITE_TAC (HolCore.Lib.funpow 3 HolLight.RAND_CONV) [MULT_SYM] THEN
      ASM_SIMP_TAC [DIVIDES_LMUL, Y_DIVIDES_LEMMA]] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP
     (← ExceptT.mk (REWRITE_RULE [IMP_CONJ] COPRIME_DIVPROD))) THEN
    REWRITE_TAC [NOT_IMP] THEN CONJ_TAC THENL
     [MP_TAC (SPECL [ [[a:num]], [[q * m:num]] ] XY_COPRIME) THEN ASM_REWRITE_TAC [] THEN
      ONCE_REWRITE_TAC [(← tt [[a ==> b <=> ~b ==> ~a]])] THEN
      REWRITE_TAC [coprime, NOT_FORALL_THM, NOT_IMP] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[d:num]] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN
      ASM_MESON_TAC [DIVIDES_TRANS, Y_DIVIDES_LEMMA], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP DIVIDES_LE) THEN
    ASM_SIMP_TAC [DE_MORGAN_THM, NOT_LE, Y_INCREASES_LT] THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM (← ExceptT.mk (HolLight.CONJUNCT1 Y_CLAUSES))))] THEN ASM_SIMP_TAC [Y_INJ])
  : ExceptT String IO thm).run
#eval Y_DIVIDES

-- ------------------------------------------------------------------------- --
-- This lemma would be trivial from binomial theorem.                        --
-- ------------------------------------------------------------------------- --

#eval phrase 36
unsafe def BINOMIAL_TRIVIALITY : thm := keep "BINOMIAL_TRIVIALITY" fun _ => (do
  prove ([[!x y d n. ?p q.
      (&x + &y * sqrt(&d)) pow (n + 2) =
      &x pow (n + 2) +
      &(n + 2) * &x pow (n + 1) * &y * sqrt(&d) +
      &(((n + 1) * (n + 2)) DIV 2) * &x pow n * &y pow 2 * &d +
      &p * &y pow 3 + &q * &y pow 3 * sqrt(&d)]])
   (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
     [REPEAT (EXISTS_TAC [[0]]) THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC [REAL_POW_1, real_pow, REAL_MUL_LZERO, REAL_ADD_RID] THEN
      REWRITE_TAC [REAL_MUL_LID] THEN REWRITE_TAC [REAL_POW_2] THEN
      REWRITE_TAC [(← rr
        [[(x + y) * (x + y) = x * x + &2 * x * y + y * y]])] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      ONCE_REWRITE_TAC [(← ExceptT.mk (AC REAL_MUL_AC [[(a * b) * (a * b) = (a * a) * b * b]]))] THEN
      SIMP_TAC [(← ExceptT.mk (HolLight.GSYM REAL_POW_2)), SQRT_POW_2, REAL_POS], ALL_TAC] THEN
    GEN_REWRITE_TAC (HolCore.Lib.funpow 2 HolLight.BINDER_CONV o HolLight.LAND_CONV o HolLight.TOP_DEPTH_CONV)
      [ADD_CLAUSES, real_pow] THEN
    FIRST_ASSUM (X_CHOOSE_THEN ([[p:num]]) (X_CHOOSE_THEN ([[q:num]]) SUBST1_TAC)) THEN
    REWRITE_TAC [(← rr
     [[(x + y) * (xn + xn1 + xn2 + p + q) =
    (x * xn) + (x * xn1 + y * xn) + (x * xn2 + y * xn1) +
    (y * xn2 + p * x + q * y) + (p * y + q * x)]])] THEN
    ONCE_REWRITE_TAC [(← rr
     [[x * n2 * xn1 * y * d + (y * d) * xn2 = (n2 * x * xn1 + xn2)  * y * d]])] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM (← ExceptT.mk (HolLight.CONJUNCT2 real_pow))))] THEN
    REWRITE_TAC [(← ar [[SUC(n + m) = n + SUC m]])] THEN
    REWRITE_TAC [(← ar [[SUC n + m = n + SUC m]])] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC [(← rr [[&n * x + x = (&n + &1) * x]])] THEN
    REWRITE_TAC [REAL_OF_NUM_ADD, (← ar [[(n + 2) + 1 = n + 3]])] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_ADD_ASSOC)), (← ExceptT.mk (HolLight.GSYM REAL_MUL_ASSOC)), SessionLibrary.Analysis.REAL_EQ_LADD] THEN
    ONCE_REWRITE_TAC [(← rr
     [[x * n12 * xn * y2 * d + y * s * n2 * xn1 * y * s + a =
    (n12 * (x * xn) * y2 * d + n2 * xn1 * (y * y) * (s * s)) + a]])] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_POW_2)), (← ExceptT.mk (HolLight.GSYM (← ExceptT.mk (HolLight.CONJUNCT2 real_pow))))] THEN
    SIMP_TAC [SQRT_POW_2, REAL_POS] THEN
    REWRITE_TAC [ADD1, REAL_MUL_ASSOC, (← ExceptT.mk (HolLight.GSYM REAL_ADD_RDISTRIB))] THEN
    SUBGOAL_THEN ([[&(((n + 1) * (n + 2)) DIV 2) + &(n + 2) =
                &(((n + 2) * (n + 3)) DIV 2)]])
    SUBST1_TAC THENL
     [REWRITE_TAC [REAL_OF_NUM_ADD, REAL_OF_NUM_EQ] THEN
      CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC DIV_UNIQ THEN
      EXISTS_TAC [[0]] THEN REWRITE_TAC [ARITH, ADD_CLAUSES] THEN
      REWRITE_TAC [(← ar [[(n + 2) * (n + 3) = n * n + 5 * n + 6]])] THEN
      REWRITE_TAC [(← ar
       [[(x + 5 * n + 6 = (y + n + 2) * 2) <=> (x + 3 * n + 2 = 2 * y)]])] THEN
      REWRITE_TAC [(← ar [[n * n + 3 * n + 2 = (n + 1) * (n + 2)]])] THEN
      SUBGOAL_THEN ([[EVEN((n + 1) * (n + 2))]]) MP_TAC THENL
       [REWRITE_TAC [EVEN_MULT, EVEN_ADD, ARITH_EVEN] THEN
        CONV_TAC (fun t => (do HolLight.EQT_INTRO (← ExceptT.mk (TAUT t)) : ExceptT String IO thm).run), ALL_TAC] THEN
      SIMP_TAC [EVEN_EXISTS, LEFT_IMP_EXISTS_THM] THEN
      SIMP_TAC [DIV_MULT, ARITH_EQ], ALL_TAC] THEN
    REWRITE_TAC [SessionLibrary.Analysis.REAL_EQ_LADD] THEN REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_MUL_ASSOC))] THEN
    ONCE_REWRITE_TAC [(← rr [[q * y3 * s * y * s = q * y * y3 * s * s]])] THEN
    SIMP_TAC [(← ExceptT.mk (HolLight.GSYM REAL_POW_2)), SQRT_POW_2, REAL_POS] THEN
    ONCE_REWRITE_TAC [(← rr
     [[y * s * nn * xn * y2 * d = nn * d * xn * (y * y2) * s]])] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM (← ExceptT.mk (HolLight.CONJUNCT2 real_pow))))] THEN
    EXISTS_TAC [[p * x + q * y * d:num]] THEN REWRITE_TAC [ARITH_SUC] THEN
    EXISTS_TAC [[((n + 1) * (n + 2)) DIV 2 * d * x EXP n +
              p * y + q * x]] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_MUL)), (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_ADD)),
                (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_POW))] THEN
    REWRITE_TAC [REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB] THEN
    REWRITE_TAC [REAL_MUL_AC] THEN REWRITE_TAC [REAL_ADD_AC])
  : ExceptT String IO thm).run
#eval BINOMIAL_TRIVIALITY

-- ------------------------------------------------------------------------- --
-- A lower bound theorem.                                                    --
-- ------------------------------------------------------------------------- --

#eval phrase 37
unsafe def Y_LOWERBOUND : thm := keep "Y_LOWERBOUND" fun _ => (do
  prove ([[!a n. (2 * a - 1) EXP n <= Y a (n + 1)]])
   (GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [EXP, ARITH, Y_CLAUSES] THEN
    ASM_CASES_TAC [[a = 0]] THEN ASM_REWRITE_TAC [ARITH, MULT_CLAUSES, LE_0] THEN
    REWRITE_TAC [(← ar [[SUC n + 1 = n + 2]]), Y_CLAUSES] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC [[(2 * a - 1) * Y a (n + 1)]] THEN
    ASM_REWRITE_TAC [LE_MULT_LCANCEL] THEN
    REWRITE_TAC [RIGHT_SUB_DISTRIB, MULT_CLAUSES, (← ExceptT.mk (HolLight.GSYM MULT_ASSOC))] THEN
    MATCH_MP_TAC (← ar [[a <= b ==> c - b <= c - a:num]]) THEN
    ASM_SIMP_TAC [Y_INCREASES])
  : ExceptT String IO thm).run
#eval Y_LOWERBOUND

#eval phrase 38
unsafe def Y_UPPERBOUND : thm := keep "Y_UPPERBOUND" fun _ => (do
  prove ([[!a n. Y a (n + 1) <= (2 * a) EXP n]])
   (GEN_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC [EXP, ADD_CLAUSES, Y_CLAUSES, LE_REFL] THEN
    REWRITE_TAC [(← ar [[SUC(n + 1) = n + 2]]), Y_CLAUSES] THEN
    MATCH_MP_TAC (← ar [[a <= b ==> a - c <= b:num]]) THEN
    ASM_REWRITE_TAC [MULT_ASSOC, LE_MULT_LCANCEL])
  : ExceptT String IO thm).run
#eval Y_UPPERBOUND

-- ------------------------------------------------------------------------- --
-- Now a key congruence.                                                     --
-- ------------------------------------------------------------------------- --

#eval phrase 39
unsafe def XY_Y3_CONGRUENCE : thm := keep "XY_Y3_CONGRUENCE" fun _ => (do
  prove ([[!a n k. ~(a = 0)
           ==> ?q. Y a (n * k) =
                   k * (X a n) EXP (k - 1) * Y a n + q * (Y a n) EXP 3]])
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC [[k = 0]] THENL
     [EXISTS_TAC [[0]] THEN
      ASM_REWRITE_TAC [Y_CLAUSES, MULT_CLAUSES, ADD_CLAUSES, SUB_0], ALL_TAC] THEN
    ASM_CASES_TAC [[a = 1]] THENL
     [ASM_REWRITE_TAC [X_DEGENERATE, Y_DEGENERATE, EXP_ONE] THEN
      EXISTS_TAC [[0]] THEN REWRITE_TAC [ADD_CLAUSES, MULT_CLAUSES] THEN
      REWRITE_TAC [MULT_AC], ALL_TAC] THEN
    ASM_CASES_TAC [[k = 1]] THENL
     [ASM_REWRITE_TAC [MULT_CLAUSES, SUB_REFL, EXP] THEN
      EXISTS_TAC [[0]] THEN REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES], ALL_TAC] THEN
    MP_TAC (SPECL [ [[a:num]], [[n * k:num]] ] XY_POWER_POS) THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_POW_POW))] THEN
    MP_TAC (SPECL [ [[a:num]], [[n:num]] ] XY_POWER_POS) THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_POW_POW))] THEN DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN
    SUBGOAL_THEN ([[2 <= k]]) MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC [ [[~(k = 0)]], [[~(k = 1)]] ] THEN ARITH_TAC,
      ALL_TAC] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [LE_EXISTS] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[d:num]])
      (SUBST1_TAC o HolLight.ONCE_REWRITE_RULE [ADD_SYM])) THEN
    MP_TAC (SPECL [ [[X a n]], [[Y a n]], [[a EXP 2 - 1]], [[d:num]] ]
                 BINOMIAL_TRIVIALITY) THEN
    SUBGOAL_THEN ([[&a pow 2 - &1 = &(a EXP 2 - 1)]]) (SUBST1_TAC o HolLight.SYM) THENL
     [REWRITE_TAC [REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_LE)), (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_POW))] THEN
      ASM_SIMP_TAC [REAL_POW_LE_1, REAL_OF_NUM_LE,
                   (← ar [[~(a = 0) ==> 1 <= a]])], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[p:num]]) (X_CHOOSE_THEN ([[q:num]]) SUBST1_TAC)) THEN
    ONCE_REWRITE_TAC [(← rr
     [[x1 + y1 + x2 + x3 + y2 = (x1 + x2 + x3) + (y1 + y2)]])] THEN
    REWRITE_TAC [REAL_MUL_ASSOC, (← ExceptT.mk (HolLight.GSYM REAL_ADD_RDISTRIB))] THEN
    SUBGOAL_THEN ([[&a pow 2 - &1 = &(a EXP 2 - 1)]]) SUBST1_TAC THENL
     [REWRITE_TAC [REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_LE)), (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_POW))] THEN
      ASM_SIMP_TAC [REAL_POW_LE_1, REAL_OF_NUM_LE,
                   (← ar [[~(a = 0) ==> 1 <= a]])], ALL_TAC] THEN
    REWRITE_TAC [REAL_OF_NUM_POW, REAL_OF_NUM_MUL, REAL_OF_NUM_ADD] THEN
    SUBGOAL_THEN ([[&a pow 2 - &1 = &(a EXP 2 - 1)]]) (SUBST1_TAC o HolLight.SYM) THENL
     [REWRITE_TAC [REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_LE)), (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_POW))] THEN
      ASM_SIMP_TAC [REAL_POW_LE_1, REAL_OF_NUM_LE,
                   (← ar [[~(a = 0) ==> 1 <= a]])], ALL_TAC] THEN
    ASM_SIMP_TAC [SQRT_LINEAR_EQ,
                 (← ar [[~(p = 0) /\ ~(p = 1) ==> 2 <= p]])] THEN
    DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN
    REWRITE_TAC [(← ar [[(d + 2) - 1 = d + 1]])] THEN
    EXISTS_TAC [[q:num]] THEN REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM MULT_ASSOC))])
  : ExceptT String IO thm).run
#eval XY_Y3_CONGRUENCE

-- ------------------------------------------------------------------------- --
-- The other key divisibility result.                                        --
-- ------------------------------------------------------------------------- --

#eval phrase 40
unsafe def Y2_DIVIDES : thm := keep "Y2_DIVIDES" fun _ => (do
  prove ([[!a m n. ~(a = 0)
           ==> (((Y a m) EXP 2) divides (Y a n) <=> (m * Y a m) divides n)]])
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC [[m = 0]] THENL
     [ASM_REWRITE_TAC [Y_CLAUSES, MULT_CLAUSES, DIVIDES_ZERO, EXP_2] THEN
      GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV) [(← ExceptT.mk (HolLight.GSYM (← ExceptT.mk (HolLight.CONJUNCT1 Y_CLAUSES))))] THEN
      ASM_SIMP_TAC [Y_INJ], ALL_TAC] THEN
    SUBGOAL_THEN ([[~(Y a m = 0)]]) ASSUME_TAC THENL
     [GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.RAND_CONV) [(← ExceptT.mk (HolLight.GSYM (← ExceptT.mk (HolLight.CONJUNCT1 Y_CLAUSES))))] THEN
      ASM_SIMP_TAC [Y_INJ], ALL_TAC] THEN
    MATCH_MP_TAC (← tt
     [[!c. (a ==> c) /\ (b ==> c) /\ (c ==> (a <=> b)) ==> (a <=> b)]]) THEN
    EXISTS_TAC [[m divides n]] THEN REPEAT CONJ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN ([[(Y a m) divides (Y a n)]]) MP_TAC THENL
       [ALL_TAC, ASM_SIMP_TAC [Y_DIVIDES]] THEN
      UNDISCH_TAC [[((Y a m) EXP 2) divides (Y a n)]] THEN
      REWRITE_TAC [divides, EXP_2, (← ExceptT.mk (HolLight.GSYM MULT_ASSOC))] THEN MESON_TAC [],
      REWRITE_TAC [divides, (← ExceptT.mk (HolLight.GSYM MULT_ASSOC))] THEN MESON_TAC [],
      ALL_TAC] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [divides] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[k:num]]) SUBST1_TAC) THEN
    MP_TAC (SPECL [ [[a:num]], [[m:num]], [[k:num]] ] XY_Y3_CONGRUENCE) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[q:num]]) SUBST1_TAC) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC [[((Y a m) EXP 2) divides (k * (X a m) EXP (k - 1) * Y a m)]] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [(← ExceptT.mk (num_CONV [[3]])), EXP] THEN
      MESON_TAC [DIVIDES_ADD, DIVIDES_ADD_REVL, DIVIDES_LMUL, DIVIDES_REFL],
      ALL_TAC] THEN
    REWRITE_TAC [MULT_ASSOC] THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV) [MULT_SYM] THEN
    REWRITE_TAC [EXP_2, (← ExceptT.mk (HolLight.GSYM MULT_ASSOC))] THEN
    ASM_SIMP_TAC [DIVIDES_LMUL2_EQ] THEN
    EQ_TAC THEN SIMP_TAC [DIVIDES_RMUL] THEN
    DISCH_TAC THEN MATCH_MP_TAC COPRIME_DIVPROD THEN
    EXISTS_TAC [[X a m EXP (k - 1)]] THEN
    ONCE_REWRITE_TAC [MULT_SYM] THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC COPRIME_EXP THEN
    ONCE_REWRITE_TAC [COPRIME_SYM] THEN ASM_SIMP_TAC [XY_COPRIME])
  : ExceptT String IO thm).run
#eval Y2_DIVIDES

-- ------------------------------------------------------------------------- --
-- Some more congruences.                                                    --
-- ------------------------------------------------------------------------- --

#eval phrase 41
unsafe def Y_N_MOD2 : thm := keep "Y_N_MOD2" fun _ => (do
  prove ([[!a n. ~(a = 0) ==> ?q. Y a n = 2 * q + n]])
   (GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC PELL_INDUCTION THEN REWRITE_TAC [Y_CLAUSES] THEN
    REPEAT CONJ_TAC THENL
     [EXISTS_TAC [[0]] THEN REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES],
      EXISTS_TAC [[0]] THEN REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES],
      ALL_TAC] THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM, LEFT_AND_EXISTS_THM,
                LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[n:num]], [[q1:num]], [[q2:num]] ] THEN STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o HolLight.SPEC ([[n:num]]) o HolLight.MATCH_MP Y_INCREASES) THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [(← ar [[2 * q1 + n <= 2 * q2 + n + 1 <=> q1 <= q2]])] THEN
    DISCH_TAC THEN
    EXISTS_TAC [[(2 * a * q2 - q1) + (a - 1) * (n + 1)]] THEN
    MATCH_MP_TAC (← ar
      [[v <= u /\ y <= x /\ (2 * (x + z) + w + v = 2 * y + u)
     ==> (u - v = 2 * ((x - y) + z) + w)]]) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC [LEFT_ADD_DISTRIB] THEN
      MATCH_MP_TAC (← ar
       [[x <= u /\ y <= v ==> 2 * x + y <= 2 * u + v + w]]) THEN
      REWRITE_TAC [MULT_ASSOC] THEN CONJ_TAC THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [(← ar [[n = 1 * n]])] THENL
       [MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC [],
        REWRITE_TAC [LE_MULT_RCANCEL] THEN DISJ1_TAC] THEN
      UNDISCH_TAC [[~(a = 0)]] THEN ARITH_TAC,
      REWRITE_TAC [MULT_ASSOC] THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [(← ar [[n = 1 * n]])] THEN
      MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC [[~(a = 0)]] THEN ARITH_TAC,
      UNDISCH_TAC [[~(a = 0)]] THEN SPEC_TAC ([[a:num]], [[a:num]]) THEN
      INDUCT_TAC THEN REWRITE_TAC [NOT_SUC] THEN
      REWRITE_TAC [(← ar [[SUC a - 1 = a]])] THEN
      REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES] THEN
      ARITH_TAC])
  : ExceptT String IO thm).run
#eval Y_N_MOD2

#eval phrase 42
unsafe def Y_N_MODA1 : thm := keep "Y_N_MODA1" fun _ => (do
  prove ([[!a n. ~(a = 0) ==> ?q. Y a n = q * (a - 1) + n]])
   (GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
    ASM_CASES_TAC [[a = 1]] THENL
     [ASM_REWRITE_TAC [SUB_REFL, Y_DEGENERATE, MULT_CLAUSES, ADD_CLAUSES],
      ALL_TAC] THEN
    MATCH_MP_TAC PELL_INDUCTION THEN REWRITE_TAC [Y_CLAUSES] THEN
    REPEAT CONJ_TAC THENL
     [EXISTS_TAC [[0]] THEN REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES],
      EXISTS_TAC [[0]] THEN REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES],
      ALL_TAC] THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM, LEFT_AND_EXISTS_THM,
                LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[n:num]], [[q1:num]], [[q2:num]] ] THEN
    STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o HolLight.SPEC ([[n:num]]) o HolLight.MATCH_MP Y_INCREASES) THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [(← ar [[q1 + n <= q2 + n + 1 <=> q1 <= q2 + 1]])] THEN
    ASM_CASES_TAC [[q2 = 0]] THENL
     [ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES] THEN
      REWRITE_TAC [(← ar [[a <= 1 <=> (a = 0) \/ (a = 1)]])] THEN
      ASM_REWRITE_TAC [MULT_EQ_0, MULT_EQ_1] THEN
      ASM_REWRITE_TAC [(← ar [[(a - 1 = 0) <=> (a = 0) \/ (a = 1)]])] THEN
      SIMP_TAC [(← ar [[(a - 1 = 1) <=> (a = 2)]])] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES] THENL
       [EXISTS_TAC [[2 * (n + 1)]] THEN
        UNDISCH_TAC [[~(a = 0)]] THEN SPEC_TAC ([[a:num]], [[b:num]]) THEN
        INDUCT_TAC THEN REWRITE_TAC [NOT_SUC] THEN
        REWRITE_TAC [(← ar [[SUC n - 1 = n]])] THEN
        REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES] THEN
        MATCH_MP_TAC (← ar [[(a + c = b) ==> (b - a = c:num)]]) THEN
        ARITH_TAC,
        REWRITE_TAC [MULT_ASSOC, ARITH] THEN
        REWRITE_TAC [(← ar [[4 * (n + 1) - (1 + n) = 3 * (n + 1)]])] THEN
        EXISTS_TAC [[2 * n + 1]] THEN ARITH_TAC],
      ALL_TAC] THEN
    DISCH_THEN (fun th =>
      EXISTS_TAC [[2 * (n + 1) + 2 * a * q2 - q1]] THEN MP_TAC th) THEN
    UNDISCH_TAC [[~(a = 1)]] THEN
    UNDISCH_TAC [[~(a = 0)]] THEN SPEC_TAC ([[a:num]], [[b:num]]) THEN
    INDUCT_TAC THEN REWRITE_TAC [NOT_SUC] THEN
    REWRITE_TAC [(← ar [[(SUC n = 1) <=> (n = 0)]])] THEN DISCH_TAC THEN
    REWRITE_TAC [(← ar [[SUC n - 1 = n]])] THEN DISCH_TAC THEN
    REWRITE_TAC [RIGHT_ADD_DISTRIB, RIGHT_SUB_DISTRIB] THEN
    MATCH_MP_TAC (← ar
      [[v <= u /\ y <= x /\ (u + y = z + x + w + v)
     ==> (u - v = (z + (x - y)) + w:num)]]) THEN
    REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC HolLight.LAND_CONV [(← ar [[a = 1 * a]])] THEN
      REWRITE_TAC [MULT_ASSOC] THEN MATCH_MP_TAC LE_MULT2 THEN
      ASM_REWRITE_TAC [(← ar [[q1 + n <= q2 + n + 1 <=> q1 <= q2 + 1]])] THEN
      REWRITE_TAC [MULT_CLAUSES] THEN ARITH_TAC,
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC [[q2 * b + 1]] THEN
      ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [(← ar [[a + 1 <= b <=> a < b]])] THEN
      ASM_SIMP_TAC [LT_MULT_RCANCEL] THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [(← ar [[a = 1 * a]])] THEN
      REWRITE_TAC [MULT_ASSOC] THEN
      ASM_SIMP_TAC [LT_MULT_RCANCEL] THEN
      REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES] THEN ARITH_TAC,
      REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES] THEN ARITH_TAC])
  : ExceptT String IO thm).run
#eval Y_N_MODA1

#eval phrase 43
unsafe def X_CONGRUENT : thm := keep "X_CONGRUENT" fun _ => (do
  prove ([[!a b c n. ~(a = 0) ==> ?q. X (a + b * c) n = X a n + q * c]])
   (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
    REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
    ASM_CASES_TAC [[b * c = 0]] THENL
     [GEN_TAC THEN EXISTS_TAC [[0]] THEN
      ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES], ALL_TAC] THEN
    UNDISCH_TAC [[~(b * c = 0)]] THEN
    REWRITE_TAC [MULT_EQ_0, DE_MORGAN_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC PELL_INDUCTION THEN REWRITE_TAC [X_CLAUSES] THEN
    REPEAT CONJ_TAC THENL
     [EXISTS_TAC [[0]] THEN REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES],
      EXISTS_TAC [[b:num]] THEN REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES],
      ALL_TAC] THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM, LEFT_AND_EXISTS_THM,
                LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[n:num]], [[q1:num]], [[q2:num]] ] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [(← ar
     [[2 * (x + y) * (u + v) = 2 * x * u + 2 * u * y + 2 * (x + y) * v]])] THEN
    EXISTS_TAC [[(2 * X a (n + 1) * b + 2 * (a + b * c) * q2) - q1]] THEN
    MATCH_MP_TAC (← ar
     [[a <= x /\ b <= y + z:num /\ ((x - a) + ((y + z) - b) = u)
    ==> ((x + y + z) - (a + b) = u)]]) THEN
    REWRITE_TAC [RIGHT_SUB_DISTRIB, RIGHT_ADD_DISTRIB, (← ExceptT.mk (HolLight.GSYM MULT_ASSOC))] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC [[1 * X a (n + 1)]] THEN CONJ_TAC THENL
       [ASM_SIMP_TAC [MULT_CLAUSES, X_INCREASES], ALL_TAC] THEN
      REWRITE_TAC [MULT_ASSOC, LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
      UNDISCH_TAC [[~(a = 0)]] THEN ARITH_TAC, ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC [[X (a + b * c) n]] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC [(← ExceptT.mk (HolLight.ONCE_REWRITE_RULE [ADD_SYM] LE_ADD))], ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC [[X (a + b * c) (n + 1)]] THEN
    CONJ_TAC THENL [ASM_SIMP_TAC [X_INCREASES, ADD_EQ_0], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC LE_ADD2 THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC HolLight.RAND_CONV [MULT_SYM] THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [(← ar [[a = a * 1]])] THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM MULT_ASSOC)), LE_MULT_LCANCEL] THEN
      ASM_REWRITE_TAC [(← ar [[1 <= x <=> ~(x = 0)]]), MULT_EQ_0, ARITH_EQ],
      MATCH_MP_TAC (← ar [[a <= y ==> a <= 2 * (x + y)]]) THEN
      ONCE_REWRITE_TAC [(← ExceptT.mk (AC MULT_AC [[a * b * c * d = (a * b) * (c * d:num)]]))] THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [(← ar [[a = 1 * a]])] THEN
      REWRITE_TAC [LE_MULT_RCANCEL] THEN
      ASM_REWRITE_TAC [(← ar [[1 <= x <=> ~(x = 0)]]), MULT_EQ_0, ARITH_EQ]])
  : ExceptT String IO thm).run
#eval X_CONGRUENT

#eval phrase 44
unsafe def Y_CONGRUENT : thm := keep "Y_CONGRUENT" fun _ => (do
  prove ([[!a b c n. ~(a = 0) ==> ?q. Y (a + b * c) n = Y a n + q * c]])
   (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
    REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
    ASM_CASES_TAC [[b * c = 0]] THENL
     [GEN_TAC THEN EXISTS_TAC [[0]] THEN
      ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES], ALL_TAC] THEN
    UNDISCH_TAC [[~(b * c = 0)]] THEN
    REWRITE_TAC [MULT_EQ_0, DE_MORGAN_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC PELL_INDUCTION THEN REWRITE_TAC [Y_CLAUSES] THEN
    REPEAT CONJ_TAC THENL
     [EXISTS_TAC [[0]] THEN REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES],
      EXISTS_TAC [[0]] THEN REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES],
      ALL_TAC] THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM, LEFT_AND_EXISTS_THM,
                LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[n:num]], [[q1:num]], [[q2:num]] ] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [(← ar
     [[2 * (x + y) * (u + v) = 2 * x * u + 2 * u * y + 2 * (x + y) * v]])] THEN
    EXISTS_TAC [[(2 * Y a (n + 1) * b + 2 * (a + b * c) * q2) - q1]] THEN
    MATCH_MP_TAC (← ar
     [[a <= x /\ b <= y + z:num /\ ((x - a) + ((y + z) - b) = u)
    ==> ((x + y + z) - (a + b) = u)]]) THEN
    REWRITE_TAC [RIGHT_SUB_DISTRIB, RIGHT_ADD_DISTRIB, (← ExceptT.mk (HolLight.GSYM MULT_ASSOC))] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC [[1 * Y a (n + 1)]] THEN CONJ_TAC THENL
       [ASM_SIMP_TAC [MULT_CLAUSES, Y_INCREASES], ALL_TAC] THEN
      REWRITE_TAC [MULT_ASSOC, LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
      UNDISCH_TAC [[~(a = 0)]] THEN ARITH_TAC, ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC [[Y (a + b * c) n]] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC [(← ExceptT.mk (HolLight.ONCE_REWRITE_RULE [ADD_SYM] LE_ADD))], ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC [[Y (a + b * c) (n + 1)]] THEN
    CONJ_TAC THENL [ASM_SIMP_TAC [Y_INCREASES, ADD_EQ_0], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC LE_ADD2 THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC HolLight.RAND_CONV [MULT_SYM] THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [(← ar [[a = a * 1]])] THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM MULT_ASSOC)), LE_MULT_LCANCEL] THEN
      ASM_REWRITE_TAC [(← ar [[1 <= x <=> ~(x = 0)]]), MULT_EQ_0, ARITH_EQ],
      MATCH_MP_TAC (← ar [[a <= y ==> a <= 2 * (x + y)]]) THEN
      ONCE_REWRITE_TAC [(← ExceptT.mk (AC MULT_AC [[a * b * c * d = (a * b) * (c * d:num)]]))] THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [(← ar [[a = 1 * a]])] THEN
      REWRITE_TAC [LE_MULT_RCANCEL] THEN
      ASM_REWRITE_TAC [(← ar [[1 <= x <=> ~(x = 0)]]), MULT_EQ_0, ARITH_EQ]])
  : ExceptT String IO thm).run
#eval Y_CONGRUENT

-- ------------------------------------------------------------------------- --
-- A more important congruence.                                              --
-- ------------------------------------------------------------------------- --

#eval phrase 45
unsafe def X_CONGRUENT_2NJ_POS : thm := keep "X_CONGRUENT_2NJ_POS" fun _ => (do
  prove ([[!a n j. ~(a = 0) ==> ?q. X a (2 * n + j) + X a j = q * X a n]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (SPECL [ [[a:num]], [[n:num]], [[n + j:num]] ] ADDITION_FORMULA_POS) THEN
    ASM_REWRITE_TAC [(← ar [[n + n + j = 2 * n + j]])] THEN
    DISCH_THEN (SUBST1_TAC o HolLight.CONJUNCT1) THEN
    MP_TAC (SPECL [ [[a:num]], [[n:num]], [[j:num]] ] ADDITION_FORMULA_POS) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o HolLight.CONJUNCT2) THEN
    ONCE_REWRITE_TAC [(← ar
     [[(xn * a + d * yn * (xn * yj + xj * yn)) + xj =
    xn * (a + d * yn * yj) + xj * (d * yn * yn + 1)]])] THEN
    ASM_SIMP_TAC [(← ExceptT.mk (HolLight.GSYM XY_ARE_SOLUTIONS)), (← ExceptT.mk (HolLight.GSYM EXP_2))] THEN
    REWRITE_TAC [EXP_2, (← ar
     [[xn * a + xj * xn * xn = (a + xj * xn) * xn:num]])] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval X_CONGRUENT_2NJ_POS

#eval phrase 46
unsafe def X_CONGRUENT_4NJ_POS : thm := keep "X_CONGRUENT_4NJ_POS" fun _ => (do
  prove ([[!a n j. ~(a = 0) ==> ?q. X a (4 * n + j) = q * X a n + X a j]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (SPECL [ [[a:num]], [[n:num]], [[2 * n + j]] ] X_CONGRUENT_2NJ_POS) THEN
    ASM_REWRITE_TAC [(← ar [[2 * n + 2 * n + j = 4 * n + j]])] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[q1:num]]) MP_TAC) THEN
    DISCH_THEN (MP_TAC o HolCore.Lib.C HolLight.AP_THM [[X a j]] o HolLight.AP_TERM [[(+):num->num->num]]) THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM ADD_ASSOC))] THEN
    MP_TAC (SPECL [ [[a:num]], [[n:num]], [[j:num]] ] X_CONGRUENT_2NJ_POS) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN ([[q2:num]]) MP_TAC) THEN
    DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← ar
     [[(y + q2 = q1 + x) ==> x <= y ==> (y = (q1 - q2) + x:num)]])) THEN
    ASM_SIMP_TAC [X_INCREASES_LE, (← ar [[j <= 4 * n + j]])] THEN
    DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM RIGHT_SUB_DISTRIB))] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval X_CONGRUENT_4NJ_POS

#eval phrase 47
unsafe def X_CONGRUENT_4MNJ_POS : thm := keep "X_CONGRUENT_4MNJ_POS" fun _ => (do
  prove ([[!a m n j. ~(a = 0) ==> ?q. X a (4 * m * n + j) = q * X a n + X a j]])
   (GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES] THENL
     [REPEAT GEN_TAC THEN EXISTS_TAC [[0]] THEN
      REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES], ALL_TAC] THEN
    UNDISCH_TAC [[!n j. ?q. X a (4 * m * n + j) = q * X a n + X a j]] THEN
    REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[q1:num]]) ASSUME_TAC) THEN
    MP_TAC (SPECL [ [[a:num]], [[n:num]], [[4 * m * n + j]] ] X_CONGRUENT_4NJ_POS) THEN
    ASM_REWRITE_TAC [(← ar
     [[4 * (m * n + n) + j = 4 * n + 4 * m * n + j]])] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[q2:num]]) SUBST1_TAC) THEN
    EXISTS_TAC [[q2 + q1:num]] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval X_CONGRUENT_4MNJ_POS

#eval phrase 48
unsafe def X_CONGRUENT_2NJ_NEG_LEMMA : thm := keep "X_CONGRUENT_2NJ_NEG_LEMMA" fun _ => (do
  prove ([[!a n j. ~(a = 0) /\ j <= n ==> ?q. X a (2 * n - j) + X a j = q * X a n]])
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC [[j = n:num]] THENL
     [EXISTS_TAC [[2]] THEN ASM_REWRITE_TAC [MULT_2, ADD_SUB], ALL_TAC] THEN
    MP_TAC (SPECL [ [[a:num]], [[n:num]], [[n - j:num]] ] ADDITION_FORMULA_POS) THEN
    ASM_SIMP_TAC [(← ar [[j <= n ==> (n + n - j = 2 * n - j)]])] THEN
    STRIP_TAC THEN
    MP_TAC (SPECL [ [[a:num]], [[j:num]], [[n:num]] ] ADDITION_FORMULA_NEG) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    EXISTS_TAC [[(X a j * X a n - (a EXP 2 - 1) * Y a j * Y a n) +
              (X a j * X a n - (a EXP 2 - 1) * Y a j * Y a n)]] THEN
    REWRITE_TAC [(← ar
     [[((xn * a + b) + c = (a + d) * xn) <=> (b + c = xn * d:num)]])] THEN
    REWRITE_TAC [LEFT_SUB_DISTRIB] THEN
    MATCH_MP_TAC (← ar
     [[b <= a /\ e <= d /\ (e + a + c = d + b)
    ==> ((a - b) + c = d - e:num)]]) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC [LE_MULT_LCANCEL] THEN REPEAT DISJ2_TAC THEN
      FIRST_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← ar
       [[(c = a - b) ==> 1 <= c ==> b <= a]])) THEN
      SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← ExceptT.mk (HolLight.SPEC ([[a:num]]) (← ec (HolCore.Lib.el 1 (CONJUNCTS Y_CLAUSES))))))) THEN
      MATCH_MP_TAC Y_INCREASES_LE THEN
      ASM_SIMP_TAC [(← ar [[j <= n ==> (1 <= n - j <=> ~(j = n))]])],
      REWRITE_TAC [LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
      FIRST_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← ar
       [[(c = a - b) ==> 1 <= c ==> b <= a]])) THEN
      SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← ExceptT.mk (HolLight.SPEC ([[a:num]]) (← ExceptT.mk (HolLight.CONJUNCT1 X_CLAUSES)))))) THEN
      MATCH_MP_TAC X_INCREASES_LE THEN ASM_REWRITE_TAC [LE_0],
      REWRITE_TAC [(← ar
       [[xn * a * yj * yn + a * yn * xj * yn + xj =
      xj * (a * yn * yn + 1) + a * yn * xn * yj]])] THEN
      ASM_SIMP_TAC [(← ExceptT.mk (HolLight.GSYM XY_ARE_SOLUTIONS)), (← ExceptT.mk (HolLight.GSYM EXP_2))] THEN
      REWRITE_TAC [EXP_2, MULT_AC]])
  : ExceptT String IO thm).run
#eval X_CONGRUENT_2NJ_NEG_LEMMA

#eval phrase 49
unsafe def X_CONGRUENT_2NJ_NEG : thm := keep "X_CONGRUENT_2NJ_NEG" fun _ => (do
  prove ([[!a n j. ~(a = 0) /\ j <= 2 * n ==> ?q. X a (2 * n - j) + X a j = q * X a n]])
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC [[j <= n:num]] THEN ASM_SIMP_TAC [X_CONGRUENT_2NJ_NEG_LEMMA] THEN
    MP_TAC (SPECL [ [[a:num]], [[n:num]], [[2 * n - j]] ] X_CONGRUENT_2NJ_NEG_LEMMA) THEN
    ASM_SIMP_TAC [(← ar [[~(j <= n) ==> 2 * n - j <= n]])] THEN
    ASM_SIMP_TAC [(← ar [[y <= x ==> (x - (x - y) = y:num)]])] THEN
    SIMP_TAC [ADD_AC])
  : ExceptT String IO thm).run
#eval X_CONGRUENT_2NJ_NEG

-- ------------------------------------------------------------------------- --
-- The cute GCD fact given by Smorynski.                                     --
-- ------------------------------------------------------------------------- --

#eval phrase 50
unsafe def XY_GCD_LEMMA : thm := keep "XY_GCD_LEMMA" fun _ => (do
  prove ([[!a m n. ~(a = 0) /\ m < n
           ==> (gcd(Y a m,Y a n) = Y a (gcd(m,n)))]])
   (GEN_TAC THEN ASM_CASES_TAC [[a = 0]] THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC [[a = 1]] THEN ASM_REWRITE_TAC [Y_DEGENERATE] THEN
    MATCH_MP_TAC num_WF THEN X_GEN_TAC [[m:num]] THEN DISCH_TAC THEN
    X_GEN_TAC [[n:num]] THEN DISCH_TAC THEN
    MP_TAC (SPECL [ [[n:num]], [[m:num]] ] DIVISION) THEN
    ASM_CASES_TAC [[m = 0]] THEN ASM_REWRITE_TAC [Y_CLAUSES, GCD_0] THEN
    ABBREV_TAC [[q = n DIV m]] THEN ABBREV_TAC [[r = n MOD m]] THEN
    DISCH_THEN (STRIP_ASSUME_TAC o HolLight.GSYM) THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[r:num]]) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[m:num]]) THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
     [EXPAND_TAC "n" THEN ASM_SIMP_TAC [ADDITION_FORMULA_POS] THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [GCD_SYM] THEN MATCH_MP_TAC GCD_EQ THEN
      X_GEN_TAC [[d:num]] THEN CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC (← tt
       [[(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)]]) THEN
      DISCH_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC [[d divides (X a (q * m) * Y a r)]] THEN CONJ_TAC THENL
       [SUBGOAL_THEN ([[d divides (Y a (q * m))]]) MP_TAC THENL
         [ASM_MESON_TAC [Y_DIVIDES, DIVIDES_TRANS, DIVIDES_LMUL, DIVIDES_REFL],
          ALL_TAC] THEN
        MESON_TAC [DIVIDES_ADD, DIVIDES_LMUL, DIVIDES_RMUL, DIVIDES_REFL,
                  DIVIDES_ADD_REVL],
        ALL_TAC] THEN
      EQ_TAC THEN SIMP_TAC [DIVIDES_LMUL] THEN
      SUBGOAL_THEN ([[coprime(d,X a (q * m))]])
       (fun th => MESON_TAC [COPRIME_DIVPROD, th]) THEN
      SUBGOAL_THEN ([[d divides (Y a (q * m))]]) MP_TAC THENL
       [ASM_MESON_TAC [Y_DIVIDES, DIVIDES_TRANS, DIVIDES_LMUL, DIVIDES_REFL],
        ALL_TAC] THEN
      MP_TAC (SPECL [ [[a:num]], [[q * m:num]] ] XY_COPRIME) THEN ASM_REWRITE_TAC [] THEN
      DISCH_TAC THEN DISCH_TAC THEN REWRITE_TAC [coprime] THEN
      X_GEN_TAC [[e:num]] THEN STRIP_TAC THEN
      UNDISCH_TAC [[coprime (X a (q * m),Y a (q * m))]] THEN
      REWRITE_TAC [coprime] THEN DISCH_THEN (MP_TAC o HolLight.SPEC [[e:num]]) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC [DIVIDES_TRANS],
      AP_TERM_TAC THEN EXPAND_TAC "n" THEN
      GEN_REWRITE_TAC HolCore.Lib.I [(← ExceptT.mk (HolLight.GSYM DIVIDES_ANTISYM))] THEN
      POP_ASSUM_LIST (HolCore.Lib.K ALL_TAC) THEN NUMBER_TAC])
  : ExceptT String IO thm).run
#eval XY_GCD_LEMMA

#eval phrase 51
unsafe def XY_GCD : thm := keep "XY_GCD" fun _ => (do
  prove ([[!a m n. ~(a = 0) ==> (gcd(Y a m,Y a n) = Y a (gcd(m,n)))]])
   (REPEAT STRIP_TAC THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (SPECL [ [[m:num]], [[n:num]] ] LT_CASES)
    THENL
     [ASM_SIMP_TAC [XY_GCD_LEMMA],
      ONCE_REWRITE_TAC [GCD_SYM] THEN ASM_SIMP_TAC [XY_GCD_LEMMA],
      ASM_REWRITE_TAC [GCD_REFL]])
  : ExceptT String IO thm).run
#eval XY_GCD

-- ------------------------------------------------------------------------- --
-- The "step-down" lemma.                                                    --
-- ------------------------------------------------------------------------- --

#eval phrase 52
unsafe def STEP_DOWN_LEMMA : thm := keep "STEP_DOWN_LEMMA" fun _ => (do
  prove ([[!a i j n q.
        ~(a = 0) /\ ~(a = 1) /\
        i <= j /\ j <= 2 * n /\
        (X a j = q * X a n + X a i)
        ==> (i = j) \/ ((a = 2) /\ (n = 1) /\ (i = 0) /\ (j = 2))]])
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC [[j <= n:num]] THENL
     [ASM_CASES_TAC [[i = j:num]] THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN ([[i < n:num]]) ASSUME_TAC THENL
       [ASM_MESON_TAC [LTE_TRANS, LT_LE], ALL_TAC] THEN
      UNDISCH_TAC [[X a j = q * X a n + X a i]] THEN
      ASM_CASES_TAC [[q = 0]] THEN
      ASM_SIMP_TAC [ADD_CLAUSES, MULT_CLAUSES, X_INJ] THEN
      DISCH_TAC THEN
      MP_TAC (SPECL [ [[a:num]], [[j:num]], [[n:num]] ] X_INCREASES_LE) THEN
      ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC (← tt [[~a ==> a ==> b]]) THEN
      MATCH_MP_TAC (← ar [[1 <= b /\ 1 * x <= qx ==> ~(qx + b <= x)]]) THEN
      SIMP_TAC [LE_MULT_RCANCEL] THEN
      ASM_SIMP_TAC [(← ar [[~(x = 0) ==> 1 <= x]])] THEN
      ONCE_REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM (← ExceptT.mk (HolLight.CONJUNCT1 X_CLAUSES))))] THEN
      ASM_SIMP_TAC [X_INCREASES_LE, LE_0], ALL_TAC] THEN
    ASM_CASES_TAC [[n = 0]] THENL
     [UNDISCH_TAC [[i <= j:num]] THEN UNDISCH_TAC [[j <= 2 * n]] THEN
      ASM_SIMP_TAC [LE, MULT_CLAUSES], ALL_TAC] THEN
    ASM_CASES_TAC [[i <= n:num]] THENL
     [MP_TAC (SPECL [ [[a:num]], [[n:num]], [[j:num]] ] X_CONGRUENT_2NJ_NEG) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[q1:num]]) MP_TAC) THEN
      UNDISCH_TAC [[X a j = q * X a n + X a i]] THEN
      ASM_CASES_TAC [[q = 0]] THEN
      ASM_SIMP_TAC [ADD_CLAUSES, MULT_CLAUSES, X_INJ] THEN DISCH_TAC THEN
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← ar
       [[(a + b + c = d:num) ==> (a + c = d - b)]])) THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM RIGHT_SUB_DISTRIB))] THEN
      ASM_CASES_TAC [[i = n:num]] THENL
       [ASM_REWRITE_TAC [] THEN
        DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← ar
         [[(x + n = q * n) ==> (x = q * n - 1 * n)]])) THEN
        MATCH_MP_TAC (← tt [[~a ==> a ==> b]]) THEN
        REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM RIGHT_SUB_DISTRIB))] THEN
        ASM_CASES_TAC [[q1 - q - 1 = 0]] THENL
         [ASM_REWRITE_TAC [MULT_CLAUSES, (← ar [[~(n = 0) <=> 1 <= n]])] THEN
          ONCE_REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM (← ExceptT.mk (HolLight.CONJUNCT1 X_CLAUSES))))] THEN
          ASM_SIMP_TAC [X_INCREASES_LE, LE_0], ALL_TAC] THEN
        MATCH_MP_TAC (← ar
         [[j < n /\ 1 * n <= a * n ==> ~(j = a * n)]]) THEN
        ASM_SIMP_TAC [LE_MULT_RCANCEL, (← ar [[~(x = 0) ==> 1 <= x]])] THEN
        MATCH_MP_TAC X_INCREASES_LT THEN ASM_REWRITE_TAC [] THEN
        UNDISCH_TAC [[~(j <= n:num)]] THEN
        UNDISCH_TAC [[~(n = 0)]] THEN ARITH_TAC, ALL_TAC] THEN
      ASM_CASES_TAC [[q1 - q = 0]] THENL
       [ASM_REWRITE_TAC [MULT_CLAUSES, ADD_EQ_0] THEN
        MATCH_MP_TAC (← tt [[~c ==> a /\ c ==> b]]) THEN
        REWRITE_TAC [(← ar [[~(n = 0) <=> 1 <= n]])] THEN
        ONCE_REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM (← ExceptT.mk (HolLight.CONJUNCT1 X_CLAUSES))))] THEN
        ASM_SIMP_TAC [X_INCREASES_LE, LE_0], ALL_TAC] THEN
      MATCH_MP_TAC (← tt [[(~b ==> a ==> c) ==> a ==> b \/ c]]) THEN
      DISCH_TAC THEN DISCH_TAC THEN
      ASM_CASES_TAC [[n = 1]] THENL
       [UNDISCH_TAC [[j <= 2 * n]] THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN
        UNDISCH_TAC [[~(j <= n:num)]] THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [IMP_IMP] THEN
        DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← ar
         [[~(j <= 1) /\ j <= 2 ==> (j = 2)]])) THEN
        DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC [] THEN
        UNDISCH_THEN ([[n = 1]]) SUBST_ALL_TAC THEN
        SUBGOAL_THEN ([[i = 0]]) SUBST_ALL_TAC THENL
         [MAP_EVERY UNDISCH_TAC [ [[i <= 1]], [[~(i = 1)]] ] THEN ARITH_TAC,
          ALL_TAC] THEN
        UNDISCH_TAC [[X a (2 * 1 - 2) + X a 0 = (q1 - q) * X a 1]] THEN
        REWRITE_TAC [ARITH, X_CLAUSES] THEN DISCH_THEN (ASSUME_TAC o HolLight.SYM) THEN
        MATCH_MP_TAC (← ar
         [[~(a = 0) /\ ~(a = 1) /\ a <= 2 ==> (a = 2)]]) THEN
        ASM_REWRITE_TAC [] THEN
        UNDISCH_THEN ([[(q1 - q) * a = 2]]) (SUBST1_TAC o HolLight.SYM) THEN
        GEN_REWRITE_TAC HolLight.LAND_CONV [(← ar [[a = 1 * a]])] THEN
        REWRITE_TAC [LE_MULT_RCANCEL] THEN
        ASM_SIMP_TAC [(← ar [[~(q = 0) ==> 1 <= q]])], ALL_TAC] THEN
      UNDISCH_TAC [[X a (2 * n - j) + X a i = (q1 - q) * X a n]] THEN
      MATCH_MP_TAC (← tt [[~b ==> b ==> a]]) THEN
      MATCH_MP_TAC (← ar
       [[s < x /\ x <= q * x ==> ~(s = q * x:num)]]) THEN
      CONJ_TAC THENL
       [ALL_TAC,
        GEN_REWRITE_TAC HolLight.LAND_CONV [(← ar [[a = 1 * a]])] THEN
        REWRITE_TAC [LE_MULT_RCANCEL] THEN
        ASM_SIMP_TAC [(← ar [[~(q = 0) ==> 1 <= q]])]] THEN
      MATCH_MP_TAC LET_TRANS THEN
      EXISTS_TAC [[2 * X a (n - 1)]] THEN CONJ_TAC THENL
       [MATCH_MP_TAC (← ar [[a <= c /\ b <= c ==> a + b <= 2 * c]]) THEN
        CONJ_TAC THEN MATCH_MP_TAC X_INCREASES_LE THEN ASM_REWRITE_TAC [] THENL
         [UNDISCH_TAC [[~(n = 0)]] THEN UNDISCH_TAC [[~(j <= n:num)]] THEN ARITH_TAC,
          UNDISCH_TAC [[~(i = n:num)]] THEN UNDISCH_TAC [[i <= n:num]] THEN
          ARITH_TAC],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[n - 1 = (n - 2) + 1]]) SUBST1_TAC THENL
       [UNDISCH_TAC [[~(n = 0)]] THEN UNDISCH_TAC [[~(n = 1)]] THEN ARITH_TAC,
        ALL_TAC] THEN
      SUBGOAL_THEN ([[n = (n - 2) + 2]])
       (fun th => GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.ONCE_DEPTH_CONV) [th])
      THENL
       [UNDISCH_TAC [[~(n = 0)]] THEN UNDISCH_TAC [[~(n = 1)]] THEN ARITH_TAC,
        ALL_TAC] THEN
      REWRITE_TAC [X_CLAUSES] THEN
      MATCH_MP_TAC (← ar [[z < x /\ 3 * x <= y ==> 2 * x < y - z]]) THEN
      ASM_SIMP_TAC [X_INCREASES_LT, (← ar [[n < n + 1]])] THEN
      REWRITE_TAC [MULT_ASSOC, LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
      UNDISCH_TAC [[~(a = 1)]] THEN UNDISCH_TAC [[~(a = 0)]] THEN ARITH_TAC,
      ALL_TAC] THEN
    MP_TAC (SPECL [ [[a:num]], [[n:num]], [[j:num]] ] X_CONGRUENT_2NJ_NEG) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[q1:num]]) MP_TAC) THEN
    MP_TAC (SPECL [ [[a:num]], [[n:num]], [[i:num]] ] X_CONGRUENT_2NJ_NEG) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [LE_TRANS], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[q2:num]]) MP_TAC) THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [IMP_IMP] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← ar
     [[(a = b) /\ (c = d) ==> (a + d = b + c:num)]])) THEN
    REWRITE_TAC [(← ar
      [[((x + i) + q1 = q2 + y + q3 + i) <=> (x + q1 = y + q2 + q3:num)]])] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← ar
     [[(x + q1 = y + q2) ==> y <= x ==> (x = y + (q2 - q1:num))]])) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC X_INCREASES_LE THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC [[i <= j:num]] THEN ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM RIGHT_ADD_DISTRIB)), (← ExceptT.mk (HolLight.GSYM RIGHT_SUB_DISTRIB))] THEN
    ASM_CASES_TAC [[(q2 + q) - q1 = 0]] THENL
     [ASM_SIMP_TAC [ADD_CLAUSES, MULT_CLAUSES, X_INJ] THEN
      MATCH_MP_TAC (← tt [[(a ==> b) ==> (a ==> b \/ c)]]) THEN
      UNDISCH_TAC [[j <= 2 * n]] THEN UNDISCH_TAC [[i <= j:num]] THEN ARITH_TAC,
      ALL_TAC] THEN
    MATCH_MP_TAC (← tt [[~a ==> a ==> b]]) THEN
    MATCH_MP_TAC (← ar
     [[1 * xi <= qxn /\ 1 <= xj ==> ~(xi = xj + qxn)]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LE_MULT2 THEN
      ASM_REWRITE_TAC [(← ar [[1 <= a <=> ~(a = 0)]])] THEN
      MATCH_MP_TAC X_INCREASES_LE THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC [[~(i <= n:num)]] THEN ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM (← ExceptT.mk (HolLight.CONJUNCT1 X_CLAUSES))))] THEN
    MATCH_MP_TAC X_INCREASES_LE THEN ASM_REWRITE_TAC [LE_0])
  : ExceptT String IO thm).run
#eval STEP_DOWN_LEMMA

#eval phrase 53
unsafe def STEP_DOWN_LEMMA_4_ASYM : thm := keep "STEP_DOWN_LEMMA_4_ASYM" fun _ => (do
  prove ([[!a i j n q.
        ~(a = 0) /\ ~(a = 1) /\
        0 < i /\ i <= n /\ j < 4 * n /\
        (X a i + q * X a n = X a j)
        ==> (j = i) \/ (j = 4 * n - i)]])
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC [[j <= 2 * n]] THENL
     [MP_TAC (SPECL [ [[a:num]], [[i:num]], [[j:num]], [[n:num]], [[q:num]] ]
         STEP_DOWN_LEMMA) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [] THEN
        UNDISCH_TAC [[X a i + q * X a n = X a j]] THEN
        SIMP_TAC [ADD_AC, MULT_AC] THEN DISCH_THEN (ASSUME_TAC o HolLight.SYM) THEN
        SUBGOAL_THEN ([[X a i <= X a j]]) MP_TAC THENL
         [ASM_REWRITE_TAC [(← ExceptT.mk (HolLight.ONCE_REWRITE_RULE [ADD_SYM] LE_ADD))], ALL_TAC] THEN
        ONCE_REWRITE_TAC [(← tt [[a ==> b <=> ~b ==> ~a]])] THEN
        ASM_SIMP_TAC [X_INCREASES_LT, NOT_LE], ALL_TAC] THEN
      ASM_SIMP_TAC [(← ar [[0 < i ==> ~(i = 0)]])], ALL_TAC] THEN
    DISJ_CASES_TAC (SPECL [ [[i:num]], [[4 * n - j]] ] LE_CASES) THEN
    (MP_TAC (SPECL [ [[a:num]], [[n:num]], [[2 * n - (4 * n - j)]] ]
                  X_CONGRUENT_2NJ_POS) THEN
     MP_TAC (SPECL [ [[a:num]], [[n:num]], [[4 * n - j]] ] X_CONGRUENT_2NJ_NEG) THEN
     ASM_SIMP_TAC [(← ar [[~(j <= 2 * n) ==> 4 * n - j <= 2 * n]])] THEN
     ASM_SIMP_TAC [(← ar
       [[j < 4 * n /\ ~(j <= 2 * n)
      ==> (2 * n + 2 * n - (4 * n - j) = j)]])] THEN
     DISCH_THEN (X_CHOOSE_THEN ([[q1:num]]) ASSUME_TAC) THEN
     DISCH_THEN (X_CHOOSE_THEN ([[q2:num]]) MP_TAC) THEN
     SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← HolLight.ASSUME [[X a i + q * X a n = X a j]]))) THEN
     UNDISCH_TAC
      [[X a (2 * n - (4 * n - j)) + X a (4 * n - j) = q1 * X a n]] THEN
     REWRITE_TAC [IMP_IMP] THEN
     DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← ar
       [[(a + b = c) /\ (d + a = e) ==> (b + e = c + d:num)]])))
    THENL
     [DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← ar
       [[(x + q1 = q2 + y + q3)
      ==> y <= x ==> (x = ((q2 + q3) - q1) + y:num)]])),
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← ar
       [[(x + q1 = q2 + y + q3)
      ==> x <= y ==> (y = (q1 - (q2 + q3)) + x:num)]]))] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM RIGHT_SUB_DISTRIB)), (← ExceptT.mk (HolLight.GSYM RIGHT_ADD_DISTRIB))] THEN
    ASM_SIMP_TAC [X_INCREASES_LE] THEN DISCH_TAC THENL
     [MP_TAC (SPECL [ [[a:num]], [[i:num]], [[4 * n - j]], [[n:num]], [[(q1 + q) - q2:num]] ]
        STEP_DOWN_LEMMA) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [] THEN UNDISCH_TAC [[~(j <= 2 * n)]] THEN ARITH_TAC,
        ALL_TAC] THEN
      ASM_SIMP_TAC [(← ar [[0 < i ==> ~(i = 0)]])] THEN
      DISCH_TAC THEN DISJ2_TAC THEN UNDISCH_TAC [[j < 4 * n]] THEN ARITH_TAC,
      MP_TAC (SPECL [ [[a:num]], [[4 * n - j]], [[i:num]], [[n:num]], [[q2:num - (q1 + q)]] ]
        STEP_DOWN_LEMMA) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [] THEN UNDISCH_TAC [[i <= n:num]] THEN ARITH_TAC,
        ALL_TAC] THEN
      ASM_REWRITE_TAC [SUB_EQ_0, (← ExceptT.mk (HolLight.GSYM NOT_LT))] THEN
      DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN
      DISJ2_TAC THEN UNDISCH_TAC [[j < 4 * n]] THEN ARITH_TAC])
  : ExceptT String IO thm).run
#eval STEP_DOWN_LEMMA_4_ASYM

#eval phrase 54
unsafe def STEP_DOWN_LEMMA_4 : thm := keep "STEP_DOWN_LEMMA_4" fun _ => (do
  prove ([[!a i j n q1 q2.
        ~(a = 0) /\ ~(a = 1) /\
        0 < i /\ i <= n /\ j < 4 * n /\
        (X a i + q1 * X a n = X a j + q2 * X a n)
        ==> (j = i) \/ (j = 4 * n - i)]])
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC [[j < i:num]] THENL
     [UNDISCH_TAC [[X a i + q1 * X a n = X a j + q2 * X a n]] THEN
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← ar
        [[(x + q1 = y + q2) ==> y < x ==> (x = y + (q2 - q1:num))]])) THEN
      ASM_SIMP_TAC [X_INCREASES_LT, (← ExceptT.mk (HolLight.GSYM RIGHT_SUB_DISTRIB))] THEN
      ASM_CASES_TAC [[q2 - q1 = 0]] THENL
       [ASM_SIMP_TAC [MULT_CLAUSES, ADD_CLAUSES, X_INJ], ALL_TAC] THEN
      MATCH_MP_TAC (← tt [[~a ==> a ==> b]]) THEN
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← ar
       [[(i = j + q * n) ==> 1 <= j /\ 1 * n <= q * n ==> ~(i <= n)]])) THEN
      ASM_SIMP_TAC [X_INCREASES_LE] THEN
      ASM_SIMP_TAC [LE_MULT_RCANCEL,
                   (← ar [[~(q2 - q1 = 0) ==> 1 <= q2 - q1]])] THEN
      ONCE_REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM (← ExceptT.mk (HolLight.CONJUNCT1 X_CLAUSES))))] THEN
      ASM_SIMP_TAC [X_INCREASES_LE, LE_0], ALL_TAC] THEN
    MP_TAC (SPECL [ [[a:num]], [[i:num]], [[j:num]], [[n:num]], [[q1 - q2:num]] ]
                 STEP_DOWN_LEMMA_4_ASYM) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [RIGHT_SUB_DISTRIB] THEN
    MATCH_MP_TAC (← ar
     [[(i + q1 = j + q2) /\ ~(j < i) ==> (i + q1 - q2 = j:num)]]) THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [NOT_LT]) THEN
    ASM_SIMP_TAC [NOT_LT, X_INCREASES_LE])
  : ExceptT String IO thm).run
#eval STEP_DOWN_LEMMA_4

#eval phrase 55
unsafe def STEP_DOWN_LEMMA_STRONG_ASYM : thm := keep "STEP_DOWN_LEMMA_STRONG_ASYM" fun _ => (do
  prove ([[!a i j n c.
        ~(a = 0) /\ ~(a = 1) /\
        0 < i /\ i <= n /\
        (X a i + c * X a n = X a j)
        ==> (?q. j = i + 4 * n * q) \/
            (?q. j + i = 4 * n * q)]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (SPECL [ [[j:num]], [[4 * n]] ] DIVISION) THEN
    ABBREV_TAC [[q = j DIV (4 * n)]] THEN ABBREV_TAC [[k = j MOD (4 * n)]] THEN
    ANTS_TAC THENL
     [UNDISCH_TAC [[0 < i]] THEN UNDISCH_TAC [[i <= n:num]] THEN ARITH_TAC,
      ALL_TAC] THEN
    DISCH_THEN (STRIP_ASSUME_TAC o HolLight.GSYM) THEN
    MP_TAC (SPECL [ [[a:num]], [[q:num]], [[n:num]], [[k:num]] ] X_CONGRUENT_4MNJ_POS) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[q1:num]]) MP_TAC) THEN
    SUBST1_TAC (← ar [[4 * q * n + k = q * 4 * n + k]]) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_CASES_TAC [[k < i:num]] THENL
     [UNDISCH_TAC [[X a i + c * X a n = q1 * X a n + X a k]] THEN
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← ar
       [[(a + q1 = q2 + b) ==> b < a ==> (a = (q2 - q1) + b:num)]])) THEN
      ASM_SIMP_TAC [X_INCREASES_LT] THEN REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM RIGHT_SUB_DISTRIB))] THEN
      ASM_CASES_TAC [[q1 - c = 0]] THENL
       [ASM_SIMP_TAC [MULT_CLAUSES, ADD_CLAUSES, X_INJ] THEN
        DISCH_TAC THEN DISJ1_TAC THEN EXISTS_TAC [[q:num]] THEN
        FIRST_ASSUM (fun th => HolLight.tactic_of do
          let s ← HolLight.SYM th
          pure (GEN_REWRITE_TAC HolLight.LAND_CONV [s])) THEN
        REWRITE_TAC [ADD_AC, MULT_AC],
        MATCH_MP_TAC (← tt [[~a ==> a ==> b]]) THEN
        MATCH_MP_TAC (← ar
         [[a <= b /\ 1 <= c ==> ~(a = b + c)]]) THEN
        CONJ_TAC THENL
         [GEN_REWRITE_TAC HolLight.LAND_CONV [(← ar [[n = 1 * n]])] THEN
          MATCH_MP_TAC LE_MULT2 THEN
          ASM_REWRITE_TAC [(← ar [[1 <= n <=> ~(n = 0)]])] THEN
          ASM_SIMP_TAC [X_INCREASES_LE, LT_IMP_LE],
          SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← ExceptT.mk (HolLight.SPEC ([[a:num]]) (← ExceptT.mk (HolLight.CONJUNCT1 X_CLAUSES)))))) THEN
          ASM_SIMP_TAC [X_INCREASES_LE, LE_0]]],
      MP_TAC (SPECL [ [[a:num]], [[i:num]], [[k:num]], [[n:num]], [[c - q1:num]] ]
                   STEP_DOWN_LEMMA_4_ASYM) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [] THEN
        UNDISCH_TAC [[X a i + c * X a n = q1 * X a n + X a k]] THEN
        DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← ar
         [[(a + q1 = q2 + b) ==> ~(b < a) ==> (a + (q1 - q2)= b:num)]])) THEN
        REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM RIGHT_SUB_DISTRIB))] THEN
        DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC [NOT_LT] THEN
        MATCH_MP_TAC X_INCREASES_LE THEN ASM_REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM NOT_LT))],
        ALL_TAC] THEN
      DISCH_THEN DISJ_CASES_TAC THENL
       [DISJ1_TAC THEN EXISTS_TAC [[q:num]] THEN
        UNDISCH_THEN ([[q * 4 * n + k = j]]) (SUBST1_TAC o HolLight.SYM) THEN
        ASM_REWRITE_TAC [MULT_AC, ADD_AC],
        DISJ2_TAC THEN EXISTS_TAC [[q + 1]] THEN
        UNDISCH_THEN ([[q * 4 * n + k = j]]) (SUBST1_TAC o HolLight.SYM) THEN
        REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM ADD_ASSOC)), LEFT_ADD_DISTRIB, MULT_CLAUSES] THEN
        ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC (← ar
         [[(a' = a) /\ i <= b ==> (a + (b - i) + i = a' + b:num)]]) THEN
        REWRITE_TAC [MULT_AC] THEN
        UNDISCH_TAC [[i <= n:num]] THEN ARITH_TAC]])
  : ExceptT String IO thm).run
#eval STEP_DOWN_LEMMA_STRONG_ASYM

#eval phrase 56
unsafe def STEP_DOWN_LEMMA_STRONG : thm := keep "STEP_DOWN_LEMMA_STRONG" fun _ => (do
  prove ([[!a i j n c1 c2.
        ~(a = 0) /\ ~(a = 1) /\ 0 < i /\ i <= n /\
        (X a i + c1 * X a n = X a j + c2 * X a n)
        ==> (?q. j = i + 4 * n * q) \/
            (?q. j + i = 4 * n * q)]])
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC [[j < i:num]] THENL
     [UNDISCH_TAC [[X a i + c1 * X a n = X a j + c2 * X a n]] THEN
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← ar
        [[(x + q1 = y + q2) ==> y < x ==> (x = y + (q2 - q1:num))]])) THEN
      ASM_SIMP_TAC [X_INCREASES_LT, (← ExceptT.mk (HolLight.GSYM RIGHT_SUB_DISTRIB))] THEN
      ASM_CASES_TAC [[c2 - c1 = 0]] THENL
       [ASM_SIMP_TAC [MULT_CLAUSES, ADD_CLAUSES, X_INJ] THEN
        DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN DISJ1_TAC THEN
        EXISTS_TAC [[0]] THEN REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES],
        ALL_TAC] THEN
      MATCH_MP_TAC (← tt [[~a ==> a ==> b]]) THEN
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← ar
       [[(i = j + q * n) ==> 1 <= j /\ 1 * n <= q * n ==> ~(i <= n)]])) THEN
      ASM_SIMP_TAC [X_INCREASES_LE] THEN
      ASM_SIMP_TAC [LE_MULT_RCANCEL,
                   (← ar [[~(q2 - q1 = 0) ==> 1 <= q2 - q1]])] THEN
      ONCE_REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM (← ExceptT.mk (HolLight.CONJUNCT1 X_CLAUSES))))] THEN
      ASM_SIMP_TAC [X_INCREASES_LE, LE_0], ALL_TAC] THEN
    MP_TAC (SPECL [ [[a:num]], [[i:num]], [[j:num]], [[n:num]], [[c1 - c2:num]] ]
                 STEP_DOWN_LEMMA_STRONG_ASYM) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [RIGHT_SUB_DISTRIB] THEN
    MATCH_MP_TAC (← ar
     [[(i + q1 = j + q2) /\ ~(j < i) ==> (i + q1 - q2 = j:num)]]) THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [NOT_LT]) THEN
    ASM_SIMP_TAC [NOT_LT, X_INCREASES_LE])
  : ExceptT String IO thm).run
#eval STEP_DOWN_LEMMA_STRONG

-- ------------------------------------------------------------------------- --
-- Diophantine nature of the Y sequence.                                     --
-- ------------------------------------------------------------------------- --

#eval phrase 57
unsafe def Y_DIOPH : thm := keep "Y_DIOPH" fun _ => (do
  prove ([[~(a = 0) /\ ~(a = 1) /\ ~(y = 0)
   ==> ((y = Y a k) <=>
        ?x u v r b p q s t c d.
                0 < r /\
                (x EXP 2 = (a EXP 2 - 1) * y EXP 2 + 1) /\
                (u EXP 2 = (a EXP 2 - 1) * v EXP 2 + 1) /\
                (s EXP 2 = (b EXP 2 - 1) * t EXP 2 + 1) /\
                (v = r * y EXP 2) /\
                (b = 1 + 4 * p * y) /\
                (b = a + q * u) /\
                (s = x + c * u) /\
                (t = k + 4 * d * y) /\
                k <= y)]])
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [ALL_TAC,
      DISCH_THEN (STRIP_ASSUME_TAC o HolLight.GSYM) THEN
      MP_TAC (SPECL [ [[a:num]], [[x:num]], [[y:num]] ] SOLUTIONS_ARE_XY) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[i:num]]) (STRIP_ASSUME_TAC o HolLight.GSYM)) THEN
      MP_TAC (SPECL [ [[a:num]], [[u:num]], [[v:num]] ] SOLUTIONS_ARE_XY) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[n:num]]) (STRIP_ASSUME_TAC o HolLight.GSYM)) THEN
      SUBGOAL_THEN ([[~(b = 0)]]) ASSUME_TAC THENL
       [SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← HolLight.ASSUME [[1 + 4 * p * y = b]]))) THEN
        REWRITE_TAC [ADD_EQ_0, ARITH_EQ], ALL_TAC] THEN
      MP_TAC (SPECL [ [[b:num]], [[s:num]], [[t:num]] ] SOLUTIONS_ARE_XY) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[j:num]]) (STRIP_ASSUME_TAC o HolLight.GSYM)) THEN
      SUBGOAL_THEN ([[y <= v:num]]) ASSUME_TAC THENL
       [SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← HolLight.ASSUME [[r * y EXP 2 = v]]))) THEN REWRITE_TAC [EXP_2] THEN
        GEN_REWRITE_TAC HolLight.LAND_CONV [(← ar [[y = 1 * y]])] THEN
        REWRITE_TAC [MULT_ASSOC, LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
        ASM_REWRITE_TAC [(← ar [[1 <= a <=> ~(a = 0)]]), MULT_EQ_0] THEN
        ASM_SIMP_TAC [(← ar [[0 < r ==> ~(r = 0)]])], ALL_TAC] THEN
      SUBGOAL_THEN ([[i <= n:num]]) ASSUME_TAC THENL
       [UNDISCH_TAC [[y <= v:num]] THEN
        SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← HolLight.ASSUME [[Y a i = y]]))) THEN
        SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← HolLight.ASSUME [[Y a n = v]]))) THEN
        ONCE_REWRITE_TAC [(← tt [[a ==> b <=> ~b ==> ~a]])] THEN
        ASM_SIMP_TAC [NOT_LE, Y_INCREASES_LT], ALL_TAC] THEN
      MP_TAC (SPECL [ [[a:num]], [[q:num]], [[u:num]], [[j:num]] ] X_CONGRUENT) THEN
      REWRITE_TAC [(← HolLight.ASSUME [[~(a = 0)]]), (← HolLight.ASSUME [[a + q * u = b:num]])] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[q1:num]]) MP_TAC) THEN
      SUBST1_TAC (← HolLight.ASSUME [[X b j = s]]) THEN
      SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← HolLight.ASSUME [[x + c * u = s:num]]))) THEN
      SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← HolLight.ASSUME [[X a i = x]]))) THEN
      SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← HolLight.ASSUME [[X a n = u]]))) THEN DISCH_TAC THEN
      SUBGOAL_THEN ([[~(i = 0)]]) ASSUME_TAC THENL
       [UNDISCH_TAC [[~(y = 0)]] THEN
        REWRITE_TAC [(← tt [[~a ==> ~b <=> b ==> a]])] THEN
        EXPAND_TAC "y" THEN SIMP_TAC [Y_CLAUSES, (← HolLight.ASSUME [[~(a = 0)]])],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[(?q. j = i + 4 * n * q) \/ (?q. j + i = 4 * n * q)]])
      ASSUME_TAC THENL
       [MATCH_MP_TAC STEP_DOWN_LEMMA_STRONG THEN
        MAP_EVERY EXISTS_TAC [ [[a:num]], [[c:num]], [[q1:num]] ] THEN
        ASM_SIMP_TAC [(← ar [[~(i = 0) ==> 0 < i]])], ALL_TAC] THEN
      MP_TAC (SPECL [ [[a:num]], [[i:num]], [[n:num]] ] Y2_DIVIDES) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (fun th => HolLight.tactic_of do
        let pr ← HolLight.EQ_IMP_RULE th
        pure (MP_TAC pr.1)) THEN
      REWRITE_TAC [divides, LEFT_IMP_EXISTS_THM] THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC [[r:num]]) THEN
      SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← HolLight.ASSUME [[r * y EXP 2 = v]]))) THEN
      REWRITE_TAC [(← ec (EQT_INTRO (← ExceptT.mk (HolLight.SPEC_ALL MULT_SYM))))] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[d1:num]]) (ASSUME_TAC o HolLight.SYM)) THEN
      UNDISCH_TAC [[(?q. j = i + 4 * n * q) \/ (?q. j + i = 4 * n * q:num)]] THEN
      UNDISCH_THEN ([[(i * y) * d1 = n:num]]) (SUBST1_TAC o HolLight.SYM) THEN DISCH_TAC THEN
      SUBGOAL_THEN ([[(?q. j = i + q * 4 * Y a i) \/
                  (?q. j + i = q * 4 * Y a i)]])
      MP_TAC THENL
       [FIRST_ASSUM (fun th => HolLight.tactic_of do
          let _ ← ec (HolCore.Lib.check HolCore.Basics.is_disj (concl th))
          pure (UNDISCH_TAC (concl th))) THEN
        REWRITE_TAC [OR_EXISTS_THM] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[d2:num]])
         (fun th => EXISTS_TAC [[i * d1 * d2:num]] THEN MP_TAC th)) THEN
        SUBST1_TAC (← HolLight.ASSUME [[Y a i = y]]) THEN REWRITE_TAC [MULT_AC],
        FIRST_X_ASSUM (fun th => HolLight.tactic_of do
          let _ ← ec (HolCore.Lib.check (fun x => HolCore.Basics.is_disj (concl x)) th)
          pure ALL_TAC) THEN
        DISCH_TAC] THEN
      MP_TAC (SPECL [ [[b:num]], [[j:num]] ] Y_N_MODA1) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[d3:num]]) MP_TAC) THEN
      SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← HolLight.ASSUME [[1 + 4 * p * y = b]]))) THEN REWRITE_TAC [ADD_SUB2] THEN
      SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← HolLight.ASSUME [[k + 4 * d * y = t]]))) THEN DISCH_TAC THEN
      SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← HolLight.ASSUME [[Y a i = y]]))) THEN AP_TERM_TAC THEN
      SUBGOAL_THEN ([[(?q1 q2. k + q1 * 4 * Y a i = i + q2 * 4 * Y a i) \/
                  (?q. i + k = q * 4 * Y a i)]])
      MP_TAC THENL
       [UNDISCH_TAC [[(?q. j = i + q * 4 * Y a i) \/
                   (?q. j + i = q * 4 * Y a i)]] THEN
        MATCH_MP_TAC (← tt
         [[(a1 ==> b1) /\ (a2 ==> b2) ==> a1 \/ a2 ==> b1 \/ b2]]) THEN
        CONJ_TAC THEN DISCH_TAC THEN
        UNDISCH_TAC [[k + 4 * d * y = d3 * 4 * p * y + j]] THENL
         [FIRST_X_ASSUM (X_CHOOSE_THEN ([[d4:num]]) SUBST1_TAC) THEN
          DISCH_THEN (fun th =>
            EXISTS_TAC [[d:num]] THEN
            EXISTS_TAC [[d3 * p + d4:num]] THEN MP_TAC th) THEN
          SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← HolLight.ASSUME [[Y a i = y]]))) THEN
          REWRITE_TAC [RIGHT_ADD_DISTRIB] THEN
          REWRITE_TAC [MULT_AC] THEN REWRITE_TAC [ADD_AC],
          DISCH_THEN (MP_TAC o HolCore.Lib.C HolLight.AP_THM [[i:num]] o
            HolLight.AP_TERM [[(+):num->num->num]]) THEN
          REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM ADD_ASSOC))] THEN
          FIRST_X_ASSUM (X_CHOOSE_THEN ([[d4:num]]) SUBST1_TAC) THEN
          DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← ar
           [[(k + q1 + i = q2) ==> (i + k = q2 - q1:num)]])) THEN
          DISCH_THEN SUBST1_TAC THEN
          SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← HolLight.ASSUME [[Y a i = y]]))) THEN
          REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM RIGHT_ADD_DISTRIB)), MULT_ASSOC,
                      (← ExceptT.mk (HolLight.GSYM RIGHT_SUB_DISTRIB))] THEN
          REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM MULT_ASSOC))] THEN
          REWRITE_TAC [(← ar
           [[(d3 * 4 * p + d4 * 4) - 4 * x =
          ((d3 * p + d4) - x) * 4]])] THEN REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM MULT_ASSOC))] THEN
          EXISTS_TAC [[(d3 * p + d4) - d:num]] THEN REFL_TAC],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[k <= Y a i]]) ASSUME_TAC THENL
       [ASM_REWRITE_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN ([[i <= Y a i]]) ASSUME_TAC THENL
       [MP_TAC (SPECL [ [[a:num]], [[i:num]] ] Y_N_MODA1) THEN
        ASM_SIMP_TAC [LEFT_IMP_EXISTS_THM] THEN
        REWRITE_TAC [(← ExceptT.mk (HolLight.ONCE_REWRITE_RULE [ADD_SYM] LE_ADD))], ALL_TAC] THEN
      DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL
       [DISCH_THEN (X_CHOOSE_THEN ([[q4:num]]) (X_CHOOSE_THEN ([[q5:num]]) MP_TAC)) THEN
        REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
         (SPECL [ [[q4:num]], [[q5:num]] ] LT_CASES)
        THENL
         [DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← ar
           [[(k + q4 = i + q5) ==> q4 < q5:num ==> (k = i + (q5 - q4))]])) THEN
          REWRITE_TAC [MULT_ASSOC, LT_MULT_RCANCEL, (← ExceptT.mk (HolLight.GSYM RIGHT_SUB_DISTRIB))] THEN
          ASM_REWRITE_TAC [MULT_EQ_0, ARITH_EQ] THEN
          UNDISCH_TAC [[k <= y:num]] THEN
          MATCH_MP_TAC (← tt [[(a ==> ~b) ==> b ==> a ==> c]]) THEN
          DISCH_THEN SUBST1_TAC THEN
          MATCH_MP_TAC (← ar [[1 * y < k * y ==> ~(i + k * y <= y)]]) THEN
          ASM_REWRITE_TAC [LT_MULT_RCANCEL] THEN
          UNDISCH_TAC [[q4 < q5:num]] THEN ARITH_TAC,
          DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← ar
           [[(k + q4 = i + q5) ==> q5 < q4:num ==> (i = k + (q4 - q5))]])) THEN
          REWRITE_TAC [MULT_ASSOC, LT_MULT_RCANCEL, (← ExceptT.mk (HolLight.GSYM RIGHT_SUB_DISTRIB))] THEN
          ASM_REWRITE_TAC [MULT_EQ_0, ARITH_EQ] THEN
          UNDISCH_TAC [[i <= Y a i]] THEN
          MATCH_MP_TAC (← tt [[(a ==> ~b) ==> b ==> a ==> c]]) THEN
          ASM_REWRITE_TAC [] THEN
          DISCH_THEN SUBST1_TAC THEN
          MATCH_MP_TAC (← ar [[1 * y < k * y ==> ~(i + k * y <= y)]]) THEN
          ASM_REWRITE_TAC [LT_MULT_RCANCEL] THEN
          UNDISCH_TAC [[q5 < q4:num]] THEN ARITH_TAC,
          ASM_SIMP_TAC [EQ_ADD_RCANCEL]],
        DISCH_THEN (X_CHOOSE_THEN ([[q6:num]]) MP_TAC) THEN
        ASM_CASES_TAC [[q6 = 0]] THEN ASM_REWRITE_TAC [MULT_CLAUSES, ADD_EQ_0] THEN
        UNDISCH_TAC [[k <= Y a i]] THEN UNDISCH_TAC [[i <= Y a i]] THEN
        SUBST1_TAC (← HolLight.ASSUME [[Y a i = y]]) THEN
        MATCH_MP_TAC (← ar
         [[2 * y < ay ==> i <= y ==> k <= y ==> (i + k = ay) ==> (i = k)]]) THEN
        REWRITE_TAC [MULT_ASSOC, LT_MULT_RCANCEL] THEN ASM_REWRITE_TAC [] THEN
        UNDISCH_TAC [[~(q6 = 0)]] THEN ARITH_TAC]] THEN
    DISCH_THEN (ASSUME_TAC o HolLight.SYM) THEN ABBREV_TAC [[x = X a k]] THEN
    SUBGOAL_THEN ([[x EXP 2 = (a EXP 2 - 1) * y EXP 2 + 1]]) (ASSUME_TAC o HolLight.SYM) THENL
     [MAP_EVERY EXPAND_TAC ["x", "y"] THEN
      SIMP_TAC [XY_ARE_SOLUTIONS, (← HolLight.ASSUME [[~(a = 0)]])], ALL_TAC] THEN
    EXISTS_TAC [[x:num]] THEN ASM_REWRITE_TAC [] THEN
    ABBREV_TAC [[m = 2 * k * Y a k]] THEN
    ABBREV_TAC [[u = X a m]] THEN ABBREV_TAC [[v = Y a m]] THEN
    SUBGOAL_THEN ([[u EXP 2 = (a EXP 2 - 1) * v EXP 2 + 1]]) (ASSUME_TAC o HolLight.SYM) THENL
     [MAP_EVERY EXPAND_TAC ["u", "v"] THEN
      SIMP_TAC [XY_ARE_SOLUTIONS, (← HolLight.ASSUME [[~(a = 0)]])], ALL_TAC] THEN
    EXISTS_TAC [[u:num]] THEN EXISTS_TAC [[v:num]] THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN ([[(y EXP 2) divides v]]) MP_TAC THENL
     [SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← HolLight.ASSUME [[Y a m = v]]))) THEN
      SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← HolLight.ASSUME [[Y a k = y]]))) THEN
      SIMP_TAC [Y2_DIVIDES, (← HolLight.ASSUME [[~(a = 0)]])] THEN
      SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← HolLight.ASSUME [[2 * k * Y a k = m]]))) THEN
      REWRITE_TAC [divides] THEN EXISTS_TAC [[2]] THEN
      REWRITE_TAC [MULT_AC], ALL_TAC] THEN
    REWRITE_TAC [divides] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[r:num]]) (ASSUME_TAC o HolLight.SYM)) THEN
    EXISTS_TAC [[r:num]] THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC [[r = 0]] THENL
     [UNDISCH_TAC [[y EXP 2 * r = v]] THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN
      DISCH_THEN (ASSUME_TAC o HolLight.SYM) THEN REWRITE_TAC [LT_REFL] THEN
      UNDISCH_TAC [[Y a m = v]] THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
      SUBGOAL_THEN ([[m = 0]]) ASSUME_TAC THENL
       [UNDISCH_TAC [[Y a m = 0]] THEN
        ONCE_REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM (← ExceptT.mk (HolLight.CONJUNCT1 Y_CLAUSES))))] THEN
        SIMP_TAC [Y_INJ, (← HolLight.ASSUME [[~(a = 0)]])] THEN
        REWRITE_TAC [Y_CLAUSES], ALL_TAC] THEN
      SUBGOAL_THEN ([[k = 0]]) ASSUME_TAC THENL
       [UNDISCH_TAC [[2 * k * Y a k = m]] THEN
        REWRITE_TAC [(← HolLight.ASSUME [[m = 0]]), MULT_EQ_0, ARITH_EQ] THEN
        ONCE_REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM (← ExceptT.mk (HolLight.CONJUNCT1 Y_CLAUSES))))] THEN
        SIMP_TAC [Y_INJ, (← HolLight.ASSUME [[~(a = 0)]])] THEN
        REWRITE_TAC [Y_CLAUSES, EQ_SYM], ALL_TAC] THEN
      UNDISCH_TAC [[Y a k = y]] THEN ASM_REWRITE_TAC [Y_CLAUSES],
      ALL_TAC] THEN
    ASM_SIMP_TAC [(← ar [[~(r = 0) ==> 0 < r]])] THEN
    SUBGOAL_THEN ([[ODD(u)]]) ASSUME_TAC THENL
     [UNDISCH_TAC [[(a EXP 2 - 1) * v EXP 2 + 1 = u EXP 2]] THEN
      DISCH_THEN (MP_TAC o HolLight.AP_TERM [[EVEN]]) THEN
      REWRITE_TAC [EXP_2, EVEN_ADD, EVEN_MULT, ARITH_EVEN] THEN
      SUBGOAL_THEN ([[EVEN v]]) (fun th => HolLight.tactic_of do
        let g ← HolLight.GSYM NOT_EVEN
        pure (REWRITE_TAC [g, th])) THEN
      SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← HolLight.ASSUME [[Y a m = v]]))) THEN
      MP_TAC (SPECL [ [[a:num]], [[m:num]] ] Y_N_MOD2) THEN
      SIMP_TAC [(← HolLight.ASSUME [[~(a = 0)]]), LEFT_IMP_EXISTS_THM] THEN
      SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← HolLight.ASSUME [[2 * k * Y a k = m]]))) THEN
      REWRITE_TAC [EVEN_ADD, EVEN_MULT, ARITH_EVEN], ALL_TAC] THEN
    SUBGOAL_THEN ([[?b0 q6 q7. (b0 = 1 + q6 * 4 * y) /\ (b0 = a + q7 * u)]])
    MP_TAC THENL
     [MATCH_MP_TAC CHINESE_REMAINDER THEN
      UNDISCH_TAC [[ODD u]] THEN
      ASM_CASES_TAC [[u = 0]] THEN ASM_REWRITE_TAC [ARITH_ODD] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC [MULT_EQ_0, ARITH_EQ] THEN
      ONCE_REWRITE_TAC [COPRIME_SYM] THEN MATCH_MP_TAC COPRIME_MUL THEN
      CONJ_TAC THENL
       [SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← ExceptT.mk (NUM_REDUCE_CONV [[2 * 2]])))) THEN
        MATCH_MP_TAC COPRIME_MUL THEN REWRITE_TAC [] THEN
        MP_TAC (SPECL [ [[u:num]], [[2]] ] PRIME_COPRIME) THEN REWRITE_TAC [PRIME_2] THEN
        MATCH_MP_TAC (← tt [[~b /\ (a ==> d) /\ (c ==> d)
                         ==> a \/ b \/ c ==> d]]) THEN
        REPEAT CONJ_TAC THENL
         [UNDISCH_TAC [[ODD u]] THEN
          ONCE_REWRITE_TAC [(← tt [[a ==> b <=> ~b ==> ~a]])] THEN
          SIMP_TAC [divides, LEFT_IMP_EXISTS_THM, ODD_MULT, ARITH_ODD],
          ONCE_REWRITE_TAC [COPRIME_SYM] THEN SIMP_TAC [COPRIME_1],
          REWRITE_TAC [COPRIME_SYM]],
        MP_TAC (SPECL [ [[a:num]], [[m:num]] ] XY_COPRIME) THEN ASM_REWRITE_TAC [] THEN
        SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← HolLight.ASSUME [[y EXP 2 * r = v]]))) THEN
        REWRITE_TAC [coprime, EXP_2] THEN
        MESON_TAC [DIVIDES_RMUL, DIVIDES_LMUL]], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[b:num]]) (X_CHOOSE_THEN ([[p:num]])
          (X_CHOOSE_THEN ([[q:num]]) (STRIP_ASSUME_TAC o HolLight.GSYM)))) THEN
    MAP_EVERY EXISTS_TAC [ [[b:num]], [[p:num]], [[q:num]] ] THEN
    ONCE_REWRITE_TAC [(← ar [[1 + 4 * p * y = 1 + p * 4 * y]])] THEN
    ASM_REWRITE_TAC [] THEN
    ABBREV_TAC [[s = X b k]] THEN ABBREV_TAC [[t = Y b k]] THEN
    EXISTS_TAC [[s:num]] THEN EXISTS_TAC [[t:num]] THEN
    SUBST1_TAC (← ar [[r * y EXP 2 = y EXP 2 * r]]) THEN
    ASM_REWRITE_TAC [] THEN
    SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← HolLight.ASSUME [[X b k = s]]))) THEN
    SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← HolLight.ASSUME [[Y b k = t]]))) THEN
    SUBGOAL_THEN ([[~(b = 0)]]) ASSUME_TAC THENL
     [UNDISCH_THEN ([[1 + p * 4 * y = b]]) (SUBST1_TAC o HolLight.SYM) THEN
      ONCE_REWRITE_TAC [(← tt [[~b ==> a ==> b ==> ~a]])] THEN
      REWRITE_TAC [ADD_EQ_0, ARITH_EQ], ALL_TAC] THEN
    SIMP_TAC [XY_ARE_SOLUTIONS, (← HolLight.ASSUME [[~(b = 0)]])] THEN
    MP_TAC (SPECL [ [[a:num]], [[q:num]], [[u:num]], [[k:num]] ] X_CONGRUENT) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[c:num]]) (ASSUME_TAC o HolLight.SYM)) THEN
    EXISTS_TAC [[c:num]] THEN ASM_REWRITE_TAC [] THEN
    MP_TAC (SPECL [ [[b:num]], [[k:num]] ] Y_N_MODA1) THEN
    SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← HolLight.ASSUME [[1 + p * 4 * y = b]]))) THEN
    REWRITE_TAC [ADD_EQ_0, ADD_SUB2, ARITH_EQ] THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[q8:num]]) SUBST1_TAC) THEN
    EXISTS_TAC [[q8 * p:num]] THEN REWRITE_TAC [MULT_AC, ADD_AC] THEN
    MP_TAC (SPECL [ [[a:num]], [[k:num]] ] Y_N_MODA1) THEN
    ASM_SIMP_TAC [LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.ONCE_REWRITE_RULE [ADD_SYM] LE_ADD))])
  : ExceptT String IO thm).run
#eval Y_DIOPH

-- ------------------------------------------------------------------------- --
-- A ratio approaches a^n for large enough k.                                --
-- ------------------------------------------------------------------------- --

#eval phrase 58
unsafe def BINOMIALISH_LEMMA : thm := keep "BINOMIALISH_LEMMA" fun _ => (do
  prove ([[!m n. m EXP n * (m - n) <= m * (m - 1) EXP n]])
   (GEN_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC [EXP, SUB_0, MULT_CLAUSES, LE_REFL] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC [[(m - 1) * m EXP n * (m - n)]] THEN CONJ_TAC THENL
     [REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM MULT_ASSOC))] THEN
      ONCE_REWRITE_TAC [(← ExceptT.mk (AC MULT_AC [[a * b * c = b * a * c:num]]))] THEN
      REWRITE_TAC [LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
      REWRITE_TAC [LEFT_SUB_DISTRIB, RIGHT_SUB_DISTRIB, MULT_CLAUSES] THEN
      ONCE_REWRITE_TAC [(← ar [[a - (b + c) = a - c - b:num]])] THEN
      MATCH_MP_TAC (← ar [[c <= b ==> a - b <= a - c:num]]) THEN ARITH_TAC,
      GEN_REWRITE_TAC HolLight.RAND_CONV
       [(← ExceptT.mk (AC MULT_AC [[m * (m - 1) * n = (m - 1) * m * n]]))] THEN
      ASM_REWRITE_TAC [LE_MULT_LCANCEL]])
  : ExceptT String IO thm).run
#eval BINOMIALISH_LEMMA

#eval phrase 59
unsafe def XY_EXP_LEMMA : thm := keep "XY_EXP_LEMMA" fun _ => (do
  prove ([[!a k n.
        ~(a = 0) /\
        2 * n * a EXP n < k
        ==> abs(&(Y (a * k) (n + 1)) / &(Y k (n + 1)) - &a pow n) < &1 / &2]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[~(k = 0)]]) ASSUME_TAC THENL
     [FIRST_ASSUM (ACCEPT_TAC o HolLight.MATCH_MP (← ar
       [[a < k ==> ~(k = 0)]])), ALL_TAC] THEN
    SUBGOAL_THEN ([[0 < Y k (n + 1)]]) ASSUME_TAC THENL
     [SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← ExceptT.mk (HolLight.SPEC ([[k:num]]) (← ExceptT.mk (HolLight.CONJUNCT1 Y_CLAUSES)))))) THEN
      ASM_SIMP_TAC [Y_INCREASES_LT, (← ar [[0 < n + 1]])],
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
    EXISTS_TAC [[abs(&(Y k (n + 1)))]] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_ABS_MUL)), REAL_SUB_LDISTRIB] THEN
    ASM_SIMP_TAC [REAL_ABS_NUM, REAL_LT_IMP_NZ,
                 REAL_OF_NUM_LT, REAL_DIV_LMUL] THEN
    REWRITE_TAC [real_div, REAL_MUL_LID, REAL_MUL_ASSOC] THEN
    SIMP_TAC [(← ExceptT.mk (HolLight.GSYM real_div)), REAL_OF_NUM_LT, ARITH, REAL_LT_RDIV_EQ] THEN
    MATCH_MP_TAC (← rr
     [[!lx ly ux uy.
        lx <= x /\ x <= ux /\ ly <= y /\ y <= uy /\
        &2 * uy < &2 * lx + d /\ &2 * ux < &2 * ly + d
        ==> abs(x - y) * &2 < d]]) THEN
    MAP_EVERY EXISTS_TAC
     [ [[&((2 * a * k - 1) EXP n)]], [[&((2 * k - 1) EXP n) * &a pow n]],
      [[&((2 * a * k) EXP n)]], [[&((2 * k) EXP n) * &a pow n]] ] THEN
    ASM_SIMP_TAC [REAL_OF_NUM_LE, Y_LOWERBOUND, Y_UPPERBOUND,
                 REAL_LE_RMUL_EQ, REAL_POW_LT, REAL_OF_NUM_LT,
                 (← ar [[~(a = 0) ==> 0 < a]])] THEN
    REWRITE_TAC [REAL_OF_NUM_ADD, REAL_OF_NUM_POW, REAL_OF_NUM_MUL] THEN
    REWRITE_TAC [REAL_OF_NUM_LT] THEN
    MATCH_MP_TAC (← ar
     [[!x:num. x <= c /\ a < b + x /\ d < e + x ==> a < b + c /\ d < e + c]]) THEN
    EXISTS_TAC [[(2 * k - 1) EXP n]] THEN REWRITE_TAC [Y_LOWERBOUND] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM MULT_EXP)), (← ExceptT.mk (HolLight.GSYM MULT_ASSOC))] THEN
    REWRITE_TAC [RIGHT_SUB_DISTRIB, (← ExceptT.mk (HolLight.GSYM MULT_ASSOC))] THEN
    SUBST1_TAC (← ExceptT.mk (AC MULT_AC [[2 * k * a = 2 * a * k]])) THEN
    REWRITE_TAC [MULT_CLAUSES] THEN
    MATCH_MP_TAC (← ar
     [[b' <= b /\ a < b' + c ==> a < b + c /\ a < b' + c:num]]) THEN
    CONJ_TAC THENL
     [REWRITE_TAC [LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
      SPEC_TAC ([[n:num]], [[m:num]]) THEN
      INDUCT_TAC THEN REWRITE_TAC [(← ExceptT.mk (HolLight.CONJUNCT1 EXP)), LE_REFL] THEN
      REWRITE_TAC [EXP_MONO_LE, NOT_SUC] THEN
      UNDISCH_TAC [[~(a = 0)]] THEN ARITH_TAC,
      ALL_TAC] THEN
    SUBST1_TAC (← ExceptT.mk (AC MULT_AC [[2 * a * k = 2 * k * a]])) THEN
    GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.LAND_CONV o HolLight.RAND_CONV o HolLight.LAND_CONV o HolLight.RAND_CONV)
     [(← ar [[a = 1 * a]])] THEN
    REWRITE_TAC [MULT_ASSOC, (← ExceptT.mk (HolLight.GSYM RIGHT_SUB_DISTRIB))] THEN
    REWRITE_TAC [MULT_EXP] THEN
    REWRITE_TAC [(← ar [[2 * e * a + e = (2 * a + 1) * e]])] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM MULT_EXP)), (← ExceptT.mk (HolLight.GSYM MULT_ASSOC))] THEN
    SUBST1_TAC (← ExceptT.mk (AC MULT_AC [[2 * k * a = a * 2 * k]])) THEN
    ONCE_REWRITE_TAC [MULT_EXP] THEN REWRITE_TAC [MULT_ASSOC] THEN
    SUBGOAL_THEN ([[(2 * k) * (2 * a EXP n) * (2 * k) EXP n <
                (2 * k) * (2 * a EXP n + 1) * (2 * k - 1) EXP n]])
    MP_TAC THENL
     [ALL_TAC, ASM_SIMP_TAC [LT_MULT_LCANCEL, MULT_EQ_0, ARITH_EQ]] THEN
    GEN_REWRITE_TAC HolLight.RAND_CONV
     [(← ExceptT.mk (AC MULT_AC [[(2 * k) * l * m = l * (2 * k) * m]]))] THEN
    MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC [[(2 * a EXP n + 1) * (2 * k) EXP n * (2 * k - n)]] THEN
    CONJ_TAC THENL
     [ALL_TAC, REWRITE_TAC [LE_MULT_LCANCEL, BINOMIALISH_LEMMA]] THEN
    REWRITE_TAC [(← ar
     [[(2 * k) * (2 * an) * 2kn < a2na * 2kn * kmn <=>
    2kn * 4 * k * an < 2kn * a2na * kmn]])] THEN
    ASM_SIMP_TAC [LT_MULT_LCANCEL, EXP_EQ_0, MULT_EQ_0, ARITH_EQ] THEN
    REWRITE_TAC [LEFT_SUB_DISTRIB] THEN
    MATCH_MP_TAC (← ar [[a + b < c ==> a < c - b:num]]) THEN
    REWRITE_TAC [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_CLAUSES] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM MULT_ASSOC))] THEN
    REWRITE_TAC [(← ar [[4 * k * an + x < 2 * an * 2 * k + y <=> x < y]])] THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (AC MULT_AC [[2 * a * n = 2 * n * a]]))] THEN
    UNDISCH_TAC [[2 * n * a EXP n < k]] THEN
    MATCH_MP_TAC (← ar
     [[n * 1 <= x ==> 2 * x < k ==> 2 * x + n < 2 * k]]) THEN
    ASM_REWRITE_TAC [LE_MULT_LCANCEL, (← ar [[1 <= n <=> ~(n = 0)]])] THEN
    ASM_REWRITE_TAC [EXP_EQ_0])
  : ExceptT String IO thm).run
#eval XY_EXP_LEMMA

#eval phrase 60
unsafe def ABS_LT_REPRESENTATION : thm := keep "ABS_LT_REPRESENTATION" fun _ => (do
  prove ([[!x y z.
    ~(y = 0)
    ==> (abs(&x / &y - &z) < &1 / &2 <=>
         4 * x EXP 2 + 4 * (y * z) EXP 2 < 8 * x * y * z + y EXP 2)]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC [[&4 * (&x / &y - &z) pow 2 < &1]] THEN CONJ_TAC THENL
     [SIMP_TAC [REAL_LT_RDIV_EQ, REAL_OF_NUM_LT, ARITH] THEN
      SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← ExceptT.mk (REAL_RAT_REDUCE_CONV [[&2 * &2]])))) THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_POW_2)), (← ExceptT.mk (HolLight.GSYM REAL_POW_MUL))] THEN
      ONCE_REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_POW2_ABS))] THEN
      REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_NUM] THEN EQ_TAC THENL
       [GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.RAND_CONV)
         [(← ExceptT.mk (HolLight.SYM (← ExceptT.mk (REAL_RAT_REDUCE_CONV [[&1 pow 2]]))))] THEN
        GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.LAND_CONV) [REAL_MUL_SYM] THEN
        SIMP_TAC [ARITH_EQ, REAL_POW_LT2, REAL_LE_MUL, REAL_POS, REAL_ABS_POS],
        ONCE_REWRITE_TAC [(← tt [[a ==> b <=> ~b ==> ~a]])] THEN
        REWRITE_TAC [REAL_NOT_LT] THEN
        GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.LAND_CONV)
         [(← ExceptT.mk (HolLight.SYM (← ExceptT.mk (REAL_RAT_REDUCE_CONV [[&1 pow 2]]))))] THEN
        GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV) [REAL_MUL_SYM] THEN
        SIMP_TAC [ARITH_EQ, REAL_POW_LE2, REAL_LE_MUL, REAL_POS, REAL_ABS_POS]],
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC [[&4 * (&x - &y * &z) pow 2 < &y pow 2]] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.RAND_CONV) [(← ExceptT.mk (HolLight.GSYM REAL_POW2_ABS))] THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_ABS_POW))] THEN
      GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.RAND_CONV) [(← ExceptT.mk (HolLight.GSYM REAL_MUL_LID))] THEN
      ASM_SIMP_TAC [(← ExceptT.mk (HolLight.GSYM REAL_LT_LDIV_EQ)), (← ExceptT.mk (HolLight.GSYM REAL_ABS_NZ)), REAL_POW_EQ_0,
                   ARITH_EQ, REAL_OF_NUM_EQ] THEN
      REWRITE_TAC [REAL_ABS_POW, REAL_POW2_ABS] THEN
      REWRITE_TAC [real_div, (← ExceptT.mk (HolLight.GSYM REAL_MUL_ASSOC))] THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM real_div)), (← ExceptT.mk (HolLight.GSYM REAL_POW_DIV))] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC [real_div, REAL_SUB_RDISTRIB, (← ExceptT.mk (HolLight.GSYM REAL_MUL_ASSOC))] THEN
      AP_TERM_TAC THEN
      ASM_SIMP_TAC [(← ExceptT.mk (HolLight.GSYM real_div)), REAL_DIV_LMUL, REAL_OF_NUM_EQ], ALL_TAC] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_LT)), (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_ADD)),
                (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_MUL)), (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_POW))] THEN
    REWRITE_TAC [REAL_POW_2] THEN REAL_ARITH_TAC)
  : ExceptT String IO thm).run
#eval ABS_LT_REPRESENTATION

#eval phrase 61
unsafe def Y_EQ_0 : thm := keep "Y_EQ_0" fun _ => (do
  prove ([[!a n. ~(a = 0) ==> ((Y a n = 0) <=> (n = 0))]])
   (REPEAT STRIP_TAC THEN
    SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← ExceptT.mk (HolLight.SPEC ([[a:num]]) (← ExceptT.mk (HolLight.CONJUNCT1 Y_CLAUSES)))))) THEN
    ASM_SIMP_TAC [Y_INJ] THEN REWRITE_TAC [Y_CLAUSES])
  : ExceptT String IO thm).run
#eval Y_EQ_0

#eval phrase 62
unsafe def XY_EXP : thm := keep "XY_EXP" fun _ => (do
  let lemma1 ← prove ([[(?x y z. (a = x) /\ (b = y) /\ (c = z) /\ P x y z) <=> P a b c]])
    (MESON_TAC [])
  let lemma2 ← (ExceptT.mk (HolLight.CONV_RULE (HolLight.RAND_CONV (HolLight.ONCE_DEPTH_CONV HolLight.SYM_CONV))
             (← ExceptT.mk (HolLight.SPEC_ALL ABS_LT_REPRESENTATION))) : ExceptT String IO thm)
  prove ([[~(a = 0)
   ==> ((a EXP n = p) <=>
        ?k x y z. (Y (a * k) (n + 1) = x) /\
                  (Y k (n + 1) = y) /\
                  (Y a (n + 1) = z) /\
                  2 * n * z < k /\
                  4 * x EXP 2 + 4 * (y * p) EXP 2 < 8 * x * y * p + y EXP 2)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [lemma1] THEN
    GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.BINDER_CONV o HolLight.LAND_CONV)
      [(← ar [[n < k <=> n < k /\ ~(k = 0)]])] THEN
    ONCE_REWRITE_TAC [(← tt [[a /\ b <=> ~(a ==> ~b)]])] THEN
    ASM_SIMP_TAC [lemma2, Y_EQ_0, ADD_EQ_0, ARITH_EQ] THEN
    REWRITE_TAC [NOT_IMP] THEN
    REWRITE_TAC [(← ar [[n < k /\ ~(k = 0) <=> n < k]])] THEN
    EQ_TAC THENL
     [DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN
      EXISTS_TAC [[2 * n * Y a (n + 1) + 1]] THEN
      REWRITE_TAC [(← ar [[c < c + 1]]), (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_POW))] THEN
      MATCH_MP_TAC XY_EXP_LEMMA THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC (← ar [[a <= b ==> 2 * a < 2 * b + 1]]) THEN
      REWRITE_TAC [LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC [[(2 * a - 1) EXP n]] THEN
      REWRITE_TAC [Y_LOWERBOUND] THEN
      SPEC_TAC ([[n:num]], [[n:num]]) THEN INDUCT_TAC THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.CONJUNCT1 EXP)), LE_REFL, EXP_MONO_LE, NOT_SUC] THEN
      UNDISCH_TAC [[~(a = 0)]] THEN ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[k:num]]) (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MP_TAC (SPECL [ [[a:num]], [[k:num]], [[n:num]] ] XY_EXP_LEMMA) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← ar
       [[2 * a < k ==> b <= a ==> 2 * b < k]])) THEN
      REWRITE_TAC [LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC [[(2 * a - 1) EXP n]] THEN
      REWRITE_TAC [Y_LOWERBOUND] THEN
      SPEC_TAC ([[n:num]], [[n:num]]) THEN INDUCT_TAC THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.CONJUNCT1 EXP)), LE_REFL, EXP_MONO_LE, NOT_SUC] THEN
      UNDISCH_TAC [[~(a = 0)]] THEN ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [IMP_IMP] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← rr
     [[abs(x - a) < e1 /\ abs(x - b) < e2 ==> abs(a - b) < e1 + e2]])) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← rr
     [[abs(a - b) < &1
    ==> a + &1 <= b \/ (a = b) \/ b + &1 <= a ==> (a = b)]])) THEN
    REWRITE_TAC [REAL_OF_NUM_POW, REAL_OF_NUM_ADD,
                REAL_OF_NUM_EQ, REAL_OF_NUM_LE] THEN
    DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval XY_EXP

-- ------------------------------------------------------------------------- --
-- Lemmas.                                                                   --
-- ------------------------------------------------------------------------- --

#eval phrase 63
unsafe def REAL_SUM_OF_SQUARES : thm := keep "REAL_SUM_OF_SQUARES" fun _ => (do
  prove ([[(x pow 2 + y pow 2 = &0) <=> (x = &0) /\ (y = &0)]])
   (REWRITE_TAC [REAL_POW_2] THEN EQ_TAC THEN
    SIMP_TAC [REAL_MUL_LZERO, REAL_ADD_LID] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← rr
     [[(a + b = &0) ==> &0 <= a /\ &0 <= b ==> (a = &0) /\ (b = &0)]])) THEN
    REWRITE_TAC [REAL_LE_SQUARE, REAL_ENTIRE])
  : ExceptT String IO thm).run
#eval REAL_SUM_OF_SQUARES

-- ------------------------------------------------------------------------- --
-- Combining theorems for conjunction and disjunction.                       --
-- ------------------------------------------------------------------------- --

#eval phrase 64
unsafe def DIOPH_CONJ : thm := keep "DIOPH_CONJ" fun _ => (do
  prove ([[(x1 = x2) /\ (y1 = y2) <=>
   (x1 * x1 + x2 * x2 + y1 * y1 + y2 * y2 = 2 * x1 * x2 + 2 * y1 * y2)]])
   (REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_EQ)),
      (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_ADD)), (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_MUL))] THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_SUB_0))] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_SUM_OF_SQUARES))] THEN
    REWRITE_TAC [REAL_POW_2] THEN REAL_ARITH_TAC)
  : ExceptT String IO thm).run
#eval DIOPH_CONJ

#eval phrase 65
unsafe def DIOPH_DISJ : thm := keep "DIOPH_DISJ" fun _ => (do
  prove ([[(x1 = x2) \/ (y1 = y2) <=>
   (x1 * y1 + x2 * y2 = x1 * y2 + x2 * y1)]])
   (REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_EQ)),
      (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_ADD)), (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_MUL))] THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_SUB_0))] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_ENTIRE))] THEN REAL_ARITH_TAC)
  : ExceptT String IO thm).run
#eval DIOPH_DISJ

-- ------------------------------------------------------------------------- --
-- Inequalities.                                                             --
-- ------------------------------------------------------------------------- --

#eval phrase 66
unsafe def DIOPH_LE : thm := keep "DIOPH_LE" fun _ => (do
  prove ([[x <= y <=> ?d:num. x + d = y]])
   (REWRITE_TAC [LE_EXISTS] THEN
    AP_TERM_TAC THEN ABS_TAC THEN
    REWRITE_TAC [ADD_AC, EQ_SYM_EQ])
  : ExceptT String IO thm).run
#eval DIOPH_LE

#eval phrase 67
unsafe def DIOPH_LT : thm := keep "DIOPH_LT" fun _ => (do
  prove ([[x < y <=> ?d. x + d + 1 = y]])
   (REWRITE_TAC [LT_EXISTS] THEN
    REWRITE_TAC [ADD1] THEN
    AP_TERM_TAC THEN ABS_TAC THEN
    REWRITE_TAC [ADD_AC, EQ_SYM_EQ])
  : ExceptT String IO thm).run
#eval DIOPH_LT

#eval phrase 68
unsafe def DIOPH_NE : thm := keep "DIOPH_NE" fun _ => (do
  prove ([[~(x = y) <=> x < y \/ y < x:num]])
   (ARITH_TAC)
  : ExceptT String IO thm).run
#eval DIOPH_NE

-- ------------------------------------------------------------------------- --
-- Exponentiation (from the Pell stuff).                                     --
-- ------------------------------------------------------------------------- --

#eval phrase 69
unsafe def Y_0 : thm := keep "Y_0" fun _ => (do
  prove ([[!k. Y 0 k = if k = 1 then 1 else 0]])
   (INDUCT_TAC THEN REWRITE_TAC [Y_CLAUSES, ARITH_EQ] THEN
    SPEC_TAC ([[k:num]], [[k:num]]) THEN
    INDUCT_TAC THEN REWRITE_TAC [Y_CLAUSES, ARITH] THEN
    REWRITE_TAC [(← ar [[SUC(SUC n) = n + 2]]), Y_CLAUSES, ARITH] THEN
    REWRITE_TAC [MULT_CLAUSES, SUB_0, (← ar [[~(k + 2 = 1)]])])
  : ExceptT String IO thm).run
#eval Y_0

#eval phrase 70
unsafe def Y_0_TRIV : thm := keep "Y_0_TRIV" fun _ => (do
  prove ([[!k. (Y 0 k = 0) <=> ~(k = 1)]])
   (GEN_TAC THEN REWRITE_TAC [Y_0] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [ARITH_EQ])
  : ExceptT String IO thm).run
#eval Y_0_TRIV

#eval phrase 71
unsafe def DIOPH_Y : thm := keep "DIOPH_Y" fun _ => (do
  prove ([[(Y a k = y) <=>
        (a = 0) /\ (k = 1) /\ (y = 1) \/
        (a = 0) /\ ~(k = 1) /\ (y = 0) \/
        (k = 0) /\ (y = 0) \/
        (a = 1) /\ (y = k) \/
        ~(a = 0) /\ ~(k = 0) /\ ~(a = 1) /\ ~(y = 0) /\
        ?x u v r b p q s t c d.
                0 < r /\
                (x EXP 2 = (a EXP 2 - 1) * y EXP 2 + 1) /\
                (u EXP 2 = (a EXP 2 - 1) * v EXP 2 + 1) /\
                (s EXP 2 = (b EXP 2 - 1) * t EXP 2 + 1) /\
                (v = r * y EXP 2) /\
                (b = 1 + 4 * p * y) /\
                (b = a + q * u) /\
                (s = x + c * u) /\
                (t = k + 4 * d * y) /\
                k <= y]])
   (ASM_CASES_TAC [[a = 0]] THENL
     [ASM_CASES_TAC [[y = 0]] THENL
       [ASM_REWRITE_TAC [Y_0_TRIV, ARITH_EQ] THEN ARITH_TAC, ALL_TAC] THEN
      ASM_CASES_TAC [[k = 0]] THEN ASM_REWRITE_TAC [Y_CLAUSES, ARITH_EQ] THEN
      ASM_REWRITE_TAC [ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES] THEN
      REWRITE_TAC [EXP_2, MULT_EQ_1] THEN
      REWRITE_TAC [Y_0] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [EQ_SYM_EQ], ALL_TAC] THEN
    ASM_REWRITE_TAC [ARITH_EQ] THEN
    ASM_CASES_TAC [[k = 0]] THEN ASM_REWRITE_TAC [Y_CLAUSES] THENL
     [REWRITE_TAC [EQ_SYM_EQ] THEN CONV_TAC (fun t => (do HolLight.EQT_INTRO (← ExceptT.mk (TAUT t)) : ExceptT String IO thm).run), ALL_TAC] THEN
    ASM_CASES_TAC [[a = 1]] THEN ASM_REWRITE_TAC [Y_DEGENERATE] THENL
     [REWRITE_TAC [EQ_SYM_EQ], ALL_TAC] THEN
    ASM_CASES_TAC [[y = 0]] THEN ASM_SIMP_TAC [Y_EQ_0] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [EQ_SYM_EQ] THEN ASM_SIMP_TAC [Y_DIOPH])
  : ExceptT String IO thm).run
#eval DIOPH_Y

#eval phrase 72
unsafe def DIOPH_EXP_LEMMA : thm := keep "DIOPH_EXP_LEMMA" fun _ => (do
  prove ([[(m EXP n = p) <=>
        (m = 0) /\ (n = 0) /\ (p = 1) \/
        (m = 0) /\ ~(n = 0) /\ (p = 0) \/
        ~(m = 0) /\
        ?k x y z. (Y (m * k) (n + 1) = x) /\
                  (Y k (n + 1) = y) /\
                  (Y m (n + 1) = z) /\
                  2 * n * z < k /\
                  4 * x EXP 2 + 4 * (y * p) EXP 2 < 8 * x * y * p + y EXP 2]])
   (ASM_CASES_TAC [[m = 0]] THEN ASM_REWRITE_TAC [ARITH_EQ] THENL
     [SPEC_TAC ([[n:num]], [[n:num]]) THEN INDUCT_TAC THEN
      REWRITE_TAC [EXP, MULT_CLAUSES, ADD_CLAUSES, NOT_SUC] THEN
      REWRITE_TAC [EQ_SYM_EQ], ALL_TAC] THEN
    ASM_SIMP_TAC [XY_EXP])
  : ExceptT String IO thm).run
#eval DIOPH_EXP_LEMMA

#eval phrase 73
unsafe def DIOPH_EXP : thm := keep "DIOPH_EXP" fun _ => (do
  let th1 ← ExceptT.mk (REWRITE_RULE [DIOPH_Y] DIOPH_EXP_LEMMA)
  let th2 ← ExceptT.mk (REWRITE_RULE [EXP_2] th1)
  let th3 ← ExceptT.mk (REWRITE_RULE [DIOPH_NE, DIOPH_LT, DIOPH_LE] th2)
  let th4 ← ExceptT.mk (REWRITE_RULE [ADD_CLAUSES, ARITH_EQ, ADD_EQ_0,
    (← ar [[(n + 1 = 1) = (n = 0)]]), ADD_ASSOC,
    EQ_ADD_RCANCEL] th3)
  let th5 ← ExceptT.mk (REWRITE_RULE [(← ExceptT.mk (HolLight.GSYM ADD_ASSOC))] th4)
  ExceptT.mk (REWRITE_RULE
   [OR_EXISTS_THM, LEFT_OR_EXISTS_THM, RIGHT_OR_EXISTS_THM,
    LEFT_AND_EXISTS_THM, RIGHT_AND_EXISTS_THM] th5)
  : ExceptT String IO thm).run
#eval DIOPH_EXP
end HolExamples.Pell
