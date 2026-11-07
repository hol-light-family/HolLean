/- File: Hol100/FourSquares.lean
Translation of HOL Light's 100/four_squares.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionLibrary.Prime
import SessionLibrary.Analysis
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Prime SessionLibrary.Analysis
namespace Hol100.FourSquares

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def nrc (tm : term) : ExceptT String IO thm := ExceptT.mk (NUM_REDUCE_CONV tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)
private def rrc (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_RAT_REDUCE_CONV tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)

/- ========================================================================= -/
/- Theorems about representations as sums of 2 and 4 squares.                -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Library/prime.ml";;
#eval SessionLibrary.Prime.ensurePrime

#eval phrase 2
-- needs "Library/analysis.ml";;
#eval SessionLibrary.Analysis.ensureAnalysis

/-** only for REAL_ARCH_LEAST! **-/

#eval phrase 3
#eval Session.prioritize_num

/- ------------------------------------------------------------------------- -/
/- Definition of involution and various basic lemmas.                        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 4
def involution : thm := keep "involution" fun _ => new_definition
 [[involution f s = !x. x IN s ==> f(x) IN s /\ (f(f(x)) = x)]]
#eval involution

#eval phrase 5
def INVOLUTION_IMAGE : thm := keep "INVOLUTION_IMAGE" fun _ => (do
  prove ([[!f s. involution f s ==> (IMAGE f s = s)]])
   (REWRITE_TAC [involution, EXTENSION, IN_IMAGE] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval INVOLUTION_IMAGE

#eval phrase 6
def INVOLUTION_DELETE : thm := keep "INVOLUTION_DELETE" fun _ => (do
  prove ([[involution f s /\ a IN s /\ (f a = a) ==> involution f (s DELETE a)]])
   (REWRITE_TAC [involution, IN_DELETE] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval INVOLUTION_DELETE

#eval phrase 7
def INVOLUTION_STEPDOWN : thm := keep "INVOLUTION_STEPDOWN" fun _ => (do
  prove ([[involution f s /\ a IN s ==> involution f (s DIFF {a, (f a)})]])
   (REWRITE_TAC [involution, IN_DIFF, IN_INSERT, NOT_IN_EMPTY] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval INVOLUTION_STEPDOWN

#eval phrase 8
def INVOLUTION_NOFIXES : thm := keep "INVOLUTION_NOFIXES" fun _ => (do
  prove ([[involution f s ==> involution f {x | x IN s /\ ~(f x = x)}]])
   (REWRITE_TAC [involution, IN_ELIM_THM] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval INVOLUTION_NOFIXES

#eval phrase 9
def INVOLUTION_SUBSET : thm := keep "INVOLUTION_SUBSET" fun _ => (do
  prove ([[!f s t. involution f s /\ (!x. x IN t ==> f(x) IN t) /\ t SUBSET s
           ==> involution f t]])
   (REWRITE_TAC [involution, SUBSET] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval INVOLUTION_SUBSET

#eval phrase 10
def INVOLUTION_EVEN : thm := keep "INVOLUTION_EVEN" fun _ => (do
  prove ([[!s. FINITE(s) /\ involution f s /\ (!x:A. x IN s ==> ~(f x = x))
       ==> EVEN(CARD s)]])
   (REWRITE_TAC [involution] THEN MESON_TAC [INVOLUTION_EVEN_NOFIXPOINTS])
  : ExceptT String IO thm).run
#eval INVOLUTION_EVEN

/- ------------------------------------------------------------------------- -/
/- So an involution with exactly one fixpoint has odd card domain.           -/
/- ------------------------------------------------------------------------- -/

#eval phrase 11
def INVOLUTION_FIX_ODD : thm := keep "INVOLUTION_FIX_ODD" fun _ => (do
  prove ([[FINITE(s) /\ involution f s /\ (?!a:A. a IN s /\ (f a = a))
   ==> ODD(CARD s)]])
   (REWRITE_TAC [EXISTS_UNIQUE_DEF] THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[s = (a:A) INSERT (s DELETE a)]]) SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_INSERT, IN_DELETE] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    ASM_SIMP_TAC [CARD_CLAUSES, FINITE_DELETE, IN_DELETE, ODD, NOT_ODD] THEN
    MATCH_MP_TAC INVOLUTION_EVEN THEN
    ASM_SIMP_TAC [INVOLUTION_DELETE, FINITE_DELETE, IN_DELETE] THEN
    ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval INVOLUTION_FIX_ODD

/- ------------------------------------------------------------------------- -/
/- And an involution on a set of odd finite card must have a fixpoint.       -/
/- ------------------------------------------------------------------------- -/

#eval phrase 12
def INVOLUTION_ODD : thm := keep "INVOLUTION_ODD" fun _ => (do
  prove ([[!n s. FINITE(s) /\ involution f s /\ ODD(CARD s)
         ==> ?a. a IN s /\ (f a = a)]])
   (REWRITE_TAC [(← HolLight.GSYM NOT_EVEN)] THEN MESON_TAC [INVOLUTION_EVEN])
  : ExceptT String IO thm).run
#eval INVOLUTION_ODD

/- ------------------------------------------------------------------------- -/
/- Consequently, if one involution has a unique fixpoint, other has one.     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 13
def INVOLUTION_FIX_FIX : thm := keep "INVOLUTION_FIX_FIX" fun _ => (do
  prove ([[!f g s. FINITE(s) /\ involution f s /\ involution g s /\
           (?!x. x IN s /\ (f x = x)) ==> ?x. x IN s /\ (g x = x)]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC INVOLUTION_ODD THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC INVOLUTION_FIX_ODD THEN
    ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval INVOLUTION_FIX_FIX

/- ------------------------------------------------------------------------- -/
/- Formalization of Zagier's "one-sentence" proof over the natural numbers.  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 14
def zset : thm := keep "zset" fun _ => new_definition
 [[zset(a) = {(x,y,z) | x EXP 2 + 4 * y * z = a}]]
#eval zset

#eval phrase 15
def zag : thm := keep "zag" fun _ => new_definition
 [[zag(x,y,z) =
        if x + z < y then (x + 2 * z,z,y - (x + z))
        else if x < 2 * y then (2 * y - x, y, (x + z) - y)
        else (x - 2 * y,(x + z) - y, y)]]
#eval zag

#eval phrase 16
def tag : thm := keep "tag" fun _ => new_definition
 [[tag((x,y,z):num#num#num) = (x,z,y)]]
#eval tag

#eval phrase 17
def ZAG_INVOLUTION_GENERAL : thm := keep "ZAG_INVOLUTION_GENERAL" fun _ => (do
  prove ([[0 < x /\ 0 < y /\ 0 < z ==> (zag(zag(x,y,z)) = (x,y,z))]])
   (REWRITE_TAC [zag] THEN REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    REWRITE_TAC [zag] THEN REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    REWRITE_TAC [PAIR_EQ] THEN
    POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist HolLight.CONJ) THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval ZAG_INVOLUTION_GENERAL

#eval phrase 18
def IN_TRIPLE : thm := keep "IN_TRIPLE" fun _ => (do
  prove ([[(a,b,c) IN {(x,y,z) | P x y z} <=> P a b c]])
   (REWRITE_TAC [IN_ELIM_THM, PAIR_EQ] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval IN_TRIPLE

#eval phrase 19
def PRIME_SQUARE : thm := keep "PRIME_SQUARE" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[n = n * 1]])
  prove ([[!n. ~prime(n * n)]])
   (GEN_TAC THEN ASM_CASES_TAC ([[n = 0]]) THEN
    ASM_REWRITE_TAC [PRIME_0, MULT_CLAUSES] THEN
    REWRITE_TAC [prime, NOT_FORALL_THM, DE_MORGAN_THM] THEN
    ASM_CASES_TAC ([[n = 1]]) THEN ASM_REWRITE_TAC [ARITH] THEN
    DISJ2_TAC THEN EXISTS_TAC ([[n:num]]) THEN
    ASM_SIMP_TAC [DIVIDES_LMUL, DIVIDES_REFL] THEN
    GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.LAND_CONV) [h1] THEN
    ASM_SIMP_TAC [EQ_MULT_LCANCEL])
  : ExceptT String IO thm).run
#eval PRIME_SQUARE

#eval phrase 20
def PRIME_4X : thm := keep "PRIME_4X" fun _ => (do
  let h1 ← nrc (← ExceptT.mk [[2 * 2]])
  prove ([[!n. ~prime(4 * n)]])
   (GEN_TAC THEN REWRITE_TAC [prime, NOT_FORALL_THM, DE_MORGAN_THM] THEN
    DISJ2_TAC THEN EXISTS_TAC ([[2]]) THEN
    SUBST1_TAC (← HolLight.SYM h1) THEN
    ASM_SIMP_TAC [(← HolLight.GSYM MULT_ASSOC), DIVIDES_RMUL, DIVIDES_REFL, ARITH_EQ] THEN
    ASM_CASES_TAC ([[n = 0]]) THEN POP_ASSUM MP_TAC THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval PRIME_4X

#eval phrase 21
def PRIME_XYZ_NONZERO : thm := keep "PRIME_XYZ_NONZERO" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[~(0 < x) = (x = 0)]])
  prove ([[prime(x EXP 2 + 4 * y * z) ==> 0 < x /\ 0 < y /\ 0 < z]])
   (CONV_TAC HolLight.CONTRAPOS_CONV THEN
    REWRITE_TAC [DE_MORGAN_THM, h1] THEN
    DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC [EXP_2, MULT_CLAUSES, ADD_CLAUSES, PRIME_SQUARE, PRIME_4X])
  : ExceptT String IO thm).run
#eval PRIME_XYZ_NONZERO

#eval phrase 22
def ZAG_INVOLUTION : thm := keep "ZAG_INVOLUTION" fun _ => (do
  prove ([[!p. prime(p) ==> involution zag (zset(p))]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [involution, FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [([[x:num]]), ([[y:num]]), ([[z:num]])] THEN
    REWRITE_TAC [zset, IN_TRIPLE] THEN DISCH_THEN (SUBST_ALL_TAC o HolLight.SYM) THEN
    CONJ_TAC THENL
     [REWRITE_TAC [zag] THEN REPEAT COND_CASES_TAC THEN
      ASM_REWRITE_TAC [IN_TRIPLE] THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [NOT_LT]) THEN
      ASM_SIMP_TAC [(← HolLight.GSYM INT_OF_NUM_EQ), (← HolLight.GSYM INT_OF_NUM_ADD), EXP_2,
                   (← HolLight.GSYM INT_OF_NUM_MUL), (← HolLight.GSYM INT_OF_NUM_SUB), LT_IMP_LE] THEN
      INT_ARITH_TAC,
      MATCH_MP_TAC ZAG_INVOLUTION_GENERAL THEN
      ASM_MESON_TAC [PRIME_XYZ_NONZERO]])
  : ExceptT String IO thm).run
#eval ZAG_INVOLUTION

#eval phrase 23
def TAG_INVOLUTION : thm := keep "TAG_INVOLUTION" fun _ => (do
  prove ([[!a. involution tag (zset a)]])
   (REWRITE_TAC [involution, tag, zset, FORALL_PAIR_THM] THEN
    REWRITE_TAC [IN_TRIPLE] THEN REWRITE_TAC [MULT_AC])
  : ExceptT String IO thm).run
#eval TAG_INVOLUTION

#eval phrase 24
def ZAG_LEMMA : thm := keep "ZAG_LEMMA" fun _ => (do
  prove ([[(zag(x,y,z) = (x,y,z)) ==> (y = x)]])
   (REWRITE_TAC [zag, INT_POW_2] THEN
    REPEAT (COND_CASES_TAC THEN ASM_SIMP_TAC [PAIR_EQ]) THEN
    POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist HolLight.CONJ) THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval ZAG_LEMMA

#eval phrase 25
def ZSET_BOUND : thm := keep "ZSET_BOUND" fun _ => (do
  let h4 ← ar (← ExceptT.mk [[0 < a ==> 1 <= 4 * a]])
  let h3 ← ar (← ExceptT.mk [[y <= 4 * a * y <=> 1 * y <= (4 * a) * y]])
  let h2 ← ar (← ExceptT.mk [[y <= z ==> y <= x + z]])
  let h1 ← ar (← ExceptT.mk [[(a <= b ==> a <= b + c)]])
  prove ([[0 < y /\ 0 < z /\ (x EXP 2 + 4 * y * z = p)
   ==> x <= p /\ y <= p /\ z <= p]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM (SUBST1_TAC o HolLight.SYM) THEN CONJ_TAC THENL
     [MESON_TAC [EXP_2, LE_SQUARE_REFL, h1],
      CONJ_TAC THEN MATCH_MP_TAC h2 THENL
       [GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.RAND_CONV) [MULT_SYM], ALL_TAC] THEN
      REWRITE_TAC [h3] THEN
      ASM_REWRITE_TAC [LE_MULT_RCANCEL] THEN
      ASM_SIMP_TAC [h4]])
  : ExceptT String IO thm).run
#eval ZSET_BOUND

#eval phrase 26
def ZSET_FINITE : thm := keep "ZSET_FINITE" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[x < p + 1 <=> x <= p]])
  let h1 ← tt (← ExceptT.mk [[a /\ b ==> c <=> b ==> a ==> c]])
  prove ([[!p. prime(p) ==> FINITE(zset p)]])
   (GEN_TAC THEN DISCH_TAC THEN
    MP_TAC (← HolLight.SPEC ([[p + 1]]) FINITE_NUMSEG_LT) THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
        pure (MP_TAC (← funpowR 2 (HolLight.MATCH_MP FINITE_PRODUCT o HolLight.CONJ th) th))) THEN
    MATCH_MP_TAC (← HolLight.REWRITE_RULE [h1] FINITE_SUBSET) THEN
    REWRITE_TAC [zset, SUBSET, FORALL_PAIR_THM, IN_TRIPLE] THEN
    MAP_EVERY X_GEN_TAC [([[x:num]]), ([[y:num]]), ([[z:num]])] THEN
    REWRITE_TAC [IN_ELIM_THM, EXISTS_PAIR_THM, PAIR_EQ] THEN
    REWRITE_TAC [h2, PAIR_EQ] THEN
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [([[x:num]]), ([[y:num]]), ([[z:num]])] THEN
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [RIGHT_AND_EXISTS_THM] THEN
    MAP_EVERY EXISTS_TAC [([[y:num]]), ([[z:num]])] THEN REWRITE_TAC [] THEN
    ASM_MESON_TAC [ZSET_BOUND, PRIME_XYZ_NONZERO])
  : ExceptT String IO thm).run
#eval ZSET_FINITE

#eval phrase 27
def SUM_OF_TWO_SQUARES : thm := keep "SUM_OF_TWO_SQUARES" fun _ => (do
  let h4 ← ar (← ExceptT.mk [[(a = a * b) = (a * b = a * 1)]])
  let h3 ← ar (← ExceptT.mk [[x * x + 4 * x * z = x * (4 * z + x)]])
  let h2 ← ar (← ExceptT.mk [[~(1 + k < 1)]])
  let h1 ← ar (← ExceptT.mk [[4 * x * y = (2 * x) * (2 * y)]])
  prove ([[!p k. prime(p) /\ (p = 4 * k + 1) ==> ?x y. p = x EXP 2 + y EXP 2]])
   (SIMP_TAC [] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[?t. t IN zset(p) /\ (tag(t) = t)]]) MP_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [LEFT_IMP_EXISTS_THM, FORALL_PAIR_THM, tag, PAIR_EQ] THEN
      REWRITE_TAC [zset, IN_TRIPLE, EXP_2] THEN
      ASM_MESON_TAC [h1]] THEN
    MATCH_MP_TAC INVOLUTION_FIX_FIX THEN EXISTS_TAC ([[zag]]) THEN
    ASM_SIMP_TAC [ZAG_INVOLUTION, TAG_INVOLUTION, ZSET_FINITE] THEN
    REWRITE_TAC [EXISTS_UNIQUE_ALT] THEN EXISTS_TAC ([[1,1,k:num]]) THEN
    REWRITE_TAC [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [([[x:num]]), ([[y:num]]), ([[z:num]])] THEN EQ_TAC THENL
     [ALL_TAC,
      DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN
      REWRITE_TAC [zset, zag, IN_TRIPLE, ARITH] THEN
      REWRITE_TAC [MULT_CLAUSES, h2, PAIR_EQ] THEN
      ARITH_TAC] THEN
    REWRITE_TAC [zset, IN_TRIPLE] THEN STRIP_TAC THEN
    FIRST_ASSUM (SUBST_ALL_TAC o HolLight.MATCH_MP ZAG_LEMMA) THEN
    UNDISCH_TAC ([[x EXP 2 + 4 * x * z = 4 * k + 1]]) THEN
    REWRITE_TAC [EXP_2, h3] THEN
    DISCH_THEN (ASSUME_TAC o HolLight.SYM) THEN UNDISCH_TAC ([[prime p]]) THEN
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [prime] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o HolLight.SPEC ([[x:num]]))) THEN
    SIMP_TAC [DIVIDES_RMUL, DIVIDES_REFL] THEN
    DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC MP_TAC) THENL
     [UNDISCH_TAC ([[4 * k + 1 = 1 * (4 * z + 1)]]) THEN
      REWRITE_TAC [MULT_CLAUSES, PAIR_EQ] THEN ARITH_TAC,
      ONCE_REWRITE_TAC [h4] THEN
      ASM_SIMP_TAC [EQ_MULT_LCANCEL] THEN STRIP_TAC THENL
       [UNDISCH_TAC ([[4 * k + 1 = x * (4 * z + x)]]) THEN
        ASM_REWRITE_TAC [MULT_CLAUSES, ADD_EQ_0, ARITH_EQ],
        UNDISCH_TAC ([[4 * z + x = 1]]) THEN REWRITE_TAC [PAIR_EQ] THEN
        ASM_CASES_TAC ([[z = 0]]) THENL
         [ALL_TAC, UNDISCH_TAC ([[~(z = 0)]]) THEN ARITH_TAC] THEN
        UNDISCH_TAC ([[4 * k + 1 = x * (4 * z + x)]]) THEN
        ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES] THEN
        ASM_CASES_TAC ([[x = 1]]) THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [MULT_CLAUSES] THEN ARITH_TAC]])
  : ExceptT String IO thm).run
#eval SUM_OF_TWO_SQUARES

/- ------------------------------------------------------------------------- -/
/- General pigeonhole lemma.                                                 -/
/- ------------------------------------------------------------------------- -/

#eval phrase 28
def PIGEONHOLE_LEMMA : thm := keep "PIGEONHOLE_LEMMA" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[!t. t < 2 * s /\ p <= t ==> ~(p = s + s)]])
  let h1 ← tt (← ExceptT.mk [[(~a ==> c) /\ ~b ==> (a ==> b) ==> c]])
  prove ([[!f:A->B g s t.
        FINITE(s) /\ FINITE(t) /\
        (!x. x IN s ==> f(x) IN t) /\
        (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)) /\
        (!x. x IN s ==> g(x) IN t) /\
        (!x y. x IN s /\ y IN s /\ (g x = g y) ==> (x = y)) /\
        CARD(t) < 2 * CARD(s)
        ==> ?x y. x IN s /\ y IN s /\ (f x = g y)]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[IMAGE (f:A->B) s]]), ([[IMAGE (g:A->B) s]])] CARD_UNION) THEN
    SUBGOAL_THEN ([[(CARD(IMAGE (f:A->B) s) = CARD s) /\
                (CARD(IMAGE (g:A->B) s) = CARD s)]]) STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [CARD_IMAGE_INJ], ALL_TAC] THEN
    ASM_SIMP_TAC [FINITE_IMAGE] THEN
    MATCH_MP_TAC h1 THEN CONJ_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_INSERT, IN_INTER, IN_IMAGE, NOT_IN_EMPTY] THEN
      MESON_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC h2 THEN
    EXISTS_TAC ([[CARD(t:B->bool)]]) THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC [SUBSET, IN_UNION, IN_IMAGE] THEN
    ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval PIGEONHOLE_LEMMA

/- ------------------------------------------------------------------------- -/
/- In particular, consider functions out of 0...(p-1)/2, mod p.              -/
/- ------------------------------------------------------------------------- -/

#eval phrase 29
def PIGEONHOLE_LEMMA_P12 : thm := keep "PIGEONHOLE_LEMMA_P12" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[2 * k + 1 < 2 * (k + 1)]])
  let h1 ← ar (← ExceptT.mk [[2 * x < 2 * k + 1 <=> x < k + 1]])
  prove ([[!f g p.
        ODD(p) /\
        (!x. 2 * x < p ==> f(x) < p) /\
        (!x y. 2 * x < p /\ 2 * y < p /\ (f x = f y) ==> (x = y)) /\
        (!x. 2 * x < p ==> g(x) < p) /\
        (!x y. 2 * x < p /\ 2 * y < p /\ (g x = g y) ==> (x = y))
        ==> ?x y. 2 * x < p /\ 2 * y < p /\ (f x = g y)]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [ODD_EXISTS] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN ([[k:num]]) SUBST1_TAC) THEN
    MP_TAC (← HolLight.ISPECL [([[f:num->num]]), ([[g:num->num]]),
                   ([[{x:num | 2 * x < 2 * k + 1}]]), ([[{x:num | x < 2 * k + 1}]])] PIGEONHOLE_LEMMA) THEN
    REWRITE_TAC [ADD1, h1] THEN
    REWRITE_TAC [FINITE_NUMSEG_LT, CARD_NUMSEG_LT] THEN
    REWRITE_TAC [IN_ELIM_THM, h2])
  : ExceptT String IO thm).run
#eval PIGEONHOLE_LEMMA_P12

/- ------------------------------------------------------------------------- -/
/- Show that \x. x^2 + a (mod p) satisfies the conditions.                   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 30
def SQUAREMOD_INJ_LEMMA : thm := keep "SQUAREMOD_INJ_LEMMA" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[!a:num. (a + b + d = a + c) ==> (b = c - d)]])
  prove ([[!p x d. prime(p) /\ 2 * (x + d) < p /\
           ((x + d) * (x + d) + m * p = x * x + n * p)
           ==> (d = 0)]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[p divides d \/ p divides (2 * x + d)]]) MP_TAC THENL
     [MATCH_MP_TAC PRIME_DIVPROD THEN ASM_REWRITE_TAC [divides] THEN
      EXISTS_TAC ([[n - m:num]]) THEN REWRITE_TAC [LEFT_SUB_DISTRIB] THEN
      MATCH_MP_TAC h1 THEN
      EXISTS_TAC ([[x * x:num]]) THEN ONCE_REWRITE_TAC [MULT_SYM] THEN
      FIRST_ASSUM (SUBST1_TAC o HolLight.SYM) THEN ARITH_TAC,
      DISCH_THEN (DISJ_CASES_THEN (MP_TAC o HolLight.MATCH_MP DIVIDES_LE)) THEN
      SIMP_TAC [ADD_EQ_0] THEN UNDISCH_TAC ([[2 * (x + d) < p]]) THEN ARITH_TAC])
  : ExceptT String IO thm).run
#eval SQUAREMOD_INJ_LEMMA

#eval phrase 31
def SQUAREMOD_INJ : thm := keep "SQUAREMOD_INJ" fun _ => (do
  let h3 ← ar (← ExceptT.mk [[(x + d = x) = (d = 0)]])
  let h2 ← ar (← ExceptT.mk [[(x2 + a = xp + b:num) /\ (y2 + a = yp + b)
    ==> (x2 + yp = y2 + xp)]])
  let h1 ← ar (← ExceptT.mk [[x < a ==> ~(a = 0)]])
  prove ([[!p. prime(p)
   ==> (!x. 2 * x < p ==> (x EXP 2 + a) MOD p < p) /\
       (!x y. 2 * x < p /\ 2 * y < p /\
              ((x EXP 2 + a) MOD p = (y EXP 2 + a) MOD p)
              ==> (x = y))]])
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o HolLight.MATCH_MP h1) THEN
    ASM_SIMP_TAC [DIVISION] THEN
    SUBGOAL_THEN ([[(x EXP 2 + a = (x EXP 2 + a) DIV p * p + (x EXP 2 + a) MOD p) /\
    (y EXP 2 + a = (y EXP 2 + a) DIV p * p + (y EXP 2 + a) MOD p)]]) MP_TAC THENL [ASM_SIMP_TAC [DIVISION], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP h2) THEN
    DISJ_CASES_THEN MP_TAC (← HolLight.SPECL [([[x:num]]), ([[y:num]])] LE_CASES) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[d:num]]) SUBST_ALL_TAC o
      HolLight.REWRITE_RULE [LE_EXISTS]) THENL [ONCE_REWRITE_TAC [EQ_SYM_EQ], ALL_TAC] THEN
    REWRITE_TAC [EXP_2, h3] THEN
    ASM_MESON_TAC [SQUAREMOD_INJ_LEMMA])
  : ExceptT String IO thm).run
#eval SQUAREMOD_INJ

/- ------------------------------------------------------------------------- -/
/- Show that also a reflection mod p retains this property.                  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 32
def REFLECT_INJ : thm := keep "REFLECT_INJ" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[x < p /\ y < p /\ (p - 1 - x = p - 1 - y) ==> (x = y)]])
  let h1 ← ar (← ExceptT.mk [[2 * x < p ==> p - 1 - y < p]])
  prove ([[(!x. 2 * x < p ==> f(x) < p) /\
   (!x y. 2 * x < p /\ 2 * y < p /\ (f x = f y) ==> (x = y))
   ==> (!x. 2 * x < p ==> p - 1 - f(x) < p) /\
       (!x y. 2 * x < p /\ 2 * y < p /\ (p - 1 - f(x) = p - 1 - f(y))
              ==> (x = y))]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC [h1] THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC h2 THEN
    ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval REFLECT_INJ

/- ------------------------------------------------------------------------- -/
/- Hence the main result.                                                    -/
/- ------------------------------------------------------------------------- -/

#eval phrase 33
def LAGRANGE_LEMMA_ODD : thm := keep "LAGRANGE_LEMMA_ODD" fun _ => (do
  let h3 ← ar (← ExceptT.mk [[(x2 + a = xd * p + xm) /\ (y2 = yd * p + ym)
       ==> (x2 + y2 + a + 1 = (xm + ym + 1) + (xd + yd) * p)]])
  let h2 ← ar (← ExceptT.mk [[(x = p - 1 - y) ==> y < p ==> (x + y + 1 = p)]])
  let h1 ← tt (← ExceptT.mk [[(a /\ b) /\ (c /\ d) ==> a /\ b /\ c /\ d]])
  prove ([[!a p. prime(p) /\ ODD(p)
         ==> ?n x y. 2 * x < p /\ 2 * y < p /\
                     (n * p = x EXP 2 + y EXP 2 + a + 1)]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[~(p = 0)]]) ASSUME_TAC THENL [ASM_MESON_TAC [ODD], ALL_TAC] THEN
    MP_TAC (← HolLight.ISPECL [([[\x. (x EXP 2 + a) MOD p]]),
                   ([[\x. p - 1 - (x EXP 2 + 0) MOD p]]), ([[p:num]])] PIGEONHOLE_LEMMA_P12) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC h1 THEN
      CONJ_TAC THENL
       [ALL_TAC, MATCH_MP_TAC REFLECT_INJ] THEN
      ASM_MESON_TAC [SQUAREMOD_INJ], ALL_TAC] THEN
    STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP h2) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [DIVISION], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o HolCore.Lib.C HolLight.AP_THM ([[p:num]]) o HolLight.AP_TERM ([[(MOD)]])) THEN
    SUBGOAL_THEN ([[((x EXP 2 + a) MOD p + (y EXP 2 + 0) MOD p + 1) MOD p =
    (x EXP 2 + y EXP 2 + a + 1) MOD p]]) SUBST1_TAC THENL
     [CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC MOD_EQ THEN
      EXISTS_TAC ([[(x EXP 2 + a) DIV p + (y EXP 2) DIV p]]) THEN
      REWRITE_TAC [ADD_CLAUSES] THEN
      MATCH_MP_TAC h3 THEN
      ASM_MESON_TAC [DIVISION], ALL_TAC] THEN
    SUBGOAL_THEN ([[p MOD p = 0]]) SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC ([[1]]) THEN
      UNDISCH_TAC ([[~(p = 0)]]) THEN ARITH_TAC, ALL_TAC] THEN
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [([[(x EXP 2 + y EXP 2 + a + 1) DIV p]]), ([[x:num]]), ([[y:num]])] THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (MP_TAC o HolLight.SPEC ([[x EXP 2 + y EXP 2 + a + 1]]) o
      HolLight.MATCH_MP DIVISION) THEN
   ASM_REWRITE_TAC [ADD_CLAUSES, MULT_CLAUSES] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval LAGRANGE_LEMMA_ODD

/- ------------------------------------------------------------------------- -/
/- Avoid the additional conditions.                                          -/
/- ------------------------------------------------------------------------- -/

#eval phrase 34
def LAGRANGE_LEMMA : thm := keep "LAGRANGE_LEMMA" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[~(a = 0) ==> (a = (a - 1) + 1)]])
  prove ([[!a p. prime(p)
         ==> ?n x y. 2 * x <= p /\ 2 * y <= p /\
                     (n * p = x EXP 2 + y EXP 2 + a)]])
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC ([[EVEN(p)]]) THENL
     [FIRST_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [prime]) THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC ([[2]]) o HolLight.CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_MESON_TAC [EVEN_EXISTS, divides], ALL_TAC] THEN
      REWRITE_TAC [ARITH_EQ] THEN DISCH_THEN (SUBST_ALL_TAC o HolLight.SYM) THEN
      ASM_CASES_TAC ([[EVEN(a)]]) THENL
       [UNDISCH_TAC ([[EVEN a]]) THEN REWRITE_TAC [EVEN_EXISTS] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[k:num]]) SUBST_ALL_TAC) THEN
        MAP_EVERY EXISTS_TAC [([[k:num]]), ([[0]]), ([[0]])] THEN
        REWRITE_TAC [ARITH, ADD_CLAUSES] THEN ARITH_TAC,
        UNDISCH_TAC ([[~(EVEN(a))]]) THEN REWRITE_TAC [NOT_EVEN, ODD_EXISTS] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[k:num]]) SUBST_ALL_TAC) THEN
        MAP_EVERY EXISTS_TAC [([[k + 1]]), ([[1]]), ([[0]])] THEN
        REWRITE_TAC [ARITH, ADD_CLAUSES] THEN ARITH_TAC],
      ASM_CASES_TAC ([[a = 0]]) THENL
       [MAP_EVERY EXISTS_TAC [([[0]]), ([[0]]), ([[0]])] THEN
        ASM_REWRITE_TAC [LE_0, ADD_CLAUSES, MULT_CLAUSES, EXP_2], ALL_TAC] THEN
      FIRST_ASSUM (SUBST1_TAC o HolLight.MATCH_MP h1) THEN
      MP_TAC (← HolLight.SPECL [([[a - 1]]), ([[p:num]])] LAGRANGE_LEMMA_ODD) THEN
      ASM_REWRITE_TAC [(← HolLight.GSYM NOT_EVEN)] THEN MESON_TAC [LT_IMP_LE]])
  : ExceptT String IO thm).run
#eval LAGRANGE_LEMMA

/- ------------------------------------------------------------------------- -/
/- Aubrey's lemma showing that rationals suffice for sums of 4 squares.      -/
/- ------------------------------------------------------------------------- -/

#eval phrase 35
#eval Session.prioritize_real

#eval phrase 36
def REAL_INTEGER_CLOSURES : thm := keep "REAL_INTEGER_CLOSURES" fun _ => (do
  let h4 ← rr (← ExceptT.mk [[(a + --b = c) <=> (b + c = a)]])
  let h3 ← rr (← ExceptT.mk [[(--a + b = c) <=> (a + c = b)]])
  let h2 ← rr (← ExceptT.mk [[&0 <= a ==> ((abs(x) = a) <=> (x = a) \/ (x = --a))]])
  let h1 ← tt (← ExceptT.mk [[x /\ c /\ d /\ e /\ f /\ (a /\ e ==> b) /\ a
    ==> x /\ a /\ b /\ c /\ d /\ e /\ f]])
  prove ([[(!n. ?p. abs(&n) = &p) /\
   (!x y. (?m. abs(x) = &m) /\ (?n. abs(y) = &n) ==> ?p. abs(x + y) = &p) /\
   (!x y. (?m. abs(x) = &m) /\ (?n. abs(y) = &n) ==> ?p. abs(x - y) = &p) /\
   (!x y. (?m. abs(x) = &m) /\ (?n. abs(y) = &n) ==> ?p. abs(x * y) = &p) /\
   (!x r. (?n. abs(x) = &n) ==> ?p. abs(x pow r) = &p) /\
   (!x. (?n. abs(x) = &n) ==> ?p. abs(--x) = &p) /\
   (!x. (?n. abs(x) = &n) ==> ?p. abs(abs x) = &p)]])
   (MATCH_MP_TAC h1 THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC [REAL_ABS_NUM] THEN MESON_TAC [],
      REWRITE_TAC [REAL_ABS_MUL] THEN MESON_TAC [REAL_OF_NUM_MUL],
      REWRITE_TAC [REAL_ABS_POW] THEN MESON_TAC [REAL_OF_NUM_POW],
      REWRITE_TAC [REAL_ABS_NEG], REWRITE_TAC [REAL_ABS_ABS],
      REWRITE_TAC [real_sub] THEN MESON_TAC [], ALL_TAC] THEN
    SIMP_TAC [h2,
             SessionLibrary.Analysis.REAL_POS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [(← HolLight.GSYM SessionLibrary.Analysis.REAL_NEG_ADD), REAL_OF_NUM_ADD] THENL
     [MESON_TAC [], ALL_TAC, ALL_TAC, MESON_TAC []] THEN
    REWRITE_TAC [h3,
                h4] THEN
    REWRITE_TAC [REAL_OF_NUM_ADD, REAL_OF_NUM_EQ] THEN
    MESON_TAC [LE_EXISTS, ADD_SYM, LE_CASES])
  : ExceptT String IO thm).run
#eval REAL_INTEGER_CLOSURES

#eval phrase 37
def REAL_NUM_ROUND : thm := keep "REAL_NUM_ROUND" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[a <= x /\ x < a + &1
     ==> abs(x - a) * &2 <= &1 \/ abs(x - (a + &1)) * &2 <= &1]])
  prove ([[!x. &0 <= x ==> ?n. abs(x - &n) <= &1 / &2]])
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP (← HolLight.MATCH_MP REAL_ARCH_LEAST SessionLibrary.Analysis.REAL_LT_01)) THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_SUC), SessionLibrary.Analysis.REAL_MUL_RID] THEN
    DISCH_THEN (CHOOSE_THEN MP_TAC) THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP h1) THEN
    SIMP_TAC [REAL_LE_RDIV_EQ, REAL_OF_NUM_LT, ARITH] THEN
    MESON_TAC [REAL_OF_NUM_ADD])
  : ExceptT String IO thm).run
#eval REAL_NUM_ROUND

#eval phrase 38
def REAL_POS_ABS_MIDDLE : thm := keep "REAL_POS_ABS_MIDDLE" fun _ => (do
  let h3 ← rr (← ExceptT.mk [[n - &1 + a = n - (&1 - a)]])
  let h2 ← rrc (← ExceptT.mk [[&0 <= &1 / &2]])
  let h1 ← ar (← ExceptT.mk [[(n = 0) \/ 1 <= n]])
  prove ([[!x n. &0 <= x /\ (abs(x - &n) = &1 / &2)
         ==> (x = &(n - 1) + &1 / &2) \/ (x = &n + &1 / &2)]])
   (REPEAT GEN_TAC THEN
    MP_TAC (← HolLight.SPECL [([[1]]), ([[n:num]])] REAL_OF_NUM_SUB) THEN
    DISJ_CASES_TAC h1 THEN
    ASM_REWRITE_TAC [ARITH] THENL
     [MP_TAC h2 THEN REAL_ARITH_TAC2,
      DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN
      REWRITE_TAC [h3] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC2])
  : ExceptT String IO thm).run
#eval REAL_POS_ABS_MIDDLE

#eval phrase 39
def REAL_RAT_ABS_MIDDLE : thm := keep "REAL_RAT_ABS_MIDDLE" fun _ => (do
  prove ([[!m n p. (abs(&m / &p - &n) = &1 / &2)
         ==> (&m / &p = &(n - 1) + &1 / &2) \/ (&m / &p = &n + &1 / &2)]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POS_ABS_MIDDLE THEN
    ASM_SIMP_TAC [REAL_LE_DIV, SessionLibrary.Analysis.REAL_POS])
  : ExceptT String IO thm).run
#eval REAL_RAT_ABS_MIDDLE

#eval phrase 40
def AUBREY_LEMMA_4 : thm := keep "AUBREY_LEMMA_4" fun _ => (do
  let h25 ← rr (← ExceptT.mk [[(&2 * x + &1) - (&2 * y + &1) = &2 * (x - y)]])
  let h24 ← tt (← ExceptT.mk [[EVEN(N) \/ ~EVEN(N)]])
  let h23 ← rr (← ExceptT.mk [[(a + b + c + d = e) <=> (a + b + c + d - e = &0)]])
  let h22 ← rr (← ExceptT.mk [[a * z * b - c * z = (a * b - c) * z]])
  let h21 ← rr (← ExceptT.mk [[(a + n' - n = b - (n - n')) <=> (a = b)]])
  let h20 ← rr (← ExceptT.mk [[(m * z - &1) * (m' * z + nn) = m * m' * z * z +
                                        (m * z * nn - m' * z) - nn]])
  let h19 ← rr (← ExceptT.mk [[(a = c) /\ (b = d) ==> (a + b + n - m = c + d + n - m)]])
  let h18 ← rr (← ExceptT.mk [[(n + s * z) * (n + s * z) + (p + t * z) * (p + t * z) +
        (q + u * z) * (q + u * z) + (r + v * z) * (r + v * z) - N =
        (s * s + t * t + u * u + v * v) * (z * z) +
        (&2 * (n * s + p * t + q * u + r * v)) * z +
        ((n * n + p * p + q * q + r * r) - N)]])
  let h17 ← rr (← ExceptT.mk [[b < a ==> ~(a - b = &0)]])
  let h16 ← ar (← ExceptT.mk [[0 < a <=> ~(a = 0)]])
  let h15 ← rr (← ExceptT.mk [[((a - &1) * m = M) <=> (a * m - M = m)]])
  let h14 ← rr (← ExceptT.mk [[(a - &1) * m < M <=> a * m - M < m]])
  let h13 ← ar (← ExceptT.mk [[0 < n <=> ~(n = 0)]])
  let h12 ← rr (← ExceptT.mk [[&0 < a - b <=> b < a]])
  let h11 ← rr (← ExceptT.mk [[((a + b) - c = &1) <=> ((a + b) - &1 = c)]])
  let h10 ← rr (← ExceptT.mk [[(a + b) - c < &1 <=> (a + b) - &1 < c]])
  let h9 ← rr (← ExceptT.mk [[&0 <= w /\ &0 <= x /\ &0 <= y /\ &0 <= z /\
      ~((w = &0) /\ (x = &0) /\ (y = &0) /\ (z = &0))
      ==> &0 < w + x + y + z]])
  let h8 ← tt (← ExceptT.mk [[~b ==> ~a <=> a ==> b]])
  let h7 ← rr (← ExceptT.mk [[&0 <= x /\ &0 < y ==> ~(x + y = &0)]])
  let h6 ← rr (← ExceptT.mk [[(a * a = b * b) <=> ((a + b) * (a - b) = &0)]])
  let h5 ← rr (← ExceptT.mk [[!m. a <= m /\ b <= m /\ c <= m /\ d <= m /\
          ~((a = m) /\ (b = m) /\ (c = m) /\ (d = m)) /\
          &4 * m <= &1
          ==> a + b + c + d < &1]])
  let h4 ← rr (← ExceptT.mk [[(a + b) - (a + c) = b - c]])
  let h3 ← rr (← ExceptT.mk [[(a + b) - a = b]])
  let h2 ← rr (← ExceptT.mk [[(a + b) - a = b]])
  let h1 ← tt (← ExceptT.mk [[(~p ==> p) ==> p]])
  prove ([[!m n p q r.
        ~(m = 0) /\ ~(m = 1) /\
        ((&n / &m) pow 2 + (&p / &m) pow 2 +
         (&q / &m) pow 2 + (&r / &m) pow 2 = &N)
        ==> ?m' n' p' q' r'.
               ~(m' = 0) /\ m' < m /\
               ((&n' / &m') pow 2 + (&p' / &m') pow 2 +
                (&q' / &m') pow 2 + (&r' / &m') pow 2 = &N)]])
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC h1 THEN
    REWRITE_TAC [NOT_EXISTS_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[?n' p' q' r'.
        (&n / &m - &n') pow 2 + (&p / &m - &p') pow 2 +
        (&q / &m - &q') pow 2 + (&r / &m - &r') pow 2 < &1 \/
        (((&n / &m - &n') pow 2 + (&p / &m - &p') pow 2 +
          (&q / &m - &q') pow 2 + (&r / &m - &r') pow 2 = &1) /\
         (m = 2) /\ (EVEN(n' + p' + q' + r') = EVEN(N)))]]) MP_TAC THENL
     [ASM_CASES_TAC ([[?n' p' q' r'. (&n / &m = &n' + &1 / &2) /\
                    (&p / &m = &p' + &1 / &2) /\
                    (&q / &m = &q' + &1 / &2) /\
                    (&r / &m = &r' + &1 / &2)]]) THENL
       [FIRST_X_ASSUM (CHOOSE_THEN STRIP_ASSUME_TAC) THEN
        MAP_EVERY EXISTS_TAC [([[n':num]]), ([[p':num]]), ([[q':num]])] THEN
        SUBGOAL_THEN ([[m = 2]]) SUBST_ALL_TAC THENL
         [FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [([[2]]), ([[2 * n' + 1]]), ([[2 * p' + 1]]), ([[2 * q' + 1]]), ([[2 * r' + 1]])]) THEN
          REWRITE_TAC [ARITH_EQ, (← HolLight.GSYM REAL_OF_NUM_ADD), (← HolLight.GSYM REAL_OF_NUM_MUL)] THEN
          REWRITE_TAC [real_div, REAL_ADD_RDISTRIB, (← HolLight.GSYM REAL_MUL_ASSOC)] THEN
          REWRITE_TAC [(← HolLight.GSYM real_div)] THEN
          SIMP_TAC [REAL_DIV_LMUL, REAL_OF_NUM_EQ, ARITH_EQ] THEN
          REPEAT (FIRST_X_ASSUM (SUBST1_TAC o HolLight.SYM)) THEN
          REWRITE_TAC [] THEN POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist HolLight.CONJ) THEN
          ARITH_TAC, ALL_TAC] THEN
        SUBGOAL_THEN ([[(EVEN(n' + p' + q' + r') <=> EVEN(N)) \/
                    (EVEN(n' + p' + q' + r' + 1) <=> EVEN(N))]]) DISJ_CASES_TAC THENL
         [REWRITE_TAC [EVEN_ADD, ARITH_EVEN] THEN CONV_TAC TAUT,
          EXISTS_TAC ([[r':num]]) THEN DISJ2_TAC THEN ASM_REWRITE_TAC [] THEN
          REWRITE_TAC [h2] THEN
          CONV_TAC REAL_RAT_REDUCE_CONV,
          EXISTS_TAC ([[r' + 1]]) THEN DISJ2_TAC THEN ASM_REWRITE_TAC [] THEN
          REWRITE_TAC [h3] THEN
          REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_ADD)] THEN
          REWRITE_TAC [h4] THEN
          CONV_TAC REAL_RAT_REDUCE_CONV],
        ALL_TAC] THEN
      MAP_EVERY (fun t => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPEC t REAL_NUM_ROUND))) [([[&n / &m]]), ([[&p / &m]]), ([[&q / &m]]), ([[&r / &m]])] THEN
      SIMP_TAC [REAL_LE_DIV, SessionLibrary.Analysis.REAL_POS] THEN
      MAP_EVERY (fun t => DISCH_THEN (X_CHOOSE_TAC t)) [([[r':num]]), ([[q':num]]), ([[p':num]]), ([[n':num]])] THEN
      MAP_EVERY EXISTS_TAC [([[n':num]]), ([[p':num]]), ([[q':num]]), ([[r':num]])] THEN
      DISJ1_TAC THEN
      MATCH_MP_TAC h5 THEN
      EXISTS_TAC ([[(&1 / &2) pow 2]]) THEN
      ONCE_REWRITE_TAC [(← HolLight.SYM (← HolLight.SPEC ([[a - b]]) REAL_POW2_ABS))] THEN
      ASM_SIMP_TAC [REAL_POW_LE2, REAL_ABS_POS, REAL_LE_DIV, SessionLibrary.Analysis.REAL_POS] THEN
      CONV_TAC (HolLight.RAND_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC [] THEN
      REWRITE_TAC [REAL_POW_2, h6] THEN
      REWRITE_TAC [REAL_ENTIRE] THEN
      SIMP_TAC [h7,
               REAL_ABS_POS, REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
      REWRITE_TAC [SessionLibrary.Analysis.REAL_SUB_0] THEN
      FIRST_ASSUM (MP_TAC o check (HolCore.Basics.is_neg o concl)) THEN
      REWRITE_TAC [h8] THEN
      DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN (MP_TAC o HolLight.MATCH_MP REAL_RAT_ABS_MIDDLE)) THEN MESON_TAC [],
      ALL_TAC] THEN
    FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o check (HolCore.Basics.is_forall o concl)) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [([[n':num]]), ([[p':num]]), ([[q':num]]), ([[r':num]])] THEN
    DISCH_TAC THEN
    ABBREV_TAC ([[s = &n - &m * &n']]) THEN
    ABBREV_TAC ([[t = &p - &m * &p']]) THEN
    ABBREV_TAC ([[u = &q - &m * &q']]) THEN
    ABBREV_TAC ([[v = &r - &m * &r']]) THEN
    ABBREV_TAC ([[N' = n' EXP 2 + p' EXP 2 + q' EXP 2 + r' EXP 2]]) THEN
    UNDISCH_TAC ([[n' EXP 2 + p' EXP 2 + q' EXP 2 + r' EXP 2 = N']]) THEN
    DISCH_THEN (ASSUME_TAC o HolLight.REWRITE_RULE [(← HolLight.GSYM REAL_OF_NUM_EQ), (← HolLight.GSYM REAL_OF_NUM_ADD), (← HolLight.GSYM REAL_OF_NUM_POW)]) THEN
    ABBREV_TAC ([[M = 2 * (n * n' + p * p' + q * q' + r * r')]]) THEN
    UNDISCH_TAC ([[2 * (n * n' + p * p' + q * q' + r * r') = M]]) THEN
    DISCH_THEN (ASSUME_TAC o HolLight.REWRITE_RULE [(← HolLight.GSYM REAL_OF_NUM_EQ), (← HolLight.GSYM REAL_OF_NUM_ADD), (← HolLight.GSYM REAL_OF_NUM_MUL),
      (← HolLight.GSYM REAL_OF_NUM_POW)]) THEN
    ASM_CASES_TAC ([[(&n / &m = &n') /\ (&p / &m = &p') /\
                 (&q / &m = &q') /\ (&r / &m = &r')]]) THENL
     [MAP_EVERY EXISTS_TAC [([[1]]), ([[n':num]]), ([[p':num]]), ([[q':num]]), ([[r':num]])] THEN
      REWRITE_TAC [ARITH_EQ, REAL_DIV_1] THEN CONJ_TAC THENL
       [UNDISCH_TAC ([[~(m = 0)]]) THEN UNDISCH_TAC ([[~(m = 1)]]) THEN ARITH_TAC,
        UNDISCH_THEN ([[(&n / &m) pow 2 + (&p / &m) pow 2 +
         (&q / &m) pow 2 + (&r / &m) pow 2 = &N]]) (SUBST1_TAC o HolLight.SYM) THEN
        ASM_REWRITE_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[&0 < (&n / &m - &n') pow 2 + (&p / &m - &p') pow 2 +
                     (&q / &m - &q') pow 2 + (&r / &m - &r') pow 2]]) MP_TAC THENL
     [MATCH_MP_TAC h9 THEN
      REWRITE_TAC [REAL_POW_2, REAL_ENTIRE, SessionLibrary.Analysis.REAL_LE_SQUARE] THEN
      ASM_REWRITE_TAC [SessionLibrary.Analysis.REAL_SUB_0],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o check (HolCore.Basics.is_disj o concl)) THEN
    SUBGOAL_THEN ([[(&n / &m - &n') pow 2 + (&p / &m - &p') pow 2 +
    (&q / &m - &q') pow 2 + (&r / &m - &r') pow 2 =
    (s pow 2 + t pow 2 + u pow 2 + v pow 2) / &m pow 2]]) MP_TAC THENL
     [MATCH_MP_TAC REAL_EQ_RCANCEL_IMP THEN EXISTS_TAC ([[&m pow 2]]) THEN
      ASM_SIMP_TAC [REAL_POW_EQ_0, REAL_DIV_RMUL, REAL_OF_NUM_EQ] THEN
      REWRITE_TAC [REAL_ADD_RDISTRIB, (← HolLight.GSYM REAL_POW_MUL), SessionLibrary.Analysis.REAL_SUB_RDISTRIB] THEN
      ASM_SIMP_TAC [REAL_POW_EQ_0, REAL_DIV_RMUL, REAL_OF_NUM_EQ] THEN
      ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN ([[(&n / &m - &n') pow 2 + (&p / &m - &p') pow 2 +
                (&q / &m - &q') pow 2 + (&r / &m - &r') pow 2 =
                (&N + &N') - &M / &m]]) ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_EQ_RCANCEL_IMP THEN EXISTS_TAC ([[&m pow 2]]) THEN
      ASM_SIMP_TAC [REAL_POW_EQ_0, REAL_DIV_RMUL, REAL_OF_NUM_EQ] THEN
      REWRITE_TAC [(← HolLight.GSYM (← HolLight.ASSUME ([[(&n / &m) pow 2 + (&p / &m) pow 2 +
                             (&q / &m) pow 2 + (&r / &m) pow 2 = &N]]))),
             (← HolLight.GSYM (← HolLight.ASSUME ([[&n' pow 2 + &p' pow 2 + &q' pow 2 + &r' pow 2 = &N']]))),
             (← HolLight.GSYM (← HolLight.ASSUME ([[&2 * (&n * &n' + &p * &p' + &q * &q' + &r * &r') = &M]])))] THEN
      REWRITE_TAC [REAL_ADD_RDISTRIB, (← HolLight.GSYM REAL_POW_MUL), SessionLibrary.Analysis.REAL_SUB_RDISTRIB] THEN
      REWRITE_TAC [REAL_POW_2, REAL_MUL_ASSOC] THEN
      SIMP_TAC [REAL_DIV_RMUL, REAL_OF_NUM_EQ, (← HolLight.ASSUME ([[~(m = 0)]]))] THEN
      REWRITE_TAC [(← HolLight.GSYM REAL_MUL_ASSOC)] THEN
      SIMP_TAC [REAL_DIV_RMUL, REAL_OF_NUM_EQ, (← HolLight.ASSUME ([[~(m = 0)]]))] THEN
      REAL_ARITH_TAC2, ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [h10,
                h11,
                h12] THEN
    SIMP_TAC [REAL_LT_LDIV_EQ, REAL_LT_RDIV_EQ, REAL_EQ_RDIV_EQ, REAL_OF_NUM_LT,
             h13, (← HolLight.ASSUME ([[~(m = 0)]]))] THEN
    REWRITE_TAC [h14,
                h15] THEN
    REPEAT DISCH_TAC THEN
    UNDISCH_TAC ([[(&N + &N') - &M / &m =
               (s pow 2 + t pow 2 + u pow 2 + v pow 2) / &m pow 2]]) THEN
    ASM_SIMP_TAC [REAL_EQ_RDIV_EQ, REAL_POW_LT, REAL_OF_NUM_LT,
                 h16] THEN
    REWRITE_TAC [REAL_POW_2, SessionLibrary.Analysis.REAL_SUB_RDISTRIB, REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC [REAL_DIV_RMUL, REAL_OF_NUM_EQ, (← HolLight.GSYM REAL_POW_2)] THEN
    ABBREV_TAC ([[m':num = (N + N') * m - M]]) THEN
    SUBGOAL_THEN ([[(&N + &N') * &m - &M = &m']]) (fun th => SUBST_ALL_TAC th THEN ASSUME_TAC th) THENL
     [SessionLibrary.Analysis.EXPAND_TAC "m'" THEN
      REWRITE_TAC [REAL_OF_NUM_ADD, REAL_OF_NUM_MUL] THEN
      MATCH_MP_TAC REAL_OF_NUM_SUB THEN
      REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_LE), (← HolLight.GSYM REAL_OF_NUM_ADD), (← HolLight.GSYM REAL_OF_NUM_MUL)] THEN
      ASM_SIMP_TAC [SessionLibrary.Analysis.REAL_LT_IMP_LE], ALL_TAC] THEN
    ASM_REWRITE_TAC [(← HolLight.GSYM SessionLibrary.Analysis.REAL_SUB_RDISTRIB)] THEN
    DISCH_THEN (ASSUME_TAC o HolLight.GSYM) THEN
    SUBGOAL_THEN ([[~(m' = 0)]]) ASSUME_TAC THENL
     [REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_EQ)] THEN
      REWRITE_TAC [(← HolLight.GSYM (← HolLight.ASSUME ([[(&N + &N') * &m - &M = &m']])))] THEN
      MATCH_MP_TAC h17 THEN
      ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN ([[!z. (&n' + s * z) pow 2 + (&p' + t * z) pow 2 +
        (&q' + u * z) pow 2 + (&r' + v * z) pow 2 - &N =
        (&m * z - &1) * (&m' * z + &N - &N')]]) ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC ([[&m * &m' * z pow 2 + (&M - &2 * &m * &N') * z + &N' - &N]]) THEN
      CONJ_TAC THENL
       [REWRITE_TAC [REAL_POW_2, h18] THEN
        ASM_REWRITE_TAC [(← HolLight.GSYM REAL_POW_2)] THEN
        MATCH_MP_TAC h19 THEN
        CONJ_TAC THENL [REWRITE_TAC [REAL_MUL_AC], ALL_TAC] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC [(← HolLight.GSYM (← HolLight.ASSUME ([[&n' pow 2 + &p' pow 2 + &q' pow 2 + &r' pow 2 = &N']]))),
                    (← HolLight.GSYM (← HolLight.ASSUME ([[&2 * (&n * &n' + &p * &p' + &q * &q' + &r * &r') = &M]])))] THEN
        MAP_EVERY SessionLibrary.Analysis.EXPAND_TAC ["s", "t", "u", "v"] THEN
        REWRITE_TAC [REAL_POW_2] THEN REAL_ARITH_TAC2,
        REWRITE_TAC [REAL_POW_2, h20] THEN
        REWRITE_TAC [REAL_EQ_ADD_LCANCEL] THEN
        REWRITE_TAC [h21] THEN
        REWRITE_TAC [h22] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC [(← HolLight.GSYM (← HolLight.ASSUME ([[(&N + &N') * &m - &M = &m']])))] THEN
        REAL_ARITH_TAC2],
      ALL_TAC] THEN
    ABBREV_TAC ([[w = &n' + s * (&N' - &N) / &m']]) THEN
    ABBREV_TAC ([[x = &p' + t * (&N' - &N) / &m']]) THEN
    ABBREV_TAC ([[y = &q' + u * (&N' - &N) / &m']]) THEN
    ABBREV_TAC ([[z = &r' + v * (&N' - &N) / &m']]) THEN
    SUBGOAL_THEN ([[w pow 2 + x pow 2 + y pow 2 + z pow 2 = &N]]) (SUBST1_TAC o HolLight.SYM) THENL
     [MAP_EVERY SessionLibrary.Analysis.EXPAND_TAC ["w", "x", "y", "z"] THEN
      ONCE_REWRITE_TAC [h23] THEN
      FIRST_ASSUM (SUBST1_TAC o HolLight.SPEC ([[(&N' - &N) / &m']])) THEN
      REWRITE_TAC [REAL_ENTIRE] THEN DISJ2_TAC THEN
      ASM_SIMP_TAC [REAL_DIV_LMUL, REAL_OF_NUM_EQ] THEN REAL_ARITH_TAC2,
      ALL_TAC] THEN
    FIRST_X_ASSUM (DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
     [EXISTS_TAC ([[m':num]]) THEN
      SUBGOAL_THEN ([[?a b c d. (abs(&n' * &m' + s * (&N' - &N)) = &a) /\
                (abs(&p' * &m' + t * (&N' - &N)) = &b) /\
                (abs(&q' * &m' + u * (&N' - &N)) = &c) /\
                (abs(&r' * &m' + v * (&N' - &N)) = &d)]]) MP_TAC THENL
       [MAP_EVERY SessionLibrary.Analysis.EXPAND_TAC ["s", "t", "u", "v"] THEN
        REWRITE_TAC [RIGHT_EXISTS_AND_THM, LEFT_EXISTS_AND_THM] THEN
        MESON_TAC [REAL_INTEGER_CLOSURES], ALL_TAC] THEN
      MAP_EVERY (fun t => MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC t) [([[a:num]]), ([[b:num]]), ([[c:num]]), ([[d:num]])] THEN
      DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN (SUBST1_TAC o HolLight.SYM)) THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [REAL_OF_NUM_LT]) THEN
      REWRITE_TAC [REAL_POW_DIV, REAL_POW2_ABS] THEN
      REWRITE_TAC [(← HolLight.GSYM REAL_POW_DIV)] THEN
      REWRITE_TAC [real_div, REAL_ADD_RDISTRIB, (← HolLight.GSYM REAL_MUL_ASSOC)] THEN
      ASM_SIMP_TAC [SessionLibrary.Analysis.REAL_MUL_RINV, REAL_OF_NUM_EQ] THEN
      REWRITE_TAC [(← HolLight.GSYM real_div), SessionLibrary.Analysis.REAL_MUL_RID] THEN
      ASM_REWRITE_TAC [], ALL_TAC] THEN
    REWRITE_TAC [REAL_OF_NUM_EQ] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC)) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN ([[?n. abs((&N' - &N) / &2) = &n]]) ASSUME_TAC THENL
     [REWRITE_TAC [(← HolLight.GSYM (← HolLight.ASSUME ([[&n' pow 2 + &p' pow 2 + &q' pow 2 + &r' pow 2 = &N']])))] THEN
      REWRITE_TAC [REAL_OF_NUM_POW, REAL_OF_NUM_ADD] THEN
      SUBGOAL_THEN ([[EVEN(n' EXP 2 + p' EXP 2 + q' EXP 2 + r' EXP 2) =
                  EVEN N]]) MP_TAC THENL
       [FIRST_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.SYM th)])) THEN
        REWRITE_TAC [EVEN_ADD, EVEN_EXP, ARITH_EQ],
        ALL_TAC] THEN
      DISJ_CASES_THEN MP_TAC h24 THEN SIMP_TAC [] THEN
      REWRITE_TAC [NOT_EVEN, EVEN_EXISTS, ODD_EXISTS] THEN
      REPEAT (DISCH_THEN (CHOOSE_THEN SUBST1_TAC)) THEN
      REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_SUC), (← HolLight.GSYM REAL_OF_NUM_MUL)] THEN
      REWRITE_TAC [h25] THEN
      REWRITE_TAC [(← HolLight.GSYM SessionLibrary.Analysis.REAL_SUB_LDISTRIB)] THEN
      ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
      REWRITE_TAC [real_div, (← HolLight.GSYM REAL_MUL_ASSOC)] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC [SessionLibrary.Analysis.REAL_MUL_RID] THEN MESON_TAC [REAL_INTEGER_CLOSURES],
      ALL_TAC] THEN
    EXISTS_TAC ([[1]]) THEN REWRITE_TAC [ARITH_EQ] THEN
    SUBGOAL_THEN ([[?a b c d. (abs(&n' + s * (&N' - &N) / &2) = &a) /\
               (abs(&p' + t * (&N' - &N) / &2) = &b) /\
               (abs(&q' + u * (&N' - &N) / &2) = &c) /\
               (abs(&r' + v * (&N' - &N) / &2) = &d)]]) MP_TAC THENL
     [MAP_EVERY SessionLibrary.Analysis.EXPAND_TAC ["s", "t", "u", "v"] THEN
      REWRITE_TAC [RIGHT_EXISTS_AND_THM, LEFT_EXISTS_AND_THM] THEN
      UNDISCH_TAC ([[?n. abs ((&N' - &N) / &2) = &n]]) THEN
      MESON_TAC [REAL_INTEGER_CLOSURES], ALL_TAC] THEN
    REWRITE_TAC [ARITH, REAL_DIV_1] THEN
    MAP_EVERY (fun t => MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC t) [([[a:num]]), ([[b:num]]), ([[c:num]]), ([[d:num]])] THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN (SUBST1_TAC o HolLight.SYM)) THEN
    ASM_REWRITE_TAC [REAL_POW2_ABS])
  : ExceptT String IO thm).run
#eval AUBREY_LEMMA_4

/- ------------------------------------------------------------------------- -/
/- Hence the main result.                                                    -/
/- ------------------------------------------------------------------------- -/

#eval phrase 41
def AUBREY_THM_4 : thm := keep "AUBREY_THM_4" fun _ => (do
  prove ([[(?q. ~(q = 0) /\
       ?a b c d.
            (&a / &q) pow 2 + (&b / &q) pow 2 +
            (&c / &q) pow 2 + (&d / &q) pow 2 = &N)
   ==> ?a b c d. &a pow 2 + &b pow 2 + &c pow 2 + &d pow 2 = &N]])
   (GEN_REWRITE_TAC HolLight.LAND_CONV [num_WOP] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[m:num]]) MP_TAC) THEN
    ASM_CASES_TAC ([[m = 1]]) THENL
     [ASM_REWRITE_TAC [REAL_DIV_1, ARITH_EQ] THEN MESON_TAC [],
      STRIP_TAC THEN MP_TAC (← HolLight.SPEC ([[m:num]]) AUBREY_LEMMA_4) THEN
      ASM_REWRITE_TAC [] THEN ASM_MESON_TAC []])
  : ExceptT String IO thm).run
#eval AUBREY_THM_4

/- ------------------------------------------------------------------------- -/
/- The algebraic lemma.                                                      -/
/- ------------------------------------------------------------------------- -/

#eval phrase 42
def LAGRANGE_IDENTITY : thm := keep "LAGRANGE_IDENTITY" fun _ => (do
  rr (← ExceptT.mk [[(w1 pow 2 + x1 pow 2 + y1 pow 2 + z1 pow 2) *
   (w2 pow 2 + x2 pow 2 + y2 pow 2 + z2 pow 2) =
   (w1 * w2 - x1 * x2 - y1 * y2 - z1 * z2) pow 2 +
   (w1 * x2 + x1 * w2 + y1 * z2 - z1 * y2) pow 2 +
   (w1 * y2 - x1 * z2 + y1 * w2 + z1 * x2) pow 2 +
   (w1 * z2 + x1 * y2 - y1 * x2 + z1 * w2) pow 2]])
  : ExceptT String IO thm).run
#eval LAGRANGE_IDENTITY

/- ------------------------------------------------------------------------- -/
/- Now sum of 4 squares.                                                     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 43
def LAGRANGE_REAL_NUM : thm := keep "LAGRANGE_REAL_NUM" fun _ => (do
  let lemma ← prove ([[(?a. abs(w) = &a) /\ (?b. abs(x) = &b) /\
     (?c. abs(y) = &c) /\ (?d. abs(z) = &d)
     ==> ?a b c d. w pow 2 + x pow 2 + y pow 2 + z pow 2 =
                   &a pow 2 + &b pow 2 + &c pow 2 + &d pow 2]])
     (STRIP_TAC THEN ONCE_REWRITE_TAC [(← HolLight.GSYM REAL_POW2_ABS)] THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [REAL_ABS_NUM] THEN
      MESON_TAC [])
  let h4 ← ar (← ExceptT.mk [[(2 * x) * (2 * x) <= p * p /\ (2 * y) * (2 * y) <= p * p /\
      2 * 2 <= p * p
      ==> x * x + y * y + 1 < p * p]])
  let h3 ← ar (← ExceptT.mk [[1 < x <=> ~(x = 0) /\ ~(x = 1)]])
  let h2 ← ar (← ExceptT.mk [[p < p * m <=> p * 1 < p * m]])
  let h1 ← ar (← ExceptT.mk [[m < p * m <=> 1 * m < p * m]])
  prove ([[!n. ?w x y z. &n = &w pow 2 + &x pow 2 + &y pow 2 + &z pow 2]])
   (MATCH_MP_TAC num_WF THEN X_GEN_TAC ([[n:num]]) THEN DISCH_TAC THEN
    ASM_CASES_TAC ([[n = 0]]) THENL
     [REPEAT (EXISTS_TAC ([[0]])) THEN ASM_REWRITE_TAC [] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV,
      ALL_TAC] THEN
    ASM_CASES_TAC ([[n = 1]]) THENL
     [EXISTS_TAC ([[1]]) THEN REPEAT (EXISTS_TAC ([[0]])) THEN
      ASM_REWRITE_TAC [] THEN CONV_TAC REAL_RAT_REDUCE_CONV,
      ALL_TAC] THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP PRIME_FACTOR) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[p:num]]) STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC ([[p divides n]]) THEN REWRITE_TAC [divides] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[m:num]]) MP_TAC) THEN
    ASM_CASES_TAC ([[m = 1]]) THENL
     [ALL_TAC,
      DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPEC ([[p:num]]) th) THEN MP_TAC (← HolLight.SPEC ([[m:num]]) th))) THEN
      ONCE_REWRITE_TAC [h1] THEN
      REWRITE_TAC [LT_MULT_RCANCEL] THEN
      ONCE_REWRITE_TAC [h2] THEN
      REWRITE_TAC [LT_MULT_LCANCEL] THEN
      UNDISCH_TAC ([[~(p * m = 0)]]) THEN REWRITE_TAC [MULT_EQ_0] THEN
      ASM_CASES_TAC ([[p = 0]]) THEN ASM_REWRITE_TAC [] THEN
      ASM_CASES_TAC ([[m = 0]]) THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN ([[~(p = 1)]]) ASSUME_TAC THENL
       [ASM_MESON_TAC [PRIME_1], ALL_TAC] THEN
      ASM_REWRITE_TAC [h3] THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[w1:num]]), ([[x1:num]]), ([[y1:num]]), ([[z1:num]])] THEN
      DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [([[w2:num]]), ([[x2:num]]), ([[y2:num]]), ([[z2:num]])] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_MUL)] THEN
      REWRITE_TAC [LAGRANGE_IDENTITY] THEN
      MATCH_MP_TAC lemma THEN REWRITE_TAC [REAL_OF_NUM_MUL] THEN
      MESON_TAC [REAL_INTEGER_CLOSURES]] THEN
    UNDISCH_TAC ([[m = 1]]) THEN DISCH_THEN SUBST_ALL_TAC THEN
    REWRITE_TAC [MULT_CLAUSES] THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP LAGRANGE_LEMMA) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[1 EXP 2 + 0 EXP 2]])) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [([[q:num]]), ([[x:num]]), ([[y:num]])] THEN STRIP_TAC THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV HolLight.SYM_CONV) THEN MATCH_MP_TAC AUBREY_THM_4 THEN
    SUBGOAL_THEN ([[q * p < p EXP 2]]) MP_TAC THENL
     [ASM_REWRITE_TAC [EXP_2, MULT_CLAUSES, ADD_CLAUSES] THEN
      MATCH_MP_TAC h4 THEN
      REPEAT CONJ_TAC THEN MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC [] THEN
      MAP_EVERY UNDISCH_TAC [([[~(p = 0)]]), ([[~(p = 1)]])] THEN ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [EXP_2, LT_MULT_RCANCEL] THEN ASM_REWRITE_TAC [] THEN
    DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[q:num]])) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [([[a:num]]), ([[b:num]]), ([[c:num]]), ([[d:num]])] THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[~(q = 0)]]) ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC ([[0 * p = x EXP 2 + y EXP 2 + 1 EXP 2 + 0 EXP 2]]) THEN
      DISCH_THEN (MP_TAC o HolLight.SYM) THEN REWRITE_TAC [MULT_CLAUSES, EXP_2] THEN
      REWRITE_TAC [ADD_EQ_0, ARITH_EQ], ALL_TAC] THEN
    SUBGOAL_THEN ([[&p = &q * &(q * p) / &q pow 2]]) SUBST1_TAC THENL
     [REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_MUL), REAL_MUL_ASSOC, real_div] THEN
      ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
      REWRITE_TAC [(← HolLight.GSYM REAL_POW_2)] THEN
      SIMP_TAC [REAL_MUL_ASSOC, REAL_POW_EQ_0, REAL_MUL_LINV, REAL_MUL_LID,
               (← HolLight.ASSUME ([[~(q = 0)]])), REAL_OF_NUM_EQ],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_ADD), (← HolLight.GSYM REAL_OF_NUM_POW)] THEN
    REWRITE_TAC [real_div, REAL_MUL_ASSOC, LAGRANGE_IDENTITY] THEN
    SUBST1_TAC (← HolLight.SYM (← HolLight.ASSUME ([[&q = &a pow 2 + &b pow 2 + &c pow 2 + &d pow 2]]))) THEN
    REWRITE_TAC [REAL_ADD_RDISTRIB] THEN
    REWRITE_TAC [(← HolLight.GSYM real_div), (← HolLight.GSYM REAL_POW_DIV)] THEN
    EXISTS_TAC ([[q:num]]) THEN REWRITE_TAC [(← HolLight.ASSUME ([[~(q = 0)]]))] THEN
    REWRITE_TAC [REAL_POW_DIV] THEN
    REWRITE_TAC [real_div, (← HolLight.GSYM REAL_ADD_RDISTRIB)] THEN
    REWRITE_TAC [REAL_EQ_MUL_RCANCEL] THEN
    REWRITE_TAC [REAL_INV_EQ_0, REAL_POW_EQ_0, REAL_OF_NUM_EQ,
                (← HolLight.ASSUME ([[~(q = 0)]]))] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV HolLight.SYM_CONV) THEN MATCH_MP_TAC lemma THEN
    REWRITE_TAC [REAL_OF_NUM_MUL] THEN MESON_TAC [REAL_INTEGER_CLOSURES])
  : ExceptT String IO thm).run
#eval LAGRANGE_REAL_NUM

/- ------------------------------------------------------------------------- -/
/- Also prove it for the natural numbers.                                    -/
/- ------------------------------------------------------------------------- -/

#eval phrase 44
def LAGRANGE_NUM : thm := keep "LAGRANGE_NUM" fun _ => (do
  prove ([[!n. ?w x y z. n = w EXP 2 + x EXP 2 + y EXP 2 + z EXP 2]])
   (GEN_TAC THEN MP_TAC (← HolLight.SPEC ([[n:num]]) LAGRANGE_REAL_NUM) THEN
    REWRITE_TAC [SessionLibrary.Analysis.REAL_POS, REAL_OF_NUM_POW, REAL_OF_NUM_ADD, REAL_OF_NUM_EQ])
  : ExceptT String IO thm).run
#eval LAGRANGE_NUM

/- ------------------------------------------------------------------------- -/
/- And for the integers.                                                     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 45
#eval Session.prioritize_int

#eval phrase 46
def LAGRANGE_INT : thm := keep "LAGRANGE_INT" fun _ => (do
  prove ([[!a. &0 <= a <=> ?w x y z. a = w pow 2 + x pow 2 + y pow 2 + z pow 2]])
   (GEN_TAC THEN EQ_TAC THENL
     [SPEC_TAC (([[a:int]]), ([[a:int]])) THEN REWRITE_TAC [(← HolLight.GSYM INT_FORALL_POS)] THEN
      X_GEN_TAC ([[n:num]]) THEN MP_TAC (← HolLight.SPEC ([[n:num]]) LAGRANGE_REAL_NUM) THEN
      REWRITE_TAC [REAL_OF_NUM_POW, REAL_OF_NUM_ADD, REAL_OF_NUM_EQ] THEN
      SIMP_TAC [(← HolLight.GSYM INT_OF_NUM_EQ), (← HolLight.GSYM INT_OF_NUM_POW), (← HolLight.GSYM INT_OF_NUM_ADD)] THEN
      MESON_TAC [],
      STRIP_TAC THEN ASM_SIMP_TAC [INT_LE_SQUARE, INT_LE_ADD, INT_POW_2]])
  : ExceptT String IO thm).run
#eval LAGRANGE_INT

#eval phrase 47
#eval Session.prioritize_num

end Hol100.FourSquares
