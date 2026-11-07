/- File: Hol100/TwoSquares.lean
Translation of HOL Light's 100/two_squares.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionLibrary.Prime
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Prime
namespace Hol100.TwoSquares

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def nrc (tm : term) : ExceptT String IO thm := ExceptT.mk (NUM_REDUCE_CONV tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)

/- ========================================================================= -/
/- Representation of primes == 1 (mod 4) as sum of 2 squares.                -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Library/prime.ml";;
#eval SessionLibrary.Prime.ensurePrime

#eval phrase 2
#eval Session.prioritize_num

/- ------------------------------------------------------------------------- -/
/- Definition of involution and various basic lemmas.                        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 3
def involution : thm := keep "involution" fun _ => new_definition
 [[involution f s = !x. x IN s ==> f(x) IN s /\ (f(f(x)) = x)]]
#eval involution

#eval phrase 4
def INVOLUTION_IMAGE : thm := keep "INVOLUTION_IMAGE" fun _ => (do
  prove ([[!f s. involution f s ==> (IMAGE f s = s)]])
   (REWRITE_TAC [involution, EXTENSION, IN_IMAGE] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval INVOLUTION_IMAGE

#eval phrase 5
def INVOLUTION_DELETE : thm := keep "INVOLUTION_DELETE" fun _ => (do
  prove ([[involution f s /\ a IN s /\ (f a = a) ==> involution f (s DELETE a)]])
   (REWRITE_TAC [involution, IN_DELETE] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval INVOLUTION_DELETE

#eval phrase 6
def INVOLUTION_STEPDOWN : thm := keep "INVOLUTION_STEPDOWN" fun _ => (do
  prove ([[involution f s /\ a IN s ==> involution f (s DIFF {a, (f a)})]])
   (REWRITE_TAC [involution, IN_DIFF, IN_INSERT, NOT_IN_EMPTY] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval INVOLUTION_STEPDOWN

#eval phrase 7
def INVOLUTION_NOFIXES : thm := keep "INVOLUTION_NOFIXES" fun _ => (do
  prove ([[involution f s ==> involution f {x | x IN s /\ ~(f x = x)}]])
   (REWRITE_TAC [involution, IN_ELIM_THM] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval INVOLUTION_NOFIXES

#eval phrase 8
def INVOLUTION_SUBSET : thm := keep "INVOLUTION_SUBSET" fun _ => (do
  prove ([[!f s t. involution f s /\ (!x. x IN t ==> f(x) IN t) /\ t SUBSET s
           ==> involution f t]])
   (REWRITE_TAC [involution, SUBSET] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval INVOLUTION_SUBSET

#eval phrase 9
def INVOLUTION_EVEN : thm := keep "INVOLUTION_EVEN" fun _ => (do
  prove ([[!s. FINITE(s) /\ involution f s /\ (!x:A. x IN s ==> ~(f x = x))
       ==> EVEN(CARD s)]])
   (REWRITE_TAC [involution] THEN MESON_TAC [INVOLUTION_EVEN_NOFIXPOINTS])
  : ExceptT String IO thm).run
#eval INVOLUTION_EVEN

/- ------------------------------------------------------------------------- -/
/- So an involution with exactly one fixpoint has odd card domain.           -/
/- ------------------------------------------------------------------------- -/

#eval phrase 10
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

#eval phrase 11
def INVOLUTION_ODD : thm := keep "INVOLUTION_ODD" fun _ => (do
  prove ([[!n s. FINITE(s) /\ involution f s /\ ODD(CARD s)
         ==> ?a. a IN s /\ (f a = a)]])
   (REWRITE_TAC [(← HolLight.GSYM NOT_EVEN)] THEN MESON_TAC [INVOLUTION_EVEN])
  : ExceptT String IO thm).run
#eval INVOLUTION_ODD

/- ------------------------------------------------------------------------- -/
/- Consequently, if one involution has a unique fixpoint, other has one.     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 12
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

#eval phrase 13
def zset : thm := keep "zset" fun _ => new_definition
 [[zset(a) = {(x,y,z) | x EXP 2 + 4 * y * z = a}]]
#eval zset

#eval phrase 14
def zag : thm := keep "zag" fun _ => new_definition
 [[zag(x,y,z) =
        if x + z < y then (x + 2 * z,z,y - (x + z))
        else if x < 2 * y then (2 * y - x, y, (x + z) - y)
        else (x - 2 * y,(x + z) - y, y)]]
#eval zag

#eval phrase 15
def tag : thm := keep "tag" fun _ => new_definition
 [[tag((x,y,z):num#num#num) = (x,z,y)]]
#eval tag

#eval phrase 16
def ZAG_INVOLUTION_GENERAL : thm := keep "ZAG_INVOLUTION_GENERAL" fun _ => (do
  prove ([[0 < x /\ 0 < y /\ 0 < z ==> (zag(zag(x,y,z)) = (x,y,z))]])
   (REWRITE_TAC [zag] THEN REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    REWRITE_TAC [zag] THEN REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    REWRITE_TAC [PAIR_EQ] THEN
    POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist HolLight.CONJ) THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval ZAG_INVOLUTION_GENERAL

#eval phrase 17
def IN_TRIPLE : thm := keep "IN_TRIPLE" fun _ => (do
  prove ([[(a,b,c) IN {(x,y,z) | P x y z} <=> P a b c]])
   (REWRITE_TAC [IN_ELIM_THM, PAIR_EQ] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval IN_TRIPLE

#eval phrase 18
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

#eval phrase 19
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

#eval phrase 20
def PRIME_XYZ_NONZERO : thm := keep "PRIME_XYZ_NONZERO" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[~(0 < x) = (x = 0)]])
  prove ([[prime(x EXP 2 + 4 * y * z) ==> 0 < x /\ 0 < y /\ 0 < z]])
   (CONV_TAC HolLight.CONTRAPOS_CONV THEN
    REWRITE_TAC [DE_MORGAN_THM, h1] THEN
    DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC [EXP_2, MULT_CLAUSES, ADD_CLAUSES, PRIME_SQUARE, PRIME_4X])
  : ExceptT String IO thm).run
#eval PRIME_XYZ_NONZERO

#eval phrase 21
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

#eval phrase 22
def TAG_INVOLUTION : thm := keep "TAG_INVOLUTION" fun _ => (do
  prove ([[!a. involution tag (zset a)]])
   (REWRITE_TAC [involution, tag, zset, FORALL_PAIR_THM] THEN
    REWRITE_TAC [IN_TRIPLE] THEN REWRITE_TAC [MULT_AC])
  : ExceptT String IO thm).run
#eval TAG_INVOLUTION

#eval phrase 23
def ZAG_LEMMA : thm := keep "ZAG_LEMMA" fun _ => (do
  prove ([[(zag(x,y,z) = (x,y,z)) ==> (y = x)]])
   (REWRITE_TAC [zag, INT_POW_2] THEN
    REPEAT (COND_CASES_TAC THEN ASM_SIMP_TAC [PAIR_EQ]) THEN
    POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist HolLight.CONJ) THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval ZAG_LEMMA

#eval phrase 24
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

#eval phrase 25
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

#eval phrase 26
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

end Hol100.TwoSquares
