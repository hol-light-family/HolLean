/- File: HolExamples/Cong.lean
Translation of HOL Light's Examples/cong.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolExamples.Common
open HolCore.Kernel Session HolLight.Syntax HolExamples
namespace HolExamples.Cong

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- ========================================================================= -/
/- Integer congruences.                                                      -/
/- ========================================================================= -/

#eval phrase 1
#eval Session.prioritize_int

/- ------------------------------------------------------------------------- -/
/- Combined rewrite, for later proofs.                                       -/
/- ------------------------------------------------------------------------- -/

#eval phrase 2
unsafe def CONG : thm := keep "CONG" fun _ => (do
  prove ([[(x == y) (mod n) <=> ?q. x - y = q * n]])
   (REWRITE_TAC [int_congruent, int_divides] THEN MESON_TAC [INT_MUL_SYM])
  : ExceptT String IO thm).run
#eval CONG

/- ------------------------------------------------------------------------- -/
/- Trivial consequences.                                                     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 3
unsafe def CONG_MOD_0 : thm := keep "CONG_MOD_0" fun _ => (do
  prove ([[(x == y) (mod (&0)) <=> (x = y)]])
   INTEGER_TAC
  : ExceptT String IO thm).run
#eval CONG_MOD_0

#eval phrase 4
unsafe def CONG_MOD_1 : thm := keep "CONG_MOD_1" fun _ => (do
  prove ([[(x == y) (mod (&1))]])
   INTEGER_TAC
  : ExceptT String IO thm).run
#eval CONG_MOD_1

/- ------------------------------------------------------------------------- -/
/- Congruence is an equivalence relation.                                    -/
/- ------------------------------------------------------------------------- -/

#eval phrase 5
unsafe def CONG_REFL : thm := keep "CONG_REFL" fun _ => (do
  prove ([[!n x. (x == x) (mod n)]])
   INTEGER_TAC
  : ExceptT String IO thm).run
#eval CONG_REFL

#eval phrase 6
unsafe def CONG_SYM : thm := keep "CONG_SYM" fun _ => (do
  prove ([[!n x y. (x == y) (mod n) ==> (y == x) (mod n)]])
   INTEGER_TAC
  : ExceptT String IO thm).run
#eval CONG_SYM

#eval phrase 7
unsafe def CONG_TRANS : thm := keep "CONG_TRANS" fun _ => (do
  prove ([[!n x y z. (x == y) (mod n) /\ (y == z) (mod n) ==> (x == z) (mod n)]])
   INTEGER_TAC
  : ExceptT String IO thm).run
#eval CONG_TRANS

/- ------------------------------------------------------------------------- -/
/- Congruences are indeed congruences.                                       -/
/- ------------------------------------------------------------------------- -/

#eval phrase 8
unsafe def CONG_ADD : thm := keep "CONG_ADD" fun _ => (do
  prove ([[!n x1 x2 y1 y2.
    (x1 == x2) (mod n) /\ (y1 == y2) (mod n) ==> (x1 + y1 == x2 + y2) (mod n)]])
   INTEGER_TAC
  : ExceptT String IO thm).run
#eval CONG_ADD

#eval phrase 9
unsafe def CONG_NEG : thm := keep "CONG_NEG" fun _ => (do
  prove ([[!n x1 x2. (x1 == x2) (mod n) ==> (--x1 == --x2) (mod n)]])
   INTEGER_TAC
  : ExceptT String IO thm).run
#eval CONG_NEG

#eval phrase 10
unsafe def CONG_SUB : thm := keep "CONG_SUB" fun _ => (do
  prove ([[!n x1 x2 y1 y2.
    (x1 == x2) (mod n) /\ (y1 == y2) (mod n) ==> (x1 - y1 == x2 - y2) (mod n)]])
   INTEGER_TAC
  : ExceptT String IO thm).run
#eval CONG_SUB

#eval phrase 11
unsafe def CONG_MUL : thm := keep "CONG_MUL" fun _ => (do
  prove ([[!n x1 x2 y1 y2.
    (x1 == x2) (mod n) /\ (y1 == y2) (mod n) ==> (x1 * y1 == x2 * y2) (mod n)]])
   INTEGER_TAC
  : ExceptT String IO thm).run
#eval CONG_MUL

/- ------------------------------------------------------------------------- -/
/- Various other trivial properties of congruences.                          -/
/- ------------------------------------------------------------------------- -/

#eval phrase 12
unsafe def CONG_MOD_NEG : thm := keep "CONG_MOD_NEG" fun _ => (do
  prove ([[!x y n. (x == y) (mod (--n)) <=> (x == y) (mod n)]])
   INTEGER_TAC
  : ExceptT String IO thm).run
#eval CONG_MOD_NEG

#eval phrase 13
unsafe def CONG_MOD_ABS : thm := keep "CONG_MOD_ABS" fun _ => (do
  prove ([[!x y n. (x == y) (mod (abs n)) <=> (x == y) (mod n)]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [INT_ABS] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [CONG_MOD_NEG])
  : ExceptT String IO thm).run
#eval CONG_MOD_ABS

#eval phrase 14
unsafe def CONG_MULTIPLE : thm := keep "CONG_MULTIPLE" fun _ => (do
  prove ([[!m n. (m * n == &0) (mod n)]])
   INTEGER_TAC
  : ExceptT String IO thm).run
#eval CONG_MULTIPLE

#eval phrase 15
unsafe def CONG_SELF : thm := keep "CONG_SELF" fun _ => (do
  prove ([[!n. (n == &0) (mod n)]])
   INTEGER_TAC
  : ExceptT String IO thm).run
#eval CONG_SELF

#eval phrase 16
unsafe def CONG_SELF_ABS : thm := keep "CONG_SELF_ABS" fun _ => (do
  prove ([[!n. (abs(n) == &0) (mod n)]])
   (ONCE_REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM CONG_MOD_ABS))] THEN REWRITE_TAC [CONG_SELF])
  : ExceptT String IO thm).run
#eval CONG_SELF_ABS

#eval phrase 17
unsafe def CONG_MOD_1_2 : thm := keep "CONG_MOD_1_2" fun _ => (do
  prove ([[(x == y) (mod &1)]])
   INTEGER_TAC
  : ExceptT String IO thm).run
#eval CONG_MOD_1_2

/- ------------------------------------------------------------------------- -/
/- Can choose a representative, either positive or with minimal magnitude.   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 18
unsafe def CONG_REP_POS_POS : thm := keep "CONG_REP_POS_POS" fun _ => (do
  prove ([[!n x. &0 <= x /\ ~(n = &0)
         ==> ?y. &0 <= y /\ y < abs(n) /\ (x == y) (mod n)]])
   (REWRITE_TAC [IMP_CONJ] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM INT_FORALL_POS))] THEN
    MAP_EVERY X_GEN_TAC [ [[n:int]], [[k:num]] ] THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM CONG_MOD_ABS))] THEN
    MP_TAC (← ExceptT.mk (HolLight.SPEC ([[n:int]]) INT_ABS_POS)) THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (INT_ARITH [[(n = &0) <=> (abs n = &0)]]))] THEN
    SPEC_TAC ([[abs n]], [[n:int]]) THEN REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM INT_FORALL_POS))] THEN
    X_GEN_TAC [[n:num]] THEN REWRITE_TAC [INT_OF_NUM_EQ] THEN DISCH_TAC THEN
    EXISTS_TAC [[&(k MOD n)]] THEN
    REWRITE_TAC [CONG, INT_OF_NUM_LE, INT_OF_NUM_LT] THEN
    ASM_SIMP_TAC [DIVISION, LE_0] THEN EXISTS_TAC [[&(k DIV n)]] THEN
    REWRITE_TAC [(← ExceptT.mk (INT_ARITH [[(x - y = z) <=> (x = z + y)]]))] THEN
    REWRITE_TAC [INT_OF_NUM_MUL, INT_OF_NUM_ADD, INT_OF_NUM_EQ] THEN
    ASM_SIMP_TAC [DIVISION])
  : ExceptT String IO thm).run
#eval CONG_REP_POS_POS

#eval phrase 19
unsafe def CONG_REP_POS : thm := keep "CONG_REP_POS" fun _ => (do
  prove ([[!n x. ~(n = &0) ==> ?y. &0 <= y /\ y < abs(n) /\ (x == y) (mod n)]])
   (REPEAT STRIP_TAC THEN
    DISJ_CASES_TAC (← ExceptT.mk (INT_ARITH [[&0 <= x \/ &0 <= --x]])) THEN
    ASM_SIMP_TAC [CONG_REP_POS_POS] THEN
    MP_TAC (← ExceptT.mk (HolLight.SPECL [ [[n:int]], [[(--x)]] ] CONG_REP_POS_POS)) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[y:int]]) STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC [[y = &0]] THENL
     [EXISTS_TAC [[y:int]] THEN
      FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP CONG_NEG) THEN
      ASM_REWRITE_TAC [INT_NEG_0, INT_NEG_NEG],
      ALL_TAC] THEN
    EXISTS_TAC [[abs(n) - y]] THEN
    ASM_SIMP_TAC [(← ExceptT.mk (INT_ARITH [[y < abs(n) ==> &0 <= abs(n) - y]])),
                 (← ExceptT.mk (INT_ARITH [[&0 <= y /\ ~(y = &0) ==> abs(n) - y < abs(n)]]))] THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP CONG_NEG) THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP CONG_SYM) THEN
    DISCH_THEN (MP_TAC o HolLight.CONJ (← ExceptT.mk (HolLight.SPEC ([[abs n]]) CONG_SELF))) THEN
    REWRITE_TAC [CONG_MOD_ABS] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP CONG_ADD) THEN
    REWRITE_TAC [INT_NEG_NEG, INT_ADD_LID] THEN
    MESON_TAC [(← ExceptT.mk (INT_ARITH [[x + --y = x - y]])), CONG_SYM])
  : ExceptT String IO thm).run
#eval CONG_REP_POS

#eval phrase 20
unsafe def CONG_REP_MIN : thm := keep "CONG_REP_MIN" fun _ => (do
  prove ([[!n x. ~(n = &0)
         ==> ?y. --(abs n) <= &2 * y /\ &2 * y < abs n /\ (x == y) (mod n)]])
   (REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP CONG_REP_POS) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[y:int]]) STRIP_ASSUME_TAC o HolLight.SPEC [[x:int]]) THEN
    MP_TAC (← ExceptT.mk (INT_ARITH
     [[&0 <= y /\ y < abs n
    ==> --(abs n) <= &2 * y /\ &2 * y < abs(n) \/
        --(abs n) <= &2 * (y - abs(n)) /\ &2 * (y - abs(n)) < abs(n)]])) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THENL
     [ASM_MESON_TAC [CONG_REP_POS, INT_LT_IMP_LE], ALL_TAC] THEN
    EXISTS_TAC [[y - abs(n)]] THEN ASM_REWRITE_TAC [] THEN
    MP_TAC (← ExceptT.mk (HolLight.SPEC ([[n:int]]) CONG_SELF_ABS)) THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP CONG_SYM) THEN
    UNDISCH_TAC [[(x == y) (mod n)]] THEN
    REWRITE_TAC [IMP_IMP] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP CONG_SUB) THEN
    REWRITE_TAC [(← ExceptT.mk (INT_ARITH [[x - &0 = x]]))])
  : ExceptT String IO thm).run
#eval CONG_REP_MIN

#eval phrase 21
unsafe def CONG_REP_MIN_ABS : thm := keep "CONG_REP_MIN_ABS" fun _ => (do
  prove ([[!n x. ~(n = &0) ==> ?y. &2 * abs(y) <= abs(n) /\ (x == y) (mod n)]])
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o HolLight.MATCH_MP CONG_REP_MIN) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[x:int]]) THEN MATCH_MP_TAC MONO_EXISTS THEN
    SIMP_TAC [] THEN INT_ARITH_TAC)
  : ExceptT String IO thm).run
#eval CONG_REP_MIN_ABS

end HolExamples.Cong
