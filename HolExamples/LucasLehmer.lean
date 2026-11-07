/- File: HolExamples/LucasLehmer.lean
Translation of HOL Light's Examples/lucas_lehmer.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionLibrary.Iter
import SessionLibrary.Pocklington
import SessionLibrary.Floor
import SessionMultiLib.Vectors
import Hol100.Sqrt
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Iter SessionLibrary.Floor SessionLibrary.Prime SessionLibrary.Wo SessionLibrary.Card SessionLibrary.Pocklington SessionLibrary.Matroids SessionMultiLib.Misc Hol100.Sqrt SessionMultiLib.Vectors
namespace HolExamples.LucasLehmer

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
/-- Run an `IO (Except String α)` once, caching under `name`. -/
private def keepIO {α : Type} [Inhabited α] (name : String) (f : Unit → IO (Except String α)) : α :=
  keep name fun _ =>
    match runIO (f ()) with
    | .ok (.ok v) => v
    | .ok (.error e) => panic! s!"keepIO {name}: {e}"
    | .error e => panic! s!"keepIO {name}: {e}"
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def ms (ths : List thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (MESON ths tm)
private def nrc (tm : term) : ExceptT String IO thm := ExceptT.mk (NUM_REDUCE_CONV tm)
private def pcv (tm : term) : ExceptT String IO thm := ExceptT.mk (PRIME_CONV tm)
private def rf (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_FIELD tm)
private def rg (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_RING tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)

/- ========================================================================= -/
/- The Lucas-Lehmer test.                                                    -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Library/iter.ml";;
#eval SessionLibrary.Iter.ensureIter

#eval phrase 2
-- needs "Library/pocklington.ml";;
#eval SessionLibrary.Pocklington.ensurePocklington

#eval phrase 3
-- needs "Library/floor.ml";;
#eval SessionLibrary.Floor.ensureFloor

#eval phrase 4
-- needs "Multivariate/vectors.ml";;
#eval SessionMultiLib.Vectors.ensureVectors

#eval phrase 5
-- needs "100/sqrt.ml";;
#eval Hol100.Sqrt.ensure

/- ------------------------------------------------------------------------- -/
/- Relate real powers to iteration.                                          -/
/- ------------------------------------------------------------------------- -/

#eval phrase 6
def REAL_POW_ITER : thm := keep "REAL_POW_ITER" fun _ => (do
  prove ([[!x n. x pow n = ITER n (\y. x * y) (&1)]])
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [ITER, real_pow])
  : ExceptT String IO thm).run
#eval REAL_POW_ITER

/- ------------------------------------------------------------------------- -/
/- Basic definition of the Lucas-Lehmer sequence. To avoid troubles with     -/
/- cutoff subtraction and keep things in N we use m^2 + (p - 2) not m^2 - 2. -/
/- ------------------------------------------------------------------------- -/

#eval phrase 7
def llseq : thm := keep "llseq" fun _ => define
 [[llseq p 0 = 4 MOD p /\
  llseq p (SUC n) = ((llseq p n) EXP 2 + (p - 2)) MOD p]]
#eval llseq

/- ------------------------------------------------------------------------- -/
/- Closed form for the Lucas-Lehmer sequence.                                -/
/- ------------------------------------------------------------------------- -/

#eval phrase 8
def LLSEQ_CLOSEDFORM : thm := keep "LLSEQ_CLOSEDFORM" fun _ => (do
  let h6 ← rr (← ExceptT.mk [[(&2 + s) * (&2 - s) = &4 - s pow 2]])
  let h5 ← rr (← ExceptT.mk [[(x + y) pow 2 = x pow 2 + y pow 2 + &2 * x * y]])
  let h4 ← ar (← ExceptT.mk [[2 <= x /\ ~(p = 0) /\ ~(p = 1) ==> x + p - 2 = (x - 2) + p]])
  let h3 ← rr (← ExceptT.mk [[&0 <= x ==> &1 <= &2 + x]])
  let h2 ← rr (← ExceptT.mk [[x <= y /\ y pow 1 <= y pow n /\ &0 <= z pow n
      ==> x <= y pow n + z pow n]])
  let h1 ← ar (← ExceptT.mk [[2 EXP 2 <= x ==> 2 <= x]])
  prove ([[!p n. ~(p = 0)
         ==> ?x. llseq p n = x MOD p /\
                 &x = (&2 + sqrt(&3)) pow (2 EXP n) +
                      (&2 - sqrt(&3)) pow (2 EXP n)]])
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
    INDUCT_TAC THENL
     [EXISTS_TAC ([[4]]) THEN REWRITE_TAC [llseq, EXP] THEN REAL_ARITH_TAC2,
      ALL_TAC] THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN ([[x:num]]) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC ([[x EXP 2 - 2]]) THEN ASM_REWRITE_TAC [llseq] THEN
    SUBGOAL_THEN ([[2 <= x EXP 2]]) ASSUME_TAC THENL
     [MATCH_MP_TAC h1 THEN
      REWRITE_TAC [EXP_MONO_LE, ARITH_EQ] THEN
      ASM_REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_LE)] THEN
      MATCH_MP_TAC h2 THEN
      REPEAT CONJ_TAC THENL
       [SIMP_TAC [REAL_LE_ADDR, SQRT_POS_LE, REAL_POS],
        MATCH_MP_TAC REAL_POW_MONO THEN
        SIMP_TAC [LE_1, EXP_EQ_0, ARITH_EQ] THEN
        MATCH_MP_TAC h3 THEN
        SIMP_TAC [SQRT_POS_LE, REAL_POS],
        MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC [REAL_SUB_LE] THEN
        MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV],
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC ([[p = 1]]) THENL [ASM_REWRITE_TAC [MOD_1], ALL_TAC] THEN
      TRANS_TAC EQ_TRANS ([[(x EXP 2 + (p - 2)) MOD p]]) THEN CONJ_TAC THENL
       [ALL_TAC,
        ASM_SIMP_TAC [h4]] THEN
      ONCE_REWRITE_TAC [(← HolLight.GSYM MOD_ADD_MOD)] THENL
       [ASM_MESON_TAC [MOD_EXP_MOD],
        ASM_SIMP_TAC [MOD_REFL, ADD_CLAUSES, MOD_MOD_REFL]],
      ASM_SIMP_TAC [(← HolLight.GSYM REAL_OF_NUM_SUB), (← HolLight.GSYM REAL_OF_NUM_POW)] THEN
      REWRITE_TAC [ADD1, EXP_ADD, (← HolLight.GSYM REAL_POW_MUL), h5] THEN
      REWRITE_TAC [h6] THEN
      REWRITE_TAC [REAL_SQRT_POW_2, REAL_ABS_NUM, (← HolLight.GSYM REAL_POW_POW)] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC [REAL_POW_ONE] THEN CONV_TAC rg])
  : ExceptT String IO thm).run
#eval LLSEQ_CLOSEDFORM

/- ------------------------------------------------------------------------- -/
/- The main Lucas-Lehmer theorem.                                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 9
def LUCAS_LEHMER : thm := keep "LUCAS_LEHMER" fun _ => (do
  let h19 ← pcv (← ExceptT.mk [[prime 3]])
  let h18 ← rf (← ExceptT.mk [[&2 = (a + b * x) * q
        ==> ~(b = &0) ==> x = (&2 - a * q) / (b * q)]])
  let h17 ← ar (← ExceptT.mk [[~(n - 1 = 0) ==> n - 1 + 2 = n + 1]])
  let h16 ← nrc (← ExceptT.mk [[2 <= 1]])
  let h15 ← rr (← ExceptT.mk [[&1 - -- &1 = &2]])
  let h14 ← ar (← ExceptT.mk [[i < p ==> i <= p - 1]])
  let h13 ← ar (← ExceptT.mk [[k <= p - 1 ==> (k = p <=> p = 0)]])
  let h12 ← rg (← ExceptT.mk [[(a + b * s) - (a' + b' * s):real = (a'' + b'' * s) * q <=>
      a + b * s = (a'' * q + a') + (b'' * q + b') * s]])
  let h11 ← ms [] (← ExceptT.mk [[(a == b) equiv /\
      ((a == b) equiv ==> !x. (x == a) equiv <=> (x == b) equiv)
      ==> !x. (x == a) equiv <=> (x == b) equiv]])
  let h10 ← ar (← ExceptT.mk [[a <= q - 1 <=> a = 0 \/ a < q]])
  let h9 ← ms [CARD_SUBSET, FINITE_SUBSET, LE_TRANS, CARD_IMAGE_LE, FINITE_IMAGE] (← ExceptT.mk [[!f:num#num->A t. s SUBSET IMAGE f t /\ FINITE t /\ CARD t <= n
            ==> FINITE s /\ CARD s <= n]])
  let h8 ← rr (← ExceptT.mk [[a - -- &1  = b <=> a = b - &1]])
  let h7 ← ar (← ExceptT.mk [[2 <= p ==> SUC(p - 2) = p - 1]])
  let h6 ← rr (← ExceptT.mk [[(&2 + s) * (&2 - s) = &4 - s pow 2]])
  let h5 ← rr (← ExceptT.mk [[x - y = (a + b * s) * q /\
       y - z = (a' + b' * s) * q
       ==> x - z:real = ((a + a') + (b + b') * s) * q]])
  let h4 ← rr (← ExceptT.mk [[x - y:real = (a + b * s) * q ==> y - x = (--a + --b * s) * q]])
  let h3 ← ms [] (← ExceptT.mk [[(!x y. P x y ==> P y x) ==> (!x y. P x y <=> P y x)]])
  let h2 ← tt (← ExceptT.mk [[p /\ (p ==> q) ==> p /\ q]])
  let h1 ← ar (← ExceptT.mk [[2 EXP 2 <= x ==> 2 <= x - 1]])
  prove ([[!p. 2 <= p /\ llseq (2 EXP p - 1) (p - 2) = 0 ==> prime(2 EXP p - 1)]])
   (REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [PRIME_PRIME_FACTOR_SQRT] THEN
    SUBGOAL_THEN ([[2 <= 2 EXP p - 1]]) ASSUME_TAC THENL
     [MATCH_MP_TAC h1 THEN
      REWRITE_TAC [LE_EXP] THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    REPEAT (MATCH_MP_TAC h2 THEN
           CONJ_TAC THENL [ASM_ARITH_TAC, DISCH_TAC]) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[q:num]]) STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM (ASSUME_TAC o HolLight.MATCH_MP PRIME_GE_2) THEN
    FIRST_ASSUM (ASSUME_TAC o HolLight.MATCH_MP PRIME_IMP_NZ) THEN
    ABBREV_TAC ([[equiv =
    \x y. ?a b. integer a /\ integer b /\
                x - y = (a + b * sqrt(&3)) * &q]]) THEN
    SUBGOAL_THEN ([[!x:real. (x == x) equiv]]) ASSUME_TAC THENL
     [REWRITE_TAC [cong] THEN EXPAND_TAC "equiv" THEN
      GEN_TAC THEN REPEAT (EXISTS_TAC ([[&0]])) THEN
      REWRITE_TAC [INTEGER_CLOSED] THEN REAL_ARITH_TAC2,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!x y:real. (x == y) equiv <=> (y == x) equiv]]) ASSUME_TAC THENL
     [MATCH_MP_TAC h3 THEN
      REWRITE_TAC [cong] THEN EXPAND_TAC "equiv" THEN
      MESON_TAC [INTEGER_CLOSED, h4],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!x y z:real. (x == y) equiv /\ (y == z) equiv ==> (x == z) equiv]]) ASSUME_TAC THENL
     [REWRITE_TAC [cong] THEN EXPAND_TAC "equiv" THEN
      MESON_TAC [INTEGER_CLOSED, h5],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!k. ?a b. (&2 + sqrt(&3)) pow k = &a + &b * sqrt(&3)]]) STRIP_ASSUME_TAC THENL
     [INDUCT_TAC THENL
       [MAP_EVERY EXISTS_TAC [([[1]]), ([[0]])] THEN REAL_ARITH_TAC2,
        FIRST_X_ASSUM (X_CHOOSE_THEN ([[a:num]]) MP_TAC) THEN
        REWRITE_TAC [real_pow, LEFT_IMP_EXISTS_THM] THEN
        X_GEN_TAC ([[b:num]]) THEN DISCH_THEN SUBST1_TAC THEN
        MAP_EVERY EXISTS_TAC [([[2 * a + 3 * b]]), ([[2 * b + a]])] THEN
        REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_MUL), (← HolLight.GSYM REAL_OF_NUM_ADD)] THEN
        MP_TAC (← HolLight.SPEC ([[&3]]) SQRT_POW_2) THEN REWRITE_TAC [REAL_POS] THEN
        CONV_TAC rg],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!x y. ((&2 + sqrt(&3)) * x == (&2 + sqrt(&3)) * y) equiv <=>
          (x == y) equiv]]) ASSUME_TAC THENL
     [SUBGOAL_THEN ([[!x y:real. (x == y) equiv <=> (x - y == &0) equiv]]) (fun th => ONCE_REWRITE_TAC [th]) THENL
       [REWRITE_TAC [cong] THEN EXPAND_TAC "equiv" THEN SIMP_TAC [REAL_SUB_RZERO],
        REWRITE_TAC [(← HolLight.GSYM REAL_SUB_LDISTRIB)]] THEN
      REPEAT GEN_TAC THEN SPEC_TAC (([[x - y:real]]), ([[x:real]])) THEN
      X_GEN_TAC ([[x:real]]) THEN REWRITE_TAC [cong] THEN EXPAND_TAC "equiv" THEN
      REWRITE_TAC [REAL_SUB_RZERO] THEN EQ_TAC THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[u:real]]), ([[v:real]])] THEN
      REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC [REAL_SUB_RZERO] THEN DISCH_TAC THENL
       [MAP_EVERY EXISTS_TAC [([[&2 * u - &3 * v]]), ([[&2 * v - u]])],
        MAP_EVERY EXISTS_TAC [([[&2 * u + &3 * v]]), ([[&2 * v + u]])]] THEN
      ASM_SIMP_TAC [INTEGER_CLOSED] THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SYM) THEN
      MP_TAC (← HolLight.SPEC ([[&3]]) SQRT_POW_2) THEN REWRITE_TAC [REAL_POS] THEN
      CONV_TAC rg,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[((&2 + sqrt(&3)) pow (2 EXP (p - 1)) == -- &1) equiv]]) ASSUME_TAC THENL
     [UNDISCH_THEN ([[!x y:real. (x == y) equiv <=> (y == x) equiv]]) ((fun _ => ALL_TAC)) THEN
      MP_TAC (← HolLight.ISPECL [([[2 EXP p - 1]]), ([[p - 2]])] LLSEQ_CLOSEDFORM) THEN
      ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
      ASM_SIMP_TAC [MOD_EQ_0, LEFT_AND_EXISTS_THM] THEN
      ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN REWRITE_TAC [UNWIND_THM2] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[r:num]]) (MP_TAC o
       HolLight.AP_TERM ([[(*) ((&2 + sqrt(&3)) pow (2 EXP (p - 2)))]]))) THEN
      REWRITE_TAC [] THEN ONCE_REWRITE_TAC [REAL_ADD_LDISTRIB] THEN
      REWRITE_TAC [(← HolLight.GSYM REAL_POW_MUL), (← HolLight.GSYM REAL_POW_2), REAL_POW_POW] THEN
      REWRITE_TAC [h6] THEN
      REWRITE_TAC [REAL_SQRT_POW_2, REAL_ABS_NUM] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [REAL_POW_ONE] THEN
      REWRITE_TAC [(← HolLight.GSYM (← HolLight.CONJUNCT2 EXP))] THEN
      ASM_SIMP_TAC [h7] THEN
      SUBGOAL_THEN ([[?a b. (&2 + sqrt(&3)) pow (2 EXP (p - 2)) = &a + &b * sqrt(&3)]]) STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      REWRITE_TAC [cong] THEN EXPAND_TAC "equiv" THEN
      REWRITE_TAC [REAL_SUB_RNEG] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (X_CHOOSE_THEN ([[s:num]]) SUBST1_TAC o
         HolLight.REWRITE_RULE [divides]) THEN
      MAP_EVERY EXISTS_TAC [([[&a * &r * &s]]), ([[&b * &r * &s]])] THEN
      SIMP_TAC [INTEGER_CLOSED, (← HolLight.GSYM REAL_OF_NUM_MUL)] THEN REAL_ARITH_TAC2,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[((&2 + sqrt(&3)) pow (2 EXP p) == &1) equiv]]) ASSUME_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [cong]) THEN
      REWRITE_TAC [cong] THEN EXPAND_TAC "equiv" THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM, h8] THEN
      MAP_EVERY X_GEN_TAC [([[a:real]]), ([[b:real]])] THEN STRIP_TAC THEN
      SUBGOAL_THEN ([[p = (p - 1) + 1]]) SUBST1_TAC THENL
       [UNDISCH_TAC ([[2 <= p]]) THEN ARITH_TAC, ALL_TAC] THEN
      ASM_REWRITE_TAC [EXP_ADD, (← HolLight.GSYM REAL_POW_POW)] THEN
      EXISTS_TAC ([[&q * (a pow 2 + &3 * b pow 2) - &2 * a]]) THEN
      EXISTS_TAC ([[&2 * a * b * &q - &2 * b]]) THEN
      REPEAT (CONJ_TAC THENL [ASM_MESON_TAC [INTEGER_CLOSED], ALL_TAC]) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      MP_TAC (← HolLight.SPEC ([[&3]]) SQRT_POW_2) THEN REWRITE_TAC [REAL_POS] THEN
      CONV_TAC rg,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[?k. 0 < k /\ k <= 2 EXP p - 1 /\
        !n. ((&2 + sqrt(&3)) pow n == &1) equiv <=> k divides n]]) STRIP_ASSUME_TAC THENL
     [MP_TAC (← HolLight.ISPEC ([[\x y:real. (x == y) equiv]]) ORDER_EXISTENCE_CARD) THEN
      REWRITE_TAC [REAL_POW_ITER] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC h9 THEN
      EXISTS_TAC ([[\(a,b) y. (y == &a + &b * sqrt(&3)) equiv]]) THEN
      EXISTS_TAC ([[(0..q-1) CROSS (0..q-1)]]) THEN
      SIMP_TAC [CARD_CROSS, FINITE_CROSS, FINITE_NUMSEG, CARD_NUMSEG] THEN
      ASM_SIMP_TAC [SUB_ADD, SUB_0, LE_1, (← HolLight.GSYM EXP_2), SUBSET] THEN
      REWRITE_TAC [FORALL_IN_GSPEC, IN_UNIV, IN_IMAGE, EXISTS_PAIR_THM] THEN
      X_GEN_TAC ([[n:num]]) THEN REWRITE_TAC [IN_CROSS, (← HolLight.GSYM REAL_POW_ITER)] THEN
      FIRST_X_ASSUM (X_CHOOSE_THEN ([[a:num]]) MP_TAC o HolLight.SPEC ([[n:num]])) THEN
      DISCH_THEN (X_CHOOSE_TAC ([[b:num]])) THEN
      MAP_EVERY EXISTS_TAC [([[a MOD q]]), ([[b MOD q]])] THEN
      ASM_SIMP_TAC [IN_NUMSEG, LE_0, DIVISION, FUN_EQ_THM,
                   h10] THEN
      MATCH_MP_TAC h11 THEN
      CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
      REWRITE_TAC [cong] THEN EXPAND_TAC "equiv" THEN
      MAP_EVERY EXISTS_TAC [([[&(a DIV q)]]), ([[&(b DIV q)]])] THEN
      REWRITE_TAC [INTEGER_CLOSED, h12] THEN
      REWRITE_TAC [REAL_OF_NUM_ADD, REAL_OF_NUM_MUL] THEN
      ASM_SIMP_TAC [(← HolLight.GSYM DIVISION)],
      SUBGOAL_THEN ([[k divides 2 EXP p]]) MP_TAC THENL
       [ASM_MESON_TAC [], SIMP_TAC [DIVIDES_PRIMEPOW, PRIME_2]] THEN
      REWRITE_TAC [LE_LT, RIGHT_OR_DISTRIB, EXISTS_OR_THM, UNWIND_THM2] THEN
      ASM_SIMP_TAC [h13] THEN
      REWRITE_TAC [EXP_EQ_0, ARITH_EQ] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[i:num]]) STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN ([[((&2 + sqrt (&3)) pow (2 EXP (p - 1)) == &1) (equiv)]]) ASSUME_TAC THENL
       [ASM_REWRITE_TAC [] THEN SIMP_TAC [DIVIDES_EXP_LE, LE_REFL] THEN
        ASM_SIMP_TAC [h14],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[(&1 == -- &1) (equiv)]]) MP_TAC THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      REWRITE_TAC [cong] THEN EXPAND_TAC "equiv" THEN
      REWRITE_TAC [NOT_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[a:real]]), ([[b:real]])] THEN
      REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC [h15] THEN
      ASM_CASES_TAC ([[b = &0]]) THENL
       [ASM_REWRITE_TAC [REAL_MUL_LZERO, REAL_ADD_RID] THEN
        DISCH_THEN (MP_TAC o HolLight.AP_TERM ([[abs]])) THEN REWRITE_TAC [REAL_ABS_MUL] THEN
        SUBGOAL_THEN ([[?q. abs a = &q]]) (CHOOSE_THEN SUBST1_TAC) THENL [ASM_MESON_TAC [integer], REWRITE_TAC [REAL_ABS_NUM]] THEN
        REWRITE_TAC [REAL_OF_NUM_MUL, REAL_OF_NUM_EQ] THEN
        DISCH_THEN (ASSUME_TAC o HolLight.SYM) THEN
        MP_TAC PRIME_2 THEN REWRITE_TAC [prime, ARITH_EQ] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[q:num]])) THEN ANTS_TAC THENL
         [REWRITE_TAC [divides] THEN ASM_MESON_TAC [MULT_SYM], ALL_TAC] THEN
        DISCH_THEN (DISJ_CASES_THEN SUBST_ALL_TAC) THENL
         [ASM_MESON_TAC [h16], ALL_TAC] THEN
        SUBGOAL_THEN ([[2 divides (2 EXP p - 1) + 2]]) MP_TAC THENL
         [MATCH_MP_TAC DIVIDES_ADD THEN ASM_REWRITE_TAC [DIVIDES_REFL],
          ASM_SIMP_TAC [h17]] THEN
        REWRITE_TAC [DIVIDES_2, EVEN_ADD, EVEN_EXP, ARITH] THEN
        UNDISCH_TAC ([[2 <= p]]) THEN ARITH_TAC,
        DISCH_THEN (MP_TAC o HolLight.MATCH_MP h18) THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o HolLight.AP_TERM ([[rational]])) THEN
        SIMP_TAC [IRRATIONAL_SQRT_PRIME, h19] THEN
        ASM_MESON_TAC [RATIONAL_CLOSED, INTEGER_CLOSED]]])
  : ExceptT String IO thm).run
#eval LUCAS_LEHMER

/- ------------------------------------------------------------------------- -/
/- Actual evaluation of the LL sequence.                                     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 10
-- let ll_verbose = ref false;;  (only ever false here: the verbose runs are commented out)
def ll_verbose : Bool := false
#eval IO.println "{contents = false}"

#eval phrase 11
-- let LUCAS_LEHMER_RULE = ...;;
def LUCAS_LEHMER_RULE_pths : thm × thm := keepIO "LUCAS_LEHMER_RULE_pths" fun _ => (do
  let pth_base ← prove ([[llseq (2 EXP p - 1) 0 = 4 MOD (2 EXP p - 1)]]) (REWRITE_TAC [llseq])
  let h4 ← ar (← ExceptT.mk [[1 <= n <=> ~(n = 0)]])
  let h3 ← ar (← ExceptT.mk [[x + y - 1 + w = u + v + z + r + 2 /\ 2 EXP 2 <= y /\ w * 1 <= v
      ==> x + y - 1 - 2 = u + (v - w + z) + r]])
  let h2 ← ar (← ExceptT.mk [[!p:num. (x + p) + y = p + z ==> x + y = z]])
  let h1 ← ar (← ExceptT.mk [[r < 1 <=> r = 0]])
  let pth_step ← prove ([[llseq (2 EXP p - 1) n = m
     ==> m * m + q = 2 EXP p * q + 2 + r /\ r < 2 EXP p - 1
         ==> llseq (2 EXP p - 1) (SUC n) = r]])
   (REWRITE_TAC [llseq] THEN
    ASM_CASES_TAC ([[p = 0]]) THEN ASM_REWRITE_TAC [] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [LT] THEN
    ASM_CASES_TAC ([[p = 1]]) THEN ASM_REWRITE_TAC [] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC [MOD_1, h1] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_UNIQ THEN
    EXISTS_TAC ([[q + 1]]) THEN ASM_REWRITE_TAC [EXP_2] THEN
    MATCH_MP_TAC h2 THEN
    EXISTS_TAC ([[q:num]]) THEN
    ASM_REWRITE_TAC [RIGHT_ADD_DISTRIB, LEFT_SUB_DISTRIB, MULT_CLAUSES] THEN
    MATCH_MP_TAC h3 THEN
    REWRITE_TAC [LE_MULT_LCANCEL, LE_EXP, EXP_EQ_0, h4] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC)
  pure (pth_base, pth_step)
  : ExceptT String IO (thm × thm)).run
def LUCAS_LEHMER_RULE (p : Int) : IO (Except String thm) := (do
  let (pth_base, pth_step) := LUCAS_LEHMER_RULE_pths
  let pconv_tt := HolLight.GEN_REWRITE_CONV HolCore.Lib.I [← HolLight.TAUT [[T /\ T <=> T]]]
  let p_tm ← ExceptT.mk [[p:num]]
  let n_tm ← ExceptT.mk [[n:num]]
  let m_tm ← ExceptT.mk [[m:num]]
  let q_tm ← ExceptT.mk [[q:num]]
  let r_tm ← ExceptT.mk [[r:num]]
  let BINOP2_CONV (c1 c2 : HolCore.Equal.ioconv) : HolCore.Equal.ioconv :=
    HolLight.COMB2_CONV (HolLight.RAND_CONV c1) c2
  let ariconv :=
    BINOP2_CONV (BINOP2_CONV (HolLight.LAND_CONV NUM_MULT_CONV THENC NUM_ADD_CONV)
                             (BINOP2_CONV NUM_MULT_CONV NUM_ADD_CONV THENC NUM_ADD_CONV) THENC
                 NUM_EQ_CONV)
                NUM_LT_CONV THENC pconv_tt
  let th_base ← HolLight.CONV_RULE (HolLight.RAND_CONV NUM_REDUCE_CONV)
    (← HolLight.INST [(← ec (mk_small_numeral p), p_tm)] pth_base)
  let th_step ← HolLight.CONV_RULE (HolLight.RAND_CONV (HolLight.LAND_CONV NUM_REDUCE_CONV))
    (← HolLight.INST [(← ec (mk_small_numeral p), p_tm)] pth_step)
  let pp1 : Rat := (2 : Rat) ^ p.toNat - 1
  let rec lucas_lehmer : Nat → ExceptT String IO (thm × Rat)
    | 0 => do pure (th_base, ← ec (HolCore.Basics.dest_numeral (← ec (rand (concl th_base)))))
    | k + 1 => do
      let (th1, mval) ← lucas_lehmer k
      -- gofer() (ll_verbose is false)
      let mtm ← ec (rand (concl th1))
      let yval := mval ^ 2
      let qval : Rat := (Int.fdiv yval.num pp1.num : Int)
      let rval : Rat := yval - qval * pp1 - 2
      let th3 ← HolLight.INST [(← ec (mk_small_numeral (Int.ofNat k)), n_tm), (mtm, m_tm),
                               (← ec (mk_numeral qval), q_tm), (← ec (mk_numeral rval), r_tm)] th_step
      let th4 ← HolLight.MP th3 th1
      let th5 ← HolLight.MP th4 (← HolLight.EQT_ELIM (← ExceptT.mk (ariconv (← ec (HolCore.Equal.lhand (concl th4))))))
      pure (← HolLight.CONV_RULE (HolLight.LAND_CONV (HolLight.RAND_CONV NUM_SUC_CONV)) th5, rval)
  let (th1, y) ← lucas_lehmer (p - 2).toNat
  if y != 0 then throw "LUCAS_LEHMER_RULE: not a prime"
  let th2 ← HolLight.SPEC (← ec (mk_small_numeral p)) LUCAS_LEHMER
  let th3 ← HolLight.CONV_RULE (HolLight.LAND_CONV (HolLight.RAND_CONV (HolLight.LAND_CONV
       (HolLight.RAND_CONV NUM_SUB_CONV THENC (fun _ => pure (.ok th1)))))) th2
  HolLight.MP th3 (← HolLight.EQT_ELIM (← ExceptT.mk (NUM_REDUCE_CONV (← ec (HolCore.Equal.lhand (concl th3))))))
  : ExceptT String IO thm).run
#eval (do replay LUCAS_LEHMER_RULE_pths; IO.println "<fun>" : IO Unit)

/- ------------------------------------------------------------------------- -/
/- Time a few small examples.                                                -/
/- ------------------------------------------------------------------------- -/

#eval phrase 12
-- ll_verbose := false;;
#eval (pure () : IO Unit)

#eval phrase 13
-- time LUCAS_LEHMER_RULE 3;;
#eval try_ (HolCore.Lib.time LUCAS_LEHMER_RULE 3) HolCore.Printer.string_of_thm

#eval phrase 14
-- time LUCAS_LEHMER_RULE 5;;
#eval try_ (HolCore.Lib.time LUCAS_LEHMER_RULE 5) HolCore.Printer.string_of_thm

#eval phrase 15
-- time LUCAS_LEHMER_RULE 7;;
#eval try_ (HolCore.Lib.time LUCAS_LEHMER_RULE 7) HolCore.Printer.string_of_thm

#eval phrase 16
-- time LUCAS_LEHMER_RULE 13;;
#eval try_ (HolCore.Lib.time LUCAS_LEHMER_RULE 13) HolCore.Printer.string_of_thm

#eval phrase 17
-- time LUCAS_LEHMER_RULE 17;;
#eval try_ (HolCore.Lib.time LUCAS_LEHMER_RULE 17) HolCore.Printer.string_of_thm

#eval phrase 18
-- time LUCAS_LEHMER_RULE 19;;
#eval try_ (HolCore.Lib.time LUCAS_LEHMER_RULE 19) HolCore.Printer.string_of_thm

#eval phrase 19
-- time LUCAS_LEHMER_RULE 31;;
#eval try_ (HolCore.Lib.time LUCAS_LEHMER_RULE 31) HolCore.Printer.string_of_thm

#eval phrase 20
-- time LUCAS_LEHMER_RULE 61;;
#eval try_ (HolCore.Lib.time LUCAS_LEHMER_RULE 61) HolCore.Printer.string_of_thm

#eval phrase 21
-- time LUCAS_LEHMER_RULE 89;;
#eval try_ (HolCore.Lib.time LUCAS_LEHMER_RULE 89) HolCore.Printer.string_of_thm

#eval phrase 22
-- time LUCAS_LEHMER_RULE 107;;
#eval try_ (HolCore.Lib.time LUCAS_LEHMER_RULE 107) HolCore.Printer.string_of_thm

#eval phrase 23
-- time LUCAS_LEHMER_RULE 127;;
#eval try_ (HolCore.Lib.time LUCAS_LEHMER_RULE 127) HolCore.Printer.string_of_thm

#eval phrase 24
-- time LUCAS_LEHMER_RULE 521;;
#eval try_ (HolCore.Lib.time LUCAS_LEHMER_RULE 521) HolCore.Printer.string_of_thm

#eval phrase 25
-- time LUCAS_LEHMER_RULE 607;;
#eval try_ (HolCore.Lib.time LUCAS_LEHMER_RULE 607) HolCore.Printer.string_of_thm

end HolExamples.LucasLehmer
