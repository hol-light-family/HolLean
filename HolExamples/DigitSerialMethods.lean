/- File: HolExamples/DigitSerialMethods.lean
Translation of HOL Light's Examples/digit_serial_methods.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolExamples.Common
import SessionMultiLib.RealAnalysis
open HolCore.Kernel Session HolLight.Syntax HolExamples
open SessionLibrary.Card SessionLibrary.Floor
open SessionMultiLib.Misc SessionMultiLib.Vectors SessionMultiLib.Determinants
open SessionMultiLib.Metric SessionMultiLib.Topology SessionMultiLib.Convex
open SessionMultiLib.ComplexAlgebra SessionMultiLib.Complexes SessionMultiLib.Transcendentals SessionMultiLib.RealAnalysis
namespace HolExamples.DigitSerialMethods

/- Helpers: the session's `prove` lifted into `ExceptT String IO`, so tactic
   scripts read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ec {α : Type} (x : Except String α) : ExceptT String IO α := ExceptT.mk (pure x)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)
private def rf (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_FIELD tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)
private def sr (tm : term) : ExceptT String IO thm := ExceptT.mk (SET_RULE tm)
private def ms (ths : List thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (MESON ths tm)
private def nd (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.new_definition tm)
private def prfe (ax : thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (prove_recursive_functions_exist ax tm)

-- ========================================================================= --
-- HOL Light formalizations of some of the main theorems from the paper      --
-- by Warren Ferguson, Jesse Bingham, Levent Erkok, John Harrison and        --
-- Joe Leslie-Hurd: "Digit Serial Methods with Applications to               --
-- Division and Square Root", IEEE Transactions on Computers, vol. 67,       --
-- issue 3, pp. 449-456, 2017.                                               --
-- ========================================================================= --

-- This dependency is just for some convex function basics.
-- It is a bit extravagent for the small amount actually used.

#eval phrase 1
-- needs "Multivariate/realanalysis.ml";;
#eval SessionMultiLib.RealAnalysis.ensureRealAnalysis

-- ------------------------------------------------------------------------- --
-- The main proxy theorem.                                                   --
-- ------------------------------------------------------------------------- --

#eval phrase 2
def THEOREM_V_1 : thm := keep "THEOREM_V_1" fun _ => (do
  -- OCaml builds the tactic right to left: the build-time rules run
  -- bottom-first, so their traces print in that order.
  let h5 ← rr (← ExceptT.mk [[&0 < x ==> abs x = x]])
  let h4 ← ar (← ExceptT.mk [[1 <= i + 1]])
  let h3 ← rr
    (← ExceptT.mk [[abs(x) <= a /\ abs(y) <= b ==> abs(x + y) <= a + b]])
  let h2 ← rr (← ExceptT.mk [[abs(x) <= a ==> abs(&1 + x) <= &1 + a]])
  let h1 ← tt (← ExceptT.mk [[(p /\ q ==> r) /\ p /\ q ==> p /\ q /\ r]])
  prove ([[!(V:real) (beta:num->real) (omega:num->real) (DSF:num->real->real)
    (B:num->real) (H:num->real) (v:num->real) (Tl:num->real) (Tp:num->real)
    (PSI:num->real#real->real) (psi:num->real#real->real)
    (taul:num->real->real) (taup:num->real->real).

        // Environmental assumptions including nondecreasing property
        &0 <= V /\
        (!i. i >= 0 ==> beta i > &0) /\
        (!i. i >= 1 ==> (!x. abs (x - DSF i x) <= omega i)) /\
        (!i. i >= 0 ==> abs (psi i (V,Tl i)) <= PSI i (V,abs(Tl i))) /\
        (!i x y. &0 <= x /\ x <= y ==> PSI i (V,x) <= PSI i (V,y)) /\

        (!u. taul 0 u = u) /\
        (!i u. taul (i + 1) u =
               beta (i + 1) * PSI i (u,taul i u) * taul i u + omega (i + 1)) /\
        (!i u. taup i u = (&1 + PSI i (u,taul i u)) * taul i u) /\

        // Computing recursively
        B 0 = &1 /\ H 0 = &0 /\ Tl 0 = V /\

        (!i. Tp i = (&1 + psi i (V,Tl i)) * Tl i) /\
        (!i. v (i + 1) = DSF (i + 1) (beta (i + 1) * Tp i)) /\
        (!i. B (i + 1) = beta (i + 1) * B i) /\
        (!i. H (i + 1) = H i + v (i + 1) / B (i + 1)) /\
        (!i. Tl (i + 1) = beta (i + 1) * Tl i - v (i + 1))

        // Conclude loop invariant and bounds.
        ==> (!i. V = H i + Tl i / B i) /\
            (!i. i >= 0 ==> abs(Tl i) <= taul i V) /\
            (!i. i >= 0 ==> abs(Tp i) <= taup i V)]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [GE, real_gt, real_gt, LE_0] THEN
    STRIP_TAC THEN

    -- Lemma: all the B_i are strictly positive, by induction

    SUBGOAL_THEN ([[!i:num. &0 < B i]]) ASSUME_TAC THENL
     [INDUCT_TAC THEN ASM_SIMP_TAC [REAL_LT_01, ADD1, REAL_LT_MUL],
      ALL_TAC] THEN

    -- Handle the tau_p clause first, assuming the other two

    MATCH_MP_TAC h1 THEN
    CONJ_TAC THENL
     [DISCH_THEN (STRIP_ASSUME_TAC o HolLight.GSYM) THEN
      ASM_REWRITE_TAC [REAL_ABS_MUL] THEN GEN_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC [REAL_ABS_POS] THEN
      MATCH_MP_TAC h2 THEN
      TRANS_TAC REAL_LE_TRANS ([[(PSI:num->real#real->real) i (V,abs(Tl i))]]) THEN
      ASM_SIMP_TAC [] THEN ASM_MESON_TAC [REAL_ABS_POS],
      ALL_TAC] THEN

    -- Start main induction and dispose of base case

    REWRITE_TAC [AND_FORALL_THM] THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC [] THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN

    -- Prove the step case of the loop invariant
    CONJ_TAC THENL
     [ASM_REWRITE_TAC [ADD1] THEN
      SUBGOAL_THEN ([[&0 < beta (i + 1) /\ &0 < B i]]) MP_TAC THENL
       [ASM_REWRITE_TAC [], CONV_TAC REAL_FIELD],
      ALL_TAC] THEN

    -- Massage the goal a little then chain through the inequalities

    FIRST_X_ASSUM (CONJUNCTS_THEN (ASSUME_TAC o HolLight.GSYM)) THEN
    REWRITE_TAC [ADD1] THEN

    TRANS_TAC REAL_LE_TRANS
     ([[abs(-- beta (i + 1)  * psi i (V:real,Tl i) * Tl i +
          (beta (i + 1) * Tp i - DSF (i + 1) (beta (i + 1) * Tp i)))]]) THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC2, ALL_TAC] THEN

    TRANS_TAC REAL_LE_TRANS
     ([[beta (i + 1) * abs(psi i (V:real,Tl i)) * abs(Tl i) + omega(i + 1)]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC h3 THEN
      ASM_SIMP_TAC [h4] THEN
      REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_NEG] THEN
      ASM_SIMP_TAC [h5, REAL_LE_REFL],
      ALL_TAC] THEN

    ASM_REWRITE_TAC [] THEN REWRITE_TAC [REAL_LE_RADD] THEN
    ASM_SIMP_TAC [REAL_LE_LMUL_EQ] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC [REAL_ABS_POS] THEN
    TRANS_TAC REAL_LE_TRANS ([[(PSI:num->real#real->real) i (V,abs(Tl i))]]) THEN
    ASM_SIMP_TAC [] THEN ASM_MESON_TAC [REAL_ABS_POS])
  : ExceptT String IO thm).run
#eval THEOREM_V_1

-- ------------------------------------------------------------------------- --
-- Restricted posynomials (definition V.2)                                   --
-- ------------------------------------------------------------------------- --

#eval phrase 3
def posynomial : thm := keep "posynomial" fun _ => (do
  nd ([[posynomial p <=>
  ?c (n:num->real) k.
        (!i. 1 <= i /\ i <= k ==> c i > &0 /\ integer(n i)) /\
        (!v. &0 < v ==> sum (1..k) (\i. c i * v rpow (n i)) = p v)]])
  : ExceptT String IO thm).run
#eval posynomial

#eval phrase 4
def POSYNOMIAL_0 : thm := keep "POSYNOMIAL_0" fun _ => (do
  prove ([[posynomial (\v. &0)]])
   (REWRITE_TAC [posynomial] THEN
    MAP_EVERY EXISTS_TAC [([[(\i. &1):num->real]]), ([[(\i. &0):num->real]]), ([[0]])] THEN
    REWRITE_TAC [SUM_CLAUSES_NUMSEG] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval POSYNOMIAL_0

#eval phrase 5
def POSYNOMIAL_1 : thm := keep "POSYNOMIAL_1" fun _ => (do
  prove ([[posynomial (\v. &1)]])
   (REWRITE_TAC [posynomial] THEN
    MAP_EVERY EXISTS_TAC [([[(\i. &1):num->real]]), ([[(\i. &0):num->real]]), ([[1]])] THEN
    REWRITE_TAC [INTEGER_CLOSED, SUM_SING_NUMSEG, RPOW_POW] THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval POSYNOMIAL_1

#eval phrase 6
def POSYNOMIAL_CMUL : thm := keep "POSYNOMIAL_CMUL" fun _ => (do
  prove ([[!p c. posynomial p /\ &0 < c ==> posynomial(\v. c * p(v))]])
   (REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    REWRITE_TAC [posynomial] THEN DISCH_THEN (X_CHOOSE_THEN ([[d:num->real]])
     (fun th => EXISTS_TAC ([[(\i. c * d i):num->real]]) THEN MP_TAC th)) THEN
    REPEAT (MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    SIMP_TAC [SUM_LMUL, (← HolLight.GSYM REAL_MUL_ASSOC)] THEN
    ASM_SIMP_TAC [real_gt, REAL_LT_MUL])
  : ExceptT String IO thm).run
#eval POSYNOMIAL_CMUL

#eval phrase 7
def POSYNOMIAL_CONST : thm := keep "POSYNOMIAL_CONST" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[&0 <= c <=> c = &0 \/ &0 < c]])
  prove ([[!c. &0 <= c ==> posynomial (\v. c)]])
   (REWRITE_TAC [h1] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [POSYNOMIAL_0] THEN
    GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.ABS_CONV) [(← HolLight.GSYM REAL_MUL_RID)] THEN
    MATCH_MP_TAC POSYNOMIAL_CMUL THEN
    ASM_REWRITE_TAC [POSYNOMIAL_1])
  : ExceptT String IO thm).run
#eval POSYNOMIAL_CONST

#eval phrase 8
def POSYNOMIAL_VPOWMUL : thm := keep "POSYNOMIAL_VPOWMUL" fun _ => (do
  prove ([[!p n. posynomial p /\ integer n ==> posynomial(\v. p(v) * v rpow n)]])
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    REWRITE_TAC [posynomial] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[c:num->real]]) THEN
    GEN_REWRITE_TAC HolLight.BINOP_CONV [SWAP_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[k:num]]) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[nn:num->real]]) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC ([[(\i. nn i + n):num->real]]) THEN
    ASM_SIMP_TAC [RPOW_ADD, REAL_MUL_ASSOC, SUM_RMUL, INTEGER_CLOSED])
  : ExceptT String IO thm).run
#eval POSYNOMIAL_VPOWMUL

#eval phrase 9
def POSYNOMIAL_VMUL : thm := keep "POSYNOMIAL_VMUL" fun _ => (do
  prove ([[!p. posynomial p ==> posynomial(\v. p(v) * v)]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[p:real->real]]), ([[&1:real]])] POSYNOMIAL_VPOWMUL) THEN
    ASM_REWRITE_TAC [RPOW_POW, REAL_POW_1, INTEGER_CLOSED])
  : ExceptT String IO thm).run
#eval POSYNOMIAL_VMUL

#eval phrase 10
def POSYNOMIAL_VDIV : thm := keep "POSYNOMIAL_VDIV" fun _ => (do
  prove ([[!p. posynomial p ==> posynomial(\v. p(v) / v)]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[p:real->real]]), ([[-- &1:real]])] POSYNOMIAL_VPOWMUL) THEN
    ASM_SIMP_TAC [RPOW_POW, real_div, RPOW_NEG, REAL_POW_1, INTEGER_CLOSED])
  : ExceptT String IO thm).run
#eval POSYNOMIAL_VDIV

#eval phrase 11
def POSYNOMIAL_V : thm := keep "POSYNOMIAL_V" fun _ => (do
  prove ([[posynomial(\v. v)]])
   (GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.ABS_CONV) [(← HolLight.GSYM REAL_MUL_LID)] THEN
    MATCH_MP_TAC POSYNOMIAL_VMUL THEN REWRITE_TAC [POSYNOMIAL_1])
  : ExceptT String IO thm).run
#eval POSYNOMIAL_V

#eval phrase 12
def POSYNOMIAL_ADD : thm := keep "POSYNOMIAL_ADD" fun _ => (do
  let h4 ← ar (← ExceptT.mk [[(1 <= i /\ i <= m + n) /\ ~(i <= m) <=>
    1 + m <= i /\ i <= n + m]])
  let h3 ← ar (← ExceptT.mk [[(1 <= i /\ i <= m + n) /\ i <= m <=> 1 <= i /\ i <= m]])
  let h2 ← ms [] (← ExceptT.mk [[(if p then f else g) (if p then x else y) =
    if p then f x else g y]])
  let h1 ← ar
    (← ExceptT.mk [[~(i:num <= m) /\ i <= m + n ==> 1 <= i - m /\ i - m <= n]])
  prove ([[!p q. posynomial p /\ posynomial q ==> posynomial(\v. p v + q v)]])
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [posynomial, IMP_CONJ, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [([[c1:num->real]]), ([[n1:num->real]]), ([[m:num]])] THEN
    DISCH_TAC THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [([[c2:num->real]]), ([[n2:num->real]]), ([[n:num]])] THEN
    DISCH_TAC THEN DISCH_TAC THEN
    EXISTS_TAC ([[\i. if i <= m then (c1:num->real) i else c2 (i - m)]]) THEN
    EXISTS_TAC ([[\i. if i <= m then (n1:num->real) i else n2 (i - m)]]) THEN
    EXISTS_TAC ([[m + n:num]]) THEN REWRITE_TAC [] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [] THEN
      ASM_MESON_TAC [h1],
      REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [COND_RAND] THEN
      ONCE_REWRITE_TAC [h2] THEN
      SIMP_TAC [SUM_CASES, FINITE_NUMSEG, IN_NUMSEG,
        h3,
        h4] THEN
      REWRITE_TAC [(← HolLight.GSYM numseg), SUM_OFFSET, ADD_SUB] THEN ASM_SIMP_TAC []])
  : ExceptT String IO thm).run
#eval POSYNOMIAL_ADD

#eval phrase 13
def POSYNOMIAL_SUM : thm := keep "POSYNOMIAL_SUM" fun _ => (do
  prove ([[!k:A->bool p.
        FINITE k /\ (!i. i IN k ==> posynomial(\v. p v i))
        ==> posynomial (\v. sum k (p v))]])
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [SUM_CLAUSES, POSYNOMIAL_0, POSYNOMIAL_ADD, FORALL_IN_INSERT,
              ETA_AX])
  : ExceptT String IO thm).run
#eval POSYNOMIAL_SUM

#eval phrase 14
def POSYNOMIAL_MUL : thm := keep "POSYNOMIAL_MUL" fun _ => (do
  let h1 ← rr
    (← ExceptT.mk [[(c * x) * (d * y):real = (c * d) * (x * y)]])
  prove ([[!p q. posynomial p /\ posynomial q ==> posynomial(\v. p v * q v)]])
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.BINOP_CONV)
     [(← HolLight.CONV_RULE (HolLight.RAND_CONV (HolLight.ONCE_DEPTH_CONV HolLight.SYM_CONV))
        (← HolLight.SPEC_ALL posynomial))] THEN
    STRIP_TAC THEN ASM_SIMP_TAC [posynomial] THEN
    REWRITE_TAC [(← HolLight.GSYM posynomial)] THEN
    SIMP_TAC [SUM_SUM_PRODUCT, FINITE_NUMSEG, REAL_MUL_SUM] THEN
    MATCH_MP_TAC POSYNOMIAL_SUM THEN
    SIMP_TAC [FINITE_PRODUCT_DEPENDENT, FINITE_NUMSEG, FORALL_IN_GSPEC] THEN
    REWRITE_TAC [IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [h1] THEN
    SIMP_TAC [posynomial, (← HolLight.GSYM RPOW_ADD)] THEN
    REWRITE_TAC [(← HolLight.GSYM posynomial)] THEN
    MATCH_MP_TAC POSYNOMIAL_VPOWMUL THEN ASM_SIMP_TAC [INTEGER_CLOSED] THEN
    ONCE_REWRITE_TAC [(← HolLight.GSYM REAL_MUL_RID)] THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [real_gt]) THEN
    MATCH_MP_TAC POSYNOMIAL_CMUL THEN
    ASM_SIMP_TAC [REAL_LT_MUL, POSYNOMIAL_1])
  : ExceptT String IO thm).run
#eval POSYNOMIAL_MUL

#eval phrase 15
def REAL_CONVEX_ON_POSYNOMIAL : thm := keep "REAL_CONVEX_ON_POSYNOMIAL" fun _ => (do
  let h2 ← ms [REAL_CONVEX_ON_EQ]
    (← ExceptT.mk [[is_realinterval s /\ f real_convex_on s
    ==> (!x. x IN s ==> f x = g x) ==> g real_convex_on s]])
  let h1 ← sr (← ExceptT.mk [[&0 < v <=> v IN {x | &0 < x}]])
  prove ([[!p. posynomial p ==> p real_convex_on {x | x > &0}]])
   (GEN_TAC THEN REWRITE_TAC [posynomial, LEFT_IMP_EXISTS_THM, real_gt] THEN
    MAP_EVERY X_GEN_TAC [([[c:num->real]]), ([[n:num->real]]), ([[m:num]])] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV)
     [h1] THEN
    MATCH_MP_TAC h2 THEN
    REWRITE_TAC [IS_REALINTERVAL_CLAUSES] THEN
    MATCH_MP_TAC REAL_CONVEX_ON_SUM THEN
    REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG] THEN
    X_GEN_TAC ([[i:num]]) THEN STRIP_TAC THEN MATCH_MP_TAC REAL_CONVEX_LMUL THEN
    ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_CONVEX_ON_RPOW_INTEGER THEN
    HolLight.ASM SET_TAC [])
  : ExceptT String IO thm).run
#eval REAL_CONVEX_ON_POSYNOMIAL

-- ------------------------------------------------------------------------- --
-- The corollary.                                                            --
-- ------------------------------------------------------------------------- --

#eval phrase 16
def COROLLARY_V_3 : thm := keep "COROLLARY_V_3" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[1 <= i + 1]])
  prove ([[!(V:real) (beta:num->real) (omega:num->real) (DSF:num->real->real)
    (B:num->real) (H:num->real) (v:num->real) (Tl:num->real) (Tp:num->real)
    (PSI:num->real#real->real) (psi:num->real#real->real)
    (taul:num->real->real) (taup:num->real->real).

        // Environmental assumptions including nondecreasing property
        &0 < V /\
        (!i. i >= 0 ==> beta i > &0) /\
        (!i. i >= 1 ==> (!x. abs (x - DSF i x) <= omega i)) /\
        (!i. i >= 0 ==> abs (psi i (V,Tl i)) <= PSI i (V,abs(Tl i))) /\
        (!i x y. &0 <= x /\ x <= y ==> PSI i (V,x) <= PSI i (V,y)) /\

        (!u. taul 0 u = u) /\
        (!i u. taul (i + 1) u =
               beta (i + 1) * PSI i (u,taul i u) * taul i u + omega (i + 1)) /\
        (!i u. taup i u = (&1 + PSI i (u,taul i u)) * taul i u) /\

        // Computing recursively
        B 0 = &1 /\ H 0 = &0 /\ Tl 0 = V /\

        (!i. Tp i = (&1 + psi i (V,Tl i)) * Tl i) /\
        (!i. v (i + 1) = DSF (i + 1) (beta (i + 1) * Tp i)) /\
        (!i. B (i + 1) = beta (i + 1) * B i) /\
        (!i. H (i + 1) = H i + v (i + 1) / B (i + 1)) /\
        (!i. Tl (i + 1) = beta (i + 1) * Tl i - v (i + 1)) /\

        // The extra posynomial-related assumption
        (!i p. i >= 0 /\ posynomial p
               ==> posynomial (\v. PSI i (v,p v)))

        // Hence conclude our bounds
        ==> !a b. real_interval[a,b] SUBSET {x | x > &0}
                  ==> !i u. u IN real_interval[a,b]
                            ==> taul i u <= max (taul i a) (taul i b) /\
                                taup i u <= max (taup i a) (taup i b)]])
   (REWRITE_TAC [real_gt, real_ge, GT, GE, LE_0] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o HolLight.MATCH_MP REAL_LT_IMP_LE) THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[!i:num. posynomial (taul i)]]) ASSUME_TAC THENL
     [INDUCT_TAC THEN GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.GSYM ETA_AX)] THEN
      ASM_REWRITE_TAC [ADD1, POSYNOMIAL_V] THEN
      MATCH_MP_TAC POSYNOMIAL_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC POSYNOMIAL_CMUL THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC POSYNOMIAL_MUL THEN ASM_SIMP_TAC [ETA_AX],
        MATCH_MP_TAC POSYNOMIAL_CONST THEN
        ASM_MESON_TAC [REAL_LE_TRANS, REAL_ABS_POS, h1]],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!i:num. posynomial (taup i)]]) ASSUME_TAC THENL
     [INDUCT_TAC THEN GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.GSYM ETA_AX)] THEN
      REWRITE_TAC [ADD1] THEN ONCE_ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC POSYNOMIAL_MUL THEN REWRITE_TAC [ETA_AX] THEN
      (CONJ_TAC THENL [ALL_TAC, FIRST_X_ASSUM MATCH_ACCEPT_TAC]) THEN
      MATCH_MP_TAC POSYNOMIAL_ADD THEN REWRITE_TAC [POSYNOMIAL_1] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [ETA_AX] THEN
      FIRST_X_ASSUM MATCH_ACCEPT_TAC,
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_CONVEX_LOWER_REAL_INTERVAL THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ_ALT]
          REAL_CONVEX_ON_SUBSET)) THEN
    REWRITE_TAC [(← HolLight.GSYM real_gt)] THEN MATCH_MP_TAC REAL_CONVEX_ON_POSYNOMIAL THEN
    FIRST_X_ASSUM MATCH_ACCEPT_TAC)
  : ExceptT String IO thm).run
#eval COROLLARY_V_3

-- ------------------------------------------------------------------------- --
-- Add the other clauses to the corollary.                                   --
-- ------------------------------------------------------------------------- --

#eval phrase 17
def FULL_COROLLARY : thm := keep "FULL_COROLLARY" fun _ => (do
  let h1 ← tt (← ExceptT.mk [[p /\ q /\ r /\ s <=> (p /\ q /\ r) /\ s]])
  prove ([[!(V:real) (beta:num->real) (omega:num->real) (DSF:num->real->real)
    (B:num->real) (H:num->real) (v:num->real) (Tl:num->real) (Tp:num->real)
    (PSI:num->real#real->real) (psi:num->real#real->real)
    (taul:num->real->real) (taup:num->real->real).

        // Not stated explicitly in the theorem itself but higher up.
        &0 < V /\

        // Environmental assumptions including nondecreasing property
        (!i. i >= 0 ==> beta i > &0) /\
        (!i. i >= 1 ==> (!x. abs (x - DSF i x) <= omega i)) /\
        (!i. i >= 0 ==> abs (psi i (V,Tl i)) <= PSI i (V,abs(Tl i))) /\
        (!i x y. &0 <= x /\ x <= y ==> PSI i (V,x) <= PSI i (V,y)) /\

        (!u. taul 0 u = u) /\
        (!i u. taul (i + 1) u =
               beta (i + 1) * PSI i (u,taul i u) * taul i u + omega (i + 1)) /\
        (!i u. taup i u = (&1 + PSI i (u,taul i u)) * taul i u) /\

        // Computing recursively
        B 0 = &1 /\ H 0 = &0 /\ Tl 0 = V /\

        (!i. Tp i = (&1 + psi i (V,Tl i)) * Tl i) /\
        (!i. v (i + 1) = DSF (i + 1) (beta (i + 1) * Tp i)) /\
        (!i. B (i + 1) = beta (i + 1) * B i) /\
        (!i. H (i + 1) = H i + v (i + 1) / B (i + 1)) /\
        (!i. Tl (i + 1) = beta (i + 1) * Tl i - v (i + 1)) /\

        // The extra posynomial-related assumption
        (!i p. i >= 0 /\ posynomial p
               ==> posynomial (\v. PSI i (v,p v)))

        // Hence conclude invariant and all bounds.
        ==> (!i. V = H i + Tl i / B i) /\
            (!i. abs(Tl i) <= taul i V) /\
            (!i. abs(Tp i) <= taup i V) /\
            (!a b. real_interval[a,b] SUBSET {x | x > &0}
                   ==> !i u. u IN real_interval[a,b]
                             ==> taul i u <= max (taul i a) (taul i b) /\
                                 taup i u <= max (taup i a) (taup i b))]])
   (REWRITE_TAC [real_gt, real_ge, GT, GE, LE_0] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o HolLight.MATCH_MP REAL_LT_IMP_LE) THEN
    ONCE_REWRITE_TAC [h1] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC (← HolLight.REWRITE_RULE [GE, LE_0] THEOREM_V_1) THEN
      MAP_EVERY EXISTS_TAC
       [([[beta:num->real]]), ([[omega:num->real]]), ([[DSF:num->real->real]]),
        ([[v:num->real]]), ([[PSI:num->real#real->real]]),
        ([[psi:num->real#real->real]])] THEN
      ASM_REWRITE_TAC [real_gt],

      MATCH_MP_TAC (← HolLight.REWRITE_RULE [real_gt] COROLLARY_V_3) THEN
      MAP_EVERY EXISTS_TAC
       [([[V:real]]), ([[beta:num->real]]), ([[omega:num->real]]), ([[DSF:num->real->real]]),
        ([[B:num->real]]), ([[H:num->real]]), ([[v:num->real]]), ([[Tl:num->real]]),
        ([[Tp:num->real]]),
        ([[PSI:num->real#real->real]]), ([[psi:num->real#real->real]])] THEN
      ASM_REWRITE_TAC [GE, LE_0]])
  : ExceptT String IO thm).run
#eval FULL_COROLLARY

-- ------------------------------------------------------------------------- --
-- Instantiations for division and square root.                              --
-- ------------------------------------------------------------------------- --

#eval phrase 18
def BOUND_THEOREM_DIV : thm := keep "BOUND_THEOREM_DIV" fun _ => (do
  let h5 ← rr
    (← ExceptT.mk [[&1 / &4 <= X / Y /\ X / Y <= &1 <=>
    &1 / &2 * inv(&2) <= X * inv Y /\ X * inv Y <= &1 * inv(&1)]])
  let h4 ← rr (← ExceptT.mk [[&0 < b ==> abs b = b]])
  let h3 ← rr (← ExceptT.mk [[a / b * c:real = a * c / b]])
  let h2 ← prfe num_RECURSION
    (← ExceptT.mk [[Tl 0 :real = X / Y /\
    !i. Tl (SUC i) = beta (i + 1) * Tl i - v (i + 1)]])
  let h1 ← prfe num_RECURSION
    (← ExceptT.mk [[(!u:real. taul 0 u = u) /\
    (!i u. taul (SUC i) u =
    beta (i + 1) * PSI i (u,taul i u) * taul i u + omega (i + 1))]])
  prove ([[!beta Sigma omega B DSF H R Tp X Y g e v.
        (!i. i >= 0 ==> beta i > &0) /\
        &1 / &2 <= X /\ X < &1 /\
        &1 <= Y /\ Y < &2 /\
        (!y. &1 <= y /\ y < &2
             ==> g y = (&1 + e y) / y /\ abs(e y) <= Sigma) /\
        (!i. i >= 1 ==> (!x. abs (x - DSF i x) <= omega i)) /\
        B 0 = &1 /\ H 0 = &0 /\ R 0 = X /\
        (!i. Tp i = g(Y) * R i) /\
        (!i. v (i + 1) = DSF (i + 1) (beta (i + 1) * Tp i)) /\
        (!i. B (i + 1) = beta (i + 1) * B i) /\
        (!i. H (i + 1) = H i + v (i + 1) / B (i + 1)) /\
        (!i. R (i + 1) = beta (i + 1) * R i -  v(i + 1) * Y)
        ==> ?taul. (!u. taul 0 u = u) /\
                   (!i u. taul (i + 1) u =
                          beta (i + 1) * Sigma * taul i u + omega (i + 1)) /\
                   (!i. abs(X / Y - H i)
                        <= max (taul i (&1 / &4)) (taul i (&1)) / B i)]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [GE, LE_0, real_gt] THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[&0 <= Sigma]]) ASSUME_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[&1:real]])) THEN REAL_ARITH_TAC2,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!i. &0 < (B:num->real) i]]) ASSUME_TAC THENL
     [INDUCT_TAC THEN ASM_SIMP_TAC [REAL_LT_MUL, ADD1, REAL_LT_01], ALL_TAC] THEN
    SUBGOAL_THEN ([[&0 < X /\ &0 < Y]]) STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    SUBGOAL_THEN ([[&0 < X / Y]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [REAL_LT_DIV], ALL_TAC] THEN
    MAP_EVERY ABBREV_TAC
     [([[PSI:num->real#real->real = \i (u,t). Sigma]]),
      ([[psi:num->real#real->real = \i (u,t). e(Y:real)]])] THEN
    X_CHOOSE_THEN ([[taul:num->real->real]])
      (STRIP_ASSUME_TAC o HolLight.REWRITE_RULE [ADD1]) h1 THEN
    X_CHOOSE_THEN ([[Tl:num->real]])
      (STRIP_ASSUME_TAC o HolLight.REWRITE_RULE [ADD1]) h2 THEN
    ABBREV_TAC
     ([[taup:num->real->real = \i u. (&1 + PSI i (u,taul i u)) * taul i u]]) THEN
    MP_TAC (← HolLight.ISPECL
     [([[X / Y:real]]),
      ([[beta:num->real]]),
      ([[omega:num->real]]),
      ([[DSF:num->real->real]]),
      ([[B:num->real]]),
      ([[H:num->real]]),
      ([[v:num->real]]),
      ([[Tl:num->real]]),
      ([[Tp:num->real]]),
      ([[PSI:num->real#real->real]]),
      ([[psi:num->real#real->real]]),
      ([[taul:num->real->real]]),
      ([[taup:num->real->real]])]
      FULL_COROLLARY) THEN
    REWRITE_TAC [GE, LE_0, real_gt] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_ACCEPT_TAC,
        FIRST_X_ASSUM MATCH_ACCEPT_TAC,
        FIRST_X_ASSUM MATCH_ACCEPT_TAC,
        X_GEN_TAC ([[i:num]]) THEN MAP_EVERY EXPAND_TAC ["PSI", "psi"] THEN
        REWRITE_TAC [] THEN ASM_SIMP_TAC [] THEN HolCore.Tactics.NO_TAC,
        EXPAND_TAC "PSI" THEN REWRITE_TAC [REAL_LE_REFL] THEN HolCore.Tactics.NO_TAC,
        FIRST_X_ASSUM MATCH_ACCEPT_TAC,
        ASM_REWRITE_TAC [] THEN HolCore.Tactics.NO_TAC,
        EXPAND_TAC "taup" THEN REWRITE_TAC [] THEN HolCore.Tactics.NO_TAC,
        FIRST_X_ASSUM MATCH_ACCEPT_TAC,
        FIRST_X_ASSUM MATCH_ACCEPT_TAC,
        FIRST_X_ASSUM MATCH_ACCEPT_TAC,
        X_GEN_TAC ([[i:num]]) THEN
        FIRST_X_ASSUM (fun th => GEN_REWRITE_TAC HolLight.LAND_CONV [th]) THEN
        EXPAND_TAC "psi" THEN REWRITE_TAC [] THEN ASM_SIMP_TAC [] THEN
        REWRITE_TAC [h3] THEN
        AP_TERM_TAC THEN ASM_SIMP_TAC [REAL_EQ_LDIV_EQ] THEN
        SPEC_TAC (([[i:num]]), ([[j:num]])) THEN
        INDUCT_TAC THEN ASM_SIMP_TAC [ADD1, REAL_DIV_RMUL, REAL_LT_IMP_NZ] THEN
        REAL_ARITH_TAC2,
        FIRST_X_ASSUM MATCH_ACCEPT_TAC,
        FIRST_X_ASSUM MATCH_ACCEPT_TAC,
        FIRST_X_ASSUM MATCH_ACCEPT_TAC,
        FIRST_X_ASSUM MATCH_ACCEPT_TAC,
        EXPAND_TAC "PSI" THEN REWRITE_TAC [] THEN
        ASM_SIMP_TAC [POSYNOMIAL_CONST] THEN HolCore.Tactics.NO_TAC],
      STRIP_TAC THEN EXISTS_TAC ([[taul:num->real->real]]) THEN
      ASM_REWRITE_TAC [REAL_ADD_SUB] THEN CONJ_TAC THENL
       [EXPAND_TAC "PSI" THEN REWRITE_TAC [], ALL_TAC] THEN
      ASM_SIMP_TAC [REAL_ABS_DIV, REAL_LE_DIV2_EQ,
                   h4] THEN
      X_GEN_TAC ([[i:num]]) THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [([[&1 / &4]]), ([[&1]])]) THEN
      REWRITE_TAC [SUBSET, IN_REAL_INTERVAL, IN_ELIM_THM] THEN
      ANTS_TAC THENL [REAL_ARITH_TAC2, ALL_TAC] THEN
      DISCH_THEN (MP_TAC o HolLight.SPECL [([[i:num]]), ([[X / Y:real]])]) THEN
      ANTS_TAC THENL [ALL_TAC, ASM_MESON_TAC [REAL_LE_TRANS]] THEN
      REWRITE_TAC [h5] THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THEN
      TRY (MATCH_MP_TAC REAL_LE_INV2) THEN
      REWRITE_TAC [REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC])
  : ExceptT String IO thm).run
#eval BOUND_THEOREM_DIV

#eval phrase 19
def BOUND_THEOREM_SQRT : thm := keep "BOUND_THEOREM_SQRT" fun _ => (do
  let h17 ← rr (← ExceptT.mk [[&0 < b ==> abs b = b]])
  let h16 ← rr
    (← ExceptT.mk [[&0 < inv(&2) * x <=> &0 < x]])
  let h15 ← rr
    (← ExceptT.mk [[x * inv(&2) * inv y * z = (inv(&2) * z) * x / y]])
  let h14 ← rr
    (← ExceptT.mk [[&0 <= s ==> &0 <= &1 + s]])
  let h13 ← rr
    (← ExceptT.mk [[(x + h) / &2 * (x - h) = (x pow 2 - h pow 2) / &2]])
  let h12 ← rf
    (← ExceptT.mk [[!b. &0 < b /\ x / b = y / &2 * z / b ==> x = y / &2 * z]])
  let h11 ← rr (← ExceptT.mk [[s - (s - h) / &2 = (s + h) / &2]])
  let h10 ← rf
    (← ExceptT.mk [[&0 < b /\ &0 < s /\ r = (s - t / b / &2) * t
    ==> inv s * r = (&1 - t * inv(&2 * s * b)) * t]])
  let h9 ← rr (← ExceptT.mk [[&1 + x - &1 = x]])
  let h8 ← rr
    (← ExceptT.mk [[&2 * c / s * x / &2 = c * x / s]])
  let h7 ← rr (← ExceptT.mk [[&0 < &2 * x <=> &0 < x]])
  let h6 ← rr (← ExceptT.mk [[&0 <= s ==> &0 < &1 + s]])
  let h5 ← rr (← ExceptT.mk [[&0 < x ==> abs(&2 * x) = &2 * x]])
  let h4 ← rr (← ExceptT.mk [[abs x <= a ==> abs(&1 + x) <= &1 + a]])
  let h3 ← rr
    (← ExceptT.mk [[abs x <= a /\ abs((&1 + x) * y) <= b
    ==> abs((&1 + x) * (&1 - y) - &1) <= a + b]])
  let h2 ← prfe num_RECURSION
    (← ExceptT.mk [[Tl 0 = sqrt(X) /\
    !i. Tl (SUC i) = beta (i + 1) * Tl i - v (i + 1)]])
  let h1 ← prfe num_RECURSION
    (← ExceptT.mk [[(!u:real. taul 0 u = u) /\
    (!i u. taul (SUC i) u =
    beta (i + 1) * PSI i (u,taul i u) * taul i u + omega (i + 1))]])
  prove ([[!beta Sigma omega B DSF H R Tp X g e v.
        (!i. i >= 0 ==> beta i > &0) /\
        &1 / &4 <= X /\ X < &1 /\
        (!x. &1 / &4 <= x /\ x < &1
             ==> g x = (&1 + e x) / sqrt x /\
                 abs(e x) <= Sigma) /\
        (!i. i >= 1 ==> (!x. abs (x - DSF i x) <= omega i)) /\
        B 0 = &1 /\ H 0 = &0 /\ R 0 = X / &2 /\
        (!i. Tp i = (if i = 0 then &2 else &1) * g(X) * R i) /\
        (!i. v (i + 1) = DSF (i + 1) (beta (i + 1) * Tp i)) /\
        (!i. B (i + 1) = beta (i + 1) * B i) /\
        (!i. H (i + 1) = H i + v (i + 1) / B (i + 1)) /\
        (!i. R (i + 1) =
             beta (i + 1) * R i -  v(i + 1) * (H(i + 1) + H i) / &2)
        ==> ?taul.
                  (!u. taul 0 u = u) /\
                  (!i u. taul (i + 1) u =
                         beta (i + 1) *
                         (if i = 0 then Sigma
                          else Sigma + (&1 + Sigma) * taul i u / (&2 * u * B i))
                          * taul i u +
                         omega (i + 1)) /\
                  (!i. abs(sqrt X - H i)
                       <= max (taul i (&1 / &2)) (taul i (&1)) / B i)]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [GE, LE_0, real_gt] THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[&0 <= Sigma]]) ASSUME_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[&1 / &2]])) THEN REAL_ARITH_TAC2,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!i. &0 < (B:num->real) i]]) ASSUME_TAC THENL
     [INDUCT_TAC THEN ASM_SIMP_TAC [REAL_LT_MUL, ADD1, REAL_LT_01], ALL_TAC] THEN
    SUBGOAL_THEN ([[&0 < X]]) ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    SUBGOAL_THEN ([[&0 < sqrt X]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [SQRT_POS_LT], ALL_TAC] THEN
    MAP_EVERY ABBREV_TAC
     [([[PSI:num->real#real->real = \i (u,t).
          if i = 0 then Sigma
          else Sigma + (&1 + Sigma) * t / (&2 * u * B i)]]),
      ([[psi:num->real#real->real = \i (u,t).
          if i = 0 then e(X)
          else (&1 + e(X:real)) * (&1 - t / (&2 * u * B i)) - &1]])] THEN
    X_CHOOSE_THEN ([[taul:num->real->real]])
      (STRIP_ASSUME_TAC o HolLight.REWRITE_RULE [ADD1]) h1 THEN
    X_CHOOSE_THEN ([[Tl:num->real]])
      (STRIP_ASSUME_TAC o HolLight.REWRITE_RULE [ADD1]) h2 THEN
    ABBREV_TAC
     ([[taup:num->real->real = \i u. (&1 + PSI i (u,taul i u)) * taul i u]]) THEN
    MP_TAC (← HolLight.ISPECL
     [([[sqrt X]]),
      ([[beta:num->real]]),
      ([[omega:num->real]]),
      ([[DSF:num->real->real]]),
      ([[B:num->real]]),
      ([[H:num->real]]),
      ([[v:num->real]]),
      ([[Tl:num->real]]),
      ([[Tp:num->real]]),
      ([[PSI:num->real#real->real]]),
      ([[psi:num->real#real->real]]),
      ([[taul:num->real->real]]),
      ([[taup:num->real->real]])]
      FULL_COROLLARY) THEN
    REWRITE_TAC [GE, LE_0, real_gt] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_ACCEPT_TAC,
        FIRST_X_ASSUM MATCH_ACCEPT_TAC,
        FIRST_X_ASSUM MATCH_ACCEPT_TAC,
        X_GEN_TAC ([[i:num]]) THEN MAP_EVERY EXPAND_TAC ["PSI", "psi"] THEN
        REWRITE_TAC [] THEN ASM_CASES_TAC ([[i = 0]]) THEN ASM_SIMP_TAC [] THEN
        MATCH_MP_TAC h3 THEN
        ASM_SIMP_TAC [REAL_ABS_MUL] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC [REAL_ABS_POS] THEN
        ASM_SIMP_TAC [h4] THEN
        REWRITE_TAC [REAL_ABS_DIV] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        AP_TERM_TAC THEN
        MATCH_MP_TAC h5 THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC [],
        MAP_EVERY X_GEN_TAC [([[i:num]]), ([[x:real]]), ([[y:real]])] THEN STRIP_TAC THEN
        EXPAND_TAC "PSI" THEN REWRITE_TAC [] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_LE_REFL, REAL_LE_LADD] THEN
        ASM_SIMP_TAC [REAL_LE_LADD, REAL_LE_LMUL_EQ, REAL_LE_DIV2_EQ,
                     h6, REAL_LT_MUL,
                     h7] THEN
        REAL_ARITH_TAC2,
        FIRST_X_ASSUM MATCH_ACCEPT_TAC,
        ASM_REWRITE_TAC [] THEN HolCore.Tactics.NO_TAC,
        EXPAND_TAC "taup" THEN REWRITE_TAC [] THEN HolCore.Tactics.NO_TAC,
        FIRST_X_ASSUM MATCH_ACCEPT_TAC,
        FIRST_X_ASSUM MATCH_ACCEPT_TAC,
        FIRST_X_ASSUM MATCH_ACCEPT_TAC,
        X_GEN_TAC ([[i:num]]) THEN
        FIRST_X_ASSUM (fun th => GEN_REWRITE_TAC HolLight.LAND_CONV [th]) THEN
        EXPAND_TAC "psi" THEN REWRITE_TAC [] THEN
        ASM_CASES_TAC ([[i = 0]]) THEN ASM_REWRITE_TAC [] THENL
         [ASM_SIMP_TAC [REAL_DIV_SQRT, REAL_LT_IMP_LE, h8],
          ALL_TAC] THEN
        REWRITE_TAC [REAL_MUL_LID, h9] THEN
        ASM_SIMP_TAC [] THEN REWRITE_TAC [real_div, (← HolLight.GSYM REAL_MUL_ASSOC)] THEN
        AP_TERM_TAC THEN MATCH_MP_TAC h10 THEN
        ASM_REWRITE_TAC [] THEN
        SUBGOAL_THEN ([[!j:num. Tl j / B j = sqrt X - H j]])
        ASSUME_TAC THENL
         [INDUCT_TAC THEN ASM_REWRITE_TAC [REAL_SUB_RZERO, REAL_DIV_1, ADD1] THEN
          UNDISCH_TAC ([[Tl(j:num) / B j = sqrt X - H j]]) THEN
          SUBGOAL_THEN ([[&0 < beta(j + 1) /\ &0 < B j]]) MP_TAC THENL
           [ASM_REWRITE_TAC [], CONV_TAC REAL_FIELD],
          ASM_REWRITE_TAC [h11]] THEN
        MATCH_MP_TAC h12 THEN
        EXISTS_TAC ([[(B:num->real) i]]) THEN ASM_REWRITE_TAC [h13] THEN
        ASM_SIMP_TAC [SQRT_POW_2, REAL_LT_IMP_LE] THEN
        ASM_SIMP_TAC [REAL_EQ_LDIV_EQ] THEN
        SPEC_TAC (([[i:num]]), ([[j:num]])) THEN
        MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
         [ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC2, REWRITE_TAC [ADD1]] THEN
        ONCE_REWRITE_TAC [(← HolLight.ASSUME
        ([[!i. R (i + 1) =
             beta (i + 1) * R i - v (i + 1) * (H (i + 1) + H i) / &2]]))] THEN
        X_GEN_TAC ([[j:num]]) THEN SIMP_TAC [] THEN
        REWRITE_TAC [(← HolLight.ASSUME
         ([[!i. H (i + 1):real = H i + v (i + 1) / B (i + 1)]]))] THEN
        REWRITE_TAC [(← HolLight.ASSUME ([[!i. B (i + 1):real = beta (i + 1) * B i]]))] THEN
        SUBGOAL_THEN ([[&0 < beta(j + 1) /\ &0 < B j]]) MP_TAC THENL
         [ASM_REWRITE_TAC [], CONV_TAC REAL_FIELD],
        FIRST_X_ASSUM MATCH_ACCEPT_TAC,
        FIRST_X_ASSUM MATCH_ACCEPT_TAC,
        FIRST_X_ASSUM MATCH_ACCEPT_TAC,
        FIRST_X_ASSUM MATCH_ACCEPT_TAC,
        MAP_EVERY X_GEN_TAC [([[i:num]]), ([[p:real->real]])] THEN DISCH_TAC THEN
        EXPAND_TAC "PSI" THEN REWRITE_TAC [] THEN
        ASM_CASES_TAC ([[i = 0]]) THEN ASM_SIMP_TAC [POSYNOMIAL_CONST] THEN
        MATCH_MP_TAC POSYNOMIAL_ADD THEN
        ASM_SIMP_TAC [POSYNOMIAL_CONST] THEN
        MATCH_MP_TAC POSYNOMIAL_MUL THEN
        ASM_SIMP_TAC [POSYNOMIAL_CONST, h14] THEN
        REWRITE_TAC [real_div, REAL_INV_MUL] THEN REWRITE_TAC [h15] THEN
        MATCH_MP_TAC POSYNOMIAL_CMUL THEN
        ASM_SIMP_TAC [REAL_LT_INV_EQ, h16] THEN
        MATCH_MP_TAC POSYNOMIAL_VDIV THEN ASM_REWRITE_TAC []],
      STRIP_TAC THEN EXISTS_TAC ([[taul:num->real->real]]) THEN
      ASM_REWRITE_TAC [REAL_ADD_SUB] THEN CONJ_TAC THENL
       [EXPAND_TAC "PSI" THEN REWRITE_TAC [], ALL_TAC] THEN
      ASM_SIMP_TAC [REAL_ABS_DIV, REAL_LE_DIV2_EQ,
                   h17] THEN
      X_GEN_TAC ([[i:num]]) THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [([[&1 / &2]]), ([[&1]])]) THEN
      REWRITE_TAC [SUBSET, IN_REAL_INTERVAL, IN_ELIM_THM] THEN
      ANTS_TAC THENL [REAL_ARITH_TAC2, ALL_TAC] THEN
      DISCH_THEN (MP_TAC o HolLight.SPECL [([[i:num]]), ([[sqrt X]])]) THEN
      ANTS_TAC THENL [ALL_TAC, ASM_MESON_TAC [REAL_LE_TRANS]] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RSQRT, MATCH_MP_TAC REAL_LE_LSQRT] THEN
      ASM_REAL_ARITH_TAC])
  : ExceptT String IO thm).run
#eval BOUND_THEOREM_SQRT

-- ------------------------------------------------------------------------- --
-- Automatically instantiate the theorems and derive error bounds.           --
--                                                                           --
-- th = theorem to instantiate (BOUND_THEOREM_DIV or BOUND_THEOREM_SQRT)     --
-- beta, sigma, omega = HOL term instantiations for corresponding parameters --
-- n = number of iterations: result will provide bounds for H_0, ..., H_n    --
-- d = number of fraction digits in resulting digit bounds                   --
-- ------------------------------------------------------------------------- --

#eval phrase 20
/-- The `pth` of BOUNDS_INSTATIATION, proved once when the phrase is run. -/
private def BOUNDS_INSTATIATION_pth : thm := keep "BOUNDS_INSTATIATION_pth" fun _ => (do
  prove ([[x <= a / b ==> &0 <= b ==> !a'. a <= a' ==> x <= a' / b]])
   (REPEAT STRIP_TAC THEN TRANS_TAC REAL_LE_TRANS ([[a / b:real]]) THEN
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [real_div] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC [REAL_LE_INV_EQ])
  : ExceptT String IO thm).run

/-- The local `calc` of BOUNDS_INSTATIATION. -/
private partial def BOUNDS_INSTATIATION_calc (rews : List thm) (thb ths : thm) (n : Int) :
    ExceptT String IO (List thm) := do
  if n = 0 then pure [thb] else
  let oths ← BOUNDS_INSTATIATION_calc rews thb ths (n - 1)
  let th1 ← HolLight.CONV_RULE NUM_REDUCE_CONV
    (← HolLight.SPEC (← ec (mk_small_numeral (n - 1))) ths)
  let th2 ← HolLight.GEN_REWRITE_RULE HolLight.TOP_DEPTH_CONV ((← ec (HolCore.Lib.hd oths)) :: rews) th1
  let th3 ← HolLight.CONV_RULE REAL_RAT_REDUCE_CONV th2
  pure (th3 :: oths)

/-- OCaml's `=` on theorems. -/
private def thmEq (a b : thm) : Bool := dest_thm a == dest_thm b

/-- `BOUNDS_INSTATIATION th beta sigma omega n d`. -/
def BOUNDS_INSTATIATION (th : thm) (beta sigma omega : term) (n d : Int) :
    ExceptT String IO thm := do
  let pth := BOUNDS_INSTATIATION_pth
  let calc_ := BOUNDS_INSTATIATION_calc
  let ith ← HolLight.BETA_RULE (← HolLight.SPECL [beta, sigma, omega] th)
  let (avs, itm) := HolCore.Basics.strip_forall (concl ith)
  let hth ← HolLight.ASSUME (← ec (HolCore.Kernel.rand (← ec (HolCore.Equal.lhand itm))))
  let eth ← HolLight.MP (← HolLight.SPECL avs ith)
    (← HolLight.CONJ (← rr (← ec (HolCore.Equal.lhand (← ec (HolCore.Equal.lhand itm))))) hth)
  let (ev, ebod) ← ec (HolCore.Basics.dest_exists (concl eth))
  let [th0, th1, bth] := HolLight.CONJUNCTS (← HolLight.ASSUME ebod)
    | throw "BOUNDS_INSTATIATION: match failure"
  let hths := HolLight.CONJUNCTS hth
  let isDiv := thmEq th BOUND_THEOREM_DIV
  let some th_b := hths[if isDiv then 6 else 4]? | throw "el"
  let some th_s := hths[if isDiv then 11 else 9]? | throw "el"
  let bths ← calc_ [] th_b th_s n
  let lo : term := if isDiv then ([[&1 / &4]]) else ([[&1 / &2]])
  let tths_lo ←
    calc_ bths (← HolLight.SPEC lo th0)
      (← HolLight.SPEC lo (← HolLight.GEN_REWRITE_RULE HolCore.Lib.I [SWAP_FORALL_THM] th1)) n
  let tths_hi ←
    calc_ bths (← HolLight.SPEC ([[&1:real]]) th0)
      (← HolLight.SPEC ([[&1:real]])
        (← HolLight.GEN_REWRITE_RULE HolCore.Lib.I [SWAP_FORALL_THM] th1)) n
  let aths ← (List.range (n.toNat + 1)).mapM fun (k : Nat) => do
    let th1 ← HolLight.SPEC (← ec (mk_small_numeral (k : Int))) bth
    let th2 ← HolLight.REWRITE_RULE (tths_lo ++ tths_hi) th1
    HolLight.CONV_RULE REAL_RAT_REDUCE_CONV th2
  let weaken (th : thm) : ExceptT String IO thm := do
    let th1 ← HolLight.MATCH_MP pth th
    let th2 ← ExceptT.mk
      (HolLight.GEN_REWRITE_CONV HolLight.RAND_CONV bths (← ec (HolCore.Equal.lhand (concl th1))))
    let th3 ← HolLight.CONV_RULE (HolLight.RAND_CONV REAL_RAT_REDUCE_CONV) th2
    let th4 ← HolLight.MP th1 (← HolLight.EQT_ELIM th3)
    let r ← ec (rat_of_term
      (← ec (HolCore.Equal.lhand (← ec (HolCore.Equal.lhand (← ec (HolCore.Basics.dest_forall (concl th4))).2)))))
    let yy := HolCore.Lib.pow10 d
    let xx : Rat := ((yy * r).ceil : Int)
    let th5 ← HolLight.SPECL [← ec (mk_numeral xx), ← ec (mk_numeral yy)] DECIMAL
    let th6 ← HolLight.SPEC (← ec (HolCore.Equal.lhand (concl th5))) th4
    HolLight.MP th6
      (← HolLight.EQT_ELIM (← ExceptT.mk (REAL_RAT_REDUCE_CONV (← ec (HolCore.Equal.lhand (concl th6))))))
  let ath ← HolLight.end_itlist HolLight.CONJ (← aths.mapM weaken)
  HolLight.GENL avs (← HolLight.DISCH_ALL (← HolLight.CHOOSE (ev, eth) ath))

#eval (do forceValue BOUNDS_INSTATIATION_pth; IO.println "<fun>" : IO Unit)

-- ------------------------------------------------------------------------- --
-- A slightly larger / more complicated example as a stress-test.            --
-- ------------------------------------------------------------------------- --

#eval phrase 21
def stress_test : thm := keep "stress_test" fun _ => (do
  BOUNDS_INSTATIATION BOUND_THEOREM_SQRT
   ([[(\i. if i = 2 then &32 else if i = 5 then &64 else &128):num->real]])
   ([[inv(&2 pow 8):real]])
   ([[(\i. if i = 0 then &1 / &2 else &9 / &16):num->real]])
   7 6
  : ExceptT String IO thm).run
#eval stress_test

-- ------------------------------------------------------------------------- --
-- The actual examples in the table.                                         --
-- ------------------------------------------------------------------------- --

#eval phrase 22
def TABLE_PART_1 : thm := keep "TABLE_PART_1" fun _ => (do
  BOUNDS_INSTATIATION BOUND_THEOREM_DIV
   ([[(\i. &128):num->real]])
   ([[inv(&2 pow 9):real]])
   ([[(\i. &5 / &8):num->real]])
   4 4
  : ExceptT String IO thm).run
#eval TABLE_PART_1

#eval phrase 23
def TABLE_PART_2 : thm := keep "TABLE_PART_2" fun _ => (do
  BOUNDS_INSTATIATION BOUND_THEOREM_DIV
   ([[(\i. if i = 2 then &32 else &128):num->real]])
   ([[inv(&2 pow 9):real]])
   ([[(\i. &5 / &8):num->real]])
   4 4
  : ExceptT String IO thm).run
#eval TABLE_PART_2

#eval phrase 24
def TABLE_PART_3 : thm := keep "TABLE_PART_3" fun _ => (do
  BOUNDS_INSTATIATION BOUND_THEOREM_SQRT
   ([[(\i. &128):num->real]])
   ([[inv(&2 pow 9):real]])
   ([[(\i. &5 / &8):num->real]])
   4 4
  : ExceptT String IO thm).run
#eval TABLE_PART_3

#eval phrase 25
def TABLE_PART_4 : thm := keep "TABLE_PART_4" fun _ => (do
  BOUNDS_INSTATIATION BOUND_THEOREM_SQRT
   ([[(\i. if i = 2 then &32 else &128):num->real]])
   ([[inv(&2 pow 9):real]])
   ([[(\i. &5 / &8):num->real]])
   4 4
  : ExceptT String IO thm).run
#eval TABLE_PART_4

end HolExamples.DigitSerialMethods
