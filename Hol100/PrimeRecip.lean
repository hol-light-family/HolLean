/- File: Hol100/PrimeRecip.lean
Translation of HOL Light's 100/primerecip.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionLibrary.Prime
import SessionLibrary.Products
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Prime SessionLibrary.Products
namespace Hol100.PrimeRecip

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)

/- ========================================================================= -/
/- Divergence of the series of reciprocals of the primes, by Erdos's         -/
/- counting argument.                                                        -/
/-                                                                           -/
/- * SMOOTH_SQUARE_DECOMPOSITION: an n > 0 whose prime factors all lie in a  -/
/-   finite set s of primes is u^2 times a product of distinct elements of   -/
/-   s (u collects the even parts of the indices).                           -/
/- * PRIMERECIP_BLOCK: for every m the primes p in (m, 4^(m + 1)] have       -/
/-   sum 1/p >= 1/2.  With N = 4^(m + 1), the n <= N whose prime factors     -/
/-   are all <= m are u^2 times a product of a set of primes <= m with       -/
/-   u <= 2^(m + 1), so there are at most 2^(m + 1) 2^m = N/2 of them;       -/
/-   every other n <= N is a multiple of some prime p in (m, N], and there   -/
/-   are N DIV p <= N / p such multiples (CARD_MULTIPLES_NUMSEG).            -/
/- * PRIMERECIP_UNBOUNDED: the partial sums sum {1/p | p <= n} are           -/
/-   unbounded, so they do not converge (PRIMERECIP_DIVERGES,                -/
/-   PRIMERECIP_DIVERGES_NUMSEG; convergence written out as in               -/
/-   100/divharmonic.ml).                                                    -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Library/prime.ml";;
#eval SessionLibrary.Prime.ensurePrime

#eval phrase 2
-- needs "Library/products.ml";;
#eval SessionLibrary.Products.ensureProducts

#eval phrase 3
#eval Session.prioritize_num

/- ------------------------------------------------------------------------- -/
/- Smooth numbers and multiples.                                             -/
/- ------------------------------------------------------------------------- -/

#eval phrase 4
def SMOOTH_SQUARE_DECOMPOSITION : thm := keep "SMOOTH_SQUARE_DECOMPOSITION" fun _ => (do
  prove ([[!s n. FINITE s /\ (!p. p IN s ==> prime p) /\ ~(n = 0) /\
         (!p. prime p /\ p divides n ==> p IN s)
         ==> n = nproduct s (\p. p EXP (index p n DIV 2)) EXP 2 *
                 nproduct {p | p IN s /\ ODD(index p n)} (\p. p)]])
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.SYM (← HolLight.MATCH_MP PRIME_FACTORIZATION_ALT th))])) THEN
    SUBGOAL_THEN ([[nproduct {p | prime p} (\p. p EXP index p n) =
    nproduct s (\p. p EXP index p n)]]) SUBST1_TAC THENL
     [MATCH_MP_TAC NPRODUCT_SUPERSET THEN
      REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN
      CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      X_GEN_TAC ([[p:num]]) THEN STRIP_TAC THEN
      REWRITE_TAC [EXP_EQ_1, INDEX_EQ_0] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    ASM_SIMP_TAC [EXP_2, NPRODUCT_RESTRICT_SET, (← HolLight.GSYM NPRODUCT_MUL)] THEN
    MATCH_MP_TAC NPRODUCT_EQ THEN X_GEN_TAC ([[p:num]]) THEN DISCH_TAC THEN
    REWRITE_TAC [] THEN SPEC_TAC (([[index p n]]), ([[e:num]])) THEN GEN_TAC THEN
    DISJ_CASES_TAC (← HolLight.SPEC ([[e:num]]) EVEN_OR_ODD) THENL
     [FIRST_X_ASSUM (X_CHOOSE_THEN ([[k:num]]) SUBST1_TAC o
        HolLight.REWRITE_RULE [EVEN_EXISTS]) THEN
      REWRITE_TAC [(← HolLight.GSYM NOT_EVEN), EVEN_DOUBLE] THEN
      SIMP_TAC [DIV_MULT, ARITH_EQ] THEN
      REWRITE_TAC [MULT_2, EXP_ADD, MULT_CLAUSES],
      FIRST_X_ASSUM (X_CHOOSE_THEN ([[k:num]]) SUBST1_TAC o
        HolLight.REWRITE_RULE [ODD_EXISTS]) THEN
      REWRITE_TAC [ODD, (← HolLight.GSYM NOT_EVEN), EVEN_DOUBLE] THEN
      SUBGOAL_THEN ([[SUC(2 * k) DIV 2 = k]]) SUBST1_TAC THENL
       [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC ([[1]]) THEN ARITH_TAC,
        REWRITE_TAC [EXP, MULT_2, EXP_ADD] THEN ARITH_TAC]])
  : ExceptT String IO thm).run
#eval SMOOTH_SQUARE_DECOMPOSITION

#eval phrase 5
def CARD_UNIONS_IMAGE_LE_NSUM : thm := keep "CARD_UNIONS_IMAGE_LE_NSUM" fun _ => (do
  prove ([[!f:A->B->bool s.
        FINITE s /\ (!x. x IN s ==> FINITE(f x))
        ==> CARD(UNIONS(IMAGE f s)) <= nsum s (\x. CARD(f x))]])
   (GEN_TAC THEN REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [IMAGE_CLAUSES, UNIONS_0, UNIONS_INSERT, CARD_CLAUSES,
             NSUM_CLAUSES, LE_REFL, FORALL_IN_INSERT] THEN
    MAP_EVERY X_GEN_TAC [([[x:A]]), ([[s:A->bool]])] THEN STRIP_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC ([[CARD((f:A->B->bool) x) + CARD(UNIONS(IMAGE f s))]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_UNION_LE THEN ASM_SIMP_TAC [FINITE_UNIONS] THEN
      ASM_SIMP_TAC [FINITE_IMAGE, FORALL_IN_IMAGE],
      ASM_SIMP_TAC [LE_ADD_LCANCEL]])
  : ExceptT String IO thm).run
#eval CARD_UNIONS_IMAGE_LE_NSUM

#eval phrase 6
def CARD_MULTIPLES_NUMSEG : thm := keep "CARD_MULTIPLES_NUMSEG" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[1 * 1 <= x ==> 1 <= x]])
  prove ([[!N p. ~(p = 0) ==> CARD {n | n IN 1..N /\ p divides n} = N DIV p]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[{n | n IN 1..N /\ p divides n} = IMAGE (\q. p * q) (1..N DIV p)]]) SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM, IN_NUMSEG, divides] THEN
      X_GEN_TAC ([[n:num]]) THEN EQ_TAC THENL
       [DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (X_CHOOSE_THEN ([[q:num]]) SUBST_ALL_TAC)) THEN
        EXISTS_TAC ([[q:num]]) THEN ASM_SIMP_TAC [LE_RDIV_EQ] THEN
        UNDISCH_TAC ([[1 <= p * q]]) THEN
        ASM_CASES_TAC ([[q = 0]]) THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN
        ASM_ARITH_TAC,
        DISCH_THEN (X_CHOOSE_THEN ([[q:num]]) STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC [] THEN
        CONJ_TAC THENL [ALL_TAC, MESON_TAC []] THEN
        UNDISCH_TAC ([[q <= N DIV p]]) THEN ASM_SIMP_TAC [LE_RDIV_EQ] THEN
        DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC h1 THEN
        MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC],
      ASM_SIMP_TAC [CARD_IMAGE_INJ, EQ_MULT_LCANCEL, FINITE_NUMSEG,
                   CARD_NUMSEG_1]])
  : ExceptT String IO thm).run
#eval CARD_MULTIPLES_NUMSEG

#eval phrase 7
#eval Session.prioritize_real

/- ------------------------------------------------------------------------- -/
/- The primes in (m, 4^(m + 1)].                                             -/
/- ------------------------------------------------------------------------- -/

#eval phrase 8
def PRIMERECIP_BLOCK : thm := keep "PRIMERECIP_BLOCK" fun _ => (do
  let h4 ← ar (← ExceptT.mk [[4 = 2 * 2]])
  let h3 ← ar (← ExceptT.mk [[(m + 1) * 2 = 2 * (m + 1)]])
  let h2 ← ar (← ExceptT.mk [[x:num = x * 1]])
  let h1 ← ar (← ExceptT.mk [[2 <= p ==> 1 <= p]])
  prove ([[!m. &1 / &2 <=
       sum {p | prime p /\ m < p /\ p <= 4 EXP (m + 1)} (\p. &1 / &p)]])
   (GEN_TAC THEN
    ABBREV_TAC ([[N = 4 EXP (m + 1)]]) THEN
    ABBREV_TAC ([[ps = {p | prime p /\ p <= m}]]) THEN
    ABBREV_TAC ([[qs = {p | prime p /\ m < p /\ p <= N}]]) THEN
    SUBGOAL_THEN ([[FINITE(ps:num->bool) /\ FINITE(qs:num->bool)]]) STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["ps", "qs"] THEN
      CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THENL
       [EXISTS_TAC ([[0..m]]), EXISTS_TAC ([[0..N]])] THEN
      REWRITE_TAC [FINITE_NUMSEG, SUBSET, IN_NUMSEG, IN_ELIM_THM, LE_0] THEN
      MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[CARD(ps:num->bool) <= m]]) ASSUME_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC ([[CARD(1..m)]]) THEN
      CONJ_TAC THENL [ALL_TAC, REWRITE_TAC [CARD_NUMSEG_1, LE_REFL]] THEN
      MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC [FINITE_NUMSEG] THEN
      EXPAND_TAC "ps" THEN REWRITE_TAC [SUBSET, IN_ELIM_THM, IN_NUMSEG] THEN
      MESON_TAC [PRIME_GE_2, h1],
      ALL_TAC] THEN
    ABBREV_TAC ([[A = IMAGE (\x. FST x EXP 2 * nproduct (SND x) (\p:num. p))
              ((1..2 EXP (m + 1)) CROSS {t | t SUBSET ps})]]) THEN
    ABBREV_TAC ([[B = UNIONS(IMAGE (\p. {n | n IN 1..N /\ p divides n}) qs)]]) THEN
    SUBGOAL_THEN ([[FINITE(A:num->bool) /\ FINITE(B:num->bool)]]) STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["A", "B"] THEN
      ASM_SIMP_TAC [FINITE_IMAGE, FINITE_CROSS, FINITE_NUMSEG, FINITE_POWERSET,
                   FINITE_UNIONS, FORALL_IN_IMAGE, FINITE_RESTRICT],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[1..N SUBSET (A:num->bool) UNION B]]) ASSUME_TAC THENL
     [REWRITE_TAC [SUBSET, IN_UNION] THEN X_GEN_TAC ([[n:num]]) THEN DISCH_TAC THEN
      SUBGOAL_THEN ([[~(n = 0) /\ n <= N]]) STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC ([[n IN 1..N]]) THEN REWRITE_TAC [IN_NUMSEG] THEN ARITH_TAC,
        ALL_TAC] THEN
      ASM_CASES_TAC ([[!p. prime p /\ p divides n ==> p IN ps]]) THENL
       [DISJ1_TAC THEN
        MP_TAC (← HolLight.ISPECL [([[ps:num->bool]]), ([[n:num]])] SMOOTH_SQUARE_DECOMPOSITION) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC [] THEN EXPAND_TAC "ps" THEN SIMP_TAC [IN_ELIM_THM],
          ALL_TAC] THEN
        ABBREV_TAC ([[s0 = nproduct ps (\p. p EXP (index p n DIV 2))]]) THEN
        ABBREV_TAC ([[t0 = {p | p IN ps /\ ODD(index p n)}]]) THEN
        ABBREV_TAC ([[q0 = nproduct t0 (\p:num. p)]]) THEN DISCH_TAC THEN
        EXPAND_TAC "A" THEN
        REWRITE_TAC [IN_IMAGE, EXISTS_PAIR_THM, IN_CROSS, IN_ELIM_THM] THEN
        MAP_EVERY EXISTS_TAC [([[s0:num]]), ([[t0:num->bool]])] THEN
        ASM_REWRITE_TAC [FST, SND] THEN CONJ_TAC THENL
         [ALL_TAC, EXPAND_TAC "t0" THEN SET_TAC []] THEN
        SUBGOAL_THEN ([[~(s0 = 0) /\ ~(q0 = 0)]]) STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC ([[~(n = 0)]]) THEN
          SUBST1_TAC (← HolLight.ASSUME ([[n = s0 EXP 2 * q0]])) THEN
          REWRITE_TAC [MULT_EQ_0, EXP_EQ_0] THEN ARITH_TAC,
          ALL_TAC] THEN
        REWRITE_TAC [IN_NUMSEG] THEN CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
        SUBGOAL_THEN ([[s0 EXP 2 <= (2 EXP (m + 1)) EXP 2]]) MP_TAC THENL
         [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC ([[n:num]]) THEN CONJ_TAC THENL
           [SUBST1_TAC (← HolLight.ASSUME ([[n = s0 EXP 2 * q0]])) THEN
            GEN_REWRITE_TAC HolLight.LAND_CONV [h2] THEN
            REWRITE_TAC [LE_MULT_LCANCEL] THEN ASM_ARITH_TAC,
            REWRITE_TAC [EXP_EXP, h3] THEN
            REWRITE_TAC [(← HolLight.GSYM EXP_EXP)] THEN CONV_TAC NUM_REDUCE_CONV THEN
            UNDISCH_TAC ([[n <= (N:num)]]) THEN EXPAND_TAC "N" THEN REWRITE_TAC []],
          REWRITE_TAC [EXP_MONO_LE, ARITH_EQ]],
        DISJ2_TAC THEN
        FIRST_X_ASSUM (X_CHOOSE_THEN ([[p:num]]) STRIP_ASSUME_TAC o
          HolLight.REWRITE_RULE [NOT_FORALL_THM, NOT_IMP]) THEN
        EXPAND_TAC "B" THEN REWRITE_TAC [IN_UNIONS, EXISTS_IN_IMAGE] THEN
        EXISTS_TAC ([[p:num]]) THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN
        EXPAND_TAC "qs" THEN REWRITE_TAC [IN_ELIM_THM] THEN
        ASM_REWRITE_TAC [] THEN
        UNDISCH_TAC ([[~((p:num) IN ps)]]) THEN EXPAND_TAC "ps" THEN
        ASM_REWRITE_TAC [IN_ELIM_THM, NOT_LE] THEN DISCH_TAC THEN
        ASM_REWRITE_TAC [] THEN MATCH_MP_TAC LE_TRANS THEN
        EXISTS_TAC ([[n:num]]) THEN ASM_REWRITE_TAC [] THEN
        MP_TAC (← HolLight.SPECL [([[p:num]]), ([[n:num]])] DIVIDES_LE) THEN ASM_REWRITE_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[N <= CARD(A:num->bool) + CARD(B:num->bool)]]) ASSUME_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC ([[CARD((A:num->bool) UNION B)]]) THEN
      ASM_SIMP_TAC [CARD_UNION_LE] THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM CARD_NUMSEG_1)] THEN
      MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC [FINITE_UNION],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[CARD(A:num->bool) <= 2 EXP (m + 1) * 2 EXP m]]) ASSUME_TAC THENL
     [EXPAND_TAC "A" THEN MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC ([[CARD((1..2 EXP (m + 1)) CROSS {t | t SUBSET (ps:num->bool)})]]) THEN
      ASM_SIMP_TAC [CARD_IMAGE_LE, FINITE_CROSS, FINITE_NUMSEG,
                   FINITE_POWERSET] THEN
      ASM_SIMP_TAC [CARD_CROSS, FINITE_NUMSEG, FINITE_POWERSET, CARD_NUMSEG_1,
                   CARD_POWERSET] THEN
      ASM_REWRITE_TAC [LE_MULT_LCANCEL, LE_EXP, ARITH_EQ],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[CARD(B:num->bool) <= nsum qs (\p. N DIV p)]]) ASSUME_TAC THENL
     [EXPAND_TAC "B" THEN MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC ([[nsum qs (\p. CARD {n | n IN 1..N /\ p divides n})]]) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CARD_UNIONS_IMAGE_LE_NSUM THEN
        ASM_SIMP_TAC [FINITE_RESTRICT, FINITE_NUMSEG],
        MATCH_MP_TAC EQ_IMP_LE THEN MATCH_MP_TAC NSUM_EQ THEN
        EXPAND_TAC "qs" THEN REWRITE_TAC [IN_ELIM_THM] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_MULTIPLES_NUMSEG THEN
        ASM_MESON_TAC [PRIME_IMP_NZ]],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[2 * (2 EXP (m + 1) * 2 EXP m) = N]]) ASSUME_TAC THENL
     [EXPAND_TAC "N" THEN REWRITE_TAC [EXP_ADD, EXP_1] THEN
      REWRITE_TAC [h4, MULT_EXP] THEN ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[&N <= &N * inv(&2) + &N * sum qs (\p. inv(&p))]]) MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC ([[&(2 EXP (m + 1) * 2 EXP m) + &(nsum qs (\p. N DIV p))]]) THEN
      CONJ_TAC THENL
       [REWRITE_TAC [REAL_OF_NUM_ADD, REAL_OF_NUM_LE] THEN ASM_ARITH_TAC,
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
       [SUBST1_TAC (← HolLight.SYM (← HolLight.ASSUME ([[2 * (2 EXP (m + 1) * 2 EXP m) = N]]))) THEN
        REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_MUL)] THEN REAL_ARITH_TAC2,
        ASM_SIMP_TAC [REAL_OF_NUM_SUM, (← HolLight.GSYM SUM_LMUL)] THEN
        MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC [] THEN
        EXPAND_TAC "qs" THEN REWRITE_TAC [IN_ELIM_THM] THEN
        X_GEN_TAC ([[p:num]]) THEN STRIP_TAC THEN
        SUBGOAL_THEN ([[&0 < &p]]) ASSUME_TAC THENL
         [REWRITE_TAC [REAL_OF_NUM_LT] THEN ASM_MESON_TAC [PRIME_IMP_NZ, LT_NZ],
          ALL_TAC] THEN
        REWRITE_TAC [(← HolLight.GSYM real_div)] THEN ASM_SIMP_TAC [REAL_LE_RDIV_EQ] THEN
        REWRITE_TAC [REAL_OF_NUM_MUL, REAL_OF_NUM_LE] THEN
        ONCE_REWRITE_TAC [MULT_SYM] THEN REWRITE_TAC [DIV_MUL_LE]],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[&0 < (&N:real)]]) ASSUME_TAC THENL
     [SUBST1_TAC (← HolLight.SYM (← HolLight.ASSUME ([[4 EXP (m + 1) = N]]))) THEN
      REWRITE_TAC [REAL_OF_NUM_LT, LT_NZ, EXP_EQ_0, ARITH_EQ],
      ALL_TAC] THEN
    DISCH_TAC THEN REWRITE_TAC [real_div, REAL_MUL_LID] THEN
    SUBGOAL_THEN ([[(&N:real) * inv(&2) <= &N * sum qs (\p. inv(&p))]]) MP_TAC THENL
     [ASM_REAL_ARITH_TAC, ASM_SIMP_TAC [REAL_LE_LMUL_EQ]])
  : ExceptT String IO thm).run
#eval PRIMERECIP_BLOCK

/- ------------------------------------------------------------------------- -/
/- Divergence.                                                               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 9
def PRIMERECIP_UNBOUNDED : thm := keep "PRIMERECIP_UNBOUNDED" fun _ => (do
  let h3 ← rr (← ExceptT.mk [[!s. &2 * b <= &k /\ &k / &2 <= s ==> b <= s]])
  let h2 ← rr (← ExceptT.mk [[(&k + &1) / &2 = &k / &2 + &1 / &2]])
  let h1 ← ar (← ExceptT.mk [[~((p:num) <= n /\ n < p)]])
  prove ([[!b. ?n. b <= sum {p | prime p /\ p <= n} (\p. &1 / &p)]])
   (SUBGOAL_THEN ([[!k. ?n. &k / &2 <= sum {p | prime p /\ p <= n} (\p. &1 / &p)]]) ASSUME_TAC THENL
     [INDUCT_TAC THENL
       [EXISTS_TAC ([[0]]) THEN REWRITE_TAC [real_div, REAL_MUL_LZERO] THEN
        MATCH_MP_TAC SUM_POS_LE THEN
        REWRITE_TAC [REAL_MUL_LID, REAL_LE_INV_EQ, REAL_POS],
        ALL_TAC] THEN
      FIRST_X_ASSUM (X_CHOOSE_TAC ([[n:num]])) THEN EXISTS_TAC ([[4 EXP (n + 1)]]) THEN
      SUBGOAL_THEN ([[n <= 4 EXP (n + 1)]]) ASSUME_TAC THENL
       [MATCH_MP_TAC LT_IMP_LE THEN MATCH_MP_TAC LTE_TRANS THEN
        EXISTS_TAC ([[2 EXP n]]) THEN REWRITE_TAC [LT_POW2_REFL] THEN
        MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC ([[4 EXP n]]) THEN CONJ_TAC THENL
         [MATCH_MP_TAC EXP_MONO_LE_IMP THEN ARITH_TAC,
          REWRITE_TAC [LE_EXP] THEN ARITH_TAC],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[{p | prime p /\ p <= 4 EXP (n + 1)} =
      {p | prime p /\ p <= n} UNION
      {p | prime p /\ n < p /\ p <= 4 EXP (n + 1)}]]) SUBST1_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_UNION, IN_ELIM_THM] THEN
        X_GEN_TAC ([[p:num]]) THEN ASM_CASES_TAC ([[prime p]]) THEN
        ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
        ALL_TAC] THEN
      HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
          let x1 ← ec (HolCore.Kernel.rand w)
          let x2 ← ExceptT.mk (HolLight.PART_MATCH (HolCore.Equal.lhand o HolCore.Kernel.rand) SUM_UNION x1)
          pure (MP_TAC x2)) THEN
      ANTS_TAC THENL
       [REWRITE_TAC [DISJOINT, EXTENSION, IN_INTER, IN_ELIM_THM,
                    NOT_IN_EMPTY] THEN
        REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC ([[0..n]]),
          MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC ([[0..4 EXP (n + 1)]]),
          MESON_TAC [h1]] THEN
        REWRITE_TAC [FINITE_NUMSEG, SUBSET, IN_NUMSEG, IN_ELIM_THM, LE_0] THEN
        MESON_TAC [],
        DISCH_THEN SUBST1_TAC] THEN
      MP_TAC (← HolLight.SPEC ([[n:num]]) PRIMERECIP_BLOCK) THEN
      REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_SUC),
                  h2] THEN
      DISCH_TAC THEN MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    X_GEN_TAC ([[b:real]]) THEN
    X_CHOOSE_TAC ([[k:num]]) (← HolLight.SPEC ([[&2 * b]]) REAL_ARCH_SIMPLE) THEN
    FIRST_X_ASSUM (X_CHOOSE_TAC ([[n:num]]) o HolLight.SPEC ([[k:num]])) THEN
    EXISTS_TAC ([[n:num]]) THEN
    MATCH_MP_TAC h3 THEN
    ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval PRIMERECIP_UNBOUNDED

#eval phrase 10
def UNBOUNDED_MONO_DIVERGES : thm := keep "UNBOUNDED_MONO_DIVERGES" fun _ => (do
  prove ([[!f:num->real.
        (!b. ?n. b <= f n) /\ (!m n. m <= n ==> f m <= f n)
        ==> ~(?s. !e. &0 < e ==> ?N. !n. N <= n ==> abs(f n - s) < e)]])
   (GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "mono")) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[s:real]]) (MP_TAC o HolLight.SPEC ([[&1]]))) THEN
    REWRITE_TAC [REAL_LT_01] THEN DISCH_THEN (X_CHOOSE_TAC ([[N:num]])) THEN
    FIRST_X_ASSUM (X_CHOOSE_TAC ([[n:num]]) o HolLight.SPEC ([[s + &1]])) THEN
    REMOVE_THEN "mono" (MP_TAC o HolLight.SPECL [([[n:num]]), ([[n + N:num]])]) THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[n + N:num]])) THEN
    REWRITE_TAC [LE_ADD, LE_ADDR] THEN ASM_REAL_ARITH_TAC)
  : ExceptT String IO thm).run
#eval UNBOUNDED_MONO_DIVERGES

#eval phrase 11
def PRIMERECIP_DIVERGES : thm := keep "PRIMERECIP_DIVERGES" fun _ => (do
  prove ([[~(?s. !e. &0 < e
             ==> ?N. !n. N <= n
                         ==> abs(sum {p | prime p /\ p <= n} (\p. &1 / &p) -
                                 s) < e)]])
   (MP_TAC (← HolLight.ISPEC ([[\n. sum {p | prime p /\ p <= n} (\p. &1 / &p)]]) UNBOUNDED_MONO_DIVERGES) THEN
    REWRITE_TAC [PRIMERECIP_UNBOUNDED] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC ([[0..n]]) THEN
      REWRITE_TAC [FINITE_NUMSEG, SUBSET, IN_NUMSEG, IN_ELIM_THM, LE_0] THEN
      MESON_TAC [],
      REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC [LE_TRANS],
      SIMP_TAC [REAL_LE_DIV, REAL_POS]])
  : ExceptT String IO thm).run
#eval PRIMERECIP_DIVERGES

#eval phrase 12
def PRIMERECIP_DIVERGES_NUMSEG : thm := keep "PRIMERECIP_DIVERGES_NUMSEG" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[2 <= p ==> 1 <= p]])
  prove ([[~(?s. !e. &0 < e
             ==> ?N. !n. N <= n
                         ==> abs(sum(1..n) (\i. if prime i then &1 / &i
                                                else &0) - s) < e)]])
   (SUBGOAL_THEN ([[!n. sum(1..n) (\i. if prime i then &1 / &i else &0) =
        sum {p | prime p /\ p <= n} (\p. &1 / &p)]]) (fun th => REWRITE_TAC [th, PRIMERECIP_DIVERGES]) THEN
    GEN_TAC THEN REWRITE_TAC [(← HolLight.GSYM SUM_RESTRICT_SET)] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_NUMSEG] THEN
    MESON_TAC [PRIME_GE_2, h1])
  : ExceptT String IO thm).run
#eval PRIMERECIP_DIVERGES_NUMSEG

end Hol100.PrimeRecip
