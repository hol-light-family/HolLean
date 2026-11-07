/- File: Hol100/Euler.lean
Translation of HOL Light's 100/euler.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionLibrary.Binary
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Binary
namespace Hol100.Euler

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)

/- ========================================================================= -/
/- Euler's partition theorem and other elementary partition theorems.        -/
/- ========================================================================= -/

#eval phrase 1
-- loadt "Library/binary.ml";;
#eval SessionLibrary.Binary.ensureBinary

/- ------------------------------------------------------------------------- -/
/- Some lemmas.                                                              -/
/- ------------------------------------------------------------------------- -/

#eval phrase 2
def NSUM_BOUND_LEMMA : thm := keep "NSUM_BOUND_LEMMA" fun _ => (do
  prove ([[!f a b n. nsum(a..b) f = n ==> !i. a <= i /\ i <= b ==> f(i) <= n]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [(← HolLight.GSYM IN_NUMSEG)] THEN
    MATCH_MP_TAC NSUM_POS_BOUND THEN ASM_REWRITE_TAC [LE_REFL, FINITE_NUMSEG])
  : ExceptT String IO thm).run
#eval NSUM_BOUND_LEMMA

#eval phrase 3
def CARD_EQ_LEMMA : thm := keep "CARD_EQ_LEMMA" fun _ => (do
  prove ([[!f:A->B g s t.
        FINITE s /\ FINITE t /\
        (!x. x IN s ==> f(x) IN t) /\
        (!y. y IN t ==> g(y) IN s) /\
        (!x. x IN s ==> g(f x) = x) /\
        (!y. y IN t ==> f(g y) = y)
        ==> FINITE s /\ FINITE t /\ CARD s = CARD t]])
   (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC CARD_IMAGE_INJ_EQ THEN
    EXISTS_TAC ([[g:B->A]]) THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval CARD_EQ_LEMMA

/- ------------------------------------------------------------------------- -/
/- Breaking a number up into 2^something * odd_number.                       -/
/- ------------------------------------------------------------------------- -/

#eval phrase 4
def index : thm := keep "index" fun _ => define
 [[index n = if n = 0 then 0 else if ODD n then 0 else SUC(index(n DIV 2))]]
#eval index

#eval phrase 5
def oddpart : thm := keep "oddpart" fun _ => define
 [[oddpart n = if n = 0 then 0 else if ODD n then n else oddpart(n DIV 2)]]
#eval oddpart

#eval phrase 6
def INDEX_ODDPART_WORK : thm := keep "INDEX_ODDPART_WORK" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[~(n = 0) /\ n = 2 * m ==> m < n /\ ~(m = 0)]])
  let h1 ← ar (← ExceptT.mk [[(2 * x) DIV 2 = x]])
  prove ([[!n. n = 2 EXP (index n) * oddpart n /\ (ODD(oddpart n) <=> ~(n = 0))]])
   (MATCH_MP_TAC num_WF THEN GEN_TAC THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC [index, oddpart] THEN
    ASM_CASES_TAC ([[n = 0]]) THEN ASM_REWRITE_TAC [ARITH] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [ARITH, MULT_CLAUSES] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [NOT_ODD]) THEN
    SIMP_TAC [EVEN_EXISTS, LEFT_IMP_EXISTS_THM, EXP, (← HolLight.GSYM MULT_ASSOC),
             ARITH, h1, EQ_MULT_LCANCEL] THEN
    ASM_MESON_TAC [h2])
  : ExceptT String IO thm).run
#eval INDEX_ODDPART_WORK

#eval phrase 7
def INDEX_ODDPART_DECOMPOSITION : thm := keep "INDEX_ODDPART_DECOMPOSITION" fun _ => (do
  prove ([[!n. n = 2 EXP (index n) * oddpart n]])
   (MESON_TAC [INDEX_ODDPART_WORK])
  : ExceptT String IO thm).run
#eval INDEX_ODDPART_DECOMPOSITION

#eval phrase 8
def ODD_ODDPART : thm := keep "ODD_ODDPART" fun _ => (do
  prove ([[!n. ODD(oddpart n) <=> ~(n = 0)]])
   (MESON_TAC [INDEX_ODDPART_WORK])
  : ExceptT String IO thm).run
#eval ODD_ODDPART

#eval phrase 9
def ODDPART_LE : thm := keep "ODDPART_LE" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[1 <= n <=> ~(n = 0)]])
  let h1 ← ar (← ExceptT.mk [[1 * x <= y * x ==> x <= y * x]])
  prove ([[!n. oddpart n <= n]])
   (GEN_TAC THEN GEN_REWRITE_TAC HolLight.RAND_CONV [INDEX_ODDPART_DECOMPOSITION] THEN
    MATCH_MP_TAC h1 THEN
    REWRITE_TAC [LE_MULT_RCANCEL, h2] THEN
    REWRITE_TAC [EXP_EQ_0, ARITH])
  : ExceptT String IO thm).run
#eval ODDPART_LE

#eval phrase 10
def INDEX_ODDPART_UNIQUE : thm := keep "INDEX_ODDPART_UNIQUE" fun _ => (do
  prove ([[!i m i' m'. ODD m /\ ODD m'
               ==> (2 EXP i * m = 2 EXP i' * m' <=> i = i' /\ m = m')]])
   (REWRITE_TAC [ODD_EXISTS, ADD1] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [(← HolLight.GSYM NUMPAIR), NUMPAIR_INJ] THEN
    ARITH_TAC)
  : ExceptT String IO thm).run
#eval INDEX_ODDPART_UNIQUE

#eval phrase 11
def INDEX_ODDPART : thm := keep "INDEX_ODDPART" fun _ => (do
  prove ([[!i m. ODD m ==> index(2 EXP i * m) = i /\ oddpart(2 EXP i * m) = m]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [([[i:num]]), ([[m:num]]), ([[index(2 EXP i * m)]]), ([[oddpart(2 EXP i * m)]])] INDEX_ODDPART_UNIQUE) THEN
    REWRITE_TAC [(← HolLight.GSYM INDEX_ODDPART_DECOMPOSITION), ODD_ODDPART] THEN
    ASM_REWRITE_TAC [MULT_EQ_0, EXP_EQ_0, ARITH] THEN ASM_MESON_TAC [ODD])
  : ExceptT String IO thm).run
#eval INDEX_ODDPART

/- ------------------------------------------------------------------------- -/
/- Partitions.                                                               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 12
-- parse_as_infix("partitions",(12,"right"));;
#eval (parse_as_infix ("partitions", (12, "right")) : IO Unit)

#eval phrase 13
def partitions : thm := keep "partitions" fun _ => new_definition
 [[p partitions n <=> (!i. ~(p i = 0) ==> 1 <= i /\ i <= n) /\
                     nsum(1..n) (\i. p(i) * i) = n]]
#eval partitions

#eval phrase 14
def PARTITIONS_BOUND : thm := keep "PARTITIONS_BOUND" fun _ => (do
  let h3 ← ar (← ExceptT.mk [[n < p /\ p * 1 <= p * k ==> n < p * k]])
  let h2 ← ar (← ExceptT.mk [[m = n ==> n < m ==> F]])
  let h1 ← ar (← ExceptT.mk [[m < n ==> ~(n = 0)]])
  prove ([[!p n. p partitions n ==> !i. p(i) <= n]])
   (REWRITE_TAC [(← HolLight.GSYM NOT_LT)] THEN SIMP_TAC [partitions] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[1 <= i /\ i <= n]]) STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC [h1], ALL_TAC] THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h2) THEN
    MATCH_MP_TAC LET_TRANS THEN
    EXISTS_TAC ([[nsum(1..n) (\j. if j = i then n else 0)]]) THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC [NSUM_DELTA, IN_NUMSEG, LE_REFL], ALL_TAC] THEN
    MATCH_MP_TAC NSUM_LT THEN REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG] THEN
    CONJ_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [LE_0] THEN
      MATCH_MP_TAC LT_IMP_LE,
      EXISTS_TAC ([[i:num]]) THEN ASM_REWRITE_TAC []] THEN
    MATCH_MP_TAC h3 THEN
    ASM_REWRITE_TAC [LE_MULT_LCANCEL])
  : ExceptT String IO thm).run
#eval PARTITIONS_BOUND

#eval phrase 15
def FINITE_PARTITIONS_LEMMA : thm := keep "FINITE_PARTITIONS_LEMMA" fun _ => (do
  let h3 ← ar (← ExceptT.mk [[SUC m <= i ==> m <= i /\ ~(i = m)]])
  let h2 ← ar (← ExceptT.mk [[m <= i /\ ~(i = m) ==> SUC m <= i]])
  let h1 ← tt (← ExceptT.mk [[a /\ b <=> ~(b ==> ~a)]])
  prove ([[!m n. FINITE {p | (!i. p(i) <= n) /\ !i. m <= i ==> p(i) = 0}]])
   (INDUCT_TAC THEN GEN_TAC THENL
     [SIMP_TAC [LE_0, h1] THEN
      SUBGOAL_THEN ([[{p | !i:num. p i = 0} = {(\n. 0)}]]) (fun th => SIMP_TAC [th, FINITE_RULES]) THEN
      REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_SING] THEN REWRITE_TAC [FUN_EQ_THM],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[{p | (!i. p i <= n) /\ (!i. SUC m <= i ==> p i = 0)} =
    IMAGE (\(a,p) j. if j = m then a else p(j))
        {a,p | a IN 0..n /\
               p IN {p | (!i. p i <= n) /\ (!i. m <= i ==> p i = 0)}}]]) (fun t => ASM_SIMP_TAC [t, FINITE_IMAGE, FINITE_PRODUCT, FINITE_NUMSEG]) THEN
    REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_IMAGE, EXISTS_PAIR_THM] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN X_GEN_TAC ([[p:num->num]]) THEN
    EQ_TAC THENL
     [STRIP_TAC THEN MAP_EVERY EXISTS_TAC [([[(p:num->num) m]]), ([[\i:num. if i = m then 0 else p i]])] THEN
      REWRITE_TAC [FUN_EQ_THM] THEN CONJ_TAC THENL [MESON_TAC [], ALL_TAC] THEN
      ONCE_REWRITE_TAC [CONJ_SYM] THEN ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
      REWRITE_TAC [PAIR_EQ, UNWIND_THM1, (← HolLight.GSYM CONJ_ASSOC), IN_NUMSEG, LE_0] THEN
      ASM_MESON_TAC [LE, h2],
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[a:num]]), ([[q:num->num]])] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      POP_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC [IN_NUMSEG] THEN
      STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o HolLight.SYM) THEN
      REWRITE_TAC [PAIR_EQ] THEN DISCH_THEN (CONJUNCTS_THEN SUBST_ALL_TAC) THEN
      ASM_MESON_TAC [h3]])
  : ExceptT String IO thm).run
#eval FINITE_PARTITIONS_LEMMA

#eval phrase 16
def FINITE_PARTITIONS : thm := keep "FINITE_PARTITIONS" fun _ => (do
  prove ([[!n. FINITE {p | p partitions n}]])
   (GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC ([[{p | (!i. p(i) <= n) /\ (!i. SUC n <= i ==> p(i) = 0)}]]) THEN
    SIMP_TAC [FINITE_PARTITIONS_LEMMA, IN_ELIM_THM, SUBSET, PARTITIONS_BOUND] THEN
    REWRITE_TAC [partitions, LE_SUC_LT] THEN MESON_TAC [NOT_LE])
  : ExceptT String IO thm).run
#eval FINITE_PARTITIONS

#eval phrase 17
def FINITE_SUBSET_PARTITIONS : thm := keep "FINITE_SUBSET_PARTITIONS" fun _ => (do
  prove ([[!P n. FINITE {p | p partitions n /\ P p}]])
   (REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC ([[{p | p partitions n}]]) THEN
    SIMP_TAC [FINITE_PARTITIONS, IN_ELIM_THM, SUBSET])
  : ExceptT String IO thm).run
#eval FINITE_SUBSET_PARTITIONS

/- ------------------------------------------------------------------------- -/
/- Mappings between "odd only" and "all distinct" partitions.                -/
/- ------------------------------------------------------------------------- -/

#eval phrase 18
def odd_of_distinct : thm := keep "odd_of_distinct" fun _ => new_definition
 [[odd_of_distinct p =
    \i. if ODD i then nsum {j | p(2 EXP j * i) = 1} (\j. 2 EXP j) else 0]]
#eval odd_of_distinct

#eval phrase 19
def distinct_of_odd : thm := keep "distinct_of_odd" fun _ => new_definition
 [[distinct_of_odd p = \i. if (index i) IN bitset (p(oddpart i)) then 1 else 0]]
#eval distinct_of_odd

/- ------------------------------------------------------------------------- -/
/- The critical properties.                                                  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 20
def ODD_ODD_OF_DISTINCT : thm := keep "ODD_ODD_OF_DISTINCT" fun _ => (do
  prove ([[!p i. ~(odd_of_distinct p i = 0) ==> ODD i]])
   (REWRITE_TAC [odd_of_distinct] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval ODD_ODD_OF_DISTINCT

#eval phrase 21
def DISTINCT_DISTINCT_OF_ODD : thm := keep "DISTINCT_DISTINCT_OF_ODD" fun _ => (do
  prove ([[!p i. distinct_of_odd p i <= 1]])
   (REWRITE_TAC [distinct_of_odd] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval DISTINCT_DISTINCT_OF_ODD

#eval phrase 22
def SUPPORT_ODD_OF_DISTINCT : thm := keep "SUPPORT_ODD_OF_DISTINCT" fun _ => (do
  let h5 ← ar (← ExceptT.mk [[1 <= i <=> ~(i = 0)]])
  let h4 ← ar (← ExceptT.mk [[i <= j * i <=> 1 * i <= j * i]])
  let h3 ← ar (← ExceptT.mk [[~((if p then x else 0) = 0) <=> p /\ ~(x = 0)]])
  let h2 ← ar (← ExceptT.mk [[j < ej /\ ej * 1 <= ej * i ==> j <= ej * i]])
  let h1 ← ar (← ExceptT.mk [[1 <= i <=> ~(i = 0)]])
  prove ([[!p. (!i. ~(p i = 0) ==> i <= n)
       ==> !i. ~(odd_of_distinct p i = 0) ==> 1 <= i /\ i <= n]])
   (REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC [ODD, h1, ODD_ODD_OF_DISTINCT],
      FIRST_X_ASSUM (MP_TAC o check (HolCore.Basics.is_neg o concl))] THEN
    REWRITE_TAC [odd_of_distinct] THEN
    ASM_CASES_TAC ([[i = 0]]) THEN ASM_REWRITE_TAC [LE_0] THEN
    SUBGOAL_THEN ([[FINITE {j | p (2 EXP j * i) = 1}]]) ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC ([[0..n]]) THEN
      REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG, SUBSET] THEN X_GEN_TAC ([[j:num]]) THEN
      REWRITE_TAC [IN_ELIM_THM, LE_0] THEN DISCH_TAC THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC ([[2 EXP j * i]]) THEN
      ASM_SIMP_TAC [ARITH_EQ] THEN
      MATCH_MP_TAC h2 THEN
      REWRITE_TAC [LT_POW2_REFL, LE_MULT_LCANCEL, EXP_EQ_0, ARITH] THEN
      UNDISCH_TAC ([[~(i = 0)]]) THEN ARITH_TAC,
      SIMP_TAC [h3] THEN
      ASM_SIMP_TAC [NSUM_EQ_0_IFF, EXP_EQ_0, ARITH] THEN
      REWRITE_TAC [NOT_FORALL_THM, IN_ELIM_THM] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC ([[j:num]]))) THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC ([[2 EXP j * i]]) THEN
      ASM_SIMP_TAC [ARITH, h4] THEN
      REWRITE_TAC [LE_MULT_RCANCEL, h5] THEN
      REWRITE_TAC [EXP_EQ_0, ARITH]])
  : ExceptT String IO thm).run
#eval SUPPORT_ODD_OF_DISTINCT

#eval phrase 23
def SUPPORT_DISTINCT_OF_ODD : thm := keep "SUPPORT_DISTINCT_OF_ODD" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[1 <= i <=> ~(i = 0)]])
  let h1 ← ar (← ExceptT.mk [[(if a then 1 else 0) = 0 <=> ~a]])
  prove ([[!p. (!i. p(i) * i <= n) /\
       (!i. ~(p i = 0) ==> ODD i)
       ==> !i. ~(distinct_of_odd p i = 0) ==> 1 <= i /\ i <= n]])
   (REWRITE_TAC [distinct_of_odd] THEN
    REWRITE_TAC [h1] THEN
    GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC ([[i:num]]) THEN REPEAT STRIP_TAC THENL
     [REWRITE_TAC [h2] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC ([[index 0 IN bitset (p (oddpart 0))]]) THEN
      REWRITE_TAC [index, oddpart, ARITH] THEN
      UNDISCH_THEN ([[!i. ~(p i = 0) ==> ODD i]]) (MP_TAC o HolLight.SPEC ([[0]])) THEN
      SIMP_TAC [ARITH, BITSET_0, NOT_IN_EMPTY],
      ALL_TAC] THEN
    FIRST_X_ASSUM (ASSUME_TAC o HolLight.MATCH_MP BITSET_BOUND_LEMMA) THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC ([[p(oddpart i) * oddpart i]]) THEN
    ASM_REWRITE_TAC [] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [INDEX_ODDPART_DECOMPOSITION] THEN
    ASM_REWRITE_TAC [LE_MULT_RCANCEL])
  : ExceptT String IO thm).run
#eval SUPPORT_DISTINCT_OF_ODD

#eval phrase 24
def ODD_OF_DISTINCT_OF_ODD : thm := keep "ODD_OF_DISTINCT_OF_ODD" fun _ => (do
  prove ([[!p. (!i. ~(p(i) = 0) ==> ODD i)
       ==> odd_of_distinct (distinct_of_odd p) = p]])
   (REWRITE_TAC [IN_ELIM_THM, odd_of_distinct, distinct_of_odd] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC ([[i:num]]) THEN
    COND_CASES_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
    ASM_SIMP_TAC [INDEX_ODDPART] THEN
    GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.GSYM BINARYSUM_BITSET)] THEN
    REWRITE_TAC [binarysum] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [ARITH_EQ])
  : ExceptT String IO thm).run
#eval ODD_OF_DISTINCT_OF_ODD

#eval phrase 25
def DISTINCT_OF_ODD_OF_DISTINCT : thm := keep "DISTINCT_OF_ODD_OF_DISTINCT" fun _ => (do
  let h5 ← ar (← ExceptT.mk [[i <= 1 ==> i = 0 \/ i = 1]])
  let h4 ← ar (← ExceptT.mk [[1 <= n <=> ~(n = 0)]])
  let h3 ← ar (← ExceptT.mk [[j < ej /\ 1 * ej <= i * ej ==> j <= ej * i]])
  let h2 ← ar (← ExceptT.mk [[!x. y <= x /\ 1 <= x /\ x <= n ==> y <= n]])
  let h1 ← ar (← ExceptT.mk [[~(1 <= 0)]])
  prove ([[!p. (!i. ~(p i = 0) ==> 1 <= i /\ i <= n) /\ (!i. p(i) <= 1)
       ==> distinct_of_odd (odd_of_distinct p) = p]])
   (REWRITE_TAC [distinct_of_odd, odd_of_distinct, IN_ELIM_THM] THEN
    REWRITE_TAC [partitions, ODD_ODDPART] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC ([[i:num]]) THEN
    ASM_CASES_TAC ([[i = 0]]) THEN ASM_REWRITE_TAC [BITSET_0, NOT_IN_EMPTY] THENL
     [ASM_MESON_TAC [h1], ALL_TAC] THEN
    SUBGOAL_THEN ([[FINITE {j | p (2 EXP j * oddpart i) = 1}]]) ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC ([[0..n]]) THEN
      REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG, SUBSET, IN_ELIM_THM] THEN
      X_GEN_TAC ([[j:num]]) THEN DISCH_TAC THEN REWRITE_TAC [LE_0] THEN
      MATCH_MP_TAC h2 THEN
      EXISTS_TAC ([[2 EXP j * oddpart i]]) THEN ASM_SIMP_TAC [ARITH] THEN
      MATCH_MP_TAC h3 THEN
      REWRITE_TAC [LT_POW2_REFL, LE_MULT_RCANCEL] THEN
      ASM_MESON_TAC [ODD_ODDPART, ODD, h4],
      ASM_SIMP_TAC [BITSET_BINARYSUM, (← HolLight.GSYM binarysum), IN_ELIM_THM] THEN
      REWRITE_TAC [(← HolLight.GSYM INDEX_ODDPART_DECOMPOSITION)] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [ARITH_EQ] THEN
      ASM_MESON_TAC [h5]])
  : ExceptT String IO thm).run
#eval DISTINCT_OF_ODD_OF_DISTINCT

#eval phrase 26
def NSUM_DISTINCT_OF_ODD : thm := keep "NSUM_DISTINCT_OF_ODD" fun _ => (do
  let h8 ← ar (← ExceptT.mk [[1 <= x <=> ~(x = 0)]])
  let h7 ← ar (← ExceptT.mk [[1 <= x <=> ~(x = 0)]])
  let h6 ← ar (← ExceptT.mk [[1 <= x <=> ~(x = 0)]])
  let h5 ← tt (← ExceptT.mk [[(a /\ b) /\ c <=> a /\ b /\ (b ==> c)]])
  let h4 ← ar (← ExceptT.mk [[(if p then 1 else 0) * x * y = (if p then x * y else 0)]])
  let h3 ← ar (← ExceptT.mk [[~(1 <= 0)]])
  let h2 ← ar (← ExceptT.mk [[(if p then 1 else 0) = 0 <=> ~p]])
  let h1 ← ar (← ExceptT.mk [[~(1 <= 0)]])
  prove ([[!p. (!i. ~(p i = 0) ==> 1 <= i /\ i <= n) /\
       (!i. p(i) * i <= n) /\
       (!i. ~(p(i) = 0) ==> ODD i)
       ==> nsum(1..n) (\i. distinct_of_odd p i * i) =
           nsum(1..n) (\i. p i * i)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [distinct_of_odd] THEN
    GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.BINDER_CONV o HolLight.LAND_CONV) [(← HolLight.GSYM BINARYSUM_BITSET)] THEN
    REWRITE_TAC [binarysum] THEN REWRITE_TAC [(← HolLight.GSYM NSUM_RMUL)] THEN
    SIMP_TAC [NSUM_NSUM_PRODUCT, FINITE_BITSET, FINITE_NUMSEG] THEN
    CONV_TAC HolLight.SYM_CONV THEN ONCE_REWRITE_TAC [(← HolLight.GSYM NSUM_SUPPORT)] THEN
    REWRITE_TAC [support, NEUTRAL_ADD] THEN
    SUBGOAL_THEN ([[{x | x IN {i,j | i IN 1..n /\ j IN bitset(p i)} /\
         ~((\(i,j). 2 EXP j * i) x = 0)} =
    {i,j | i IN 1..n /\ j IN bitset(p i)}]]) SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, FORALL_PAIR_THM, IN_ELIM_PAIR_THM, IN_ELIM_THM] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC [IN_NUMSEG, EXP_EQ_0, MULT_EQ_0, ARITH] THEN
      MESON_TAC [h1],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[{x | x IN 1 .. n /\
         ~((if index x IN bitset (p (oddpart x)) then 1 else 0) * x = 0)} =
    {i | i IN 1..n /\ (index i) IN bitset (p(oddpart i))}]]) SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_ELIM_THM, MULT_EQ_0] THEN
      REWRITE_TAC [IN_NUMSEG, h2] THEN
      MESON_TAC [h3],
      ALL_TAC] THEN
    MATCH_MP_TAC NSUM_EQ_GENERAL THEN
    EXISTS_TAC ([[\(i,b). 2 EXP b * i]]) THEN
    SIMP_TAC [FORALL_PAIR_THM, IN_ELIM_PAIR_THM] THEN
    CONV_TAC (HolLight.TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC [h4] THEN
    GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.TOP_DEPTH_CONV) [IN_ELIM_THM] THEN
    ONCE_REWRITE_TAC [h5] THEN
    SIMP_TAC [] THEN REWRITE_TAC [EXISTS_UNIQUE_THM] THEN
    REWRITE_TAC [FORALL_PAIR_THM, EXISTS_PAIR_THM, IN_ELIM_PAIR_THM] THEN
    CONV_TAC (HolLight.TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC [IN_ELIM_THM, IN_NUMSEG] THEN
    SUBGOAL_THEN ([[!i j. j IN bitset(p i) ==> ODD i]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [BITSET_0, NOT_IN_EMPTY], ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC ([[m:num]]) THEN STRIP_TAC THEN CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC [([[oddpart m]]), ([[index m]])] THEN
        ASM_REWRITE_TAC [(← HolLight.GSYM INDEX_ODDPART_DECOMPOSITION)] THEN
        ASM_MESON_TAC [ODDPART_LE, LE_TRANS, h6,
                      ODD_ODDPART, ODD],
        ASM_MESON_TAC [INDEX_ODDPART_UNIQUE]],
      MAP_EVERY X_GEN_TAC [([[m:num]]), ([[i:num]])] THEN STRIP_TAC THEN
      CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [INDEX_ODDPART]] THEN CONJ_TAC THENL
       [REWRITE_TAC [h7] THEN
        REWRITE_TAC [MULT_EQ_0, EXP_EQ_0, ARITH] THEN
        ASM_MESON_TAC [h8],
        ASM_MESON_TAC [BITSET_BOUND_LEMMA, LE_MULT_RCANCEL, LE_TRANS]]])
  : ExceptT String IO thm).run
#eval NSUM_DISTINCT_OF_ODD

#eval phrase 27
def DISTINCT_OF_ODD : thm := keep "DISTINCT_OF_ODD" fun _ => (do
  prove ([[!p. p IN {p | p partitions n /\ !i. ~(p(i) = 0) ==> ODD i}
       ==> (distinct_of_odd p) IN {p | p partitions n /\ !i. p(i) <= 1}]])
   (GEN_TAC THEN REWRITE_TAC [IN_ELIM_THM, partitions] THEN STRIP_TAC THEN
    REWRITE_TAC [DISTINCT_DISTINCT_OF_ODD] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUPPORT_DISTINCT_OF_ODD,
      FIRST_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.SYM th)])) THEN
      MATCH_MP_TAC NSUM_DISTINCT_OF_ODD] THEN
    ASM_REWRITE_TAC [] THEN
    X_GEN_TAC ([[i:num]]) THEN ASM_CASES_TAC ([[(p:num->num) i = 0]]) THEN
    ASM_REWRITE_TAC [MULT_CLAUSES, LE_0] THEN
    ASM_MESON_TAC [NSUM_BOUND_LEMMA])
  : ExceptT String IO thm).run
#eval DISTINCT_OF_ODD

#eval phrase 28
def ODD_OF_DISTINCT : thm := keep "ODD_OF_DISTINCT" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[~(1 = 0)]])
  let h1 ← ar (← ExceptT.mk [[~(1 = 0)]])
  prove ([[!p. p IN {p | p partitions n /\ !i. p(i) <= 1}
       ==> (odd_of_distinct p) IN
           {p | p partitions n /\ !i. ~(p(i) = 0) ==> ODD i}]])
   (GEN_TAC THEN REWRITE_TAC [partitions, IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC [ODD_ODD_OF_DISTINCT] THEN
    CONJ_TAC THENL [ASM_MESON_TAC [SUPPORT_ODD_OF_DISTINCT], ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC ([[nsum(1..n) (\i. distinct_of_odd(odd_of_distinct p) i * i)]]) THEN
    CONJ_TAC THENL
     [ALL_TAC,
      FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.SYM th)])) THEN
      AP_TERM_TAC THEN ABS_TAC THEN AP_THM_TAC THEN
      ASM_MESON_TAC [DISTINCT_OF_ODD_OF_DISTINCT]] THEN
    CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC NSUM_DISTINCT_OF_ODD THEN
    REWRITE_TAC [ODD_ODD_OF_DISTINCT] THEN
    CONJ_TAC THENL [ASM_MESON_TAC [SUPPORT_ODD_OF_DISTINCT], ALL_TAC] THEN
    X_GEN_TAC ([[i:num]]) THEN REWRITE_TAC [odd_of_distinct] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [LE_0, MULT_CLAUSES] THEN
    REWRITE_TAC [(← HolLight.GSYM NSUM_RMUL)] THEN
    SUBGOAL_THEN ([[FINITE {i:num | p(i) = 1}]]) ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC ([[1..n]]) THEN
      REWRITE_TAC [FINITE_NUMSEG, SUBSET, IN_NUMSEG, IN_ELIM_THM] THEN
      ASM_MESON_TAC [h1],
      ALL_TAC] THEN
    ONCE_REWRITE_TAC [(← HolLight.GSYM (HolLight.REWRITE_CONV [o_DEF] ([[(\j. j) o (\j. 2 EXP j * i)]])))] THEN
    ASM_SIMP_TAC [(← HolLight.GSYM NSUM_IMAGE), INDEX_ODDPART_UNIQUE] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC ([[nsum {i | p(i) = 1} (\j. j)]]) THEN CONJ_TAC THENL
     [MATCH_MP_TAC NSUM_SUBSET_SIMPLE THEN ASM_REWRITE_TAC [] THEN SET_TAC [],
      ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC ([[nsum {i | p(i) = 1} (\j. p(j) * j)]]) THEN CONJ_TAC THENL
     [MATCH_MP_TAC EQ_IMP_LE THEN MATCH_MP_TAC NSUM_EQ THEN
      SIMP_TAC [IN_ELIM_THM, MULT_CLAUSES],
      FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.SYM th)])) THEN
      MATCH_MP_TAC NSUM_SUBSET_SIMPLE THEN
      REWRITE_TAC [FINITE_NUMSEG, SUBSET, IN_NUMSEG, IN_ELIM_THM] THEN
      ASM_MESON_TAC [h2]])
  : ExceptT String IO thm).run
#eval ODD_OF_DISTINCT

/- ------------------------------------------------------------------------- -/
/- Euler's partition theorem:                                                -/
/-                                                                           -/
/- The number of partitions into distinct numbers is equal to the number of  -/
/- partitions into odd numbers (and there are only finitely many of each).   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 29
def EULER_PARTITION_THEOREM : thm := keep "EULER_PARTITION_THEOREM" fun _ => (do
  prove ([[FINITE {p | p partitions n /\ !i. p(i) <= 1} /\
   FINITE {p | p partitions n /\ !i. ~(p(i) = 0) ==> ODD i} /\
   CARD {p | p partitions n /\ !i. p(i) <= 1} =
   CARD {p | p partitions n /\ !i. ~(p(i) = 0) ==> ODD i}]])
   (MATCH_MP_TAC CARD_EQ_LEMMA THEN REWRITE_TAC [FINITE_SUBSET_PARTITIONS] THEN
    MAP_EVERY EXISTS_TAC [([[odd_of_distinct]]), ([[distinct_of_odd]])] THEN
    REWRITE_TAC [ODD_OF_DISTINCT, DISTINCT_OF_ODD] THEN
    CONJ_TAC THEN X_GEN_TAC ([[p:num->num]]) THEN
    REWRITE_TAC [IN_ELIM_THM, partitions] THEN STRIP_TAC THENL
     [MATCH_MP_TAC DISTINCT_OF_ODD_OF_DISTINCT,
      MATCH_MP_TAC ODD_OF_DISTINCT_OF_ODD] THEN
    ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval EULER_PARTITION_THEOREM

end Hol100.Euler
