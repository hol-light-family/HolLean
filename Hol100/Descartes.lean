/- File: Hol100/Descartes.lean
Translation of HOL Light's 100/descartes.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionMultiLib.RealAnalysis
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Binomial SessionLibrary.Permutations SessionLibrary.Wo SessionLibrary.Products SessionLibrary.Floor SessionLibrary.Iter SessionLibrary.Frag SessionLibrary.Prime SessionLibrary.Card SessionLibrary.Matroids SessionMultiLib.Misc SessionLibrary.GroupTheory SessionMultiLib.Vectors SessionMultiLib.Metric SessionMultiLib.Determinants SessionMultiLib.Homology SessionMultiLib.Topology SessionMultiLib.Convex SessionMultiLib.ComplexAlgebra SessionMultiLib.Complexes SessionMultiLib.Paths SessionMultiLib.Polytope SessionMultiLib.Degree SessionMultiLib.Derivatives SessionMultiLib.Integration SessionMultiLib.Measure SessionMultiLib.Canal SessionMultiLib.Transcendentals SessionMultiLib.RealAnalysis
namespace Hol100.Descartes

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def ia (tm : term) : ExceptT String IO thm := ExceptT.mk (INT_ARITH tm)
private def ms (ths : List thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (MESON ths tm)
private def nc (tm : term) : ExceptT String IO thm := ExceptT.mk (num_CONV tm)
private def rg (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_RING tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)
private def sr (tm : term) : ExceptT String IO thm := ExceptT.mk (SET_RULE tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)

/- ========================================================================= -/
/- Rob Arthan's "Descartes's Rule of Signs by an Easy Induction".            -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Multivariate/realanalysis.ml";;
#eval SessionMultiLib.RealAnalysis.ensureRealAnalysis

/- ------------------------------------------------------------------------- -/
/- A couple of handy lemmas.                                                 -/
/- ------------------------------------------------------------------------- -/

#eval phrase 2
def OPPOSITE_SIGNS : thm := keep "OPPOSITE_SIGNS" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[a * b < &0 <=> &0 < a * --b]])
  prove ([[!a b:real. a * b < &0 <=> &0 < a /\ b < &0 \/ a < &0 /\ &0 < b]])
   (REWRITE_TAC [h1, REAL_MUL_POS_LT] THEN
    REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval OPPOSITE_SIGNS

#eval phrase 3
def VARIATION_SET_FINITE : thm := keep "VARIATION_SET_FINITE" fun _ => (do
  let h1 ← sr (← ExceptT.mk [[{p,q | p IN s /\ q IN t /\ R p q} =
    {p,q | p IN s /\ q IN {q | q IN t /\ R p q}}]])
  prove ([[FINITE s ==> FINITE {p,q | p IN s /\ q IN s /\ P p q}]])
   (REWRITE_TAC [h1] THEN
    SIMP_TAC [FINITE_PRODUCT_DEPENDENT, FINITE_RESTRICT])
  : ExceptT String IO thm).run
#eval VARIATION_SET_FINITE

/- ------------------------------------------------------------------------- -/
/- Variation in a sequence of coefficients.                                  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 4
def variation : thm := keep "variation" fun _ => new_definition
 [[variation s (a:num->real) =
     CARD {(p,q) | p IN s /\ q IN s /\ p < q /\
                   a(p) * a(q) < &0 /\
                   !i. i IN s /\ p < i /\ i < q ==> a(i) = &0 }]]
#eval variation

#eval phrase 5
def VARIATION_EQ : thm := keep "VARIATION_EQ" fun _ => (do
  prove ([[!a b s. (!i. i IN s ==> a i = b i) ==> variation s a = variation s b]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [variation] THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, FORALL_PAIR_THM, IN_ELIM_PAIR_THM] THEN
    ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval VARIATION_EQ

#eval phrase 6
def VARIATION_SUBSET : thm := keep "VARIATION_SUBSET" fun _ => (do
  prove ([[!a s t. t SUBSET s /\ (!i. i IN (s DIFF t) ==> a i = &0)
           ==> variation s a = variation t a]])
   (REWRITE_TAC [IN_DIFF, SUBSET] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [variation] THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, FORALL_PAIR_THM, IN_ELIM_PAIR_THM] THEN
    ASM_MESON_TAC [REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_LT_REFL])
  : ExceptT String IO thm).run
#eval VARIATION_SUBSET

#eval phrase 7
def VARIATION_SPLIT : thm := keep "VARIATION_SPLIT" fun _ => (do
  let h1 ← tt (← ExceptT.mk [[~(a /\ b) <=> ~b \/ ~a]])
  prove ([[!a s n.
        FINITE s /\ n IN s /\ ~(a n = &0)
        ==> variation s a = variation {i | i IN s /\ i <= n} a +
                            variation {i | i IN s /\ n <= i} a]])
   (REWRITE_TAC [variation] THEN REPEAT STRIP_TAC THEN
    CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC CARD_UNION_EQ THEN
    ASM_SIMP_TAC [VARIATION_SET_FINITE, FINITE_RESTRICT] THEN
    REWRITE_TAC [EXTENSION, FORALL_PAIR_THM] THEN CONJ_TAC THENL
     [REWRITE_TAC [IN_INTER, NOT_IN_EMPTY, IN_ELIM_PAIR_THM, IN_NUMSEG] THEN
      REWRITE_TAC [IN_ELIM_THM] THEN ARITH_TAC,
      REWRITE_TAC [IN_UNION, IN_ELIM_PAIR_THM, IN_NUMSEG] THEN
      REPEAT GEN_TAC THEN EQ_TAC THENL
       [STRIP_TAC,
        STRIP_TAC THEN FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPEC ([[n:num]]) th) THEN ASM_REWRITE_TAC [] THEN ASSUME_TAC th)) THEN
        SIMP_TAC [h1] THEN MATCH_MP_TAC MONO_OR] THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [IN_ELIM_THM]) THEN
      ASM_REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      TRY (FIRST_ASSUM MATCH_MP_TAC) THEN
      FIRST_ASSUM (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPEC ([[n:num]]) th) THEN ASM_REWRITE_TAC [])) THEN
      ASM_ARITH_TAC])
  : ExceptT String IO thm).run
#eval VARIATION_SPLIT

#eval phrase 8
def VARIATION_SPLIT_NUMSEG : thm := keep "VARIATION_SPLIT_NUMSEG" fun _ => (do
  let h1 ← tt (← ExceptT.mk [[a /\ b /\ c ==> d <=> b /\ c ==> a ==> d]])
  prove ([[!a m n p. n IN m..p /\ ~(a n = &0)
             ==> variation(m..p) a = variation(m..n) a + variation(n..p) a]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [h1] VARIATION_SPLIT)) THEN
    REWRITE_TAC [FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
    BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_NUMSEG] THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [IN_NUMSEG]) THEN ASM_ARITH_TAC)
  : ExceptT String IO thm).run
#eval VARIATION_SPLIT_NUMSEG

#eval phrase 9
def VARIATION_1 : thm := keep "VARIATION_1" fun _ => (do
  let h2 ← ms [CARD_CLAUSES] (← ExceptT.mk [[s = {} ==> CARD s = 0]])
  let h1 ← ar (← ExceptT.mk [[p:num = n /\ q = n /\ p < q /\ X <=> F]])
  prove ([[!a n. variation {n} a = 0]])
   (REWRITE_TAC [variation, IN_SING] THEN
    REWRITE_TAC [h1] THEN
    MATCH_MP_TAC h2 THEN
    REWRITE_TAC [EXTENSION, FORALL_PAIR_THM, IN_ELIM_PAIR_THM, NOT_IN_EMPTY])
  : ExceptT String IO thm).run
#eval VARIATION_1

#eval phrase 10
def VARIATION_2 : thm := keep "VARIATION_2" fun _ => (do
  let h6 ← ms [CARD_CLAUSES] (← ExceptT.mk [[s = {} ==> CARD s = 0]])
  let h5 ← sr (← ExceptT.mk [[{p,q | p = a /\ q = b} = {(a,b)}]])
  let h4 ← ar (← ExceptT.mk [[(i:num = m \/ i = n) /\ m < i /\ i < n <=> F]])
  let h3 ← ms [] (← ExceptT.mk [[(p = m /\ q = n) /\ X p q <=>
                         (p = m /\ q = n) /\ X m n]])
  let h2 ← ar (← ExceptT.mk [[m:num < n
      ==> ((p = m \/ p = n) /\ (q = m \/ q = n) /\ p < q <=>
           p = m /\ q = n)]])
  let h1 ← tt (← ExceptT.mk [[a /\ b /\ c /\ d /\ e <=> (a /\ b /\ c) /\ d /\ e]])
  prove ([[!a m n. variation {m,n} a = if a(m) * a(n) < &0 then 1 else 0]])
   (GEN_TAC THEN MATCH_MP_TAC WLOG_LT THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC [INSERT_AC, VARIATION_1, (← HolLight.GSYM REAL_NOT_LE), REAL_LE_SQUARE],
      REWRITE_TAC [INSERT_AC, REAL_MUL_SYM],
      REPEAT STRIP_TAC THEN REWRITE_TAC [variation, IN_INSERT, NOT_IN_EMPTY] THEN
      ONCE_REWRITE_TAC [h1] THEN
      ASM_SIMP_TAC [h2] THEN
      REWRITE_TAC [h3] THEN
      REWRITE_TAC [h4] THEN
      ASM_CASES_TAC ([[a m * a(n:num) < &0]]) THEN ASM_REWRITE_TAC [] THENL
       [REWRITE_TAC [h5] THEN
        SIMP_TAC [CARD_CLAUSES, FINITE_RULES, NOT_IN_EMPTY, ARITH],
        MATCH_MP_TAC h6 THEN
        SIMP_TAC [EXTENSION, FORALL_PAIR_THM, IN_ELIM_PAIR_THM, NOT_IN_EMPTY]]])
  : ExceptT String IO thm).run
#eval VARIATION_2

#eval phrase 11
def VARIATION_3 : thm := keep "VARIATION_3" fun _ => (do
  prove ([[!a m n p.
        m < n /\ n < p
        ==> variation {m,n,p} a = if a(n) = &0 then variation{m,p} a
                                  else variation {m,n} a + variation{n,p} a]])
   (REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
     [MATCH_MP_TAC VARIATION_SUBSET THEN HolLight.ASM SET_TAC [],
      MP_TAC (← HolLight.ISPECL [([[a:num->real]]), ([[{m:num,n,p}]]), ([[n:num]])] VARIATION_SPLIT) THEN
      ASM_SIMP_TAC [FINITE_INSERT, FINITE_EMPTY, IN_INSERT, NOT_IN_EMPTY] THEN
      DISCH_THEN SUBST1_TAC THEN BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_INSERT, NOT_IN_EMPTY] THEN
      ASM_ARITH_TAC])
  : ExceptT String IO thm).run
#eval VARIATION_3

#eval phrase 12
def VARIATION_OFFSET : thm := keep "VARIATION_OFFSET" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[y < &0 ==> x = y ==> x < &0]])
  prove ([[!p m n a. variation(m+p..n+p) a = variation(m..n) (\i. a(i + p))]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [variation] THEN
    MATCH_MP_TAC BIJECTIONS_CARD_EQ THEN MAP_EVERY EXISTS_TAC [([[\(i:num,j). i - p,j - p]]), ([[\(i:num,j). i + p,j + p]])] THEN
    REWRITE_TAC [FORALL_IN_GSPEC] THEN REWRITE_TAC [IN_ELIM_PAIR_THM] THEN
    SIMP_TAC [VARIATION_SET_FINITE, FINITE_NUMSEG] THEN
    REWRITE_TAC [IN_NUMSEG, PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN TRY ASM_ARITH_TAC THENL
     [FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h1) THEN
      BINOP_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC,
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC,
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[i - p:num]])) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC, MATCH_MP_TAC EQ_IMP] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC])
  : ExceptT String IO thm).run
#eval VARIATION_OFFSET

/- ------------------------------------------------------------------------- -/
/- The crucial lemma (roughly Lemma 2 in the paper).                         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 13
def ARTHAN_LEMMA : thm := keep "ARTHAN_LEMMA" fun _ => (do
  let h18 ← ia (← ExceptT.mk [[x:int = y + --z <=> x + z = y]])
  let h17 ← ar (← ExceptT.mk [[1 < p ==> ~(p = 1)]])
  let h16 ← nc (← ExceptT.mk [[1]])
  let h15 ← nc (← ExceptT.mk [[1]])
  let h14 ← rr (← ExceptT.mk [[~(ap = &0) ==> s = &0 ==> ~(s + ap = &0)]])
  let h13 ← ar (← ExceptT.mk [[1 < p ==> 0 < p /\ 0 <= p]])
  let h12 ← ar (← ExceptT.mk [[1 < p ==> 0 < p /\ 0 <= p]])
  let h11 ← ar (← ExceptT.mk [[0 < i ==> 0 + 1 <= i]])
  let h10 ← ia (← ExceptT.mk [[a + b:int = c + d <=> d = (a + b) - c]])
  let h9 ← ia (← ExceptT.mk [[a + b:int = c + d ==> c = (a + b) - d]])
  let h8 ← ar (← ExceptT.mk [[2 <= n ==> n - 1 + 1 = n /\ n - 1 - 1 + 1 = n - 1]])
  let h7 ← ar (← ExceptT.mk [[2 = 1 + 1]])
  let h6 ← ar (← ExceptT.mk [[0 + 1 <= n + 1]])
  let h5 ← ar (← ExceptT.mk [[2 <= n ==> ~(n = 1) /\ n - 1 + 1 = n]])
  let h4 ← tt (← ExceptT.mk [[a ==> ~(b /\ c /\ ~d) <=> a /\ b /\ c ==> d]])
  let h3 ← ar (← ExceptT.mk [[2 <= n ==> 1 < n]])
  let h2 ← nc (← ExceptT.mk [[1]])
  let h1 ← ar (← ExceptT.mk [[~(n = 0) ==> n = 1 \/ 2 <= n]])
  prove ([[!n a b.
        ~(a n = &0) /\ (b n = &0) /\ (!m. sum(0..m) a = b m)
        ==> ?d. ODD d /\ variation (0..n) a = variation (0..n) b + d]])
   (MATCH_MP_TAC num_WF THEN X_GEN_TAC ([[n:num]]) THEN
    DISCH_THEN (LABEL_TAC "*") THEN
    REPEAT STRIP_TAC THEN ASM_CASES_TAC ([[n = 0]]) THENL
     [FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[0]])) THEN
      ASM_REWRITE_TAC [SUM_SING_NUMSEG] THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    FIRST_ASSUM (DISJ_CASES_TAC o HolLight.MATCH_MP h1) THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN EXISTS_TAC ([[1]]) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV NUMSEG_CONV) THEN
      REWRITE_TAC [VARIATION_2, OPPOSITE_SIGNS] THEN
      FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPEC ([[0]]) th) THEN MP_TAC (← HolLight.SPEC ([[1]]) th))) THEN
      SIMP_TAC [h2, SUM_CLAUSES_NUMSEG] THEN
      CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THEN REWRITE_TAC [] THEN
      ASM_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[?p. 1 < p /\ p <= n /\ ~(a p = &0)]]) MP_TAC THENL
     [ASM_MESON_TAC [h3, LE_REFL],
      GEN_REWRITE_TAC HolLight.LAND_CONV [num_WOP] THEN
      REWRITE_TAC [h4] THEN
      STRIP_TAC] THEN
    REMOVE_THEN "*" (MP_TAC o HolLight.SPEC ([[n - 1]])) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN DISCH_THEN (MP_TAC o HolLight.SPECL [([[(\i. if i + 1 = 1 then a 0 + a 1 else a(i + 1)):num->real]]),
      ([[(\i. b(i + 1)):num->real]])]) THEN
    ASM_SIMP_TAC [h5] THEN
    REWRITE_TAC [(← HolLight.GSYM (← HolLight.SPEC ([[1]]) VARIATION_OFFSET))] THEN ANTS_TAC THENL
     [X_GEN_TAC ([[m:num]]) THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC ([[sum(0..m+1) a]]) THEN CONJ_TAC THENL
       [SIMP_TAC [SUM_CLAUSES_LEFT, LE_0, h6] THEN
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [REAL_ADD_ASSOC] THEN
        AP_TERM_TAC THEN REWRITE_TAC [h7, SUM_OFFSET] THEN
        MATCH_MP_TAC SUM_EQ_NUMSEG THEN ARITH_TAC,
        ASM_REWRITE_TAC []],
      ABBREV_TAC ([[a':num->real = \m. if m = 1 then a 0 + a 1 else a m]]) THEN
      ASM_SIMP_TAC [h8] THEN
      CONV_TAC NUM_REDUCE_CONV] THEN
    SUBGOAL_THEN ([[variation (1..n) a' = variation {1,p} a' + variation (p..n) a /\
    variation (0..n) a = variation {0,1,p} a + variation (p..n) a]]) (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THEN MATCH_MP_TAC EQ_TRANS THENL
       [EXISTS_TAC ([[variation(1..p) a' + variation(p..n) a']]),
        EXISTS_TAC ([[variation(0..p) a + variation(p..n) a]])] THEN
      (CONJ_TAC THENL
        [MATCH_MP_TAC VARIATION_SPLIT_NUMSEG THEN EXPAND_TAC "a'" THEN
         REWRITE_TAC [IN_NUMSEG] THEN ASM_ARITH_TAC,
         BINOP_TAC THENL
          [MATCH_MP_TAC VARIATION_SUBSET, MATCH_MP_TAC VARIATION_EQ] THEN
         EXPAND_TAC "a'" THEN REWRITE_TAC [INSERT_SUBSET, EMPTY_SUBSET] THEN
         REWRITE_TAC [IN_NUMSEG] THEN TRY (GEN_TAC THEN ASM_ARITH_TAC) THEN
         (CONJ_TAC THENL [ASM_ARITH_TAC, REWRITE_TAC [IN_DIFF]]) THEN
         REWRITE_TAC [IN_NUMSEG, IN_INSERT, NOT_IN_EMPTY] THEN
         REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN
         TRY (FIRST_X_ASSUM MATCH_MP_TAC) THEN ASM_ARITH_TAC]),
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[d:num]]) (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC [(← HolLight.GSYM INT_OF_NUM_EQ), (← HolLight.GSYM INT_OF_NUM_ADD)] THEN
    DISCH_THEN (ASSUME_TAC o HolLight.MATCH_MP h9) THEN
    REWRITE_TAC [h10] THEN
    ASM_CASES_TAC ([[a 0 + a 1 = &0]]) THENL
     [SUBGOAL_THEN ([[!i. 0 < i /\ i < p ==> b i = &0]]) ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM (SUBST1_TAC o HolLight.SYM o HolLight.SPEC ([[i:num]])) THEN
        ASM_SIMP_TAC [SUM_CLAUSES_LEFT, LE_0,
                     h11] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        ASM_REWRITE_TAC [REAL_ADD_ASSOC, REAL_ADD_LID] THEN
        MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC,
        ALL_TAC] THEN
      SUBGOAL_THEN ([[(b:num->real) p = a p]]) ASSUME_TAC THENL
       [FIRST_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM th)])) THEN
        SIMP_TAC [SUM_CLAUSES_RIGHT, (← HolLight.ASSUME ([[1 < p]])),
                   h12] THEN
        ASM_REWRITE_TAC [REAL_EQ_ADD_RCANCEL_0] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC,
        ALL_TAC] THEN
      SUBGOAL_THEN ([[variation(0..n) b = variation {0,p} b + variation(1..n) b]]) SUBST1_TAC THENL
       [MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC ([[variation(0..p) b + variation(p..n) b]]) THEN CONJ_TAC THENL
         [MATCH_MP_TAC VARIATION_SPLIT_NUMSEG THEN REWRITE_TAC [IN_NUMSEG] THEN
          CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
          FIRST_ASSUM (SUBST1_TAC o HolLight.SYM o HolLight.SPEC ([[p:num]])) THEN
          SIMP_TAC [SUM_CLAUSES_RIGHT, (← HolLight.ASSUME ([[1 < p]])),
                   h13] THEN
          ASM_REWRITE_TAC [] THEN
          FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h14) THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC,
          BINOP_TAC THENL [ALL_TAC, CONV_TAC HolLight.SYM_CONV] THEN
          MATCH_MP_TAC VARIATION_SUBSET THEN
          REWRITE_TAC [SUBSET, IN_DIFF, IN_NUMSEG, IN_INSERT, NOT_IN_EMPTY] THEN
          (CONJ_TAC THENL [ASM_ARITH_TAC, REPEAT STRIP_TAC]) THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC],
        ALL_TAC],
      SUBGOAL_THEN ([[variation(0..n) b = variation {0,1} b + variation(1..n) b]]) SUBST1_TAC THENL
       [MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC ([[variation(0..1) b + variation(1..n) b]]) THEN CONJ_TAC THENL
         [MATCH_MP_TAC VARIATION_SPLIT_NUMSEG THEN REWRITE_TAC [IN_NUMSEG] THEN
          CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
          FIRST_ASSUM (SUBST1_TAC o HolLight.SYM o HolLight.SPEC ([[1]])) THEN
          SIMP_TAC [SUM_CLAUSES_NUMSEG, h15] THEN
          CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC [],
          AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC VARIATION_SUBSET THEN
          REWRITE_TAC [SUBSET, IN_DIFF, IN_NUMSEG, IN_INSERT, NOT_IN_EMPTY] THEN
          ARITH_TAC],
        SUBGOAL_THEN ([[(b:num->real) 1 = a 0 + a 1]]) ASSUME_TAC THENL
         [FIRST_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM th)])) THEN
          SIMP_TAC [h16, SUM_CLAUSES_NUMSEG] THEN
          CONV_TAC NUM_REDUCE_CONV,
          ALL_TAC]]] THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[0]]))) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC [SUM_SING_NUMSEG] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC [(← HolLight.GSYM INT_OF_NUM_ADD)] THEN
    ASM_SIMP_TAC [VARIATION_3, ARITH, OPPOSITE_SIGNS] THEN COND_CASES_TAC THEN
    REWRITE_TAC [VARIATION_2, OPPOSITE_SIGNS, REAL_LT_REFL] THEN
    EXPAND_TAC "a'" THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC [h17, REAL_LT_REFL] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC (HolLight.BINDER_CONV (HolLight.RAND_CONV (HolLight.RAND_CONV INT_POLY_CONV))) THEN
    REWRITE_TAC [h18] THEN
    REWRITE_TAC [INT_OF_NUM_ADD, INT_OF_NUM_EQ] THEN
    ONCE_REWRITE_TAC [CONJ_SYM] THEN ASM_REWRITE_TAC [UNWIND_THM2] THEN
    ASM_REWRITE_TAC [ODD_ADD, ARITH_ODD, ARITH_EVEN] THEN ASM_REAL_ARITH_TAC)
  : ExceptT String IO thm).run
#eval ARTHAN_LEMMA

/- ------------------------------------------------------------------------- -/
/- Relate even-ness or oddity of variation to signs of end coefficients.     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 14
def VARIATION_OPPOSITE_ENDS : thm := keep "VARIATION_OPPOSITE_ENDS" fun _ => (do
  prove ([[!a m n.
    m <= n /\ ~(a m = &0) /\ ~(a n = &0)
    ==> (ODD(variation(m..n) a) <=> a m * a n < &0)]])
   (REPEAT GEN_TAC THEN WF_INDUCT_TAC ([[n - m:num]]) THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC ([[!i:num. m < i /\ i < n ==> a i = &0]]) THENL
     [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC ([[ODD(variation {m,n} a)]]) THEN
      CONJ_TAC THENL
       [AP_TERM_TAC THEN MATCH_MP_TAC VARIATION_SUBSET THEN
        ASM_REWRITE_TAC [INSERT_SUBSET, IN_NUMSEG, IN_DIFF, EMPTY_SUBSET] THEN
        REWRITE_TAC [LE_REFL, IN_INSERT, NOT_IN_EMPTY] THEN
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC,
        REWRITE_TAC [VARIATION_2] THEN COND_CASES_TAC THEN
        ASM_REWRITE_TAC [ARITH]],
      FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [NOT_FORALL_THM]) THEN
      REWRITE_TAC [NOT_IMP] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[p:num]]) STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPECL [([[n:num]]), ([[p:num]])] th) THEN
          MP_TAC (← HolLight.SPECL [([[p:num]]), ([[m:num]])] th))) THEN
      ASM_SIMP_TAC [LT_IMP_LE] THEN
      REPEAT (ANTS_TAC THENL [ASM_ARITH_TAC, DISCH_TAC]) THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC ([[ODD(variation(m..p) a + variation(p..n) a)]]) THEN CONJ_TAC THENL
       [AP_TERM_TAC THEN MATCH_MP_TAC VARIATION_SPLIT_NUMSEG THEN
        ASM_SIMP_TAC [LT_IMP_LE, IN_NUMSEG],
        ASM_REWRITE_TAC [ODD_ADD, OPPOSITE_SIGNS] THEN ASM_REAL_ARITH_TAC]])
  : ExceptT String IO thm).run
#eval VARIATION_OPPOSITE_ENDS

/- ------------------------------------------------------------------------- -/
/- Polynomial with odd variation has at least one positive root.             -/
/- This is the only "analytical" part of the proof.                          -/
/- ------------------------------------------------------------------------- -/

#eval phrase 15
def REAL_POLYFUN_SGN_AT_INFINITY : thm := keep "REAL_POLYFUN_SGN_AT_INFINITY" fun _ => (do
  let lemma ← prove ([[abs(x) < abs(y) ==> real_sgn(x + y) = real_sgn y]])
     (REWRITE_TAC [real_sgn] THEN REAL_ARITH_TAC2)
  prove ([[!a n. ~(a n = &0)
         ==> ?B. &0 < B /\
                 !x. B <= abs x
                     ==> real_sgn(sum(0..n) (\i. a i * x pow i)) =
                         real_sgn(a n * x pow n)]])
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC ([[n = 0]]) THENL
     [EXISTS_TAC ([[&1]]) THEN ASM_REWRITE_TAC [REAL_LT_01, SUM_SING_NUMSEG],
      ALL_TAC] THEN
    ABBREV_TAC ([[B = sum (0..n-1) (\i. abs(a i)) / abs(a n)]]) THEN
    SUBGOAL_THEN ([[&0 <= B]]) ASSUME_TAC THENL
     [EXPAND_TAC "B" THEN SIMP_TAC [REAL_LE_DIV, REAL_ABS_POS, SUM_POS_LE_NUMSEG],
      ALL_TAC] THEN
    EXISTS_TAC ([[&1 + B]]) THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    X_GEN_TAC ([[x:real]]) THEN STRIP_TAC THEN
    ASM_SIMP_TAC [SUM_CLAUSES_RIGHT, LE_0, LE_1] THEN MATCH_MP_TAC lemma THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC ([[sum(0..n-1) (\i. abs(a i)) * abs x pow (n - 1)]]) THEN
    CONJ_TAC THENL
     [REWRITE_TAC [(← HolLight.GSYM SUM_RMUL)] THEN MATCH_MP_TAC SUM_ABS_LE THEN
      REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG] THEN
      X_GEN_TAC ([[i:num]]) THEN STRIP_TAC THEN REWRITE_TAC [REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [REAL_ABS_POS, REAL_ABS_POW] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC,
      SUBGOAL_THEN ([[(x:real) pow n = x * x pow (n - 1)]]) SUBST1_TAC THENL
       [SIMP_TAC [(← HolLight.GSYM (← HolLight.CONJUNCT2 real_pow))] THEN AP_TERM_TAC THEN ASM_ARITH_TAC,
        REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_POW, REAL_MUL_ASSOC] THEN
        MATCH_MP_TAC REAL_LT_RMUL THEN CONJ_TAC THENL
         [ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
          ASM_SIMP_TAC [(← HolLight.GSYM REAL_LT_LDIV_EQ), (← HolLight.GSYM REAL_ABS_NZ)] THEN
          ASM_REAL_ARITH_TAC,
          MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC]]])
  : ExceptT String IO thm).run
#eval REAL_POLYFUN_SGN_AT_INFINITY

#eval phrase 16
def REAL_POLYFUN_HAS_POSITIVE_ROOT : thm := keep "REAL_POLYFUN_HAS_POSITIVE_ROOT" fun _ => (do
  prove ([[!a n. a 0 < &0 /\ &0 < a n
         ==> ?x. &0 < x /\ sum(0..n) (\i. a i * x pow i) = &0]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[?x. &0 < x /\ &0 <= sum(0..n) (\i. a i * x pow i)]]) STRIP_ASSUME_TAC THENL
     [MP_TAC (← HolLight.ISPECL [([[a:num->real]]), ([[n:num]])] REAL_POLYFUN_SGN_AT_INFINITY) THEN
      ASM_SIMP_TAC [REAL_LT_IMP_NZ] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC ([[x:real]]) THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o HolLight.SPEC ([[x:real]]))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      SUBGOAL_THEN ([[real_sgn(a n * x pow n) = &1]]) SUBST1_TAC THEN
      ASM_SIMP_TAC [REAL_SGN_EQ, REAL_LT_MUL, REAL_POW_LT, real_gt] THEN
      REWRITE_TAC [REAL_LT_IMP_LE],
      MP_TAC (← HolLight.ISPECL [([[\x. sum(0..n) (\i. a i * x pow i)]]),
                     ([[&0]]), ([[x:real]]), ([[&0]])] REAL_IVT_INCREASING) THEN
      ASM_SIMP_TAC [REAL_LT_IMP_LE, IN_REAL_INTERVAL,
                   REAL_POW_ZERO, COND_RAND] THEN
      REWRITE_TAC [REAL_MUL_RID, REAL_MUL_RZERO, SUM_DELTA, IN_NUMSEG, LE_0] THEN
      ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN ANTS_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUM THEN
        REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN
        REWRITE_TAC [REAL_CONTINUOUS_ON_ID],
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[y:real]]) THEN
        SIMP_TAC [REAL_LT_LE] THEN ASM_CASES_TAC ([[y:real = &0]]) THEN
        ASM_SIMP_TAC [REAL_POW_ZERO, COND_RAND, REAL_MUL_RZERO, REAL_MUL_RID] THEN
        REWRITE_TAC [SUM_DELTA, IN_NUMSEG, LE_0] THEN ASM_REAL_ARITH_TAC]])
  : ExceptT String IO thm).run
#eval REAL_POLYFUN_HAS_POSITIVE_ROOT

#eval phrase 17
def ODD_VARIATION_POSITIVE_ROOT : thm := keep "ODD_VARIATION_POSITIVE_ROOT" fun _ => (do
  let h9 ← rr (← ExceptT.mk [[(aq * xp) * api / aq * xi:real = (aq / aq) * api * (xp * xi)]])
  let h8 ← rg (← ExceptT.mk [[!a. y = a * x ==> x = &0 ==> y = &0]])
  let h7 ← rr (← ExceptT.mk [[x < &0 <=> &0 < --x]])
  let h6 ← ar (← ExceptT.mk [[p:num <= q ==> p + q - p = q]])
  let h5 ← ms [] (← ExceptT.mk [[ODD p ==> p = q ==> ODD q]])
  let h4 ← tt (← ExceptT.mk [[p /\ ~q ==> r <=> p /\ ~r ==> q]])
  let h3 ← tt (← ExceptT.mk [[p ==> ~(q /\ r) <=> p /\ q ==> ~r]])
  let h2 ← tt (← ExceptT.mk [[a ==> b ==> c <=> a ==> a /\ b ==> c]])
  let h1 ← ms [] (← ExceptT.mk [[((!i. P i ==> Q i) ==> F) ==> ?i. P i /\ ~Q i]])
  prove ([[!a n. ODD(variation(0..n) a)
         ==> ?x. &0 < x /\ sum(0..n) (\i. a i * x pow i) = &0]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[?M. !i. i IN 0..n /\ ~(a i = &0) ==> i <= M]]) MP_TAC THENL
     [EXISTS_TAC ([[n:num]]) THEN SIMP_TAC [IN_NUMSEG], ALL_TAC] THEN
    SUBGOAL_THEN ([[?i. i IN 0..n /\ ~(a i = &0)]]) MP_TAC THENL
     [MATCH_MP_TAC h1 THEN
      DISCH_TAC THEN SUBGOAL_THEN ([[variation (0..n) a = variation {0} a]]) (fun th => SUBST_ALL_TAC th THEN ASM_MESON_TAC [VARIATION_1, ODD]) THEN
      MATCH_MP_TAC VARIATION_SUBSET THEN
      ASM_SIMP_TAC [IN_DIFF] THEN REWRITE_TAC [IN_NUMSEG, SING_SUBSET, LE_0],
      ALL_TAC] THEN
    ONCE_REWRITE_TAC [h2] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [num_WOP] THEN REWRITE_TAC [num_MAX] THEN
    REWRITE_TAC [h3, IN_NUMSEG] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[p:num]]) STRIP_ASSUME_TAC) THEN
    ONCE_REWRITE_TAC [h4] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[q:num]]) STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN ([[p:num <= q]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [NOT_LT], ALL_TAC] THEN
    SUBGOAL_THEN ([[(a:num->real) p * a q < &0]]) ASSUME_TAC THENL
     [ASM_SIMP_TAC [(← HolLight.GSYM VARIATION_OPPOSITE_ENDS)] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h5) THEN
      MATCH_MP_TAC VARIATION_SUBSET THEN
      REWRITE_TAC [SUBSET_NUMSEG, IN_NUMSEG, IN_DIFF, DE_MORGAN_THM] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC, REPEAT STRIP_TAC] THEN
      FIRST_X_ASSUM (fun th => MATCH_MP_TAC th THEN ASM_ARITH_TAC),
      ALL_TAC] THEN
    MP_TAC (← HolLight.ISPECL [([[\i. (a:num->real)(p + i) / a q]]), ([[q - p:num]])] REAL_POLYFUN_HAS_POSITIVE_ROOT) THEN
    ASM_SIMP_TAC [ADD_CLAUSES, h6] THEN
    ANTS_TAC THENL
     [REWRITE_TAC [real_div, OPPOSITE_SIGNS, REAL_MUL_POS_LT] THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [OPPOSITE_SIGNS]) THEN
      REWRITE_TAC [h7, (← HolLight.GSYM REAL_INV_NEG)] THEN
      REWRITE_TAC [REAL_LT_INV_EQ] THEN REAL_ARITH_TAC2,
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[x:real]]) THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC [] THEN MATCH_MP_TAC h8 THEN
    EXISTS_TAC ([[(a:num->real) q * x pow p]]) THEN
    REWRITE_TAC [(← HolLight.GSYM SUM_LMUL), h9] THEN
    ASM_CASES_TAC ([[(a:num->real) q = &0]]) THENL
     [ASM_MESON_TAC [REAL_MUL_LZERO, REAL_LT_REFL], ALL_TAC] THEN
    ASM_SIMP_TAC [(← HolLight.GSYM REAL_POW_ADD), REAL_DIV_REFL, REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN MP_TAC (← HolLight.SPEC ([[p:num]]) SUM_OFFSET) THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
        pure (REWRITE_TAC [(← HolLight.GSYM th)])) THEN
    MATCH_MP_TAC SUM_SUPERSET THEN
    REWRITE_TAC [SUBSET_NUMSEG, IN_NUMSEG, IN_DIFF, DE_MORGAN_THM] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC, REPEAT STRIP_TAC] THEN
    REWRITE_TAC [REAL_ENTIRE] THEN DISJ1_TAC THEN
    FIRST_X_ASSUM (fun th => MATCH_MP_TAC th THEN ASM_ARITH_TAC))
  : ExceptT String IO thm).run
#eval ODD_VARIATION_POSITIVE_ROOT

/- ------------------------------------------------------------------------- -/
/- Define root multiplicities.                                               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 18
def multiplicity : thm := keep "multiplicity" fun _ => new_definition
 [[multiplicity f r =
        @k. ?a n. ~(sum(0..n) (\i. a i * r pow i) = &0) /\
                  !x. f(x) = (x - r) pow k * sum(0..n) (\i. a i * x pow i)]]
#eval multiplicity

#eval phrase 19
def MULTIPLICITY_UNIQUE : thm := keep "MULTIPLICITY_UNIQUE" fun _ => (do
  let lemma ← prove ([[!i j f g. f real_continuous_on (:real) /\ g real_continuous_on (:real) /\
               ~(f r = &0) /\ ~(g r = &0)
               ==> (!x. (x - r) pow i * f(x) = (x - r) pow j * g(x))
                   ==> j = i]])
     (MATCH_MP_TAC WLOG_LT THEN
      REWRITE_TAC [] THEN CONJ_TAC THENL [MESON_TAC [], ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [([[i:num]]), ([[j:num]])] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC (← tt (← ExceptT.mk [[F ==> p]])) THEN
      MP_TAC (← HolLight.ISPECL [([[atreal r]]), ([[f:real->real]]),
                     ([[(f:real->real) r]]), ([[&0]])] REALLIM_UNIQUE) THEN
      ASM_REWRITE_TAC [TRIVIAL_LIMIT_ATREAL] THEN CONJ_TAC THENL
       [REWRITE_TAC [(← HolLight.GSYM REAL_CONTINUOUS_ATREAL)] THEN
        ASM_MESON_TAC [REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT, REAL_OPEN_UNIV,
                      IN_UNIV],
        MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
        EXISTS_TAC ([[\x:real. (x - r) pow (j - i) * g x]]) THEN
        REWRITE_TAC [] THEN CONJ_TAC THENL
         [REWRITE_TAC [EVENTUALLY_ATREAL] THEN EXISTS_TAC ([[&1]]) THEN
          REWRITE_TAC [REAL_LT_01, (← rr (← ExceptT.mk [[&0 < abs(x - r) <=> ~(x = r)]]))] THEN
          X_GEN_TAC ([[x:real]]) THEN STRIP_TAC THEN MATCH_MP_TAC (← rg (← ExceptT.mk [[!a. a * x = a * y /\ ~(a = &0) ==> x = y]])) THEN
          EXISTS_TAC ([[(x - r:real) pow i]]) THEN
          ASM_REWRITE_TAC [REAL_MUL_ASSOC, (← HolLight.GSYM REAL_POW_ADD), REAL_POW_EQ_0] THEN
          ASM_SIMP_TAC [REAL_SUB_0, (← ar (← ExceptT.mk [[i:num < j ==> i + j - i = j]]))],
          SUBST1_TAC (← rr (← ExceptT.mk [[&0 = &0 * (g:real->real) r]])) THEN
          MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THENL
           [REWRITE_TAC [] THEN MATCH_MP_TAC REALLIM_NULL_POW THEN
            REWRITE_TAC [(← HolLight.GSYM REALLIM_NULL), REALLIM_ATREAL_ID] THEN ASM_ARITH_TAC,
            REWRITE_TAC [(← HolLight.GSYM REAL_CONTINUOUS_ATREAL)] THEN
            ASM_MESON_TAC [REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT,
                          REAL_OPEN_UNIV, IN_UNIV]]]])
  prove ([[!f a r b m k.
        (!x. f(x) = (x - r) pow k * sum(0..m) (\j. b j * x pow j)) /\
        ~(sum(0..m) (\j. b j * r pow j) = &0)
        ==> k = multiplicity f r]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [multiplicity] THEN
    CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    X_GEN_TAC ([[j:num]]) THEN EQ_TAC THEN ASM_SIMP_TAC [LEFT_IMP_EXISTS_THM] THENL
     [REPEAT GEN_TAC THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      MATCH_MP_TAC lemma THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUM THEN
      REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN
      REWRITE_TAC [REAL_CONTINUOUS_ON_ID],
      DISCH_THEN SUBST1_TAC THEN
      MAP_EVERY EXISTS_TAC [([[b:num->real]]), ([[m:num]])] THEN ASM_REWRITE_TAC []])
  : ExceptT String IO thm).run
#eval MULTIPLICITY_UNIQUE

#eval phrase 20
def MULTIPLICITY_WORKS : thm := keep "MULTIPLICITY_WORKS" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[n - (n - 1) - 1 = 0]])
  prove ([[!r n a.
    (?i. i IN 0..n /\ ~(a i = &0))
    ==> ?b m.
        ~(sum(0..m) (\i. b i * r pow i) = &0) /\
        !x. sum(0..n) (\i. a i * x pow i) =
            (x - r) pow multiplicity (\x. sum(0..n) (\i. a i * x pow i)) r *
            sum(0..m) (\i. b i * x pow i)]])
   (REWRITE_TAC [multiplicity] THEN CONV_TAC (HolLight.ONCE_DEPTH_CONV (pureC SELECT_CONV)) THEN
    GEN_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC ([[n:num]]) THEN
    DISCH_TAC THEN X_GEN_TAC ([[a:num->real]]) THEN
    ASM_CASES_TAC ([[(a:num->real) n = &0]]) THENL
     [ASM_CASES_TAC ([[n = 0]]) THEN
      ASM_REWRITE_TAC [NUMSEG_SING, IN_SING, UNWIND_THM2] THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[n - 1]])) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC ([[a:num->real]])) THEN
      ASM_SIMP_TAC [SUM_CLAUSES_RIGHT, LE_0, LE_1] THEN
      REWRITE_TAC [REAL_MUL_LZERO, REAL_ADD_RID] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      FIRST_X_ASSUM (X_CHOOSE_THEN ([[i:num]]) MP_TAC) THEN
      REWRITE_TAC [IN_NUMSEG] THEN STRIP_TAC THEN
      EXISTS_TAC ([[i:num]]) THEN ASM_REWRITE_TAC [] THEN
      ASM_CASES_TAC ([[i:num = n]]) THENL [ASM_MESON_TAC [], ASM_ARITH_TAC],
      ALL_TAC] THEN
    DISCH_THEN ((fun _ => ALL_TAC)) THEN
    ASM_CASES_TAC ([[sum(0..n) (\i. a i * r pow i) = &0]]) THENL
     [ASM_CASES_TAC ([[n = 0]]) THENL
       [UNDISCH_TAC ([[sum (0..n) (\i. a i * r pow i) = &0]]) THEN
        ASM_REWRITE_TAC [NUMSEG_SING, IN_SING, UNWIND_THM2, SUM_SING] THEN
        REWRITE_TAC [real_pow, REAL_MUL_RID] THEN ASM_MESON_TAC [],
        ALL_TAC] THEN
      MP_TAC (← HolLight.GEN ([[x:real]]) (← HolLight.ISPECL [([[a:num->real]]), ([[x:real]]), ([[r:real]]), ([[n:num]])] REAL_SUB_POLYFUN)) THEN ASM_SIMP_TAC [LE_1, REAL_SUB_RZERO] THEN
      ABBREV_TAC ([[b j = sum (j + 1..n) (\i. a i * r pow (i - j - 1))]]) THEN
      DISCH_THEN ((fun _ => ALL_TAC)) THEN
      FIRST_X_ASSUM (ASSUME_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [(← HolLight.GSYM FUN_EQ_THM)]) THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[n - 1]])) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC ([[b:num->real]])) THEN ANTS_TAC THENL
       [EXISTS_TAC ([[n - 1]]) THEN REWRITE_TAC [IN_NUMSEG, LE_REFL, LE_0] THEN
        EXPAND_TAC "b" THEN REWRITE_TAC [] THEN
        ASM_SIMP_TAC [SUB_ADD, LE_1, SUM_SING_NUMSEG, real_pow, REAL_MUL_RID,
                     h1],
        ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[k:num]]) (fun th => EXISTS_TAC ([[SUC k]]) THEN MP_TAC th)) THEN
      REPEAT (MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [real_pow, (← HolLight.GSYM REAL_MUL_ASSOC)],
      MAP_EVERY EXISTS_TAC [([[0]]), ([[a:num->real]]), ([[n:num]])] THEN
      ASM_REWRITE_TAC [real_pow, REAL_MUL_LID]])
  : ExceptT String IO thm).run
#eval MULTIPLICITY_WORKS

#eval phrase 21
def MULTIPLICITY_OTHER_ROOT : thm := keep "MULTIPLICITY_OTHER_ROOT" fun _ => (do
  let h5 ← ar (← ExceptT.mk [[~(n + 1 <= n)]])
  let h4 ← ar (← ExceptT.mk [[0 < n + 1]])
  let h3 ← ar (← ExceptT.mk [[0 < i + 1]])
  let h2 ← ar (← ExceptT.mk [[0 <= n + 1]])
  let h1 ← rg (← ExceptT.mk [[r * x = s * r * y <=> r = &0 \/ s * y = x]])
  prove ([[!a n r s.
    ~(r = s) /\ (?i. i IN 0..n /\ ~(a i = &0))
     ==> multiplicity (\x. (x - r) pow m * sum(0..n) (\i. a i * x pow i)) s =
         multiplicity (\x.  sum(0..n) (\i. a i * x pow i)) s]])
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC) THEN
    CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC MULTIPLICITY_UNIQUE THEN
    REWRITE_TAC [] THEN
    MP_TAC (← HolLight.ISPECL [([[s:real]]), ([[n:num]]), ([[a:num->real]])] MULTIPLICITY_WORKS) THEN
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [([[c:num->real]]), ([[p:num]])] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o HolLight.GSYM)) THEN
    SUBGOAL_THEN ([[?b q. !x. sum(0..q) (\j. b j * x pow j) =
              (x - r) pow m * sum (0..p) (\i. c i * x pow i)]]) MP_TAC THENL
     [ALL_TAC,
      REPEAT (MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC [h1] THEN
      ASM_REWRITE_TAC [REAL_ENTIRE, REAL_POW_EQ_0, REAL_SUB_0]] THEN
    MAP_EVERY (fun t => SPEC_TAC (t, t)) [([[c:num->real]]), ([[p:num]]), ([[m:num]])] THEN
    POP_ASSUM_LIST ((fun _ => ALL_TAC)) THEN INDUCT_TAC THEN REPEAT GEN_TAC THENL
     [MAP_EVERY EXISTS_TAC [([[c:num->real]]), ([[p:num]])] THEN
      ASM_REWRITE_TAC [real_pow, REAL_MUL_LID],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [([[p:num]]), ([[c:num->real]])]) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [([[a:num->real]]), ([[n:num]])] THEN
    DISCH_THEN (ASSUME_TAC o HolLight.GSYM) THEN
    ASM_REWRITE_TAC [real_pow, (← HolLight.GSYM REAL_MUL_ASSOC)] THEN
    EXISTS_TAC ([[\i. (if 0 < i then a(i - 1) else &0) -
                  (if i <= n then r * a i else &0)]]) THEN
    EXISTS_TAC ([[n + 1]]) THEN
    REWRITE_TAC [REAL_SUB_RDISTRIB, SUM_SUB_NUMSEG] THEN X_GEN_TAC ([[x:real]]) THEN
    BINOP_TAC THENL
     [MP_TAC h2 THEN SIMP_TAC [SUM_CLAUSES_LEFT] THEN
      DISCH_THEN ((fun _ => ALL_TAC)) THEN REWRITE_TAC [SUM_OFFSET, LT_REFL] THEN
      REWRITE_TAC [REAL_MUL_LZERO, REAL_ADD_LID, h3] THEN
      REWRITE_TAC [(← HolLight.GSYM SUM_LMUL), ADD_SUB, REAL_POW_ADD, REAL_POW_1],
      SIMP_TAC [SUM_CLAUSES_RIGHT, LE_0, h4] THEN
      REWRITE_TAC [ADD_SUB, h5] THEN
      SIMP_TAC [REAL_MUL_LZERO, REAL_ADD_RID, (← HolLight.GSYM SUM_LMUL)]] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REWRITE_TAC [REAL_MUL_AC])
  : ExceptT String IO thm).run
#eval MULTIPLICITY_OTHER_ROOT

/- ------------------------------------------------------------------------- -/
/- The main lemmas to be applied iteratively.                                -/
/- ------------------------------------------------------------------------- -/

#eval phrase 22
def VARIATION_POSITIVE_ROOT_FACTOR : thm := keep "VARIATION_POSITIVE_ROOT_FACTOR" fun _ => (do
  let h8 ← rr (← ExceptT.mk [[x * y < &0 <=> &0 < x * --y]])
  let h7 ← rr (← ExceptT.mk [[--x * --y:real = x * y]])
  let h6 ← rr (← ExceptT.mk [[(a * x) * (b * x'):real = (x * x') * a * b]])
  let h5 ← ar (← ExceptT.mk [[x':num = x /\ y' = y ==> x' = y' + d ==> x = y + d]])
  let h4 ← ar (← ExceptT.mk [[~(j <= n) ==> ((0 <= i /\ i <= j) /\ i <= n <=> 0 <= i /\ i <= n)]])
  let h3 ← ar (← ExceptT.mk [[j + 1 <= k ==> k - j - 1 + j + 1 = k]])
  let h2 ← rr (← ExceptT.mk [[a:real = --b * c <=> a + b * c = &0]])
  let h1 ← ar (← ExceptT.mk [[n - (n - 1) - 1 = 0]])
  prove ([[!a n r.
    ~(a n = &0) /\ &0 < r /\ sum(0..n) (\i. a i * r pow i) = &0
    ==> ?b. ~(b(n - 1) = &0) /\
            (!x. sum(0..n) (\i. a i * x pow i) =
                 (x - r) * sum(0..n-1) (\i. b i * x pow i)) /\
            ?d. ODD d /\ variation(0..n) a = variation(0..n-1) b + d]])
   (REPEAT GEN_TAC THEN ASM_CASES_TAC ([[n = 0]]) THENL
     [ASM_SIMP_TAC [SUM_CLAUSES_NUMSEG, real_pow, REAL_MUL_RID] THEN MESON_TAC [],
      STRIP_TAC] THEN
    ABBREV_TAC ([[b = \j. sum (j + 1..n) (\i. a i * r pow (i - j - 1))]]) THEN
    EXISTS_TAC ([[b:num->real]]) THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "b" THEN REWRITE_TAC [] THEN ASM_SIMP_TAC [SUB_ADD, LE_1] THEN
      ASM_SIMP_TAC [SUM_SING_NUMSEG, h1] THEN
      ASM_REWRITE_TAC [real_pow, REAL_MUL_RID],
      MP_TAC (← HolLight.GEN ([[x:real]]) (← HolLight.SPECL [([[a:num->real]]), ([[x:real]]), ([[r:real]]), ([[n:num]])] REAL_SUB_POLYFUN)) THEN
      ASM_SIMP_TAC [LE_1, REAL_SUB_RZERO] THEN DISCH_THEN ((fun _ => ALL_TAC)) THEN
      EXPAND_TAC "b" THEN REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[(b:num->real) n = &0]]) ASSUME_TAC THENL
     [EXPAND_TAC "b" THEN REWRITE_TAC [] THEN MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
      ARITH_TAC,
      ALL_TAC] THEN
    MP_TAC (← HolLight.ISPECL [([[n:num]]), ([[\i. if i <= n then a i * (r:real) pow i else &0]]),
      ([[\i. if i <= n then --b i * (r:real) pow (i + 1) else &0]])] ARTHAN_LEMMA) THEN
    ASM_SIMP_TAC [REAL_ENTIRE, REAL_POW_EQ_0, REAL_LT_IMP_NZ, REAL_NEG_0,
                 LE_REFL] THEN
    ANTS_TAC THENL
     [X_GEN_TAC ([[j:num]]) THEN EXPAND_TAC "b" THEN REWRITE_TAC [] THEN
      ASM_CASES_TAC ([[j:num <= n]]) THEN ASM_REWRITE_TAC [] THENL
       [SUBGOAL_THEN ([[!i:num. i <= j ==> i <= n]]) MP_TAC THENL
         [ASM_ARITH_TAC, SIMP_TAC [] THEN DISCH_THEN ((fun _ => ALL_TAC))] THEN
        REWRITE_TAC [h2] THEN
        REWRITE_TAC [(← HolLight.GSYM SUM_RMUL), (← HolLight.GSYM REAL_POW_ADD), (← HolLight.GSYM REAL_MUL_ASSOC)] THEN
        SIMP_TAC [h3] THEN
        ASM_SIMP_TAC [SUM_COMBINE_R, LE_0],
        REWRITE_TAC [(← HolLight.GSYM SUM_RESTRICT_SET), IN_NUMSEG] THEN
        ASM_SIMP_TAC [h4] THEN
        ASM_REWRITE_TAC [(← HolLight.GSYM numseg)]],
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[d:num]]) THEN
      MATCH_MP_TAC MONO_AND THEN REWRITE_TAC [] THEN MATCH_MP_TAC h5 THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC ([[variation(0..n) (\i. a i * r pow i)]]) THEN CONJ_TAC THENL
         [MATCH_MP_TAC VARIATION_EQ THEN SIMP_TAC [IN_NUMSEG],
          ALL_TAC],
        MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC ([[variation(0..n) (\i. --b i * r pow (i + 1))]]) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC VARIATION_EQ THEN SIMP_TAC [IN_NUMSEG],
          ALL_TAC] THEN
        MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC ([[variation(0..n-1) (\i. --b i * r pow (i + 1))]]) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC VARIATION_SUBSET THEN
          REWRITE_TAC [SUBSET_NUMSEG, IN_DIFF, IN_NUMSEG] THEN
          CONJ_TAC THENL [ARITH_TAC, X_GEN_TAC ([[i:num]]) THEN STRIP_TAC] THEN
          SUBGOAL_THEN ([[i:num = n]]) SUBST_ALL_TAC THENL
           [ASM_ARITH_TAC, ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC2],
          ALL_TAC]] THEN
      REWRITE_TAC [variation] THEN
      ONCE_REWRITE_TAC [h6] THEN
      SIMP_TAC [NOT_IMP, (← HolLight.GSYM CONJ_ASSOC), (← HolLight.GSYM REAL_POW_ADD),
               h7] THEN
      ONCE_REWRITE_TAC [h8] THEN
      ASM_SIMP_TAC [REAL_LT_MUL_EQ, REAL_POW_LT] THEN
      ASM_SIMP_TAC [REAL_MUL_RNEG, REAL_ENTIRE, REAL_NEG_EQ_0, REAL_POW_EQ_0] THEN
      ASM_SIMP_TAC [REAL_LT_IMP_NZ]])
  : ExceptT String IO thm).run
#eval VARIATION_POSITIVE_ROOT_FACTOR

#eval phrase 23
def VARIATION_POSITIVE_ROOT_MULTIPLE_FACTOR : thm := keep "VARIATION_POSITIVE_ROOT_MULTIPLE_FACTOR" fun _ => (do
  prove ([[!r n a.
    ~(a n = &0) /\ &0 < r /\ sum(0..n) (\i. a i * r pow i) = &0
    ==> ?b k m. 0 < k /\ m < n /\ ~(b m = &0) /\
                (!x. sum(0..n) (\i. a i * x pow i) =
                     (x - r) pow k * sum(0..m) (\i. b i * x pow i)) /\
                ~(sum(0..m) (\j. b j * r pow j) = &0) /\
                ?d. EVEN d /\ variation(0..n) a = variation(0..m) b + k + d]])
   (GEN_TAC THEN MATCH_MP_TAC num_WF THEN
    X_GEN_TAC ([[n:num]]) THEN DISCH_TAC THEN X_GEN_TAC ([[a:num->real]]) THEN
    ASM_CASES_TAC ([[n = 0]]) THENL
     [ASM_SIMP_TAC [SUM_CLAUSES_NUMSEG, real_pow, REAL_MUL_RID] THEN MESON_TAC [],
      STRIP_TAC] THEN
    MP_TAC (← HolLight.ISPECL [([[a:num->real]]), ([[n:num]]), ([[r:real]])] VARIATION_POSITIVE_ROOT_FACTOR) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN ([[c:num->real]]) MP_TAC) THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[d:num]]) STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC ([[sum(0..n-1) (\i. c i * r pow i) = &0]]) THENL
     [FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[n - 1]])) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC, DISCH_THEN (MP_TAC o HolLight.SPEC ([[c:num->real]]))] THEN
      ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[b:num->real]]) THEN
      ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[m:num]]) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[k:num]]) MP_TAC) THEN
      REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[e:num]]) STRIP_ASSUME_TAC) THEN
      EXISTS_TAC ([[SUC k]]) THEN ASM_REWRITE_TAC [real_pow, REAL_MUL_ASSOC] THEN
      REPEAT (CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC]) THEN
      REWRITE_TAC [ADD1, ADD_ASSOC] THEN EXISTS_TAC ([[d - 1 + e]]),
      MAP_EVERY EXISTS_TAC [([[c:num->real]]), ([[1]]), ([[n - 1]])] THEN
      ASM_REWRITE_TAC [REAL_POW_1] THEN
      REPEAT (CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC]) THEN
      EXISTS_TAC ([[d - 1]])] THEN
    UNDISCH_TAC ([[ODD d]]) THEN GEN_REWRITE_TAC HolLight.LAND_CONV [ODD_EXISTS] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[p:num]]) SUBST1_TAC) THEN
    ASM_REWRITE_TAC [SUC_SUB1, EVEN_ADD, EVEN_MULT, ARITH] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval VARIATION_POSITIVE_ROOT_MULTIPLE_FACTOR

#eval phrase 24
def VARIATION_POSITIVE_ROOT_MULTIPLICITY_FACTOR : thm := keep "VARIATION_POSITIVE_ROOT_MULTIPLICITY_FACTOR" fun _ => (do
  prove ([[!r n a.
    ~(a n = &0) /\ &0 < r /\ sum(0..n) (\i. a i * r pow i) = &0
    ==> ?b m. m < n /\ ~(b m = &0) /\
              (!x. sum(0..n) (\i. a i * x pow i) =
                   (x - r) pow
                   (multiplicity (\x. sum(0..n) (\i. a i * x pow i)) r) *
                   sum(0..m) (\i. b i * x pow i)) /\
              ~(sum(0..m) (\j. b j * r pow j) = &0) /\
              ?d. EVEN d /\
                  variation(0..n) a = variation(0..m) b +
                     multiplicity (\x. sum(0..n) (\i. a i * x pow i)) r + d]])
   (REPEAT GEN_TAC THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP VARIATION_POSITIVE_ROOT_MULTIPLE_FACTOR) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[b:num->real]]) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[k:num]]) MP_TAC) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[m:num]]) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN ([[multiplicity (\x. sum(0..n) (\i. a i * x pow i)) r = k]]) (fun th => ASM_REWRITE_TAC [th]) THEN
    CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC MULTIPLICITY_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [([[b:num->real]]), ([[m:num]])] THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval VARIATION_POSITIVE_ROOT_MULTIPLICITY_FACTOR

/- ------------------------------------------------------------------------- -/
/- Hence the main theorem.                                                   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 25
def DESCARTES_RULE_OF_SIGNS : thm := keep "DESCARTES_RULE_OF_SIGNS" fun _ => (do
  let h5 ← ms [] (← ExceptT.mk [[(?i. P i /\ Q i) <=> ~(!i. P i ==> ~Q i)]])
  let h4 ← ar (← ExceptT.mk [[s1:num = s2 ==> s1 + m = m + s2]])
  let h3 ← sr (← ExceptT.mk [[x IN s /\ s DELETE x = t ==> s = x INSERT t]])
  let h2 ← ar (← ExceptT.mk [[x + y = z ==> (x + d1) + (y + d2):num = z + d1 + d2]])
  let h1 ← ar (← ExceptT.mk [[i <= n ==> i <= n - 1 \/ i = n]])
  prove ([[!f a n. f = (\x. sum(0..n) (\i. a i * x pow i)) /\
           (?i. i IN 0..n /\ ~(a i = &0))
           ==> ?d. EVEN d /\
                   variation(0..n) a =
                   nsum {r | &0 < r /\ f(r) = &0} (\r. multiplicity f r) + d]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [IMP_CONJ] THEN
    DISCH_THEN (fun th => REWRITE_TAC [th]) THEN
    MAP_EVERY (fun t => SPEC_TAC (t, t)) [([[a:num->real]]), ([[n:num]])] THEN
    MATCH_MP_TAC num_WF THEN X_GEN_TAC ([[n:num]]) THEN DISCH_TAC THEN
    X_GEN_TAC ([[a:num->real]]) THEN ASM_CASES_TAC ([[(a:num->real) n = &0]]) THENL
     [ASM_CASES_TAC ([[n = 0]]) THEN
      ASM_REWRITE_TAC [NUMSEG_SING, IN_SING, UNWIND_THM2] THENL [ASM_MESON_TAC [], DISCH_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[n - 1]])) THEN ANTS_TAC THENL
       [ASM_ARITH_TAC, DISCH_THEN (MP_TAC o HolLight.SPEC ([[a:num->real]]))] THEN
      ANTS_TAC THENL
       [ASM_MESON_TAC [IN_NUMSEG, h1],
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[d:num]]) THEN
        ASM_SIMP_TAC [LE_0, LE_1, SUM_CLAUSES_RIGHT] THEN
        REWRITE_TAC [REAL_MUL_LZERO, REAL_ADD_RID] THEN
        DISCH_THEN (SUBST1_TAC o HolLight.SYM o HolLight.CONJUNCT2) THEN
        MATCH_MP_TAC VARIATION_SUBSET THEN
        REWRITE_TAC [SUBSET_NUMSEG, IN_DIFF, IN_NUMSEG] THEN
        CONJ_TAC THENL [ASM_ARITH_TAC, X_GEN_TAC ([[i:num]]) THEN STRIP_TAC] THEN
        SUBGOAL_THEN ([[i:num = n]]) (fun th => ASM_REWRITE_TAC [th]) THEN
        ASM_ARITH_TAC],
      DISCH_THEN ((fun _ => ALL_TAC))] THEN
    ASM_CASES_TAC ([[{r | &0 < r /\ sum(0..n) (\i. a i * r pow i) = &0} = {}]]) THENL
     [ASM_REWRITE_TAC [NSUM_CLAUSES, ADD_CLAUSES] THEN
      ONCE_REWRITE_TAC [CONJ_SYM] THEN REWRITE_TAC [UNWIND_THM1] THEN
      ONCE_REWRITE_TAC [(← HolLight.GSYM NOT_ODD)] THEN
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP ODD_VARIATION_POSITIVE_ROOT) THEN
      HolLight.ASM SET_TAC [],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [(← HolLight.GSYM MEMBER_NOT_EMPTY)]) THEN
    REWRITE_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC ([[r:real]]) THEN STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[r:real]]), ([[n:num]]), ([[a:num->real]])] VARIATION_POSITIVE_ROOT_MULTIPLICITY_FACTOR) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [([[b:num->real]]), ([[m:num]])] THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[m:num]])) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[b:num->real]])) THEN ANTS_TAC THENL
     [EXISTS_TAC ([[m:num]]) THEN ASM_REWRITE_TAC [IN_NUMSEG, LE_REFL, LE_0],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[d1:num]]) (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN ([[d2:num]]) (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
    EXISTS_TAC ([[d1 + d2:num]]) THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC [EVEN_ADD], ALL_TAC] THEN
    MATCH_MP_TAC h2 THEN
    SUBGOAL_THEN ([[{r | &0 < r /\ sum(0..n) (\i. a i * r pow i) = &0} =
    r INSERT {r | &0 < r /\ sum(0..m) (\i. b i * r pow i) = &0}]]) SUBST1_TAC THENL
     [MATCH_MP_TAC h3 THEN
      CONJ_TAC THENL
       [REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [],
        ONCE_ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [REAL_ENTIRE, REAL_POW_EQ_0, REAL_SUB_0] THEN
        REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_DELETE] THEN
        X_GEN_TAC ([[s:real]]) THEN
        FIRST_X_ASSUM (fun (th : thm) => match SPEC_VAR th with | .ok _ => ALL_TAC | .error e => FAIL_TAC e) THEN
        ASM_CASES_TAC ([[s:real = r]]) THEN ASM_REWRITE_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[FINITE {r | &0 < r /\ sum(0..m) (\i. b i * r pow i) = &0}]]) MP_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC ([[{r | sum(0..m) (\i. b i * r pow i) = &0}]]) THEN
      SIMP_TAC [SUBSET, IN_ELIM_THM, REAL_POLYFUN_FINITE_ROOTS] THEN
      EXISTS_TAC ([[m:num]]) THEN ASM_REWRITE_TAC [IN_NUMSEG, LE_0, LE_REFL],
      SIMP_TAC [NSUM_CLAUSES, IN_ELIM_THM] THEN DISCH_TAC] THEN
    FIRST_X_ASSUM (ASSUME_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [(← HolLight.GSYM FUN_EQ_THM)]) THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC h4 THEN
    MATCH_MP_TAC NSUM_EQ THEN
    X_GEN_TAC ([[s:real]]) THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (fun t => GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.LAND_CONV) [t]) THEN
    CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC MULTIPLICITY_OTHER_ROOT THEN
    REWRITE_TAC [h5] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC ([[~(sum (0..m) (\j. b j * r pow j) = &0)]]) THEN ASM_SIMP_TAC [] THEN
    REWRITE_TAC [REAL_MUL_LZERO, SUM_0])
  : ExceptT String IO thm).run
#eval DESCARTES_RULE_OF_SIGNS

end Hol100.Descartes
