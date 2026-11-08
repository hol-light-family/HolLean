/- File: Hol100/Isoperimetric.lean
Translation of HOL Light's 100/isoperimetric.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionMultiLib.Cauchy
import SessionMultiLib.LpSpaces
import Hol100.Green
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Binomial SessionLibrary.Iter SessionLibrary.Permutations SessionLibrary.Wo SessionLibrary.Products SessionLibrary.Floor SessionLibrary.Frag SessionLibrary.Prime SessionLibrary.Card SessionLibrary.Matroids SessionMultiLib.Misc SessionLibrary.GroupTheory SessionMultiLib.Vectors SessionMultiLib.Metric SessionMultiLib.Determinants SessionMultiLib.Homology SessionMultiLib.Topology SessionMultiLib.Convex SessionMultiLib.ComplexAlgebra SessionMultiLib.Complexes SessionMultiLib.Paths SessionMultiLib.Polytope SessionMultiLib.Degree SessionMultiLib.Derivatives SessionMultiLib.Integration SessionMultiLib.Measure SessionMultiLib.Canal SessionMultiLib.Transcendentals SessionMultiLib.RealAnalysis SessionMultiLib.LpSpaces SessionMultiLib.MoreTop SessionMultiLib.Cauchy Hol100.Green
namespace Hol100.Isoperimetric

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ms (ths : List thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (MESON ths tm)
private def na (tm : term) : ExceptT String IO thm := ExceptT.mk (NORM_ARITH tm)
private def rf (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_FIELD tm)
private def rg (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_RING tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)
private def sr (tm : term) : ExceptT String IO thm := ExceptT.mk (SET_RULE tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)
private def va (tm : term) : ExceptT String IO thm := ExceptT.mk (VECTOR_ARITH tm)

/- ========================================================================= -/
/- The isoperimetric inequality.                                             -/
/- ========================================================================= -/

/-- `CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) n`. -/
private def gsimp (n : Int) (ths : List thm) : HolCore.Tactics.tactic := HolLight.tactic_of do
  pure (CONV_TAC (← ExceptT.mk (HolCore.Simp.GEN_SIMPLIFY_CONV Session.B (TOP_DEPTH_SQCONV Session.B)
    (← ExceptT.mk (Session.basic_ss [])) n ths)))

#eval phrase 1
-- needs "Multivariate/cauchy.ml";;
#eval SessionMultiLib.Cauchy.ensureCauchy

#eval phrase 2
-- needs "Multivariate/lpspaces.ml";;
#eval SessionMultiLib.LpSpaces.ensureLpSpaces

#eval phrase 3
-- needs "100/green.ml";;
#eval Hol100.Green.ensure

/- ------------------------------------------------------------------------- -/
/- A few lemmas to switch between views of a convex curve.                   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 4
def lemma1 : thm := keep "lemma1" fun _ => (do
  prove ([[!g:real^1->real^2.
        simple_path g /\ pathfinish g = pathstart g /\
        convex(inside(path_image g))
        ==> convex hull (path_image g) = closure(inside(path_image g))]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN ASM_SIMP_TAC [CONVEX_CLOSURE] THEN
      REWRITE_TAC [(← HolLight.GSYM FRONTIER_UNION_INTERIOR)] THEN
      ASM_SIMP_TAC [JORDAN_INSIDE_OUTSIDE] THEN SET_TAC [],
      MATCH_MP_TAC CLOSURE_MINIMAL THEN
      REWRITE_TAC [INSIDE_SUBSET_CONVEX_HULL] THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      ASM_SIMP_TAC [COMPACT_CONVEX_HULL, COMPACT_PATH_IMAGE,
                   SIMPLE_PATH_IMP_PATH]])
  : ExceptT String IO thm).run
#eval lemma1

#eval phrase 5
def lemma2 : thm := keep "lemma2" fun _ => (do
  prove ([[!g:real^1->real^2.
        simple_path g /\ pathfinish g = pathstart g /\
        convex(inside(path_image g))
        ==> frontier(convex hull (path_image g)) = path_image g]])
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [lemma1, FRONTIER_CLOSURE_CONVEX] THEN
    ASM_SIMP_TAC [JORDAN_INSIDE_OUTSIDE])
  : ExceptT String IO thm).run
#eval lemma2

#eval phrase 6
def lemma3 : thm := keep "lemma3" fun _ => (do
  let h1 ← sr (← ExceptT.mk [[t = s <=> s SUBSET t /\ ~(s PSUBSET t)]])
  prove ([[!g:real^1->real^2.
        simple_path g /\
        pathfinish g = pathstart g /\
        path_image g SUBSET frontier (convex hull path_image g)
        ==> frontier (convex hull path_image g) = path_image g]])
   (REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [h1] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN ([[~(inside(path_image g):real^2->bool = {})]]) MP_TAC THENL
     [ASM_MESON_TAC [JORDAN_INSIDE_OUTSIDE], REWRITE_TAC []] THEN
    MATCH_MP_TAC EMPTY_INSIDE_PSUBSET_CONVEX_FRONTIER THEN
    ASM_MESON_TAC [CONVEX_CONVEX_HULL])
  : ExceptT String IO thm).run
#eval lemma3

/- ------------------------------------------------------------------------- -/
/- Part 1: The Wirtinger inequality.                                         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 7
def REAL_HOELDER_BOUND_2 : thm := keep "REAL_HOELDER_BOUND_2" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[abs x <= x <=> &0 <= x]])
  prove ([[!f s. real_measurable s /\
         f real_measurable_on s /\
         (\x. f x pow 2) real_integrable_on s
         ==> (real_integral s f) pow 2
             <= real_measure s * real_integral s (\x. f x pow 2)]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[lift o f o drop]]), ([[IMAGE lift s]]), ([[&2]])] HOELDER_BOUND) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC [lspace, IN_ELIM_THM, RPOW_POW, REAL_POW_1] THEN
    ASM_REWRITE_TAC [(← HolLight.GSYM real_measurable_on), (← HolLight.GSYM REAL_MEASURABLE_MEASURABLE),
                    (← HolLight.GSYM ABSOLUTELY_REAL_INTEGRABLE_ON)] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [REAL_INTEGRABLE_ON]) THEN
    SIMP_TAC [o_DEF, NORM_1, LIFT_DROP, REAL_POW2_ABS] THEN
    DISCH_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_SIMP_TAC [SessionMultiLib.RealAnalysis.REAL_INTEGRAL, ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
    ASM_SIMP_TAC [SessionMultiLib.RealAnalysis.REAL_INTEGRAL, REAL_INTEGRABLE_ON, o_DEF] THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_MEASURE_MEASURE)] THEN
    MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_CONJ_ALT] REAL_LE_TRANS) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC [REAL_MEASURE_POS_LE] THEN
    REWRITE_TAC [h1] THEN
    MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    ASM_REWRITE_TAC [LIFT_DROP, REAL_LE_POW_2])
  : ExceptT String IO thm).run
#eval REAL_HOELDER_BOUND_2

#eval phrase 8
def WIRTINGER_INEQUALITY : thm := keep "WIRTINGER_INEQUALITY" fun _ => (do
  let h40 ← rr (← ExceptT.mk [[&2 * pi - a = --a + &2 * pi]])
  let h39 ← rr (← ExceptT.mk [[a - b:real = --b + a]])
  let h38 ← rg (← ExceptT.mk [[f(&2 * pi) = c3 * sin(&2 * pi - a) /\ f(&0) = c1 * sin(&0 - a) /\
    f(&2 * pi) = f(&0) /\ sin(&2 * pi - a) = sin(&0 - a) /\
    ~(sin(&0 - a) = &0)
    ==> c3 = c1]])
  let h37 ← rr (← ExceptT.mk [[x - a = (x - (a + pi)) + pi]])
  let h36 ← tt (← ExceptT.mk [[p1 /\ p2 /\ p3 /\ (q1 /\ q2 /\ q3 ==> r)
    ==> (p1 ==> q1) ==> (p2 ==> q2) ==> (p3 ==> q3) ==> r]])
  let h35 ← tt (← ExceptT.mk [[p1 /\ p2 /\ (q1 /\ q2 ==> r)
      ==> (p1 ==> q1) ==> (p2 ==> q2) ==> r]])
  let h34 ← rr (← ExceptT.mk [[x / x' = y / y' <=> &0 = y * inv y' - x * inv x']])
  let h33 ← ms [] (← ExceptT.mk [[(?c. !u. P u ==> f u = c) <=> (!u v. P u /\ P v ==> f u = f v)]])
  let h32 ← rf (← ExceptT.mk [[~(y = &0) ==> (x = c * y <=> x / y = c)]])
  let h31 ← rr (← ExceptT.mk [[x' pow 2 - x pow 2 - (x' pow 2 - (x - a) pow 2 - b):real =
    (a pow 2 + b) - (&2 * a) * x]])
  let h30 ← tt (← ExceptT.mk [[p ==> q ==> r <=> p /\ q ==> p /\ q ==> r]])
  let h29 ← rr (← ExceptT.mk [[&2 * pi - a = &0 - a + &2 * pi]])
  let h28 ← rr (← ExceptT.mk [[(a1 - a0) + (a2 - a1) + (a3 - a2):real = a3 - a0]])
  let h27 ← tt (← ExceptT.mk [[p /\ q /\ r /\ s ==> t <=>
                        r /\ s ==> p /\ q ==> t]])
  let h26 ← tt (← ExceptT.mk [[p /\ q /\ r /\ s ==> t <=>
                        r /\ s ==> p /\ q ==> t]])
  let h25 ← rr (← ExceptT.mk [[x - a = (x - (a + pi)) + pi]])
  let h24 ← tt (← ExceptT.mk [[p1 /\ p2 /\ p3 /\ (q1 /\ q2 /\ q3 ==> r)
    ==> (p1 ==> q1) ==> (p2 ==> q2) ==> (p3 ==> q3) ==> r]])
  let h23 ← tt (← ExceptT.mk [[p /\ q /\ r ==> s <=> q ==> p /\ r ==> s]])
  let h22 ← tt (← ExceptT.mk [[p /\ q /\ r ==> s <=> q ==> p /\ r ==> s]])
  let h21 ← rr (← ExceptT.mk [[(g:real->real) d - g c =
      (g((c + d) / &2) - g c) + (g d - g((c + d) / &2))]])
  let h20 ← rr (← ExceptT.mk [[abs(x) <= a /\ abs(y) <= a ==> abs(x - y) <= &2 * a]])
  let h19 ← rr (← ExceptT.mk [[x <= x' /\ abs(g) <= &2 * abs b
        ==> &2 * x - g <= &2 * abs(abs b + x')]])
  let h18 ← rr (← ExceptT.mk [[&0 <= x /\ &0 <= y /\ &0 <= z
          ==> abs(x - y - z) <= &2 * x - (x - y - z)]])
  let h17 ← rr (← ExceptT.mk [[&0 <= x /\ x <= y ==> abs x <= y]])
  let h16 ← rr (← ExceptT.mk [[abs(&0):real <= &2 * abs x]])
  let h15 ← tt (← ExceptT.mk [[p /\ (p ==> q) ==> p /\ q]])
  let h14 ← rr (← ExceptT.mk [[&0 = &0 * abs(inv(&1))]])
  let h13 ← rr (← ExceptT.mk [[x + z:real = y ==> abs(x - y) <= abs z]])
  let h12 ← rr (← ExceptT.mk [[y + z:real = x ==> abs(x - y) <= abs z]])
  let h11 ← rr (← ExceptT.mk [[x - a:real = (x - c) + (c - a)]])
  let h10 ← tt (← ExceptT.mk [[(~p ==> F) ==> p]])
  let h9 ← tt (← ExceptT.mk [[p /\ (p ==> q) ==> p /\ q]])
  let h8 ← tt (← ExceptT.mk [[(q ==> p) /\ q ==> p /\ q]])
  let h7 ← tt (← ExceptT.mk [[p /\ (p ==> q) ==> p /\ q]])
  let h6 ← rr (← ExceptT.mk [[x - a - (c - a):real = x - c]])
  let h5 ← rr (← ExceptT.mk [[&2 * a * b = a * b + b * a]])
  let h4 ← rr (← ExceptT.mk [[a < pi <=> a <= pi /\ ~(a = pi)]])
  let h3 ← tt (← ExceptT.mk [[(q1 \/ q2) /\ p /\ (r ==> s)
      ==> (p /\ q1 ==> r) ==> (p /\ q2 ==> r) ==> s]])
  let h2 ← rr (← ExceptT.mk [[a - b <= &0 <=> a <= b]])
  let h1 ← tt (← ExceptT.mk [[p /\ (p ==> q) ==> p /\ q]])
  prove ([[!f f'.
        (!x. x IN real_interval[&0,&2 * pi]
             ==> (f' has_real_integral (f x - f(&0))) (real_interval[&0,x])) /\
        f(&2 * pi) = f(&0) /\
        (f has_real_integral &0) (real_interval[&0,&2 * pi]) /\
        (\x. f'(x) pow 2) real_integrable_on real_interval[&0,&2 * pi]
        ==> (\x. f(x) pow 2) real_integrable_on real_interval[&0,&2 * pi] /\
            real_integral (real_interval[&0,&2 * pi]) (\x. f(x) pow 2) <=
            real_integral (real_interval[&0,&2 * pi]) (\x. f'(x) pow 2) /\
            (real_integral (real_interval[&0,&2 * pi]) (\x. f(x) pow 2) =
             real_integral (real_interval[&0,&2 * pi]) (\x. f'(x) pow 2)
             ==> ?c a. !x. x IN real_interval[&0,&2 * pi]
                           ==> f x = c * sin(x - a))]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[f' real_integrable_on real_interval[&0,&2 * pi] ]]) ASSUME_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[&2 * pi]])) THEN
      REWRITE_TAC [HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL, IN_REAL_INTERVAL] THEN
      ANTS_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC2, SIMP_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[f' absolutely_real_integrable_on real_interval[&0,&2 * pi] ]]) ASSUME_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_INTEGRABLE_BOUND THEN
      EXISTS_TAC ([[\x. &1 + (f':real->real) x pow 2]]) THEN
      ASM_SIMP_TAC [REAL_INTEGRABLE_ADD, REAL_INTEGRABLE_CONST] THEN
      X_GEN_TAC ([[x:real]]) THEN STRIP_TAC THEN
      MP_TAC (← HolLight.SPEC ([[&1 - (f':real->real) x]]) REAL_LE_POW_2) THEN
      MP_TAC (← HolLight.SPEC ([[&1 + (f':real->real) x]]) REAL_LE_POW_2) THEN
      REAL_ARITH_TAC2,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[f real_continuous_on real_interval[&0,&2 * pi] ]]) ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THEN
      EXISTS_TAC ([[\x. real_integral (real_interval [&0,x]) f' + f(&0)]]) THEN
      ASM_SIMP_TAC [REAL_INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT,
                   REAL_CONTINUOUS_ON_ADD, REAL_CONTINUOUS_ON_CONST] THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL]) THEN
      ASM_SIMP_TAC [REAL_SUB_ADD],
      ALL_TAC] THEN
    MATCH_MP_TAC h1 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN ASM_REWRITE_TAC [],
      DISCH_TAC] THEN
    SUBGOAL_THEN ([[?a. &0 <= a /\ a < pi /\ f (a + pi):real = f(a)]]) STRIP_ASSUME_TAC THENL
     [MP_TAC (← HolLight.ISPECL [([[\x. (f:real->real)(x + pi) - f x]]), ([[&0]]), ([[pi]]), ([[&0]])] REAL_IVT_INCREASING) THEN
      MP_TAC (← HolLight.ISPECL [([[\x. (f:real->real)(x + pi) - f x]]), ([[&0]]), ([[pi]]), ([[&0]])] REAL_IVT_DECREASING) THEN
      ASM_SIMP_TAC [PI_POS_LE, REAL_ADD_LID, (← HolLight.GSYM REAL_MUL_2)] THEN
      REWRITE_TAC [REAL_SUB_LE, h2] THEN
      MATCH_MP_TAC h3 THEN
      REWRITE_TAC [REAL_LE_TOTAL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
         [GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM o_DEF)] THEN
          MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
          SIMP_TAC [REAL_CONTINUOUS_ON_ADD, REAL_CONTINUOUS_ON_ID,
                   REAL_CONTINUOUS_ON_CONST] THEN
          ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
          REWRITE_TAC [(← HolLight.GSYM REAL_INTERVAL_TRANSLATION)],
          ALL_TAC] THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] REAL_CONTINUOUS_ON_SUBSET)) THEN
        REWRITE_TAC [SUBSET_REAL_INTERVAL] THEN
        MP_TAC PI_POS THEN REAL_ARITH_TAC2,
        REWRITE_TAC [IN_REAL_INTERVAL, LEFT_IMP_EXISTS_THM, REAL_SUB_0]] THEN
      X_GEN_TAC ([[a:real]]) THEN ASM_CASES_TAC ([[a = pi]]) THENL
       [ASM_REWRITE_TAC [(← HolLight.GSYM REAL_MUL_2)] THEN
        DISCH_THEN (ASSUME_TAC o HolLight.SYM o (HolCore.Lib.last (α := thm)) o HolLight.CONJUNCTS) THEN
        EXISTS_TAC ([[&0:real]]) THEN ASM_REWRITE_TAC [REAL_ADD_LID] THEN
        REWRITE_TAC [REAL_LE_REFL, PI_POS],
        ASM_REWRITE_TAC [h4] THEN
        ASM_MESON_TAC []],
      ALL_TAC] THEN
    MAP_EVERY ABBREV_TAC [([[g = \x. (f(x) - f(a)) pow 2 / tan(x - a)]]),
      ([[g' = \x. f'(x) pow 2 - (f(x) - f(a)) pow 2 -
              (f'(x) - (f(x) - f(a)) / tan(x - a)) pow 2]])] THEN
    SUBGOAL_THEN ([[!c d. c <= d /\
          real_interval[c,d] SUBSET real_interval[&0,&2 * pi] /\
          (!x. x IN real_interval[c,d] ==> ~(sin(x - a) = &0))
          ==> (g' has_real_integral g d - g c) (real_interval[c,d])]]) ASSUME_TAC THENL
     [REWRITE_TAC [SUBSET_REAL_INTERVAL, IN_REAL_INTERVAL] THEN
      REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ASM_REWRITE_TAC [(← HolLight.GSYM REAL_NOT_LE)] THEN STRIP_TAC THEN
      MAP_EVERY EXPAND_TAC ["g", "g'"] THEN REWRITE_TAC [real_div] THEN
      MP_TAC (← HolLight.ISPECL [([[\x. ((f:real->real) x - f a) pow 2]]), ([[\x. inv(tan(x - a))]]),
                     ([[\x. &2 * ((f:real->real) x - f a) * f' x]]),
                     ([[\x. --(inv(sin(x - a) pow 2))]]),
                     ([[c:real]]), ([[d:real]])] ABSOLUTE_REAL_INTEGRATION_BY_PARTS_SUM) THEN
      ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [REWRITE_TAC [REAL_POW_2, h5] THEN
          MATCH_MP_TAC ABSOLUTE_REAL_INTEGRATION_BY_PARTS_SUM THEN
          ASM_REWRITE_TAC [h6] THEN
          CONJ_TAC THENL
           [FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
            REWRITE_TAC [SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC,
            X_GEN_TAC ([[x:real]]) THEN REWRITE_TAC [IN_REAL_INTERVAL] THEN
            STRIP_TAC] THEN
          REWRITE_TAC [HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
          MATCH_MP_TAC h7 THEN CONJ_TAC THENL
           [FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
            REWRITE_TAC [SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC,
            DISCH_TAC] THEN
          MP_TAC (← HolLight.SPECL [([[f':real->real]]), ([[&0:real]]), ([[x:real]]), ([[c:real]])] REAL_INTEGRAL_COMBINE) THEN
          SUBGOAL_THEN ([[(f' has_real_integral f c - f(&0)) (real_interval [&0,c]) /\
          (f' has_real_integral f x - f(&0)) (real_interval [&0,x])]]) MP_TAC THENL
           [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
            REWRITE_TAC [IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC,
            SIMP_TAC [HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
            ASM_REAL_ARITH_TAC],
          REWRITE_TAC [absolutely_real_integrable_on, REAL_ABS_NEG] THEN
          REWRITE_TAC [REAL_ABS_INV, REAL_ABS_POW, REAL_POW2_ABS] THEN
          REWRITE_TAC [REAL_INTEGRABLE_NEG_EQ, CONJ_ASSOC] THEN
          ONCE_REWRITE_TAC [(← HolLight.GSYM REAL_INTEGRABLE_NEG_EQ)] THEN
          REWRITE_TAC [] THEN
          MATCH_MP_TAC h8 THEN CONJ_TAC THENL
           [DISCH_THEN (MP_TAC o HolLight.SPEC ([[d:real]])) THEN
            ASM_REWRITE_TAC [IN_REAL_INTERVAL, REAL_LE_REFL] THEN
            SIMP_TAC [HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL],
            ALL_TAC] THEN
          X_GEN_TAC ([[x:real]]) THEN REWRITE_TAC [IN_REAL_INTERVAL] THEN
          STRIP_TAC THEN MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS THEN
          ASM_REWRITE_TAC [IN_REAL_INTERVAL] THEN
          X_GEN_TAC ([[y:real]]) THEN STRIP_TAC THEN
          REWRITE_TAC [tan, REAL_INV_DIV, REAL_INV_INV] THEN
          REAL_DIFF_TAC THEN
          MATCH_MP_TAC h9 THEN CONJ_TAC THENL
           [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC,
            MP_TAC (← HolLight.SPEC ([[y - a:real]]) SIN_CIRCLE) THEN CONV_TAC rf]],
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[d:real]]) o HolLight.CONJUNCT2) THEN
        ASM_REWRITE_TAC [IN_REAL_INTERVAL, REAL_LE_REFL] THEN
        MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_CONJ] HAS_REAL_INTEGRAL_EQ) THEN
        X_GEN_TAC ([[x:real]]) THEN REWRITE_TAC [IN_REAL_INTERVAL] THEN STRIP_TAC THEN
        FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[x:real]])) THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [tan, real_div, REAL_INV_MUL, REAL_INV_INV] THEN
        MP_TAC (← HolLight.SPEC ([[x - a:real]]) SIN_CIRCLE) THEN CONV_TAC rf],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[g real_continuous_on real_interval[&0,&2 * pi] ]]) ASSUME_TAC THENL
     [REWRITE_TAC [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      X_GEN_TAC ([[c:real]]) THEN REWRITE_TAC [IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      EXPAND_TAC "g" THEN
      REWRITE_TAC [tan, real_div, REAL_INV_MUL, REAL_INV_INV, REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN CONJ_TAC THENL
       [ALL_TAC,
        MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_WITHINREAL THEN
        REAL_DIFFERENTIABLE_TAC] THEN
      ASM_CASES_TAC ([[sin(c - a) = &0]]) THENL
       [REWRITE_TAC [REAL_CONTINUOUS_WITHINREAL],
        MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_CONTINUOUS_POW THEN
          MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN
          REWRITE_TAC [REAL_CONTINUOUS_CONST] THEN
          FIRST_X_ASSUM (MATCH_MP_TAC o
           HolLight.GEN_REWRITE_RULE HolCore.Lib.I [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]) THEN
          ASM_REWRITE_TAC [IN_REAL_INTERVAL],
          ALL_TAC] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_INV_WITHINREAL THEN
        ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_WITHINREAL THEN
        REAL_DIFFERENTIABLE_TAC] THEN
      ASM_REWRITE_TAC [REAL_INV_0, REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
      ONCE_REWRITE_TAC [(← HolLight.GSYM REALLIM_NULL_ABS)] THEN
      MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
      EXISTS_TAC ([[\x. abs((f x - f c) pow 2 * inv(sin(x - c)))]]) THEN
      REWRITE_TAC [] THEN CONJ_TAC THENL
       [REWRITE_TAC [EVENTUALLY_WITHINREAL] THEN EXISTS_TAC ([[&1:real]]) THEN
        REWRITE_TAC [REAL_LT_01] THEN X_GEN_TAC ([[x:real]]) THEN
        REWRITE_TAC [IN_REAL_INTERVAL, REAL_ABS_MUL] THEN STRIP_TAC THEN
        BINOP_TAC THENL
         [AP_TERM_TAC THEN
          SUBGOAL_THEN ([[c = a \/ c = a + pi \/ a = &0 /\ c = &2 * pi]]) MP_TAC THENL [ALL_TAC, STRIP_TAC THEN ASM_REWRITE_TAC []] THEN
          MATCH_MP_TAC h10 THEN DISCH_TAC THEN
          SUBGOAL_THEN ([[&0 < abs(c - a) /\ abs(c - a) < pi \/
          &0 < abs(--(c - a) + pi) /\ abs(--(c - a) + pi) < pi]]) MP_TAC THENL [MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN
          DISCH_THEN (DISJ_CASES_THEN (MP_TAC o HolLight.MATCH_MP SIN_POS_PI)) THEN
          REWRITE_TAC [real_abs] THEN COND_CASES_TAC THEN
          ASM_REWRITE_TAC [SIN_NEG, REAL_NEG_0, SIN_PERIODIC_PI, REAL_LT_REFL],
          REWRITE_TAC [REAL_ABS_INV] THEN AP_TERM_TAC THEN
          SUBST1_TAC h11 THEN
          ASM_REWRITE_TAC [SIN_ADD, REAL_MUL_RZERO, REAL_ADD_RID] THEN
          REWRITE_TAC [REAL_EQ_SQUARE_ABS] THEN
          MP_TAC (← HolLight.SPEC ([[c - a:real]]) SIN_CIRCLE) THEN ASM_REWRITE_TAC [] THEN
          CONV_TAC rg],
        ALL_TAC] THEN
      REWRITE_TAC [REALLIM_NULL_ABS] THEN
      MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
      EXISTS_TAC ([[\x. real_integral (real_segment[c,x]) (\x. f' x pow 2) *
          abs((x - c) / sin(x - c))]]) THEN
      REWRITE_TAC [] THEN CONJ_TAC THENL
       [REWRITE_TAC [EVENTUALLY_WITHINREAL] THEN EXISTS_TAC ([[&1:real]]) THEN
        REWRITE_TAC [REAL_LT_01] THEN X_GEN_TAC ([[x:real]]) THEN
        REWRITE_TAC [IN_REAL_INTERVAL, REAL_ABS_MUL, real_div] THEN
        STRIP_TAC THEN REWRITE_TAC [REAL_MUL_ASSOC] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [REAL_ABS_POS] THEN
        REWRITE_TAC [REAL_ABS_POW, REAL_POW2_ABS] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC ([[(real_integral (real_interval[&0,x]) f' -
                   real_integral (real_interval[&0,c]) f') pow 2]]) THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN ([[(f' has_real_integral f c - f(&0)) (real_interval [&0,c]) /\
          (f' has_real_integral f x - f(&0)) (real_interval [&0,x])]]) MP_TAC THENL
           [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
            REWRITE_TAC [IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC,
            SIMP_TAC [HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
            ASM_REAL_ARITH_TAC],
          ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC ([[(real_integral (real_segment[c,x]) f') pow 2]]) THEN
        CONJ_TAC THENL
         [REWRITE_TAC [(← HolLight.GSYM REAL_LE_SQUARE_ABS)] THEN
          REWRITE_TAC [REAL_SEGMENT_INTERVAL] THEN COND_CASES_TAC THENL
           [MATCH_MP_TAC h12,
            MATCH_MP_TAC h13] THEN
          MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN
          REPEAT (CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC]) THEN
          FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] REAL_INTEGRABLE_SUBINTERVAL)) THEN
          REWRITE_TAC [SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC,
          ALL_TAC] THEN
        GEN_REWRITE_TAC HolLight.RAND_CONV [REAL_MUL_SYM] THEN
        MP_TAC (← HolLight.ISPECL [([[f':real->real]]), ([[real_segment[c,x] ]])] REAL_HOELDER_BOUND_2) THEN
        REWRITE_TAC [REAL_MEASURABLE_REAL_SEGMENT] THEN
        REWRITE_TAC [REAL_MEASURE_REAL_SEGMENT] THEN
        DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
         [MATCH_MP_TAC INTEGRABLE_IMP_REAL_MEASURABLE, ALL_TAC] THEN
        REWRITE_TAC [REAL_SEGMENT_INTERVAL] THEN COND_CASES_TAC THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] REAL_INTEGRABLE_SUBINTERVAL)) THEN
        REWRITE_TAC [SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC,
        ALL_TAC] THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [h14] THEN
      MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC [REALLIM_WITHINREAL] THEN
        X_GEN_TAC ([[e:real]]) THEN DISCH_TAC THEN MP_TAC (← HolLight.ISPECL [([[\x. (f':real->real) x pow 2]]), ([[&0:real]]), ([[&2 * pi]]),
          ([[c:real]]), ([[c:real]]), ([[e:real]])] REAL_INDEFINITE_INTEGRAL_CONTINUOUS) THEN
        ASM_REWRITE_TAC [IN_REAL_INTERVAL] THEN MATCH_MP_TAC MONO_EXISTS THEN
        X_GEN_TAC ([[d:real]]) THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
        X_GEN_TAC ([[x:real]]) THEN STRIP_TAC THEN
        REWRITE_TAC [REAL_SUB_RZERO, REAL_SEGMENT_INTERVAL] THEN
        COND_CASES_TAC THENL
         [FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [([[c:real]]), ([[x:real]])]),
          FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [([[x:real]]), ([[c:real]])])] THEN
        ASM_SIMP_TAC [REAL_LT_IMP_LE, REAL_INTEGRAL_NULL, REAL_LE_REFL,
                     REAL_SUB_REFL, REAL_ABS_0, REAL_SUB_RZERO],
        MATCH_MP_TAC REALLIM_ABS THEN ONCE_REWRITE_TAC [(← HolLight.GSYM REAL_INV_DIV)] THEN
        MATCH_MP_TAC REALLIM_INV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        MATCH_MP_TAC REALLIM_ATREAL_WITHINREAL THEN
        MP_TAC REALLIM_SIN_OVER_X THEN
        REWRITE_TAC [REALLIM_ATREAL, REAL_SUB_RZERO] THEN MESON_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!c d. c <= d /\
          real_interval[c,d] SUBSET real_interval[&0,&2 * pi] /\
          (!x. x IN real_interval(c,d) ==> ~(sin(x - a) = &0))
          ==> (g' has_real_integral g d - g c) (real_interval[c,d])]]) MP_TAC THENL
     [REWRITE_TAC [SUBSET_REAL_INTERVAL, IN_REAL_INTERVAL] THEN
      REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ASM_REWRITE_TAC [(← HolLight.GSYM REAL_NOT_LE)] THEN STRIP_TAC THEN
      SUBGOAL_THEN ([[g' absolutely_real_integrable_on real_interval[c,d] ]]) ASSUME_TAC THENL
       [MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMPROPER_SIMPLE THEN
        SUBGOAL_THEN ([[(\x. f' x pow 2) absolutely_real_integrable_on
        real_interval[&0,&2 * pi] /\
        (\x. (f x - f a) pow 2) absolutely_real_integrable_on
        real_interval[&0,&2 * pi] ]]) STRIP_ASSUME_TAC THENL
         [CONJ_TAC THEN MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_REAL_INTEGRABLE THEN
          ASM_REWRITE_TAC [REAL_LE_POW_2] THEN
          MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
          MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN
          MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN
          ASM_REWRITE_TAC [REAL_CONTINUOUS_ON_CONST],
          ALL_TAC] THEN
        SUBGOAL_THEN ([[!u v. real_interval[u,v] SUBSET real_interval(c,d)
              ==> g' real_integrable_on real_interval[u,v] ]]) ASSUME_TAC THENL
         [MAP_EVERY X_GEN_TAC [([[u:real]]), ([[v:real]])] THEN
          REWRITE_TAC [SUBSET_REAL_INTERVAL] THEN STRIP_TAC THENL
           [ASM_MESON_TAC [REAL_INTERVAL_EQ_EMPTY, REAL_INTEGRABLE_ON_EMPTY],
            ALL_TAC] THEN
          FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [([[u:real]]), ([[v:real]])]) THEN
          ASM_REWRITE_TAC [IN_REAL_INTERVAL, SUBSET_REAL_INTERVAL] THEN
          REWRITE_TAC [HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
          ANTS_TAC THENL [ALL_TAC, SIMP_TAC []] THEN
          CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
          GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_REAL_ARITH_TAC,
          ALL_TAC] THEN
        MATCH_MP_TAC h15 THEN CONJ_TAC THENL
         [MAP_EVERY X_GEN_TAC [([[u:real]]), ([[v:real]])] THEN
          REWRITE_TAC [SUBSET_REAL_INTERVAL] THEN STRIP_TAC THENL
           [ASM_MESON_TAC [REAL_INTERVAL_EQ_EMPTY,
                          ABSOLUTELY_REAL_INTEGRABLE_ON_EMPTY],
            ALL_TAC] THEN
          EXPAND_TAC "g'" THEN REWRITE_TAC [] THEN
          MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_SUB THEN CONJ_TAC THENL
           [MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_SUB THEN CONJ_TAC THEN
            FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
            REWRITE_TAC [SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC,
            MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_REAL_INTEGRABLE THEN
            ASM_REWRITE_TAC [REAL_LE_POW_2]] THEN
          MATCH_MP_TAC REAL_INTEGRABLE_EQ THEN
          EXISTS_TAC ([[\x. (f':real->real) x pow 2 - (f x - f a) pow 2 - g' x]]) THEN
          REWRITE_TAC [] THEN CONJ_TAC THENL
           [EXPAND_TAC "g'" THEN REWRITE_TAC [] THEN REAL_ARITH_TAC2,
            REPEAT (MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN CONJ_TAC) THEN
            ASM_SIMP_TAC [SUBSET_REAL_INTERVAL] THEN
            MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
            FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
            REWRITE_TAC [SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC],
          DISCH_TAC] THEN
        REWRITE_TAC [real_bounded, FORALL_IN_GSPEC] THEN
        MP_TAC (← HolLight.SPECL [([[\x. abs((g:real->real) x)]]), ([[real_interval[&0,&2 * pi] ]])] REAL_CONTINUOUS_ATTAINS_SUP) THEN
        ASM_REWRITE_TAC [REAL_COMPACT_INTERVAL, REAL_INTERVAL_EQ_EMPTY] THEN
        ASM_SIMP_TAC [REAL_CONTINUOUS_ON_ABS] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[w:real]]) STRIP_ASSUME_TAC) THEN
        EXISTS_TAC ([[&2 * abs(abs((g:real->real) w) +
                 real_integral (real_interval[&0,&2 * pi])
                               (\x. f' x pow 2))]]) THEN
        MAP_EVERY X_GEN_TAC [([[u:real]]), ([[v:real]])] THEN
        REWRITE_TAC [SUBSET_REAL_INTERVAL] THEN STRIP_TAC THENL
         [ASM_MESON_TAC [REAL_INTERVAL_EQ_EMPTY, REAL_INTEGRAL_EMPTY, h16],
          ALL_TAC] THEN
        SUBGOAL_THEN ([[(\x. f' x pow 2) absolutely_real_integrable_on
         real_interval[u,v] /\
         (\x. (f x - f a) pow 2) absolutely_real_integrable_on
         real_interval[u,v] /\
         g' absolutely_real_integrable_on real_interval[u,v] ]]) STRIP_ASSUME_TAC THENL
         [ASM_SIMP_TAC [SUBSET_REAL_INTERVAL] THEN CONJ_TAC THEN
          FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
          REWRITE_TAC [SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC,
          ALL_TAC] THEN
        MATCH_MP_TAC h17 THEN
        ASM_SIMP_TAC [REAL_INTEGRAL_POS, REAL_ABS_POS,
                     ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE,
                     ABSOLUTELY_REAL_INTEGRABLE_ABS] THEN
        TRANS_TAC REAL_LE_TRANS ([[real_integral (real_interval [u,v]) (\x. &2 * f' x pow 2 - g' x)]]) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_INTEGRAL_LE THEN
          ASM_SIMP_TAC [REAL_ABS_POS, ABSOLUTELY_REAL_INTEGRABLE_ABS,
                       ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE,
                       ABSOLUTELY_REAL_INTEGRABLE_SUB,
                       ABSOLUTELY_REAL_INTEGRABLE_LMUL] THEN
          EXPAND_TAC "g'" THEN REWRITE_TAC [IN_REAL_INTERVAL] THEN
          REPEAT STRIP_TAC THEN MATCH_MP_TAC h18 THEN
          REWRITE_TAC [REAL_LE_POW_2],
          ALL_TAC] THEN
        ASM_SIMP_TAC [REAL_INTEGRAL_SUB, REAL_INTEGRAL_LMUL,
                     ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE,
                     ABSOLUTELY_REAL_INTEGRABLE_SUB,
                     ABSOLUTELY_REAL_INTEGRABLE_LMUL] THEN
        MATCH_MP_TAC h19 THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_INTEGRAL_SUBSET_LE THEN
          ASM_SIMP_TAC [SUBSET_REAL_INTERVAL, REAL_LE_POW_2,
                       ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
          ASM_REAL_ARITH_TAC,
          ALL_TAC] THEN
        SUBGOAL_THEN ([[(g' has_real_integral g v - g u) (real_interval[u,v])]]) MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_REWRITE_TAC [SUBSET_REAL_INTERVAL] THEN
          CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
          GEN_TAC THEN REWRITE_TAC [IN_REAL_INTERVAL] THEN STRIP_TAC THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC,
          REWRITE_TAC [HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
          STRIP_TAC THEN ASM_REWRITE_TAC []] THEN
        MATCH_MP_TAC h20 THEN
        CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC [IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC,
        ASM_REWRITE_TAC [HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
        ASM_SIMP_TAC [ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE]] THEN
        ASM_CASES_TAC ([[c:real = d]]) THEN
        ASM_SIMP_TAC [REAL_INTEGRAL_NULL, REAL_LE_REFL, REAL_SUB_REFL] THEN
        SUBGOAL_THEN ([[c:real < d]]) ASSUME_TAC THENL
         [ASM_REWRITE_TAC [REAL_LT_LE], ALL_TAC] THEN
      TRANS_TAC EQ_TRANS ([[real_integral (real_interval[c,(c+d) / &2]) g' +
      real_integral (real_interval[(c+d) / &2,d]) g']]) THEN
      CONJ_TAC THENL
       [CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN
        ASM_SIMP_TAC [ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
        ASM_REAL_ARITH_TAC,
        ALL_TAC] THEN
      SUBST1_TAC h21 THEN
      BINOP_TAC THEN ONCE_REWRITE_TAC [(← HolLight.GSYM REAL_SUB_0)] THENL
       [SUBGOAL_THEN ([[(\x. real_integral(real_interval[x,(c + d) / &2]) g' -
             (g ((c + d) / &2) - g x))
         real_continuous_on (real_interval [c,(c + d) / &2])]]) MP_TAC THENL
         [REPEAT (MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN CONJ_TAC) THEN
          REWRITE_TAC [REAL_CONTINUOUS_ON_CONST] THENL
           [MATCH_MP_TAC REAL_INDEFINITE_INTEGRAL_CONTINUOUS_LEFT THEN
            MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
            FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
            REWRITE_TAC [SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC,
            FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] REAL_CONTINUOUS_ON_SUBSET)) THEN
            REWRITE_TAC [SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC],
          REWRITE_TAC [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[c:real]])) THEN
        REWRITE_TAC [IN_REAL_INTERVAL] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
        REWRITE_TAC [REAL_CONTINUOUS_WITHINREAL] THEN
        DISCH_THEN (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [h22] REALLIM_UNIQUE)) THEN
        CONJ_TAC THENL
         [HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
              let x1 ← ec (HolCore.Kernel.rand w)
              let x2 ← ExceptT.mk (HolLight.PART_MATCH (HolCore.Equal.lhand o HolCore.Kernel.rand) TRIVIAL_LIMIT_WITHIN_REALINTERVAL x1)
              pure (MP_TAC x2)) THEN
          REWRITE_TAC [IS_REALINTERVAL_INTERVAL, IN_REAL_INTERVAL] THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC, DISCH_THEN SUBST1_TAC] THEN
          DISCH_THEN (MP_TAC o HolLight.AP_TERM ([[(IN) ((c + d) / &2)]])) THEN
          REWRITE_TAC [IN_SING, IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC,
          MATCH_MP_TAC REALLIM_EVENTUALLY THEN
          REWRITE_TAC [EVENTUALLY_WITHINREAL] THEN
          EXISTS_TAC ([[&1]]) THEN REWRITE_TAC [REAL_LT_01] THEN
          REWRITE_TAC [IN_REAL_INTERVAL] THEN X_GEN_TAC ([[x:real]]) THEN
          STRIP_TAC THEN
          FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [([[x:real]]), ([[(c + d) / &2]])]) THEN
          REWRITE_TAC [HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
          ANTS_TAC THENL [ALL_TAC, SIMP_TAC [REAL_SUB_REFL]] THEN
          REWRITE_TAC [SUBSET_REAL_INTERVAL, IN_REAL_INTERVAL] THEN
          REPEAT (CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC]) THEN
          GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_REAL_ARITH_TAC],
        SUBGOAL_THEN ([[(\x. real_integral(real_interval[(c + d) / &2,x]) g' -
             (g x - g((c + d) / &2)))
         real_continuous_on (real_interval [(c + d) / &2,d])]]) MP_TAC THENL
         [REPEAT (MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN CONJ_TAC) THEN
          REWRITE_TAC [REAL_CONTINUOUS_ON_CONST] THENL
           [MATCH_MP_TAC REAL_INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT THEN
            MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
            FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
            REWRITE_TAC [SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC,
            FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] REAL_CONTINUOUS_ON_SUBSET)) THEN
            REWRITE_TAC [SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC],
          REWRITE_TAC [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[d:real]])) THEN
        REWRITE_TAC [IN_REAL_INTERVAL] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
        REWRITE_TAC [REAL_CONTINUOUS_WITHINREAL] THEN
        DISCH_THEN (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [h23] REALLIM_UNIQUE)) THEN
        CONJ_TAC THENL
         [HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
              let x1 ← ec (HolCore.Kernel.rand w)
              let x2 ← ExceptT.mk (HolLight.PART_MATCH (HolCore.Equal.lhand o HolCore.Kernel.rand) TRIVIAL_LIMIT_WITHIN_REALINTERVAL x1)
              pure (MP_TAC x2)) THEN
          REWRITE_TAC [IS_REALINTERVAL_INTERVAL, IN_REAL_INTERVAL] THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC, DISCH_THEN SUBST1_TAC] THEN
          DISCH_THEN (MP_TAC o HolLight.AP_TERM ([[(IN) ((c + d) / &2)]])) THEN
          REWRITE_TAC [IN_SING, IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC,
          MATCH_MP_TAC REALLIM_EVENTUALLY THEN
          REWRITE_TAC [EVENTUALLY_WITHINREAL] THEN
          EXISTS_TAC ([[&1]]) THEN REWRITE_TAC [REAL_LT_01] THEN
          REWRITE_TAC [IN_REAL_INTERVAL] THEN X_GEN_TAC ([[x:real]]) THEN
          STRIP_TAC THEN
          FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [([[(c + d) / &2]]), ([[x:real]])]) THEN
          REWRITE_TAC [HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
          ANTS_TAC THENL [ALL_TAC, SIMP_TAC [REAL_SUB_REFL]] THEN
          REWRITE_TAC [SUBSET_REAL_INTERVAL, IN_REAL_INTERVAL] THEN
          REPEAT (CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC]) THEN
          GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_REAL_ARITH_TAC]],
      ALL_TAC] THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPECL [([[a + pi]]), ([[&2 * pi]])] th) THEN
      MP_TAC (← HolLight.SPECL [([[a:real]]), ([[a + pi]])] th) THEN
      MP_TAC (← HolLight.SPECL [([[&0:real]]), ([[a:real]])] th))) THEN
    MATCH_MP_TAC h24 THEN
    REWRITE_TAC [SUBSET_REAL_INTERVAL, IN_REAL_INTERVAL] THEN CONJ_TAC THENL
     [REPEAT (CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC]) THEN
      GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC [(← HolLight.GSYM REAL_NEG_SUB)] THEN
      REWRITE_TAC [SIN_NEG, REAL_NEG_EQ_0] THEN
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SIN_POS_PI THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REPEAT (CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC]) THEN
      GEN_TAC THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SIN_POS_PI THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REPEAT (CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC]) THEN
      GEN_TAC THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC [h25] THEN
      REWRITE_TAC [SIN_PERIODIC_PI, REAL_NEG_EQ_0] THEN
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SIN_POS_PI THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC (MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [h26] HAS_REAL_INTEGRAL_COMBINE))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC, REWRITE_TAC [(← HolLight.GSYM IMP_CONJ_ALT)]] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [h27] HAS_REAL_INTEGRAL_COMBINE)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [h28] THEN
    EXPAND_TAC "g" THEN REWRITE_TAC [] THEN
    ASM_REWRITE_TAC [h29] THEN
    REWRITE_TAC [TAN_PERIODIC_NPI, REAL_SUB_REFL] THEN
    MAP_EVERY UNDISCH_TAC [([[(\x. f x pow 2) real_integrable_on real_interval[&0,&2 * pi] ]]),
     ([[(\x. f' x pow 2) real_integrable_on real_interval[&0,&2 * pi] ]])] THEN
    REWRITE_TAC [real_integrable_on, LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [RIGHT_IMP_FORALL_THM] THEN
    MAP_EVERY X_GEN_TAC [([[i':real]]), ([[i:real]])] THEN
    GEN_REWRITE_TAC HolCore.Lib.I [h30] THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP HAS_REAL_INTEGRAL_SUB) THEN
    REWRITE_TAC [IMP_IMP] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP HAS_REAL_INTEGRAL_SUB) THEN
    EXPAND_TAC "g'" THEN
    REWRITE_TAC [h31] THEN
    MP_TAC (← HolLight.ASSUME ([[(f has_real_integral &0) (real_interval [&0,&2 * pi])]])) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[&2 * (f:real->real) a]]) o
        HolLight.MATCH_MP HAS_REAL_INTEGRAL_LMUL) THEN
    REWRITE_TAC [(← HolLight.GSYM IMP_CONJ_ALT)] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP HAS_REAL_INTEGRAL_ADD) THEN
    REWRITE_TAC [REAL_SUB_ADD, REAL_MUL_RZERO] THEN
    DISCH_THEN (fun th => CONJ_TAC THEN MP_TAC th) THENL
     [GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.GSYM REAL_SUB_LE)] THEN
      MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_CONJ_ALT] HAS_REAL_INTEGRAL_POS) THEN
      SIMP_TAC [REAL_LE_ADD, REAL_LE_POW_2],
      ALL_TAC] THEN
    ASM_CASES_TAC ([[i':real = i]]) THEN ASM_REWRITE_TAC [REAL_SUB_REFL] THEN
    HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
        let x1 ← ec (HolCore.Equal.lhand w)
        let x2 ← ExceptT.mk (HolLight.PART_MATCH (HolCore.Equal.lhand o HolCore.Kernel.rand) HAS_REAL_INTEGRAL_NEGLIGIBLE_EQ x1)
        pure (MP_TAC x2)) THEN
    SIMP_TAC [REAL_LE_ADD, REAL_LE_POW_2] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [REAL_SOS_EQ_0] THEN
    ASM_CASES_TAC ([[(f:real->real) a = &0]]) THEN ASM_REWRITE_TAC [] THENL
     [POP_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC [REAL_SUB_RZERO, REAL_SUB_0],
      REWRITE_TAC [IN_GSPEC, REAL_NEGLIGIBLE_REAL_INTERVAL] THEN
      REWRITE_TAC [REAL_INTERVAL_EQ_EMPTY] THEN
      MP_TAC PI_POS THEN REAL_ARITH_TAC2] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN ([[!u v. &0 <= u /\ u < v /\ v <= &2 * pi /\
          (!x. u < x /\ x < v ==> ~(sin(x - a) = &0))
          ==> ?c. !x. u <= x /\ x <= v ==> f(x) = c * sin(x - a)]]) MP_TAC THENL
     [MAP_EVERY X_GEN_TAC [([[u:real]]), ([[v:real]])] THEN STRIP_TAC THEN
      SUBGOAL_THEN ([[?c. !x. u < x /\ x < v ==> f x = c * sin (x - a)]]) MP_TAC THENL
       [ALL_TAC,
        MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC [(← HolLight.GSYM IN_REAL_INTERVAL)] THEN
        GEN_TAC THEN DISCH_TAC THEN
        MATCH_MP_TAC REAL_CONTINUOUS_AGREE_ON_CLOSURE_INTERVAL THEN
        ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
         [FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] REAL_CONTINUOUS_ON_SUBSET)) THEN
          REWRITE_TAC [SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC,
          REWRITE_TAC [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
          X_GEN_TAC ([[w:real]]) THEN REWRITE_TAC [IN_REAL_INTERVAL] THEN
          STRIP_TAC THEN
          MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_WITHINREAL THEN
          REAL_DIFFERENTIABLE_TAC]] THEN
      ASM_SIMP_TAC [h32] THEN
      REWRITE_TAC [h33] THEN
      MATCH_MP_TAC REAL_WLOG_LT THEN REWRITE_TAC [] THEN
      CONJ_TAC THENL [MESON_TAC [], ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [([[x:real]]), ([[y:real]])] THEN REPEAT STRIP_TAC THEN
      MP_TAC (← HolLight.SPECL [([[f:real->real]]), ([[\x. inv(sin(x - a))]]),
                    ([[f':real->real]]), ([[\x. --(cos(x - a) / sin(x - a) pow 2)]]),
                    ([[x:real]]), ([[y:real]])] ABSOLUTE_REAL_INTEGRATION_BY_PARTS_SUM) THEN
      ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
          REWRITE_TAC [SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC,
          X_GEN_TAC ([[z:real]]) THEN REWRITE_TAC [IN_REAL_INTERVAL] THEN
          STRIP_TAC THEN
          SUBGOAL_THEN ([[(f' has_real_integral f x - f(&0)) (real_interval[&0,x]) /\
          (f' has_real_integral f z - f(&0)) (real_interval[&0,z])]]) MP_TAC THENL
           [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
            REWRITE_TAC [IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC,
            REWRITE_TAC [HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
            STRIP_TAC] THEN
          CONJ_TAC THENL
           [FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
            REWRITE_TAC [SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC,
            MP_TAC (← HolLight.SPECL [([[f':real->real]]), ([[&0:real]]), ([[z:real]]), ([[x:real]])] REAL_INTEGRAL_COMBINE) THEN
            ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC],
          MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_CONTINUOUS THEN
          REWRITE_TAC [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
          X_GEN_TAC ([[w:real]]) THEN REWRITE_TAC [IN_REAL_INTERVAL] THEN
          STRIP_TAC THEN
          MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_WITHINREAL THEN
          REAL_DIFFERENTIABLE_TAC THEN REWRITE_TAC [REAL_POW_EQ_0, ARITH_EQ] THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC,
          X_GEN_TAC ([[z:real]]) THEN REWRITE_TAC [IN_REAL_INTERVAL] THEN
          STRIP_TAC THEN MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS THEN
          ASM_REWRITE_TAC [] THEN
          X_GEN_TAC ([[w:real]]) THEN REWRITE_TAC [IN_REAL_INTERVAL] THEN
          STRIP_TAC THEN REAL_DIFF_TAC THEN CONJ_TAC THENL
           [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC,
            REAL_ARITH_TAC2]],
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o HolLight.SPEC ([[y:real]])))] THEN
      REWRITE_TAC [IN_REAL_INTERVAL] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      REWRITE_TAC [h34] THEN
      MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_CONJ] HAS_REAL_INTEGRAL_UNIQUE) THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] HAS_REAL_INTEGRAL_NEGLIGIBLE)) THEN
      X_GEN_TAC ([[z:real]]) THEN
      REWRITE_TAC [IN_DIFF, IN_ELIM_THM, IN_REAL_INTERVAL] THEN
      ONCE_REWRITE_TAC [DE_MORGAN_THM] THEN REWRITE_TAC [] THEN STRIP_TAC THENL
       [ASM_REAL_ARITH_TAC, ASM_REWRITE_TAC []] THEN
      REWRITE_TAC [real_div, tan, REAL_INV_MUL, REAL_INV_INV, REAL_INV_POW] THEN
      REAL_ARITH_TAC2,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!u v c. u <= v
            ==> real_integral(real_interval[u,v]) (\x. c * sin(x - a)) =
                c * (cos(u - a) - cos(v - a))]]) ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC (← HolLight.SPECL [([[\x. --(c * cos(x - a))]]), ([[\x. c * sin(x - a)]]),
              ([[u:real]]), ([[v:real]])] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
      ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC [] THEN
        X_GEN_TAC ([[w:real]]) THEN REWRITE_TAC [IN_REAL_INTERVAL] THEN
        STRIP_TAC THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC2,
        REWRITE_TAC [HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
        DISCH_THEN (SUBST1_TAC o HolLight.CONJUNCT2) THEN REAL_ARITH_TAC2],
      ALL_TAC] THEN
    ASM_CASES_TAC ([[a = &0]]) THENL
     [POP_ASSUM SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [REAL_ADD_LID, REAL_ADD_RID, REAL_SUB_RZERO]) THEN
      REWRITE_TAC [REAL_SUB_RZERO] THEN
      DISCH_THEN (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPECL [([[pi]]), ([[&2 * pi]])] th) THEN
        MP_TAC (← HolLight.SPECL [([[&0:real]]), ([[pi]])] th))) THEN
      MATCH_MP_TAC h35 THEN
      REWRITE_TAC [SUBSET_REAL_INTERVAL, IN_REAL_INTERVAL] THEN CONJ_TAC THENL
       [REPEAT (CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC]) THEN
        GEN_TAC THEN STRIP_TAC THEN
        MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SIN_POS_PI THEN
        ASM_REAL_ARITH_TAC,
        ALL_TAC] THEN
      CONJ_TAC THENL
       [REPEAT (CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC]) THEN
        X_GEN_TAC ([[x:real]]) THEN STRIP_TAC THEN
        MP_TAC (← HolLight.SPEC ([[x - pi]]) SIN_PERIODIC_PI) THEN
        REWRITE_TAC [REAL_SUB_ADD, REAL_SUB_RZERO] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [REAL_NEG_EQ_0] THEN
        MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SIN_POS_PI THEN
        ASM_REAL_ARITH_TAC,
        ALL_TAC] THEN
      DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC ([[c1:real]])) MP_TAC) THEN
      DISCH_THEN (X_CHOOSE_TAC ([[c2:real]])) THEN
      SUBGOAL_THEN ([[c2:real = c1:real]]) SUBST_ALL_TAC THENL
       [SUBGOAL_THEN ([[real_integral(real_interval[&0,pi]) f +
        real_integral(real_interval[pi,&2*pi]) f = &0]]) MP_TAC THENL
         [UNDISCH_TAC ([[(f has_real_integral &0) (real_interval[&0,&2 * pi])]]) THEN
          REWRITE_TAC [HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN STRIP_TAC THEN
          HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
              let x1 ← ec (HolCore.Equal.lhand w)
              let x2 ← ExceptT.mk (HolLight.PART_MATCH (HolCore.Equal.lhand o HolCore.Kernel.rand) REAL_INTEGRAL_COMBINE x1)
              pure (MP_TAC x2)) THEN
          ANTS_TAC THENL
           [REPEAT (CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC]) THEN
            FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
            REWRITE_TAC [SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC,
            DISCH_THEN SUBST1_TAC] THEN
          ASM_REWRITE_TAC [],
          ALL_TAC] THEN
        SUBGOAL_THEN ([[real_integral(real_interval[&0,pi]) f =
        real_integral(real_interval[&0,pi]) (\x. c1 * sin(x)) /\
        real_integral(real_interval[pi,&2*pi]) f =
        real_integral(real_interval[pi,&2*pi]) (\x. c2 * sin(x))]]) MP_TAC THENL
         [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_EQ THEN
          REWRITE_TAC [IN_REAL_INTERVAL] THEN ASM_SIMP_TAC [],
          ALL_TAC] THEN
        FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPECL [([[pi]]), ([[&2 * pi]]), ([[c2:real]])] th) THEN
          MP_TAC (← HolLight.SPECL [([[&0:real]]), ([[pi:real]]), ([[c1:real]])] th))) THEN
        REPLICATE_TAC 2 (ANTS_TAC THENL [ASM_REAL_ARITH_TAC, DISCH_THEN SUBST1_TAC]) THEN
        DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
        REWRITE_TAC [COS_0, COS_PI, COS_NPI] THEN CONV_TAC rg,
        ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [([[c1:real]]), ([[&0:real]])] THEN X_GEN_TAC ([[x:real]]) THEN
      REPLICATE_TAC 2 (FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[x:real]]))) THEN
      REWRITE_TAC [REAL_SUB_RZERO] THEN REAL_ARITH_TAC2,
      ALL_TAC] THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPECL [([[a + pi]]), ([[&2 * pi]])] th) THEN
      MP_TAC (← HolLight.SPECL [([[a:real]]), ([[a + pi]])] th) THEN
      MP_TAC (← HolLight.SPECL [([[&0:real]]), ([[a:real]])] th))) THEN
    MATCH_MP_TAC h36 THEN
    REWRITE_TAC [SUBSET_REAL_INTERVAL, IN_REAL_INTERVAL] THEN CONJ_TAC THENL
     [REPEAT (CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC]) THEN
      GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC [(← HolLight.GSYM REAL_NEG_SUB)] THEN
      REWRITE_TAC [SIN_NEG, REAL_NEG_EQ_0] THEN
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SIN_POS_PI THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REPEAT (CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC]) THEN
      GEN_TAC THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SIN_POS_PI THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REPEAT (CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC]) THEN
      GEN_TAC THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC [h37] THEN
      REWRITE_TAC [SIN_PERIODIC_PI, REAL_NEG_EQ_0] THEN
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SIN_POS_PI THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC ([[c1:real]])) MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC ([[c2:real]])) MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_TAC ([[c3:real]])) THEN
    MP_TAC h38 THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC,
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC,
        FIRST_X_ASSUM ACCEPT_TAC,
        REWRITE_TAC [h39] THEN
        REWRITE_TAC [SIN_PERIODIC, REAL_ADD_RID],
        ONCE_REWRITE_TAC [(← HolLight.GSYM REAL_NEG_SUB)] THEN
        REWRITE_TAC [SIN_NEG, REAL_NEG_EQ_0] THEN
        MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SIN_POS_PI THEN
        ASM_REAL_ARITH_TAC],
      DISCH_THEN SUBST_ALL_TAC] THEN
    SUBGOAL_THEN ([[c2:real = c1:real]]) SUBST_ALL_TAC THENL
     [SUBGOAL_THEN ([[real_integral(real_interval[&0,a]) f +
      real_integral(real_interval[a,a+pi]) f +
      real_integral(real_interval[a+pi,&2*pi]) f = &0]]) MP_TAC THENL
       [UNDISCH_TAC ([[(f has_real_integral &0) (real_interval[&0,&2 * pi])]]) THEN
        REWRITE_TAC [HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN STRIP_TAC THEN
        HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
            let x1 ← ec (HolCore.Equal.lhand w)
            let x2 ← ec (HolCore.Kernel.rand x1)
            let x3 ← ExceptT.mk (HolLight.PART_MATCH (HolCore.Equal.lhand o HolCore.Kernel.rand) REAL_INTEGRAL_COMBINE x2)
            pure (MP_TAC x3)) THEN
        ANTS_TAC THENL
         [REPEAT (CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC]) THEN
          FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
          REWRITE_TAC [SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC,
          DISCH_THEN SUBST1_TAC] THEN
        HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
            let x1 ← ec (HolCore.Equal.lhand w)
            let x2 ← ExceptT.mk (HolLight.PART_MATCH (HolCore.Equal.lhand o HolCore.Kernel.rand) REAL_INTEGRAL_COMBINE x1)
            pure (MP_TAC x2)) THEN
        ANTS_TAC THENL
         [REPEAT (CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC]) THEN
          FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
          REWRITE_TAC [SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC,
          DISCH_THEN SUBST1_TAC] THEN
        ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[real_integral(real_interval[&0,a]) f =
      real_integral(real_interval[&0,a]) (\x. c1 * sin(x - a)) /\
      real_integral(real_interval[a,a+pi]) f =
      real_integral(real_interval[a,a+pi]) (\x. c2 * sin(x - a)) /\
      real_integral(real_interval[a+pi,&2*pi]) f =
      real_integral(real_interval[a+pi,&2*pi]) (\x. c1 * sin(x - a))]]) MP_TAC THENL
       [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_EQ THEN
        REWRITE_TAC [IN_REAL_INTERVAL] THEN ASM_SIMP_TAC [],
        ALL_TAC] THEN
      FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPECL [([[a + pi]]), ([[&2 * pi]]), ([[c1:real]])] th) THEN
        MP_TAC (← HolLight.SPECL [([[a:real]]), ([[a + pi]]), ([[c2:real]])] th) THEN
        MP_TAC (← HolLight.SPECL [([[&0:real]]), ([[a:real]]), ([[c1:real]])] th))) THEN
      REPLICATE_TAC 3 (ANTS_TAC THENL [ASM_REAL_ARITH_TAC, DISCH_THEN SUBST1_TAC]) THEN
      DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
      REWRITE_TAC [REAL_ADD_SUB, COS_PI, REAL_SUB_REFL, COS_0] THEN
      REWRITE_TAC [REAL_SUB_LZERO, h40] THEN
      REWRITE_TAC [COS_PERIODIC, COS_NEG] THEN CONV_TAC rg,
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [([[c1:real]]), ([[a:real]])] THEN X_GEN_TAC ([[x:real]]) THEN
    REPLICATE_TAC 3 (FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[x:real]]))) THEN
    REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval WIRTINGER_INEQUALITY

#eval phrase 9
def SCALED_WIRTINGER_INEQUALITY : thm := keep "SCALED_WIRTINGER_INEQUALITY" fun _ => (do
  let h10 ← rr (← ExceptT.mk [[&2 * pi * x <= &2 * pi <=> pi * x <= pi * &1]])
  let h9 ← rf (← ExceptT.mk [[&0 < pi ==> inv(&2 * pi) * &2 * pi * x = x]])
  let h8 ← rf (← ExceptT.mk [[&0 < z ==> (x / z = y / z <=> x = y)]])
  let h7 ← rr (← ExceptT.mk [[&0 < &2 * x <=> &0 < x]])
  let h6 ← rr (← ExceptT.mk [[&0 < &2 * x <=> &0 < x]])
  let h5 ← rf (← ExceptT.mk [[&0 < t ==> inv t * t * x = x]])
  let h4 ← tt (← ExceptT.mk [[(p ==> p') /\ (p' ==> q ==> q') ==> (p /\ q ==> p' /\ q')]])
  let h3 ← rr (← ExceptT.mk [[inv x * y:real = y / x]])
  let h2 ← rr (← ExceptT.mk [[&0 < &2 * x <=> &0 < x]])
  let h1 ← rr (← ExceptT.mk [[&0 < &2 * x <=> &0 < x]])
  prove ([[!f f'.
      (!x. x IN real_interval[&0,&1]
           ==> (f' has_real_integral (f x - f(&0))) (real_interval[&0,x])) /\
      f(&1) = f(&0) /\
      (f has_real_integral &0) (real_interval[&0,&1]) /\
      (\x. f'(x) pow 2) real_integrable_on real_interval[&0,&1]
      ==> (\x. f(x) pow 2) real_integrable_on real_interval[&0,&1] /\
          real_integral (real_interval[&0,&1]) (\x. (&2 * pi * f(x)) pow 2) <=
          real_integral (real_interval[&0,&1]) (\x. f'(x) pow 2) /\
          (real_integral (real_interval[&0,&1]) (\x. (&2 * pi * f(x)) pow 2) =
           real_integral (real_interval[&0,&1]) (\x. f'(x) pow 2)
           ==> ?c a. !x. x IN real_interval[&0,&1]
                         ==> f x = c * sin(&2 * pi * x - a))]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [([[(\x. f(inv(&2 * pi) * x)):real->real]]),
      ([[(\x. inv(&2 * pi) * f'(inv(&2 * pi) * x)):real->real]])] WIRTINGER_INEQUALITY) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [X_GEN_TAC ([[x:real]]) THEN REWRITE_TAC [IN_REAL_INTERVAL] THEN STRIP_TAC THEN
        SUBGOAL_THEN ([[!x. x = inv(&2 * pi) * &2 * pi * x]]) MP_TAC THENL
         [MP_TAC PI_POS THEN CONV_TAC rf, ALL_TAC] THEN
        DISCH_THEN (fun th => GEN_REWRITE_TAC HolLight.LAND_CONV [th]) THEN
        MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
        FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[x / (&2 * pi)]])) THEN
        SIMP_TAC [IN_REAL_INTERVAL, REAL_LE_LDIV_EQ, REAL_LE_RDIV_EQ,
                 PI_POS, h1] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[inv(&2 * pi)]]) o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] HAS_REAL_INTEGRAL_STRETCH)) THEN
        ANTS_TAC THENL [MP_TAC PI_POS THEN CONV_TAC rf, ALL_TAC] THEN
        REWRITE_TAC [IMAGE_STRETCH_REAL_INTERVAL, REAL_SUB_RZERO] THEN
        REWRITE_TAC [REAL_INTERVAL_EQ_EMPTY, REAL_MUL_RZERO, REAL_ADD_RID,
                    REAL_ABS_INV, REAL_INV_INV, REAL_ABS_MUL,
                    REAL_ABS_NUM, REAL_ABS_PI] THEN
        ASM_SIMP_TAC [REAL_LT_LDIV_EQ, REAL_LT_IMP_LE, REAL_DIV_LMUL, PI_POS,
                     REAL_LT_IMP_NZ, h2] THEN
        COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
        REWRITE_TAC [h3] THEN
        REWRITE_TAC [(← HolLight.GSYM REAL_MUL_ASSOC)],
        UNDISCH_TAC ([[(f:real->real) (&1) = f (&0)]]) THEN
        MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN
        AP_TERM_TAC THEN MP_TAC PI_POS THEN CONV_TAC rf,
        FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[inv(&2 * pi)]]) o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] HAS_REAL_INTEGRAL_STRETCH)),
        REWRITE_TAC [REAL_POW_MUL] THEN MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN
        FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[inv(&2 * pi)]]) o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] REAL_INTEGRABLE_STRETCH))] THEN
      (ANTS_TAC THENL [MP_TAC PI_POS THEN CONV_TAC rf, ALL_TAC] THEN
       REWRITE_TAC [IMAGE_STRETCH_REAL_INTERVAL, REAL_SUB_RZERO] THEN
       REWRITE_TAC [REAL_INV_INV, REAL_MUL_RZERO, REAL_INTERVAL_EQ_EMPTY] THEN
       CONV_TAC REAL_RAT_REDUCE_CONV THEN
       COND_CASES_TAC THEN REWRITE_TAC [REAL_MUL_RID] THEN
       MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC),
      ALL_TAC] THEN
    MATCH_MP_TAC h4 THEN
    CONJ_TAC THENL
     [DISCH_THEN (MP_TAC o HolLight.SPEC ([[&2 * pi]]) o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] REAL_INTEGRABLE_STRETCH)) THEN
      REWRITE_TAC [IMAGE_STRETCH_REAL_INTERVAL, REAL_LE_INV_EQ] THEN
      ANTS_TAC THENL [MP_TAC PI_POS THEN CONV_TAC rf, ALL_TAC] THEN
      REWRITE_TAC [REAL_INTERVAL_EQ_EMPTY, (← HolLight.GSYM REAL_NOT_LE), COND_SWAP] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THENL
       [ALL_TAC, MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC] THEN
      SIMP_TAC [PI_POS, REAL_LT_IMP_NZ, REAL_MUL_LINV, REAL_MUL_RZERO,
               h5,
               h6],
      DISCH_TAC] THEN
    SUBGOAL_THEN ([[real_integral (real_interval [&0,&2 * pi])
                  (\x. f (inv (&2 * pi) * x) pow 2) =
    real_integral (real_interval [&0,&1]) (\x. (&2 * pi * f x) pow 2) /
    (&2 * pi) /\
    real_integral (real_interval [&0,&2 * pi])
                  (\x. (inv (&2 * pi) * f' (inv (&2 * pi) * x)) pow 2) =
    real_integral (real_interval [&0,&1]) (\x. f' x pow 2) / (&2 * pi)]]) (CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_SIMP_TAC [REAL_POW_MUL, REAL_MUL_ASSOC, REAL_INTEGRAL_LMUL] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC ([[(\x. f x pow 2) real_integrable_on real_interval[&0,&1] ]]),
        UNDISCH_TAC ([[(\x. f' x pow 2) real_integrable_on real_interval[&0,&1] ]])] THEN
      REWRITE_TAC [real_integrable_on] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[y:real]]) MP_TAC) THEN
      DISCH_THEN (fun th => HolLight.tactic_of do
        pure (SUBST1_TAC (← HolLight.MATCH_MP REAL_INTEGRAL_UNIQUE th) THEN
        MP_TAC (← HolLight.SPEC ([[inv(&2 * pi)]]) (← HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] HAS_REAL_INTEGRAL_STRETCH) th)))) THEN
      REWRITE_TAC [IMAGE_STRETCH_REAL_INTERVAL, REAL_LE_INV_EQ] THEN
      (ANTS_TAC THENL [MP_TAC PI_POS THEN CONV_TAC rf, ALL_TAC]) THEN
      REWRITE_TAC [REAL_INTERVAL_EQ_EMPTY] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      (COND_CASES_TAC THENL
        [ALL_TAC, MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC]) THEN
      REWRITE_TAC [REAL_INV_INV, REAL_ABS_INV, REAL_ABS_NUM,
                  REAL_ABS_MUL, REAL_ABS_PI] THEN
      REWRITE_TAC [REAL_MUL_RZERO, REAL_MUL_RID] THEN
      SIMP_TAC [HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL, REAL_INTEGRAL_LMUL] THEN
      STRIP_TAC THEN MP_TAC PI_POS THEN CONV_TAC rf,
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_AND THEN
    SIMP_TAC [REAL_LE_DIV2_EQ, PI_POS, h7,
             h8] THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC [] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[c:real]]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[a:real]]) THEN
    REWRITE_TAC [IN_REAL_INTERVAL] THEN DISCH_THEN (fun th => HolLight.tactic_of do
        pure (X_GEN_TAC ([[x:real]]) THEN STRIP_TAC THEN MP_TAC (← HolLight.SPEC ([[&2 * pi * x]]) th))) THEN
    ASM_SIMP_TAC [PI_POS, h9,
                 REAL_LE_MUL, REAL_POS, REAL_LT_IMP_LE] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC [h10] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC)
  : ExceptT String IO thm).run
#eval SCALED_WIRTINGER_INEQUALITY

/- ------------------------------------------------------------------------- -/
/- Part 2: a very special case of Green's theorem for a convex area.         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 10
def GREEN_AREA_THEOREM : thm := keep "GREEN_AREA_THEOREM" fun _ => (do
  prove ([[!(g:real^1->real^2) g' u a.
        simple_path g /\ pathstart g = a /\ pathfinish g = a /\
        g absolutely_continuous_on interval[vec 0,vec 1] /\
        negligible u /\
        (!t. t IN interval[vec 0,vec 1] DIFF u
             ==> (g has_vector_derivative g'(t)) (at t))
        ==> (\t. lift(g'(t)$1 * g(t)$2)) integrable_on
            interval[vec 0,vec 1] /\
            norm(integral (interval[vec 0,vec 1])
                          (\t. lift(g'(t)$1 * g(t)$2))) =
            measure(inside(path_image g))]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← HolLight.SPEC ([[g:real^1->real^2]]) GREEN_AREA_ABS_ALT) THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_SPIKE,
      DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN AP_TERM_TAC THEN
      MATCH_MP_TAC INTEGRAL_SPIKE] THEN
    EXISTS_TAC ([[u:real^1->bool]]) THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC ([[x:real^1]]) THEN DISCH_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC [(← HolLight.GSYM LIFT_EQ)] THEN
    MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
    MAP_EVERY EXISTS_TAC [([[g:real^1->real^2]]), ([[x:real^1]])] THEN
    ASM_SIMP_TAC [] THEN
    REWRITE_TAC [(← HolLight.GSYM VECTOR_DERIVATIVE_WORKS), VECTOR_DIFFERENTIABLE] THEN
    ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval GREEN_AREA_THEOREM

/- ------------------------------------------------------------------------- -/
/- Part 3: Isoperimetric theorem for a convex curve.                         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 11
def ISOPERIMETRIC_THEOREM_CONVEX : thm := keep "ISOPERIMETRIC_THEOREM_CONVEX" fun _ => (do
  let h22 ← sr (← ExceptT.mk [[s SUBSET t /\ ~(s PSUBSET t) ==> s = t]])
  let h21 ← ms [] (← ExceptT.mk [[negligible t ==> P t ==> ?s. negligible s /\ P s]])
  let h20 ← tt (← ExceptT.mk [[p /\ ~q <=> ~(p ==> q)]])
  let h19 ← rr (← ExceptT.mk [[&0 <= x /\ &0 <= y ==> (x + y:real = &0 <=> x = &0 /\ y = &0)]])
  let h18 ← va (← ExceptT.mk [[(a + b) - b:real^N = a]])
  let h17 ← tt (← ExceptT.mk [[p /\ (p /\ q ==> r ==> s) ==> (p ==> q /\ (q ==> r)) ==> s]])
  let h16 ← ms [DROP_EQ, REAL_SUB_0] (← ExceptT.mk [[drop x = drop y <=> drop y - drop x = &0]])
  let h15 ← rr (← ExceptT.mk [[drop x <= drop y <=> &0 <= drop y - drop x]])
  let h14 ← tt (← ExceptT.mk [[(p ==> q /\ r) <=> p ==> q /\ (q ==> r)]])
  let h13 ← rr (← ExceptT.mk [[x * &4 * pi = &4 * pi * x]])
  let h12 ← rg (← ExceptT.mk [[s pow 2 = &1
         ==> (x' - &2 * pi * s * y) pow 2 + (y' pow 2 - (&2 * pi * y) pow 2) =
             (x' pow 2 + y' pow 2) - &4 * pi * s * x' * y]])
  let h11 ← rf (← ExceptT.mk [[&0 < z ==> (x = y / (&4 * z) <=> y - x * &4 * z = &0)]])
  let h10 ← rr (← ExceptT.mk [[&0:real < &4 * x <=> &0 < x]])
  let h9 ← va (← ExceptT.mk [[b - a:real^N = c ==> b = a + c]])
  let h8 ← rr (← ExceptT.mk [[x - y:real = &0 <=> y = x]])
  let h7 ← rr (← ExceptT.mk [[&0 < l ==> abs l = l]])
  let h6 ← rr (← ExceptT.mk [[&0 < l ==> abs l = l]])
  let h5 ← rr (← ExceptT.mk [[&0 < l ==> abs l = l]])
  let h4 ← rr (← ExceptT.mk [[&0 < l ==> abs l = l]])
  let h3 ← na (← ExceptT.mk [[norm(a - a:real^2) = d ==> d = &0]])
  let h2 ← va (← ExceptT.mk [[b - a:real^2 = &0 % c ==> b = a]])
  let h1 ← rr (← ExceptT.mk [[&0 <= b <=> b = &0 \/ &0 < b]])
  prove ([[!L g:real^1->real^2.
        rectifiable_path g /\
        simple_path g /\
        pathfinish g = pathstart g /\
        convex(inside(path_image g)) /\
        path_length g = L
        ==> measure(inside(path_image g)) <= L pow 2 / (&4 * pi) /\
            (measure(inside(path_image g)) =  L pow 2 / (&4 * pi)
             ==> ?a r. path_image g = sphere(a,r))]])
   (MAP_EVERY X_GEN_TAC [([[L:real]]), ([[g0:real^1->real^2]])] THEN STRIP_TAC THEN
    MP_TAC (← HolLight.ISPEC ([[g0:real^1->real^2]]) SIMPLE_PATH_LENGTH_POS_LT) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o HolLight.MATCH_MP SIMPLE_PATH_IMP_PATH) THEN
    MP_TAC (← HolLight.ISPEC ([[path_image g0:real^2->bool]]) DIAMETER_COMPACT_ATTAINED) THEN
    ASM_SIMP_TAC [LEFT_IMP_EXISTS_THM, PATH_IMAGE_NONEMPTY,
                 COMPACT_PATH_IMAGE] THEN
    MAP_EVERY X_GEN_TAC [([[a:real^2]]), ([[b:real^2]])] THEN STRIP_TAC THEN
    ABBREV_TAC ([[baseline:real^2 = b - a]]) THEN
    REPEAT (POP_ASSUM MP_TAC) THEN
    GEOM_BASIS_MULTIPLE_TAC 1 ([[baseline:real^2]]) THEN
    X_GEN_TAC ([[baseline:real]]) THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [h1] THEN
    STRIP_TAC THEN REPEAT GEN_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM (SUBST_ALL_TAC o HolLight.MATCH_MP h2) THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP h3) THEN
      ASM_SIMP_TAC [DIAMETER_EQ_0, BOUNDED_PATH_IMAGE] THEN
      DISCH_THEN (REPEAT_TCL STRIP_THM_THEN (MP_TAC o HolLight.AP_TERM ([[INFINITE:(real^2->bool)->bool]]))) THEN
      ASM_SIMP_TAC [INFINITE_SIMPLE_PATH_IMAGE] THEN
      REWRITE_TAC [INFINITE, FINITE_EMPTY, FINITE_SING],
      REPEAT DISCH_TAC] THEN
    MP_TAC (← HolLight.ASSUME ([[(a:real^2) IN path_image g0]])) THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV) [path_image] THEN
    REWRITE_TAC [IN_IMAGE, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC ([[t:real^1]]) THEN DISCH_THEN (STRIP_ASSUME_TAC o HolLight.GSYM) THEN
    ABBREV_TAC ([[g1:real^1->real^2 = shiftpath t g0]]) THEN
    SUBGOAL_THEN ([[path_image g0 = path_image g1 /\
    rectifiable_path g1 /\
    simple_path g1 /\
    pathstart g1 = a /\
    pathfinish g1 :real^2 = a /\
    convex(inside(path_image g1)) /\
    path_length g1 = L]]) MP_TAC THENL
     [FIRST_X_ASSUM (SUBST1_TAC o HolLight.SYM) THEN
      ASM_SIMP_TAC [RECTIFIABLE_PATH_SHIFTPATH, SIMPLE_PATH_SHIFTPATH,
                   CLOSED_SHIFTPATH, PATH_IMAGE_SHIFTPATH,
                   PATH_LENGTH_SHIFTPATH] THEN
      EXPAND_TAC "a" THEN MATCH_MP_TAC PATHSTART_SHIFTPATH THEN
      ASM_MESON_TAC [IN_INTERVAL_1, DROP_VEC],
      DISCH_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC) THEN
      REPEAT (FIRST_X_ASSUM (fun (th : thm) => HolLight.tactic_of do
        let q ← ExceptT.mk [[g0:real^1->real^2]]
        pure (if HolCore.Basics.free_in q (concl th) then ALL_TAC else FAIL_TAC "check"))) THEN
      UNDISCH_THEN ([[(t:real^1) IN interval[vec 0,vec 1] ]]) ((fun _ => ALL_TAC)) THEN
      FIRST_ASSUM (ASSUME_TAC o HolLight.MATCH_MP SIMPLE_PATH_IMP_PATH)] THEN
    MP_TAC (← HolLight.ISPEC ([[g1:real^1->real^2]]) ARC_LENGTH_REPARAMETRIZATION) THEN
    ANTS_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC, ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[g2:real^1->real^2]]) MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REPLICATE_TAC 3 (DISCH_THEN (CONJUNCTS_THEN2 (SUBST_ALL_TAC o HolLight.SYM) MP_TAC)) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    REPEAT (FIRST_X_ASSUM (fun (th : thm) => HolLight.tactic_of do
        let q ← ExceptT.mk [[g1:real^1->real^2]]
        pure (if HolCore.Basics.free_in q (concl th) then ALL_TAC else FAIL_TAC "check"))) THEN
    SUBGOAL_THEN ([[(\t. lift((g2:real^1->real^2)(t)$2)) integrable_on interval[vec 0,vec 1] ]]) MP_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
      MATCH_MP_TAC LIPSCHITZ_IMP_CONTINUOUS_ON THEN
      EXISTS_TAC ([[L:real]]) THEN ASM_REWRITE_TAC [(← HolLight.GSYM SessionMultiLib.Vectors.dist)],
      REWRITE_TAC [integrable_on, LEFT_IMP_EXISTS_THM]] THEN
    REWRITE_TAC [FORALL_LIFT] THEN X_GEN_TAC ([[av:real]]) THEN DISCH_TAC THEN
    ABBREV_TAC ([[origin:real^2 = vector[(a:real^2)$1;av] ]]) THEN
    SUBGOAL_THEN ([[(origin:real^2)$1 = (a:real^2)$1 /\
                (origin:real^2)$2 = av]]) MP_TAC THENL
     [EXPAND_TAC "origin" THEN REWRITE_TAC [VECTOR_2],
      POP_ASSUM ((fun _ => ALL_TAC))] THEN
    POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist HolLight.CONJ o HolLight.rev) THEN
    GEOM_ORIGIN_TAC ([[origin:real^2]]) THEN
    REWRITE_TAC [VECTOR_ADD_COMPONENT, VEC_COMPONENT, REAL_EQ_ADD_LCANCEL] THEN
    REWRITE_TAC [REAL_LE_LADD, REAL_ADD_RID] THEN
    MAP_EVERY X_GEN_TAC [([[origin:real^2]]), ([[b:real^2]]), ([[baseline:real]]), ([[a:real^2]]),
      ([[av:real]]), ([[L:real]]), ([[g:real^1->real^2]])] THEN
    STRIP_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 (MP_TAC o HolLight.SYM) SUBST_ALL_TAC) THEN
    DISCH_THEN (fun th => POP_ASSUM MP_TAC THEN
      SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
    MP_TAC (← HolLight.ISPECL [([[vec 0:real^1]]), ([[vec 1:real^1]]), ([[--lift av]])] HAS_INTEGRAL_CONST) THEN
    REWRITE_TAC [CONTENT_UNIT_1, IMP_IMP] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP HAS_INTEGRAL_ADD) THEN
    REWRITE_TAC [VECTOR_ADD_ASSOC, LIFT_ADD, VECTOR_ADD_LINV,
                VECTOR_ADD_LID, VECTOR_MUL_LID] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN ([[(g:real^1->real^2) absolutely_continuous_on interval[vec 0,vec 1] ]]) ASSUME_TAC THENL
     [MATCH_MP_TAC LIPSCHITZ_IMP_ABSOLUTELY_CONTINUOUS THEN
      REWRITE_TAC [BOUNDED_INTERVAL, (← HolLight.GSYM SessionMultiLib.Vectors.dist)] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] ABSOLUTELY_CONTINUOUS_ON_IMP_HAS_BOUNDED_VARIATION_ON)) THEN
    REWRITE_TAC [BOUNDED_INTERVAL] THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP LEBESGUE_DIFFERENTIATION_THEOREM_COMPACT) THEN
    ABBREV_TAC ([[s = {x | x IN interval[vec 0,vec 1] /\
              ~((g:real^1->real^2) differentiable at x)}]]) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN ([[?g':real^1->real^2.
        !x. x IN interval[vec 0,vec 1] /\ ~(x IN s)
            ==> (g has_vector_derivative g' x) (at x)]]) STRIP_ASSUME_TAC THENL
     [EXISTS_TAC ([[\x. vector_derivative (g:real^1->real^2) (at x)]]) THEN
      ASM_REWRITE_TAC [(← HolLight.GSYM VECTOR_DERIVATIVE_WORKS)] THEN
      EXPAND_TAC "s" THEN SIMP_TAC [IN_ELIM_THM, IMP_CONJ],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!t. t IN interval[vec 0,vec 1]
        ==> (g':real^1->real^2) absolutely_integrable_on interval[vec 0,t] /\
            integral (interval[vec 0,t]) g' = g t - a]]) ASSUME_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN
      MP_TAC (← HolLight.ISPECL [([[g:real^1->real^2]]), ([[g':real^1->real^2]]), ([[vec 0:real^1]]), ([[vec 1:real^1]])] ABSOLUTE_INTEGRAL_ABSOLUTELY_CONTINUOUS_DERIVATIVE_EQ) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (Prod.snd : thm × thm → thm) o HolLight.EQ_IMP_RULE) THEN
      ANTS_TAC THENL
       [ASM_MESON_TAC [IN_DIFF, HAS_VECTOR_DERIVATIVE_AT_WITHIN],
        REWRITE_TAC [HAS_INTEGRAL_INTEGRABLE_INTEGRAL]] THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [pathstart]) THEN
      ASM_SIMP_TAC [] THEN DISCH_THEN (MP_TAC o HolLight.CONJUNCT1) THEN
      MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_CONJ_ALT] ABSOLUTELY_INTEGRABLE_ON_SUBINTERVAL) THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [IN_INTERVAL_1]) THEN
      REWRITE_TAC [SUBSET_INTERVAL_1, DROP_VEC, LIFT_DROP] THEN REAL_ARITH_TAC2,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!x. x IN interval[vec 0,vec 1]
        ==> (\x. lift(norm((g':real^1->real^2) x))) absolutely_integrable_on
            interval[vec 0,x] /\
            integral (interval[vec 0,x]) (\x. lift(norm(g' x))) =
            L % x]]) ASSUME_TAC THENL
     [X_GEN_TAC ([[x:real^1]]) THEN DISCH_TAC THEN
      FIRST_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [IN_INTERVAL_1]) THEN
      REWRITE_TAC [DROP_VEC] THEN STRIP_TAC THEN
      MP_TAC (← HolLight.ISPECL [([[g:real^1->real^2]]), ([[vec 0:real^1]]), ([[x:real^1]])] PATH_LENGTH_SUBPATH) THEN
      ASM_SIMP_TAC [SEGMENT_1, DROP_VEC] THEN
      REWRITE_TAC [(← HolLight.GSYM LIFT_EQ), LIFT_CMUL, LIFT_DROP] THEN
      DISCH_THEN SUBST1_TAC THEN
      MP_TAC (← HolLight.ISPECL [([[g:real^1->real^2]]), ([[g':real^1->real^2]]),
                     ([[vec 0:real^1]]), ([[x:real^1]]), ([[s:real^1->bool]])] VECTOR_VARIATION_INTEGRAL_NORM_DERIVATIVE_GEN) THEN
      ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] ABSOLUTELY_CONTINUOUS_ON_SUBSET)) THEN
          FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [IN_INTERVAL_1]) THEN
          REWRITE_TAC [SUBSET_INTERVAL_1, DROP_VEC, LIFT_DROP] THEN
          REAL_ARITH_TAC2,
          REWRITE_TAC [IN_INTERVAL_1, LIFT_DROP, DROP_VEC, IN_DIFF] THEN
          REPEAT STRIP_TAC THEN
          MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_REWRITE_TAC [IN_INTERVAL_1, LIFT_DROP, DROP_VEC, IN_DIFF] THEN
          ASM_REAL_ARITH_TAC],
        SIMP_TAC [ABSOLUTELY_INTEGRABLE_NORM, LIFT_DROP]],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!x. x IN interval[vec 0,vec 1] /\ ~(x IN s)
        ==> norm((g':real^1->real^2) x) <= L]]) ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN ([[L = norm(lift L)]]) SUBST1_TAC THENL
       [ASM_SIMP_TAC [NORM_LIFT, h4],
        MATCH_MP_TAC NORM_VECTOR_DERIVATIVES_LE_WITHIN] THEN
      MAP_EVERY EXISTS_TAC [([[g:real^1->real^2]]), ([[\x:real^1. L % x]]),
        ([[x:real^1]]), ([[interval[vec 0:real^1,vec 1] ]])] THEN
      ASM_SIMP_TAC [HAS_VECTOR_DERIVATIVE_AT_WITHIN] THEN
      REWRITE_TAC [LIFT_EQ_CMUL] THEN
      SIMP_TAC [HAS_VECTOR_DERIVATIVE_ID, HAS_VECTOR_DERIVATIVE_CMUL] THEN
      CONJ_TAC THENL
       [HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
            let x1 ← ExceptT.mk (HolLight.PART_MATCH (HolCore.Equal.lhand o HolCore.Kernel.rand) LIMPT_OF_CONVEX w)
            pure (MP_TAC x1)) THEN
        ASM_REWRITE_TAC [CONVEX_INTERVAL, (← HolLight.GSYM INTERVAL_SING)] THEN
        DISCH_THEN SUBST1_TAC THEN
        DISCH_THEN (MP_TAC o HolLight.AP_TERM ([[interior:(real^1->bool)->real^1->bool]])) THEN
        REWRITE_TAC [INTERVAL_SING, INTERIOR_INTERVAL] THEN
        REWRITE_TAC [INTERVAL_NE_EMPTY_1, DROP_VEC, REAL_LT_01],
        REWRITE_TAC [EVENTUALLY_WITHIN] THEN
        REWRITE_TAC [(← HolLight.GSYM VECTOR_SUB_LDISTRIB), NORM_MUL] THEN
        ASM_SIMP_TAC [(← HolLight.GSYM SessionMultiLib.Vectors.dist), h5] THEN
        MESON_TAC [REAL_LT_01]],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[(\x. lift(norm((g':real^1->real^2) x) pow 2))
    absolutely_integrable_on interval[vec 0,vec 1] ]]) ASSUME_TAC THENL
     [MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE_AE THEN
      EXISTS_TAC ([[\x:real^1. lift(L pow 2)]]) THEN
      EXISTS_TAC ([[s:real^1->bool]]) THEN
      REWRITE_TAC [INTEGRABLE_CONST, NORM_LIFT, REAL_ABS_NORM, LIFT_DROP,
                  REAL_ABS_POW, IN_DIFF, (← HolLight.GSYM REAL_LE_SQUARE_ABS)] THEN
      ASM_SIMP_TAC [h6] THEN
      MATCH_MP_TAC MEASURABLE_ON_LIFT_POW THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      MATCH_MP_TAC MEASURABLE_ON_NORM THEN
      ASM_MESON_TAC [ENDS_IN_UNIT_INTERVAL, ABSOLUTELY_INTEGRABLE_MEASURABLE],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[integral (interval[vec 0,vec 1])
             (\x. lift(norm((g':real^1->real^2) x) pow 2)) =
    lift(L pow 2)]]) ASSUME_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC ([[integral (interval[vec 0,vec 1]) (\x:real^1. lift(L pow 2))]]) THEN
       CONJ_TAC THENL
        [GEN_REWRITE_TAC HolCore.Lib.I [(← HolLight.GSYM DROP_EQ)],
         REWRITE_TAC [INTEGRAL_CONST, CONTENT_UNIT_1, (← HolLight.GSYM LIFT_CMUL)] THEN
         REWRITE_TAC [REAL_MUL_LID]] THEN
       REWRITE_TAC [(← HolLight.GSYM REAL_LE_ANTISYM)] THEN CONJ_TAC THEN
       MATCH_MP_TAC INTEGRAL_DROP_LE_AE THEN
       ASM_SIMP_TAC [INTEGRABLE_CONST, ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
       REWRITE_TAC [LIFT_DROP, (← HolLight.GSYM REAL_LE_SQUARE_ABS), REAL_ABS_NORM] THEN
       ASM_SIMP_TAC [IN_DIFF, h7] THENL
        [ASM_MESON_TAC [], ALL_TAC] THEN
       SUBGOAL_THEN ([[((\x. lift(L - norm((g':real^1->real^2) x))) has_integral (vec 0))
       (interval[vec 0,vec 1] DIFF s)]]) MP_TAC THENL
        [MATCH_MP_TAC HAS_INTEGRAL_SPIKE_SET THEN
         EXISTS_TAC ([[interval[vec 0:real^1,vec 1] ]]) THEN CONJ_TAC THENL
          [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC ([[s:real^1->bool]]) THEN
           ASM_REWRITE_TAC [] THEN SET_TAC [],
           REWRITE_TAC [LIFT_SUB]] THEN
         SUBGOAL_THEN ([[vec 0 = content(interval[vec 0:real^1,vec 1]) % lift L - lift L]]) MP_TAC THENL
          [REWRITE_TAC [CONTENT_UNIT_1, LIFT_CMUL] THEN
           CONV_TAC va,
           DISCH_THEN (fun th => GEN_REWRITE_TAC HolLight.LAND_CONV [th])] THEN
         MATCH_MP_TAC HAS_INTEGRAL_SUB THEN REWRITE_TAC [HAS_INTEGRAL_CONST] THEN
         ASM_SIMP_TAC [HAS_INTEGRAL_INTEGRABLE_INTEGRAL, ENDS_IN_UNIT_INTERVAL,
                      ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
         REWRITE_TAC [(← HolLight.GSYM LIFT_EQ_CMUL)],
         ALL_TAC] THEN
      HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
          let x1 ← ec (HolCore.Equal.lhand w)
          let x2 ← ExceptT.mk (HolLight.PART_MATCH (HolCore.Equal.lhand o HolCore.Kernel.rand) HAS_INTEGRAL_NEGLIGIBLE_EQ x1)
          pure (MP_TAC x2)) THEN
      REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC [IMP_IMP, FORALL_1, DIMINDEX_1] THEN
      REWRITE_TAC [LIFT_DROP, (← HolLight.GSYM drop), IN_DIFF] THEN
      ASM_SIMP_TAC [REAL_SUB_LE] THEN
      GEN_REWRITE_TAC HolCore.Lib.I [IMP_CONJ] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [(← HolLight.GSYM LIFT_NUM), LIFT_EQ] THEN
      REWRITE_TAC [h8] THEN
      REWRITE_TAC [LIFT_NUM] THEN STRIP_TAC THEN
      EXISTS_TAC ([[s UNION {x | (x IN interval[vec 0,vec 1] /\ ~(x IN s)) /\
                    ~(norm ((g':real^1->real^2) x) = L)}]]) THEN
      ASM_REWRITE_TAC [NEGLIGIBLE_UNION_EQ] THEN
      REWRITE_TAC [IN_UNION, IN_ELIM_THM] THEN MESON_TAC [REAL_LE_REFL],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[(\t. lift(g'(t)$1 * (g:real^1->real^2)(t)$2)) integrable_on
    interval[vec 0,vec 1] /\
    norm(integral (interval[vec 0,vec 1])
                  (\t. lift((g':real^1->real^2)(t)$1 * g(t)$2))) =
    measure(inside(path_image g))]]) STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC GREEN_AREA_THEOREM THEN
      MAP_EVERY EXISTS_TAC [([[s:real^1->bool]]), ([[a:real^2]])] THEN
      ASM_SIMP_TAC [IN_DIFF, SessionMultiLib.Vectors.dist] THEN FIRST_X_ASSUM (SUBST1_TAC o HolLight.MATCH_MP h9) THEN
      ASM_REWRITE_TAC [VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT] THEN
      SIMP_TAC [BASIS_COMPONENT, DIMINDEX_2, ARITH] THEN ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[?sgn. sgn pow 2 = &1 /\
          ((\x. lift((g':real^1->real^2)(x)$1 * g(x)$2)) has_integral
           sgn % lift(measure(inside(path_image(g:real^1->real^2)))))
          (interval[vec 0,vec 1])]]) STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC [HAS_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolLight.LAND_CONV [NORM_1]) THEN
      REWRITE_TAC [real_abs] THEN COND_CASES_TAC THEN
      DISCH_THEN (SUBST1_TAC o HolLight.SYM) THENL
       [EXISTS_TAC ([[&1:real]]), EXISTS_TAC ([[--(&1):real]])] THEN
      ASM_REWRITE_TAC [LIFT_DROP, LIFT_NEG] THEN
      REWRITE_TAC [VECTOR_MUL_LNEG, VECTOR_MUL_RNEG, VECTOR_NEG_NEG] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [VECTOR_MUL_LID],
      ALL_TAC] THEN
    SIMP_TAC [PI_POS, h10, REAL_LE_RDIV_EQ,
      h11] THEN
    ONCE_REWRITE_TAC [(← HolLight.GSYM REAL_SUB_LE)] THEN
    SUBGOAL_THEN ([[((\x. lift(((g':real^1->real^2) x$1 -
                &2 * pi * sgn * (g:real^1->real^2)(x)$2) pow 2 +
               (g'(x)$2 pow 2 - (&2 * pi * g(x)$2) pow 2)))
     has_integral lift(L pow 2 - measure (inside (path_image g)) * &4 * pi))
    (interval[vec 0,vec 1])]]) ASSUME_TAC THENL
     [ASM_SIMP_TAC [h12] THEN
      REWRITE_TAC [LIFT_SUB] THEN MATCH_MP_TAC HAS_INTEGRAL_SUB THEN
      CONJ_TAC THENL
       [REWRITE_TAC [(← HolLight.GSYM DOT_2), REAL_POW_2] THEN
        REWRITE_TAC [(← HolLight.GSYM REAL_POW_2), (← HolLight.GSYM NORM_POW_2)] THEN
        ASM_SIMP_TAC [HAS_INTEGRAL_INTEGRABLE_INTEGRAL,
                     ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE],
        FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (REWRITE_TAC [(← HolLight.MATCH_MP (← rg (← ExceptT.mk [[s pow 2 = &1 ==> x * &4 * pi = &4 * pi * s * s * x]])) th)])) THEN
        REWRITE_TAC [h13] THEN
        REWRITE_TAC [LIFT_CMUL] THEN
        REPLICATE_TAC 3 (MATCH_MP_TAC HAS_INTEGRAL_CMUL) THEN
        RULE_ASSUM_TAC (HolLight.REWRITE_RULE [LIFT_CMUL]) THEN ASM_REWRITE_TAC []],
      ALL_TAC] THEN
    ASM_CASES_TAC ([[inside(path_image g):real^2->bool = {}]]) THENL
     [ASM_REWRITE_TAC [MEASURE_EMPTY, REAL_MUL_LZERO, REAL_SUB_RZERO] THEN
      ASM_SIMP_TAC [REAL_LE_POW_2, REAL_POW_EQ_0, ARITH_EQ, REAL_LT_IMP_NZ],
      ALL_TAC] THEN
    MP_TAC (← HolLight.SPECL [([[\x. (g:real^1->real^2)(lift x)$2]]), ([[\x. (g':real^1->real^2)(lift x)$2]])] SCALED_WIRTINGER_INEQUALITY) THEN
    ASM_REWRITE_TAC [LIFT_NUM] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [h14] THEN
    SIMP_TAC [SessionMultiLib.RealAnalysis.REAL_INTEGRAL, REAL_POW_MUL, REAL_INTEGRAL_LMUL,
             REAL_INTEGRABLE_LMUL] THEN
    REWRITE_TAC [IMAGE_LIFT_REAL_INTERVAL, LIFT_NUM] THEN
    REWRITE_TAC [has_real_integral, REAL_INTEGRABLE_ON, o_DEF, LIFT_DROP,
                IMAGE_LIFT_REAL_INTERVAL, LIFT_NUM] THEN
    REWRITE_TAC [h15] THEN
    REWRITE_TAC [h16] THEN
    SIMP_TAC [(← HolLight.GSYM DROP_SUB), (← HolLight.GSYM INTEGRAL_SUB), LIFT_CMUL, INTEGRABLE_CMUL] THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_POW_MUL), (← HolLight.GSYM LIFT_CMUL), (← HolLight.GSYM LIFT_SUB)] THEN
    SUBST1_TAC (← HolLight.SYM (← HolLight.ISPEC ([[g:real^1->real^2]]) pathstart)) THEN
    SUBST1_TAC (← HolLight.SYM (← HolLight.ISPEC ([[g:real^1->real^2]]) pathfinish)) THEN
    ASM_REWRITE_TAC [] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [IMP_CONJ] THEN ANTS_TAC THENL
     [REWRITE_TAC [FORALL_DROP, IN_REAL_INTERVAL, LIFT_DROP] THEN
      X_GEN_TAC ([[x:real^1]]) THEN STRIP_TAC THEN
      MP_TAC (← HolLight.ISPECL [([[\x. lift((g:real^1->real^2) x$2)]]),
        ([[\x. lift((g':real^1->real^2) x$2)]]),
        ([[s:real^1->bool]]), ([[vec 0:real^1]]), ([[x:real^1]])] FUNDAMENTAL_THEOREM_OF_CALCULUS_ABSOLUTELY_CONTINUOUS) THEN
      ASM_REWRITE_TAC [DROP_VEC] THEN
      SUBST1_TAC (← HolLight.SYM (← HolLight.ISPEC ([[g:real^1->real^2]]) pathstart)) THEN
      ASM_REWRITE_TAC [LIFT_SUB] THEN DISCH_THEN MATCH_MP_TAC THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[2]]) o
          HolLight.GEN_REWRITE_RULE HolCore.Lib.I [ABSOLUTELY_CONTINUOUS_ON_COMPONENTWISE]) THEN
        REWRITE_TAC [DIMINDEX_2, ARITH] THEN
        MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_CONJ_ALT] ABSOLUTELY_CONTINUOUS_ON_SUBSET) THEN
        ASM_REWRITE_TAC [SUBSET_INTERVAL_1, DROP_VEC, REAL_LE_REFL],
        X_GEN_TAC ([[y:real^1]]) THEN
        REWRITE_TAC [IN_INTERVAL_1, DROP_VEC, IN_DIFF] THEN
        STRIP_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
        MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_LIFT_COMPONENT_AT THEN
        REWRITE_TAC [DIMINDEX_2, ARITH] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC [IN_INTERVAL_1, DROP_VEC] THEN ASM_REAL_ARITH_TAC],
      ALL_TAC] THEN
    MATCH_MP_TAC h17 THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
      EXISTS_TAC ([[\x. lift(norm((g':real^1->real^2) x) pow 2)]]) THEN
      ASM_SIMP_TAC [ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
      REWRITE_TAC [NORM_1, LIFT_DROP, REAL_ABS_POW, (← HolLight.GSYM REAL_LE_SQUARE_ABS)] THEN
      REWRITE_TAC [REAL_ABS_ABS, REAL_ABS_NORM, COMPONENT_LE_NORM] THEN
      MATCH_MP_TAC MEASURABLE_ON_LIFT_POW THEN REWRITE_TAC [ARITH_EQ] THEN
      SUBGOAL_THEN ([[(g':real^1->real^2) absolutely_integrable_on interval[vec 0,vec 1] ]]) MP_TAC THENL [ASM_MESON_TAC [ENDS_IN_UNIT_INTERVAL], ALL_TAC] THEN
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE) THEN
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP INTEGRABLE_IMP_MEASURABLE) THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [MEASURABLE_ON_COMPONENTWISE] THEN
      DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC [DIMINDEX_2, ARITH],
      STRIP_TAC] THEN
    SUBGOAL_THEN ([[(\x. lift((g':real^1->real^2)x$2 pow 2 -
              (&2 * pi * (g:real^1->real^2)x$2) pow 2))
     integrable_on interval[vec 0,vec 1] ]]) MP_TAC THENL
     [REWRITE_TAC [REAL_MUL_ASSOC, LIFT_SUB] THEN
      ONCE_REWRITE_TAC [REAL_POW_MUL] THEN REWRITE_TAC [LIFT_CMUL] THEN
      ASM_SIMP_TAC [INTEGRABLE_SUB, INTEGRABLE_CMUL],
      GEN_REWRITE_TAC HolLight.LAND_CONV [integrable_on]] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[w:real^1]]) MP_TAC) THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
        pure (SUBST1_TAC (← HolLight.MATCH_MP INTEGRAL_UNIQUE th) THEN MP_TAC th)) THEN
    FIRST_X_ASSUM (fun (th : thm) => HolLight.tactic_of do
        let q ← ExceptT.mk [[(f has_integral y) s]]
        let ok ← ExceptT.lift (show IO Bool from do
          let r ← HolCore.Drule.term_match [] q (concl th)
          pure (r matches .ok _))
        pure (if ok then MP_TAC th else FAIL_TAC "check")) THEN
    GEN_REWRITE_TAC HolCore.Lib.I [IMP_IMP] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP HAS_INTEGRAL_SUB) THEN
    REWRITE_TAC [LIFT_ADD, h18] THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
        pure (ASSUME_TAC th THEN
      MP_TAC (← HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] HAS_INTEGRAL_DROP_POS) th))) THEN
    REWRITE_TAC [LIFT_DROP, REAL_LE_POW_2, DROP_SUB] THEN
    ABBREV_TAC ([[d = L pow 2 -
        measure(inside(path_image g:real^2->bool)) * &4 * pi - drop w]]) THEN
    SUBGOAL_THEN ([[L pow 2 - measure(inside(path_image g:real^2->bool)) * &4 * pi =
    d + drop w]]) SUBST_ALL_TAC THENL [EXPAND_TAC "d" THEN REAL_ARITH_TAC2, ALL_TAC] THEN
    DISCH_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_SIMP_TAC [REAL_LE_ADD, h19] THEN
    ASM_CASES_TAC ([[d:real = &0]]) THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC ([[drop w = &0]]) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    FIRST_X_ASSUM (fun (th : thm) => HolLight.tactic_of do
        let q ← ExceptT.mk [[(f has_integral y) s]]
        let ok ← ExceptT.lift (show IO Bool from do
          let r ← HolCore.Drule.term_match [] q (concl th)
          pure (r matches .ok _))
        pure (if ok then MP_TAC th else FAIL_TAC "check")) THEN
    ASM_REWRITE_TAC [REAL_ADD_RID] THEN
    MP_TAC (← HolLight.ASSUME ([[drop w = &0]])) THEN REWRITE_TAC [(← HolLight.GSYM LIFT_EQ), LIFT_DROP] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [VECTOR_SUB_REFL] THEN
    HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
        let x1 ← ec (HolCore.Equal.lhand w)
        let x2 ← ExceptT.mk (HolLight.PART_MATCH (HolCore.Equal.lhand o HolCore.Kernel.rand) HAS_INTEGRAL_NEGLIGIBLE_EQ x1)
        pure (MP_TAC x2)) THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC [IMP_IMP, DIMINDEX_1, FORALL_1] THEN
    REWRITE_TAC [(← HolLight.GSYM drop), LIFT_DROP, REAL_LE_POW_2] THEN
    GEN_REWRITE_TAC HolCore.Lib.I [IMP_CONJ] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [(← HolLight.GSYM DROP_EQ), DROP_VEC, LIFT_DROP, REAL_POW_EQ_0] THEN
    REWRITE_TAC [ARITH_EQ] THEN REWRITE_TAC [h20] THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN ([[C:real]]) (X_CHOOSE_THEN ([[A:real]]) MP_TAC)) THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [FORALL_DROP] THEN
    SIMP_TAC [IN_INTERVAL_1, IN_REAL_INTERVAL, LIFT_DROP, DROP_VEC] THEN
    REWRITE_TAC [(← HolLight.GSYM DROP_VEC), (← HolLight.GSYM IN_INTERVAL_1)] THEN
    REWRITE_TAC [DROP_VEC, NOT_IMP] THEN DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[!x. x IN interval[vec 0,vec 1]
        ==> (g:real^1->real^2)x$1 =
            --sgn * C * (cos(&2 * pi * drop x - A) - cos A)]]) ASSUME_TAC THENL
     [X_GEN_TAC ([[x:real^1]]) THEN
      REWRITE_TAC [IN_INTERVAL_1, DROP_VEC] THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC [(← HolLight.GSYM REAL_SUB_0)] THEN CONV_TAC HolLight.SYM_CONV THEN
      REWRITE_TAC [(← HolLight.GSYM LIFT_EQ), LIFT_NUM] THEN
      MP_TAC (← HolLight.ISPECL [([[\x. lift((g':real^1->real^2) x$1 -
               &2 * pi * sgn * C * sin(&2 * pi * drop x - A))]]),
        ([[interval[vec 0:real^1,x] ]])] HAS_INTEGRAL_UNIQUE) THEN
      REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_INTEGRAL_NEGLIGIBLE THEN FIRST_X_ASSUM (MATCH_MP_TAC o
          HolLight.MATCH_MP h21) THEN
        REWRITE_TAC [IN_DIFF, IN_ELIM_THM, IN_INTERVAL_1, DROP_VEC] THEN
        X_GEN_TAC ([[y:real^1]]) THEN
        DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
        GEN_REWRITE_TAC HolCore.Lib.I [(← HolLight.GSYM CONTRAPOS_THM)] THEN
        SIMP_TAC [(← HolLight.GSYM DROP_EQ), DROP_VEC, LIFT_DROP] THEN ASM_REAL_ARITH_TAC,
        ALL_TAC] THEN
      REWRITE_TAC [LIFT_SUB] THEN MATCH_MP_TAC HAS_INTEGRAL_SUB THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN ([[(g':real^1->real^2) absolutely_integrable_on interval[vec 0,x] /\
        integral (interval [vec 0,x]) g' = g x - a]]) MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN
          REWRITE_TAC [IN_INTERVAL_1, DROP_VEC] THEN
          ASM_REAL_ARITH_TAC,
          ALL_TAC] THEN
        DISCH_THEN (CONJUNCTS_THEN2 (MP_TAC o HolLight.MATCH_MP ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE) MP_TAC) THEN
        REWRITE_TAC [(← HolLight.GSYM HAS_INTEGRAL_INTEGRABLE_INTEGRAL),
                    (← HolLight.GSYM IMP_CONJ_ALT)] THEN
        GEN_REWRITE_TAC HolLight.LAND_CONV [HAS_INTEGRAL_COMPONENTWISE] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[1]])) THEN
        ASM_REWRITE_TAC [DIMINDEX_2, ARITH, VECTOR_SUB_COMPONENT] THEN
        REWRITE_TAC [REAL_SUB_RZERO],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[((\x. &2 * pi * sgn * C * sin (&2 * pi * x - A))
       has_real_integral
       (--sgn * C * cos (&2 * pi * drop x - A) -
        --sgn * C * cos (&2 * pi * &0 - A))) (real_interval[&0,drop x])]]) MP_TAC THENL
       [MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS THEN
        ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
        REAL_DIFF_TAC THEN REAL_ARITH_TAC2,
        REWRITE_TAC [has_real_integral, o_DEF, IMAGE_LIFT_REAL_INTERVAL] THEN
        REWRITE_TAC [REAL_MUL_RZERO, REAL_SUB_LZERO, COS_NEG]] THEN
      REWRITE_TAC [LIFT_NUM, LIFT_DROP] THEN MATCH_MP_TAC EQ_IMP THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC2,
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [([[vector[sgn * C * cos A; &0]:real^2]]), ([[abs C:real]])] THEN
    MATCH_MP_TAC h22 THEN
    CONJ_TAC THENL
     [REWRITE_TAC [path_image, SUBSET, FORALL_IN_IMAGE, IN_SPHERE] THEN
      REWRITE_TAC [SessionMultiLib.Vectors.dist, NORM_EQ_SQUARE, REAL_ABS_POS, REAL_POW2_ABS] THEN
      X_GEN_TAC ([[x:real^1]]) THEN DISCH_TAC THEN
      REWRITE_TAC [DOT_2, VECTOR_SUB_COMPONENT, VECTOR_2] THEN
      ASM_SIMP_TAC [] THEN
      MP_TAC (← HolLight.SPEC ([[&2 * pi * drop x - A]]) SIN_CIRCLE) THEN
      UNDISCH_TAC ([[(sgn:real) pow 2 = &1]]) THEN
      CONV_TAC rg,
      ALL_TAC] THEN
    ABBREV_TAC ([[z:real^2 = vector[sgn * C * cos A; &0] ]]) THEN DISCH_TAC THEN
    UNDISCH_TAC ([[~(inside(path_image g):real^2->bool = {})]]) THEN
    REWRITE_TAC [] THEN
    MATCH_MP_TAC INSIDE_BOUNDED_COMPLEMENT_CONNECTED_EMPTY THEN
    ASM_SIMP_TAC [BOUNDED_PATH_IMAGE, SIMPLE_PATH_IMP_PATH] THEN
    MATCH_MP_TAC JORDAN_BROUWER_NONSEPARATION THEN
    MAP_EVERY EXISTS_TAC [([[sphere(z:real^2,abs C)]]), ([[z:real^2]]), ([[abs C:real]])] THEN
    ASM_REWRITE_TAC [DIMINDEX_2, ARITH, HOMEOMORPHIC_REFL])
  : ExceptT String IO thm).run
#eval ISOPERIMETRIC_THEOREM_CONVEX

/- ------------------------------------------------------------------------- -/
/- Part 4: Convexification of an arbitrary rectifiable simple curve.         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 12
def STEP_LEMMA : thm := keep "STEP_LEMMA" fun _ => (do
  let h68 ← sr (← ExceptT.mk [[IMAGE g i SUBSET j ==> c IN i ==> g c IN j]])
  let h67 ← sr (← ExceptT.mk [[s SUBSET t ==> ~(x IN t) ==> ~(x IN s)]])
  let h66 ← na (← ExceptT.mk [[!c:real^N. (norm(c - a) <= v /\ norm(b - c) <= w) /\
                 ~(dist(a,b) = dist(a,c) + dist(c,b))
                 ==> ~(norm(b - a) = v + w)]])
  let h65 ← rf (← ExceptT.mk [[a < b ==> inv(b - a) * (b - a) = &1]])
  let h64 ← rr (← ExceptT.mk [[a < b ==> ~(b < a)]])
  let h63 ← va (← ExceptT.mk [[c % (x - a):real^N = --(c % a) + c % x]])
  let h62 ← rf (← ExceptT.mk [[a < b ==> (b - a) / (b - a) = &1]])
  let h61 ← rr (← ExceptT.mk [[(a - a) / b = &0]])
  let h60 ← rr (← ExceptT.mk [[a:real = b /\ c < d ==> c + a < d + b]])
  let h59 ← rr (← ExceptT.mk [[a:real = b /\ c < d ==> a + c < b + d]])
  let h58 ← rr (← ExceptT.mk [[(a * b) * c:real = b * a * c]])
  let h57 ← rr (← ExceptT.mk [[a / b * c:real = (a * c) / b]])
  let h56 ← rf (← ExceptT.mk [[a < b
      ==> (x - a) / (b - a) - (y - a) / (b - a) = (x - y) / (b - a)]])
  let h55 ← va (← ExceptT.mk [[(a + x % c) - (a + y % c):real^N = (x - y) % c]])
  let h54 ← rf (← ExceptT.mk [[a < b ==> (b - a) / (b - a) = &1]])
  let h53 ← rr (← ExceptT.mk [[(a - a) / b = &0]])
  let h52 ← tt (← ExceptT.mk [[p /\ (p ==> q) ==> p /\ q]])
  let h51 ← sr (← ExceptT.mk [[~(~(x IN {b,a}) /\ x IN t UNION {a,b})
        ==> ~(a IN t) /\ ~(b IN t) ==> ~(x IN t)]])
  let h50 ← sr (← ExceptT.mk [[IMAGE f s = t ==> !x. x IN s ==> f x IN t]])
  let h49 ← rf (← ExceptT.mk [[a < b ==> ((x - a) / (b - a) = (y - a) / (b - a) <=> x = y)]])
  let h48 ← va (← ExceptT.mk [[a + x:real^N = a + y <=> x = y]])
  let h47 ← ms [] (← ExceptT.mk [[!Q. (!x y. P x y <=> P y x) /\
          (!x y. ~Q x /\ ~Q y ==> P x y) /\
          (!x y. Q x /\ Q y ==> P x y) /\
          (!x y. ~Q x /\ Q y ==> P x y)
      ==> !x y. P x y]])
  let h46 ← tt (← ExceptT.mk [[(r ==> p) /\ q /\ r /\ s ==> p /\ q /\ r /\ s]])
  let h45 ← va (← ExceptT.mk [[(&1 - a) % x + a % y:real^N = x + a % (y - x)]])
  let h44 ← sr (← ExceptT.mk [[(!x. f x = g x) ==> IMAGE f s = IMAGE g s]])
  let h43 ← sr (← ExceptT.mk [[(\x. if x IN s then f x else g x) = h
      ==> IMAGE f s = t
          ==> IMAGE h s = t]])
  let h42 ← sr (← ExceptT.mk [[s INTER h' = {} /\ h UNION h' = UNIV ==> ~(d SUBSET h)
          ==> ~(h' INTER (d DIFF s) = {})]])
  let h41 ← sr (← ExceptT.mk [[s SUBSET t ==> s DIFF f SUBSET t]])
  let h40 ← sr (← ExceptT.mk [[z IN s ==> s SUBSET t ==> z IN t]])
  let h39 ← sr (← ExceptT.mk [[z IN i ==> z IN c ==> ~(c SUBSET a DIFF i)]])
  let h38 ← rr (← ExceptT.mk [[&0 < x \/ x < &0 <=> ~(x = &0)]])
  let h37 ← sr (← ExceptT.mk [[(!x. x IN s ==> x IN t /\ ~P x) <=>
      s SUBSET t /\ (!x. x IN s ==> ~P x)]])
  let h36 ← sr (← ExceptT.mk [[d UNION d' = g ==> g INTER s SUBSET a ==> d INTER s SUBSET a]])
  let h35 ← sr (← ExceptT.mk [[s INTER t SUBSET a /\ s INTER u SUBSET a
          ==> (u UNION t) INTER s SUBSET a]])
  let h34 ← sr (← ExceptT.mk [[s INTER t SUBSET u ==> s INTER (t UNION u) SUBSET u]])
  let h33 ← sr (← ExceptT.mk [[s SUBSET c ==> s DIFF (s INTER (c DIFF i)) SUBSET i]])
  let h32 ← sr (← ExceptT.mk [[s = t ==> s SUBSET t]])
  let h31 ← sr (← ExceptT.mk [[(~(s INTER (t UNION u) = {}) ==> s INTER (v UNION w) = {})
      ==> s INTER t = {} \/ s INTER v = {}]])
  let h30 ← sr (← ExceptT.mk [[f UNION e = d ==> d INTER g SUBSET s ==> e INTER g SUBSET s]])
  let h29 ← sr (← ExceptT.mk [[e UNION f = d ==> d INTER g SUBSET s ==> e INTER g SUBSET s]])
  let h28 ← sr (← ExceptT.mk [[s SUBSET f ==> s SUBSET t UNION f]])
  let h27 ← sr (← ExceptT.mk [[p SUBSET c ==> c INTER i = {} ==> ~(z IN i INTER p)]])
  let h26 ← sr (← ExceptT.mk [[i INTER j = {}
        ==> ~(z IN s INTER t) /\ ~(z IN s INTER j) /\ ~(z IN t INTER i)
            ==> ~(z IN s UNION i /\ z IN t UNION j)]])
  let h25 ← sr (← ExceptT.mk [[(s INTER t) INTER (s INTER u) = {} <=>
        !x. x IN s ==> ~(x IN t INTER u)]])
  let h24 ← sr (← ExceptT.mk [[i UNION j UNION p = k
        ==> ~(z IN p) /\ z IN f UNION k
            ==> z IN f UNION i UNION j]])
  let h23 ← sr (← ExceptT.mk [[(s UNION t) UNION (u UNION v) = (s UNION u) UNION (t UNION v)]])
  let h22 ← sr (← ExceptT.mk [[s SUBSET t UNION u
        ==> s SUBSET (s INTER t) UNION (s INTER u)]])
  let h21 ← sr (← ExceptT.mk [[f UNION e = d
           ==> d INTER g SUBSET s ==> e INTER g SUBSET s]])
  let h20 ← sr (← ExceptT.mk [[e UNION f = d
           ==> d INTER g SUBSET s ==> e INTER g SUBSET s]])
  let h19 ← sr (← ExceptT.mk [[s SUBSET f ==> s SUBSET t UNION f]])
  let h18 ← sr (← ExceptT.mk [[p SUBSET c ==> c INTER i = {} ==> ~(z IN i INTER p)]])
  let h17 ← sr (← ExceptT.mk [[i INTER j = {}
          ==> ~(z IN s INTER t) /\ ~(z IN s INTER j) /\ ~(z IN t INTER i)
              ==> ~(z IN s UNION i /\ z IN t UNION j)]])
  let h16 ← sr (← ExceptT.mk [[i UNION j UNION p = k
          ==> ~(z IN p) /\ z IN f UNION k
              ==> z IN f UNION i UNION j]])
  let h15 ← sr (← ExceptT.mk [[z IN s UNION t \/ z IN u UNION v <=>
          z IN (s UNION u) UNION (t UNION v)]])
  let h14 ← tt (← ExceptT.mk [[(~p <=> q) <=> (p \/ q) /\ ~(p /\ q)]])
  let h13 ← tt (← ExceptT.mk [[(~p <=> q) <=> ~q <=> p]])
  let h12 ← sr (← ExceptT.mk [[(!x. x IN s ==> (~(x IN u) <=> x IN t))
        ==> s DIFF u = s INTER t]])
  let h11 ← sr (← ExceptT.mk [[g0 INTER g1 = {a,b}
        ==> (g1 DIFF {b,a}) DIFF (i UNION d1 UNION g0) =
            (g1 DIFF {b,a}) DIFF (d1 UNION i)]])
  let h10 ← sr (← ExceptT.mk [[f UNION e = d
           ==> d INTER g SUBSET s ==> e INTER g SUBSET s]])
  let h9 ← sr (← ExceptT.mk [[e UNION f = d
           ==> d INTER g SUBSET s ==> e INTER g SUBSET s]])
  let h8 ← tt (← ExceptT.mk [[~(p /\ q) <=> p ==> ~q]])
  let h7 ← sr (← ExceptT.mk [[(s DIFF t) INTER t = {}]])
  let h6 ← sr (← ExceptT.mk [[IMAGE g i SUBSET n
        ==> g a IN d0 /\ g b IN d0 /\ g a IN d1 /\ g b IN d1 /\
            ~(i = {}) /\ (d0 UNION d1) INTER n = {}
            ==> d0 INTER IMAGE g (i UNION {a,b}) = {g a,g b} /\
                d1 INTER IMAGE g (i UNION {a,b}) = {g a,g b} /\
                ~(IMAGE g (i UNION {a,b}) INTER n = {})]])
  let h5 ← sr (← ExceptT.mk [[IMAGE f t SUBSET u
        ==> IMAGE f s DIFF IMAGE f (s DIFF t) SUBSET u]])
  let h4 ← ms [] (← ExceptT.mk [[c = b /\ b = a ==> b = a /\ c = a]])
  let h3 ← sr (← ExceptT.mk [[s SUBSET convex hull s /\ t SUBSET s ==> t SUBSET convex hull s]])
  let h2 ← sr (← ExceptT.mk [[s SUBSET closure s /\ u SUBSET s
      ==> u SUBSET closure s DIFF interior s UNION interior s]])
  let h1 ← sr (← ExceptT.mk [[s INTER f = {} ==> s SUBSET f UNION i ==> s SUBSET i]])
  prove ([[!g:real^1->real^2 a b L.
        simple_path g /\ pathfinish g = pathstart g /\
        (!x y. x IN interval [vec 0,vec 1] /\
               y IN interval [vec 0,vec 1]
               ==> dist(g x,g y) <= L * dist(x,y)) /\
        drop a < drop b /\
        a IN interval[vec 0,vec 1] /\ b IN interval[vec 0,vec 1] /\
        g(a) IN frontier(convex hull (path_image g)) /\
        g(b) IN frontier(convex hull (path_image g)) /\
        IMAGE g (interval(a,b)) INTER frontier(convex hull (path_image g)) = {}
        ==> ?h. simple_path h /\
                pathstart h = pathstart g /\ pathfinish h = pathstart g /\
                (!x y. x IN interval [vec 0,vec 1] /\
                       y IN interval [vec 0,vec 1]
                       ==> dist(h x,h y) <= L * dist(x,y)) /\
                path_length h < path_length g /\
                convex hull (path_image h) = convex hull (path_image g) /\
                (!x. ~(x IN interval(a,b)) ==> h x = g x) /\
                IMAGE h (interval[a,b]) SUBSET
                frontier(convex hull (path_image g))]])
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC ([[interval(a:real^1,b) = {}]]) THENL
     [ASM_MESON_TAC [INTERVAL_NE_EMPTY_1], ALL_TAC] THEN
    SUBGOAL_THEN ([[IMAGE (g:real^1->real^2) (interval(a,b)) SUBSET
    interior(convex hull (path_image g))]]) ASSUME_TAC THENL
     [FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h1) THEN
      REWRITE_TAC [frontier, (← HolLight.GSYM path_image)] THEN
      MATCH_MP_TAC h2 THEN
      REWRITE_TAC [CLOSURE_SUBSET, path_image] THEN
      MATCH_MP_TAC h3 THEN
      REWRITE_TAC [HULL_SUBSET] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC [SUBSET_INTERVAL_1, DROP_VEC] THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [IN_INTERVAL_1, DROP_VEC]) THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[~(interior(convex hull (path_image g)):real^2->bool = {})]]) ASSUME_TAC THENL
     [RULE_ASSUM_TAC (HolLight.REWRITE_RULE [(← HolLight.GSYM INTERVAL_NE_EMPTY_1)]) THEN HolLight.ASM SET_TAC [],
      ALL_TAC] THEN
    ASM_CASES_TAC ([[(g:real^1->real^2) a = g b]]) THENL
     [FIRST_ASSUM (MP_TAC o HolLight.SPECL [([[a:real^1]]), ([[b:real^1]])] o HolLight.CONJUNCT2 o
          HolLight.REWRITE_RULE [simple_path]) THEN
      ASM_REWRITE_TAC [] THEN
      STRIP_TAC THEN UNDISCH_TAC ([[drop a < drop b]]) THEN
      ASM_REWRITE_TAC [DROP_VEC, REAL_LT_REFL] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      UNDISCH_TAC ([[~(interior(convex hull path_image g):real^2->bool = {})]]) THEN
      SUBGOAL_THEN ([[convex hull path_image g:real^2->bool = convex hull IMAGE g {a, b}]]) (fun th => HolLight.tactic_of do
        pure (REWRITE_TAC [th, IMAGE_CLAUSES, (← HolLight.GSYM SEGMENT_CONVEX_HULL),
                              INTERIOR_SEGMENT, DIMINDEX_2, LE_REFL])) THEN
      MATCH_MP_TAC CONVEX_HULL_REDUNDANT_SUBSET THEN
      ASM_SIMP_TAC [COMPACT_PATH_IMAGE, SIMPLE_PATH_IMP_PATH] THEN
      CONJ_TAC THENL [REWRITE_TAC [path_image] THEN HolLight.ASM SET_TAC [], ALL_TAC] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ_ALT] SUBSET_TRANS)) THEN
      ASM_REWRITE_TAC [path_image, OPEN_CLOSED_INTERVAL_1] THEN SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[convex hull (IMAGE (g:real^1->real^2)
                  (interval[vec 0,vec 1] DIFF interval(a,b))) =
    convex hull (path_image g) /\
    convex hull (segment[(g:real^1->real^2) a,g b] UNION
                 IMAGE g (interval[vec 0,vec 1] DIFF interval(a,b))) =
    convex hull (path_image g)]]) STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC h4 THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_ANTISYM THEN SIMP_TAC [HULL_MONO, SUBSET_UNION] THEN
        MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [CONVEX_CONVEX_HULL] THEN
        REWRITE_TAC [UNION_SUBSET, HULL_SUBSET] THEN
        REWRITE_TAC [SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
        REWRITE_TAC [INSERT_SUBSET, EMPTY_SUBSET] THEN
        CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_REWRITE_TAC [IN_DIFF, ENDS_IN_INTERVAL],
        CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC CONVEX_HULL_REDUNDANT_SUBSET THEN
        ASM_SIMP_TAC [COMPACT_PATH_IMAGE, SIMPLE_PATH_IMP_PATH] THEN
        REWRITE_TAC [path_image] THEN CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN
        MATCH_MP_TAC h5 THEN
        ASM_REWRITE_TAC [(← HolLight.GSYM path_image)]],
      ALL_TAC] THEN
    MP_TAC (← HolLight.ISPECL [([[g:real^1->real^2]]), ([[a:real^1]]), ([[b:real^1]])] EXISTS_DOUBLE_ARC_EXPLICIT) THEN
    ASM_SIMP_TAC [REAL_LT_IMP_LE, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [([[g0:real^1->real^2]]), ([[g1:real^1->real^2]])] THEN
    REPLICATE_TAC 6 (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (ASSUME_TAC o HolLight.SYM) MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (MP_TAC o HolLight.SYM) STRIP_ASSUME_TAC) THEN
    DISCH_THEN (fun th => RULE_ASSUM_TAC (HolLight.REWRITE_RULE [th]) THEN ASSUME_TAC th) THEN
    MP_TAC (← HolLight.ISPEC ([[convex hull (path_image g):real^2->bool]]) RECTIFIABLE_LOOP_RELATIVE_FRONTIER_CONVEX) THEN
    ASM_SIMP_TAC [RELATIVE_FRONTIER_NONEMPTY_INTERIOR] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC [CONVEX_CONVEX_HULL, BOUNDED_CONVEX_HULL,
                   BOUNDED_PATH_IMAGE, SIMPLE_PATH_IMP_PATH] THEN
      ASM_MESON_TAC [AFF_DIM_NONEMPTY_INTERIOR, DIMINDEX_2],
      DISCH_THEN (X_CHOOSE_THEN ([[d:real^1->real^2]]) STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN ([[?d0 d1.
      arc d0 /\
      arc d1 /\
      pathstart d0 = g a /\
      pathfinish d0 = g b /\
      pathstart d1 = g b /\
      pathfinish d1 = g a /\
      path_image d0 INTER path_image d1 = {(g:real^1->real^2) a, g b} /\
      path_image d0 UNION path_image d1 = path_image d /\
      inside (path_image d0 UNION path_image g0) INTER
      inside (path_image d1 UNION path_image g0) = {} /\
      inside (path_image d0 UNION path_image g0) UNION
      inside (path_image d1 UNION path_image g0) UNION
      path_image g0 DIFF {g a, g b} =
      interior (convex hull path_image g) /\
      (path_image g1 DIFF {g b, g a}) INTER path_image d0 = {}]]) STRIP_ASSUME_TAC THENL
     [MP_TAC (← HolLight.ISPECL [([[d:real^1->real^2]]),
                     ([[(g:real^1->real^2) a]]), ([[(g:real^1->real^2) b]])] EXISTS_DOUBLE_ARC) THEN
      ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[d0:real^1->real^2]]), ([[d1:real^1->real^2]])] THEN
      STRIP_TAC THEN
      MP_TAC (← HolLight.ISPECL [([[d0:real^1->real^2]]), ([[reversepath d1:real^1->real^2]]),
        ([[g0:real^1->real^2]]), ([[(g:real^1->real^2) a]]), ([[(g:real^1->real^2) b]])] SPLIT_INSIDE_SIMPLE_CLOSED_CURVE) THEN
      ASM_REWRITE_TAC [PATH_IMAGE_REVERSEPATH,
        SIMPLE_PATH_REVERSEPATH_EQ, PATHSTART_REVERSEPATH,
        PATHFINISH_REVERSEPATH] THEN
      HolLight.ASM (gsimp 4) [INSIDE_FRONTIER_EQ_INTERIOR, CONVEX_CONVEX_HULL,
        BOUNDED_CONVEX_HULL, BOUNDED_PATH_IMAGE, SIMPLE_PATH_IMP_PATH] THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC [ARC_IMP_SIMPLE_PATH] THEN
        SUBST1_TAC (← HolLight.SYM (← HolLight.ASSUME ([[IMAGE (g:real^1->real^2) (interval[a,b]) = path_image g0]]))) THEN
        MP_TAC (← HolLight.ISPECL [([[a:real^1]]), ([[b:real^1]])] CLOSED_OPEN_INTERVAL_1) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC, DISCH_THEN SUBST1_TAC] THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h6) THEN
        ASM_REWRITE_TAC [INTERVAL_NE_EMPTY_1] THEN
        REWRITE_TAC [frontier, h7] THEN
        ASM_MESON_TAC [PATHSTART_IN_PATH_IMAGE, PATHFINISH_IN_PATH_IMAGE],
        STRIP_TAC] THEN
      MP_TAC (← HolLight.ISPEC ([[g1:real^1->real^2]]) CONNECTED_SIMPLE_PATH_ENDLESS) THEN
      ASM_SIMP_TAC [ARC_IMP_SIMPLE_PATH] THEN
      REWRITE_TAC [CONNECTED_OPEN_IN, NOT_EXISTS_THM] THEN
      DISCH_THEN (MP_TAC o HolLight.SPECL [([[(path_image(g1:real^1->real^2) DIFF {g(b:real^1),g a}) DIFF
       closure(inside(path_image d1 UNION path_image g0))]]),
        ([[(path_image(g1:real^1->real^2) DIFF {g(b:real^1),g a}) DIFF
       closure(inside(path_image d0 UNION path_image g0))]])]) THEN
      REWRITE_TAC [h8] THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [IMP_IMP] THEN ANTS_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC OPEN_IN_DIFF_CLOSED THEN
        REWRITE_TAC [CLOSED_CLOSURE],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[(path_image g1 DIFF {(g:real^1->real^2) b, g a}) DIFF
      closure(inside(path_image d1 UNION path_image g0)) =
      (path_image g1 DIFF {(g:real^1->real^2) b, g a}) INTER
      (path_image d0 UNION inside(path_image d0 UNION path_image g0)) /\
      (path_image g1 DIFF {(g:real^1->real^2) b, g a}) DIFF
      closure(inside(path_image d0 UNION path_image g0)) =
      (path_image g1 DIFF {(g:real^1->real^2) b, g a}) INTER
      (path_image d1 UNION inside(path_image d1 UNION path_image g0))]]) (CONJUNCTS_THEN SUBST1_TAC) THENL
       [REWRITE_TAC [CLOSURE_UNION_FRONTIER] THEN CONJ_TAC THENL
         [MP_TAC (← HolLight.ISPEC ([[reversepath d1 ++ reversepath g0:real^1->real^2]]) JORDAN_INSIDE_OUTSIDE),
          MP_TAC (← HolLight.ISPEC ([[d0 ++ reversepath g0:real^1->real^2]]) JORDAN_INSIDE_OUTSIDE)] THEN
       (ANTS_TAC THENL
         [ASM_REWRITE_TAC [PATHFINISH_JOIN, PATHSTART_JOIN,
                          PATHSTART_REVERSEPATH, PATHFINISH_REVERSEPATH] THEN
          MATCH_MP_TAC SIMPLE_PATH_JOIN_LOOP THEN
          ASM_REWRITE_TAC [PATHSTART_REVERSEPATH, PATHFINISH_REVERSEPATH] THEN
          ASM_REWRITE_TAC [ARC_REVERSEPATH_EQ, PATH_IMAGE_REVERSEPATH] THEN
          FIRST [FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h9),
            FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h10)] THEN
          ASM_REWRITE_TAC [] THEN
          SUBST1_TAC (← HolLight.SYM (← HolLight.ASSUME ([[IMAGE (g:real^1->real^2) (interval [a,b]) = path_image g0]]))) THEN
          MP_TAC (← HolLight.ISPECL [([[a:real^1]]), ([[b:real^1]])] CLOSED_OPEN_INTERVAL_1) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC, DISCH_THEN SUBST1_TAC] THEN
          REWRITE_TAC [frontier] THEN HolLight.ASM SET_TAC [],
          ASM_SIMP_TAC [PATH_IMAGE_JOIN, PATH_IMAGE_REVERSEPATH,
                       PATHSTART_REVERSEPATH, PATHFINISH_REVERSEPATH] THEN
          DISCH_THEN (fun th => REWRITE_TAC [th])]) THEN
        ASM_SIMP_TAC [h11] THEN
        MATCH_MP_TAC h12 THENL [ONCE_REWRITE_TAC [h13], ALL_TAC] THEN
       (X_GEN_TAC ([[z:real^2]]) THEN
        REWRITE_TAC [IN_DIFF, IN_INSERT, NOT_IN_EMPTY, DE_MORGAN_THM] THEN
        STRIP_TAC THEN
        REWRITE_TAC [h14] THEN
        CONJ_TAC THENL
         [ASM_REWRITE_TAC [h15] THEN
          FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h16) THEN
          CONJ_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
          REWRITE_TAC [FRONTIER_UNION_INTERIOR] THEN
          MATCH_MP_TAC CLOSURE_INC THEN MATCH_MP_TAC HULL_INC THEN
          HolLight.ASM SET_TAC [],
          FIRST_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h17) THEN
          ASM_REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN CONJ_TAC THENL
           [MP_TAC (← HolLight.ISPECL [([[inside(path_image d1 UNION path_image g0):real^2->bool]]),
              ([[inside(path_image d0 UNION path_image g0):real^2->bool]])] OPEN_INTER_CLOSURE_EQ_EMPTY),
            MP_TAC (← HolLight.ISPECL [([[inside(path_image d0 UNION path_image g0):real^2->bool]]),
              ([[inside(path_image d1 UNION path_image g0):real^2->bool]])] OPEN_INTER_CLOSURE_EQ_EMPTY)] THEN
          HolLight.ASM (gsimp 4) [OPEN_INSIDE, CLOSED_UNION, CLOSED_PATH_IMAGE, ARC_IMP_PATH] THEN
          ONCE_REWRITE_TAC [INTER_COMM] THEN ASM_REWRITE_TAC [] THEN
          MATCH_MP_TAC h18 THEN
          REWRITE_TAC [CLOSURE_UNION_FRONTIER] THEN
          MATCH_MP_TAC h19 THENL
           [MP_TAC (← HolLight.ISPEC ([[d0 ++ reversepath g0:real^1->real^2]]) JORDAN_INSIDE_OUTSIDE),
            MP_TAC (← HolLight.ISPEC ([[reversepath d1 ++ reversepath g0:real^1->real^2]]) JORDAN_INSIDE_OUTSIDE)] THEN
          ASM_SIMP_TAC [PATH_IMAGE_JOIN, PATH_IMAGE_REVERSEPATH,
                       PATHSTART_REVERSEPATH, PATHFINISH_REVERSEPATH] THEN
          (ANTS_TAC THENL [ALL_TAC, SET_TAC []]) THEN
          ASM_REWRITE_TAC [PATHFINISH_JOIN, PATHSTART_JOIN,
                          PATHSTART_REVERSEPATH, PATHFINISH_REVERSEPATH] THEN
          MATCH_MP_TAC SIMPLE_PATH_JOIN_LOOP THEN
          ASM_REWRITE_TAC [PATHSTART_REVERSEPATH, PATHFINISH_REVERSEPATH] THEN
          ASM_REWRITE_TAC [ARC_REVERSEPATH_EQ, PATH_IMAGE_REVERSEPATH] THEN
          FIRST [FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h20),
            FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h21)] THEN
          ASM_REWRITE_TAC [] THEN
          SUBST1_TAC (← HolLight.SYM (← HolLight.ASSUME ([[IMAGE (g:real^1->real^2) (interval [a,b]) = path_image g0]]))) THEN
          MP_TAC (← HolLight.ISPECL [([[a:real^1]]), ([[b:real^1]])] CLOSED_OPEN_INTERVAL_1) THEN
          (ANTS_TAC THENL [ASM_REAL_ARITH_TAC, DISCH_THEN SUBST1_TAC]) THEN
          REWRITE_TAC [frontier] THEN HolLight.ASM SET_TAC []]),
        ALL_TAC] THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC h22 THEN
        REWRITE_TAC [SUBSET, IN_DIFF, IN_INSERT,
                    NOT_IN_EMPTY, DE_MORGAN_THM] THEN
        X_GEN_TAC ([[z:real^2]]) THEN STRIP_TAC THEN
        ONCE_REWRITE_TAC [h23] THEN
        ASM_REWRITE_TAC [] THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h24) THEN
        CONJ_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
        REWRITE_TAC [FRONTIER_UNION_INTERIOR] THEN
        MATCH_MP_TAC CLOSURE_INC THEN MATCH_MP_TAC HULL_INC THEN
        HolLight.ASM SET_TAC [],
        ALL_TAC] THEN
      ANTS_TAC THENL
       [REWRITE_TAC [h25] THEN
        REWRITE_TAC [SUBSET, IN_DIFF, IN_INSERT,
                    NOT_IN_EMPTY, DE_MORGAN_THM] THEN
        X_GEN_TAC ([[z:real^2]]) THEN STRIP_TAC THEN REWRITE_TAC [IN_INTER] THEN
        FIRST_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h26) THEN
        ASM_REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN CONJ_TAC THENL
         [MP_TAC (← HolLight.ISPECL [([[inside(path_image d1 UNION path_image g0):real^2->bool]]),
            ([[inside(path_image d0 UNION path_image g0):real^2->bool]])] OPEN_INTER_CLOSURE_EQ_EMPTY),
          MP_TAC (← HolLight.ISPECL [([[inside(path_image d0 UNION path_image g0):real^2->bool]]),
            ([[inside(path_image d1 UNION path_image g0):real^2->bool]])] OPEN_INTER_CLOSURE_EQ_EMPTY)] THEN
        HolLight.ASM (gsimp 4) [OPEN_INSIDE, CLOSED_UNION, CLOSED_PATH_IMAGE, ARC_IMP_PATH] THEN
        ONCE_REWRITE_TAC [INTER_COMM] THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC h27 THEN
        REWRITE_TAC [CLOSURE_UNION_FRONTIER] THEN
        MATCH_MP_TAC h28 THENL
         [MP_TAC (← HolLight.ISPEC ([[d0 ++ reversepath g0:real^1->real^2]]) JORDAN_INSIDE_OUTSIDE),
          MP_TAC (← HolLight.ISPEC ([[reversepath d1 ++ reversepath g0:real^1->real^2]]) JORDAN_INSIDE_OUTSIDE)] THEN
        ASM_SIMP_TAC [PATH_IMAGE_JOIN, PATH_IMAGE_REVERSEPATH,
                     PATHSTART_REVERSEPATH, PATHFINISH_REVERSEPATH] THEN
        (ANTS_TAC THENL [ALL_TAC, SET_TAC []]) THEN
        ASM_REWRITE_TAC [PATHFINISH_JOIN, PATHSTART_JOIN,
                        PATHSTART_REVERSEPATH, PATHFINISH_REVERSEPATH] THEN
        MATCH_MP_TAC SIMPLE_PATH_JOIN_LOOP THEN
        ASM_REWRITE_TAC [PATHSTART_REVERSEPATH, PATHFINISH_REVERSEPATH] THEN
        ASM_REWRITE_TAC [ARC_REVERSEPATH_EQ, PATH_IMAGE_REVERSEPATH] THEN
        FIRST [FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h29),
          FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h30)] THEN
        ASM_REWRITE_TAC [] THEN
        SUBST1_TAC (← HolLight.SYM (← HolLight.ASSUME ([[IMAGE (g:real^1->real^2) (interval [a,b]) = path_image g0]]))) THEN
        MP_TAC (← HolLight.ISPECL [([[a:real^1]]), ([[b:real^1]])] CLOSED_OPEN_INTERVAL_1) THEN
        (ANTS_TAC THENL [ASM_REAL_ARITH_TAC, DISCH_THEN SUBST1_TAC]) THEN
        REWRITE_TAC [frontier] THEN HolLight.ASM SET_TAC [],
        ALL_TAC] THEN
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP h31) THEN
      DISCH_THEN DISJ_CASES_TAC THENL
       [MAP_EVERY EXISTS_TAC [([[d0:real^1->real^2]]), ([[d1:real^1->real^2]])],
        MAP_EVERY EXISTS_TAC [([[reversepath d1:real^1->real^2]]),
          ([[reversepath d0:real^1->real^2]])]] THEN
      ASM_REWRITE_TAC [] THEN
      ASM_REWRITE_TAC [ARC_REVERSEPATH_EQ, PATHSTART_REVERSEPATH,
                      PATHFINISH_REVERSEPATH, PATH_IMAGE_REVERSEPATH] THEN
      HolLight.ASM SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[convex hull (path_image d1):real^2->bool = convex hull (path_image g)]]) ASSUME_TAC THENL
     [REWRITE_TAC [(← HolLight.GSYM SUBSET_ANTISYM_EQ)] THEN CONJ_TAC THENL
       [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [CONVEX_CONVEX_HULL] THEN
        UNDISCH_TAC ([[path_image d:real^2->bool = frontier (convex hull path_image g)]]) THEN
        HolLight.ASM (gsimp 5) [frontier, CLOSURE_CLOSED, COMPACT_IMP_CLOSED, COMPACT_PATH_IMAGE,
          COMPACT_CONVEX_HULL, SIMPLE_PATH_IMP_PATH] THEN
        HolLight.ASM SET_TAC [],
        ALL_TAC] THEN
      TRANS_TAC SUBSET_TRANS ([[convex hull ((path_image g0 UNION path_image g1) INTER
                   (path_image d0 UNION path_image d1)):real^2->bool]]) THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC h32 THEN
        MATCH_MP_TAC CONVEX_HULL_REDUNDANT_SUBSET THEN
        ASM_SIMP_TAC [COMPACT_PATH_IMAGE, SIMPLE_PATH_IMP_PATH, INTER_SUBSET] THEN
        REWRITE_TAC [frontier] THEN
        MATCH_MP_TAC h33 THEN
        MESON_TAC [SUBSET_TRANS, CLOSURE_SUBSET, HULL_SUBSET],
        MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC h34 THEN
        TRANS_TAC SUBSET_TRANS ([[{(g:real^1->real^2) a,g b}]]) THEN CONJ_TAC THENL
         [MATCH_MP_TAC h35 THEN
          CONJ_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
          FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h36) THEN
          SUBST1_TAC (← HolLight.SYM (← HolLight.ASSUME ([[IMAGE (g:real^1->real^2) (interval [a,b]) = path_image g0]]))) THEN
          RULE_ASSUM_TAC (HolLight.REWRITE_RULE [OPEN_CLOSED_INTERVAL_1]) THEN
          HolLight.ASM SET_TAC [],
          REWRITE_TAC [INSERT_SUBSET, EMPTY_SUBSET] THEN
          ASM_MESON_TAC [ARC_IMP_PATH, PATHSTART_IN_PATH_IMAGE,
                        PATHFINISH_IN_PATH_IMAGE]]],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[segment[(g:real^1->real^2) a,g b] SUBSET
    frontier(convex hull (path_image g))]]) ASSUME_TAC THENL
     [REWRITE_TAC [SUBSET, frontier, IN_DIFF] THEN
      REWRITE_TAC [h37] THEN
      CONJ_TAC THENL
       [RULE_ASSUM_TAC (HolLight.REWRITE_RULE [frontier, IN_DIFF]) THEN
        ASM_SIMP_TAC [CONVEX_CONTAINS_SEGMENT_IMP,
                     CONVEX_CLOSURE, CONVEX_CONVEX_HULL],
        ALL_TAC] THEN
      ASM_SIMP_TAC [SEGMENT_CLOSED_OPEN, IN_UNION, IN_INSERT, NOT_IN_EMPTY] THEN
      X_GEN_TAC ([[z:real^2]]) THEN DISCH_THEN DISJ_CASES_TAC THENL
       [DISCH_TAC,
        RULE_ASSUM_TAC (HolLight.REWRITE_RULE [frontier, IN_DIFF]) THEN HolLight.ASM SET_TAC []] THEN
      ABBREV_TAC ([[ga = (g:real^1->real^2) a]]) THEN
      ABBREV_TAC ([[gb = (g:real^1->real^2) b]]) THEN
      REPEAT (POP_ASSUM MP_TAC) THEN
      GEOM_ORIGIN_TAC ([[ga:real^2]]) THEN
      GEOM_BASIS_MULTIPLE_TAC 1 ([[gb:real^2]]) THEN
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN ([[(g:real^1->real^2) a $2 = &0 /\
      (g:real^1->real^2) b $2 = &0]]) STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC [VEC_COMPONENT, VECTOR_MUL_COMPONENT] THEN
        SIMP_TAC [BASIS_COMPONENT, DIMINDEX_2, ARITH, REAL_MUL_RZERO],
        UNDISCH_THEN ([[(g:real^1->real^2) a = vec 0]]) (SUBST_ALL_TAC o HolLight.SYM) THEN
        UNDISCH_THEN ([[(g:real^1->real^2) b = gb % basis 1]]) (SUBST_ALL_TAC o HolLight.SYM)] THEN
      REWRITE_TAC [SUBSET, frontier, IN_DIFF] THEN
      MP_TAC (← HolLight.ISPECL [([[(g:real^1->real^2) a]]), ([[(g:real^1->real^2) b]]), ([[z:real^2]])] SEGMENT_HORIZONTAL) THEN
      ASM_REWRITE_TAC [SEGMENT_CLOSED_OPEN, IN_UNION] THEN
      DISCH_THEN (ASSUME_TAC o HolLight.CONJUNCT1) THEN
      SUBGOAL_THEN ([[~(path_image d1 SUBSET {x:real^2 | &0 <= x$2}) /\
      ~(path_image d1 SUBSET {x:real^2 | x$2 <= &0})]]) STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[convex:(real^2->bool)->bool]]) o
            HolLight.MATCH_MP HULL_MONO) THEN
        ASM_REWRITE_TAC [] THEN
        SIMP_TAC [HULL_P, CONVEX_HALFSPACE_COMPONENT_LE,
                 (← HolLight.REWRITE_RULE [real_ge] CONVEX_HALFSPACE_COMPONENT_GE)] THEN
        DISCH_THEN (MP_TAC o HolLight.MATCH_MP SUBSET_INTERIOR) THEN
        REWRITE_TAC [INTERIOR_HALFSPACE_COMPONENT_LE,
                  (← HolLight.REWRITE_RULE [real_ge] INTERIOR_HALFSPACE_COMPONENT_GE)] THEN
        REWRITE_TAC [real_gt, REAL_LT_LE] THEN HolLight.ASM SET_TAC [],
        ALL_TAC] THEN
      MP_TAC (← HolLight.ISPEC ([[d1:real^1->real^2]]) CONNECTED_SIMPLE_PATH_ENDLESS) THEN
      ASM_SIMP_TAC [ARC_IMP_SIMPLE_PATH, connected] THEN
      MAP_EVERY EXISTS_TAC [([[{x:real^2 | &0 < x$2}]]), ([[{x:real^2 | x$2 < &0}]])] THEN
      REWRITE_TAC [OPEN_HALFSPACE_COMPONENT_LT,
                  (← HolLight.REWRITE_RULE [real_gt] OPEN_HALFSPACE_COMPONENT_GT)] THEN
      CONJ_TAC THENL
       [REWRITE_TAC [SUBSET, IN_DIFF, IN_DIFF, IN_INSERT, NOT_IN_EMPTY] THEN
        X_GEN_TAC ([[w:real^2]]) THEN REWRITE_TAC [DE_MORGAN_THM] THEN STRIP_TAC THEN
        REWRITE_TAC [IN_ELIM_THM, IN_UNION] THEN
        REWRITE_TAC [h38] THEN
        DISCH_TAC THEN
        MP_TAC (← HolLight.ISPECL [([[convex hull (path_image g):real^2->bool]]),
          ([[(g:real^1->real^2) a]]), ([[(g:real^1->real^2) b]]), ([[w:real^2]])] SEGMENT_SUBSET_RELATIVE_FRONTIER_CONVEX_GEN) THEN
        ASM_REWRITE_TAC [NOT_IMP, CONVEX_CONVEX_HULL] THEN
        REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC [COLLINEAR_3_2D] THEN REAL_ARITH_TAC2,
          ASM_SIMP_TAC [RELATIVE_FRONTIER_NONEMPTY_INTERIOR] THEN HolLight.ASM SET_TAC [],
          ASM_SIMP_TAC [RELATIVE_FRONTIER_NONEMPTY_INTERIOR] THEN
          REWRITE_TAC [frontier] THEN FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h39) THEN
          FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h40) THEN
          REWRITE_TAC [open_segment] THEN
          MATCH_MP_TAC h41 THEN
          REWRITE_TAC [SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
          SET_TAC []],
        CONJ_TAC THENL
         [REWRITE_TAC [EXTENSION, IN_INTER, IN_ELIM_THM, NOT_IN_EMPTY] THEN
          REAL_ARITH_TAC2,
          ALL_TAC] THEN
        CONJ_TAC THENL
         [UNDISCH_TAC ([[~(path_image d1 SUBSET {x:real^2 | x$2 <= &0})]]),
          UNDISCH_TAC ([[~(path_image d1 SUBSET {x:real^2 | &0 <= x$2})]])] THEN
        MATCH_MP_TAC h42 THEN
        REWRITE_TAC [EXTENSION, IN_UNIV, NOT_IN_EMPTY, IN_ELIM_THM, IN_INTER,
                    IN_INSERT, IN_UNION] THEN
        (CONJ_TAC THENL [ASM_MESON_TAC [REAL_LT_REFL], REAL_ARITH_TAC2])],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[path_image d0 SUBSET segment[(g:real^1->real^2) a,g b] \/
    path_image(reversepath d1) SUBSET segment[(g:real^1->real^2) a,g b] ]]) MP_TAC THENL
     [MATCH_MP_TAC CONNECTED_SUBSET_ARC_PAIR THEN
      ASM_SIMP_TAC [ARC_REVERSEPATH_EQ, PATHSTART_REVERSEPATH,
                   PATHFINISH_REVERSEPATH, PATH_IMAGE_REVERSEPATH] THEN
      REWRITE_TAC [ENDS_IN_SEGMENT, CONNECTED_SEGMENT],
      REWRITE_TAC [PATH_IMAGE_REVERSEPATH]] THEN
    STRIP_TAC THENL
     [ALL_TAC,
      SUBGOAL_THEN ([[interior(convex hull (path_image d1)) SUBSET
      interior(convex hull (segment[(g:real^1->real^2) a,g b]))]]) MP_TAC THENL
       [ASM_SIMP_TAC [SUBSET_INTERIOR, HULL_MONO],
        ASM_SIMP_TAC [HULL_P, CONVEX_SEGMENT, INTERIOR_SEGMENT] THEN
        REWRITE_TAC [DIMINDEX_2, LE_REFL] THEN HolLight.ASM SET_TAC []]] THEN
    SUBGOAL_THEN ([[path_image d0 = segment[(g:real^1->real^2) a,g b] ]]) ASSUME_TAC THENL
     [MATCH_MP_TAC CONNECTED_SUBSET_SEGMENT THEN
      ASM_SIMP_TAC [CONNECTED_PATH_IMAGE, ARC_IMP_PATH] THEN
      ASM_MESON_TAC [PATHSTART_IN_PATH_IMAGE, PATHFINISH_IN_PATH_IMAGE,
                    ARC_IMP_PATH],
      ALL_TAC] THEN
    ABBREV_TAC ([[h = \t. if t IN interval(a,b)
            then g(a) + (drop t - drop a) / (drop b - drop a) % (g b - g a)
            else (g:real^1->real^2) t]]) THEN
    EXISTS_TAC ([[h:real^1->real^2]]) THEN
    SUBGOAL_THEN ([[pathstart h:real^2 = pathstart g /\ pathfinish h = pathfinish g]]) MP_TAC THENL
     [EXPAND_TAC "h" THEN REWRITE_TAC [pathstart, pathfinish] THEN
      CONJ_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [IN_INTERVAL_1, DROP_VEC]) THEN
      ASM_REAL_ARITH_TAC,
      ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC []] THEN
    SUBGOAL_THEN ([[IMAGE h (interval(a,b)) = segment((g:real^1->real^2) a,g b)]]) ASSUME_TAC THENL
     [ASM_SIMP_TAC [SEGMENT_IMAGE_INTERVAL] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h43) THEN
      MP_TAC (← HolLight.ISPECL [([[a:real^1]]), ([[b:real^1]])] (← HolLight.CONJUNCT2 SEGMENT_IMAGE_INTERVAL)) THEN
      ASM_SIMP_TAC [(← HolLight.GSYM DROP_EQ), REAL_LT_IMP_LE, REAL_LT_IMP_NE, SEGMENT_1] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [(← HolLight.GSYM IMAGE_o), o_DEF] THEN
      MATCH_MP_TAC h44 THEN
      X_GEN_TAC ([[t:real^1]]) THEN REWRITE_TAC [h45] THEN
      AP_TERM_TAC THEN REWRITE_TAC [VECTOR_MUL_ASSOC] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC [DROP_ADD, DROP_SUB, DROP_CMUL] THEN
      UNDISCH_TAC ([[drop a < drop b]]) THEN CONV_TAC rf,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[(h:real^1->real^2) a = g a /\ h b = g b]]) STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "h" THEN REWRITE_TAC [ENDS_IN_INTERVAL],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[IMAGE h (interval[a,b]) = segment[(g:real^1->real^2) a,g b] ]]) ASSUME_TAC THENL
     [ASM_SIMP_TAC [CLOSED_OPEN_INTERVAL_1, REAL_LT_IMP_LE] THEN
      REWRITE_TAC [SEGMENT_CLOSED_OPEN] THEN HolLight.ASM SET_TAC [],
      ASM_REWRITE_TAC []] THEN
    REWRITE_TAC [CONJ_ASSOC] THEN ONCE_REWRITE_TAC [CONJ_SYM] THEN
    REWRITE_TAC [(← HolLight.GSYM CONJ_ASSOC)] THEN CONJ_TAC THENL
     [EXPAND_TAC "h" THEN SIMP_TAC [], ALL_TAC] THEN
    REWRITE_TAC [simple_path, (← HolLight.GSYM CONJ_ASSOC)] THEN
    MATCH_MP_TAC h46 THEN
    REWRITE_TAC [(← HolLight.GSYM CONJ_ASSOC)] THEN CONJ_TAC THENL
     [REWRITE_TAC [SessionMultiLib.Vectors.dist, path] THEN MESON_TAC [LIPSCHITZ_IMP_CONTINUOUS_ON],
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC h47 THEN
      EXISTS_TAC ([[\x:real^1. x IN interval(a,b)]]) THEN
      CONJ_TAC THENL [MESON_TAC [], REWRITE_TAC []] THEN REPEAT CONJ_TAC THENL
       [EXPAND_TAC "h" THEN SIMP_TAC [] THEN
        UNDISCH_TAC ([[simple_path(g:real^1->real^2)]]) THEN
        REWRITE_TAC [simple_path] THEN MESON_TAC [],
        EXPAND_TAC "h" THEN SIMP_TAC [] THEN
        REWRITE_TAC [h48] THEN
        ASM_REWRITE_TAC [VECTOR_MUL_RCANCEL, VECTOR_SUB_EQ] THEN
        ASM_SIMP_TAC [h49] THEN
        ASM_SIMP_TAC [DROP_EQ, VECTOR_SUB_EQ],
        MAP_EVERY X_GEN_TAC [([[x:real^1]]), ([[y:real^1]])] THEN REPEAT STRIP_TAC THEN
        UNDISCH_TAC ([[IMAGE (g:real^1->real^2) (interval [vec 0,vec 1] DIFF interval (a,b)) =
        path_image g1]]) THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[x:real^1]]) o HolLight.MATCH_MP h50) THEN
        ASM_REWRITE_TAC [IN_DIFF] THEN DISCH_TAC THEN
        UNDISCH_TAC ([[(path_image g1 DIFF {(g:real^1->real^2) b, g a}) INTER path_image d0 =
         {}]]) THEN
        ASM_REWRITE_TAC [EXTENSION, NOT_IN_EMPTY, NOT_EXISTS_THM] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[(g:real^1->real^2) x]])) THEN
        ASM_REWRITE_TAC [SEGMENT_CLOSED_OPEN, IN_DIFF, IN_INTER] THEN
        SUBGOAL_THEN ([[(g:real^1->real^2) x = h x]]) SUBST1_TAC THENL
         [EXPAND_TAC "h" THEN REWRITE_TAC [] THEN ASM_REWRITE_TAC [],
          ALL_TAC] THEN
        DISCH_THEN (MP_TAC o HolLight.MATCH_MP h51) THEN
        REWRITE_TAC [ENDS_NOT_IN_SEGMENT] THEN HolLight.ASM SET_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[~(a:real^1 = b)]]) ASSUME_TAC THENL
      [ASM_MESON_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC h52 THEN CONJ_TAC THENL
     [REWRITE_TAC [SessionMultiLib.Vectors.dist] THEN
      MATCH_MP_TAC LIPSCHITZ_ON_COMBINE THEN EXISTS_TAC ([[a:real^1]]) THEN
      CONJ_TAC THENL
       [EXPAND_TAC "h" THEN
        SIMP_TAC [IN_INTERVAL_1, (← HolLight.GSYM REAL_NOT_LE), DROP_VEC] THEN
        REPEAT STRIP_TAC THEN REWRITE_TAC [(← HolLight.GSYM SessionMultiLib.Vectors.dist)] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC [IN_INTERVAL_1, DROP_VEC] THEN
        RULE_ASSUM_TAC (HolLight.REWRITE_RULE [IN_INTERVAL_1, DROP_VEC]) THEN
        ASM_REAL_ARITH_TAC,
        ALL_TAC] THEN
      MATCH_MP_TAC LIPSCHITZ_ON_COMBINE THEN EXISTS_TAC ([[b:real^1]]) THEN
      CONJ_TAC THENL
       [ALL_TAC,
        EXPAND_TAC "h" THEN
        SIMP_TAC [IN_INTERVAL_1, (← HolLight.GSYM REAL_NOT_LE), DROP_VEC] THEN
        REPEAT STRIP_TAC THEN REWRITE_TAC [(← HolLight.GSYM SessionMultiLib.Vectors.dist)] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC [IN_INTERVAL_1, DROP_VEC] THEN
        RULE_ASSUM_TAC (HolLight.REWRITE_RULE [IN_INTERVAL_1, DROP_VEC]) THEN
        ASM_REAL_ARITH_TAC] THEN
      SUBGOAL_THEN ([[!t. t IN interval[a,b]
          ==> (h:real^1->real^2) t =
              g a + (drop t - drop a) / (drop b - drop a) % (g b - g a)]]) (fun th => SIMP_TAC [th]) THENL
       [ASM_SIMP_TAC [CLOSED_OPEN_INTERVAL_1, REAL_LT_IMP_LE] THEN
        REWRITE_TAC [IN_UNION, IN_INSERT, NOT_IN_EMPTY] THEN
        REPEAT STRIP_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC [] THEN
        ASM_REWRITE_TAC [ENDS_IN_INTERVAL] THEN
        REWRITE_TAC [h53, VECTOR_MUL_LZERO] THEN
        REWRITE_TAC [VECTOR_ADD_RID] THEN
        ASM_SIMP_TAC [h54] THEN
        CONV_TAC va,
        ALL_TAC] THEN
      REWRITE_TAC [h55] THEN
      ASM_SIMP_TAC [NORM_MUL, REAL_ABS_DIV, h56] THEN
      REWRITE_TAC [(← HolLight.GSYM DROP_SUB), ABS_DROP, h57] THEN
      ASM_SIMP_TAC [REAL_LE_LDIV_EQ, NORM_POS_LT, VECTOR_SUB_EQ] THEN
      ONCE_REWRITE_TAC [h58] THEN
      REWRITE_TAC [IN_INTERVAL_1] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [NORM_POS_LE] THEN
      REWRITE_TAC [(← HolLight.GSYM SessionMultiLib.Vectors.dist)] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC [IN_INTERVAL_1, DROP_VEC] THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [IN_INTERVAL_1, DROP_VEC]) THEN
      ASM_REAL_ARITH_TAC,
      DISCH_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [path_length] THEN
      MP_TAC (← HolLight.GEN ([[f:real^1->real^2]]) (← HolLight.ISPECL [([[f:real^1->real^2]]), ([[vec 0:real^1]]), ([[vec 1:real^1]]), ([[a:real^1]])] VECTOR_VARIATION_COMBINE)) THEN
      ASM_REWRITE_TAC [CONJ_ASSOC, (← HolLight.GSYM IN_INTERVAL_1)] THEN
      DISCH_THEN (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPEC ([[h:real^1->real^2]]) th) THEN
       MP_TAC (← HolLight.SPEC ([[g:real^1->real^2]]) th))) THEN
      REPEAT (ANTS_TAC THENL
       [MATCH_MP_TAC LIPSCHITZ_IMP_HAS_BOUNDED_VARIATION THEN
        REWRITE_TAC [BOUNDED_INTERVAL, (← HolLight.GSYM SessionMultiLib.Vectors.dist)] THEN ASM_MESON_TAC [],
        DISCH_THEN (SUBST1_TAC o HolLight.SYM)]) THEN
      MATCH_MP_TAC h59 THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC VECTOR_VARIATION_EQ THEN EXPAND_TAC "h" THEN
        SIMP_TAC [IN_INTERVAL_1, (← HolLight.GSYM REAL_NOT_LE)],
        ALL_TAC] THEN
      MP_TAC (← HolLight.GEN ([[f:real^1->real^2]]) (← HolLight.ISPECL [([[f:real^1->real^2]]), ([[a:real^1]]), ([[vec 1:real^1]]), ([[b:real^1]])] VECTOR_VARIATION_COMBINE)) THEN
      ASM_SIMP_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, REAL_LT_IMP_LE] THEN
      ANTS_TAC THENL [ASM_MESON_TAC [IN_INTERVAL_1], ALL_TAC] THEN
      DISCH_THEN (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPEC ([[h:real^1->real^2]]) th) THEN
       MP_TAC (← HolLight.SPEC ([[g:real^1->real^2]]) th))) THEN
      REPEAT (ANTS_TAC THENL
       [MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_SUBSET THEN
        EXISTS_TAC ([[interval[vec 0:real^1,vec 1] ]]) THEN CONJ_TAC THENL
         [MATCH_MP_TAC LIPSCHITZ_IMP_HAS_BOUNDED_VARIATION THEN
          REWRITE_TAC [BOUNDED_INTERVAL, (← HolLight.GSYM SessionMultiLib.Vectors.dist)] THEN ASM_MESON_TAC [],
          REWRITE_TAC [SUBSET_INTERVAL_1, DROP_VEC] THEN
          RULE_ASSUM_TAC (HolLight.REWRITE_RULE [IN_INTERVAL_1, DROP_VEC]) THEN
          ASM_REAL_ARITH_TAC],
        DISCH_THEN (SUBST1_TAC o HolLight.SYM)]) THEN
      MATCH_MP_TAC h60 THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC VECTOR_VARIATION_EQ THEN EXPAND_TAC "h" THEN
        SIMP_TAC [IN_INTERVAL_1, (← HolLight.GSYM REAL_NOT_LE)],
        ALL_TAC] THEN
      TRANS_TAC REAL_LET_TRANS ([[vector_variation (interval[a,b])
                       (\t. g a + (drop t - drop a) / (drop b - drop a) %
                                  ((g:real^1->real^2) b - g a))]]) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC VECTOR_VARIATION_EQ THEN
        X_GEN_TAC ([[t:real^1]]) THEN
        ASM_SIMP_TAC [CLOSED_OPEN_INTERVAL_1, REAL_LT_IMP_LE] THEN
        REWRITE_TAC [IN_UNION, IN_INSERT, NOT_IN_EMPTY] THEN
        REPEAT STRIP_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC [] THEN
        ASM_REWRITE_TAC [ENDS_IN_INTERVAL] THEN
        REWRITE_TAC [h61, VECTOR_MUL_LZERO] THEN
        REWRITE_TAC [VECTOR_ADD_RID] THEN
        ASM_SIMP_TAC [h62] THEN
        CONV_TAC va,
        ALL_TAC] THEN
      REWRITE_TAC [VECTOR_VARIATION_TRANSLATION] THEN
      HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
          let x1 ← ec (HolCore.Equal.lhand w)
          let x2 ← ExceptT.mk (HolLight.PART_MATCH (HolCore.Equal.lhand o HolCore.Kernel.rand) VECTOR_VARIATION_VMUL x1)
          pure (MP_TAC x2)) THEN
      ANTS_TAC THENL [ALL_TAC, DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC [(← HolLight.ONCE_REWRITE_RULE [REAL_MUL_SYM] real_div), LIFT_CMUL] THEN
      REWRITE_TAC [LIFT_DROP, LIFT_SUB] THEN
      REWRITE_TAC [h63] THEN
      SIMP_TAC [VECTOR_VARIATION_TRANSLATION,
               HAS_BOUNDED_VARIATION_ON_TRANSLATION,
               HAS_BOUNDED_VARIATION_ON_CMUL_EQ, VECTOR_VARIATION_CMUL,
               HAS_BOUNDED_VARIATION_ON_ID, BOUNDED_INTERVAL] THEN
      REWRITE_TAC [VECTOR_VARIATION_ID] THEN
      ASM_SIMP_TAC [INTERVAL_EQ_EMPTY_1, h64] THEN
      ASM_SIMP_TAC [REAL_ABS_INV, real_abs, REAL_SUB_LE, REAL_LT_IMP_LE,
                   h65] THEN
      REWRITE_TAC [REAL_MUL_RID] THEN
      REWRITE_TAC [REAL_LT_LE] THEN
      SUBGOAL_THEN ([[(g:real^1->real^2) has_bounded_variation_on interval[a,b] ]]) ASSUME_TAC THENL
       [MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_SUBSET THEN
        EXISTS_TAC ([[interval[vec 0:real^1,vec 1] ]]) THEN CONJ_TAC THENL
         [MATCH_MP_TAC LIPSCHITZ_IMP_HAS_BOUNDED_VARIATION THEN
          REWRITE_TAC [BOUNDED_INTERVAL, (← HolLight.GSYM SessionMultiLib.Vectors.dist)] THEN ASM_MESON_TAC [],
          REWRITE_TAC [SUBSET_INTERVAL_1, DROP_VEC] THEN
          RULE_ASSUM_TAC (HolLight.REWRITE_RULE [IN_INTERVAL_1, DROP_VEC]) THEN
          ASM_REAL_ARITH_TAC],
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC VECTOR_VARIATION_GE_NORM_FUNCTION THEN
        ASM_SIMP_TAC [SEGMENT_1, REAL_LT_IMP_LE, SUBSET_REFL],
        ALL_TAC] THEN
      ABBREV_TAC ([[c:real^1 = midpoint(a,b)]]) THEN
      MP_TAC (← HolLight.ISPECL [([[g:real^1->real^2]]), ([[a:real^1]]), ([[b:real^1]]), ([[c:real^1]])] VECTOR_VARIATION_COMBINE) THEN
      SUBGOAL_THEN ([[drop a < drop c /\ drop c < drop b]]) STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "c" THEN REWRITE_TAC [midpoint, DROP_CMUL, DROP_ADD] THEN
        ASM_REAL_ARITH_TAC,
        ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN DISCH_THEN (SUBST1_TAC o HolLight.SYM)] THEN
      MATCH_MP_TAC h66 THEN
      EXISTS_TAC ([[(g:real^1->real^2) c]]) THEN CONJ_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC VECTOR_VARIATION_GE_NORM_FUNCTION THEN
        ASM_SIMP_TAC [SEGMENT_1, REAL_LT_IMP_LE, SUBSET_REFL] THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] HAS_BOUNDED_VARIATION_ON_SUBSET)) THEN
        REWRITE_TAC [SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC,
        REWRITE_TAC [(← HolLight.GSYM between), BETWEEN_IN_SEGMENT]] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h67) THEN
      REWRITE_TAC [frontier, IN_DIFF] THEN
      DISCH_THEN (MP_TAC o HolLight.CONJUNCT2) THEN REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h68) THEN
      ASM_REWRITE_TAC [IN_INTERVAL_1],
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [CONVEX_CONVEX_HULL] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC ([[IMAGE g (interval [vec 0,vec 1] DIFF interval (a,b)) UNION
                IMAGE (h:real^1->real^2) (interval(a,b))]]) THEN
      CONJ_TAC THENL
       [EXPAND_TAC "h" THEN REWRITE_TAC [path_image] THEN SET_TAC [],
        REWRITE_TAC [UNION_SUBSET] THEN ASM_REWRITE_TAC []] THEN
      CONJ_TAC THENL [ASM_MESON_TAC [SUBSET, HULL_SUBSET], ALL_TAC] THEN
      TRANS_TAC SUBSET_TRANS ([[segment[(g:real^1->real^2) a,g b] ]]) THEN
      REWRITE_TAC [SEGMENT_OPEN_SUBSET_CLOSED] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] SUBSET_TRANS)) THEN
      REWRITE_TAC [FRONTIER_SUBSET_EQ] THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MATCH_MP_TAC COMPACT_CONVEX_HULL THEN MATCH_MP_TAC COMPACT_PATH_IMAGE THEN
      ASM_SIMP_TAC [SIMPLE_PATH_IMP_PATH],
      TRANS_TAC SUBSET_TRANS ([[convex hull
       (IMAGE (g:real^1->real^2)
              (interval[vec 0,vec 1] DIFF interval(a,b)))]]) THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC [SUBSET_REFL], ALL_TAC] THEN
      MATCH_MP_TAC HULL_MONO THEN EXPAND_TAC "h" THEN
      REWRITE_TAC [path_image] THEN SET_TAC []])
  : ExceptT String IO thm).run
#eval STEP_LEMMA

#eval phrase 13
def ISOPERIMETRIC_CONVEXIFICATION : thm := keep "ISOPERIMETRIC_CONVEXIFICATION" fun _ => (do
  let h31 ← sr (← ExceptT.mk [[(!x. x IN k DIFF j ==> h x = g x)
      ==> IMAGE g (k DIFF j) SUBSET IMAGE h k]])
  let h30 ← sr (← ExceptT.mk [[(!x. x IN k /\ x IN j ==> ~(g x IN t))
      ==> DISJOINT (IMAGE g k DIFF IMAGE g (k DIFF j)) t]])
  let h29 ← sr (← ExceptT.mk [[p SUBSET c /\ DISJOINT (p DIFF q) f
      ==> p DIFF q SUBSET c DIFF f]])
  let h28 ← sr (← ExceptT.mk [[s = t ==> s SUBSET t]])
  let h27 ← sr (← ExceptT.mk [[c = {k n | n IN (:num)}
          ==> ~(?n. x IN k n) /\ (~(g(x) IN t) ==> x IN UNIONS c)
              ==> g x IN t]])
  let h26 ← tt (← ExceptT.mk [[(p ==> q) /\ p ==> p /\ q]])
  let h25 ← tt (← ExceptT.mk [[p /\ (p ==> q) ==> p /\ q]])
  let h24 ← tt (← ExceptT.mk [[p /\ (p ==> q) ==> p /\ q]])
  let h23 ← tt (← ExceptT.mk [[p /\ (p ==> q) ==> p /\ q]])
  let h22 ← tt (← ExceptT.mk [[p /\ (p ==> q) ==> p /\ q]])
  let h21 ← ms [LE_EXISTS] (← ExceptT.mk [[(!d:num. P(n + d)) ==> (!m. n <= m ==> P m)]])
  let h20 ← sr (← ExceptT.mk [[(!m. m < n ==> ~(k n SUBSET k m))
         ==> x IN k n /\
            (!s t. s IN {k n | n IN (:num)} /\
                       t IN {k n | n IN (:num)} /\
                       ~(s = t)
                       ==> DISJOINT s t)
            ==> ~(!m. m < n ==> ~(x IN k m)) ==> p]])
  let h19 ← sr (← ExceptT.mk [[(!m. m < n ==> ~(k n SUBSET k m))
          ==> (x IN UNIONS {k m | m < n}) /\
              (!s t. s IN {k n | n IN (:num)} /\
                     t IN {k n | n IN (:num)} /\
                     ~(s = t)
                     ==> DISJOINT s t)
              ==> ~(x IN k n)]])
  let h18 ← sr (← ExceptT.mk [[IMAGE f c SUBSET t
        ==> i SUBSET c ==> !x. x IN i ==> f x IN t]])
  let h17 ← sr (← ExceptT.mk [[{f x | x = a \/ P x} = (f a) INSERT {f x | P x}]])
  let h16 ← sr (← ExceptT.mk [[s = {k n | n IN (:num)}
        ==> IMAGE g (UNIONS s) INTER f = {}
            ==> IMAGE g (k n) INTER f = {}]])
  let h15 ← sr (← ExceptT.mk [[(!x. x IN s ==> h x = g x)
        ==> IMAGE g s INTER k = j
            ==> IMAGE h s INTER k = j]])
  let h14 ← sr (← ExceptT.mk [[(!m. m < n ==> ~(k n SUBSET k m))
        ==> x IN k n /\
            (!s t. s IN {k n | n IN (:num)} /\
                   t IN {k n | n IN (:num)} /\
                   ~(s = t)
                   ==> DISJOINT s t)
            ==> ~(?m. m < n /\ x IN k m)]])
  let h13 ← sr (← ExceptT.mk [[s = {i n | n IN (:num)} ==> ~(x IN UNIONS s)
        ==> ~(x IN UNIONS {i n | P n})]])
  let h12 ← tt (← ExceptT.mk [[~(p /\ q) <=> p ==> ~q]])
  let h11 ← sr (← ExceptT.mk [[x INSERT s = s <=> x IN s]])
  let h10 ← tt (← ExceptT.mk [[q /\ ~s /\ r /\ (~t ==> p) ==> (p ==> q ==> r ==> s) ==> t]])
  let h9 ← tt (← ExceptT.mk [[(p /\ q) /\ (p /\ q ==> r) ==> p /\ q /\ r]])
  let h8 ← sr (← ExceptT.mk [[s = IMAGE q UNIV
        ==> (!c. c IN s ==> c SUBSET t) ==> q n SUBSET t]])
  let h7 ← sr (← ExceptT.mk [[s = IMAGE q UNIV
        ==> (!c. c IN s ==> ~(c = {})) ==> !n. ~(q n = {})]])
  let h6 ← sr (← ExceptT.mk [[s = IMAGE q UNIV
          ==> UNIONS s SUBSET t
              ==> q n SUBSET t]])
  let h5 ← sr (← ExceptT.mk [[s = IMAGE q UNIV ==> ~(a IN UNIONS s) ==> ~(a IN q n)]])
  let h4 ← sr (← ExceptT.mk [[(~(a IN t) /\ ~(b IN t)) /\ t SUBSET s
            ==> t SUBSET s DIFF {a,b}]])
  let h3 ← sr (← ExceptT.mk [[s = IMAGE q UNIV
            ==> (!x. x IN s ==> connected x) ==> connected(q n)]])
  let h2 ← sr (← ExceptT.mk [[s = IMAGE q UNIV
            ==> (!x. x IN s ==> connected x) ==> connected(q n)]])
  let h1 ← sr (← ExceptT.mk [[{t | t IN k /\ g t IN UNIV DIFF f} = {}
        ==> IMAGE g k SUBSET f]])
  prove ([[!g:real^1->real^2.
        rectifiable_path g /\
        simple_path g /\
        pathfinish g = pathstart g
        ==> ?h:real^1->real^2.
                rectifiable_path h /\
                simple_path h /\
                pathfinish h = pathstart h /\
                path_length h <= path_length g /\
                convex hull (path_image h) = convex hull (path_image g) /\
                path_image h = frontier(convex hull (path_image g))]])
   (SUBGOAL_THEN ([[!g:real^1->real^2.
        rectifiable_path g /\
        simple_path g /\
        pathfinish g = pathstart g /\
        pathstart g IN frontier(convex hull (path_image g))
        ==> ?h:real^1->real^2.
                rectifiable_path h /\
                simple_path h /\
                pathfinish h = pathstart h /\
                path_length h <= path_length g /\
                convex hull (path_image h) = convex hull (path_image g) /\
                path_image h = frontier(convex hull (path_image g))]]) MP_TAC THENL
     [ALL_TAC,
      REPEAT STRIP_TAC THEN
      MP_TAC (← HolLight.ISPECL [([[path_image g:real^2->bool]]), ([[{}:real^2->bool]])] CONVEX_HULL_REDUNDANT_SUBSET) THEN
      REWRITE_TAC [EMPTY_SUBSET, DIFF_EMPTY, CONVEX_HULL_EMPTY] THEN
      REWRITE_TAC [CONVEX_HULL_EQ_EMPTY, PATH_IMAGE_NONEMPTY] THEN
      ASM_SIMP_TAC [COMPACT_PATH_IMAGE, SIMPLE_PATH_IMP_PATH] THEN
      REWRITE_TAC [SUBSET, NOT_FORALL_THM, NOT_IMP] THEN
      GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.BINDER_CONV o HolLight.LAND_CONV o HolLight.RAND_CONV) [path_image] THEN
      REWRITE_TAC [EXISTS_IN_IMAGE] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[t:real^1]]) STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[shiftpath t (g:real^1->real^2)]])) THEN
      ASM_SIMP_TAC [RECTIFIABLE_PATH_SHIFTPATH, SIMPLE_PATH_SHIFTPATH] THEN
      ASM_SIMP_TAC [PATH_LENGTH_SHIFTPATH, PATH_IMAGE_SHIFTPATH] THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [IN_INTERVAL_1, DROP_VEC]) THEN
      ASM_SIMP_TAC [PATHSTART_SHIFTPATH, PATHFINISH_SHIFTPATH] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [frontier, IN_DIFF] THEN
      MATCH_MP_TAC CLOSURE_INC THEN MATCH_MP_TAC HULL_INC THEN
      REWRITE_TAC [path_image, IN_INTERVAL_1, DROP_VEC, IN_IMAGE] THEN
      ASM_MESON_TAC []] THEN
    REPEAT STRIP_TAC THEN
    ABBREV_TAC ([[L = path_length(g:real^1->real^2)]]) THEN
    MP_TAC (← HolLight.ISPEC ([[g:real^1->real^2]]) ARC_LENGTH_REPARAMETRIZATION) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[g':real^1->real^2]]) (STRIP_ASSUME_TAC o HolLight.GSYM)) THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN ([[&0 <= L /\
    path_length g' = L /\
    simple_path(g':real^1->real^2) /\
    rectifiable_path(g':real^1->real^2) /\
    pathfinish g' = pathstart g' /\
    pathstart g' IN frontier(convex hull (path_image g')) /\
    (!x y. x IN interval[vec 0,vec 1] /\ y IN interval[vec 0,vec 1]
           ==> dist(g' x,g' y) <= L * dist(x,y))]]) MP_TAC THENL
     [ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC [PATH_LENGTH_POS_LE, SIMPLE_PATH_IMP_PATH],
      POP_ASSUM_LIST ((fun _ => ALL_TAC)) THEN
      SPEC_TAC (([[g':real^1->real^2]]), ([[g:real^1->real^2]]))] THEN
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC ([[(path_image g:real^2->bool) SUBSET frontier(convex hull path_image g)]]) THENL
     [EXISTS_TAC ([[g:real^1->real^2]]) THEN ASM_REWRITE_TAC [REAL_LE_REFL] THEN
      CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC lemma3 THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[?a b. (!n. a n IN interval[vec 0,vec 1]) /\
          (!n. b n IN interval[vec 0,vec 1]) /\
          (!n:num. drop(a n) <= drop(b n)) /\
          (!n. g(a n) IN frontier(convex hull (path_image g))) /\
          (!n. g(b n) IN frontier(convex hull (path_image g))) /\
          components
            {t | t IN interval[vec 0,vec 1] /\
                 (g:real^1->real^2) t IN
                 (:real^2) DIFF frontier(convex hull (path_image g))} =
          {interval(a n,b n) | n IN (:num)}]]) STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN ([[open_in (subtopology euclidean (interval[vec 0,vec 1]))
              {t | t IN interval[vec 0,vec 1] /\
                   (g:real^1->real^2) t IN
                   (:real^2) DIFF frontier(convex hull (path_image g))}]]) ASSUME_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN
        REWRITE_TAC [(← HolLight.GSYM closed), FRONTIER_CLOSED] THEN
        MATCH_MP_TAC LIPSCHITZ_IMP_CONTINUOUS_ON THEN
        REWRITE_TAC [(← HolLight.GSYM SessionMultiLib.Vectors.dist)] THEN ASM_MESON_TAC [],
        ALL_TAC] THEN
      ABBREV_TAC ([[s =
        {t | t IN interval[vec 0,vec 1] /\
             (g:real^1->real^2) t IN
             (:real^2) DIFF frontier(convex hull (path_image g))}]]) THEN
      ASM_CASES_TAC ([[s:real^1->bool = {}]]) THENL
       [UNDISCH_TAC ([[s:real^1->bool = {}]]) THEN EXPAND_TAC "s" THEN
        DISCH_THEN (MP_TAC o HolLight.MATCH_MP h1) THEN
        ASM_REWRITE_TAC [(← HolLight.GSYM path_image)],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[COUNTABLE(components(s:real^1->bool))]]) ASSUME_TAC THENL
       [EXPAND_TAC "s" THEN MATCH_MP_TAC COUNTABLE_COMPONENTS THEN
        MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN
        EXISTS_TAC ([[interval[vec 0:real^1,vec 1] ]]) THEN
        ASM_SIMP_TAC [CONVEX_IMP_LOCALLY_CONNECTED, CONVEX_INTERVAL],
        ALL_TAC] THEN
      MP_TAC (← HolLight.ISPEC ([[components(s:real^1->bool)]]) COUNTABLE_AS_IMAGE) THEN
      ASM_REWRITE_TAC [COMPONENTS_EQ_EMPTY] THEN
      DISCH_THEN (X_CHOOSE_TAC ([[q:num->real^1->bool]])) THEN
      SUBGOAL_THEN ([[!n:num. ?a b:real^1. q n = interval(a,b)]]) MP_TAC THENL
       [X_GEN_TAC ([[n:num]]) THEN
        MP_TAC (← HolLight.ISPEC ([[closure((q:num->real^1->bool) n)]]) CONNECTED_COMPACT_INTERVAL_1) THEN
        DISCH_THEN (MP_TAC o (Prod.fst : thm × thm → thm) o HolLight.EQ_IMP_RULE) THEN ANTS_TAC THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC CONNECTED_CLOSURE THEN
            FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h2) THEN
            REWRITE_TAC [IN_COMPONENTS_CONNECTED],
            REWRITE_TAC [COMPACT_EQ_BOUNDED_CLOSED, CLOSED_CLOSURE] THEN
            MATCH_MP_TAC BOUNDED_SUBSET THEN
            EXISTS_TAC ([[interval[vec 0:real^1,vec 1] ]]) THEN
            REWRITE_TAC [BOUNDED_INTERVAL] THEN
            MATCH_MP_TAC CLOSURE_MINIMAL THEN
            REWRITE_TAC [CLOSED_INTERVAL]],
          MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[a:real^1]]) THEN
          MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[b:real^1]]) THEN
          REWRITE_TAC [(← HolLight.GSYM INTERIOR_INTERVAL)] THEN
          DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN CONV_TAC HolLight.SYM_CONV THEN
          TRANS_TAC EQ_TRANS ([[interior((q:num->real^1->bool) n)]]) THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC CONVEX_INTERIOR_CLOSURE THEN
            REWRITE_TAC [CONVEX_CONNECTED_1] THEN
            FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h3) THEN
            REWRITE_TAC [IN_COMPONENTS_CONNECTED],
            ALL_TAC] THEN
          MATCH_MP_TAC INTERIOR_OPEN THEN MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
          EXISTS_TAC ([[interval(vec 0:real^1,vec 1)]]) THEN
          REWRITE_TAC [OPEN_INTERVAL] THEN
          MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
          EXISTS_TAC ([[interval[vec 0:real^1,vec 1] ]]) THEN
          REWRITE_TAC [INTERVAL_OPEN_SUBSET_CLOSED] THEN CONJ_TAC THENL
           [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC ([[s:real^1->bool]]) THEN
            CONJ_TAC THENL
             [MATCH_MP_TAC OPEN_IN_COMPONENTS_LOCALLY_CONNECTED THEN
              CONJ_TAC THENL [ALL_TAC, HolLight.ASM SET_TAC []] THEN
              MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN
              EXISTS_TAC ([[interval[vec 0:real^1,vec 1] ]]) THEN
              SIMP_TAC [CONVEX_IMP_LOCALLY_CONNECTED, CONVEX_INTERVAL],
              ALL_TAC] THEN
            EXPAND_TAC "s" THEN
            MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN
            ASM_SIMP_TAC [(← HolLight.GSYM path), RECTIFIABLE_PATH_IMP_PATH] THEN
            REWRITE_TAC [(← HolLight.GSYM closed), FRONTIER_CLOSED],
            REWRITE_TAC [OPEN_CLOSED_INTERVAL_1] THEN
            MATCH_MP_TAC h4 THEN
            CONJ_TAC THENL
             [CONJ_TAC THEN FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h5) THEN
              REWRITE_TAC [(← HolLight.GSYM UNIONS_COMPONENTS)] THEN EXPAND_TAC "s" THEN
              RULE_ASSUM_TAC (HolLight.REWRITE_RULE [pathstart, pathfinish]) THEN
              HolLight.ASM SET_TAC [],
              ALL_TAC]]] THEN
          FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h6) THEN
          REWRITE_TAC [(← HolLight.GSYM UNIONS_COMPONENTS)] THEN EXPAND_TAC "s" THEN
          REWRITE_TAC [SUBSET_RESTRICT],
        REWRITE_TAC [SKOLEM_THM]] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[a:num->real^1]]) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[b:num->real^1]]) THEN
      DISCH_TAC THEN
      SUBGOAL_THEN ([[!n. drop((a:num->real^1) n) < drop(b n)]]) ASSUME_TAC THENL
       [REWRITE_TAC [(← HolLight.GSYM INTERVAL_NE_EMPTY_1)] THEN
        FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC (HolLight.BINDER_CONV o HolLight.RAND_CONV o HolLight.LAND_CONV) [(← HolLight.GSYM th)])) THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h7) THEN
        REWRITE_TAC [IN_COMPONENTS_NONEMPTY],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[!n. interval((a:num->real^1) n,b n) SUBSET s]]) ASSUME_TAC THENL
       [GEN_TAC THEN
        FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM th)])) THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h8) THEN
        GEN_TAC THEN DISCH_THEN (MP_TAC o HolLight.MATCH_MP IN_COMPONENTS_SUBSET) THEN
        HolLight.ASM SET_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[!n. closure(interval((a:num->real^1) n,b n)) SUBSET interval[vec 0,vec 1] ]]) MP_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
        REWRITE_TAC [CLOSED_INTERVAL] THEN HolLight.ASM SET_TAC [],
        ASM_SIMP_TAC [CLOSURE_OPEN_INTERVAL, INTERVAL_NE_EMPTY_1] THEN
        DISCH_TAC] THEN
      ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC h9 THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC [SUBSET, ENDS_IN_INTERVAL, INTERVAL_NE_EMPTY_1,
                      REAL_LT_IMP_LE],
        STRIP_TAC] THEN
      ONCE_REWRITE_TAC [CONJ_ASSOC] THEN CONJ_TAC THENL
       [CONJ_TAC THEN X_GEN_TAC ([[n:num]]) THEN
        MP_TAC (← HolLight.ISPECL [([[s:real^1->bool]]), ([[interval((a:num->real^1) n,b n)]])] IN_COMPONENTS_MAXIMAL) THEN
        (DISCH_THEN (MP_TAC o (Prod.fst : thm × thm → thm) o HolLight.EQ_IMP_RULE) THEN ANTS_TAC THENL
          [ASM_REWRITE_TAC [IN_IMAGE, IN_UNIV] THEN MESON_TAC [],
           DISCH_THEN (MP_TAC o (HolCore.Lib.last (α := thm)) o HolLight.CONJUNCTS)]) THENL
         [DISCH_THEN (MP_TAC o HolLight.SPEC ([[(a:num->real^1) n INSERT interval(a n,b n)]])),
          DISCH_THEN (MP_TAC o HolLight.SPEC ([[(b:num->real^1) n INSERT interval(a n,b n)]]))] THEN
        REWRITE_TAC [NOT_INSERT_EMPTY, INSERT_SUBSET, IMP_CONJ] THEN
        (ANTS_TAC THENL [SET_TAC [], ALL_TAC]) THEN
        MATCH_MP_TAC h10 THEN
        REWRITE_TAC [h11, ENDS_IN_INTERVAL] THEN
        ASM_REWRITE_TAC [] THEN EXPAND_TAC "s" THEN
        SIMP_TAC [IN_ELIM_THM, IN_DIFF, IN_UNIV] THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
        EXISTS_TAC ([[interval((a:num->real^1) n,b n)]]) THEN
        ASM_SIMP_TAC [CLOSURE_INTERVAL, INTERVAL_EQ_EMPTY_1] THEN
        ASM_REWRITE_TAC [(← HolLight.GSYM REAL_NOT_LT), CONNECTED_INTERVAL] THEN
        REWRITE_TAC [INSERT_SUBSET, ENDS_IN_INTERVAL] THEN
        REWRITE_TAC [INTERVAL_OPEN_SUBSET_CLOSED, INTERVAL_NE_EMPTY_1] THEN
        ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN SET_TAC [],
        GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN
        REWRITE_TAC [IN_IMAGE, IN_ELIM_THM, IN_UNIV] THEN
        HolLight.ASM SET_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[?h. (!n. simple_path (h n) /\
             rectifiable_path (h n) /\
             pathstart (h n) = pathstart g /\
             pathfinish (h n) = pathfinish g /\
             convex hull path_image (h n) = convex hull path_image g /\
             (!x y.
                x IN interval [vec 0,vec 1] /\ y IN interval [vec 0,vec 1]
                ==> dist (h n x,h n y) <= L * dist (x,y)) /\
             (!x.
                x IN UNIONS {interval (a m,b m) | m < n}
                ==> h n x IN frontier (convex hull path_image g)) /\
             (!x. ~(x IN UNIONS {interval (a m,b m) | m < n})
                  ==> h n x = g x)) /\
        (!n x. ~(x IN interval(a n,b n) /\
                 !m. m < n ==> ~(x IN interval(a m,b m)))
               ==> (h:num->real^1->real^2)(SUC n) x = h n x)]]) MP_TAC THENL
     [MATCH_MP_TAC DEPENDENT_CHOICE THEN CONJ_TAC THENL
       [EXISTS_TAC ([[g:real^1->real^2]]) THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [LT] THEN SET_TAC [],
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [([[n:num]]), ([[h:real^1->real^2]])] THEN STRIP_TAC THEN
      ASM_CASES_TAC ([[interval(a n,b n) = {} \/
      ?m. m:num < n /\
          interval(a(n):real^1,b(n)) SUBSET interval(a m,b m)]]) THENL
       [SUBGOAL_THEN ([[UNIONS {interval(a m:real^1,b m) | m < SUC n} =
        UNIONS {interval(a m:real^1,b m) | m < n}]]) SUBST1_TAC THENL
         [REWRITE_TAC [LT, UNIONS_GSPEC] THEN HolLight.ASM SET_TAC [], ALL_TAC] THEN
        EXISTS_TAC ([[h:real^1->real^2]]) THEN ASM_REWRITE_TAC [],
        FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [DE_MORGAN_THM]) THEN
        REWRITE_TAC [INTERVAL_NE_EMPTY_1, NOT_EXISTS_THM] THEN
        REWRITE_TAC [h12] THEN STRIP_TAC] THEN
      MP_TAC (← HolLight.ISPECL [([[h:real^1->real^2]]), ([[(a:num->real^1) n]]), ([[(b:num->real^1) n]]),
        ([[L:real]])] STEP_LEMMA) THEN
      ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN ([[(h:real^1->real^2)(a(n:num)) = g(a n) /\
      (h:real^1->real^2)(b(n:num)) = g(b n)]]) STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h13) THEN
        REWRITE_TAC [UNIONS_INSERT, UNION_EMPTY, (← HolLight.GSYM UNIONS_COMPONENTS)] THEN
        HolLight.ASM SET_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[!x. x IN interval(a(n:num),b n) ==> (h:real^1->real^2) x = g x]]) ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC [UNIONS_GSPEC, IN_ELIM_THM] THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h14) THEN
        ASM_REWRITE_TAC [(← HolLight.GSYM pairwise)] THEN
        FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.SYM th)])) THEN
        REWRITE_TAC [PAIRWISE_INSERT, DISJOINT_EMPTY] THEN
        REWRITE_TAC [PAIRWISE_DISJOINT_COMPONENTS],
        ALL_TAC] THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [] THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h15) THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h16) THEN
        REWRITE_TAC [UNIONS_INSERT, UNION_EMPTY, (← HolLight.GSYM UNIONS_COMPONENTS)] THEN
        HolLight.ASM SET_TAC [],
        MATCH_MP_TAC MONO_EXISTS] THEN
      X_GEN_TAC ([[f:real^1->real^2]]) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [(← HolLight.GSYM CONJ_ASSOC)] THEN CONJ_TAC THENL
       [MATCH_MP_TAC LIPSCHITZ_IMP_RECTIFIABLE_PATH THEN
        REWRITE_TAC [(← HolLight.GSYM SessionMultiLib.Vectors.dist)] THEN ASM_MESON_TAC [],
        ALL_TAC] THEN
      REWRITE_TAC [LT, h17] THEN
      ASM_REWRITE_TAC [UNIONS_INSERT, FORALL_IN_UNION] THEN
      REWRITE_TAC [IN_UNION, DE_MORGAN_THM] THEN ASM_SIMP_TAC [] THEN
      REWRITE_TAC [(← HolLight.GSYM CONJ_ASSOC)] THEN REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h18) THEN
        REWRITE_TAC [INTERVAL_OPEN_SUBSET_CLOSED],
        X_GEN_TAC ([[x:real^1]]) THEN DISCH_TAC THEN
        SUBGOAL_THEN ([[(f:real^1->real^2) x = h x]]) (fun th => ASM_SIMP_TAC [th]) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h19) THEN
        ASM_REWRITE_TAC [(← HolLight.GSYM pairwise)] THEN
        FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.SYM th)])) THEN
        REWRITE_TAC [PAIRWISE_INSERT, DISJOINT_EMPTY] THEN
        REWRITE_TAC [PAIRWISE_DISJOINT_COMPONENTS],
        X_GEN_TAC ([[x:real^1]]) THEN
        ASM_CASES_TAC ([[x IN interval((a:num->real^1) n,b n)]]) THEN
        ASM_SIMP_TAC [] THEN FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h20) THEN
         ASM_REWRITE_TAC [(← HolLight.GSYM pairwise)] THEN
         FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.SYM th)])) THEN
         REWRITE_TAC [PAIRWISE_INSERT, DISJOINT_EMPTY] THEN
         REWRITE_TAC [PAIRWISE_DISJOINT_COMPONENTS]],
      REWRITE_TAC [SKOLEM_THM, FORALL_AND_THM]] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[f:num->real^1->real^2]]) STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN ([[!x. ?y. x IN interval[vec 0,vec 1]
            ==> eventually (\n. (f:num->real^1->real^2) n x = y) sequentially]]) MP_TAC THENL
     [X_GEN_TAC ([[x:real^1]]) THEN
      ASM_CASES_TAC ([[(x:real^1) IN interval[vec 0,vec 1] ]]) THEN
      ASM_REWRITE_TAC [] THEN
      ASM_CASES_TAC ([[(x:real^1) IN UNIONS {interval (a n,b n) | n IN (:num)}]]) THENL
       [ALL_TAC,
        EXISTS_TAC ([[(g:real^1->real^2) x]]) THEN
        REWRITE_TAC [EVENTUALLY_SEQUENTIALLY] THEN HolLight.ASM SET_TAC []] THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [IN_UNIONS]) THEN
      REWRITE_TAC [EXISTS_IN_GSPEC, IN_UNIV] THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [num_WOP] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[n:num]]) STRIP_ASSUME_TAC) THEN
      EXISTS_TAC ([[(f:num->real^1->real^2) (n + 1) x]]) THEN
      REWRITE_TAC [EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC ([[n + 1]]) THEN
      MATCH_MP_TAC h21 THEN
      INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES] THEN
      FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.SYM th)])) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC ([[n:num]]) o HolLight.CONJUNCT2) THEN
      ASM_REWRITE_TAC [] THEN ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [SKOLEM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC ([[h:real^1->real^2]]) THEN DISCH_THEN (LABEL_TAC "*") THEN
    SUBGOAL_THEN ([[!x y. x IN interval[vec 0,vec 1] /\ y IN interval[vec 0,vec 1]
          ==> dist((h:real^1->real^2) x,h y) <= L * dist(x,y)]]) ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN REMOVE_THEN "*" (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPEC ([[y:real^1]]) th) THEN MP_TAC (← HolLight.SPEC ([[x:real^1]]) th))) THEN
      ASM_REWRITE_TAC [IMP_IMP, (← HolLight.GSYM EVENTUALLY_AND)] THEN
      REWRITE_TAC [EVENTUALLY_SEQUENTIALLY] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[n:num]]) (MP_TAC o HolLight.SPEC ([[n:num]]))) THEN
      REWRITE_TAC [LE_REFL] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    MATCH_MP_TAC h22 THEN CONJ_TAC THENL
     [MATCH_MP_TAC LIPSCHITZ_IMP_RECTIFIABLE_PATH THEN
      REWRITE_TAC [(← HolLight.GSYM SessionMultiLib.Vectors.dist)] THEN ASM_MESON_TAC [],
      DISCH_TAC] THEN
    MATCH_MP_TAC h23 THEN CONJ_TAC THENL
     [ASM_SIMP_TAC [simple_path, RECTIFIABLE_PATH_IMP_PATH] THEN
      MAP_EVERY X_GEN_TAC [([[x:real^1]]), ([[y:real^1]])] THEN STRIP_TAC THEN
      REMOVE_THEN "*" (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPEC ([[y:real^1]]) th) THEN MP_TAC (← HolLight.SPEC ([[x:real^1]]) th))) THEN
      ASM_REWRITE_TAC [IMP_IMP, (← HolLight.GSYM EVENTUALLY_AND)] THEN
      REWRITE_TAC [EVENTUALLY_SEQUENTIALLY] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[n:num]]) (MP_TAC o HolLight.SPEC ([[n:num]]))) THEN
      REWRITE_TAC [LE_REFL] THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [simple_path]) THEN ASM_MESON_TAC [],
      DISCH_TAC] THEN
    MATCH_MP_TAC h24 THEN CONJ_TAC THENL
     [REMOVE_THEN "*" (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPEC ([[vec 0:real^1]]) th) THEN
         MP_TAC (← HolLight.SPEC ([[vec 1:real^1]]) th))) THEN
      REWRITE_TAC [ENDS_IN_UNIT_INTERVAL, IMP_IMP, (← HolLight.GSYM EVENTUALLY_AND)] THEN
      REWRITE_TAC [EVENTUALLY_SEQUENTIALLY] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[n:num]]) (MP_TAC o HolLight.SPEC ([[n:num]]))) THEN
      REWRITE_TAC [LE_REFL] THEN ASM_MESON_TAC [pathstart, pathfinish],
      DISCH_TAC] THEN
    MATCH_MP_TAC h25 THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC PATH_LENGTH_LIPSCHITZ THEN
      ASM_REWRITE_TAC [(← HolLight.GSYM SessionMultiLib.Vectors.dist)],
      DISCH_TAC] THEN
    MATCH_MP_TAC h26 THEN CONJ_TAC THENL
     [DISCH_THEN (fun th => HolLight.tactic_of do
        pure (SUBST1_TAC (← HolLight.SYM th) THEN ASSUME_TAC th)) THEN
      CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC lemma3 THEN ASM_REWRITE_TAC [] THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [path_image] THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN X_GEN_TAC ([[x:real^1]]) THEN
      DISCH_TAC THEN
      ASM_CASES_TAC ([[?n. x IN interval((a:num->real^1) n,b n)]]) THENL
       [FIRST_X_ASSUM (X_CHOOSE_TAC ([[n:num]])) THEN
        REMOVE_THEN "*" (MP_TAC o HolLight.SPEC ([[x:real^1]])) THEN
        ASM_REWRITE_TAC [EVENTUALLY_SEQUENTIALLY] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[N:num]]) (MP_TAC o HolLight.SPEC ([[N + SUC n]]))) THEN
        REWRITE_TAC [LE_ADD] THEN DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC [UNIONS_GSPEC, IN_ELIM_THM] THEN EXISTS_TAC ([[n:num]]) THEN
        ASM_REWRITE_TAC [] THEN ARITH_TAC,
        REMOVE_THEN "*" (MP_TAC o HolLight.SPEC ([[x:real^1]])) THEN
        ASM_REWRITE_TAC [EVENTUALLY_SEQUENTIALLY] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[n:num]]) (MP_TAC o HolLight.SPEC ([[n:num]]))) THEN
        REWRITE_TAC [LE_REFL] THEN DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN
        SUBGOAL_THEN ([[(f:num->real^1->real^2) n x = g x]]) SUBST1_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [UNIONS_GSPEC] THEN
          HolLight.ASM SET_TAC [],
          FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h27) THEN
          ASM_REWRITE_TAC [(← HolLight.GSYM UNIONS_COMPONENTS)] THEN HolLight.ASM SET_TAC []]],
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [CONVEX_CONVEX_HULL] THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [path_image] THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN X_GEN_TAC ([[x:real^1]]) THEN
      DISCH_TAC THEN
      REMOVE_THEN "*" (MP_TAC o HolLight.SPEC ([[x:real^1]])) THEN
      ASM_REWRITE_TAC [EVENTUALLY_SEQUENTIALLY] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[n:num]]) (MP_TAC o HolLight.SPEC ([[n:num]]))) THEN
      REWRITE_TAC [LE_REFL] THEN DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN
      SUBGOAL_THEN ([[convex hull path_image g =
      convex hull path_image((f:num->real^1->real^2) n)]]) SUBST1_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC [path_image] THEN HolLight.ASM SET_TAC [],
      ALL_TAC] THEN
    TRANS_TAC SUBSET_TRANS ([[convex hull IMAGE (g:real^1->real^2)
    (interval[vec 0,vec 1] DIFF UNIONS {interval(a n,b n) | n IN (:num)})]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC h28 THEN
      MATCH_MP_TAC CONVEX_HULL_REDUNDANT_SUBSET THEN
      ASM_SIMP_TAC [COMPACT_PATH_IMAGE, SIMPLE_PATH_IMP_PATH] THEN
      REWRITE_TAC [path_image] THEN CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN
      REWRITE_TAC [(← HolLight.GSYM SET_DIFF_FRONTIER)] THEN
      MATCH_MP_TAC h29 THEN
      REWRITE_TAC [HULL_SUBSET] THEN MATCH_MP_TAC h30 THEN
      X_GEN_TAC ([[x:real^1]]) THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      FIRST_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV o HolLight.RAND_CONV) [(← HolLight.SYM th)])) THEN
      REWRITE_TAC [(← HolLight.GSYM UNIONS_COMPONENTS), (← HolLight.GSYM path_image)] THEN HolLight.ASM SET_TAC [],
      MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC [path_image] THEN
      MATCH_MP_TAC h31 THEN
      X_GEN_TAC ([[x:real^1]]) THEN
      SIMP_TAC [UNIONS_GSPEC, IN_DIFF, NOT_EXISTS_THM, IN_ELIM_THM, IN_UNIV] THEN
      STRIP_TAC THEN REMOVE_THEN "*" (MP_TAC o HolLight.SPEC ([[x:real^1]])) THEN
      ASM_REWRITE_TAC [EVENTUALLY_SEQUENTIALLY] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[n:num]]) (MP_TAC o HolLight.SPEC ([[n:num]]))) THEN
      REWRITE_TAC [LE_REFL] THEN DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [UNIONS_GSPEC] THEN
      HolLight.ASM SET_TAC []])
  : ExceptT String IO thm).run
#eval ISOPERIMETRIC_CONVEXIFICATION

#eval phrase 14
def ISOPERIMETRIC_CONVEXIFICATION_1 : thm := keep "ISOPERIMETRIC_CONVEXIFICATION_1" fun _ => (do
  let h4 ← sr (← ExceptT.mk [[b SUBSET t ==> s INTER t = {} ==> DISJOINT b s]])
  let h3 ← sr (← ExceptT.mk [[DISJOINT s v /\ t SUBSET u ==> s INTER t SUBSET u DIFF v]])
  let h2 ← tt (← ExceptT.mk [[~p ==> p ==> F]])
  let h1 ← sr (← ExceptT.mk [[p SUBSET c /\ ~(p SUBSET f) ==> ~(p INTER (c DIFF f) = {})]])
  prove ([[!g:real^1->real^2.
        rectifiable_path g /\
        simple_path g /\
        pathfinish g = pathstart g /\
        ~convex(inside(path_image g))
        ==> ?h:real^1->real^2.
                rectifiable_path h /\
                simple_path h /\
                pathfinish h = pathstart h /\
                path_length h <= path_length g /\
                convex hull path_image h = convex hull path_image g /\
                path_image h = frontier (convex hull path_image g) /\
                measure(inside(path_image g)) < measure(inside(path_image h))]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPEC ([[g:real^1->real^2]]) ISOPERIMETRIC_CONVEXIFICATION) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC ([[h:real^1->real^2]]) THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [(← HolLight.GSYM REAL_SUB_LT)] THEN
    HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
        let x1 ← ec (HolCore.Kernel.rand w)
        let x2 ← ExceptT.mk (HolLight.PART_MATCH (HolCore.Kernel.rand o HolCore.Kernel.rand) MEASURE_DIFF_SUBSET x1)
        pure (MP_TAC x2)) THEN
    ANTS_TAC THENL [ALL_TAC, DISCH_THEN (SUBST1_TAC o HolLight.SYM)] THEN
    HolLight.ASM (gsimp 6) [MEASURABLE_INSIDE, COMPACT_PATH_IMAGE, SIMPLE_PATH_IMP_PATH,
      COMPACT_FRONTIER, COMPACT_CONVEX_HULL, INSIDE_FRONTIER_EQ_INTERIOR,
      CONVEX_CONVEX_HULL, BOUNDED_CONVEX_HULL, BOUNDED_PATH_IMAGE,
      SIMPLE_PATH_IMP_PATH, MEASURABLE_MEASURE_POS_LT, MEASURABLE_DIFF,
      MEASURABLE_INTERIOR] THEN
    REWRITE_TAC [INSIDE_SUBSET_INTERIOR_CONVEX_HULL] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP NEGLIGIBLE_EMPTY_INTERIOR) THEN
    SUBGOAL_THEN ([[~(path_image g INTER interior(convex hull path_image g):real^2->bool = {})]]) MP_TAC THENL
     [REWRITE_TAC [(← HolLight.GSYM SET_DIFF_FRONTIER)] THEN MATCH_MP_TAC h1 THEN
      REWRITE_TAC [HULL_SUBSET] THEN DISCH_TAC THEN
      MP_TAC (← HolLight.ISPEC ([[g:real^1->real^2]]) lemma3) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST_ALL_TAC o HolLight.SYM) THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h2) THEN
      HolLight.ASM (gsimp 4) [INSIDE_FRONTIER_EQ_INTERIOR, CONVEX_CONVEX_HULL, BOUNDED_CONVEX_HULL,
        BOUNDED_PATH_IMAGE, SIMPLE_PATH_IMP_PATH, CONVEX_INTERIOR],
      ALL_TAC] THEN
    REWRITE_TAC [(← HolLight.GSYM MEMBER_NOT_EMPTY), IN_INTER, IN_INTERIOR] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[x:real^2]]) (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[e:real]]) STRIP_ASSUME_TAC) THEN
    MP_TAC (← HolLight.ISPEC ([[g:real^1->real^2]]) JORDAN_INSIDE_OUTSIDE) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o (HolCore.Lib.last (α := thm)) o HolLight.CONJUNCTS) THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [EXTENSION] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[x:real^2]])) THEN
    ASM_REWRITE_TAC [FRONTIER_STRADDLE] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[e / &2]])) THEN ASM_REWRITE_TAC [REAL_HALF] THEN
    DISCH_THEN (MP_TAC o HolLight.CONJUNCT1) THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC ([[y:real^2]]) THEN STRIP_TAC THEN
    MP_TAC (← HolLight.ISPEC ([[path_image g:real^2->bool]]) OPEN_OUTSIDE) THEN
    ASM_SIMP_TAC [CLOSED_PATH_IMAGE, SIMPLE_PATH_IMP_PATH] THEN
    REWRITE_TAC [OPEN_CONTAINS_BALL] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[y:real^2]])) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[d:real]]) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC ([[min d (e / &2)]]) THEN
    ASM_REWRITE_TAC [REAL_LT_MIN, BALL_MIN_INTER, REAL_HALF] THEN
    MATCH_MP_TAC h3 THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h4) THEN
      REWRITE_TAC [INSIDE_INTER_OUTSIDE],
      MATCH_MP_TAC INTERIOR_MAXIMAL THEN REWRITE_TAC [OPEN_BALL] THEN
      TRANS_TAC SUBSET_TRANS ([[ball(x:real^2,e)]]) THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC ([[dist(x:real^2,y) < e / &2]]) THEN
      REWRITE_TAC [SUBSET, IN_BALL] THEN CONV_TAC na])
  : ExceptT String IO thm).run
#eval ISOPERIMETRIC_CONVEXIFICATION_1

/- ------------------------------------------------------------------------- -/
/- The grand finale.                                                         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 15
def ISOPERIMETRIC_THEOREM : thm := keep "ISOPERIMETRIC_THEOREM" fun _ => (do
  let h4 ← rr (← ExceptT.mk [[&0 <= x /\ x <= y ==> abs x <= abs y]])
  let h3 ← rr (← ExceptT.mk [[&0 < &4 * x <=> &0 < x]])
  let h2 ← rr (← ExceptT.mk [[g:real < h /\ m <= l ==> h <= m ==> g < l]])
  let h1 ← tt (← ExceptT.mk [[(p ==> q /\ ~r) ==> (p /\ s ==> q /\ (r ==> t))]])
  prove ([[!L g:real^1->real^2.
        rectifiable_path g /\
        simple_path g /\
        pathfinish g = pathstart g /\
        path_length g = L
        ==> measure(inside(path_image g)) <= L pow 2 / (&4 * pi) /\
            (measure(inside(path_image g)) =  L pow 2 / (&4 * pi)
             ==> ?a r. path_image g = sphere(a,r))]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o HolLight.MATCH_MP SIMPLE_PATH_IMP_PATH) THEN
    ASM_CASES_TAC ([[convex(inside(path_image g):real^2->bool)]]) THENL
     [ASM_MESON_TAC [ISOPERIMETRIC_THEOREM_CONVEX], ALL_TAC] THEN
    MP_TAC (← HolLight.SPEC ([[g:real^1->real^2]]) ISOPERIMETRIC_CONVEXIFICATION_1) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[h:real^1->real^2]]) STRIP_ASSUME_TAC) THEN
    MP_TAC (← HolLight.SPECL [([[path_length(h:real^1->real^2)]]), ([[h:real^1->real^2]])] ISOPERIMETRIC_THEOREM_CONVEX) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC [INSIDE_FRONTIER_EQ_INTERIOR, CONVEX_CONVEX_HULL,
                   BOUNDED_CONVEX_HULL, BOUNDED_PATH_IMAGE, CONVEX_INTERIOR],
      MATCH_MP_TAC h1 THEN
      REWRITE_TAC [(← HolLight.GSYM REAL_LT_LE)] THEN MATCH_MP_TAC h2 THEN
      ASM_SIMP_TAC [REAL_LE_DIV2_EQ, PI_POS,
                   h3] THEN
      REWRITE_TAC [(← HolLight.GSYM REAL_LE_SQUARE_ABS)] THEN
      MATCH_MP_TAC h4 THEN
      ASM_SIMP_TAC [PATH_LENGTH_POS_LE]])
  : ExceptT String IO thm).run
#eval ISOPERIMETRIC_THEOREM

end Hol100.Isoperimetric
