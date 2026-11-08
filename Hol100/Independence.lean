/- File: Hol100/Independence.lean
Translation of HOL Light's 100/independence.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionMultiLib.Cauchy
import SessionMultiLib.Tarski
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Binomial SessionLibrary.Iter SessionLibrary.Floor SessionLibrary.Wo SessionLibrary.Permutations SessionLibrary.Products SessionLibrary.Frag SessionLibrary.Prime SessionLibrary.Card SessionLibrary.Matroids SessionMultiLib.Misc SessionLibrary.GroupTheory SessionMultiLib.Vectors SessionMultiLib.Metric SessionMultiLib.Determinants SessionMultiLib.Homology SessionMultiLib.Topology SessionMultiLib.Convex SessionMultiLib.Tarski SessionMultiLib.ComplexAlgebra SessionMultiLib.Complexes SessionMultiLib.Paths SessionMultiLib.Polytope SessionMultiLib.Degree SessionMultiLib.Derivatives SessionMultiLib.Integration SessionMultiLib.Measure SessionMultiLib.Canal SessionMultiLib.Transcendentals SessionMultiLib.RealAnalysis SessionMultiLib.MoreTop SessionMultiLib.Cauchy
namespace Hol100.Independence

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
/-- Run an `IO (Except String α)` once, caching under `name` (OCaml's `let`
    evaluates its right-hand side once), for the `let X,Y,Z = e` bindings
    whose result is a tuple. -/
private def keepIO {α : Type} [Inhabited α] (name : String) (f : Unit → IO (Except String α)) : α :=
  keep name fun _ =>
    match runIO (f ()) with
    | .ok (.ok v) => v
    | .ok (.error e) => panic! s!"keepIO {name}: {e}"
    | .error e => panic! s!"keepIO {name}: {e}"
private def cf (tm : term) : ExceptT String IO thm := ExceptT.mk (COMPLEX_FIELD tm)
private def cr (tm : term) : ExceptT String IO thm := ExceptT.mk (COMPLEX_RING tm)
private def ms (ths : List thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (MESON ths tm)
private def na (tm : term) : ExceptT String IO thm := ExceptT.mk (NORM_ARITH tm)
private def rf (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_FIELD tm)
private def rg (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_RING tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)
private def va (tm : term) : ExceptT String IO thm := ExceptT.mk (VECTOR_ARITH tm)

/- ========================================================================= -/
/- Independence of the parallel postulate. The statement and some ideas are  -/
/- taken from Tim Makarios's MSc thesis "A mechanical verification of the    -/
/- independence of Tarski's Euclidean axiom".                                -/
/-                                                                           -/
/- In the file Multivariate/tarski.ml it is shown that all 11 of Tarski's    -/
/- axioms for geometry hold for the Euclidean plane `:real^2`, with          -/
/- betweenness and congruence of segments as:                                -/
/-                                                                           -/
/-      B x y z  <=> between y (x,z)                                         -/
/-      ab == pq <=> dist(a,b) = dist(p,q)                                   -/
/-                                                                           -/
/- The present file shows that the Klein model of the hyperbolic plane (type -/
/- `:plane`) satisfies all Tarski's axioms except that it satisfies the      -/
/- negation of the Euclidean axiom (10), with betweenness and congruence of  -/
/- segments as:                                                              -/
/-                                                                           -/
/-      B x y z  <=> pbetween y (x,z)                                        -/
/-      ab == pq <=> pdist(a,b) = pdist(p,q)                                 -/
/-                                                                           -/
/- Collectively, these two results show that the Euclidean axiom is          -/
/- independent of the others. For more references regarding Tarski's axioms  -/
/- for geometry see "http://en.wikipedia.org/wiki/Tarski's_axioms".          -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Multivariate/cauchy.ml";;
#eval SessionMultiLib.Cauchy.ensureCauchy

#eval phrase 2
-- needs "Multivariate/tarski.ml";;
#eval SessionMultiLib.Tarski.ensureTarski

/- ------------------------------------------------------------------------- -/
/- The semimetric we will use, directly on real^N first. Choose a sensible   -/
/- default outside unit ball so some handy theorems become unconditional.    -/
/- ------------------------------------------------------------------------- -/

#eval phrase 3
def ddist : thm := keep "ddist" fun _ => new_definition
 [[ddist(x:real^N,y:real^N) =
    if norm(x) < &1 /\ norm(y) < &1 then
     (&1 - x dot y) pow 2 / ((&1 - norm(x) pow 2) * (&1 - norm(y) pow 2)) - &1
    else dist(x,y)]]
#eval ddist

#eval phrase 4
def DDIST_INCREASES_ONLINE : thm := keep "DDIST_INCREASES_ONLINE" fun _ => (do
  let h8 ← rr (← ExceptT.mk [[(&1 - (a + x * b)) pow 2 * (&1 - (a + &2 * b + c)) <
    (&1 - (a + b)) pow 2 * (&1 - (a + &2 * x * b + x * x * c)) <=>
    &0 < (&1 - a - b * x) * ((&1 - a) * c + b pow 2) * (&1 - x) +
         (&1 - a - b) * ((&1 - a) * c + b pow 2) * (&1 - x) * x]])
  let h7 ← va (← ExceptT.mk [[(a + b:real^N) dot (a + b) = a dot a + &2 * a dot b + b dot b]])
  let h6 ← va (← ExceptT.mk [[a + c:real^N = a <=> c = vec 0]])
  let h5 ← va (← ExceptT.mk [[(&1 - u) % a + u % b:real^N = a + u % (b - a)]])
  let h4 ← va (← ExceptT.mk [[(&1 - &1) % a + &1 % b:real^N = b]])
  let h3 ← ms [REAL_LET_TRANS, NORM_CAUCHY_SCHWARZ] (← ExceptT.mk [[norm(x) * norm(y) < &1 ==> (x:real^N) dot y < &1]])
  let h2 ← rr (← ExceptT.mk [[(a * inv b) * c:real = (a * c) / b]])
  let h1 ← rr (← ExceptT.mk [[a * inv x * inv b - &1 < c * inv x * d - &1 <=>
                          (a / b) / x < (c * d) / x]])
  prove ([[!a b x:real^N.
      norm a < &1 /\ norm b < &1 /\ norm x < &1 /\ between x (a,b) /\ ~(x = b)
      ==> ddist(a,x) < ddist(a,b)]])
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC ([[b:real^N = a]]) THENL
     [ASM_MESON_TAC [BETWEEN_REFL_EQ], ALL_TAC] THEN
    ASM_SIMP_TAC [ddist, real_div, REAL_INV_MUL] THEN
    SUBGOAL_THEN ([[norm(a:real^N) pow 2 < &1 /\ norm(b:real^N) pow 2 < &1 /\
    norm(x:real^N) pow 2 < &1]]) MP_TAC THENL [ASM_SIMP_TAC [ABS_SQUARE_LT_1, REAL_ABS_NORM], ALL_TAC] THEN
    REWRITE_TAC [h1] THEN
    SIMP_TAC [REAL_LT_DIV2_EQ, REAL_LT_LDIV_EQ, REAL_SUB_LT] THEN
    ONCE_REWRITE_TAC [h2] THEN
    SIMP_TAC [REAL_LT_RDIV_EQ, REAL_SUB_LT] THEN
    SUBGOAL_THEN ([[(a:real^N) dot b < &1 /\ (a:real^N) dot x < &1]]) MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC h3 THEN
      GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.GSYM REAL_MUL_LID)] THEN
      MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REWRITE_TAC [NORM_POS_LE],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [BETWEEN_IN_SEGMENT]) THEN
    REWRITE_TAC [IN_SEGMENT, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC ([[u:real]]) THEN
    ASM_CASES_TAC ([[u = &1]]) THEN
    ASM_SIMP_TAC [h4] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    SIMP_TAC [h5] THEN
    ABBREV_TAC ([[c:real^N = b - a]]) THEN
    SUBGOAL_THEN ([[b:real^N = a + c]]) SUBST_ALL_TAC THENL
     [EXPAND_TAC "c" THEN VECTOR_ARITH_TAC, ALL_TAC] THEN
    RULE_ASSUM_TAC (Session.SIMP_RULE [h6]) THEN
    REWRITE_TAC [NORM_POW_2, h7] THEN
    REWRITE_TAC [DOT_RADD, DOT_RMUL] THEN REWRITE_TAC [DOT_LMUL] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [h8] THEN
    MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
     [REPEAT (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC),
      REPEAT (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC)] THEN
    TRY ASM_REAL_ARITH_TAC THEN TRY (MATCH_MP_TAC REAL_LT_IMP_LE) THEN
    MATCH_MP_TAC REAL_LTE_ADD THEN REWRITE_TAC [REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC [DOT_POS_LT, REAL_SUB_LT])
  : ExceptT String IO thm).run
#eval DDIST_INCREASES_ONLINE

#eval phrase 5
def DDIST_REFL : thm := keep "DDIST_REFL" fun _ => (do
  prove ([[!x:real^N. ddist(x,x) = &0]])
   (GEN_TAC THEN REWRITE_TAC [ddist, SessionMultiLib.Vectors.DIST_REFL, NORM_POW_2, NORM_LT_SQUARE] THEN
    CONV_TAC REAL_FIELD)
  : ExceptT String IO thm).run
#eval DDIST_REFL

#eval phrase 6
def DDIST_SYM : thm := keep "DDIST_SYM" fun _ => (do
  prove ([[!x y:real^N. ddist(x,y) = ddist(y,x)]])
   (REWRITE_TAC [ddist, CONJ_ACI, REAL_MUL_AC, SessionMultiLib.Vectors.DIST_SYM, DOT_SYM])
  : ExceptT String IO thm).run
#eval DDIST_SYM

#eval phrase 7
def DDIST_POS_LT : thm := keep "DDIST_POS_LT" fun _ => (do
  prove ([[!x y:real^N. ~(x = y) ==> &0 < ddist(x,y)]])
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC ([[norm(x:real^N) < &1 /\ norm(y:real^N) < &1]]) THENL
     [ASM_MESON_TAC [DDIST_INCREASES_ONLINE, DDIST_REFL, BETWEEN_REFL],
      ASM_SIMP_TAC [ddist, DIST_POS_LT]])
  : ExceptT String IO thm).run
#eval DDIST_POS_LT

#eval phrase 8
def DDIST_POS_LE : thm := keep "DDIST_POS_LE" fun _ => (do
  prove ([[!x y:real^N. &0 <= ddist(x,y)]])
   (REPEAT GEN_TAC THEN ASM_CASES_TAC ([[x:real^N = y]]) THEN
    ASM_SIMP_TAC [DDIST_REFL, DDIST_POS_LT, REAL_LE_LT])
  : ExceptT String IO thm).run
#eval DDIST_POS_LE

#eval phrase 9
def DDIST_EQ_0 : thm := keep "DDIST_EQ_0" fun _ => (do
  prove ([[!x y:real^N. ddist(x,y) = &0 <=> x = y]])
   (MESON_TAC [DDIST_REFL, DDIST_POS_LT, REAL_LT_REFL])
  : ExceptT String IO thm).run
#eval DDIST_EQ_0

#eval phrase 10
def BETWEEN_COLLINEAR_DDIST_EQ : thm := keep "BETWEEN_COLLINEAR_DDIST_EQ" fun _ => (do
  prove ([[!a b x:real^N.
        norm(a) < &1 /\ norm(b) < &1 /\ norm(x) < &1
        ==> (between x (a,b) <=>
             collinear {a, x, b} /\
             ddist(x,a) <= ddist (a,b) /\ ddist(x,b) <= ddist(a,b))]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL
     [SIMP_TAC [BETWEEN_IMP_COLLINEAR],
      REWRITE_TAC [COLLINEAR_BETWEEN_CASES]] THEN
    ASM_MESON_TAC [DDIST_INCREASES_ONLINE, DDIST_SYM, REAL_LT_IMP_LE,
                  REAL_LE_REFL, BETWEEN_SYM, REAL_NOT_LE, BETWEEN_REFL])
  : ExceptT String IO thm).run
#eval BETWEEN_COLLINEAR_DDIST_EQ

#eval phrase 11
def CONTINUOUS_AT_LIFT_DDIST : thm := keep "CONTINUOUS_AT_LIFT_DDIST" fun _ => (do
  let h2 ← rr (← ExceptT.mk [[x < &1 * &1 ==> ~(&1 - x = &0)]])
  let h1 ← na (← ExceptT.mk [[dist(y,x) < &1 - norm x ==> norm y < &1]])
  prove ([[!a x:real^N.
      norm(a) < &1 /\ norm(x) < &1 ==> (\x. lift(ddist(a,x))) continuous at x]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN EXISTS_TAC ([[\x:real^N. lift((&1 - a dot x) pow 2 /
                    ((&1 - norm a pow 2) * (&1 - norm x pow 2)) - &1)]]) THEN
    EXISTS_TAC ([[&1 - norm(x:real^N)]]) THEN ASM_REWRITE_TAC [REAL_SUB_LT] THEN
    CONJ_TAC THENL
     [X_GEN_TAC ([[y:real^N]]) THEN DISCH_THEN (MP_TAC o HolLight.MATCH_MP h1) THEN ASM_SIMP_TAC [ddist],
      REWRITE_TAC [LIFT_SUB, real_div, LIFT_CMUL, REAL_INV_MUL] THEN
      MATCH_MP_TAC CONTINUOUS_SUB THEN SIMP_TAC [CONTINUOUS_CONST] THEN
      REPEAT (MATCH_MP_TAC CONTINUOUS_MUL THEN CONJ_TAC) THEN
      SIMP_TAC [CONTINUOUS_CONST, o_DEF, REAL_POW_2, LIFT_CMUL] THENL
       [MATCH_MP_TAC (← HolLight.REWRITE_RULE [o_DEF] CONTINUOUS_MUL),
        MATCH_MP_TAC (← HolLight.REWRITE_RULE [o_DEF] CONTINUOUS_AT_INV)] THEN
      ASM_SIMP_TAC [h2, REAL_LT_MUL2,
                   NORM_POS_LE, LIFT_SUB] THEN
      SIMP_TAC [(← HolLight.GSYM REAL_POW_2), NORM_POW_2, CONTINUOUS_CONST, CONTINUOUS_AT_ID,
               CONTINUOUS_SUB, CONTINUOUS_LIFT_DOT2]])
  : ExceptT String IO thm).run
#eval CONTINUOUS_AT_LIFT_DDIST

#eval phrase 12
def HYPERBOLIC_MIDPOINT : thm := keep "HYPERBOLIC_MIDPOINT" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[&0 - x <= &0 <=> &0 <= x]])
  prove ([[!a b:real^N.
        norm a < &1 /\ norm b < &1
        ==> ?x. between x (a,b) /\ ddist(x,a) = ddist(x,b)]])
   (REPEAT STRIP_TAC THEN MP_TAC (← HolLight.ISPECL [([[\x:real^N. lift(ddist(x,a) - ddist(x,b))]]), ([[segment[a:real^N,b] ]])] CONNECTED_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC [CONNECTED_SEGMENT, LIFT_SUB] THEN
      MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC CONTINUOUS_SUB THEN ONCE_REWRITE_TAC [DDIST_SYM] THEN
      CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_LIFT_DDIST THEN
      ASM_MESON_TAC [BETWEEN_NORM_LT, BETWEEN_IN_SEGMENT],
      REWRITE_TAC [(← HolLight.GSYM IS_INTERVAL_CONNECTED_1), IS_INTERVAL_1] THEN
      REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_IMAGE] THEN
      REWRITE_TAC [IMP_IMP, RIGHT_IMP_FORALL_THM, LIFT_DROP] THEN
      DISCH_THEN (MP_TAC o HolLight.SPECL [([[a:real^N]]), ([[b:real^N]]), ([[lift(&0)]])]) THEN
      ASM_SIMP_TAC [DDIST_REFL, LIFT_DROP, ENDS_IN_SEGMENT, IN_IMAGE] THEN
      REWRITE_TAC [REAL_SUB_RZERO, h1] THEN
      ASM_SIMP_TAC [DDIST_POS_LE, LIFT_EQ, BETWEEN_IN_SEGMENT] THEN
      ASM_MESON_TAC [REAL_SUB_0, DDIST_SYM]])
  : ExceptT String IO thm).run
#eval HYPERBOLIC_MIDPOINT

#eval phrase 13
def DDIST_EQ_ORIGIN : thm := keep "DDIST_EQ_ORIGIN" fun _ => (do
  let h2 ← rr (← ExceptT.mk [[&1 - x = &1 - y <=> x = y]])
  let h1 ← rr (← ExceptT.mk [[x - &1 = y - &1 <=> x = y]])
  prove ([[!x:real^N y:real^N.
        norm x < &1 /\ norm y < &1
        ==> (ddist(vec 0,x) = ddist(vec 0,y) <=> norm x = norm y)]])
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [ddist, NORM_0, REAL_LT_01] THEN
    REWRITE_TAC [DOT_LZERO] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC [real_div, REAL_MUL_LID, REAL_EQ_INV2,
                h1] THEN
    REWRITE_TAC [h2,
                (← HolLight.GSYM REAL_EQ_SQUARE_ABS), REAL_ABS_NORM])
  : ExceptT String IO thm).run
#eval DDIST_EQ_ORIGIN

#eval phrase 14
def DDIST_CONGRUENT_TRIPLES_0 : thm := keep "DDIST_CONGRUENT_TRIPLES_0" fun _ => (do
  let h3 ← ms [NORM_CAUCHY_SCHWARZ, REAL_LET_TRANS, NORM_POS_LE,
                       REAL_LT_MUL2, REAL_MUL_RID, REAL_LT_IMP_LE] (← ExceptT.mk [[norm x < &1 /\ norm y < &1 ==> x dot y < &1]])
  let h2 ← rg (← ExceptT.mk [[x * a * b - &1 = y * a * b - &1 <=> x = y \/ a = &0 \/ b = &0]])
  let h1 ← tt (← ExceptT.mk [[(a /\ b ==> (x <=> y)) ==> (a /\ x /\ b <=> a /\ y /\ b)]])
  prove ([[!a b:real^N a' b':real^N.
        norm a < &1 /\ norm b < &1 /\ norm a' < &1 /\ norm b' < &1
        ==> (ddist(vec 0,a) = ddist(vec 0,a') /\ ddist(a,b) = ddist(a',b') /\
             ddist(b,vec 0) = ddist(b',vec 0) <=>
             dist(vec 0,a) = dist(vec 0,a') /\ dist(a,b) = dist(a',b') /\
             dist(b,vec 0) = dist(b',vec 0))]])
   (REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [DDIST_EQ_ORIGIN, (← HolLight.REWRITE_RULE [DDIST_SYM] DDIST_EQ_ORIGIN)] THEN
    REWRITE_TAC [DIST_0, NORM_0, REAL_LT_01] THEN MATCH_MP_TAC h1 THEN
    STRIP_TAC THEN ASM_SIMP_TAC [ddist, DIST_EQ, real_div, REAL_INV_MUL, h2] THEN
    REWRITE_TAC [SessionMultiLib.Vectors.dist, NORM_POW_2, DOT_LSUB, DOT_RSUB, DOT_SYM] THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_EQ_SQUARE_ABS), NORM_POW_2] THEN
    ASM_SIMP_TAC [REAL_INV_EQ_0, real_abs, REAL_SUB_LE, REAL_SUB_0] THEN
    ASM_SIMP_TAC [ABS_SQUARE_LT_1, REAL_ABS_NORM, REAL_LT_IMP_NE, REAL_LT_IMP_LE,
                 h3] THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [NORM_EQ]) THEN ASM_REAL_ARITH_TAC)
  : ExceptT String IO thm).run
#eval DDIST_CONGRUENT_TRIPLES_0

/- ------------------------------------------------------------------------- -/
/- Deduce existence of hyperbolic translations via the Poincare disc model.  -/
/- Use orthogonal projection onto a hemisphere touching the unit disc,       -/
/- then stereographic projection back from the other pole of the sphere plus -/
/- scaling. See Greenberg's "Euclidean & Non-Euclidean Geometries" fig 7.13. -/
/- ------------------------------------------------------------------------- -/

#eval phrase 15
def kleinify : thm := keep "kleinify" fun _ => new_definition
 [[kleinify z = Cx(&2 / (&1 + norm(z) pow 2)) * z]]
#eval kleinify

#eval phrase 16
def poincarify : thm := keep "poincarify" fun _ => new_definition
 [[poincarify x = Cx((&1 - sqrt(&1 - norm(x) pow 2)) / norm(x) pow 2) * x]]
#eval poincarify

#eval phrase 17
-- let KLEINIFY_0, POINCARIFY_0 = (CONJ_PAIR o prove) ...
def KLEINIFY_0_POINCARIFY_0_THMS : List thm := keepIO "KLEINIFY_0_POINCARIFY_0_THMS" fun _ => (do
  let th ← prove ([[kleinify (Cx(&0)) = Cx(&0) /\ poincarify (Cx(&0)) = Cx(&0)]])
   (REWRITE_TAC [kleinify, poincarify, COMPLEX_MUL_RZERO])
  let p ← HolLight.CONJ_PAIR th
  pure [p.1, p.2]
  : ExceptT String IO (List thm)).run
def KLEINIFY_0 : thm := KLEINIFY_0_POINCARIFY_0_THMS[0]!
def POINCARIFY_0 : thm := KLEINIFY_0_POINCARIFY_0_THMS[1]!
#eval do IO.println (repr KLEINIFY_0); IO.println (repr POINCARIFY_0)

#eval phrase 18
def NORM_KLEINIFY : thm := keep "NORM_KLEINIFY" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[&0 <= x ==> abs(&1 + x) = &1 + x]])
  prove ([[!z. norm(kleinify z) = (&2 * norm(z)) / (&1 + norm(z) pow 2)]])
   (REWRITE_TAC [kleinify, COMPLEX_NORM_MUL, COMPLEX_NORM_CX, REAL_ABS_DIV] THEN
    SIMP_TAC [REAL_LE_POW_2, h1] THEN
    REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval NORM_KLEINIFY

#eval phrase 19
def NORM_KLEINIFY_LT : thm := keep "NORM_KLEINIFY_LT" fun _ => (do
  let h2 ← rr (← ExceptT.mk [[&2 * z < (&1 + z pow 2) <=> &0 < (z - &1) pow 2]])
  let h1 ← rr (← ExceptT.mk [[&0 <= x ==> &0 < &1 + x]])
  prove ([[!z. norm(kleinify z) < &1 <=> ~(norm z = &1)]])
   (ASM_SIMP_TAC [NORM_KLEINIFY, REAL_LE_POW_2, REAL_LT_LDIV_EQ, REAL_MUL_LID,
                  h1] THEN
    SIMP_TAC [h2] THEN
    REWRITE_TAC [REAL_POW_2, REAL_LT_SQUARE] THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval NORM_KLEINIFY_LT

#eval phrase 20
def NORM_POINCARIFY_LT : thm := keep "NORM_POINCARIFY_LT" fun _ => (do
  let h4 ← rr (← ExceptT.mk [[&1 - x <= &1 <=> &0 <= x]])
  let h3 ← rr (← ExceptT.mk [[(&1 - x) pow 2 <= &1 - x <=> &0 <= x * (&1 - x)]])
  let h2 ← rr (← ExceptT.mk [[s <= &1 /\ &1 - x <= s ==> abs(&1 - s) <= x]])
  let h1 ← rr (← ExceptT.mk [[x * y <= &1 * y /\ y < &1 ==> x * y < &1]])
  prove ([[!x. norm(x) < &1 ==> norm(poincarify x) < &1]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [poincarify, COMPLEX_NORM_MUL] THEN
    MATCH_MP_TAC h1 THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC [NORM_POS_LE, COMPLEX_NORM_MUL, COMPLEX_NORM_CX] THEN
    REWRITE_TAC [REAL_ABS_DIV, REAL_ABS_NORM, REAL_ABS_POW] THEN
    ASM_CASES_TAC ([[x:real^2 = vec 0]]) THEN
    ASM_SIMP_TAC [REAL_LE_LDIV_EQ, NORM_POS_LT, REAL_POW_LT, NORM_0] THENL
     [REAL_ARITH_TAC2, REWRITE_TAC [REAL_MUL_LID]] THEN
    MATCH_MP_TAC h2 THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LSQRT, MATCH_MP_TAC REAL_LE_RSQRT] THEN
    REWRITE_TAC [REAL_SUB_LE, REAL_POS, REAL_MUL_LID, REAL_POW_ONE] THEN
    ASM_SIMP_TAC [h3,
     h4, REAL_LE_MUL, REAL_POW_LE,
     REAL_SUB_LE, ABS_SQUARE_LE_1, REAL_LT_IMP_LE, REAL_ABS_NORM, NORM_POS_LE])
  : ExceptT String IO thm).run
#eval NORM_POINCARIFY_LT

#eval phrase 21
def KLEINIFY_POINCARIFY : thm := keep "KLEINIFY_POINCARIFY" fun _ => (do
  let h5 ← rr (← ExceptT.mk [[&1 - x < &1 pow 2 <=> &0 < x]])
  let h4 ← rf (← ExceptT.mk [[&0 < y /\ &2 * y = x ==> &2 * inv(x) * y = &1]])
  let h3 ← rf (← ExceptT.mk [[~(y = &0) ==> (&2 * x * y pow 2) * z * inv(y pow 2) = &2 * x * z]])
  let h2 ← rf (← ExceptT.mk [[~(y = &0)
    ==> (&1 + (a / y pow 2 * y) pow 2) = (y pow 2 + a pow 2) / y pow 2]])
  let h1 ← cr (← ExceptT.mk [[(~(x = Cx(&0)) ==> w * z = Cx(&1)) ==> w * z * x = x]])
  prove ([[!x. norm(x) < &1 ==> kleinify(poincarify x) = x]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [kleinify, poincarify] THEN MATCH_MP_TAC h1 THEN
    DISCH_TAC THEN REWRITE_TAC [(← HolLight.GSYM CX_MUL), CX_INJ, COMPLEX_NORM_MUL] THEN
    REWRITE_TAC [COMPLEX_NORM_CX, REAL_ABS_DIV, REAL_ABS_NORM, REAL_ABS_POW] THEN
    ASM_SIMP_TAC [COMPLEX_NORM_ZERO, h2] THEN
    REWRITE_TAC [REAL_POW2_ABS, real_div, REAL_INV_MUL, REAL_INV_INV] THEN
    ASM_SIMP_TAC [COMPLEX_NORM_ZERO, h3] THEN
    MATCH_MP_TAC h4 THEN
    CONJ_TAC THENL
     [REWRITE_TAC [REAL_SUB_LT] THEN MATCH_MP_TAC REAL_LT_LSQRT THEN
      REWRITE_TAC [REAL_POS, h5] THEN
      ASM_SIMP_TAC [REAL_POW_LT, COMPLEX_NORM_NZ],
      SUBGOAL_THEN ([[sqrt(&1 - norm(x:real^2) pow 2) pow 2 = &1 - norm x pow 2]]) MP_TAC THENL [MATCH_MP_TAC SQRT_POW_2, CONV_TAC REAL_FIELD]] THEN
    ASM_SIMP_TAC [REAL_SUB_LE, ABS_SQUARE_LE_1, REAL_ABS_NORM, REAL_LT_IMP_LE])
  : ExceptT String IO thm).run
#eval KLEINIFY_POINCARIFY

#eval phrase 22
def POINCARIFY_KLEINIFY : thm := keep "POINCARIFY_KLEINIFY" fun _ => (do
  let h9 ← rr (← ExceptT.mk [[abs(x) < &1 ==> ~(&1 + x = &0)]])
  let h8 ← rr (← ExceptT.mk [[&2 * x <= &1 * (&1 + x) <=> x <= &1]])
  let h7 ← rr (← ExceptT.mk [[&0 <= x ==> &0 < &1 + x]])
  let h6 ← rr (← ExceptT.mk [[&0 <= &1 - &2 * x / y <=> (&2 * x) / y <= &1]])
  let h5 ← rr (← ExceptT.mk [[x = &1 - y ==> &1 - x = y]])
  let h4 ← rf (← ExceptT.mk [[~(x = &0) /\ abs x < &1 /\ a = &2 * x / (&1 + x)
    ==> a * (&1 + x) pow 2 = &2 * x * (&1 + x)]])
  let h3 ← rr (← ExceptT.mk [[&0 <= x ==> abs(&1 + x) = &1 + x]])
  let h2 ← rf (← ExceptT.mk [[~(c = &0) /\ abs d < &1 /\ a * b = &2 * c pow 2 * (&1 + d)
    ==> a * inv(&2) pow 2 * b * inv(c) pow 2 * &2 * inv(&1 + d) = &1]])
  let h1 ← cr (← ExceptT.mk [[(~(x = Cx(&0)) ==> w * z = Cx(&1)) ==> w * z * x = x]])
  prove ([[!x. norm(x) < &1 ==> poincarify(kleinify x) = x]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [kleinify, poincarify] THEN
    MATCH_MP_TAC h1 THEN
    DISCH_TAC THEN REWRITE_TAC [(← HolLight.GSYM CX_MUL), CX_INJ] THEN
    REWRITE_TAC [COMPLEX_NORM_MUL, COMPLEX_NORM_CX] THEN
    REWRITE_TAC [REAL_ABS_DIV, REAL_ABS_NORM, REAL_ABS_POW, REAL_ABS_NUM] THEN
    REWRITE_TAC [real_div, REAL_INV_MUL, REAL_INV_INV, (← HolLight.GSYM REAL_MUL_ASSOC),
                REAL_INV_POW, REAL_POW_MUL] THEN
    MATCH_MP_TAC h2 THEN
    ASM_REWRITE_TAC [REAL_ABS_POW, COMPLEX_NORM_ZERO, ABS_SQUARE_LT_1] THEN
    ASM_SIMP_TAC [REAL_ABS_NORM, REAL_POW_LE, NORM_POS_LE, h3] THEN
    MATCH_MP_TAC h4 THEN
    ASM_REWRITE_TAC [REAL_ABS_NORM, COMPLEX_NORM_ZERO, REAL_ABS_POW,
                    ABS_SQUARE_LT_1, REAL_POW_EQ_0] THEN
    MATCH_MP_TAC h5 THEN
    MATCH_MP_TAC SQRT_UNIQUE THEN
    REWRITE_TAC [h6] THEN
    SIMP_TAC [REAL_LE_LDIV_EQ, REAL_POW_LE, NORM_POS_LE, h7] THEN
    REWRITE_TAC [h8] THEN
    ASM_SIMP_TAC [ABS_SQUARE_LE_1, REAL_ABS_NORM, REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN ([[~(&1 + norm(x:complex) pow 2 = &0)]]) MP_TAC THENL
     [ALL_TAC, CONV_TAC REAL_FIELD] THEN
    MATCH_MP_TAC h9 THEN
    ASM_REWRITE_TAC [REAL_ABS_POW, REAL_ABS_NORM, ABS_SQUARE_LT_1])
  : ExceptT String IO thm).run
#eval POINCARIFY_KLEINIFY

#eval phrase 23
def DDIST_KLEINIFY : thm := keep "DDIST_KLEINIFY" fun _ => (do
  let h8 ← rr (← ExceptT.mk [[&1 - x = &0 <=> x = &1]])
  let h7 ← rf (← ExceptT.mk [[(~(y = &0) /\ ~(y' = &0)) /\ a - y * y' = b
          ==> a = (b / (y * y') + &1) * y * y']])
  let h6 ← rg (← ExceptT.mk [[(&1 + x) pow 2 - &4 * x = (&1 - x) pow 2]])
  let h5 ← rr (← ExceptT.mk [[~(abs x = &1) ==> ~(&1 + x = &0)]])
  let h4 ← rf (← ExceptT.mk [[(~(y' = &0) /\ ~(y = &0)) /\
        (y * y' - &4 * d) pow 2 =
        b * (y pow 2 - &4 * x pow 2) * (y' pow 2 - &4 * x' pow 2)
        ==> (&1 - &2 / y * &2 / y' * d) pow 2 =
            b * (&1 - (&2 / y * x) pow 2) * (&1 - (&2 / y' * x') pow 2)]])
  let h3 ← rr (← ExceptT.mk [[&0 <= x ==> abs(&1 + x) = &1 + x]])
  let h2 ← rr (← ExceptT.mk [[x < &1 ==> ~(&1 - x = &0)]])
  let h1 ← rf (← ExceptT.mk [[~(y = &0) /\ z = (w + &1) * y ==> z / y - &1 = w]])
  prove ([[!w z. ~(norm w = &1) /\ ~(norm z = &1)
         ==> ddist(kleinify w,kleinify z) =
             &4 * (&1 / &2 + norm(w - z) pow 2 /
                             ((&1 - norm w pow 2) * (&1 - norm z pow 2))) pow 2
             - &1]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC ([[(&4 * norm(w - z:real^2) pow 2 *
     ((&1 - norm w pow 2) * (&1 - norm z pow 2) + norm(w - z) pow 2)) /
    ((&1 - norm w pow 2) pow 2 * (&1 - norm z pow 2) pow 2)]]) THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC [ddist, NORM_KLEINIFY_LT] THEN MATCH_MP_TAC h1 THEN
      CONJ_TAC THENL
       [REWRITE_TAC [REAL_ENTIRE, DE_MORGAN_THM] THEN CONJ_TAC THEN
        MATCH_MP_TAC h2 THEN
        ASM_SIMP_TAC [REAL_POW_1_LT, NORM_KLEINIFY_LT, NORM_POS_LE, ARITH],
        REWRITE_TAC [kleinify, COMPLEX_NORM_MUL, COMPLEX_NORM_CX] THEN
        REWRITE_TAC [(← HolLight.GSYM COMPLEX_CMUL), DOT_LMUL] THEN REWRITE_TAC [DOT_RMUL] THEN
        SIMP_TAC [REAL_ABS_DIV, REAL_ABS_NUM, REAL_POW_LE, NORM_POS_LE,
                 h3] THEN
        MATCH_MP_TAC h4 THEN
        CONJ_TAC THENL
         [CONJ_TAC THEN
          MATCH_MP_TAC h5 THEN
          ASM_SIMP_TAC [REAL_ABS_POW, REAL_POW_EQ_1, REAL_ABS_NORM] THEN ARITH_TAC,
          REWRITE_TAC [h6] THEN
          MATCH_MP_TAC h7 THEN
          CONJ_TAC THENL
           [ASM_REWRITE_TAC [REAL_POW_EQ_0, REAL_POW_EQ_1, REAL_ABS_NORM, ARITH,
                            h8],
            REWRITE_TAC [NORM_POW_2, DOT_LSUB, DOT_RSUB, DOT_SYM] THEN
            REAL_ARITH_TAC2]]],
      REPEAT (POP_ASSUM MP_TAC) THEN
      REWRITE_TAC [NORM_EQ_SQUARE, (← HolLight.GSYM NORM_POW_2)] THEN CONV_TAC REAL_FIELD])
  : ExceptT String IO thm).run
#eval DDIST_KLEINIFY

#eval phrase 24
def DDIST_KLEINIFY_EQ : thm := keep "DDIST_KLEINIFY_EQ" fun _ => (do
  prove ([[!w z w' z'.
      ~(norm w = &1) /\ ~(norm z = &1) /\ ~(norm w' = &1) /\ ~(norm z' = &1) /\
      norm(w - z) pow 2 * (&1 - norm w' pow 2) * (&1 - norm z' pow 2) =
      norm(w' - z') pow 2 * (&1 - norm w pow 2) * (&1 - norm z pow 2)
      ==> ddist(kleinify w,kleinify z) = ddist(kleinify w',kleinify z')]])
   (SIMP_TAC [DDIST_KLEINIFY, NORM_EQ_SQUARE, (← HolLight.GSYM NORM_POW_2), REAL_POS] THEN
    CONV_TAC REAL_FIELD)
  : ExceptT String IO thm).run
#eval DDIST_KLEINIFY_EQ

#eval phrase 25
def NORM_KLEINIFY_MOEBIUS_LT : thm := keep "NORM_KLEINIFY_MOEBIUS_LT" fun _ => (do
  prove ([[!w x. norm w < &1 /\ norm x < &1
         ==> norm(kleinify(moebius_function (&0) w x)) < &1]])
   (SIMP_TAC [MOEBIUS_FUNCTION_NORM_LT_1, NORM_KLEINIFY_LT, REAL_LT_IMP_NE])
  : ExceptT String IO thm).run
#eval NORM_KLEINIFY_MOEBIUS_LT

#eval phrase 26
def DDIST_KLEINIFY_MOEBIUS : thm := keep "DDIST_KLEINIFY_MOEBIUS" fun _ => (do
  let h4 ← rg (← ExceptT.mk [[x * y:real = w * z ==> (x * i) * y = w * z * i]])
  let h3 ← rf (← ExceptT.mk [[~(y = &0) /\ ~(y' = &0)
      ==> (&1 - (x / y) pow 2) * (&1 - (x' / y') pow 2) =
          ((y pow 2 - x pow 2) * (y' pow 2 - x' pow 2)) / (y * y') pow 2]])
  let h2 ← cf (← ExceptT.mk [[~(Cx(&1) - cnj w * x = Cx(&0)) /\ ~(Cx(&1) - cnj w * y = Cx(&0))
      ==> (x - w) / (Cx (&1) - cnj w * x) - (y - w) / (Cx (&1) - cnj w * y) =
          ((Cx(&1) - w * cnj w) * (x - y)) /
          ((Cx (&1) - cnj w * x) * (Cx (&1) - cnj w * y))]])
  let h1 ← ms [REAL_LT_REFL] (← ExceptT.mk [[norm(x) < norm(y) ==> ~(y = x)]])
  prove ([[!w x y. norm w < &1 /\ norm x < &1 /\ norm y < &1
           ==> ddist(kleinify(moebius_function (&0) w x),
                     kleinify(moebius_function (&0) w y)) =
               ddist(kleinify x,kleinify y)]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC DDIST_KLEINIFY_EQ THEN
    ASM_SIMP_TAC [MOEBIUS_FUNCTION_NORM_LT_1, REAL_LT_IMP_NE] THEN
    REWRITE_TAC [MOEBIUS_FUNCTION_SIMPLE] THEN
    SUBGOAL_THEN ([[~(Cx(&1) - cnj w * x = Cx(&0)) /\ ~(Cx(&1) - cnj w * y = Cx(&0))]]) STRIP_ASSUME_TAC THENL
     [REWRITE_TAC [COMPLEX_SUB_0] THEN CONJ_TAC THEN
      MATCH_MP_TAC h1 THEN
      REWRITE_TAC [COMPLEX_NORM_CX, REAL_ABS_NUM, COMPLEX_NORM_MUL] THEN
      GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.GSYM REAL_MUL_LID)] THEN
      MATCH_MP_TAC REAL_LT_MUL2 THEN REWRITE_TAC [NORM_POS_LE] THEN
      ASM_REWRITE_TAC [COMPLEX_NORM_CNJ],
      ASM_SIMP_TAC [h2] THEN
      REWRITE_TAC [COMPLEX_NORM_DIV, COMPLEX_NORM_POW] THEN
      ASM_SIMP_TAC [COMPLEX_NORM_ZERO, h3] THEN
      REWRITE_TAC [REAL_POW_DIV, COMPLEX_NORM_MUL] THEN REWRITE_TAC [real_div] THEN
      MATCH_MP_TAC h4 THEN
      REWRITE_TAC [(← HolLight.GSYM COMPLEX_NORM_MUL)] THEN REWRITE_TAC [NORM_POW_2, DOT_2] THEN
      REWRITE_TAC [(← HolLight.GSYM RE_DEF), (← HolLight.GSYM IM_DEF), complex_sub, complex_mul, CX_DEF,
                  complex_add, RE, IM, cnj, complex_neg] THEN REAL_ARITH_TAC2])
  : ExceptT String IO thm).run
#eval DDIST_KLEINIFY_MOEBIUS

#eval phrase 27
def COLLINEAR_KLEINIFY_MOEBIUS : thm := keep "COLLINEAR_KLEINIFY_MOEBIUS" fun _ => (do
  let h10 ← rr (← ExceptT.mk [[&0 < &1 - x - y <=> x + y < &1]])
  let h9 ← rr (← ExceptT.mk [[&0 < x /\ &0 <= y ==> ~(x + y = &0)]])
  let h8 ← rr (← ExceptT.mk [[x + y < &1 ==> ~(--(x + y - &1) = &0)]])
  let h7 ← rr (← ExceptT.mk [[&0 <= x + y ==> ~(x + y + &1 = &0)]])
  let h6 ← rg (← ExceptT.mk [[!a b. a * lhs = b * rhs /\ ~(a = &0) /\ ~(b = &0)
          ==> (lhs = &0 <=> rhs = &0)]])
  let h5 ← rf (← ExceptT.mk [[~(nx = &0) /\ ~(ny = &0) /\ ~(nz = &0)
    ==>(((&1 + (nxw / nx) pow 2) * rz / nz pow 2 -
         (&1 + (nzw / nz) pow 2) * rx / nx pow 2) *
        ((&1 + (nxw / nx) pow 2) * iy / ny pow 2 -
         (&1 + (nyw / ny) pow 2) * ix / nx pow 2) =
        ((&1 + (nxw / nx) pow 2) * ry / ny pow 2 -
         (&1 + (nyw / ny) pow 2) * rx / nx pow 2) *
        ((&1 + (nxw / nx) pow 2) * iz / nz pow 2 -
         (&1 + (nzw / nz) pow 2) * ix / nx pow 2) <=>
        ((nx pow 2 + nxw pow 2) * rz - (nz pow 2 + nzw pow 2) * rx) *
        ((nx pow 2 + nxw pow 2) * iy - (ny pow 2 + nyw pow 2) * ix) =
        ((nx pow 2 + nxw pow 2) * ry - (ny pow 2 + nyw pow 2) * rx) *
        ((nx pow 2 + nxw pow 2) * iz - (nz pow 2 + nzw pow 2) * ix))]])
  let h4 ← rr (← ExceptT.mk [[abs(&1) = &1 * &1]])
  let h3 ← ms [REAL_LT_REFL] (← ExceptT.mk [[norm x < norm y ==> ~(y = x)]])
  let h2 ← rf (← ExceptT.mk [[~(nx = &0) /\ ~(ny = &0) /\ ~(nz = &0)
      ==> ((&2 / nz * rz - &2 / nx * rx) * (&2 / ny * iy - &2 / nx * ix) =
           (&2 / ny * ry - &2 / nx * rx) * (&2 / nz * iz - &2 / nx * ix) <=>
           (nx * rz - nz * rx) * (nx * iy - ny * ix) =
           (nx * ry - ny * rx) * (nx * iz - nz * ix))]])
  let h1 ← rr (← ExceptT.mk [[&0 <= x ==> ~(&1 + x = &0)]])
  prove ([[!w x y z. norm w < &1 /\ norm x < &1 /\ norm y < &1 /\ norm z < &1
             ==> (collinear {kleinify(moebius_function (&0) w x),
                             kleinify(moebius_function (&0) w y),
                             kleinify(moebius_function (&0) w z)} <=>
                  collinear {kleinify x,kleinify y,kleinify z})]])
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [COLLINEAR_3_2D, kleinify, (← HolLight.GSYM RE_DEF), (← HolLight.GSYM IM_DEF)] THEN
    REWRITE_TAC [RE_MUL_CX, IM_MUL_CX] THEN
    SIMP_TAC [NORM_POS_LE, REAL_POW_LE, h1,
       h2] THEN
    REWRITE_TAC [COMPLEX_NORM_DIV, MOEBIUS_FUNCTION_SIMPLE] THEN
    ONCE_REWRITE_TAC [COMPLEX_DIV_CNJ] THEN
    REWRITE_TAC [RE_DIV_CX, (← HolLight.GSYM CX_POW), IM_DIV_CX] THEN
    SUBGOAL_THEN ([[~(Cx (&1) - cnj w * x = Cx(&0)) /\ ~(Cx (&1) - cnj w * y = Cx(&0)) /\
    ~(Cx (&1) - cnj w * z = Cx(&0))]]) STRIP_ASSUME_TAC THENL
     [REWRITE_TAC [COMPLEX_SUB_0] THEN REPEAT CONJ_TAC THEN
      MATCH_MP_TAC h3 THEN
      REWRITE_TAC [COMPLEX_NORM_MUL, COMPLEX_NORM_CNJ, COMPLEX_NORM_CX] THEN
      ONCE_REWRITE_TAC [h4] THEN
      MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REWRITE_TAC [NORM_POS_LE],
      ALL_TAC] THEN
    ASM_SIMP_TAC [COMPLEX_NORM_ZERO, h5] THEN
    REWRITE_TAC [COMPLEX_SQNORM, complex_sub, complex_mul, complex_add,
                complex_neg, cnj, CX_DEF, RE, IM] THEN
    ONCE_REWRITE_TAC [(← HolLight.GSYM REAL_SUB_0)] THEN MATCH_MP_TAC h6 THEN
    EXISTS_TAC ([[Re x pow 2 + Im x pow 2 + &1]]) THEN
    EXISTS_TAC ([[--(Re w pow 2 + Im w pow 2 - &1) pow 3 *
              ((&1 - Re(x) pow 2 - Im(x) pow 2) *
               (&1 - Re(w) pow 2 - Im(w) pow 2) +
               &2 * (Re w - Re x) pow 2 + &2 * (Im w - Im x) pow 2)]]) THEN
    REWRITE_TAC [REAL_ENTIRE, DE_MORGAN_THM, REAL_POW_EQ_0, ARITH_EQ] THEN
    REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC2,
      MATCH_MP_TAC h7 THEN
      ASM_SIMP_TAC [(← HolLight.GSYM COMPLEX_SQNORM), REAL_LE_POW_2],
      MATCH_MP_TAC h8 THEN
      ASM_SIMP_TAC [(← HolLight.GSYM COMPLEX_SQNORM), REAL_POW_1_LT, NORM_POS_LE, ARITH],
      MATCH_MP_TAC h9 THEN
      SIMP_TAC [REAL_LE_ADD, REAL_LE_MUL, REAL_POS, REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REWRITE_TAC [h10] THEN
      ASM_SIMP_TAC [(← HolLight.GSYM COMPLEX_SQNORM), REAL_POW_1_LT, NORM_POS_LE, ARITH]])
  : ExceptT String IO thm).run
#eval COLLINEAR_KLEINIFY_MOEBIUS

#eval phrase 28
def BETWEEN_KLEINIFY_MOEBIUS : thm := keep "BETWEEN_KLEINIFY_MOEBIUS" fun _ => (do
  prove ([[!w x y z. norm w < &1 /\ norm x < &1 /\ norm y < &1 /\ norm z < &1
             ==> (between (kleinify(moebius_function (&0) w x))
                          (kleinify(moebius_function (&0) w y),
                           kleinify(moebius_function (&0) w z)) <=>
                  between (kleinify x) (kleinify y,kleinify z))]])
   (SIMP_TAC [BETWEEN_COLLINEAR_DDIST_EQ, NORM_KLEINIFY_MOEBIUS_LT,
             NORM_KLEINIFY_LT, REAL_LT_IMP_NE,
             COLLINEAR_KLEINIFY_MOEBIUS, DDIST_KLEINIFY_MOEBIUS])
  : ExceptT String IO thm).run
#eval BETWEEN_KLEINIFY_MOEBIUS

#eval phrase 29
def hyperbolic_isometry : thm := keep "hyperbolic_isometry" fun _ => new_definition
 [[hyperbolic_isometry (f:real^2->real^2) <=>
    (!x. norm x < &1 ==> norm(f x) < &1) /\
    (!x y. norm x < &1 /\ norm y < &1 ==> ddist(f x,f y) = ddist(x,y)) /\
    (!x y z. norm x < &1 /\ norm y < &1 /\ norm z < &1
             ==> (between (f x) (f y,f z) <=> between x (y,z)))]]
#eval hyperbolic_isometry

#eval phrase 30
def HYPERBOLIC_TRANSLATION : thm := keep "HYPERBOLIC_TRANSLATION" fun _ => (do
  prove ([[!w. norm w < &1
       ==> ?f:real^2->real^2 g:real^2->real^2.
                hyperbolic_isometry f /\ hyperbolic_isometry g /\
                f(w) = vec 0 /\ g(vec 0) = w /\
                (!x. norm x < &1 ==> f(g x) = x) /\
                (!x. norm x < &1 ==> g(f x) = x)]])
   (REPEAT STRIP_TAC THEN SIMP_TAC [hyperbolic_isometry] THEN MAP_EVERY EXISTS_TAC [([[\x. kleinify(moebius_function(&0) (poincarify w) (poincarify x))]]),
     ([[\x. kleinify(moebius_function(&0) (--(poincarify w)) (poincarify x))]])] THEN
    ASM_SIMP_TAC [NORM_KLEINIFY_MOEBIUS_LT, NORM_POINCARIFY_LT,
                 DDIST_KLEINIFY_MOEBIUS, KLEINIFY_POINCARIFY, VECTOR_NEG_NEG,
                 BETWEEN_KLEINIFY_MOEBIUS, NORM_NEG, MOEBIUS_FUNCTION_COMPOSE,
                 POINCARIFY_KLEINIFY, MOEBIUS_FUNCTION_NORM_LT_1] THEN
    ASM_SIMP_TAC [MOEBIUS_FUNCTION_SIMPLE, COMPLEX_SUB_REFL, complex_div,
                 COMPLEX_VEC_0, KLEINIFY_0, POINCARIFY_0, COMPLEX_MUL_LZERO,
                 COMPLEX_MUL_RZERO, COMPLEX_SUB_LZERO, COMPLEX_NEG_NEG,
                 COMPLEX_SUB_RZERO, COMPLEX_INV_1, COMPLEX_MUL_RID,
                 KLEINIFY_POINCARIFY])
  : ExceptT String IO thm).run
#eval HYPERBOLIC_TRANSLATION

/- ------------------------------------------------------------------------- -/
/- Our model.                                                                -/
/- ------------------------------------------------------------------------- -/

#eval phrase 31
-- let plane_tybij = ...;;
def plane_tybij : thm := keep "plane_tybij" fun _ => (do
  let th ← prove ([[?x:real^2. norm x < &1]])
    (EXISTS_TAC ([[vec 0:real^2]]) THEN NORM_ARITH_TAC)
  ExceptT.mk (new_type_definition "plane" "mk_plane" "dest_plane" th)
  : ExceptT String IO thm).run
#eval plane_tybij

#eval phrase 32
def pbetween : thm := keep "pbetween" fun _ => new_definition
 [[pbetween y (x,z) <=> between (dest_plane y) (dest_plane x,dest_plane z)]]
#eval pbetween

#eval phrase 33
def pdist : thm := keep "pdist" fun _ => new_definition
 [[pdist(x,y) = ddist(dest_plane x,dest_plane y)]]
#eval pdist

#eval phrase 34
def DEST_PLANE_NORM_LT : thm := keep "DEST_PLANE_NORM_LT" fun _ => (do
  prove ([[!x. norm(dest_plane x) < &1]])
   (MESON_TAC [plane_tybij])
  : ExceptT String IO thm).run
#eval DEST_PLANE_NORM_LT

#eval phrase 35
def DEST_PLANE_EQ : thm := keep "DEST_PLANE_EQ" fun _ => (do
  prove ([[!x y. dest_plane x = dest_plane y <=> x = y]])
   (MESON_TAC [plane_tybij])
  : ExceptT String IO thm).run
#eval DEST_PLANE_EQ

#eval phrase 36
def FORALL_DEST_PLANE : thm := keep "FORALL_DEST_PLANE" fun _ => (do
  prove ([[!P. (!x. P(dest_plane x)) <=> (!x. norm x < &1 ==> P x)]])
   (MESON_TAC [plane_tybij])
  : ExceptT String IO thm).run
#eval FORALL_DEST_PLANE

#eval phrase 37
def EXISTS_DEST_PLANE : thm := keep "EXISTS_DEST_PLANE" fun _ => (do
  prove ([[!P. (?x. P(dest_plane x)) <=> (?x. norm x < &1 /\ P x)]])
   (MESON_TAC [plane_tybij])
  : ExceptT String IO thm).run
#eval EXISTS_DEST_PLANE

/- ------------------------------------------------------------------------- -/
/- Axiom 1 (reflexivity for equidistance).                                   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 38
def TARSKI_AXIOM_1_NONEUCLIDEAN : thm := keep "TARSKI_AXIOM_1_NONEUCLIDEAN" fun _ => (do
  prove ([[!a b. pdist(a,b) = pdist(b,a)]])
   (REWRITE_TAC [pdist, DDIST_SYM])
  : ExceptT String IO thm).run
#eval TARSKI_AXIOM_1_NONEUCLIDEAN

/- ------------------------------------------------------------------------- -/
/- Axiom 2 (transitivity for equidistance).                                  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 39
def TARSKI_AXIOM_2_NONEUCLIDEAN : thm := keep "TARSKI_AXIOM_2_NONEUCLIDEAN" fun _ => (do
  prove ([[!a b p q r s.
        pdist(a,b) = pdist(p,q) /\ pdist(a,b) = pdist(r,s)
        ==> pdist(p,q) = pdist(r,s)]])
   (REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval TARSKI_AXIOM_2_NONEUCLIDEAN

/- ------------------------------------------------------------------------- -/
/- Axiom 3 (identity for equidistance).                                      -/
/- ------------------------------------------------------------------------- -/

#eval phrase 40
def TARSKI_AXIOM_3_NONEUCLIDEAN : thm := keep "TARSKI_AXIOM_3_NONEUCLIDEAN" fun _ => (do
  prove ([[!a b c. pdist(a,b) = pdist(c,c) ==> a = b]])
   (SIMP_TAC [FORALL_DEST_PLANE, pdist, DDIST_REFL, DDIST_EQ_0, DEST_PLANE_EQ])
  : ExceptT String IO thm).run
#eval TARSKI_AXIOM_3_NONEUCLIDEAN

/- ------------------------------------------------------------------------- -/
/- Axiom 4 (segment construction).                                           -/
/- ------------------------------------------------------------------------- -/

#eval phrase 41
def TARSKI_AXIOM_4_NONEUCLIDEAN : thm := keep "TARSKI_AXIOM_4_NONEUCLIDEAN" fun _ => (do
  let h1 ← ms [] (← ExceptT.mk [[P(vec 0) /\ (P(vec 0) ==> !x. P x) ==> !x. P x]])
  prove ([[!a q b c. ?x. pbetween a (q,x) /\ pdist(a,x) = pdist(b,c)]])
   (REWRITE_TAC [pbetween, pdist, FORALL_DEST_PLANE, EXISTS_DEST_PLANE] THEN
    REWRITE_TAC [RIGHT_IMP_FORALL_THM, IMP_IMP, (← HolLight.GSYM CONJ_ASSOC)] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[?d:real^2. norm d < &1 /\ ddist(b:real^2,c) = ddist(vec 0,d)]]) STRIP_ASSUME_TAC THENL
     [MP_TAC (← HolLight.SPEC ([[b:real^2]]) HYPERBOLIC_TRANSLATION) THEN
      ASM_REWRITE_TAC [hyperbolic_isometry] THEN ASM_MESON_TAC [],
      ASM_REWRITE_TAC []] THEN
    SUBGOAL_THEN ([[norm(a:real^2) < &1 /\ norm(q:real^2) < &1 /\ norm(d:real^2) < &1]]) MP_TAC THENL [ASM_REWRITE_TAC [], REPEAT (POP_ASSUM ((fun _ => ALL_TAC)))] THEN
    MAP_EVERY (fun t => SPEC_TAC (t, t)) [([[d:real^2]]), ([[q:real^2]]), ([[a:real^2]])] THEN
    MATCH_MP_TAC h1 THEN
    REWRITE_TAC [NORM_0, REAL_LT_01] THEN CONJ_TAC THENL
     [MP_TAC (← HolLight.ISPEC ([[vec 0:real^2]]) TARSKI_AXIOM_4_EUCLIDEAN) THEN
      MESON_TAC [DIST_0, DDIST_EQ_ORIGIN],
      DISCH_THEN (LABEL_TAC "*") THEN REPEAT STRIP_TAC THEN
      MP_TAC (← HolLight.ISPEC ([[a:real^2]]) HYPERBOLIC_TRANSLATION) THEN
      ASM_REWRITE_TAC [hyperbolic_isometry, LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[f:real^2->real^2]]), ([[g:real^2->real^2]])] THEN
      STRIP_TAC THEN
      REMOVE_THEN "*" (MP_TAC o HolLight.SPECL [([[(f:real^2->real^2) q]]), ([[d:real^2]])]) THEN
      ASM_SIMP_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[x:real^2]]) STRIP_ASSUME_TAC) THEN
      EXISTS_TAC ([[(g:real^2->real^2) x]]) THEN ASM_MESON_TAC []])
  : ExceptT String IO thm).run
#eval TARSKI_AXIOM_4_NONEUCLIDEAN

/- ------------------------------------------------------------------------- -/
/- Axiom 5 (five-segments axiom).                                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 42
def TARSKI_AXIOM_5_NONEUCLIDEAN : thm := keep "TARSKI_AXIOM_5_NONEUCLIDEAN" fun _ => (do
  let h2 ← tt (← ExceptT.mk [[p /\ (q ==> r) ==> (p <=> q) ==> r]])
  let h1 ← tt (← ExceptT.mk [[(p ==> r) /\ q ==> (p <=> q) ==> r]])
  prove ([[!a b c x a' b' c' x'.
        ~(a = b) /\
        pdist(a,b) = pdist(a',b') /\
        pdist(a,c) = pdist(a',c') /\
        pdist(b,c) = pdist(b',c') /\
        pbetween b (a,x) /\ pbetween b' (a',x') /\ pdist(b,x) = pdist(b',x')
        ==> pdist(c,x) = pdist(c',x')]])
   (REWRITE_TAC [FORALL_DEST_PLANE, pdist, pbetween, (← HolLight.GSYM DEST_PLANE_EQ)] THEN
    REPEAT STRIP_TAC THEN MP_TAC (← HolLight.ISPEC ([[b':real^2]]) HYPERBOLIC_TRANSLATION) THEN
    MP_TAC (← HolLight.ISPEC ([[b:real^2]]) HYPERBOLIC_TRANSLATION) THEN
    ASM_REWRITE_TAC [RIGHT_IMP_FORALL_THM, LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [hyperbolic_isometry] THEN MAP_EVERY X_GEN_TAC [([[f:real^2->real^2]]), ([[f':real^2->real^2]]), ([[g:real^2->real^2]]),
      ([[g':real^2->real^2]])] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[(f:real^2->real^2) x]]), ([[(f:real^2->real^2) c]]),
                  ([[(g:real^2->real^2) x']]), ([[(g:real^2->real^2) c']])] DDIST_CONGRUENT_TRIPLES_0) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC h1 THEN
    CONJ_TAC THENL [ASM_MESON_TAC [DDIST_SYM], ALL_TAC] THEN
    MP_TAC (← HolLight.ISPECL [([[(f:real^2->real^2) a]]), ([[(f:real^2->real^2) c]]),
                  ([[(g:real^2->real^2) a']]), ([[(g:real^2->real^2) c']])] DDIST_CONGRUENT_TRIPLES_0) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC h2 THEN CONJ_TAC THENL
     [ASM_SIMP_TAC [(← HolLight.GSYM DDIST_CONGRUENT_TRIPLES_0)] THEN CONJ_TAC THEN
      GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [(← HolLight.SYM (← HolLight.ASSUME ([[(f:complex->complex) b = vec 0]])))] THEN
      GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.ONCE_DEPTH_CONV) [(← HolLight.SYM (← HolLight.ASSUME ([[(g:complex->complex) b' = vec 0]])))] THEN
      ASM_SIMP_TAC [] THEN ASM_MESON_TAC [DDIST_SYM],
      STRIP_TAC THEN MP_TAC (← HolLight.ISPECL [([[(f:real^2->real^2) a]]), ([[(f:real^2->real^2) b]]), ([[(f:real^2->real^2) c]]),
        ([[(f:real^2->real^2) x]]), ([[(g:real^2->real^2) a']]), ([[(g:real^2->real^2) b']]),
        ([[(g:real^2->real^2) c']]), ([[(g:real^2->real^2) x']])] TARSKI_AXIOM_5_EUCLIDEAN) THEN
      SUBGOAL_THEN ([[ddist((f:real^2->real^2) b,f x) = ddist((g:real^2->real^2) b',g x')]]) MP_TAC THENL
       [ASM_SIMP_TAC [],
        ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [DDIST_EQ_ORIGIN] THEN DISCH_TAC] THEN
      ASM_MESON_TAC [SessionMultiLib.Vectors.DIST_SYM, DIST_0]])
  : ExceptT String IO thm).run
#eval TARSKI_AXIOM_5_NONEUCLIDEAN

/- ------------------------------------------------------------------------- -/
/- Axiom 6 (identity for between-ness).                                      -/
/- ------------------------------------------------------------------------- -/

#eval phrase 43
def TARSKI_AXIOM_6_NONEUCLIDEAN : thm := keep "TARSKI_AXIOM_6_NONEUCLIDEAN" fun _ => (do
  prove ([[!a b. pbetween b (a,a) ==> a = b]])
   (REWRITE_TAC [pbetween, FORALL_DEST_PLANE, (← HolLight.GSYM DEST_PLANE_EQ)] THEN
    MESON_TAC [TARSKI_AXIOM_6_EUCLIDEAN])
  : ExceptT String IO thm).run
#eval TARSKI_AXIOM_6_NONEUCLIDEAN

/- ------------------------------------------------------------------------- -/
/- Axiom 7 (Pasch's axiom).                                                  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 44
def TARSKI_AXIOM_7_NONEUCLIDEAN : thm := keep "TARSKI_AXIOM_7_NONEUCLIDEAN" fun _ => (do
  prove ([[!a b c p q.
    pbetween p (a,c) /\ pbetween q (b,c)
    ==> ?x. pbetween x (p,b) /\ pbetween x (q,a)]])
   (REWRITE_TAC [pbetween, FORALL_DEST_PLANE, EXISTS_DEST_PLANE] THEN
    MESON_TAC [BETWEEN_NORM_LT, TARSKI_AXIOM_7_EUCLIDEAN])
  : ExceptT String IO thm).run
#eval TARSKI_AXIOM_7_NONEUCLIDEAN

/- ------------------------------------------------------------------------- -/
/- Axiom 8 (lower 2-dimensional axiom).                                      -/
/- ------------------------------------------------------------------------- -/

#eval phrase 45
def TARSKI_AXIOM_8_NONEUCLIDEAN : thm := keep "TARSKI_AXIOM_8_NONEUCLIDEAN" fun _ => (do
  prove ([[?a b c. ~pbetween b (a,c) /\ ~pbetween c (b,a) /\ ~pbetween a (c,b)]])
   (REWRITE_TAC [pbetween, EXISTS_DEST_PLANE, NORM_LT_SQUARE, NORM_POW_2] THEN
    MAP_EVERY (fun t => EXISTS_TAC t THEN
      SIMP_TAC [DOT_LMUL, DOT_RMUL, DOT_BASIS_BASIS, DIMINDEX_2, ARITH] THEN
      REWRITE_TAC [DOT_LZERO] THEN CONV_TAC REAL_RAT_REDUCE_CONV) [([[vec 0:real^2]]), ([[(&1 / &2) % basis 1:real^2]]),
      ([[(&1 / &2) % basis 2:real^2]])] THEN
    REPEAT CONJ_TAC THEN DISCH_THEN (MP_TAC o HolLight.MATCH_MP BETWEEN_IMP_COLLINEAR) THEN
    SIMP_TAC [COLLINEAR_3_2D, VECTOR_MUL_COMPONENT, VEC_COMPONENT, ARITH,
             BASIS_COMPONENT, DIMINDEX_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV)
  : ExceptT String IO thm).run
#eval TARSKI_AXIOM_8_NONEUCLIDEAN

/- ------------------------------------------------------------------------- -/
/- Axiom 9 (upper 2-dimensional axiom).                                      -/
/- ------------------------------------------------------------------------- -/

#eval phrase 46
def TARSKI_AXIOM_9_NONEUCLIDEAN : thm := keep "TARSKI_AXIOM_9_NONEUCLIDEAN" fun _ => (do
  let h3 ← va (← ExceptT.mk [[--x:real^N = x <=> x = vec 0]])
  let h2 ← rf (← ExceptT.mk [[&0 < x /\ &0 < y
      ==> (a * inv x * inv y - &1 = b * inv x * inv y - &1 <=> a = b)]])
  let h1 ← na (← ExceptT.mk [[norm(a:real^N) = norm b <=> dist(a,vec 0) = dist(vec 0,b)]])
  prove ([[!p q a b c.
        ~(p = q) /\
        pdist(a,p) = pdist(a,q) /\ pdist(b,p) = pdist(b,q) /\
        pdist(c,p) = pdist(c,q)
        ==> pbetween b (a,c) \/ pbetween c (b,a) \/ pbetween a (c,b)]])
   (REWRITE_TAC [pdist, pbetween, FORALL_DEST_PLANE, (← HolLight.GSYM DEST_PLANE_EQ)] THEN
    REWRITE_TAC [RIGHT_IMP_FORALL_THM, IMP_IMP, (← HolLight.GSYM CONJ_ASSOC)] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[p:real^2]]), ([[q:real^2]])] HYPERBOLIC_MIDPOINT) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC ([[x:real^2]]) THEN
    STRIP_TAC THEN MP_TAC (← HolLight.ISPEC ([[x:real^2]]) HYPERBOLIC_TRANSLATION) THEN
    SUBGOAL_THEN ([[norm(x:real^2) < &1]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [BETWEEN_NORM_LT], ONCE_REWRITE_TAC [BETWEEN_SYM]] THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM, hyperbolic_isometry] THEN
    REWRITE_TAC [(← HolLight.GSYM COLLINEAR_BETWEEN_CASES)] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[collinear{(f:real^2->real^2) b,f c,f a}]]) MP_TAC THENL
     [ALL_TAC, ASM_SIMP_TAC [COLLINEAR_BETWEEN_CASES]] THEN
    SUBGOAL_THEN ([[ddist(f a,f p) = ddist(f a,f q) /\
                ddist(f b,f p) = ddist(f b,f q) /\
                ddist(f c,f p) = ddist(f c,f q) /\
                ~((f:real^2->real^2) q = f p)]]) MP_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN ([[(f:real^2->real^2) q = --(f p)]]) SUBST1_TAC THENL
     [SUBGOAL_THEN ([[between ((f:real^2->real^2) x) (f p,f q) /\
                  ddist(f x,f p) = ddist(f x,f q)]]) MP_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [DDIST_EQ_ORIGIN] THEN
      REWRITE_TAC [(← HolLight.GSYM MIDPOINT_BETWEEN), midpoint, h1] THEN
      VECTOR_ARITH_TAC,
      REWRITE_TAC [ddist] THEN ASM_SIMP_TAC [NORM_NEG, real_div, REAL_INV_MUL] THEN
      ASM_SIMP_TAC [REAL_SUB_LT, ABS_SQUARE_LT_1, REAL_ABS_NORM, h2] THEN
      ONCE_REWRITE_TAC [h3] THEN
      REWRITE_TAC [COLLINEAR_3_2D, VECTOR_SUB_COMPONENT, DOT_2, (← HolLight.GSYM DOT_EQ_0),
                    VECTOR_NEG_COMPONENT] THEN CONV_TAC REAL_RING])
  : ExceptT String IO thm).run
#eval TARSKI_AXIOM_9_NONEUCLIDEAN

/- ------------------------------------------------------------------------- -/
/- Axiom 10 (Euclidean axiom).                                               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 47
def NOT_TARSKI_AXIOM_10_NONEUCLIDEAN : thm := keep "NOT_TARSKI_AXIOM_10_NONEUCLIDEAN" fun _ => (do
  let h3 ← rr (← ExceptT.mk [[a * &0 + y = x + b * &0 ==> abs x + abs y <= (&1 - u) * &1 + u * &1
         ==> abs x <= abs(&1 / &2) /\ abs y <= abs(&1 / &2)]])
  let h2 ← rr (← ExceptT.mk [[&0 = &1 / &2 * x <=> x = &0]])
  let h1 ← tt (← ExceptT.mk [[~(p /\ q) <=> p ==> ~q]])
  prove ([[~(!a b c d t.
      pbetween d (a,t) /\ pbetween d (b,c) /\ ~(a = d)
      ==> ?x y. pbetween b (a,x) /\ pbetween c (a,y) /\ pbetween t (x,y))]])
   (REWRITE_TAC [pbetween, FORALL_DEST_PLANE, EXISTS_DEST_PLANE,
                (← HolLight.GSYM DEST_PLANE_EQ), RIGHT_IMP_FORALL_THM, IMP_IMP] THEN
    DISCH_THEN (MP_TAC o HolLight.SPECL [([[vec 0:real^2]]), ([[&1 / &2 % basis 1:real^2]]), ([[&1 / &2 % basis 2:real^2]]),
      ([[&1 / &4 % basis 1 + &1 / &4 % basis 2:real^2]]),
      ([[&3 / &5 % basis 1 + &3 / &5 % basis 2:real^2]])]) THEN
    REWRITE_TAC [NOT_IMP, CONJ_ASSOC] THEN CONJ_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [NOT_EXISTS_THM, h1] THEN
      REWRITE_TAC [IMP_CONJ] THEN REPEAT (GEN_TAC THEN DISCH_TAC) THEN
      REWRITE_TAC [IMP_IMP] THEN
      DISCH_THEN (CONJUNCTS_THEN (MP_TAC o HolLight.MATCH_MP BETWEEN_IMP_COLLINEAR)) THEN
      SIMP_TAC [COLLINEAR_3_2D, BASIS_COMPONENT, DIMINDEX_2, ARITH, VEC_COMPONENT,
               VECTOR_MUL_COMPONENT] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC [REAL_SUB_LZERO, REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_SUB_RZERO,
                  h2] THEN
      REWRITE_TAC [REAL_ENTIRE] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MP_TAC (← HolLight.ISPECL [([[x:real^2]]), ([[1]])] COMPONENT_LE_NORM) THEN
      MP_TAC (← HolLight.ISPECL [([[y:real^2]]), ([[2]])] COMPONENT_LE_NORM) THEN
      SIMP_TAC [DIMINDEX_2, ARITH, BETWEEN_IN_SEGMENT, IN_SEGMENT] THEN
      REPEAT STRIP_TAC THEN SUBGOAL_THEN ([[norm(&3 / &5 % basis 1 + &3 / &5 % basis 2:real^2) pow 2 <= &1 / &2]]) MP_TAC THENL
       [SUBGOAL_THEN ([[(&3 / &5 % basis 1 + &3 / &5 % basis 2:real^2)$2 =
                    (&3 / &5 % basis 1 + &3 / &5 % basis 2:real^2)$1]]) MP_TAC THENL
         [SIMP_TAC [CART_EQ, DIMINDEX_2, FORALL_2, ARITH, BASIS_COMPONENT,
                  VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT, VEC_COMPONENT] THEN
          REAL_ARITH_TAC2,
          ASM_REWRITE_TAC []] THEN
        REWRITE_TAC [NORM_POW_2, DOT_LADD, DOT_RADD, DOT_LMUL, DOT_RMUL] THEN
        ASM_SIMP_TAC [DIMINDEX_2, FORALL_2, DOT_2, VECTOR_ADD_COMPONENT, ARITH,
                     VECTOR_MUL_COMPONENT, BASIS_COMPONENT, DIMINDEX_2] THEN
        DISCH_THEN (MP_TAC o HolLight.MATCH_MP h3) THEN
        ANTS_TAC THENL
         [REWRITE_TAC [REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
          CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC,
          REWRITE_TAC [REAL_LE_SQUARE_ABS] THEN REAL_ARITH_TAC2],
        ALL_TAC]] THEN
    SIMP_TAC [NORM_LT_SQUARE, NORM_POW_2, DOT_LADD, DOT_RADD, DOT_LZERO,
             DOT_LMUL, DOT_RMUL, DOT_BASIS_BASIS, DIMINDEX_2, ARITH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC [BETWEEN_IN_SEGMENT, IN_SEGMENT] THEN REPEAT CONJ_TAC THENL
     [EXISTS_TAC ([[&5 / &12]]), EXISTS_TAC ([[&1 / &2]]), ALL_TAC] THEN
    SIMP_TAC [CART_EQ, DIMINDEX_2, FORALL_2, ARITH, BASIS_COMPONENT,
             VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT, VEC_COMPONENT] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV)
  : ExceptT String IO thm).run
#eval NOT_TARSKI_AXIOM_10_NONEUCLIDEAN

/- ------------------------------------------------------------------------- -/
/- Axiom 11 (Continuity).                                                    -/
/- ------------------------------------------------------------------------- -/

#eval phrase 48
def TARSKI_AXIOM_11_NONEUCLIDEAN : thm := keep "TARSKI_AXIOM_11_NONEUCLIDEAN" fun _ => (do
  prove ([[!X Y. (?a. !x y. x IN X /\ y IN Y ==> pbetween x (a,y))
         ==> (?b. !x y. x IN X /\ y IN Y ==> pbetween b (x,y))]])
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC ([[X:plane->bool = {}]]) THEN ASM_REWRITE_TAC [NOT_IN_EMPTY] THEN
    ASM_CASES_TAC ([[Y:plane->bool = {}]]) THEN ASM_REWRITE_TAC [NOT_IN_EMPTY] THEN
    REWRITE_TAC [pbetween, EXISTS_DEST_PLANE] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[a:real^2]]) STRIP_ASSUME_TAC) THEN
    MP_TAC (← HolLight.ISPECL [([[IMAGE dest_plane X]]), ([[IMAGE dest_plane Y]])] TARSKI_AXIOM_11_EUCLIDEAN) THEN REWRITE_TAC [IN_IMAGE] THEN
    ANTS_TAC THENL [HolLight.ASM SET_TAC [], MATCH_MP_TAC MONO_EXISTS] THEN
    ASM_MESON_TAC [MEMBER_NOT_EMPTY, DEST_PLANE_NORM_LT, BETWEEN_NORM_LT])
  : ExceptT String IO thm).run
#eval TARSKI_AXIOM_11_NONEUCLIDEAN

end Hol100.Independence
