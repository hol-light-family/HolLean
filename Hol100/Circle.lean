/- File: Hol100/Circle.lean
Translation of HOL Light's 100/circle.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionMultiLib.Measure
import SessionMultiLib.RealAnalysis
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Permutations SessionLibrary.Binomial SessionLibrary.Wo SessionLibrary.Products SessionLibrary.Floor SessionLibrary.Iter SessionLibrary.Frag SessionLibrary.Prime SessionLibrary.Card SessionLibrary.Matroids SessionMultiLib.Misc SessionLibrary.GroupTheory SessionMultiLib.Vectors SessionMultiLib.Metric SessionMultiLib.Determinants SessionMultiLib.Homology SessionMultiLib.Topology SessionMultiLib.Convex SessionMultiLib.ComplexAlgebra SessionMultiLib.Complexes SessionMultiLib.Paths SessionMultiLib.Polytope SessionMultiLib.Degree SessionMultiLib.Derivatives SessionMultiLib.Integration SessionMultiLib.Measure SessionMultiLib.Canal SessionMultiLib.Transcendentals SessionMultiLib.RealAnalysis
namespace Hol100.Circle

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def na (tm : term) : ExceptT String IO thm := ExceptT.mk (NORM_ARITH tm)
private def rf (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_FIELD tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)

/- ========================================================================= -/
/- Area of a circle.                                                         -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Multivariate/measure.ml";;
#eval SessionMultiLib.Measure.ensureMeasure

#eval phrase 2
-- needs "Multivariate/realanalysis.ml";;
#eval SessionMultiLib.RealAnalysis.ensureRealAnalysis

/- ------------------------------------------------------------------------- -/
/- Circle area. Should maybe extend WLOG tactics for such scaling.           -/
/- ------------------------------------------------------------------------- -/

#eval phrase 3
def AREA_UNIT_CBALL : thm := keep "AREA_UNIT_CBALL" fun _ => (do
  let h3 ← rf (← ExceptT.mk [[s pow 2 = &1 - x pow 2 /\ x pow 2 < &1
      ==> (inv s + x * --(&2 * x) * inv (&2) * inv s + s) = &2 * s]])
  let h2 ← rr (← ExceptT.mk [[x / &2 - --(x / &2) = x]])
  let h1 ← rr (← ExceptT.mk [[&0 <= x ==> --x <= x]])
  prove ([[measure(cball(vec 0:real^2,&1)) = pi]])
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (← HolLight.INST_TYPE [((← ExceptT.mk (HolCore.Parser.parse_type "1")), (← ExceptT.mk (HolCore.Parser.parse_type "M"))), ((← ExceptT.mk (HolCore.Parser.parse_type "2")), (← ExceptT.mk (HolCore.Parser.parse_type "N")))] FUBINI_SIMPLE_COMPACT) THEN
    EXISTS_TAC ([[1]]) THEN
    SIMP_TAC [DIMINDEX_1, DIMINDEX_2, ARITH, COMPACT_CBALL, SLICE_CBALL] THEN
    REWRITE_TAC [VEC_COMPONENT, DROPOUT_0, REAL_SUB_RZERO] THEN
    ONCE_REWRITE_TAC [COND_RAND] THEN REWRITE_TAC [MEASURE_EMPTY] THEN
    SUBGOAL_THEN ([[!t. abs(t) <= &1 <=> t IN real_interval[-- &1,&1] ]]) (fun th => REWRITE_TAC [th]) THENL [REWRITE_TAC [IN_REAL_INTERVAL] THEN REAL_ARITH_TAC2, ALL_TAC] THEN
    REWRITE_TAC [HAS_REAL_INTEGRAL_RESTRICT_UNIV, BALL_1] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
    EXISTS_TAC ([[\t. &2 * sqrt(&1 - t pow 2)]]) THEN CONJ_TAC THENL
     [X_GEN_TAC ([[t:real]]) THEN SIMP_TAC [IN_REAL_INTERVAL, MEASURE_INTERVAL] THEN
      REWRITE_TAC [REAL_BOUNDS_LE, VECTOR_ADD_LID, VECTOR_SUB_LZERO] THEN
      DISCH_TAC THEN
      HolCore.Lib.W (MP_TAC o HolLight.PART_MATCH (HolCore.Equal.lhs o HolCore.Kernel.rand) CONTENT_1 o HolCore.Kernel.rand o HolLight.snd) THEN
      REWRITE_TAC [LIFT_DROP, DROP_NEG] THEN
      ANTS_TAC THENL [ALL_TAC, SIMP_TAC [REAL_POW_ONE] THEN REAL_ARITH_TAC2] THEN
      MATCH_MP_TAC h1 THEN
      ASM_SIMP_TAC [SQRT_POS_LE, REAL_SUB_LE, (← HolLight.GSYM REAL_LE_SQUARE_ABS),
                   REAL_ABS_NUM],
      ALL_TAC] THEN
    MP_TAC (← HolLight.ISPECL [([[\x.  asn(x) + x * sqrt(&1 - x pow 2)]]),
      ([[\x. &2 * sqrt(&1 - x pow 2)]]),
      ([[-- &1]]), ([[&1]])] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR) THEN
    REWRITE_TAC [ASN_1, ASN_NEG_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC [SQRT_0, REAL_MUL_RZERO, REAL_ADD_RID] THEN
    REWRITE_TAC [h2] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN
      SIMP_TAC [REAL_CONTINUOUS_ON_ASN, IN_REAL_INTERVAL, REAL_BOUNDS_LE] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN
      REWRITE_TAC [REAL_CONTINUOUS_ON_ID] THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM o_DEF)] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC [REAL_CONTINUOUS_ON_SUB, REAL_CONTINUOUS_ON_POW,
               REAL_CONTINUOUS_ON_ID, REAL_CONTINUOUS_ON_CONST] THEN
      REWRITE_TAC [REAL_CONTINUOUS_ON_SQRT],
      REWRITE_TAC [IN_REAL_INTERVAL, REAL_BOUNDS_LT] THEN REPEAT STRIP_TAC THEN
      REAL_DIFF_TAC THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC [REAL_MUL_LID, REAL_POW_1, REAL_MUL_RID] THEN
      REWRITE_TAC [REAL_SUB_LZERO, REAL_MUL_RNEG, REAL_INV_MUL] THEN
      ASM_REWRITE_TAC [REAL_SUB_LT, ABS_SQUARE_LT_1] THEN
      MATCH_MP_TAC h3 THEN
      ASM_SIMP_TAC [ABS_SQUARE_LT_1, SQRT_POW_2, REAL_SUB_LE, REAL_LT_IMP_LE]])
  : ExceptT String IO thm).run
#eval AREA_UNIT_CBALL

#eval phrase 4
def AREA_CBALL : thm := keep "AREA_CBALL" fun _ => (do
  let h2 ← rr (← ExceptT.mk [[abs r * x <= r <=> abs r * x <= r * &1]])
  let h1 ← na (← ExceptT.mk [[dist(z,a + z) = norm a]])
  prove ([[!z:real^2 r. &0 <= r ==> measure(cball(z,r)) = pi * r pow 2]])
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC ([[r = &0]]) THENL
     [ASM_SIMP_TAC [CBALL_SING, REAL_POW_2, REAL_MUL_RZERO] THEN
      MATCH_MP_TAC MEASURE_UNIQUE THEN
      REWRITE_TAC [HAS_MEASURE_0, NEGLIGIBLE_SING],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[&0 < r]]) ASSUME_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    MP_TAC (← HolLight.ISPECL [([[cball(vec 0:real^2,&1)]]), ([[r:real]]), ([[z:real^2]]), ([[pi]])] HAS_MEASURE_AFFINITY) THEN
    REWRITE_TAC [HAS_MEASURE_MEASURABLE_MEASURE, MEASURABLE_CBALL,
                AREA_UNIT_CBALL] THEN
    ASM_REWRITE_TAC [real_abs, DIMINDEX_2] THEN
    DISCH_THEN (MP_TAC o HolLight.CONJUNCT2) THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
    DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
    REWRITE_TAC [IN_CBALL_0, IN_IMAGE] THEN REWRITE_TAC [IN_CBALL] THEN
    REWRITE_TAC [h1, NORM_MUL] THEN
    ONCE_REWRITE_TAC [h2] THEN
    ASM_SIMP_TAC [real_abs, REAL_LE_LMUL, SessionMultiLib.Vectors.dist] THEN X_GEN_TAC ([[w:real^2]]) THEN
    DISCH_TAC THEN EXISTS_TAC ([[inv(r) % (w - z):real^2]]) THEN
    ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_RINV] THEN
    CONJ_TAC THENL [NORM_ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [NORM_MUL, REAL_ABS_INV] THEN ASM_REWRITE_TAC [real_abs] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    ASM_SIMP_TAC [(← HolLight.GSYM real_div), REAL_LE_LDIV_EQ, REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC [NORM_SUB] THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval AREA_CBALL

#eval phrase 5
def AREA_BALL : thm := keep "AREA_BALL" fun _ => (do
  prove ([[!z:real^2 r. &0 <= r ==> measure(ball(z,r)) = pi * r pow 2]])
   (SIMP_TAC [(← HolLight.GSYM INTERIOR_CBALL), (← HolLight.GSYM AREA_CBALL)] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_INTERIOR THEN
    SIMP_TAC [BOUNDED_CBALL, NEGLIGIBLE_CONVEX_FRONTIER, CONVEX_CBALL])
  : ExceptT String IO thm).run
#eval AREA_BALL

/- ------------------------------------------------------------------------- -/
/- Volume of a ball too, just for fun.                                       -/
/- ------------------------------------------------------------------------- -/

#eval phrase 6
def VOLUME_CBALL : thm := keep "VOLUME_CBALL" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[abs x <= r ==> abs x <= abs r]])
  prove ([[!z:real^3 r. &0 <= r ==> measure(cball(z,r)) = &4 / &3 * pi * r pow 3]])
   (GEOM_ORIGIN_TAC ([[z:real^3]]) THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (← HolLight.INST_TYPE [((← ExceptT.mk (HolCore.Parser.parse_type "2")), (← ExceptT.mk (HolCore.Parser.parse_type "M"))), ((← ExceptT.mk (HolCore.Parser.parse_type "3")), (← ExceptT.mk (HolCore.Parser.parse_type "N")))] FUBINI_SIMPLE_COMPACT) THEN
    EXISTS_TAC ([[1]]) THEN
    SIMP_TAC [DIMINDEX_2, DIMINDEX_3, ARITH, COMPACT_CBALL, SLICE_CBALL] THEN
    REWRITE_TAC [VEC_COMPONENT, DROPOUT_0, REAL_SUB_RZERO] THEN
    ONCE_REWRITE_TAC [COND_RAND] THEN REWRITE_TAC [MEASURE_EMPTY] THEN
    SUBGOAL_THEN ([[!t. abs(t) <= r <=> t IN real_interval[--r,r] ]]) (fun th => REWRITE_TAC [th]) THENL [REWRITE_TAC [IN_REAL_INTERVAL] THEN REAL_ARITH_TAC2, ALL_TAC] THEN
    REWRITE_TAC [HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
    EXISTS_TAC ([[\t. pi * (r pow 2 - t pow 2)]]) THEN CONJ_TAC THENL
     [X_GEN_TAC ([[t:real]]) THEN REWRITE_TAC [IN_REAL_INTERVAL, REAL_BOUNDS_LE] THEN
      SIMP_TAC [AREA_CBALL, SQRT_POS_LE, REAL_SUB_LE, (← HolLight.GSYM REAL_LE_SQUARE_ABS),
               SQRT_POW_2, h1],
      ALL_TAC] THEN
    MP_TAC (← HolLight.ISPECL [([[\t. pi * (r pow 2 * t - &1 / &3 * t pow 3)]]),
      ([[\t. pi * (r pow 2 - t pow 2)]]),
      ([[--r:real]]), ([[r:real]])] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING,
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC REAL_RING])
  : ExceptT String IO thm).run
#eval VOLUME_CBALL

#eval phrase 7
def VOLUME_BALL : thm := keep "VOLUME_BALL" fun _ => (do
  prove ([[!z:real^3 r. &0 <= r ==> measure(ball(z,r)) =  &4 / &3 * pi * r pow 3]])
   (SIMP_TAC [(← HolLight.GSYM INTERIOR_CBALL), (← HolLight.GSYM VOLUME_CBALL)] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_INTERIOR THEN
    SIMP_TAC [BOUNDED_CBALL, NEGLIGIBLE_CONVEX_FRONTIER, CONVEX_CBALL])
  : ExceptT String IO thm).run
#eval VOLUME_BALL

end Hol100.Circle
