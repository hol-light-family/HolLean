/- File: Hol100/Cosine.lean
Translation of HOL Light's 100/cosine.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionMultiLib.Transcendentals
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Permutations SessionLibrary.Floor SessionLibrary.Iter SessionLibrary.Wo SessionLibrary.Products SessionLibrary.Frag SessionLibrary.Prime SessionLibrary.Card SessionLibrary.Matroids SessionMultiLib.Misc SessionLibrary.GroupTheory SessionMultiLib.Vectors SessionMultiLib.Metric SessionMultiLib.Determinants SessionMultiLib.Homology SessionMultiLib.Topology SessionMultiLib.Convex SessionMultiLib.Complexes SessionMultiLib.Paths SessionMultiLib.Polytope SessionMultiLib.Degree SessionMultiLib.Derivatives SessionMultiLib.Integration SessionMultiLib.Measure SessionMultiLib.Canal SessionMultiLib.Transcendentals
namespace Hol100.Cosine

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def rg (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_RING tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)
private def va (tm : term) : ExceptT String IO thm := ExceptT.mk (VECTOR_ARITH tm)

/- ========================================================================= -/
/- The law of cosines, of sines, and sum of angles of a triangle.            -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Multivariate/transcendentals.ml";;
#eval SessionMultiLib.Transcendentals.ensureTranscendentals

#eval phrase 2
#eval SessionMultiLib.Vectors.prioritize_vector

/- ------------------------------------------------------------------------- -/
/- Angle between vectors (always 0 <= angle <= pi).                          -/
/- ------------------------------------------------------------------------- -/

#eval phrase 3
def vangle : thm := keep "vangle" fun _ => new_definition
 [[vangle x y = if x = vec 0 \/ y = vec 0 then pi / &2
               else acs((x dot y) / (norm x * norm y))]]
#eval vangle

/- ------------------------------------------------------------------------- -/
/- Traditional geometric notion of angle (but always 0 <= theta <= pi).      -/
/- ------------------------------------------------------------------------- -/

#eval phrase 4
def angle : thm := keep "angle" fun _ => new_definition
 [[angle(a,b,c) = vangle (a - b) (c - b)]]
#eval angle

/- ------------------------------------------------------------------------- -/
/- Lemmas (more than we need for this result).                               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 5
def VANGLE : thm := keep "VANGLE" fun _ => (do
  prove ([[!x y:real^N. x dot y = norm(x) * norm(y) * cos(vangle x y)]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [vangle] THEN
    ASM_CASES_TAC ([[x:real^N = vec 0]]) THEN
    ASM_REWRITE_TAC [DOT_LZERO, NORM_0, REAL_MUL_LZERO] THEN
    ASM_CASES_TAC ([[y:real^N = vec 0]]) THEN
    ASM_REWRITE_TAC [DOT_RZERO, NORM_0, REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
    ONCE_REWRITE_TAC [AC REAL_MUL_AC ([[a * b * c:real = c * a * b]])] THEN
    ASM_SIMP_TAC [(← HolLight.GSYM REAL_EQ_LDIV_EQ), REAL_LT_MUL, NORM_POS_LT] THEN
    MATCH_MP_TAC (← HolLight.GSYM COS_ACS) THEN
    ASM_SIMP_TAC [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ, NORM_POS_LT, REAL_LT_MUL] THEN
    MP_TAC (← HolLight.SPECL [([[x:real^N]]), ([[y:real^N]])] NORM_CAUCHY_SCHWARZ_ABS) THEN
    REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval VANGLE

#eval phrase 6
def VANGLE_RANGE : thm := keep "VANGLE_RANGE" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[abs(x) <= a ==> -- &1 * a <= x /\ x <= &1 * a]])
  prove ([[!x y:real^N. &0 <= vangle x y /\ vangle x y <= pi]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [vangle] THEN COND_CASES_TAC THENL
     [MP_TAC PI_POS THEN REAL_ARITH_TAC2, ALL_TAC] THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [DE_MORGAN_THM]) THEN MATCH_MP_TAC ACS_BOUNDS THEN
    ASM_SIMP_TAC [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ, REAL_LT_MUL, NORM_POS_LT] THEN
    MATCH_MP_TAC h1 THEN
    REWRITE_TAC [NORM_CAUCHY_SCHWARZ_ABS])
  : ExceptT String IO thm).run
#eval VANGLE_RANGE

#eval phrase 7
def ORTHOGONAL_VANGLE : thm := keep "ORTHOGONAL_VANGLE" fun _ => (do
  prove ([[!x y:real^N. orthogonal x y <=> vangle x y = pi / &2]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [orthogonal, vangle] THEN
    ASM_CASES_TAC ([[x:real^N = vec 0]]) THEN ASM_REWRITE_TAC [DOT_LZERO] THEN
    ASM_CASES_TAC ([[y:real^N = vec 0]]) THEN ASM_REWRITE_TAC [DOT_RZERO] THEN
    EQ_TAC THENL
     [SIMP_TAC [real_div, REAL_MUL_LZERO] THEN DISCH_TAC THEN
      REWRITE_TAC [(← HolLight.GSYM real_div), (← HolLight.GSYM COS_PI2)] THEN
      MATCH_MP_TAC ACS_COS THEN MP_TAC PI_POS THEN REAL_ARITH_TAC2,
      MP_TAC (← HolLight.SPECL [([[x:real^N]]), ([[y:real^N]])] NORM_CAUCHY_SCHWARZ_ABS) THEN
      GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV) [(← HolLight.GSYM REAL_MUL_LID)] THEN
      REWRITE_TAC [(← HolLight.GSYM REAL_BOUNDS_LE)] THEN
      ONCE_REWRITE_TAC [(← HolLight.GSYM REAL_MUL_LNEG)] THEN
      ASM_SIMP_TAC [(← HolLight.GSYM REAL_LE_RDIV_EQ), (← HolLight.GSYM REAL_LE_LDIV_EQ),
                   REAL_LT_MUL, NORM_POS_LT] THEN
      STRIP_TAC THEN DISCH_THEN (MP_TAC o HolLight.AP_TERM ([[cos]])) THEN
      ASM_SIMP_TAC [COS_ACS, COS_PI2] THEN
      REWRITE_TAC [real_div, REAL_ENTIRE, REAL_INV_EQ_0] THEN
      ASM_REWRITE_TAC [NORM_EQ_0]])
  : ExceptT String IO thm).run
#eval ORTHOGONAL_VANGLE

#eval phrase 8
def VANGLE_EQ_PI : thm := keep "VANGLE_EQ_PI" fun _ => (do
  prove ([[!x y:real^N. vangle x y = pi ==> norm(x) % y + norm(y) % x = vec 0]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [([[x:real^N]]), ([[y:real^N]])] VANGLE) THEN
    ASM_REWRITE_TAC [COS_PI] THEN STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[x:real^N]]), ([[--y:real^N]])] NORM_CAUCHY_SCHWARZ_EQ) THEN
    REWRITE_TAC [NORM_NEG, DOT_RNEG, VECTOR_MUL_RNEG] THEN
    ASM_REWRITE_TAC [REAL_MUL_RNEG, REAL_NEG_NEG, REAL_MUL_RID] THEN
    VECTOR_ARITH_TAC)
  : ExceptT String IO thm).run
#eval VANGLE_EQ_PI

#eval phrase 9
def ANGLE_EQ_PI : thm := keep "ANGLE_EQ_PI" fun _ => (do
  let h2 ← va (← ExceptT.mk [[(B - A) + (C - B):real^N = C - A]])
  let h1 ← va (← ExceptT.mk [[a + x % (b - c) = vec 0 <=> a = x % (c - b)]])
  prove ([[!A B C:real^N. angle(A,B,C) = pi ==> dist(A,C) = dist(A,B) + dist(B,C)]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [angle] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP VANGLE_EQ_PI) THEN
    REWRITE_TAC [h1] THEN
    GEN_REWRITE_TAC (HolCore.Lib.funpow 3 HolLight.LAND_CONV) [NORM_SUB] THEN
    REWRITE_TAC [(← HolLight.GSYM NORM_TRIANGLE_EQ)] THEN
    REWRITE_TAC [h2] THEN
    REWRITE_TAC [SessionMultiLib.Vectors.dist, NORM_SUB])
  : ExceptT String IO thm).run
#eval ANGLE_EQ_PI

#eval phrase 10
def SIN_ANGLE_POS : thm := keep "SIN_ANGLE_POS" fun _ => (do
  prove ([[!A B C. &0 <= sin(angle(A,B,C))]])
   (SIMP_TAC [SIN_POS_PI_LE, angle, VANGLE_RANGE])
  : ExceptT String IO thm).run
#eval SIN_ANGLE_POS

#eval phrase 11
def ANGLE : thm := keep "ANGLE" fun _ => (do
  prove ([[!A B C. (A - C) dot (B - C) = dist(A,C) * dist(B,C) * cos(angle(A,C,B))]])
   (REWRITE_TAC [angle, SessionMultiLib.Vectors.dist, (← HolLight.GSYM VANGLE)])
  : ExceptT String IO thm).run
#eval ANGLE

#eval phrase 12
def ANGLE_REFL : thm := keep "ANGLE_REFL" fun _ => (do
  prove ([[!A B. angle(A,A,B) = pi / &2 /\
         angle(B,A,A) = pi / &2]])
   (REWRITE_TAC [angle, vangle, VECTOR_SUB_REFL])
  : ExceptT String IO thm).run
#eval ANGLE_REFL

#eval phrase 13
def ANGLE_REFL_MID : thm := keep "ANGLE_REFL_MID" fun _ => (do
  prove ([[!A B. ~(A = B) ==> angle(A,B,A) = &0]])
   (SIMP_TAC [angle, vangle, VECTOR_SUB_EQ, (← HolLight.GSYM NORM_POW_2), (← HolLight.GSYM REAL_POW_2),
             REAL_DIV_REFL, ACS_1, REAL_POW_EQ_0, ARITH, NORM_EQ_0])
  : ExceptT String IO thm).run
#eval ANGLE_REFL_MID

#eval phrase 14
def ANGLE_SYM : thm := keep "ANGLE_SYM" fun _ => (do
  prove ([[!A B C. angle(A,B,C) = angle(C,B,A)]])
   (REWRITE_TAC [angle, vangle, VECTOR_SUB_EQ, DISJ_SYM, REAL_MUL_SYM, DOT_SYM])
  : ExceptT String IO thm).run
#eval ANGLE_SYM

#eval phrase 15
def ANGLE_RANGE : thm := keep "ANGLE_RANGE" fun _ => (do
  prove ([[!A B C. &0 <= angle(A,B,C) /\ angle(A,B,C) <= pi]])
   (REWRITE_TAC [angle, VANGLE_RANGE])
  : ExceptT String IO thm).run
#eval ANGLE_RANGE

/- ------------------------------------------------------------------------- -/
/- The law of cosines.                                                       -/
/- ------------------------------------------------------------------------- -/

#eval phrase 16
def LAW_OF_COSINES : thm := keep "LAW_OF_COSINES" fun _ => (do
  prove ([[!A B C:real^N.
     dist(B,C) pow 2 = dist(A,B) pow 2 + dist(A,C) pow 2 -
                         &2 * dist(A,B) * dist(A,C) * cos(angle(B,A,C))]])
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [angle, (← HolLight.ONCE_REWRITE_RULE [NORM_SUB] SessionMultiLib.Vectors.dist), (← HolLight.GSYM VANGLE),
                NORM_POW_2] THEN
    VECTOR_ARITH_TAC)
  : ExceptT String IO thm).run
#eval LAW_OF_COSINES

/- ------------------------------------------------------------------------- -/
/- The law of sines.                                                         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 17
def LAW_OF_SINES : thm := keep "LAW_OF_SINES" fun _ => (do
  let h3 ← rg (← ExceptT.mk [[a * (&1 - x) * b = c * (&1 - y) * d <=>
    a * b - a * b * x = c * d - c * d * y]])
  let h2 ← rg (← ExceptT.mk [[~(a = &0) ==> a pow 2 * x = a pow 2 * y ==> x = y]])
  let h1 ← rr (← ExceptT.mk [[x + y = &1 ==> x = &1 - y]])
  prove ([[!A B C:real^N.
      sin(angle(A,B,C)) * dist(B,C) = sin(angle(B,A,C)) * dist(A,C)]])
   (REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC ([[2]]) THEN
    SIMP_TAC [SIN_ANGLE_POS, DIST_POS_LE, REAL_LE_MUL, ARITH] THEN
    REWRITE_TAC [REAL_POW_MUL, (← HolLight.MATCH_MP h1 (← HolLight.SPEC_ALL SIN_CIRCLE))] THEN
    ASM_CASES_TAC ([[A:real^N = B]]) THEN ASM_REWRITE_TAC [ANGLE_REFL, COS_PI2] THEN
    RULE_ASSUM_TAC (HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM VECTOR_SUB_EQ)]) THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [(← HolLight.GSYM NORM_EQ_0)]) THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h2) THEN
    ONCE_REWRITE_TAC [SessionMultiLib.Vectors.DIST_SYM] THEN REWRITE_TAC [(← HolLight.GSYM SessionMultiLib.Vectors.dist)] THEN
    GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [SessionMultiLib.Vectors.DIST_SYM] THEN
    REWRITE_TAC [h3] THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_POW_MUL), (← HolLight.GSYM ANGLE)] THEN
    REWRITE_TAC [REAL_POW_MUL, SessionMultiLib.Vectors.dist, NORM_POW_2] THEN
    REWRITE_TAC [DOT_LSUB, DOT_RSUB, DOT_SYM] THEN CONV_TAC REAL_RING)
  : ExceptT String IO thm).run
#eval LAW_OF_SINES

/- ------------------------------------------------------------------------- -/
/- Hence the sum of the angles of a triangle.                                -/
/- ------------------------------------------------------------------------- -/

#eval phrase 18
def TRIANGLE_ANGLE_SUM_LEMMA : thm := keep "TRIANGLE_ANGLE_SUM_LEMMA" fun _ => (do
  prove ([[!A B C:real^N. ~(A = B) /\ ~(A = C) /\ ~(B = C)
                  ==> cos(angle(B,A,C) + angle(A,B,C) + angle(B,C,A)) = -- &1]])
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [(← HolLight.GSYM VECTOR_SUB_EQ)] THEN
    REWRITE_TAC [(← HolLight.GSYM NORM_EQ_0)] THEN
    MP_TAC (← HolLight.ISPECL [([[A:real^N]]), ([[B:real^N]]), ([[C:real^N]])] LAW_OF_COSINES) THEN
    MP_TAC (← HolLight.ISPECL [([[B:real^N]]), ([[A:real^N]]), ([[C:real^N]])] LAW_OF_COSINES) THEN
    MP_TAC (← HolLight.ISPECL [([[C:real^N]]), ([[B:real^N]]), ([[A:real^N]])] LAW_OF_COSINES) THEN
    MP_TAC (← HolLight.ISPECL [([[A:real^N]]), ([[B:real^N]]), ([[C:real^N]])] LAW_OF_SINES) THEN
    MP_TAC (← HolLight.ISPECL [([[B:real^N]]), ([[A:real^N]]), ([[C:real^N]])] LAW_OF_SINES) THEN
    MP_TAC (← HolLight.ISPECL [([[B:real^N]]), ([[C:real^N]]), ([[A:real^N]])] LAW_OF_SINES) THEN
    REWRITE_TAC [COS_ADD, SIN_ADD, SessionMultiLib.Vectors.dist, NORM_SUB] THEN
    MAP_EVERY (fun t => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPEC t SIN_CIRCLE))) [([[angle(B:real^N,A,C)]]), ([[angle(A:real^N,B,C)]]), ([[angle(B:real^N,C,A)]])] THEN
    REWRITE_TAC [COS_ADD, SIN_ADD, ANGLE_SYM] THEN CONV_TAC REAL_RING)
  : ExceptT String IO thm).run
#eval TRIANGLE_ANGLE_SUM_LEMMA

#eval phrase 19
def COS_MINUS1_LEMMA : thm := keep "COS_MINUS1_LEMMA" fun _ => (do
  let h3 ← ar (← ExceptT.mk [[n < 3 /\ ~(n = 0) /\ ~(n = 2) ==> n = 1]])
  let h2 ← rg (← ExceptT.mk [[n = &1 ==> n * p = p]])
  let h1 ← rr (← ExceptT.mk [[&0 < p ==> ~(p < &0) /\ ~(p = &0)]])
  prove ([[!x. cos(x) = -- &1 /\ &0 <= x /\ x < &3 * pi ==> x = pi]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[?n. integer n /\ x = n * pi]]) (X_CHOOSE_THEN ([[nn:real]]) (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
    REWRITE_TAC [(← HolLight.GSYM SIN_EQ_0)] THENL
     [MP_TAC (← HolLight.SPEC ([[x:real]]) SIN_CIRCLE) THEN ASM_REWRITE_TAC [] THEN
      CONV_TAC REAL_RING,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[?n. nn = &n]]) (X_CHOOSE_THEN ([[n:num]]) SUBST_ALL_TAC) THENL
     [FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [REAL_MUL_POS_LE]) THEN
      SIMP_TAC [PI_POS, h1] THEN
      ASM_MESON_TAC [INTEGER_POS, REAL_LT_LE],
      ALL_TAC] THEN
    MATCH_MP_TAC h2 THEN
    REWRITE_TAC [REAL_OF_NUM_EQ] THEN
    MATCH_MP_TAC h3 THEN
    RULE_ASSUM_TAC (Session.SIMP_RULE [REAL_LT_RMUL_EQ, PI_POS, REAL_OF_NUM_LT]) THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    REPEAT (POP_ASSUM MP_TAC) THEN SIMP_TAC [COS_0, REAL_MUL_LZERO, COS_NPI] THEN
    REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval COS_MINUS1_LEMMA

#eval phrase 20
def TRIANGLE_ANGLE_SUM : thm := keep "TRIANGLE_ANGLE_SUM" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[&0 <= x /\ x <= p /\ &0 <= y /\ y <= p /\ &0 <= z /\ z <= p /\
    ~(x = p /\ y = p /\ z = p)
    ==> x + y + z < &3 * p]])
  prove ([[!A B C:real^N. ~(A = B) /\ ~(A = C) /\ ~(B = C)
                  ==> angle(B,A,C) + angle(A,B,C) + angle(B,C,A) = pi]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC COS_MINUS1_LEMMA THEN
    ASM_SIMP_TAC [TRIANGLE_ANGLE_SUM_LEMMA, REAL_LE_ADD, ANGLE_RANGE] THEN
    MATCH_MP_TAC h1 THEN
    ASM_SIMP_TAC [ANGLE_RANGE] THEN REPEAT STRIP_TAC THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP ANGLE_EQ_PI)) THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolLight.RAND_CONV [(← HolLight.GSYM VECTOR_SUB_EQ)])) THEN
    REWRITE_TAC [(← HolLight.GSYM NORM_EQ_0), SessionMultiLib.Vectors.dist, NORM_SUB] THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval TRIANGLE_ANGLE_SUM

end Hol100.Cosine
