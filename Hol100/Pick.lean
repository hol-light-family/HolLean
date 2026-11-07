/- File: Hol100/Pick.lean
Translation of HOL Light's 100/pick.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionMultiLib.Polytope
import SessionMultiLib.Measure
import SessionMultiLib.MoreTop
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Permutations SessionLibrary.Wo SessionLibrary.Products SessionLibrary.Floor SessionLibrary.Binomial SessionLibrary.Frag SessionLibrary.Iter SessionLibrary.Prime SessionLibrary.Card SessionLibrary.Matroids SessionMultiLib.Misc SessionLibrary.GroupTheory SessionMultiLib.Vectors SessionMultiLib.Metric SessionMultiLib.Determinants SessionMultiLib.Homology SessionMultiLib.Topology SessionMultiLib.Convex SessionMultiLib.Complexes SessionMultiLib.Paths SessionMultiLib.Polytope SessionMultiLib.Degree SessionMultiLib.Derivatives SessionMultiLib.Integration SessionMultiLib.Measure SessionMultiLib.Canal SessionMultiLib.Transcendentals SessionMultiLib.RealAnalysis SessionMultiLib.MoreTop
namespace Hol100.Pick

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def ms (ths : List thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (MESON ths tm)
private def na (tm : term) : ExceptT String IO thm := ExceptT.mk (NORM_ARITH tm)
private def nc (tm : term) : ExceptT String IO thm := ExceptT.mk (num_CONV tm)
private def rf (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_FIELD tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)
private def sr (tm : term) : ExceptT String IO thm := ExceptT.mk (SET_RULE tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)
private def va (tm : term) : ExceptT String IO thm := ExceptT.mk (VECTOR_ARITH tm)

/- ========================================================================= -/
/- Pick's theorem.                                                           -/
/- ========================================================================= -/

/-- `CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) n`. -/
private def gsimp (n : Int) (ths : List thm) : HolCore.Tactics.tactic := HolLight.tactic_of do
  pure (CONV_TAC (← ExceptT.mk (HolCore.Simp.GEN_SIMPLIFY_CONV Session.B (TOP_DEPTH_SQCONV Session.B)
    (← ExceptT.mk (Session.basic_ss [])) n ths)))

#eval phrase 1
-- needs "Multivariate/polytope.ml";;
#eval SessionMultiLib.Polytope.ensurePolytope

#eval phrase 2
-- needs "Multivariate/measure.ml";;
#eval SessionMultiLib.Measure.ensureMeasure

#eval phrase 3
-- needs "Multivariate/moretop.ml";;
#eval SessionMultiLib.MoreTop.ensureMoreTop

#eval phrase 4
#eval Session.prioritize_real

/- ------------------------------------------------------------------------- -/
/- Misc lemmas.                                                              -/
/- ------------------------------------------------------------------------- -/

#eval phrase 5
def COLLINEAR_IMP_NEGLIGIBLE : thm := keep "COLLINEAR_IMP_NEGLIGIBLE" fun _ => (do
  prove ([[!s:real^2->bool. collinear s ==> negligible s]])
   (REWRITE_TAC [COLLINEAR_AFFINE_HULL] THEN
    MESON_TAC [NEGLIGIBLE_AFFINE_HULL_2, NEGLIGIBLE_SUBSET])
  : ExceptT String IO thm).run
#eval COLLINEAR_IMP_NEGLIGIBLE

#eval phrase 6
def CONVEX_HULL_3_0 : thm := keep "CONVEX_HULL_3_0" fun _ => (do
  let h1 ← sr (← ExceptT.mk [[{c,a,b} = {a,b,c}]])
  prove ([[!a b:real^N.
        convex hull {vec 0,a,b} =
        {x % a + y % b | &0 <= x /\ &0 <= y /\ x + y <= &1}]])
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [h1] THEN
    REWRITE_TAC [CONVEX_HULL_3, EXTENSION, IN_ELIM_THM] THEN
    X_GEN_TAC ([[y:real^N]]) THEN
    AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC ([[x:real]]) THEN
    AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC ([[y:real]]) THEN
    REWRITE_TAC [VECTOR_MUL_RZERO, VECTOR_ADD_RID] THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THENL
     [ASM_ARITH_TAC, EXISTS_TAC ([[&1 - x - y]]) THEN ASM_ARITH_TAC])
  : ExceptT String IO thm).run
#eval CONVEX_HULL_3_0

#eval phrase 7
def INTERIOR_CONVEX_HULL_3_0 : thm := keep "INTERIOR_CONVEX_HULL_3_0" fun _ => (do
  let h3 ← rr (← ExceptT.mk [[x + y + z = &1 <=> &1 - x - y = z]])
  let h2 ← tt (← ExceptT.mk [[a /\ x = &1 /\ b <=> x = &1 /\ a /\ b]])
  let h1 ← sr (← ExceptT.mk [[{c,a,b} = {a,b,c}]])
  prove ([[!a b:real^2.
        ~(collinear {vec 0,a,b})
        ==> interior(convex hull {vec 0,a,b}) =
              {x % a + y % b | &0 < x /\ &0 < y /\ x + y < &1}]])
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [h1] THEN
    STRIP_TAC THEN ASM_SIMP_TAC [INTERIOR_CONVEX_HULL_3] THEN
    REWRITE_TAC [h2] THEN
    REWRITE_TAC [VECTOR_MUL_RZERO, VECTOR_ADD_RID] THEN
    REWRITE_TAC [h3, UNWIND_THM1] THEN
    REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
    GEN_TAC THEN REPEAT (AP_TERM_TAC THEN ABS_TAC) THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_REAL_ARITH_TAC)
  : ExceptT String IO thm).run
#eval INTERIOR_CONVEX_HULL_3_0

#eval phrase 8
def MEASURE_CONVEX_HULL_2_TRIVIAL : thm := keep "MEASURE_CONVEX_HULL_2_TRIVIAL" fun _ => (do
  prove ([[(!a:real^2. measure(convex hull {a}) = &0) /\
   (!a b:real^2. measure(convex hull {a,b}) = &0)]])
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MEASURE_EQ_0 THEN
    MATCH_MP_TAC COLLINEAR_IMP_NEGLIGIBLE THEN
    REWRITE_TAC [(← HolLight.GSYM SEGMENT_CONVEX_HULL), CONVEX_HULL_SING] THEN
    REWRITE_TAC [COLLINEAR_SING, COLLINEAR_SEGMENT])
  : ExceptT String IO thm).run
#eval MEASURE_CONVEX_HULL_2_TRIVIAL

#eval phrase 9
def NEGLIGIBLE_SEGMENT_2 : thm := keep "NEGLIGIBLE_SEGMENT_2" fun _ => (do
  prove ([[!a b:real^2. negligible(segment[a,b])]])
   (SIMP_TAC [COLLINEAR_IMP_NEGLIGIBLE, COLLINEAR_SEGMENT])
  : ExceptT String IO thm).run
#eval NEGLIGIBLE_SEGMENT_2

/- ------------------------------------------------------------------------- -/
/- Decomposing an additive function on a triangle.                           -/
/- ------------------------------------------------------------------------- -/

#eval phrase 10
def TRIANGLE_DECOMPOSITION : thm := keep "TRIANGLE_DECOMPOSITION" fun _ => (do
  prove ([[!a b c d:real^2.
        d IN convex hull {a,b,c}
        ==> (convex hull {a,b,c} =
             convex hull {d,b,c} UNION
             convex hull {d,a,c} UNION
             convex hull {d,a,b})]])
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC [UNION_SUBSET] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [SUBSET] THEN X_GEN_TAC ([[x:real^2]]) THEN DISCH_TAC THEN
      MP_TAC (← HolLight.ISPECL [([[{a:real^2,b,c}]]), ([[d:real^2]]), ([[x:real^2]])] IN_CONVEX_HULL_EXCHANGE) THEN
      ASM_REWRITE_TAC [EXISTS_IN_INSERT, NOT_IN_EMPTY, IN_UNION] THEN
      REPEAT (MATCH_MP_TAC MONO_OR THEN CONJ_TAC) THEN
      SPEC_TAC (([[x:real^2]]), ([[x:real^2]])) THEN REWRITE_TAC [(← HolLight.GSYM SUBSET)] THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC [],
      SIMP_TAC [SUBSET_HULL, CONVEX_CONVEX_HULL] THEN
      REWRITE_TAC [INSERT_SUBSET, EMPTY_SUBSET] THEN
      ASM_SIMP_TAC [HULL_INC, IN_INSERT]])
  : ExceptT String IO thm).run
#eval TRIANGLE_DECOMPOSITION

#eval phrase 11
def TRIANGLE_ADDITIVE_DECOMPOSITION : thm := keep "TRIANGLE_ADDITIVE_DECOMPOSITION" fun _ => (do
  let h1 ← sr (← ExceptT.mk [[s SUBSET u /\ t SUBSET u ==> (s INTER t) SUBSET u]])
  prove ([[!f:(real^2->bool)->real a b c d.
        (!s t. compact s /\ compact t
               ==> f(s UNION t) = f(s) + f(t) - f(s INTER t)) /\
        ~(a = b) /\ ~(a = c) /\ ~(b = c) /\
        ~affine_dependent {a,b,c} /\ d IN convex hull {a,b,c}
        ==> f(convex hull {a,b,c}) =
            (f(convex hull {a,b,d}) +
             f(convex hull {a,c,d}) +
             f(convex hull {b,c,d})) -
            (f(convex hull {a,d}) +
             f(convex hull {b,d}) +
             f(convex hull {c,d})) +
            f(convex hull {d})]])
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (SUBST1_TAC o HolLight.MATCH_MP TRIANGLE_DECOMPOSITION) THEN
    HolLight.ASM (gsimp 5) [COMPACT_UNION, COMPACT_INTER, COMPACT_CONVEX_HULL,
                 FINITE_IMP_COMPACT, FINITE_INSERT, FINITE_EMPTY,
                 UNION_OVER_INTER] THEN
    MP_TAC (← HolLight.ISPECL [([[{a:real^2,b,c}]]), ([[d:real^2]])] CONVEX_HULL_EXCHANGE_INTER) THEN
    ASM_REWRITE_TAC [] THEN
    SIMP_TAC [INSERT_SUBSET, EMPTY_SUBSET, IN_INSERT, NOT_IN_EMPTY,
             h1] THEN
    ASM_REWRITE_TAC [INSERT_INTER, IN_INSERT, NOT_IN_EMPTY, INTER_EMPTY] THEN
    DISCH_TAC THEN REWRITE_TAC [INSERT_AC] THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval TRIANGLE_ADDITIVE_DECOMPOSITION

/- ------------------------------------------------------------------------- -/
/- Vectors all of whose coordinates are integers.                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 12
def integral_vector : thm := keep "integral_vector" fun _ => define
 [[integral_vector(x:real^N) <=>
        !i. 1 <= i /\ i <= dimindex(:N) ==> integer(x$i)]]
#eval integral_vector

#eval phrase 13
def INTEGRAL_VECTOR_VEC : thm := keep "INTEGRAL_VECTOR_VEC" fun _ => (do
  prove ([[!n. integral_vector(vec n)]])
   (REWRITE_TAC [integral_vector, VEC_COMPONENT, INTEGER_CLOSED])
  : ExceptT String IO thm).run
#eval INTEGRAL_VECTOR_VEC

#eval phrase 14
def INTEGRAL_VECTOR_STDBASIS : thm := keep "INTEGRAL_VECTOR_STDBASIS" fun _ => (do
  prove ([[!i. integral_vector(basis i:real^N)]])
   (REWRITE_TAC [integral_vector] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC [BASIS_COMPONENT] THEN
    COND_CASES_TAC THEN REWRITE_TAC [INTEGER_CLOSED])
  : ExceptT String IO thm).run
#eval INTEGRAL_VECTOR_STDBASIS

#eval phrase 15
def INTEGRAL_VECTOR_ADD : thm := keep "INTEGRAL_VECTOR_ADD" fun _ => (do
  prove ([[!x y:real^N.
        integral_vector x /\ integral_vector y ==> integral_vector(x + y)]])
   (SIMP_TAC [integral_vector, VECTOR_ADD_COMPONENT, INTEGER_CLOSED])
  : ExceptT String IO thm).run
#eval INTEGRAL_VECTOR_ADD

#eval phrase 16
def INTEGRAL_VECTOR_SUB : thm := keep "INTEGRAL_VECTOR_SUB" fun _ => (do
  prove ([[!x y:real^N.
        integral_vector x /\ integral_vector y ==> integral_vector(x - y)]])
   (SIMP_TAC [integral_vector, VECTOR_SUB_COMPONENT, INTEGER_CLOSED])
  : ExceptT String IO thm).run
#eval INTEGRAL_VECTOR_SUB

#eval phrase 17
def INTEGRAL_VECTOR_ADD_LCANCEL : thm := keep "INTEGRAL_VECTOR_ADD_LCANCEL" fun _ => (do
  let h1 ← va (← ExceptT.mk [[(x + y) - x:real^N = y]])
  prove ([[!x y:real^N.
        integral_vector x ==> (integral_vector(x + y) <=> integral_vector y)]])
   (MESON_TAC [INTEGRAL_VECTOR_ADD, INTEGRAL_VECTOR_SUB,
              h1])
  : ExceptT String IO thm).run
#eval INTEGRAL_VECTOR_ADD_LCANCEL

#eval phrase 18
def FINITE_BOUNDED_INTEGER_POINTS : thm := keep "FINITE_BOUNDED_INTEGER_POINTS" fun _ => (do
  prove ([[!s:real^N->bool. bounded s ==> FINITE {x | x IN s /\ integral_vector x}]])
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [([[a:real^N]]), ([[b:real^N]])] THEN
    REWRITE_TAC [SUBSET, IN_INTERVAL, integral_vector] THEN DISCH_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC ([[{x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                       ==> integer(x$i) /\
                           (a:real^N)$i <= x$i /\ x$i <= (b:real^N)$i}]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_CART THEN REWRITE_TAC [FINITE_INTSEG],
      HolLight.ASM SET_TAC []])
  : ExceptT String IO thm).run
#eval FINITE_BOUNDED_INTEGER_POINTS

#eval phrase 19
def FINITE_TRIANGLE_INTEGER_POINTS : thm := keep "FINITE_TRIANGLE_INTEGER_POINTS" fun _ => (do
  prove ([[!a b c:real^N. FINITE {x | x IN convex hull {a,b,c} /\ integral_vector x}]])
   (REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_BOUNDED_INTEGER_POINTS THEN
    SIMP_TAC [FINITE_IMP_BOUNDED_CONVEX_HULL, FINITE_INSERT, FINITE_EMPTY])
  : ExceptT String IO thm).run
#eval FINITE_TRIANGLE_INTEGER_POINTS

/- ------------------------------------------------------------------------- -/
/- Properties of a basis for the integer lattice.                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 20
def LINEAR_INTEGRAL_VECTOR : thm := keep "LINEAR_INTEGRAL_VECTOR" fun _ => (do
  prove ([[!f:real^N->real^N.
        linear f
        ==> ((!x. integral_vector x ==> integral_vector(f x)) <=>
             (!i j. 1 <= i /\ i <= dimindex(:N) /\
                    1 <= j /\ j <= dimindex(:N)
                    ==> integer(matrix f$i$j)))]])
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (fun th => HolLight.tactic_of do
        pure (ONCE_REWRITE_TAC [(← HolLight.GSYM (← HolLight.MATCH_MP MATRIX_WORKS th))])) THEN
    ABBREV_TAC ([[M = matrix(f:real^N->real^N)]]) THEN
    SIMP_TAC [integral_vector, matrix_vector_mul, LAMBDA_BETA] THEN
    EQ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
     [MAP_EVERY X_GEN_TAC [([[i:num]]), ([[j:num]])] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[basis j:real^N]])) THEN
      REWRITE_TAC [(← HolLight.GSYM integral_vector), INTEGRAL_VECTOR_STDBASIS] THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC ([[i:num]])) THEN ASM_REWRITE_TAC [] THEN
      ASM_SIMP_TAC [BASIS_COMPONENT, COND_RAND, COND_RATOR] THEN
      ASM_REWRITE_TAC [REAL_MUL_RZERO, SUM_DELTA, IN_NUMSEG, REAL_MUL_RID],
      X_GEN_TAC ([[x:real^N]]) THEN DISCH_TAC THEN
      X_GEN_TAC ([[i:num]]) THEN STRIP_TAC THEN
      MATCH_MP_TAC INTEGER_SUM THEN
      ASM_SIMP_TAC [INTEGER_CLOSED, IN_NUMSEG]])
  : ExceptT String IO thm).run
#eval LINEAR_INTEGRAL_VECTOR

#eval phrase 21
def INTEGRAL_BASIS_UNIMODULAR : thm := keep "INTEGRAL_BASIS_UNIMODULAR" fun _ => (do
  let h1 ← tt (← ExceptT.mk [[(b ==> a) /\ b ==> a /\ b]])
  prove ([[!f:real^N->real^N.
        linear f /\ IMAGE f integral_vector = integral_vector
        ==> abs(det(matrix f)) = &1]])
   (REWRITE_TAC [(← HolLight.GSYM SUBSET_ANTISYM_EQ), SUBSET, FORALL_IN_IMAGE] THEN
    REWRITE_TAC [IN_IMAGE] THEN REWRITE_TAC [IN] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[!i j. 1 <= i /\ i <= dimindex(:N) /\
          1 <= j /\ j <= dimindex(:N)
          ==> integer(matrix(f:real^N->real^N)$i$j)]]) ASSUME_TAC THENL [ASM_SIMP_TAC [(← HolLight.GSYM LINEAR_INTEGRAL_VECTOR)], ALL_TAC] THEN
    SUBGOAL_THEN ([[?g:real^N->real^N. linear g /\ (!x. g(f x) = x) /\ (!y. f(g y) = y)]]) STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE THEN ASM_SIMP_TAC [] THEN
      MATCH_MP_TAC h1 THEN CONJ_TAC THENL
       [ASM_MESON_TAC [LINEAR_SURJECTIVE_IMP_INJECTIVE], ALL_TAC] THEN
      SUBGOAL_THEN ([[!y. y:real^N IN span(IMAGE f (:real^N))]]) MP_TAC THENL
       [ALL_TAC, ASM_SIMP_TAC [SPAN_LINEAR_IMAGE, SPAN_UNIV] THEN SET_TAC []] THEN
      GEN_TAC THEN GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM BASIS_EXPANSION)] THEN
      MATCH_MP_TAC SPAN_VSUM THEN REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG] THEN
      X_GEN_TAC ([[k:num]]) THEN STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
      MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC [IN_IMAGE, IN_UNIV] THEN
      ASM_MESON_TAC [INTEGRAL_VECTOR_STDBASIS],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!i j. 1 <= i /\ i <= dimindex(:N) /\
          1 <= j /\ j <= dimindex(:N)
          ==> integer(matrix(g:real^N->real^N)$i$j)]]) ASSUME_TAC THENL
     [ASM_SIMP_TAC [(← HolLight.GSYM LINEAR_INTEGRAL_VECTOR)] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[det(matrix(f:real^N->real^N)) * det(matrix(g:real^N->real^N)) =
    det(matrix(I:real^N->real^N))]]) MP_TAC THENL
     [ASM_SIMP_TAC [(← HolLight.GSYM DET_MUL), (← HolLight.GSYM MATRIX_COMPOSE)] THEN
      REPEAT AP_TERM_TAC THEN ASM_REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM],
      ALL_TAC] THEN
    DISCH_THEN (MP_TAC o HolLight.AP_TERM ([[abs:real->real]])) THEN
    REWRITE_TAC [MATRIX_I, DET_I, REAL_ABS_NUM] THEN
    ASM_SIMP_TAC [INTEGER_DET, INTEGER_ABS_MUL_EQ_1])
  : ExceptT String IO thm).run
#eval INTEGRAL_BASIS_UNIMODULAR

/- ------------------------------------------------------------------------- -/
/- Pick's theorem for an elementary triangle.                                -/
/- ------------------------------------------------------------------------- -/

#eval phrase 22
def PICK_ELEMENTARY_TRIANGLE_0 : thm := keep "PICK_ELEMENTARY_TRIANGLE_0" fun _ => (do
  let h8 ← va (← ExceptT.mk [[x % a + y % b = b <=> x % a + (y - &1) % b = vec 0]])
  let h7 ← va (← ExceptT.mk [[x % a + y % b = a <=> (x - &1) % a + y % b = vec 0]])
  let h6 ← va (← ExceptT.mk [[(&1 - u) % a + (&1 - v) % b = (a + b) - (u % a + v % b)]])
  let h5 ← rr (← ExceptT.mk [[u - x:real = y <=> u = x + y]])
  let h4 ← va (← ExceptT.mk [[(x % a + y % b) - (u % a + v % b) = (x - u) % a + (y - v) % b]])
  let h3 ← tt (← ExceptT.mk [[b' /\ (b' ==> b) /\ (a \/ a') /\ (c \/ c' ==> x)
    ==> (a /\ b ==> c) ==> (a' /\ b' ==> c') ==> x]])
  let h2 ← sr (← ExceptT.mk [[a IN s ==> s SUBSET t ==> a IN t]])
  let h1 ← sr (← ExceptT.mk [[{c,a,b} = {c,b,a}]])
  prove ([[!a b:real^2.
        {x | x IN convex hull {vec 0,a,b} /\ integral_vector x} = {vec 0,a,b}
        ==> measure(convex hull {vec 0,a,b}) =
               if collinear {vec 0,a,b} then &0 else &1 / &2]])
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [MEASURE_EQ_0, COLLINEAR_IMP_NEGLIGIBLE,
                 COLLINEAR_CONVEX_HULL_COLLINEAR] THEN
    POP_ASSUM MP_TAC THEN
    MAP_EVERY (fun t => ASM_CASES_TAC t THENL [ASM_REWRITE_TAC [INSERT_AC, COLLINEAR_2], ALL_TAC]) [([[a:real^2 = vec 0]]), ([[b:real^2 = vec 0]]), ([[a:real^2 = b]])] THEN
    DISCH_TAC THEN SUBGOAL_THEN ([[independent {a:real^2,b}]]) ASSUME_TAC THENL
     [UNDISCH_TAC ([[~collinear{vec 0:real^2, a, b}]]) THEN
      REWRITE_TAC [independent, CONTRAPOS_THM] THEN
      REWRITE_TAC [dependent, EXISTS_IN_INSERT, NOT_IN_EMPTY] THEN STRIP_TAC THENL
       [ONCE_REWRITE_TAC [h1], ALL_TAC] THEN
      ASM_SIMP_TAC [COLLINEAR_3_AFFINE_HULL] THEN
      ASM_SIMP_TAC [AFFINE_HULL_EQ_SPAN, HULL_INC, IN_INSERT] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h2) THEN
      MATCH_MP_TAC SPAN_MONO THEN SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[span{a,b} = (:real^2)]]) ASSUME_TAC THENL
     [MP_TAC (← HolLight.ISPECL [([[(:real^2)]]), ([[{a:real^2,b}]])] CARD_EQ_DIM) THEN
      ASM_REWRITE_TAC [SUBSET_UNIV, SUBSET, EXTENSION, IN_ELIM_THM, IN_UNIV] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC [HAS_SIZE, FINITE_INSERT, FINITE_EMPTY] THEN
      SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY, IN_INSERT] THEN
      ASM_REWRITE_TAC [NOT_IN_EMPTY, DIM_UNIV, DIMINDEX_2, ARITH],
      ALL_TAC] THEN
    REWRITE_TAC [(← HolLight.GSYM SUBSET_ANTISYM_EQ), SUBSET, FORALL_IN_INSERT,
                FORALL_IN_GSPEC] THEN
    REWRITE_TAC [IN_ELIM_THM, NOT_IN_EMPTY, IN_INSERT] THEN STRIP_TAC THEN
    MP_TAC (← HolLight.ISPEC ([[\x:real^2. transp(vector[a;b]:real^2^2) ** x]]) INTEGRAL_BASIS_UNIMODULAR) THEN
    REWRITE_TAC [MATRIX_OF_MATRIX_VECTOR_MUL, MATRIX_VECTOR_MUL_LINEAR] THEN
    REWRITE_TAC [DET_2, MEASURE_TRIANGLE, VECTOR_2, DET_TRANSP, VEC_COMPONENT] THEN
    ANTS_TAC THENL [ALL_TAC, REAL_ARITH_TAC2] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [IN] THEN
      SIMP_TAC [LINEAR_INTEGRAL_VECTOR, MATRIX_VECTOR_MUL_LINEAR, LAMBDA_BETA,
               MATRIX_OF_MATRIX_VECTOR_MUL, transp, DIMINDEX_2, ARITH] THEN
      MAP_EVERY UNDISCH_TAC [([[integral_vector(a:real^2)]]), ([[integral_vector(b:real^2)]])] THEN
      REWRITE_TAC [integral_vector, IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC [IMP_IMP, FORALL_2, DIMINDEX_2, VECTOR_2] THEN
      REWRITE_TAC [CONJ_ACI],
      ALL_TAC] THEN
    REWRITE_TAC [IN_IMAGE] THEN REWRITE_TAC [IN] THEN
    X_GEN_TAC ([[x:real^2]]) THEN DISCH_TAC THEN REWRITE_TAC [EXISTS_VECTOR_2] THEN
    REWRITE_TAC [MATRIX_VECTOR_COLUMN, TRANSP_TRANSP] THEN
    REWRITE_TAC [DIMINDEX_2, VSUM_2, VECTOR_2, integral_vector, FORALL_2] THEN
    SUBGOAL_THEN ([[(x:real^2) IN span{a,b}]]) MP_TAC THENL
     [ASM_REWRITE_TAC [IN_UNIV], ALL_TAC] THEN
    REWRITE_TAC [SPAN_2, IN_UNIV, IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[u:real]]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[v:real]]) THEN
    DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (MP_TAC o HolLight.SPEC ([[frac u % a + frac v % b:real^2]])) THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[(&1 - frac u) % a + (&1 - frac v) % b:real^2]])) THEN
    MATCH_MP_TAC h3 THEN
    REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN ([[integral_vector(floor u % a + floor v % b:real^2)]]) MP_TAC THENL
       [MAP_EVERY UNDISCH_TAC [([[integral_vector(a:real^2)]]), ([[integral_vector(b:real^2)]])] THEN
        SIMP_TAC [integral_vector, DIMINDEX_2, FORALL_2,
                 VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT] THEN
        SIMP_TAC [FLOOR, INTEGER_CLOSED],
        UNDISCH_TAC ([[integral_vector(x:real^2)]]) THEN REWRITE_TAC [IMP_IMP] THEN
        DISCH_THEN (MP_TAC o HolLight.MATCH_MP INTEGRAL_VECTOR_SUB) THEN
        ASM_REWRITE_TAC [h4] THEN
        MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN BINOP_TAC THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC [h5] THEN
        REWRITE_TAC [(← HolLight.GSYM FLOOR_FRAC)]],
      REWRITE_TAC [h6] THEN
      ASM_SIMP_TAC [INTEGRAL_VECTOR_ADD, INTEGRAL_VECTOR_SUB],
      REWRITE_TAC [CONVEX_HULL_3_0, IN_ELIM_THM] THEN
      SUBGOAL_THEN ([[&0 <= frac u /\ &0 <= frac v /\ frac u + frac v <= &1 \/
      &0 <= &1 - frac u /\ &0 <= &1 - frac v /\
      (&1 - frac u) + (&1 - frac v) <= &1]]) MP_TAC THENL
       [MP_TAC (← HolLight.SPEC ([[u:real]]) FLOOR_FRAC) THEN
        MP_TAC (← HolLight.SPEC ([[v:real]]) FLOOR_FRAC) THEN REAL_ARITH_TAC2,
        MESON_TAC []],
      REWRITE_TAC [h7,
        h8] THEN
      ASM_SIMP_TAC [INDEPENDENT_2, (← HolLight.GSYM REAL_FRAC_EQ_0)] THEN
      MP_TAC (← HolLight.SPEC ([[u:real]]) FLOOR_FRAC) THEN
      MP_TAC (← HolLight.SPEC ([[v:real]]) FLOOR_FRAC) THEN REAL_ARITH_TAC2])
  : ExceptT String IO thm).run
#eval PICK_ELEMENTARY_TRIANGLE_0

#eval phrase 23
def PICK_ELEMENTARY_TRIANGLE : thm := keep "PICK_ELEMENTARY_TRIANGLE" fun _ => (do
  let h1 ← sr (← ExceptT.mk [[s = t ==> (!x. x IN s <=> x IN t) /\ s = t]])
  prove ([[!a b c:real^2.
        {x | x IN convex hull {a,b,c} /\ integral_vector x} = {a,b,c}
        ==> measure(convex hull {a,b,c}) =
               if collinear {a,b,c} then &0 else &1 / &2]])
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o HolLight.MATCH_MP h1) THEN
    REWRITE_TAC [IMP_CONJ] THEN DISCH_THEN (MP_TAC o HolLight.SPEC ([[a:real^2]])) THEN
    REWRITE_TAC [IN_INSERT, IN_ELIM_THM] THEN
    GEOM_ORIGIN_TAC ([[a:real^2]]) THEN
    SIMP_TAC [INTEGRAL_VECTOR_ADD_LCANCEL, VECTOR_ADD_RID] THEN
    REWRITE_TAC [PICK_ELEMENTARY_TRIANGLE_0])
  : ExceptT String IO thm).run
#eval PICK_ELEMENTARY_TRIANGLE

/- ------------------------------------------------------------------------- -/
/- Our form of Pick's theorem holds degenerately for a flat triangle.        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 24
def PICK_TRIANGLE_FLAT : thm := keep "PICK_TRIANGLE_FLAT" fun _ => (do
  let h4 ← sr (← ExceptT.mk [[{x | x IN s /\ P x} INTER {x | x IN t /\ P x} =
                          {x | x IN (s INTER t) /\ P x}]])
  let h3 ← ar (← ExceptT.mk [[z:num <= x /\ z = 1 ==> x + y = (x + y) - z + 1]])
  let h2 ← sr (← ExceptT.mk [[{x | x IN (s UNION t) /\ P x} =
     {x | x IN s /\ P x} UNION {x | x IN t /\ P x}]])
  let h1 ← rr (← ExceptT.mk [[&0 = c - (a + b + c) / &2 + &1 / &2 <=> a + b = c + &1]])
  prove ([[!a b c:real^2.
        integral_vector a /\ integral_vector b /\ integral_vector c /\
        c IN segment[a,b]
        ==> measure(convex hull {a,b,c}) =
             &(CARD {x | x IN convex hull {a,b,c} /\ integral_vector x}) -
             (&(CARD {x | x IN convex hull {b,c} /\ integral_vector x}) +
              &(CARD {x | x IN convex hull {a,c} /\ integral_vector x}) +
              &(CARD {x | x IN convex hull {a,b} /\ integral_vector x})) / &2 +
             &1 / &2]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [(← HolLight.GSYM SEGMENT_CONVEX_HULL)] THEN
    SUBGOAL_THEN ([[convex hull {a:real^2,b,c} = segment[a,b] ]]) SUBST1_TAC THENL
     [REWRITE_TAC [SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC CONVEX_HULLS_EQ THEN
      ASM_REWRITE_TAC [(← HolLight.GSYM SEGMENT_CONVEX_HULL), INSERT_SUBSET, EMPTY_SUBSET] THEN
      SIMP_TAC [ENDS_IN_SEGMENT, HULL_INC, IN_INSERT],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[measure(segment[a:real^2,b]) = &0]]) SUBST1_TAC THENL
     [MATCH_MP_TAC MEASURE_EQ_0 THEN
      MATCH_MP_TAC COLLINEAR_IMP_NEGLIGIBLE THEN
      REWRITE_TAC [COLLINEAR_SEGMENT],
      ALL_TAC] THEN
    REWRITE_TAC [h1] THEN
    REWRITE_TAC [REAL_OF_NUM_ADD, REAL_OF_NUM_EQ] THEN
    SUBGOAL_THEN ([[segment[a:real^2,b] = segment[b,c] UNION segment[a,c] ]]) SUBST1_TAC THENL [ASM_MESON_TAC [SEGMENT_SYM, UNION_SEGMENT], ALL_TAC] THEN
    REWRITE_TAC [h2] THEN
    SIMP_TAC [CARD_UNION_GEN, FINITE_BOUNDED_INTEGER_POINTS, BOUNDED_SEGMENT] THEN
    MATCH_MP_TAC h3 THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN
      SIMP_TAC [FINITE_BOUNDED_INTEGER_POINTS, BOUNDED_SEGMENT] THEN SET_TAC [],
      REWRITE_TAC [h4] THEN
      SUBGOAL_THEN ([[segment[b:real^2,c] INTER segment[a,c] = {c}]]) SUBST1_TAC THENL [ASM_MESON_TAC [INTER_SEGMENT, SEGMENT_SYM], ALL_TAC] THEN
      SUBGOAL_THEN ([[{x:real^2 | x IN {c} /\ integral_vector x} = {c}]]) SUBST1_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
      SIMP_TAC [CARD_CLAUSES, FINITE_EMPTY, ARITH, NOT_IN_EMPTY]])
  : ExceptT String IO thm).run
#eval PICK_TRIANGLE_FLAT

/- ------------------------------------------------------------------------- -/
/- Pick's theorem for a triangle.                                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 25
def PICK_TRIANGLE_ALT : thm := keep "PICK_TRIANGLE_ALT" fun _ => (do
  let tac := fun (a bc : term) => (do
        pure (MATCH_MP_TAC CARD_PSUBSET THEN
      REWRITE_TAC [FINITE_TRIANGLE_INTEGER_POINTS] THEN
      REWRITE_TAC [PSUBSET] THEN CONJ_TAC THENL
       [MATCH_MP_TAC (← sr (← ExceptT.mk [[s SUBSET t ==> {x | x IN s /\ P x} SUBSET {x | x IN t /\ P x}]])) THEN
        MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [CONVEX_CONVEX_HULL] THEN
        ASM_SIMP_TAC [INSERT_SUBSET, EMPTY_SUBSET, IN_INSERT, HULL_INC],
        DISCH_TAC] THEN
      SUBGOAL_THEN ((← ExceptT.mk ((← ExceptT.mk (HolCore.Basics.subst [(bc, (← ExceptT.mk [[bc:real^2->bool]]))])) (← ExceptT.mk [[convex hull {a:real^2,b,c} = convex hull bc]])))) ASSUME_TAC THENL
       [MATCH_MP_TAC CONVEX_HULLS_EQ THEN
        ASM_SIMP_TAC [HULL_INC, IN_INSERT, INSERT_SUBSET, EMPTY_SUBSET] THEN
        SUBGOAL_THEN ((← ExceptT.mk ((← ExceptT.mk (HolCore.Basics.subst [(a, (← ExceptT.mk [[x:real^2]]))])) (← ExceptT.mk [[x IN convex hull {a:real^2,b,c}]])))) MP_TAC THENL
         [SIMP_TAC [HULL_INC, IN_INSERT], HolLight.ASM SET_TAC []],
        ALL_TAC] THEN
      MP_TAC (← HolLight.ISPECL [([[{a:real^2,b,c}]]), a] EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
      ASM_REWRITE_TAC [IN_INSERT] THEN
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP EXTREME_POINT_OF_CONVEX_HULL) THEN
      ASM_REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY]) : ExceptT String IO HolCore.Tactics.tactic)
  let tac3 ← tac (← ExceptT.mk [[c:real^2]]) (← ExceptT.mk [[{a:real^2,b,d}]])
  let tac2 ← tac (← ExceptT.mk [[b:real^2]]) (← ExceptT.mk [[{a:real^2,c,d}]])
  let tac1 ← tac (← ExceptT.mk [[a:real^2]]) (← ExceptT.mk [[{b:real^2,c,d}]])
  let h9 ← sr (← ExceptT.mk [[{x | x IN s /\ P x} = s INTER P]])
  let h8 ← ar (← ExceptT.mk [[x:num = (y + z) - w /\ w <= z ==> x + w = y + z]])
  let h7 ← rr (← ExceptT.mk [[x:real = y + z - w <=> x + w = y + z]])
  let h6 ← sr (← ExceptT.mk [[{x | x IN (s INTER t) /\ P x} =
                          {x | x IN s /\ P x} INTER {x | x IN t /\ P x}]])
  let h5 ← sr (← ExceptT.mk [[{x | x IN (s UNION t) /\ P x} =
                          {x | x IN s /\ P x} UNION {x | x IN t /\ P x}]])
  let h4 ← sr (← ExceptT.mk [[~(s = t) ==> t SUBSET s ==> ?d. d IN s /\ ~(d IN t)]])
  let h3 ← sr (← ExceptT.mk [[~(x IN s) ==> {x} INTER s = {}]])
  let h2 ← sr (← ExceptT.mk [[{x | x IN cs /\ P x} = s
         ==> t SUBSET s /\ t SUBSET ct /\ ct SUBSET cs /\
                (s DIFF t) INTER ct = {}
             ==> {x | x IN ct /\ P x} = t]])
  let h1 ← sr (← ExceptT.mk [[{x | x IN s /\ P x} = s INTER P]])
  prove ([[!a b c:real^2.
        integral_vector a /\ integral_vector b /\ integral_vector c
        ==> measure(convex hull {a,b,c}) =
             &(CARD {x | x IN convex hull {a,b,c} /\ integral_vector x}) -
             (&(CARD {x | x IN convex hull {b,c} /\ integral_vector x}) +
              &(CARD {x | x IN convex hull {a,c} /\ integral_vector x}) +
              &(CARD {x | x IN convex hull {a,b} /\ integral_vector x})) / &2 +
             &1 / &2]])
   (REPEAT GEN_TAC THEN
    WF_INDUCT_TAC ([[CARD {x:real^2 | x IN convex hull {a,b,c} /\
                                  integral_vector x}]]) THEN
    ASM_CASES_TAC ([[collinear{a:real^2,b,c}]]) THENL
     [FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [COLLINEAR_BETWEEN_CASES]) THEN
      REWRITE_TAC [BETWEEN_IN_SEGMENT] THEN REPEAT STRIP_TAC THENL
       [MP_TAC (← HolLight.ISPECL [([[b:real^2]]), ([[c:real^2]]), ([[a:real^2]])] PICK_TRIANGLE_FLAT),
        MP_TAC (← HolLight.ISPECL [([[a:real^2]]), ([[c:real^2]]), ([[b:real^2]])] PICK_TRIANGLE_FLAT),
        MP_TAC (← HolLight.ISPECL [([[a:real^2]]), ([[b:real^2]]), ([[c:real^2]])] PICK_TRIANGLE_FLAT)] THEN
      (ANTS_TAC THENL [ASM_MESON_TAC [SEGMENT_SYM], ALL_TAC] THEN
       REWRITE_TAC [h1] THEN
       REWRITE_TAC [INSERT_AC, REAL_ADD_AC]),
      ALL_TAC] THEN
    UNDISCH_TAC ([[~collinear{a:real^2,b,c}]]) THEN
    MAP_EVERY (fun t => ASM_CASES_TAC t THENL
       [ASM_REWRITE_TAC [INSERT_AC, COLLINEAR_2], ALL_TAC]) [([[a:real^2 = b]]), ([[a:real^2 = c]]), ([[b:real^2 = c]])] THEN
    DISCH_TAC THEN STRIP_TAC THEN
    ASM_CASES_TAC ([[{x:real^2 | x IN convex hull {a, b, c} /\ integral_vector x} =
    {a,b,c}]]) THENL
     [ASM_SIMP_TAC [PICK_ELEMENTARY_TRIANGLE] THEN
      SUBGOAL_THEN ([[{x | x IN convex hull {b,c} /\ integral_vector x} = {b,c} /\
      {x | x IN convex hull {a,c} /\ integral_vector x} = {a,c} /\
      {x | x IN convex hull {a,b} /\ integral_vector x} = {a:real^2,b}]]) (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THENL
       [REPEAT CONJ_TAC THEN
        (FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h2) THEN
         REPEAT CONJ_TAC THENL
          [SET_TAC [],
           MATCH_ACCEPT_TAC HULL_SUBSET,
           MATCH_MP_TAC HULL_MONO THEN SET_TAC [],
           ASM_REWRITE_TAC [INSERT_DIFF, IN_INSERT, NOT_IN_EMPTY, EMPTY_DIFF] THEN
           MATCH_MP_TAC h3 THEN
           REWRITE_TAC [(← HolLight.GSYM SEGMENT_CONVEX_HULL), (← HolLight.GSYM BETWEEN_IN_SEGMENT)] THEN
           DISCH_THEN (MP_TAC o HolLight.MATCH_MP BETWEEN_IMP_COLLINEAR) THEN
           UNDISCH_TAC ([[~collinear{a:real^2,b,c}]]) THEN REWRITE_TAC [INSERT_AC]]),
         SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY] THEN
         ASM_REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
         CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV],
       ALL_TAC] THEN
    SUBGOAL_THEN ([[?d:real^2. d IN convex hull {a, b, c} /\ integral_vector d /\
               ~(d = a) /\ ~(d = b) /\ ~(d = c)]]) STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP h4) THEN
      REWRITE_TAC [SUBSET, FORALL_IN_INSERT, IN_ELIM_THM] THEN
      ASM_SIMP_TAC [IN_INSERT, NOT_IN_EMPTY, DE_MORGAN_THM, (← HolLight.GSYM CONJ_ASSOC)] THEN
      DISCH_THEN MATCH_MP_TAC THEN SIMP_TAC [HULL_INC, IN_INSERT],
      ALL_TAC] THEN
    FIRST_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolLight.RAND_CONV [COLLINEAR_3_EQ_AFFINE_DEPENDENT]) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[measure:(real^2->bool)->real]]),
      ([[a:real^2]]), ([[b:real^2]]), ([[c:real^2]]), ([[d:real^2]])] TRIANGLE_ADDITIVE_DECOMPOSITION) THEN
    SIMP_TAC [MEASURE_UNION, MEASURABLE_COMPACT] THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [MEASURE_CONVEX_HULL_2_TRIVIAL, REAL_ADD_RID, REAL_SUB_RZERO] THEN
    MP_TAC (← HolLight.ISPECL [([[\s. &(CARD {x:real^2 | x IN s /\ integral_vector x})]]),
      ([[a:real^2]]), ([[b:real^2]]), ([[c:real^2]]), ([[d:real^2]])] TRIANGLE_ADDITIVE_DECOMPOSITION) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [REWRITE_TAC [h5,
                  h6] THEN
      REPEAT STRIP_TAC THEN
      REWRITE_TAC [h7] THEN
      REWRITE_TAC [REAL_OF_NUM_ADD, REAL_OF_NUM_EQ] THEN
      MATCH_MP_TAC h8 THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CARD_UNION_GEN,
        MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC [INTER_SUBSET]] THEN
      ASM_SIMP_TAC [FINITE_BOUNDED_INTEGER_POINTS, COMPACT_IMP_BOUNDED],
      DISCH_THEN SUBST1_TAC] THEN
    FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.ISPECL [([[a:real^2]]), ([[b:real^2]]), ([[d:real^2]])] th) THEN
     MP_TAC (← HolLight.ISPECL [([[a:real^2]]), ([[c:real^2]]), ([[d:real^2]])] th) THEN
     MP_TAC (← HolLight.ISPECL [([[b:real^2]]), ([[c:real^2]]), ([[d:real^2]])] th))) THEN
    ASM_REWRITE_TAC [] THEN
    ANTS_TAC THENL [tac1, DISCH_THEN SUBST1_TAC] THEN
    ANTS_TAC THENL [tac2, DISCH_THEN SUBST1_TAC] THEN
    ANTS_TAC THENL [tac3, DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN ([[{x:real^2 | x IN convex hull {d} /\ integral_vector x} = {d}]]) SUBST1_TAC THENL
     [REWRITE_TAC [CONVEX_HULL_SING] THEN HolLight.ASM SET_TAC [], ALL_TAC] THEN
    SIMP_TAC [CARD_CLAUSES, FINITE_RULES, NOT_IN_EMPTY] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC [h9] THEN
    REWRITE_TAC [INSERT_AC] THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval PICK_TRIANGLE_ALT

#eval phrase 26
def PICK_TRIANGLE : thm := keep "PICK_TRIANGLE" fun _ => (do
  let h10 ← sr (← ExceptT.mk [[{x | x IN s /\ P x} = s INTER P]])
  let h9 ← ar (← ExceptT.mk [[c:num <= ca /\ a <= ab /\ b <= bc /\
      bc' + ac' + ab' + a + b + c = ab + bc + ca + 3
      ==> bc' + ac' + ab' = (ab + (bc + ca) - c) - (b + a) + 3]])
  let h8 ← sr (← ExceptT.mk [[~(a = b) ==> {b} INTER {a} = {}]])
  let h7 ← sr (← ExceptT.mk [[P a ==> {x | x IN {a} /\ P x} = {a}]])
  let h6 ← sr (← ExceptT.mk [[{x | x IN s /\ P x} INTER {x | x IN t /\ P x} =
      {x | x IN (s INTER t) /\ P x}]])
  let h5 ← sr (← ExceptT.mk [[{x | x IN (s UNION t) /\ P x} =
      {x | x IN s /\ P x} UNION {x | x IN t /\ P x}]])
  let h4 ← sr (← ExceptT.mk [[s SUBSET t ==> {x | x IN s /\ P x} SUBSET {x | x IN t /\ P x}]])
  let h3 ← ar (← ExceptT.mk [[y:num <= x /\ x - y = z ==> z + y = x]])
  let h2 ← rr (← ExceptT.mk [[i + c = s /\ ccc = c + &3
    ==> s - ccc / &2 + &1 / &2 = i + c / &2 - &1]])
  let h1 ← sr (← ExceptT.mk [[{x | x IN (s DIFF t) /\ P x} =
    {x | x IN s /\ P x} DIFF {x | x IN t /\ P x}]])
  prove ([[!a b c:real^2.
        integral_vector a /\ integral_vector b /\ integral_vector c
        ==> measure(convex hull {a,b,c}) =
                if collinear {a,b,c} then &0
                else &(CARD {x | x IN interior(convex hull {a,b,c}) /\
                                 integral_vector x}) +
                     &(CARD {x | x IN frontier(convex hull {a,b,c}) /\
                                 integral_vector x}) / &2 - &1]])
   (REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [MEASURE_EQ_0, COLLINEAR_IMP_NEGLIGIBLE,
                 COLLINEAR_CONVEX_HULL_COLLINEAR] THEN
    ASM_SIMP_TAC [PICK_TRIANGLE_ALT] THEN
    REWRITE_TAC [INTERIOR_OF_TRIANGLE, FRONTIER_OF_TRIANGLE] THEN
    REWRITE_TAC [h1] THEN
    MATCH_MP_TAC h2 THEN
    CONJ_TAC THENL
     [REWRITE_TAC [REAL_OF_NUM_ADD, REAL_OF_NUM_EQ] THEN
      MATCH_MP_TAC h3 THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CARD_SUBSET, MATCH_MP_TAC (← HolLight.GSYM CARD_DIFF)] THEN
      ASM_SIMP_TAC [FINITE_BOUNDED_INTEGER_POINTS,
        FINITE_IMP_BOUNDED_CONVEX_HULL, FINITE_INSERT, FINITE_EMPTY] THEN
      MATCH_MP_TAC h4 THEN
      REWRITE_TAC [UNION_SUBSET, SEGMENT_CONVEX_HULL] THEN
      REPEAT CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC [],
      REWRITE_TAC [h5] THEN
      SIMP_TAC [CARD_UNION_GEN, FINITE_BOUNDED_INTEGER_POINTS,
        FINITE_INTER, FINITE_UNION, BOUNDED_SEGMENT, UNION_OVER_INTER] THEN
      REWRITE_TAC [h6] THEN
      SUBGOAL_THEN ([[segment[b:real^2,c] INTER segment [c,a] = {c} /\
      segment[a,b] INTER segment [b,c] = {b} /\
      segment[a,b] INTER segment [c,a] = {a}]]) (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THENL
       [ASM_MESON_TAC [INTER_SEGMENT, SEGMENT_SYM, INSERT_AC], ALL_TAC] THEN
      ASM_SIMP_TAC [h7] THEN
      ASM_CASES_TAC ([[b:real^2 = a]]) THENL
       [ASM_MESON_TAC [COLLINEAR_2, INSERT_AC], ALL_TAC] THEN
      ASM_SIMP_TAC [h8] THEN
      REWRITE_TAC [REAL_OF_NUM_ADD, REAL_OF_NUM_EQ] THEN
      REWRITE_TAC [NOT_IN_EMPTY, EMPTY_GSPEC, CARD_CLAUSES, SUB_0] THEN
      MATCH_MP_TAC h9 THEN
      ASM_SIMP_TAC [CARD_SUBSET, SING_SUBSET, IN_ELIM_THM, ENDS_IN_SEGMENT,
                   FINITE_BOUNDED_INTEGER_POINTS, BOUNDED_SEGMENT] THEN
      SIMP_TAC [NOT_IN_EMPTY, EMPTY_GSPEC, CARD_CLAUSES, FINITE_INSERT,
               FINITE_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC [h10] THEN
      REWRITE_TAC [SEGMENT_CONVEX_HULL, INSERT_AC] THEN ARITH_TAC])
  : ExceptT String IO thm).run
#eval PICK_TRIANGLE

/- ------------------------------------------------------------------------- -/
/- Parity lemma for segment crossing a polygon.                              -/
/- ------------------------------------------------------------------------- -/

#eval phrase 27
def PARITY_LEMMA : thm := keep "PARITY_LEMMA" fun _ => (do
  let lemma ← prove ([[!a b x y:real^N.
          collinear{y,a,b} /\ between x (a,b) /\
          dist(y,x) < dist(x,b) /\ dist(y,x) < dist(x,a)
          ==> y IN segment(a,b)]])
     (REPEAT STRIP_TAC THEN MATCH_MP_TAC COLLINEAR_DIST_IN_OPEN_SEGMENT THEN
      ASM_REWRITE_TAC [] THEN
      REPEAT (POP_ASSUM MP_TAC) THEN REWRITE_TAC [between, SessionMultiLib.Vectors.DIST_SYM] THEN
      NORM_ARITH_TAC)
  let symlemma ← prove ([[(!n. P(--n) <=> P (n)) /\ (!n. &0 < n dot x ==> P n)
     ==> !n:real^N. ~(n dot x = &0) ==> P n]])
     (STRIP_TAC THEN GEN_TAC THEN
      REWRITE_TAC [(← rr (← ExceptT.mk [[~(x = &0) <=> &0 < x \/ &0 < --x]]))] THEN
      REWRITE_TAC [(← HolLight.GSYM DOT_LNEG)] THEN ASM_MESON_TAC [])
  let h53 ← rr (← ExceptT.mk [[&0 < --x <=> x < &0]])
  let h52 ← rr (← ExceptT.mk [[x * y < &0 <=> &0 < x * --y]])
  let h51 ← rr (← ExceptT.mk [[&0 < x /\ x < e ==> abs(min (&1 / &2) x) < e]])
  let h50 ← va (← ExceptT.mk [[(x + a) - x:real^N = a]])
  let h49 ← na (← ExceptT.mk [[norm(x - (x + a):real^N) = norm a]])
  let h48 ← sr (← ExceptT.mk [[{x,b,a} = {a,x,b}]])
  let h47 ← va (← ExceptT.mk [[((&1 - v) % x + v % b) - x:real^N = v % (b - x)]])
  let h46 ← rr (← ExceptT.mk [[u + v = &1 <=> u = &1 - v]])
  let h45 ← sr (← ExceptT.mk [[s INTER t = {} <=> !x. x IN s ==> ~(x IN t)]])
  let h44 ← sr (← ExceptT.mk [[!t. t INTER u = {} /\ s SUBSET t ==> s INTER u = {}]])
  let h43 ← sr (← ExceptT.mk [[p SUBSET (UNIV DIFF b) /\ l INTER w = {}
          ==> (b INTER w) SUBSET (UNIV DIFF (p UNION l))]])
  let h42 ← rr (← ExceptT.mk [[a - b < &0 <=> a < b]])
  let h41 ← rr (← ExceptT.mk [[&0 < x ==> ~(min (&1 / &2) x = &0)]])
  let h40 ← va (← ExceptT.mk [[x + a:real^N = x <=> a = vec 0]])
  let h39 ← va (← ExceptT.mk [[x + a % (y - x):real^N = (&1 - a) % x + a % y]])
  let h38 ← sr (← ExceptT.mk [[cd INTER p = {x}
          ==> xd SUBSET cd
              ==> (xd DELETE x) SUBSET (UNIV DIFF p)]])
  let h37 ← rr (← ExceptT.mk [[&0 < x /\ x < e ==> abs(min (&1 / &2) x) < e]])
  let h36 ← va (← ExceptT.mk [[(x + a) - x:real^N = a]])
  let h35 ← na (← ExceptT.mk [[norm(x - (x + a):real^N) = norm a]])
  let h34 ← sr (← ExceptT.mk [[{x,b,a} = {a,x,b}]])
  let h33 ← va (← ExceptT.mk [[((&1 - v) % x + v % b) - x:real^N = v % (b - x)]])
  let h32 ← rr (← ExceptT.mk [[u + v = &1 <=> u = &1 - v]])
  let h31 ← sr (← ExceptT.mk [[s INTER t = {} <=> !x. x IN s ==> ~(x IN t)]])
  let h30 ← sr (← ExceptT.mk [[!t. t INTER u = {} /\ s SUBSET t ==> s INTER u = {}]])
  let h29 ← sr (← ExceptT.mk [[p SUBSET (UNIV DIFF b) /\ l INTER w = {}
          ==> (b INTER w) SUBSET (UNIV DIFF (p UNION l))]])
  let h28 ← rr (← ExceptT.mk [[&0 < x ==> ~(min (&1 / &2) x = &0)]])
  let h27 ← va (← ExceptT.mk [[x + a:real^N = x <=> a = vec 0]])
  let h26 ← va (← ExceptT.mk [[x + a % (y - x):real^N = (&1 - a) % x + a % y]])
  let h25 ← sr (← ExceptT.mk [[cd INTER p = {x}
          ==> xd SUBSET cd
              ==> (xd DELETE x) SUBSET (UNIV DIFF p)]])
  let h24 ← tt (← ExceptT.mk [[~p ==> p ==> q]])
  let h23 ← sr (← ExceptT.mk [[~(a IN segment[c,d]) /\ ~(b IN segment[c,d]) /\
      segment(a,b) INTER segment(c,d) = {x} /\
      segment(a,b) = segment[a,b] DIFF {a,b} /\
      segment(c,d) = segment[c,d] DIFF {c,d}
      ==> segment[a,b] INTER segment(c,d) = {x}]])
  let h22 ← sr (← ExceptT.mk [[cd INTER p = {} /\ l INTER (cd DIFF {c,d}) = {x}
      ==> (cd DIFF {c,d}) INTER (p UNION l) = {x}]])
  let h21 ← sr (← ExceptT.mk [[{c,d} INTER p = {} /\ (segment[c,d] DIFF {c,d}) INTER p = {x}
      ==> segment[c,d] INTER p = {x}]])
  let h20 ← sr (← ExceptT.mk [[s SUBSET UNIV DIFF t <=> s INTER t = {}]])
  let h19 ← sr (← ExceptT.mk [[s SUBSET UNIV DIFF t <=> s INTER t = {}]])
  let h18 ← sr (← ExceptT.mk [[s SUBSET UNIV DIFF t <=> s INTER t = {}]])
  let h17 ← sr (← ExceptT.mk [[t SUBSET UNIV DIFF s <=> t INTER s = {}]])
  let h16 ← sr (← ExceptT.mk [[~(x IN s <=> y IN t)
      ==> !p. s UNION t = (:real^2) DIFF p /\ {x,y} INTER p = {}
              ==> x IN s /\ y IN s \/ x IN t /\ y IN t]])
  let h15 ← sr (← ExceptT.mk [[{y,a,b} = {a,b,y}]])
  let h14 ← rr (← ExceptT.mk [[~(x < &0) /\ ~(&0 < x) <=> x = &0]])
  let h13 ← tt (← ExceptT.mk [[(~c /\ ~b ==> a) ==> a \/ b \/ c]])
  let h12 ← rr (← ExceptT.mk [[--x < &0 <=> &0 < x]])
  let h11 ← va (← ExceptT.mk [[d - ((&1 - u) % c + u % d):real^N = (&1 - u) % (d - c) /\
       c - ((&1 - u) % c + u % d) = --u % (d - c)]])
  let h10 ← sr (← ExceptT.mk [[{a,b,c} = {c,b,a}]])
  let h9 ← sr (← ExceptT.mk [[{a,b,c} = {c,b,a}]])
  let h8 ← sr (← ExceptT.mk [[{a,b,c,d} = {b,d,a,c}]])
  let h7 ← sr (← ExceptT.mk [[{c,d} INTER (s UNION t) = {} <=>
      (~(c IN s) /\ ~(d IN s)) /\ ~(c IN t) /\ ~(d IN t)]])
  let h6 ← ms [SEGMENT_SYM] (← ExceptT.mk [[segment(d:real^2,c) = segment(c,d)]])
  let h5 ← sr (← ExceptT.mk [[p INTER s SUBSET u ==> x IN (s DIFF u) ==> ~(x IN p)]])
  let h4 ← sr (← ExceptT.mk [[a = {x} ==> x IN a]])
  let h3 ← tt (← ExceptT.mk [[~a ==> a /\ b ==> c]])
  let h2 ← na (← ExceptT.mk [[cp = x \/ &0 < dist(x:real^2,cp)]])
  let h1 ← sr (← ExceptT.mk [[a INSERT b INSERT c INSERT d INSERT s =
                             {a,b,c,d} UNION s]])
  prove ([[!a b c d p x:real^2.
        simple_path(p ++ linepath(a,b)) /\
        pathstart p = b /\ pathfinish p = a /\
        segment(a,b) INTER segment(c,d) = {x} /\
        segment[c,d] INTER path_image p = {}
        ==> (c IN inside(path_image(p ++ linepath(a,b))) <=>
             d IN outside(path_image(p ++ linepath(a,b))))]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[p:real^1->real^2]]), ([[linepath(a:real^2,b)]])] SIMPLE_PATH_JOIN_LOOP_EQ) THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP SIMPLE_PATH_IMP_PATH) THEN
    ASM_SIMP_TAC [PATH_JOIN, PATHSTART_LINEPATH, PATHFINISH_LINEPATH] THEN
    DISCH_THEN (ASSUME_TAC o HolLight.CONJUNCT1) THEN STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[(a:real^2) INSERT b INSERT c INSERT d INSERT path_image p]]),
                   ([[x:real^2]])] DISTANCE_ATTAINS_INF) THEN
    REWRITE_TAC [FORALL_IN_INSERT] THEN
    ONCE_REWRITE_TAC [h1] THEN
    ASM_SIMP_TAC [CLOSED_UNION, FINITE_IMP_CLOSED, CLOSED_PATH_IMAGE,
                 FINITE_INSERT, FINITE_EMPTY] THEN
    ANTS_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[cp:real^2]]) MP_TAC) THEN
    DISJ_CASES_TAC h2 THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MATCH_MP_TAC h3 THEN
      FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP h4) THEN
      REWRITE_TAC [open_segment, IN_DIFF, IN_UNION, IN_INSERT, NOT_IN_EMPTY,
                  IN_INTER, DE_MORGAN_THM] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h5) THEN
      ASM_REWRITE_TAC [IN_DIFF, IN_INSERT, NOT_IN_EMPTY, PATH_IMAGE_LINEPATH],
      ALL_TAC] THEN
    ABBREV_TAC ([[e = dist(x:real^2,cp)]]) THEN FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o HolLight.SYM) THEN
    DISCH_THEN (STRIP_ASSUME_TAC o HolLight.CONJUNCT2) THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [ARC_LINEPATH_EQ]) THEN
    MP_TAC (← HolLight.ISPECL [([[a:real^2]]), ([[b:real^2]]), ([[c:real^2]]), ([[d:real^2]])] FINITE_INTER_COLLINEAR_OPEN_SEGMENTS) THEN
    MP_TAC (← HolLight.ISPECL [([[a:real^2]]), ([[b:real^2]]), ([[d:real^2]]), ([[c:real^2]])] FINITE_INTER_COLLINEAR_OPEN_SEGMENTS) THEN
    SUBST1_TAC h6 THEN
    ASM_REWRITE_TAC [FINITE_SING, NOT_INSERT_EMPTY] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN ([[~(a IN segment[c:real^2,d]) /\ ~(b IN segment[c,d])]]) STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC [PATHSTART_IN_PATH_IMAGE, PATHFINISH_IN_PATH_IMAGE,
                    IN_INTER, NOT_IN_EMPTY],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[~(c:real^2 = a) /\ ~(c = b) /\ ~(d = a) /\ ~(d = b)]]) STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [ENDS_IN_SEGMENT], ALL_TAC] THEN
    SUBGOAL_THEN ([[x IN segment(a:real^2,b) /\ x IN segment(c,d)]]) MP_TAC THENL
     [HolLight.ASM SET_TAC [], ALL_TAC] THEN
    REWRITE_TAC [IN_OPEN_SEGMENT_ALT] THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[{c,d} INTER path_image(p ++ linepath(a:real^2,b)) = {}]]) ASSUME_TAC THENL
     [ASM_SIMP_TAC [PATH_IMAGE_JOIN, PATH_LINEPATH, PATHSTART_LINEPATH] THEN
      REWRITE_TAC [h7] THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC [ENDS_IN_SEGMENT, IN_INTER, NOT_IN_EMPTY],
        REWRITE_TAC [PATH_IMAGE_LINEPATH, (← HolLight.GSYM BETWEEN_IN_SEGMENT)] THEN
        CONJ_TAC THEN DISCH_THEN (ASSUME_TAC o HolLight.MATCH_MP BETWEEN_IMP_COLLINEAR) THEN
        RULE_ASSUM_TAC (HolLight.REWRITE_RULE [INSERT_AC]) THEN ASM_MESON_TAC []],
      ALL_TAC] THEN
    MP_TAC (← HolLight.ISPEC ([[b - x:real^2]]) ORTHOGONAL_TO_VECTOR_EXISTS) THEN
    REWRITE_TAC [DIMINDEX_2, LE_REFL, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC ([[n:real^2]]) THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[(x:real^2) IN segment(a,b) /\ x IN segment(c,d)]]) MP_TAC THENL
     [HolLight.ASM SET_TAC [],
      SIMP_TAC [IN_OPEN_SEGMENT_ALT, (← HolLight.GSYM BETWEEN_IN_SEGMENT)] THEN STRIP_TAC] THEN
    SUBGOAL_THEN ([[~collinear{a:real^2, b, c, d}]]) ASSUME_TAC THENL
     [UNDISCH_TAC ([[~collinear{a:real^2,b,c}]]) THEN REWRITE_TAC [CONTRAPOS_THM] THEN
      MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_CONJ_ALT] COLLINEAR_SUBSET) THEN SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[~(n dot (d - x:real^2) = &0)]]) MP_TAC THENL
     [REWRITE_TAC [(← HolLight.GSYM orthogonal)] THEN DISCH_TAC THEN
      MP_TAC (← HolLight.SPECL [([[n:real^2]]), ([[d - x:real^2]]), ([[b - x:real^2]])] ORTHOGONAL_TO_ORTHOGONAL_2D) THEN
      ANTS_TAC THENL [ASM_MESON_TAC [ORTHOGONAL_SYM], ALL_TAC] THEN
      REWRITE_TAC [(← HolLight.GSYM COLLINEAR_3)] THEN DISCH_TAC THEN
      UNDISCH_TAC ([[~collinear{a:real^2, b, c, d}]]) THEN ASM_REWRITE_TAC [] THEN
      ONCE_REWRITE_TAC [h8] THEN
      ASM_SIMP_TAC [COLLINEAR_4_3] THEN CONJ_TAC THENL
       [MATCH_MP_TAC COLLINEAR_SUBSET THEN EXISTS_TAC ([[{b:real^2,x,a,d}]]) THEN
        CONJ_TAC THENL [ASM_SIMP_TAC [COLLINEAR_4_3], SET_TAC []] THEN
        ONCE_REWRITE_TAC [h9] THEN
        ASM_SIMP_TAC [BETWEEN_IMP_COLLINEAR],
        MATCH_MP_TAC COLLINEAR_SUBSET THEN EXISTS_TAC ([[{d:real^2,x,b,c}]]) THEN
        CONJ_TAC THENL [ASM_SIMP_TAC [COLLINEAR_4_3], SET_TAC []] THEN
        ONCE_REWRITE_TAC [h10] THEN
        ASM_SIMP_TAC [BETWEEN_IMP_COLLINEAR]],
      ALL_TAC] THEN
    DISCH_THEN (fun th => POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist HolLight.CONJ) THEN
                         MP_TAC th) THEN
    SPEC_TAC (([[n:real^2]]), ([[n:real^2]])) THEN
    MATCH_MP_TAC symlemma THEN CONJ_TAC THENL
     [REWRITE_TAC [ORTHOGONAL_RNEG, VECTOR_NEG_EQ_0], ALL_TAC] THEN
    GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[n dot (c - x:real^2) < &0]]) ASSUME_TAC THENL
     [UNDISCH_TAC ([[&0 < n dot (d - x:real^2)]]) THEN
      SUBGOAL_THEN ([[(x:real^2) IN segment(c,d)]]) MP_TAC THENL
       [HolLight.ASM SET_TAC [], ALL_TAC] THEN
      ASM_REWRITE_TAC [IN_SEGMENT] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [h11] THEN
      REWRITE_TAC [DOT_RMUL, REAL_MUL_LNEG, h12] THEN
      ASM_SIMP_TAC [REAL_LT_MUL_EQ, REAL_SUB_LT],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!y. y IN ball(x:real^2,e)
        ==> y IN segment(a,b) \/
            &0 < n dot (y - x) \/
            n dot (y - x) < &0]]) ASSUME_TAC THENL
     [REWRITE_TAC [IN_BALL] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC h13 THEN
      REWRITE_TAC [h14] THEN
      REWRITE_TAC [(← HolLight.GSYM orthogonal)] THEN DISCH_TAC THEN
      MP_TAC (← HolLight.SPECL [([[n:real^2]]), ([[y - x:real^2]]), ([[b - x:real^2]])] ORTHOGONAL_TO_ORTHOGONAL_2D) THEN
      ANTS_TAC THENL [ASM_MESON_TAC [ORTHOGONAL_SYM], ALL_TAC] THEN
      REWRITE_TAC [(← HolLight.GSYM COLLINEAR_3)] THEN DISCH_TAC THEN
      MATCH_MP_TAC lemma THEN EXISTS_TAC ([[x:real^2]]) THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [ALL_TAC, ASM_MESON_TAC [REAL_LTE_TRANS, SessionMultiLib.Vectors.DIST_SYM]] THEN
      ONCE_REWRITE_TAC [h15] THEN
      MATCH_MP_TAC COLLINEAR_3_TRANS THEN EXISTS_TAC ([[x:real^2]]) THEN
      ASM_REWRITE_TAC [] THEN UNDISCH_TAC ([[collinear{y:real^2, x, b}]]) THEN
      MP_TAC (← HolLight.MATCH_MP BETWEEN_IMP_COLLINEAR (← HolLight.ASSUME ([[between (x:real^2) (a,b)]]))) THEN
      SIMP_TAC [INSERT_AC],
      ALL_TAC] THEN
    MP_TAC (← HolLight.SPEC ([[p ++ linepath(a:real^2,b)]]) JORDAN_INSIDE_OUTSIDE) THEN
    ASM_REWRITE_TAC [PATHFINISH_JOIN, PATHSTART_JOIN, PATHFINISH_LINEPATH] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN ([[~(connected_component((:real^2) DIFF path_image(p ++ linepath (a,b))) c d)]]) MP_TAC THENL
     [DISCH_TAC,
      ONCE_REWRITE_TAC [(← HolLight.GSYM CONTRAPOS_THM)] THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC ([[path_image(p ++ linepath(a:real^2,b))]]) o
        HolLight.MATCH_MP h16) THEN
      ASM_REWRITE_TAC [connected_component] THEN
      ASM_REWRITE_TAC [h17] THEN
      ASM_MESON_TAC [INSIDE_NO_OVERLAP, OUTSIDE_NO_OVERLAP]] THEN
    MP_TAC (← HolLight.SPEC ([[p ++ linepath(a:real^2,b)]]) JORDAN_DISCONNECTED) THEN
    ASM_REWRITE_TAC [PATHFINISH_JOIN, PATHSTART_JOIN, PATHFINISH_LINEPATH] THEN
    REWRITE_TAC [CONNECTED_IFF_CONNECTED_COMPONENT] THEN
    SUBGOAL_THEN ([[!u v. u IN inside(path_image(p ++ linepath(a,b))) /\
          v IN outside(path_image(p ++ linepath(a,b)))
          ==> connected_component
              ((:real^2) DIFF path_image (p ++ linepath (a,b))) u v]]) ASSUME_TAC THENL
     [ALL_TAC,
      MAP_EVERY X_GEN_TAC [([[u:real^2]]), ([[v:real^2]])] THEN
      GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [(← HolLight.SYM (← HolLight.ASSUME ([[inside (path_image (p ++ linepath (a,b))) UNION
                  outside (path_image (p ++ linepath (a,b))) =
                  (:real^2) DIFF path_image (p ++ linepath (a,b))]])))] THEN
      REWRITE_TAC [IN_UNION, CONNECTED_IFF_CONNECTED_COMPONENT] THEN
      STRIP_TAC THENL
       [REWRITE_TAC [connected_component] THEN
        EXISTS_TAC ([[inside(path_image(p ++ linepath(a:real^2,b)))]]),
        ASM_MESON_TAC [],
        ASM_MESON_TAC [CONNECTED_COMPONENT_SYM],
        REWRITE_TAC [connected_component] THEN
        EXISTS_TAC ([[outside(path_image(p ++ linepath(a:real^2,b)))]])] THEN
      ASM_REWRITE_TAC [h18] THEN
      REWRITE_TAC [OUTSIDE_NO_OVERLAP, INSIDE_NO_OVERLAP]] THEN
    SUBGOAL_THEN ([[(x:real^2) IN path_image(p ++ linepath(a,b))]]) ASSUME_TAC THENL
     [ASM_SIMP_TAC [PATHSTART_LINEPATH, PATH_IMAGE_JOIN, PATH_LINEPATH] THEN
      REWRITE_TAC [IN_UNION, PATH_IMAGE_LINEPATH] THEN DISJ2_TAC THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [open_segment]) THEN HolLight.ASM SET_TAC [],
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [([[u:real^2]]), ([[v:real^2]])] THEN STRIP_TAC THEN
    UNDISCH_TAC ([[frontier(inside(path_image(p ++ linepath(a:real^2,b)))) =
    path_image(p ++ linepath(a,b))]]) THEN
    REWRITE_TAC [EXTENSION] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[x:real^2]])) THEN ASM_REWRITE_TAC [frontier] THEN
    REWRITE_TAC [IN_DIFF, CLOSURE_APPROACHABLE] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[e:real]]) o HolLight.CONJUNCT1) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC ([[w:real^2]]) THEN STRIP_TAC THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN EXISTS_TAC ([[w:real^2]]) THEN
    CONJ_TAC THENL
     [REWRITE_TAC [connected_component] THEN
      EXISTS_TAC ([[inside(path_image(p ++ linepath(a:real^2,b)))]]) THEN
      ASM_REWRITE_TAC [h19] THEN
      REWRITE_TAC [INSIDE_NO_OVERLAP],
      ALL_TAC] THEN
    UNDISCH_TAC ([[frontier(outside(path_image(p ++ linepath(a:real^2,b)))) =
    path_image(p ++ linepath(a,b))]]) THEN
    REWRITE_TAC [EXTENSION] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[x:real^2]])) THEN ASM_REWRITE_TAC [frontier] THEN
    REWRITE_TAC [IN_DIFF, CLOSURE_APPROACHABLE] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[e:real]]) o HolLight.CONJUNCT1) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC ([[z:real^2]]) THEN STRIP_TAC THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN EXISTS_TAC ([[z:real^2]]) THEN
    CONJ_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [connected_component] THEN
      EXISTS_TAC ([[outside(path_image(p ++ linepath(a:real^2,b)))]]) THEN
      ASM_REWRITE_TAC [h20] THEN
      REWRITE_TAC [OUTSIDE_NO_OVERLAP]] THEN
    SUBGOAL_THEN ([[!y. dist(y,x) < e /\ ~(y IN path_image(p ++ linepath (a,b)))
        ==> connected_component
             ((:real^2) DIFF path_image(p ++ linepath(a,b))) c y]]) ASSUME_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN EXISTS_TAC ([[c:real^2]]) THEN
      CONJ_TAC THENL [MATCH_MP_TAC CONNECTED_COMPONENT_SYM, ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC [INSIDE_NO_OVERLAP, OUTSIDE_NO_OVERLAP, IN_INTER,
                    NOT_IN_EMPTY]] THEN
    X_GEN_TAC ([[y:real^2]]) THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[segment[c,d] INTER path_image(p ++ linepath(a,b)) = {x:real^2}]]) ASSUME_TAC THENL
     [MATCH_MP_TAC h21 THEN
      ASM_SIMP_TAC [PATH_IMAGE_JOIN, PATHSTART_LINEPATH, PATH_LINEPATH] THEN
      MATCH_MP_TAC h22 THEN
      ASM_REWRITE_TAC [(← HolLight.GSYM open_segment), PATH_IMAGE_LINEPATH] THEN
      MATCH_MP_TAC h23 THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [open_segment],
      ALL_TAC] THEN
    UNDISCH_THEN ([[!y. y IN ball(x:real^2,e)
          ==> y IN segment(a,b) \/ &0 < n dot (y - x) \/ n dot (y - x) < &0]]) (MP_TAC o HolLight.SPEC ([[y:real^2]])) THEN
    REWRITE_TAC [IN_BALL] THEN ONCE_REWRITE_TAC [SessionMultiLib.Vectors.DIST_SYM] THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN MP_TAC) THENL
     [MATCH_MP_TAC h24 THEN
      UNDISCH_TAC ([[~(y IN path_image(p ++ linepath(a:real^2,b)))]]) THEN
      ASM_SIMP_TAC [PATHSTART_LINEPATH, PATH_IMAGE_JOIN, PATH_LINEPATH] THEN
      SIMP_TAC [CONTRAPOS_THM, open_segment, IN_DIFF, IN_UNION,
               PATH_IMAGE_LINEPATH],
      DISCH_TAC THEN MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN
      EXISTS_TAC ([[d:real^2]]) THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN
      EXISTS_TAC ([[x + min (&1 / &2) (e / &2 / norm(d - x)) % (d - x):real^2]]) THEN
      REWRITE_TAC [connected_component] THEN CONJ_TAC THENL
       [EXISTS_TAC ([[segment[x:real^2,d] DELETE x]]) THEN
        SIMP_TAC [CONVEX_SEMIOPEN_SEGMENT, CONVEX_CONNECTED] THEN
        ASM_REWRITE_TAC [IN_DELETE, ENDS_IN_SEGMENT] THEN REPEAT CONJ_TAC THENL
         [FIRST_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h25) THEN
          REWRITE_TAC [SUBSET_SEGMENT, ENDS_IN_SEGMENT] THEN
          UNDISCH_TAC ([[segment (a,b) INTER segment (c,d) = {x:real^2}]]) THEN
          REWRITE_TAC [open_segment] THEN SET_TAC [],
          REWRITE_TAC [IN_SEGMENT, h26] THEN
          EXISTS_TAC ([[min (&1 / &2) (e / &2 / norm(d - x:real^2))]]) THEN
          REWRITE_TAC [] THEN CONJ_TAC THENL [ALL_TAC, REAL_ARITH_TAC2] THEN
          REWRITE_TAC [REAL_LE_MIN] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
          ASM_SIMP_TAC [REAL_LE_DIV, REAL_POS, NORM_POS_LE, REAL_LT_IMP_LE],
          ASM_REWRITE_TAC [VECTOR_MUL_EQ_0, VECTOR_SUB_EQ,
                          h27] THEN
          MATCH_MP_TAC h28 THEN
          MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC [REAL_HALF] THEN
          ASM_REWRITE_TAC [NORM_POS_LT, VECTOR_SUB_EQ]],
        EXISTS_TAC ([[ball(x,e) INTER {w:real^2 | &0 < n dot (w - x)}]]) THEN
        REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTER THEN
          REWRITE_TAC [CONVEX_BALL, DOT_RSUB, REAL_SUB_LT] THEN
          REWRITE_TAC [(← HolLight.GSYM real_gt), CONVEX_HALFSPACE_GT],
          ASM_SIMP_TAC [PATHSTART_LINEPATH, PATH_IMAGE_JOIN, PATH_LINEPATH] THEN
          MATCH_MP_TAC h29 THEN
          ASM_REWRITE_TAC [SUBSET, IN_DIFF, IN_UNIV, IN_BALL, REAL_NOT_LT] THEN
          MATCH_MP_TAC h30 THEN
          EXISTS_TAC ([[affine hull {x:real^2,b}]]) THEN CONJ_TAC THENL
           [REWRITE_TAC [AFFINE_HULL_2, FORALL_IN_GSPEC, h31] THEN
            REWRITE_TAC [IN_ELIM_THM] THEN
            SIMP_TAC [h32] THEN
            REWRITE_TAC [DOT_RMUL, h33] THEN
            RULE_ASSUM_TAC (HolLight.REWRITE_RULE [orthogonal]) THEN
            ONCE_REWRITE_TAC [DOT_SYM] THEN
            ASM_REWRITE_TAC [REAL_MUL_RZERO, REAL_LT_REFL],
            REWRITE_TAC [PATH_IMAGE_LINEPATH, SEGMENT_CONVEX_HULL] THEN
            SIMP_TAC [SUBSET_HULL, AFFINE_IMP_CONVEX, AFFINE_AFFINE_HULL] THEN
            REWRITE_TAC [INSERT_SUBSET, EMPTY_SUBSET] THEN
            SIMP_TAC [HULL_INC, IN_INSERT] THEN
            ASM_SIMP_TAC [(← HolLight.GSYM COLLINEAR_3_AFFINE_HULL)] THEN
            ONCE_REWRITE_TAC [h34] THEN
            MATCH_MP_TAC BETWEEN_IMP_COLLINEAR THEN ASM_REWRITE_TAC []],
          REWRITE_TAC [IN_BALL, IN_INTER, IN_ELIM_THM, SessionMultiLib.Vectors.dist] THEN
          REWRITE_TAC [h35] THEN
          REWRITE_TAC [h36] THEN CONJ_TAC THENL
           [ASM_SIMP_TAC [NORM_MUL, (← HolLight.GSYM REAL_LT_RDIV_EQ), NORM_POS_LT,
                         VECTOR_SUB_EQ] THEN
            MATCH_MP_TAC h37 THEN
            ASM_SIMP_TAC [REAL_LT_DIV, REAL_HALF, NORM_POS_LT, VECTOR_SUB_EQ,
                         REAL_LT_DIV2_EQ] THEN ASM_REAL_ARITH_TAC,
            REWRITE_TAC [DOT_RMUL] THEN MATCH_MP_TAC REAL_LT_MUL THEN
            ASM_REWRITE_TAC [REAL_LT_MIN] THEN
            ASM_SIMP_TAC [REAL_LT_DIV, REAL_HALF, NORM_POS_LT, VECTOR_SUB_EQ,
                         REAL_LT_01]],
          REWRITE_TAC [IN_BALL, IN_INTER, IN_ELIM_THM] THEN
          ONCE_REWRITE_TAC [SessionMultiLib.Vectors.DIST_SYM] THEN ASM_REWRITE_TAC []]],
      DISCH_TAC THEN MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN
      EXISTS_TAC ([[x + min (&1 / &2) (e / &2 / norm(c - x)) % (c - x):real^2]]) THEN
      REWRITE_TAC [connected_component] THEN CONJ_TAC THENL
       [EXISTS_TAC ([[segment[x:real^2,c] DELETE x]]) THEN
        SIMP_TAC [CONVEX_SEMIOPEN_SEGMENT, CONVEX_CONNECTED] THEN
        ASM_REWRITE_TAC [IN_DELETE, ENDS_IN_SEGMENT] THEN REPEAT CONJ_TAC THENL
         [FIRST_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h38) THEN
          REWRITE_TAC [SUBSET_SEGMENT, ENDS_IN_SEGMENT] THEN
          UNDISCH_TAC ([[segment (a,b) INTER segment (c,d) = {x:real^2}]]) THEN
          REWRITE_TAC [open_segment] THEN SET_TAC [],
          REWRITE_TAC [IN_SEGMENT, h39] THEN
          EXISTS_TAC ([[min (&1 / &2) (e / &2 / norm(c - x:real^2))]]) THEN
          REWRITE_TAC [] THEN CONJ_TAC THENL [ALL_TAC, REAL_ARITH_TAC2] THEN
          REWRITE_TAC [REAL_LE_MIN] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
          ASM_SIMP_TAC [REAL_LE_DIV, REAL_POS, NORM_POS_LE, REAL_LT_IMP_LE],
          ASM_REWRITE_TAC [VECTOR_MUL_EQ_0, VECTOR_SUB_EQ,
                          h40] THEN
          MATCH_MP_TAC h41 THEN
          MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC [REAL_HALF] THEN
          ASM_REWRITE_TAC [NORM_POS_LT, VECTOR_SUB_EQ]],
        EXISTS_TAC ([[ball(x,e) INTER {w:real^2 | n dot (w - x) < &0}]]) THEN
        REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTER THEN
          REWRITE_TAC [CONVEX_BALL, DOT_RSUB, h42,
                      CONVEX_HALFSPACE_LT],
          ASM_SIMP_TAC [PATHSTART_LINEPATH, PATH_IMAGE_JOIN, PATH_LINEPATH] THEN
          MATCH_MP_TAC h43 THEN
          ASM_REWRITE_TAC [SUBSET, IN_DIFF, IN_UNIV, IN_BALL, REAL_NOT_LT] THEN
          MATCH_MP_TAC h44 THEN
          EXISTS_TAC ([[affine hull {x:real^2,b}]]) THEN CONJ_TAC THENL
           [REWRITE_TAC [AFFINE_HULL_2, FORALL_IN_GSPEC, h45] THEN
            REWRITE_TAC [IN_ELIM_THM] THEN
            SIMP_TAC [h46] THEN
            REWRITE_TAC [DOT_RMUL, h47] THEN
            RULE_ASSUM_TAC (HolLight.REWRITE_RULE [orthogonal]) THEN
            ONCE_REWRITE_TAC [DOT_SYM] THEN
            ASM_REWRITE_TAC [REAL_MUL_RZERO, REAL_LT_REFL],
            REWRITE_TAC [PATH_IMAGE_LINEPATH, SEGMENT_CONVEX_HULL] THEN
            SIMP_TAC [SUBSET_HULL, AFFINE_IMP_CONVEX, AFFINE_AFFINE_HULL] THEN
            REWRITE_TAC [INSERT_SUBSET, EMPTY_SUBSET] THEN
            SIMP_TAC [HULL_INC, IN_INSERT] THEN
            ASM_SIMP_TAC [(← HolLight.GSYM COLLINEAR_3_AFFINE_HULL)] THEN
            ONCE_REWRITE_TAC [h48] THEN
            MATCH_MP_TAC BETWEEN_IMP_COLLINEAR THEN ASM_REWRITE_TAC []],
          REWRITE_TAC [IN_BALL, IN_INTER, IN_ELIM_THM, SessionMultiLib.Vectors.dist] THEN
          REWRITE_TAC [h49] THEN
          REWRITE_TAC [h50] THEN CONJ_TAC THENL
           [ASM_SIMP_TAC [NORM_MUL, (← HolLight.GSYM REAL_LT_RDIV_EQ), NORM_POS_LT,
                         VECTOR_SUB_EQ] THEN
            MATCH_MP_TAC h51 THEN
            ASM_SIMP_TAC [REAL_LT_DIV, REAL_HALF, NORM_POS_LT, VECTOR_SUB_EQ,
                         REAL_LT_DIV2_EQ] THEN ASM_REAL_ARITH_TAC,
            REWRITE_TAC [DOT_RMUL, h52] THEN
            MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC [REAL_LT_MIN] THEN
            ASM_REWRITE_TAC [h53] THEN
            ASM_SIMP_TAC [REAL_LT_DIV, REAL_HALF, NORM_POS_LT, VECTOR_SUB_EQ,
                         REAL_LT_01]],
          REWRITE_TAC [IN_BALL, IN_INTER, IN_ELIM_THM] THEN
          ONCE_REWRITE_TAC [SessionMultiLib.Vectors.DIST_SYM] THEN ASM_REWRITE_TAC []]]])
  : ExceptT String IO thm).run
#eval PARITY_LEMMA

/- ------------------------------------------------------------------------- -/
/- Polygonal path; 0 in the empty case is just for linear invariance.        -/
/- Note that we *are* forced to assume non-emptiness for translation.        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 28
def polygonal_path : thm := keep "polygonal_path" fun _ => define
 [[polygonal_path[] = linepath(vec 0,vec 0) /\
  polygonal_path[a] = linepath(a,a) /\
  polygonal_path [a;b] = linepath(a,b) /\
  polygonal_path (CONS a (CONS b (CONS c l))) =
       linepath(a,b) ++ polygonal_path(CONS b (CONS c l))]]
#eval polygonal_path

#eval phrase 29
def POLYGONAL_PATH_CONS_CONS : thm := keep "POLYGONAL_PATH_CONS_CONS" fun _ => (do
  prove ([[!a b p. ~(p = [])
           ==> polygonal_path(CONS a (CONS b p)) =
               linepath(a,b) ++ polygonal_path(CONS b p)]])
   (GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC [polygonal_path])
  : ExceptT String IO thm).run
#eval POLYGONAL_PATH_CONS_CONS

#eval phrase 30
def POLYGONAL_PATH_TRANSLATION : thm := keep "POLYGONAL_PATH_TRANSLATION" fun _ => (do
  prove ([[!a b p. polygonal_path (MAP (\x. a + x) (CONS b p)) =
         (\x. a + x) o (polygonal_path (CONS b p))]])
   (GEN_TAC THEN ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC [Session.listDefs.MAP, polygonal_path, LINEPATH_TRANSLATION] THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    MATCH_MP_TAC list_INDUCT THEN
    ASM_SIMP_TAC [Session.listDefs.MAP, polygonal_path, LINEPATH_TRANSLATION] THEN
    REWRITE_TAC [JOINPATHS_TRANSLATION])
  : ExceptT String IO thm).run
#eval POLYGONAL_PATH_TRANSLATION

#eval phrase 31
-- add_translation_invariants [POLYGONAL_PATH_TRANSLATION];;
#eval (do match ← (SessionMultiLib.Vectors.add_translation_invariants [POLYGONAL_PATH_TRANSLATION]).run with
  | .ok _ => pure () | .error e => failure e : IO Unit)

#eval phrase 32
def POLYGONAL_PATH_LINEAR_IMAGE : thm := keep "POLYGONAL_PATH_LINEAR_IMAGE" fun _ => (do
  prove ([[!f p. linear f ==> polygonal_path (MAP f p) = f o polygonal_path p]])
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC [polygonal_path, Session.listDefs.MAP] THEN CONJ_TAC THENL
     [REWRITE_TAC [LINEPATH_REFL, o_DEF, FUN_EQ_THM] THEN ASM_MESON_TAC [LINEAR_0],
      ONCE_REWRITE_TAC [SWAP_FORALL_THM]] THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [polygonal_path, Session.listDefs.MAP] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC [LINEPATH_LINEAR_IMAGE],
      ONCE_REWRITE_TAC [SWAP_FORALL_THM]] THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [polygonal_path, Session.listDefs.MAP] THEN
    ASM_SIMP_TAC [(← HolLight.GSYM JOINPATHS_LINEAR_IMAGE), (← HolLight.GSYM LINEPATH_LINEAR_IMAGE)])
  : ExceptT String IO thm).run
#eval POLYGONAL_PATH_LINEAR_IMAGE

#eval phrase 33
-- add_linear_invariants [POLYGONAL_PATH_LINEAR_IMAGE];;
#eval (do match ← (SessionMultiLib.Vectors.add_linear_invariants [POLYGONAL_PATH_LINEAR_IMAGE]).run with
  | .ok _ => pure () | .error e => failure e : IO Unit)

#eval phrase 34
def PATHSTART_POLYGONAL_PATH : thm := keep "PATHSTART_POLYGONAL_PATH" fun _ => (do
  prove ([[!p. pathstart(polygonal_path p) = if p = [] then vec 0 else HD p]])
   (MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC [polygonal_path, PATHSTART_LINEPATH] THEN
    GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC [polygonal_path, PATHSTART_LINEPATH, Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD] THEN
    GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC [polygonal_path, PATHSTART_LINEPATH, Session.listDefs.HD, PATHSTART_JOIN])
  : ExceptT String IO thm).run
#eval PATHSTART_POLYGONAL_PATH

#eval phrase 35
def PATHFINISH_POLYGONAL_PATH : thm := keep "PATHFINISH_POLYGONAL_PATH" fun _ => (do
  prove ([[!p. pathfinish(polygonal_path p) = if p = [] then vec 0 else LAST p]])
   (MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC [polygonal_path, PATHFINISH_LINEPATH] THEN
    GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC [polygonal_path, PATHFINISH_LINEPATH, Session.listThms1.NOT_CONS_NIL, Session.listDefs.LAST] THEN
    GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC [polygonal_path, PATHFINISH_LINEPATH, PATHFINISH_JOIN])
  : ExceptT String IO thm).run
#eval PATHFINISH_POLYGONAL_PATH

#eval phrase 36
def VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH : thm := keep "VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH" fun _ => (do
  prove ([[!p:(real^N)list. set_of_list p SUBSET path_image (polygonal_path p)]])
   (MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [set_of_list, EMPTY_SUBSET] THEN
    GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC [set_of_list, polygonal_path, PATH_IMAGE_LINEPATH] THEN
    REWRITE_TAC [SEGMENT_REFL, INSERT_AC, SUBSET_REFL] THEN
     GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC [set_of_list, polygonal_path] THEN CONJ_TAC THENL
     [REWRITE_TAC [PATH_IMAGE_LINEPATH, INSERT_SUBSET, ENDS_IN_SEGMENT] THEN
      REWRITE_TAC [EMPTY_SUBSET],
      REPEAT GEN_TAC THEN REPLICATE_TAC 3 DISCH_TAC THEN
      ONCE_REWRITE_TAC [INSERT_SUBSET] THEN
      SIMP_TAC [PATH_IMAGE_JOIN, PATHFINISH_LINEPATH, PATHSTART_POLYGONAL_PATH,
          Session.listDefs.HD, Session.listThms1.NOT_CONS_NIL, IN_UNION, ENDS_IN_SEGMENT, PATH_IMAGE_LINEPATH] THEN
      HolLight.ASM SET_TAC []])
  : ExceptT String IO thm).run
#eval VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH

#eval phrase 37
def ARC_POLYGONAL_PATH_IMP_DISTINCT : thm := keep "ARC_POLYGONAL_PATH_IMP_DISTINCT" fun _ => (do
  prove ([[!p:(real^N)list. arc(polygonal_path p) ==> PAIRWISE (\x y. ~(x = y)) p]])
   (MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC [polygonal_path, ARC_LINEPATH_EQ] THEN
    X_GEN_TAC ([[a:real^N]]) THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC [polygonal_path, ARC_LINEPATH_EQ] THEN
    X_GEN_TAC ([[b:real^N]]) THEN
    MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC [polygonal_path, ARC_LINEPATH_EQ] THEN CONJ_TAC THENL
     [REWRITE_TAC [Session.listDefs.PAIRWISE, Session.listDefs.ALL], ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [([[c:real^N]]), ([[p:(real^N)list]])] THEN
    REPLICATE_TAC 3 DISCH_TAC THEN
    SIMP_TAC [ARC_JOIN_EQ, PATHFINISH_LINEPATH, PATHSTART_POLYGONAL_PATH,
             Session.listDefs.HD, Session.listThms1.NOT_CONS_NIL, ARC_LINEPATH_EQ] THEN
    STRIP_TAC THEN ONCE_REWRITE_TAC [Session.listDefs.PAIRWISE] THEN
    ASM_SIMP_TAC [] THEN REWRITE_TAC [Session.listDefs.ALL] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [SUBSET]) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[a:real^N]])) THEN
    ASM_REWRITE_TAC [IN_INTER, IN_SING, ENDS_IN_SEGMENT, PATH_IMAGE_LINEPATH] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM CONTRAPOS_THM)] (← HolLight.REWRITE_RULE [SUBSET] VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH))) THEN
    ASM_REWRITE_TAC [IN_SET_OF_LIST, Session.listDefs.MEM, DE_MORGAN_THM, (← HolLight.GSYM Session.listThms1.ALL_MEM)] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval ARC_POLYGONAL_PATH_IMP_DISTINCT

#eval phrase 38
def PATH_POLYGONAL_PATH : thm := keep "PATH_POLYGONAL_PATH" fun _ => (do
  prove ([[!p:(real^N)list. path(polygonal_path p)]])
   (MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC [polygonal_path, PATH_LINEPATH] THEN
    GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC [polygonal_path, PATH_LINEPATH] THEN
    GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC [polygonal_path, PATH_LINEPATH] THEN
    SIMP_TAC [PATH_JOIN, PATHFINISH_LINEPATH, PATHSTART_POLYGONAL_PATH,
             Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD, PATH_LINEPATH])
  : ExceptT String IO thm).run
#eval PATH_POLYGONAL_PATH

#eval phrase 39
def PATH_IMAGE_POLYGONAL_PATH_SUBSET_CONVEX_HULL : thm := keep "PATH_IMAGE_POLYGONAL_PATH_SUBSET_CONVEX_HULL" fun _ => (do
  prove ([[!p. ~(p = [])
       ==> path_image(polygonal_path p) SUBSET convex hull (set_of_list p)]])
   (MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [] THEN GEN_TAC THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [Session.listThms1.NOT_CONS_NIL] THEN CONJ_TAC THENL
     [REWRITE_TAC [polygonal_path, PATH_IMAGE_LINEPATH, set_of_list] THEN
      REWRITE_TAC [SEGMENT_REFL, CONVEX_HULL_SING] THEN SET_TAC [],
      GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
      REWRITE_TAC [polygonal_path] THEN CONJ_TAC THENL
       [REWRITE_TAC [polygonal_path, PATH_IMAGE_LINEPATH, set_of_list] THEN
        REWRITE_TAC [SEGMENT_CONVEX_HULL, SUBSET_REFL],
        REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_PATH_IMAGE_JOIN THEN
        REWRITE_TAC [PATH_IMAGE_LINEPATH, SEGMENT_CONVEX_HULL, set_of_list] THEN
        SIMP_TAC [HULL_MONO, INSERT_SUBSET, EMPTY_SUBSET, IN_INSERT] THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] SUBSET_TRANS)) THEN
        MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC [set_of_list] THEN
        SET_TAC []]])
  : ExceptT String IO thm).run
#eval PATH_IMAGE_POLYGONAL_PATH_SUBSET_CONVEX_HULL

#eval phrase 40
def PATH_IMAGE_POLYGONAL_PATH_SUBSET_SEGMENTS : thm := keep "PATH_IMAGE_POLYGONAL_PATH_SUBSET_SEGMENTS" fun _ => (do
  let h3 ← sr (← ExceptT.mk [[(sab INTER p) SUBSET {b}
          ==> !sde a. sde SUBSET p /\
              ~(b IN sde) /\ d IN sde /\ a IN sde /\ a IN sab
              ==> F]])
  let h2 ← ar (← ExceptT.mk [[3 <= SUC(SUC p) <=> ~(p = 0)]])
  let h1 ← sr (← ExceptT.mk [[!p b. (s INTER p) SUBSET {b} /\
      x IN p /\ b IN s /\ ~(x = b)
      ==> ~(x IN s)]])
  prove ([[!p x:real^N.
        arc(polygonal_path p) /\ 3 <= LENGTH p /\
        x IN path_image(polygonal_path p)
        ==> ?a b. MEM a p /\ MEM b p /\ x IN segment[a,b] /\
                  segment[a,b] SUBSET path_image(polygonal_path p) /\
                  ~(pathstart(polygonal_path p) IN segment[a,b] /\
                    pathfinish(polygonal_path p) IN segment[a,b])]])
   (MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN
    X_GEN_TAC ([[a:real^N]]) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN
    X_GEN_TAC ([[b:real^N]]) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN
    X_GEN_TAC ([[c:real^N]]) THEN X_GEN_TAC ([[p:(real^N)list]]) THEN
    REPEAT DISCH_TAC THEN REWRITE_TAC [polygonal_path] THEN
    X_GEN_TAC ([[x:real^N]]) THEN
    REWRITE_TAC [PATHSTART_JOIN, PATHFINISH_JOIN] THEN
    SIMP_TAC [PATH_IMAGE_JOIN, PATHFINISH_LINEPATH, PATHSTART_POLYGONAL_PATH,
             ARC_JOIN_EQ, Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD] THEN
    REWRITE_TAC [PATHSTART_LINEPATH, PATH_IMAGE_LINEPATH, ARC_LINEPATH] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [IN_UNION] THEN STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [([[a:real^N]]), ([[b:real^N]])] THEN
      ASM_REWRITE_TAC [Session.listDefs.MEM, SUBSET_UNION, ENDS_IN_SEGMENT] THEN
      FIRST_X_ASSUM (CONJUNCTS_THEN MP_TAC) THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP ARC_DISTINCT_ENDS) THEN
      REWRITE_TAC [PATHSTART_POLYGONAL_PATH, Session.listDefs.HD, Session.listThms1.NOT_CONS_NIL] THEN
      DISCH_TAC THEN REWRITE_TAC [ARC_LINEPATH_EQ] THEN DISCH_TAC THEN
      MATCH_MP_TAC h1 THEN
      MAP_EVERY EXISTS_TAC [([[path_image(polygonal_path (CONS (b:real^N) (CONS c p)))]]),
        ([[b:real^N]])] THEN
      ASM_REWRITE_TAC [ENDS_IN_SEGMENT, PATHFINISH_IN_PATH_IMAGE],
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[x:real^N]])) THEN
      ASM_REWRITE_TAC [h2] THEN
      REWRITE_TAC [Session.listThms1.LENGTH_EQ_NIL] THEN ASM_CASES_TAC ([[p:(real^N)list = [] ]]) THENL
       [ASM_REWRITE_TAC [Session.listDefs.LENGTH, polygonal_path] THEN
        REWRITE_TAC [PATHFINISH_LINEPATH, PATH_IMAGE_LINEPATH] THEN
        UNDISCH_TAC ([[x IN path_image(polygonal_path (CONS (b:real^N) (CONS c p)))]]) THEN
        ASM_REWRITE_TAC [polygonal_path, PATH_IMAGE_LINEPATH] THEN
        DISCH_TAC THEN MAP_EVERY EXISTS_TAC [([[b:real^N]]), ([[c:real^N]])] THEN
        ASM_REWRITE_TAC [Session.listDefs.MEM, SUBSET_UNION, ENDS_IN_SEGMENT] THEN
        FIRST_X_ASSUM (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        ASM_REWRITE_TAC [polygonal_path, PATH_IMAGE_LINEPATH] THEN
        REWRITE_TAC [ARC_LINEPATH_EQ] THEN
        MP_TAC (← HolLight.ISPECL [([[a:real^N]]), ([[b:real^N]])] ENDS_IN_SEGMENT) THEN
        FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP ARC_DISTINCT_ENDS) THEN
        REWRITE_TAC [PATHSTART_LINEPATH, PATHFINISH_LINEPATH] THEN SET_TAC [],
        ASM_REWRITE_TAC [Session.listThms1.LENGTH_EQ_NIL] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[d:real^N]]) THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[e:real^N]]) THEN
        REWRITE_TAC [PATHSTART_POLYGONAL_PATH, Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD] THEN
        REPEAT STRIP_TAC THENL
         [ASM_MESON_TAC [Session.listDefs.MEM],
          ASM_MESON_TAC [Session.listDefs.MEM],
          ASM_REWRITE_TAC [],
          HolLight.ASM SET_TAC [],
          FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h3 o (HolCore.Lib.el (α := thm)) 2 o HolLight.CONJUNCTS) THEN
          MAP_EVERY EXISTS_TAC [([[segment[d:real^N,e] ]]), ([[a:real^N]])] THEN
          ASM_REWRITE_TAC [ENDS_IN_SEGMENT] THEN ASM_MESON_TAC []]]])
  : ExceptT String IO thm).run
#eval PATH_IMAGE_POLYGONAL_PATH_SUBSET_SEGMENTS

/- ------------------------------------------------------------------------- -/
/- Rotating the starting point to move a preferred vertex forward.           -/
/- ------------------------------------------------------------------------- -/

#eval phrase 41
def SET_OF_LIST_POLYGONAL_PATH_ROTATE : thm := keep "SET_OF_LIST_POLYGONAL_PATH_ROTATE" fun _ => (do
  prove ([[!p. ~(p = []) ==> set_of_list(CONS (LAST p) (BUTLAST p)) = set_of_list p]])
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.RAND_CONV) [(← HolLight.GSYM (← HolLight.MATCH_MP Session.listThms2.APPEND_BUTLAST_LAST th))])) THEN
    REWRITE_TAC [SET_OF_LIST_APPEND, set_of_list] THEN SET_TAC [])
  : ExceptT String IO thm).run
#eval SET_OF_LIST_POLYGONAL_PATH_ROTATE

#eval phrase 42
def PROPERTIES_POLYGONAL_PATH_SNOC : thm := keep "PROPERTIES_POLYGONAL_PATH_SNOC" fun _ => (do
  let h3 ← tt (← ExceptT.mk [[((q <=> p) /\ (q' <=> p')) /\ (p <=> p')
      ==> (p <=> p') /\ (q <=> q')]])
  let h2 ← tt (← ExceptT.mk [[(~p /\ ~p') /\ (q <=> q') ==> (p <=> p') /\ (q <=> q')]])
  let h1 ← ar (← ExceptT.mk [[2 <= SUC(SUC n)]])
  prove ([[!p d:real^N.
        2 <= LENGTH p
        ==> path_image(polygonal_path(APPEND p [d])) =
            path_image(polygonal_path p ++ linepath(LAST p,d)) /\
            (arc(polygonal_path(APPEND p [d])) <=>
             arc(polygonal_path p ++ linepath(LAST p,d))) /\
            (simple_path(polygonal_path(APPEND p [d])) <=>
             simple_path(polygonal_path p ++ linepath(LAST p,d)))]])
   (MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN
    X_GEN_TAC ([[a:real^N]]) THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN X_GEN_TAC ([[b:real^N]]) THEN
    MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
     [REWRITE_TAC [Session.listDefs.APPEND, polygonal_path, Session.listDefs.LAST, Session.listThms1.NOT_CONS_NIL], ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [([[c:real^N]]), ([[p:(real^N)list]])] THEN REPEAT DISCH_TAC THEN
    X_GEN_TAC ([[d:real^N]]) THEN DISCH_TAC THEN REWRITE_TAC [Session.listDefs.APPEND] THEN
    ONCE_REWRITE_TAC [Session.listDefs.LAST] THEN REWRITE_TAC [Session.listThms1.NOT_CONS_NIL] THEN
    ONCE_REWRITE_TAC [polygonal_path] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[d:real^N]])) THEN POP_ASSUM_LIST ((fun _ => ALL_TAC)) THEN
    REWRITE_TAC [Session.listDefs.APPEND, Session.listDefs.LENGTH, h1] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    SIMP_TAC [(← HolLight.GSYM ARC_ASSOC), (← HolLight.GSYM SIMPLE_PATH_ASSOC), PATHSTART_JOIN,
             PATHFINISH_JOIN, PATHSTART_POLYGONAL_PATH,
             PATHFINISH_POLYGONAL_PATH,
             PATHSTART_LINEPATH, PATHFINISH_LINEPATH, Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD] THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [ASM_SIMP_TAC [PATH_IMAGE_JOIN, PATHSTART_JOIN, PATHFINISH_JOIN,
             PATHSTART_POLYGONAL_PATH, PATHFINISH_POLYGONAL_PATH,
             PATHSTART_LINEPATH, PATHFINISH_LINEPATH, Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD] THEN
      REWRITE_TAC [UNION_ACI],
      ALL_TAC] THEN
    ASM_CASES_TAC ([[a:real^N = d]]) THENL
     [MATCH_MP_TAC h2 THEN
      CONJ_TAC THENL
       [REWRITE_TAC [ARC_SIMPLE_PATH, PATHSTART_JOIN, PATHFINISH_JOIN] THEN
        REWRITE_TAC [PATHSTART_LINEPATH, PATHFINISH_LINEPATH] THEN
        ASM_REWRITE_TAC [PATHFINISH_POLYGONAL_PATH, Session.listThms1.NOT_CONS_NIL, Session.listDefs.LAST,
                        Session.listThms2.APPEND_EQ_NIL, Session.listThms2.LAST_APPEND],
        ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN
      HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
          let x1 ← ec (HolCore.Equal.lhs w)
          let x2 ← ExceptT.mk (HolLight.PART_MATCH (HolCore.Equal.lhs o HolCore.Kernel.rand) SIMPLE_PATH_JOIN_LOOP_EQ x1)
          pure (MP_TAC x2)) THEN
      ANTS_TAC THENL
       [REWRITE_TAC [PATHSTART_POLYGONAL_PATH, PATHFINISH_LINEPATH] THEN
        REWRITE_TAC [PATHFINISH_POLYGONAL_PATH, PATHSTART_LINEPATH] THEN
        REWRITE_TAC [Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD, Session.listDefs.LAST, Session.listThms2.LAST_APPEND, Session.listThms2.APPEND_EQ_NIL],
        DISCH_THEN SUBST1_TAC] THEN
      HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
          let x1 ← ec (HolCore.Equal.rhs w)
          let x2 ← ExceptT.mk (HolLight.PART_MATCH (HolCore.Equal.lhs o HolCore.Kernel.rand) SIMPLE_PATH_JOIN_LOOP_EQ x1)
          pure (MP_TAC x2)) THEN
      ANTS_TAC THENL
       [REWRITE_TAC [PATHSTART_JOIN, PATHFINISH_JOIN, PATHSTART_LINEPATH,
                    PATHFINISH_LINEPATH, PATHSTART_POLYGONAL_PATH,
                    PATHFINISH_POLYGONAL_PATH] THEN
        REWRITE_TAC [Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD, Session.listDefs.LAST, Session.listThms2.LAST_APPEND, Session.listThms2.APPEND_EQ_NIL],
        DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [PATHSTART_JOIN, PATHSTART_POLYGONAL_PATH, Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD],
      MATCH_MP_TAC h3 THEN
      CONJ_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC SIMPLE_PATH_EQ_ARC THEN
        REWRITE_TAC [PATHSTART_JOIN, PATHFINISH_JOIN, PATHSTART_LINEPATH,
                    PATHFINISH_LINEPATH, PATHSTART_POLYGONAL_PATH,
                    PATHFINISH_POLYGONAL_PATH] THEN
        ASM_REWRITE_TAC [Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD, Session.listDefs.LAST, Session.listThms2.LAST_APPEND, Session.listThms2.APPEND_EQ_NIL],
        ALL_TAC] THEN
      HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
          let x1 ← ec (HolCore.Equal.lhs w)
          let x2 ← ExceptT.mk (HolLight.PART_MATCH (HolCore.Equal.lhs o HolCore.Kernel.rand) ARC_JOIN_EQ x1)
          pure (MP_TAC x2)) THEN
      ANTS_TAC THENL
       [REWRITE_TAC [PATHSTART_POLYGONAL_PATH, PATHFINISH_LINEPATH] THEN
        REWRITE_TAC [Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD],
        DISCH_THEN SUBST1_TAC] THEN
      HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
          let x1 ← ec (HolCore.Equal.rhs w)
          let x2 ← ExceptT.mk (HolLight.PART_MATCH (HolCore.Equal.lhs o HolCore.Kernel.rand) ARC_JOIN_EQ x1)
          pure (MP_TAC x2)) THEN
      ANTS_TAC THENL
       [SIMP_TAC [PATHSTART_POLYGONAL_PATH, PATHFINISH_LINEPATH, PATHSTART_JOIN,
                 Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD],
        DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [PATHSTART_JOIN, PATHSTART_POLYGONAL_PATH, Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD]])
  : ExceptT String IO thm).run
#eval PROPERTIES_POLYGONAL_PATH_SNOC

#eval phrase 43
def PATH_IMAGE_POLYGONAL_PATH_ROTATE : thm := keep "PATH_IMAGE_POLYGONAL_PATH_ROTATE" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[2 <= SUC(SUC n)]])
  prove ([[!p:(real^N)list.
        2 <= LENGTH p /\ LAST p = HD p
        ==> path_image(polygonal_path(APPEND (TL p) [HD(TL p)])) =
            path_image(polygonal_path p)]])
   (MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN
    X_GEN_TAC ([[a:real^N]]) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN
    X_GEN_TAC ([[b:real^N]]) THEN REWRITE_TAC [Session.listDefs.HD, Session.listDefs.TL] THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN CONJ_TAC THENL
     [REWRITE_TAC [Session.listDefs.LAST, Session.listDefs.APPEND, Session.listThms1.NOT_CONS_NIL] THEN MESON_TAC [], ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [([[c:real^N]]), ([[p:(real^N)list]])] THEN
    REPLICATE_TAC 3 (DISCH_THEN ((fun _ => ALL_TAC))) THEN
    DISCH_THEN (MP_TAC o HolLight.CONJUNCT2) THEN
    REWRITE_TAC [Session.listDefs.LAST, Session.listThms1.NOT_CONS_NIL] THEN ONCE_REWRITE_TAC [(← HolLight.GSYM Session.listDefs.LAST)] THEN
    DISCH_TAC THEN
    SIMP_TAC [PROPERTIES_POLYGONAL_PATH_SNOC, Session.listDefs.LENGTH,
             h1] THEN
    ONCE_REWRITE_TAC [Session.listDefs.LAST] THEN ASM_REWRITE_TAC [Session.listThms1.NOT_CONS_NIL] THEN
    GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.RAND_CONV) [polygonal_path] THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [Session.listDefs.LAST]) THEN
    ASM_SIMP_TAC [PATH_IMAGE_JOIN, PATHSTART_LINEPATH, PATHFINISH_LINEPATH,
             PATHSTART_POLYGONAL_PATH, PATHFINISH_POLYGONAL_PATH,
             Session.listDefs.LAST, Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD] THEN
    REWRITE_TAC [UNION_ACI])
  : ExceptT String IO thm).run
#eval PATH_IMAGE_POLYGONAL_PATH_ROTATE

#eval phrase 44
def SIMPLE_PATH_POLYGONAL_PATH_ROTATE : thm := keep "SIMPLE_PATH_POLYGONAL_PATH_ROTATE" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[2 <= SUC(SUC n)]])
  prove ([[!p:(real^N)list.
        2 <= LENGTH p /\ LAST p = HD p
        ==> (simple_path(polygonal_path(APPEND (TL p) [HD(TL p)])) =
             simple_path(polygonal_path p))]])
   (MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN
    X_GEN_TAC ([[a:real^N]]) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN
    X_GEN_TAC ([[b:real^N]]) THEN REWRITE_TAC [Session.listDefs.HD, Session.listDefs.TL] THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN CONJ_TAC THENL
     [REWRITE_TAC [Session.listDefs.LAST, Session.listDefs.APPEND, Session.listThms1.NOT_CONS_NIL] THEN MESON_TAC [], ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [([[c:real^N]]), ([[p:(real^N)list]])] THEN
    REPLICATE_TAC 3 (DISCH_THEN ((fun _ => ALL_TAC))) THEN
    DISCH_THEN (MP_TAC o HolLight.CONJUNCT2) THEN
    REWRITE_TAC [Session.listDefs.LAST, Session.listThms1.NOT_CONS_NIL] THEN ONCE_REWRITE_TAC [(← HolLight.GSYM Session.listDefs.LAST)] THEN
    DISCH_TAC THEN
    SIMP_TAC [PROPERTIES_POLYGONAL_PATH_SNOC, Session.listDefs.LENGTH,
             h1] THEN
    ONCE_REWRITE_TAC [Session.listDefs.LAST] THEN ASM_REWRITE_TAC [Session.listThms1.NOT_CONS_NIL] THEN
    GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.RAND_CONV) [polygonal_path] THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [Session.listDefs.LAST]) THEN
    ASM_SIMP_TAC [SIMPLE_PATH_JOIN_LOOP_EQ, PATHSTART_LINEPATH,
                 PATHFINISH_LINEPATH, PATHSTART_POLYGONAL_PATH,
                 PATHFINISH_POLYGONAL_PATH, Session.listDefs.LAST, Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD] THEN
    REWRITE_TAC [INSERT_AC, INTER_ACI, CONJ_ACI])
  : ExceptT String IO thm).run
#eval SIMPLE_PATH_POLYGONAL_PATH_ROTATE

#eval phrase 45
def ROTATE_LIST_TO_FRONT_1 : thm := keep "ROTATE_LIST_TO_FRONT_1" fun _ => (do
  let lemma0 ← prove ([[!P. (!i. P i /\ 0 < i ==> P(i - 1)) /\ (?k. 0 < k /\ P k)
             ==> P 1]])
     (REPEAT STRIP_TAC THEN
        SUBGOAL_THEN ([[!i:num. i < k ==> P(k - i)]]) MP_TAC THENL
         [INDUCT_TAC THEN ASM_REWRITE_TAC [SUB_0] THEN DISCH_TAC THEN
          REWRITE_TAC [(← ar (← ExceptT.mk [[k - SUC i = k - i - 1]]))] THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN
          CONJ_TAC THEN TRY (FIRST_X_ASSUM MATCH_MP_TAC) THEN ASM_ARITH_TAC,
          DISCH_THEN (MP_TAC o HolLight.SPEC ([[k - 1]])) THEN
          ASM_SIMP_TAC [(← ar (← ExceptT.mk [[0 < k ==> k - 1 < k /\ k - (k - 1) = 1]]))]])
  let h6 ← ar (← ExceptT.mk [[0 < k ==> k - 1 + 1 = k]])
  let h5 ← ar (← ExceptT.mk [[~(3 <= 0)]])
  let h4 ← ar (← ExceptT.mk [[3 <= n ==> n - 2 + 1 = n - 1]])
  let h3 ← ar (← ExceptT.mk [[3 <= n ==> n - 2 < n - 1]])
  let h2 ← ar (← ExceptT.mk [[i = 0 \/ 0 < i]])
  let h1 ← ar (← ExceptT.mk [[~(3 <= 0)]])
  prove ([[!P l a:A.
      (!l. P(l) ==> 3 <= LENGTH l /\ LAST l = HD l) /\
      (!l. P(l) ==> P(APPEND (TL l) [HD(TL l)])) /\
      P l /\ MEM a l
      ==> ?l'. EL 1 l' = a /\ P l']])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[?i l'. 0 < i /\ i < LENGTH l' /\ P l' /\ EL i l' = (a:A)]]) MP_TAC THENL
     [SUBGOAL_THEN ([[~(l:A list = [])]]) ASSUME_TAC THENL
       [ASM_MESON_TAC [Session.listDefs.LENGTH, h1], ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [Session.listThms2.MEM_EXISTS_EL]) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[i:num]]) STRIP_ASSUME_TAC) THEN
      DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC h2 THENL
       [EXISTS_TAC ([[LENGTH(l:A list) - 2]]) THEN
        EXISTS_TAC ([[(APPEND (TL l) [HD(TL l):A])]]) THEN
        ASM_SIMP_TAC [Session.listThms1.LENGTH_APPEND, Session.listThms2.LENGTH_TL, Session.listThms2.EL_APPEND] THEN
        REWRITE_TAC [LT_REFL, Session.listDefs.LENGTH, SUB_REFL, Session.listDefs.EL, Session.listDefs.HD] THEN
        SUBGOAL_THEN ([[3 <= LENGTH(l:A list)]]) ASSUME_TAC THENL
         [ASM_MESON_TAC [], ALL_TAC] THEN
        REPLICATE_TAC 2 (CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC]) THEN
        ASM_SIMP_TAC [h3] THEN
        ASM_SIMP_TAC [Session.listThms2.EL_TL, h4] THEN
        ASM_MESON_TAC [Session.listThms2.LAST_EL],
        MAP_EVERY EXISTS_TAC [([[i:num]]), ([[l:A list]])] THEN ASM_REWRITE_TAC []],
      REWRITE_TAC [RIGHT_EXISTS_AND_THM] THEN
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← HolLight.ONCE_REWRITE_RULE [IMP_CONJ_ALT] lemma0)) THEN
      ANTS_TAC THENL [ALL_TAC, MESON_TAC []] THEN X_GEN_TAC ([[k:num]]) THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[m:A list]]) STRIP_ASSUME_TAC) THEN
      EXISTS_TAC ([[APPEND (TL m) [HD(TL m):A] ]]) THEN
      SUBGOAL_THEN ([[~(m:A list = [])]]) ASSUME_TAC THENL
       [ASM_MESON_TAC [Session.listDefs.LENGTH, h5], ALL_TAC] THEN
      ASM_SIMP_TAC [Session.listThms1.LENGTH_APPEND, Session.listThms2.LENGTH_TL, Session.listThms2.EL_APPEND] THEN
      ASM_REWRITE_TAC [Session.listDefs.LENGTH] THEN CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      COND_CASES_TAC THENL [ALL_TAC, ASM_ARITH_TAC] THEN
      ASM_SIMP_TAC [Session.listThms2.EL_TL, h6]])
  : ExceptT String IO thm).run
#eval ROTATE_LIST_TO_FRONT_1

#eval phrase 46
def ROTATE_LIST_TO_FRONT_0 : thm := keep "ROTATE_LIST_TO_FRONT_0" fun _ => (do
  let h1 ← nc (← ExceptT.mk [[1]])
  prove ([[!P l a:A.
      (!l. P(l) ==> 3 <= LENGTH l /\ LAST l = HD l) /\
      (!l. P(l) ==> P(APPEND (TL l) [HD(TL l)])) /\
      P l /\ MEM a l
      ==> ?l'. HD l' = a /\ P l']])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[P:A list->bool]]), ([[l:A list]]), ([[a:A]])] ROTATE_LIST_TO_FRONT_1) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC ([[l':A list]]) THEN
    STRIP_TAC THEN EXISTS_TAC ([[APPEND (TL l') [HD(TL l'):A] ]]) THEN
    ASM_SIMP_TAC [] THEN UNDISCH_TAC ([[EL 1 l' = (a:A)]]) THEN
    SUBGOAL_THEN ([[3 <= LENGTH(l':A list)]]) MP_TAC THENL
     [ASM_MESON_TAC [], ALL_TAC] THEN
    SPEC_TAC (([[l':A list]]), ([[p:A list]])) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN
    GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN
    REWRITE_TAC [Session.listDefs.APPEND, Session.listDefs.HD, Session.listDefs.TL, h1, Session.listDefs.EL])
  : ExceptT String IO thm).run
#eval ROTATE_LIST_TO_FRONT_0

/- ------------------------------------------------------------------------- -/
/- We can pick a transformation to make all y coordinates distinct.          -/
/- ------------------------------------------------------------------------- -/

#eval phrase 47
def DISTINGUISHING_ROTATION_EXISTS_PAIR : thm := keep "DISTINGUISHING_ROTATION_EXISTS_PAIR" fun _ => (do
  let h3 ← sr (← ExceptT.mk [[(!x y. x IN s /\ y IN s ==> x = y) ==> ?a. s SUBSET {a}]])
  let h2 ← ms [FINITE_SING, FINITE_SUBSET] (← ExceptT.mk [[(?a. s SUBSET {a}) ==> FINITE s]])
  let h1 ← sr (← ExceptT.mk [[{x | p x /\ q x /\ (r x \/ s x)} =
    {x | p x /\ q x /\ r x} UNION {x | p x /\ q x /\ s x}]])
  prove ([[!x y. ~(x = y)
         ==> FINITE {t | &0 <= t /\ t < &2 * pi /\
                         (rotate2d t x)$2 = (rotate2d t y)$2}]])
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [(← HolLight.GSYM REAL_SUB_0)] THEN
    ONCE_REWRITE_TAC [(← HolLight.GSYM VECTOR_SUB_COMPONENT)] THEN
    ONCE_REWRITE_TAC [(← HolLight.GSYM ROTATE2D_SUB)] THEN
    REWRITE_TAC [(← HolLight.GSYM IM_DEF), (← HolLight.GSYM real), (← HolLight.GSYM ARG_EQ_0_PI)] THEN
    REWRITE_TAC [FINITE_UNION, h1] THEN
    CONJ_TAC THEN
    MATCH_MP_TAC h2 THEN
    MATCH_MP_TAC h3 THEN
    REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ARG_ROTATE2D_UNIQUE_2PI THEN EXISTS_TAC ([[x - y:complex]]) THEN
    ASM_REWRITE_TAC [COMPLEX_SUB_0])
  : ExceptT String IO thm).run
#eval DISTINGUISHING_ROTATION_EXISTS_PAIR

#eval phrase 48
def DISTINGUISHING_ROTATION_EXISTS : thm := keep "DISTINGUISHING_ROTATION_EXISTS" fun _ => (do
  let h1 ← ms [FINITE_EMPTY, INFINITE] (← ExceptT.mk [[INFINITE s ==> ~(s = {})]])
  prove ([[!s. FINITE s ==> ?t. pairwise (\x y. ~(x$2 = y$2)) (IMAGE (rotate2d t) s)]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[INFINITE ({t | &0 <= t /\ t < &2 * pi} DIFF
              UNIONS (IMAGE (\(x,y). {t | &0 <= t /\ t < &2 * pi /\
                                          (rotate2d t x)$2 = (rotate2d t y)$2})
                            ({(x,y) | x IN s /\ y IN s /\ ~(x = y)})))]]) MP_TAC THENL
     [MATCH_MP_TAC INFINITE_DIFF_FINITE THEN
      REWRITE_TAC [INFINITE, FINITE_REAL_INTERVAL, REAL_NOT_LE] THEN
      CONJ_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC2, ALL_TAC] THEN
      REWRITE_TAC [FINITE_UNIONS] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC ([[{(x:real^2,y:real^2) | x IN s /\ y IN s}]]) THEN
        ASM_SIMP_TAC [FINITE_PRODUCT_DEPENDENT] THEN SET_TAC [],
        REWRITE_TAC [FORALL_IN_IMAGE, FORALL_IN_GSPEC] THEN
        ASM_SIMP_TAC [DISTINGUISHING_ROTATION_EXISTS_PAIR]],
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP h1) THEN
      REWRITE_TAC [(← HolLight.GSYM MEMBER_NOT_EMPTY), IN_DIFF, IN_ELIM_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[t:real]]) THEN
      DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
      REWRITE_TAC [UNIONS_IMAGE, EXISTS_IN_GSPEC] THEN
      REWRITE_TAC [pairwise, IN_ELIM_THM] THEN
      REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_IMAGE] THEN
      ASM_REWRITE_TAC [ROTATE2D_EQ] THEN MESON_TAC []])
  : ExceptT String IO thm).run
#eval DISTINGUISHING_ROTATION_EXISTS

#eval phrase 49
def DISTINGUISHING_ROTATION_EXISTS_POLYGON : thm := keep "DISTINGUISHING_ROTATION_EXISTS_POLYGON" fun _ => (do
  prove ([[!p:(real^2)list.
        ?f q. (?g. orthogonal_transformation g /\ f = MAP g) /\
              (!x y. MEM x q /\ MEM y q /\ ~(x = y) ==> ~(x$2 = y$2)) /\
              f q = p]])
   (GEN_TAC THEN MP_TAC (← HolLight.ISPEC ([[set_of_list(p:(real^2)list)]]) DISTINGUISHING_ROTATION_EXISTS) THEN
    REWRITE_TAC [FINITE_SET_OF_LIST, pairwise] THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_IMAGE] THEN
    REWRITE_TAC [IN_SET_OF_LIST, ROTATE2D_EQ] THEN
    REWRITE_TAC [IMP_IMP, RIGHT_IMP_FORALL_THM, (← HolLight.GSYM CONJ_ASSOC)] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[t:real]]) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC ([[MAP (rotate2d(--t))]]) THEN
    EXISTS_TAC ([[MAP (rotate2d t) p]]) THEN
    REWRITE_TAC [(← HolLight.GSYM Session.listThms1.MAP_o), o_DEF, (← HolLight.GSYM ROTATE2D_ADD)] THEN
    REWRITE_TAC [REAL_ADD_LINV, ROTATE2D_ZERO, Session.listThms2.MAP_ID] THEN
    CONJ_TAC THENL [MESON_TAC [ORTHOGONAL_TRANSFORMATION_ROTATE2D], ALL_TAC] THEN
    REWRITE_TAC [(← HolLight.GSYM IN_SET_OF_LIST), SET_OF_LIST_MAP] THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_IMAGE] THEN
    ASM_REWRITE_TAC [IN_SET_OF_LIST, ROTATE2D_EQ] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval DISTINGUISHING_ROTATION_EXISTS_POLYGON

/- ------------------------------------------------------------------------- -/
/- Proof that we can chop a polygon's inside in two.                         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 50
set_option maxHeartbeats 2000000 in
def POLYGON_CHOP_IN_TWO : thm := keep "POLYGON_CHOP_IN_TWO" fun _ => (do
  let wlog_lemma ← ms [] (← ExceptT.mk [[(!x. ?f:A->A y. transform f /\ nice y /\ f y = x)
    ==> !P. (!f x. transform f ==> (P(f x) <=> P x)) /\
            (!x. nice x ==> P x)
            ==> !x. P x]])
  let between_lemma ← prove ([[!a c u v m:real^N.
          collinear {a,c,u,v,m} /\ m IN segment[u,v] /\ m IN segment(a,c)
          ==> u IN segment(a,c) \/ v IN segment(a,c) \/
              segment[a,c] SUBSET segment[u,v] ]])
     (REPEAT GEN_TAC THEN
      ONCE_REWRITE_TAC [IMP_CONJ] THEN REWRITE_TAC [COLLINEAR_AFFINE_HULL] THEN
      REWRITE_TAC [INSERT_SUBSET, LEFT_IMP_EXISTS_THM, EMPTY_SUBSET] THEN
      MAP_EVERY X_GEN_TAC [([[origin:real^N]]), ([[dir:real^N]])] THEN
      GEOM_ORIGIN_TAC ([[origin:real^N]]) THEN
      REWRITE_TAC [AFFINE_HULL_2, VECTOR_MUL_RZERO, VECTOR_ADD_LID] THEN
      REWRITE_TAC [IN_ELIM_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [] THEN ASM_CASES_TAC ([[dir:real^N = vec 0]]) THENL
       [ASM_REWRITE_TAC [VECTOR_MUL_RZERO, SEGMENT_REFL, SUBSET_REFL],
        ALL_TAC] THEN
      REWRITE_TAC [SUBSET_SEGMENT] THEN
      ASM_SIMP_TAC [SEGMENT_SCALAR_MULTIPLE, IN_ELIM_THM] THEN
      ASM_REWRITE_TAC [VECTOR_MUL_RCANCEL] THEN
      REWRITE_TAC [(← HolLight.ONCE_REWRITE_RULE [CONJ_SYM] UNWIND_THM1)] THEN
      REAL_ARITH_TAC2)
  let h111 ← va (← ExceptT.mk [[(u % a + v % c) - b:real^N =
        u % (a - b) + v % (c - b) + ((u + v) - &1) % b]])
  let h110 ← sr (← ExceptT.mk [[{a,v,c} = {a,c,v}]])
  let h109 ← sr (← ExceptT.mk [[{a,b,c} = {a,c,b}]])
  let h108 ← sr (← ExceptT.mk [[{a,c,b} = {a,b,c}]])
  let h107 ← sr (← ExceptT.mk [[{a,b,c} = {a,c,b}]])
  let h106 ← rr (← ExceptT.mk [[!mx. n dot (u - b) <= m /\
           ~(n dot (u - b) < n dot (c - b)) /\
           n dot (mx - b) = m /\
           n dot (mx - b) <= n dot (c - b)
           ==> n dot (u - b) = m /\ n dot (c - b) = m]])
  let h105 ← rr (← ExceptT.mk [[r * x + s * x < x <=> &0 < (&1 - r - s) * x]])
  let h104 ← va (← ExceptT.mk [[(r % a + s % b + t % c) - b =
      r % (a - b) + t % (c - b) + ((r + s + t) - &1) % b]])
  let h103 ← rr (← ExceptT.mk [[&0 <= (&1 - q) * r + q * s <=> q * (r - s) <= r]])
  let h102 ← rr (← ExceptT.mk [[((&1 - q) * rx + q * r) +
      q * s +
      ((&1 - q) * tx + q * t) =
      (rx + tx) + q * ((r + s + t) - (rx + tx))]])
  let h101 ← rr (← ExceptT.mk [[&0 <= a /\ &0 <= x /\ &0 <= b ==> abs(min a (min b x)) <= x]])
  let h100 ← rr (← ExceptT.mk [[~(x = y) ==> &0 < abs(x - y)]])
  let h99 ← rr (← ExceptT.mk [[abs x <= a ==> x <= a]])
  let h98 ← rr (← ExceptT.mk [[&0 <= a /\ &0 <= x /\ &0 <= b ==> abs(min a (min x b)) <= x]])
  let h97 ← rr (← ExceptT.mk [[~(x = y) ==> &0 < abs(x - y)]])
  let h96 ← rr (← ExceptT.mk [[abs x <= a ==> x <= a]])
  let h95 ← tt (← ExceptT.mk [[p ==> ~p ==> q]])
  let h94 ← tt (← ExceptT.mk [[~q /\ p ==> (p ==> q) ==> r]])
  let h93 ← tt (← ExceptT.mk [[~q /\ p ==> (p ==> q) ==> r]])
  let h92 ← rr (← ExceptT.mk [[&0 < x ==> abs(min (&1 / &2) x) <= x]])
  let h91 ← va (← ExceptT.mk [[a - ((&1 - u) % a + u % b):real^N = u % (a - b)]])
  let h90 ← rr (← ExceptT.mk [[&0 < x ==> &0 < min (&1 / &2) x]])
  let h89 ← ms [] (← ExceptT.mk [[(?x. (?u. P u /\ Q u /\ x = f u) /\ R x) <=>
        (?u. P u /\ Q u /\ R(f u))]])
  let h88 ← rr (← ExceptT.mk [[(&1 - t) * a < (&1 - t) * m /\ t * b <= t * m
          ==> ~((&1 - s) * m + s * m = (&1 - t) * a + t * b)]])
  let h87 ← va (← ExceptT.mk [[((&1 - u) % c + u % a) - b =
            (&1 - u) % (c - b) + u % (a - b)]])
  let h86 ← rr (← ExceptT.mk [[x >= b + e <=> e <= x - b]])
  let h85 ← sr (← ExceptT.mk [[!t. ~(b IN t) /\ s SUBSET t ==> ~(b IN s)]])
  let h84 ← sr (← ExceptT.mk [[~(x IN t) ==> s SUBSET t ==> ~(x IN s)]])
  let h83 ← sr (← ExceptT.mk [[!a b c t u.
                s SUBSET t /\ t SUBSET u /\
                a IN ca /\ c IN ca /\
                ab INTER u SUBSET {a,b} /\ bc INTER u SUBSET {c} /\
                ~(b IN u) /\ s INTER ca = {}
                ==> s INTER (ab UNION bc UNION ca) = {}]])
  let h82 ← sr (← ExceptT.mk [[(s SUBSET c ==> u IN c) /\ s INTER f = {} /\ ~(s INTER c = {})
      ==> (~(s INTER c = {}) /\ ~(s DIFF c = {}) ==> ~(s INTER f = {}))
          ==> u IN c]])
  let h81 ← tt (← ExceptT.mk [[(a ==> b) /\ a ==> a /\ b]])
  let h80 ← rr (← ExceptT.mk [[--x < --m ==> ~(x = m)]])
  let h79 ← va (← ExceptT.mk [[((&1 - u) % x + u % y) - a:real^N =
        (&1 - u) % (x - a) + u % (y - a)]])
  let h78 ← ar (← ExceptT.mk [[3 <= SUC n <=> 2 <= n]])
  let h77 ← rr (← ExceptT.mk [[x >= b + e <=> e <= x - b]])
  let h76 ← rr (← ExceptT.mk [[e <= x - b <=> x >= b + e]])
  let h75 ← sr (← ExceptT.mk [[t SUBSET {x | P x} ==> s SUBSET t ==> !x. x IN s ==> P x]])
  let h74 ← sr (← ExceptT.mk [[s INTER t = {} <=> s SUBSET (UNIV DIFF t)]])
  let h73 ← sr (← ExceptT.mk [[!t. s SUBSET t /\ u INTER t = {} ==> s INTER u = {}]])
  let h72 ← sr (← ExceptT.mk [[!s. i SUBSET s /\ s SUBSET c
          ==> c DIFF i = a UNION b UNION d ==> i INTER b = {}]])
  let h71 ← sr (← ExceptT.mk [[!t. s SUBSET t /\ t INTER u = {} ==> s INTER u = {}]])
  let h70 ← sr (← ExceptT.mk [[!s. i SUBSET s /\ s SUBSET c
          ==> c DIFF i = a UNION b ==> i INTER a = {}]])
  let h69 ← sr (← ExceptT.mk [[!t. s SUBSET t /\ t INTER u = {} ==> s INTER u = {}]])
  let h68 ← sr (← ExceptT.mk [[s SUBSET UNIV DIFF (a UNION b UNION c) <=>
        s INTER a = {} /\ s INTER b = {} /\ s INTER c = {}]])
  let h67 ← rr (← ExceptT.mk [[&0 <= x ==> abs(min (&1 / &2) x) <= x]])
  let h66 ← rr (← ExceptT.mk [[abs(x$2) <= norm x /\ norm x <= e / &2 /\ &0 < e ==> x$2 < e]])
  let h65 ← sr (← ExceptT.mk [[(?y. y IN s /\ P y) /\ s SUBSET t
        ==> ?y. y IN s /\ y IN t /\ P y]])
  let h64 ← rr (← ExceptT.mk [[&0 < m * (&1 - t) /\ m <= x ==> ~((&1 - s) * x + s * x = t * m)]])
  let h63 ← va (← ExceptT.mk [[((&1 - u) % c + u % a) - b =
          (&1 - u) % (c - b) + u % (a - b)]])
  let h62 ← sr (← ExceptT.mk [[s INTER a = {} /\ s INTER b = {} /\ s INTER c = {} /\ s SUBSET u
        ==> s SUBSET u DIFF (a UNION b UNION c)]])
  let h61 ← sr (← ExceptT.mk [[s SUBSET u ==> s DIFF (u DIFF t) SUBSET t]])
  let h60 ← rr (← ExceptT.mk [[t * m < m <=> &0 < m * (&1 - t)]])
  let h59 ← va (← ExceptT.mk [[((&1 - t) % a + t % b) - a:real^N = t % (b - a)]])
  let h58 ← sr (← ExceptT.mk [[{a,b,c} = {b,a,c}]])
  let h57 ← sr (← ExceptT.mk [[!c. x IN c /\ ~(x IN (a INTER c)) /\ ~(x IN (b INTER c))
            ==> ~(x IN a) /\ ~(x IN b)]])
  let h56 ← tt (← ExceptT.mk [[p /\ (p ==> q) ==> p /\ q]])
  let h55 ← rr (← ExceptT.mk [[(&1 - u - v) * x + v * x <= x <=> &0 <= u * x]])
  let h54 ← va (← ExceptT.mk [[(a + u % (b - a) + v % (c - a)) - b =
      (&1 - u - v) % (a - b) + v % (c - b)]])
  let h53 ← rr (← ExceptT.mk [[(&1 - u - v) * x + v * x = (&1 - u) * x]])
  let h52 ← va (← ExceptT.mk [[(a + u % (b - a) + v % (c - a)) - b =
      (&1 - u - v) % (a - b) + v % (c - b)]])
  let h51 ← rr (← ExceptT.mk [[x = y <=> y - x = &0]])
  let h50 ← tt (← ExceptT.mk [[p ==> ~p ==> q]])
  let h49 ← sr (← ExceptT.mk [[{a,b,c} = {a,c,b}]])
  let h48 ← rr (← ExceptT.mk [[&0 < n dot (c - b) \/ &0 < --(n dot (c - b)) \/
      (n:real^2) dot (c - b) = &0]])
  let h47 ← tt (← ExceptT.mk [[p ==> (p <=> q /\ r /\ s) ==> r]])
  let h46 ← tt (← ExceptT.mk [[p ==> (p <=> q /\ r /\ s) ==> r]])
  let h45 ← sr (← ExceptT.mk [[s DIFF (t UNION u) = (s DIFF t) INTER (s DIFF u)]])
  let h44 ← sr (← ExceptT.mk [[{a,b,c} = {b,c,a}]])
  let h43 ← sr (← ExceptT.mk [[{a,b,c} = {b,a,c}]])
  let h42 ← sr (← ExceptT.mk [[s SUBSET t ==> x IN s /\ P x ==> x IN t]])
  let h41 ← sr (← ExceptT.mk [[t INTER s SUBSET c
        ==> c SUBSET (a UNION b)
            ==> s DIFF (a UNION b) SUBSET UNIV DIFF (a UNION b UNION t)]])
  let h40 ← sr (← ExceptT.mk [[s INTER (t UNION u) = {} <=>
                        s INTER t = {} /\ s INTER u = {}]])
  let h39 ← sr (← ExceptT.mk [[x IN s /\ x IN t /\ (!y. y IN s /\ y IN t ==> y = x)
          ==> s INTER t = {x}]])
  let h38 ← sr (← ExceptT.mk [[s INTER (t UNION u) = {} <=>
                        s INTER t = {} /\ s INTER u = {}]])
  let h37 ← sr (← ExceptT.mk [[x IN s /\ x IN t /\ (!y. y IN s /\ y IN t ==> y = x)
          ==> s INTER t = {x}]])
  let h36 ← rr (← ExceptT.mk [[&0 <= x /\ &0 <= y ==> (x + y = &0 <=> x = &0 /\ y = &0)]])
  let h35 ← va (← ExceptT.mk [[d = (&1 - w) % ((&1 - u) % d + u % d') + w % ((&1 - v) % d + v % d') <=>
        ((&1 - w) * u + w * v) % (d' - d) = vec 0]])
  let h34 ← sr (← ExceptT.mk [[s INTER t = {} <=> !x. x IN s ==> ~(x IN t)]])
  let h33 ← rr (← ExceptT.mk [[b + e <= x <=> e <= x - b]])
  let h32 ← sr (← ExceptT.mk [[!u. t SUBSET u /\ s INTER u = {} ==> s INTER t = {}]])
  let h31 ← sr (← ExceptT.mk [[~(x IN u) /\ s SUBSET s' /\ t SUBSET t'
      ==> x IN (s UNION t UNION u) ==> x IN s' \/ x IN t']])
  let h30 ← sr (← ExceptT.mk [[!t. s SUBSET t /\ ~(x IN t) ==> ~(x IN s)]])
  let h29 ← rr (← ExceptT.mk [[r * (e + b) + (&1 - (r + t)) * b + t * (e + b) < b + e <=>
      (r + t) * e < &1 * e]])
  let h28 ← rr (← ExceptT.mk [[b < r * x + (&1 - (r + t)) * b + t * x <=> (r + t) * b < (r + t) * x]])
  let h27 ← rr (← ExceptT.mk [[r + s + t = &1 ==> s = &1 - (r + t)]])
  let h26 ← rr (← ExceptT.mk [[b < a ==> ~(a - b = &0)]])
  let h25 ← rr (← ExceptT.mk [[((&1 - u) * b + u * a) - b = u * (a - b)]])
  let h24 ← na (← ExceptT.mk [[!a. dist(x + a,y) < k / &2 /\ norm(a) = k / &2 ==> dist(x,y) < k]])
  let h23 ← rr (← ExceptT.mk [[&0 < k ==> ~(b + k / &2 = b)]])
  let h22 ← na (← ExceptT.mk [[dist(x,x + e) = norm e]])
  let h21 ← rr (← ExceptT.mk [[(&1 - u) * b + u * a <= e + b <=> (a - b) * u <= e]])
  let h20 ← rf (← ExceptT.mk [[y < x /\ &0 < e ==> s = (s * (x - y)) / e * e / (x - y)]])
  let h19 ← rr (← ExceptT.mk [[a / e + b / e:real = (a + b) / e]])
  let h18 ← va (← ExceptT.mk [[((&1 - u) % b + u % a) - b:real^N = u % (a - b)]])
  let h17 ← va (← ExceptT.mk [[a + x:real^N = a + y <=> x = y]])
  let h16 ← sr (← ExceptT.mk [[{a,b,c} = {b,a,c}]])
  let h15 ← rf (← ExceptT.mk [[~(a = &0) /\ ~(c = &0)
      ==> (a * c * x) pow 2 = (a * a * y) * (c * c * z)
          ==> x pow 2 = y * z]])
  let h14 ← va (← ExceptT.mk [[((&1 - u) % b + u % a) - b = u % (a - b)]])
  let h13 ← va (← ExceptT.mk [[(&1 - u) % a + u % b = a <=> u % (b - a) = vec 0]])
  let h12 ← tt (← ExceptT.mk [[p /\ q /\ r <=> r /\ p /\ q]])
  let h11 ← va (← ExceptT.mk [[(&1 - u) % a + u % b = (&1 - v) % a + v % b <=>
      (u - v) % (b - a) = vec 0]])
  let h10 ← sr (← ExceptT.mk [[s INTER t = t <=> t SUBSET s]])
  let h9 ← rr (← ExceptT.mk [[(&1 - u) * b < (&1 - u) * c /\ u * b < u * a
        ==> ~(b = (&1 - u) * c + u * a)]])
  let h8 ← sr (← ExceptT.mk [[s INTER t = s <=> s SUBSET t]])
  let h7 ← ms [] (← ExceptT.mk [[(!x. P x ==> ~(a = x)) <=> ~(P a)]])
  let h6 ← sr (← ExceptT.mk [[s INTER (t UNION u) SUBSET v <=>
                        s INTER t SUBSET v /\ s INTER u SUBSET v]])
  let h5 ← ms [Session.listDefs.MEM] (← ExceptT.mk [[MEM b (CONS a (CONS b l))]])
  let h4 ← ar (← ExceptT.mk [[5 <= SUC(SUC(SUC n)) <=> ~(n = 0) /\ 2 <= n]])
  let h3 ← nc (← ExceptT.mk [[1]])
  let h2 ← sr (← ExceptT.mk [[a IN s /\ b IN s ==> s UNION {a} = b INSERT s]])
  let h1 ← ms [] (← ExceptT.mk [[(!x y. (?z. P z /\ x = f z) ==> Q x y) <=>
                         (!z y. P z ==> Q (f z) y)]])
  prove ([[!p:(real^2)list.
        simple_path(polygonal_path p) /\
        pathfinish(polygonal_path p) = pathstart(polygonal_path p) /\
        5 <= LENGTH p
        ==> ?a b. ~(a = b) /\ MEM a p /\ MEM b p /\
                  segment(a,b) SUBSET inside(path_image(polygonal_path p))]])
   (MATCH_MP_TAC (← HolLight.MATCH_MP wlog_lemma DISTINGUISHING_ROTATION_EXISTS_POLYGON) THEN
    CONJ_TAC THENL
     [REWRITE_TAC [h1] THEN
      REWRITE_TAC [ORTHOGONAL_TRANSFORMATION] THEN
      GEOM_TRANSFORM_TAC [],
      ALL_TAC] THEN
    X_GEN_TAC ([[q:(real^2)list]]) THEN DISCH_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[?b:real^2. MEM b q /\ !d. MEM d q ==> b$2 <= d$2]]) STRIP_ASSUME_TAC THENL
     [MP_TAC (← HolLight.ISPEC ([[IMAGE (\x:real^2. x$2) (set_of_list q)]]) INF_FINITE) THEN
      SIMP_TAC [FINITE_SET_OF_LIST, FINITE_IMAGE] THEN
      REWRITE_TAC [IMAGE_EQ_EMPTY, SET_OF_LIST_EQ_EMPTY] THEN
      UNDISCH_TAC ([[5 <= LENGTH(q:(real^2)list)]]) THEN
      ASM_CASES_TAC ([[q:(real^2)list = [] ]]) THEN
      ASM_REWRITE_TAC [Session.listDefs.LENGTH, ARITH, FORALL_IN_IMAGE] THEN DISCH_TAC THEN
      REWRITE_TAC [IN_IMAGE, LEFT_AND_EXISTS_THM, IN_SET_OF_LIST] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[b:real^2]]) THEN
      DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[?p:(real^2)list.
        EL 1 p = b /\ LAST p = HD p /\
        LENGTH p = LENGTH q /\ set_of_list p = set_of_list q /\
        path_image(polygonal_path p) = path_image(polygonal_path q) /\
        simple_path(polygonal_path p) /\
        pathfinish(polygonal_path p) = pathstart(polygonal_path p)]]) MP_TAC THENL
     [MATCH_MP_TAC ROTATE_LIST_TO_FRONT_1 THEN EXISTS_TAC ([[q:(real^2)list]]) THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC, ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC [([[pathfinish(polygonal_path(q:(real^2)list)) =
       pathstart(polygonal_path q)]]),
        ([[5 <= LENGTH(q:(real^2)list)]])] THEN
      ASM_CASES_TAC ([[q:(real^2)list = [] ]]) THEN
      ASM_REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN
      ASM_REWRITE_TAC [PATHSTART_POLYGONAL_PATH, PATHFINISH_POLYGONAL_PATH] THEN
      DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
      X_GEN_TAC ([[l:(real^2)list]]) THEN
      REWRITE_TAC [Session.listThms2.APPEND_EQ_NIL, Session.listThms1.NOT_CONS_NIL] THEN
      ASM_CASES_TAC ([[l:(real^2)list = [] ]]) THENL
       [ASM_MESON_TAC [Session.listThms1.LENGTH_EQ_NIL], ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (STRIP_ASSUME_TAC o HolLight.GSYM) THEN
      ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN ([[~(TL l:(real^2)list = [])]]) ASSUME_TAC THENL
       [DISCH_THEN (MP_TAC o HolLight.AP_TERM ([[LENGTH:(real^2)list->num]])) THEN
        ASM_SIMP_TAC [Session.listDefs.LENGTH, Session.listThms2.LENGTH_TL] THEN ASM_ARITH_TAC,
        ALL_TAC] THEN
      ASM_SIMP_TAC [Session.listThms2.LAST_APPEND, Session.listThms1.LENGTH_APPEND, Session.listThms2.LENGTH_TL, Session.listThms1.NOT_CONS_NIL] THEN
      ASM_REWRITE_TAC [Session.listDefs.LAST, Session.listThms2.HD_APPEND, Session.listDefs.LENGTH] THEN REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC,
        MAP_EVERY UNDISCH_TAC [([[HD(l:(real^2)list) = LAST l]]), ([[5 <= LENGTH(q:(real^2)list)]]),
          ([[~(l:(real^2)list = [])]])] THEN
        ASM_REWRITE_TAC [] THEN
        SPEC_TAC (([[l:(real^2)list]]), ([[l:(real^2)list]])) THEN
        LIST_INDUCT_TAC THEN REWRITE_TAC [Session.listDefs.HD, Session.listDefs.TL, Session.listDefs.APPEND] THEN
        REWRITE_TAC [SET_OF_LIST_APPEND, set_of_list] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC h2 THEN
        ASM_REWRITE_TAC [Session.listDefs.LAST] THEN ONCE_ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [Session.listDefs.LAST] THEN UNDISCH_TAC ([[5 <= LENGTH(CONS (h:real^2) t)]]) THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN
        REWRITE_TAC [IN_SET_OF_LIST, Session.listThms2.MEM_EXISTS_EL, Session.listDefs.LENGTH] THEN
        DISCH_TAC THEN CONJ_TAC THENL
         [EXISTS_TAC ([[0]]) THEN REWRITE_TAC [Session.listDefs.EL] THEN ASM_ARITH_TAC,
          EXISTS_TAC ([[LENGTH(t:(real^2)list) - 1]]) THEN
          ASM_SIMP_TAC [Session.listThms2.LAST_EL] THEN ASM_ARITH_TAC],
        MATCH_MP_TAC PATH_IMAGE_POLYGONAL_PATH_ROTATE THEN
        ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
        MP_TAC (← HolLight.ISPEC ([[l:(real^2)list]]) SIMPLE_PATH_POLYGONAL_PATH_ROTATE) THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC],
      ALL_TAC] THEN
    UNDISCH_THEN ([[pathfinish(polygonal_path(q:(real^2)list)) =
                pathstart(polygonal_path q)]]) ((fun _ => ALL_TAC)) THEN
    UNDISCH_THEN ([[simple_path(polygonal_path(q:(real^2)list))]]) ((fun _ => ALL_TAC)) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[r:(real^2)list]]) MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (SUBST_ALL_TAC o HolLight.SYM) MP_TAC) THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.LAND_CONV) [EXTENSION] THEN
    REWRITE_TAC [IN_SET_OF_LIST] THEN DISCH_THEN (CONJUNCTS_THEN2 (fun th => HolLight.tactic_of do
        pure (REWRITE_TAC [(← HolLight.GSYM th)] THEN
                RULE_ASSUM_TAC (HolLight.REWRITE_RULE [(← HolLight.GSYM th)]))) MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (SUBST_ALL_TAC o HolLight.SYM) STRIP_ASSUME_TAC) THEN
    UNDISCH_THEN ([[MEM (b:real^2) r]]) ((fun _ => ALL_TAC)) THEN
    POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist HolLight.CONJ o HolLight.rev) THEN
    SPEC_TAC (([[r:(real^2)list]]), ([[r:(real^2)list]])) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN
    X_GEN_TAC ([[a:real^2]]) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN
    X_GEN_TAC ([[b':real^2]]) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN
    X_GEN_TAC ([[c:real^2]]) THEN X_GEN_TAC ([[p:(real^2)list]]) THEN
    REPLICATE_TAC 3 (DISCH_THEN ((fun _ => ALL_TAC))) THEN
    REWRITE_TAC [h3, Session.listDefs.EL, Session.listDefs.HD, Session.listDefs.TL] THEN
    ASM_CASES_TAC ([[b':real^2 = b]]) THEN ASM_REWRITE_TAC [] THEN
    POP_ASSUM ((fun _ => ALL_TAC)) THEN
    REWRITE_TAC [h4] THEN
    ASM_CASES_TAC ([[p:(real^2)list = [] ]]) THEN ASM_REWRITE_TAC [Session.listThms1.LENGTH_EQ_NIL] THEN
    ASM_SIMP_TAC [POLYGONAL_PATH_CONS_CONS, Session.listDefs.LAST, Session.listThms1.NOT_CONS_NIL] THEN
    REWRITE_TAC [PATHSTART_JOIN, PATHSTART_LINEPATH] THEN
    REPLICATE_TAC 2 (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[b:real^2]])) THEN
    REWRITE_TAC [h5] THEN
    DISCH_THEN (ASSUME_TAC o HolLight.GSYM) THEN STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[linepath(a:real^2,b)]]),
      ([[polygonal_path(CONS (b:real^2) (CONS c p))]])] SIMPLE_PATH_JOIN_IMP) THEN
    ASM_SIMP_TAC [POLYGONAL_PATH_CONS_CONS] THEN
    REWRITE_TAC [PATHFINISH_LINEPATH, PATHSTART_JOIN, PATHSTART_LINEPATH] THEN
    REWRITE_TAC [ARC_LINEPATH_EQ] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (fun th => ASSUME_TAC th THEN MP_TAC th) MP_TAC) THEN
    SIMP_TAC [ARC_JOIN_EQ, PATHFINISH_LINEPATH, PATHSTART_POLYGONAL_PATH,
             Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD] THEN
    REWRITE_TAC [ARC_LINEPATH_EQ, (← HolLight.GSYM CONJ_ASSOC), PATH_IMAGE_LINEPATH] THEN
    SIMP_TAC [PATH_IMAGE_JOIN, PATHFINISH_LINEPATH, PATHSTART_POLYGONAL_PATH,
             Session.listDefs.HD, Session.listThms1.NOT_CONS_NIL] THEN
    REWRITE_TAC [h6] THEN
    ASM_CASES_TAC ([[a:real^2 = c]]) THENL
     [DISCH_THEN (MP_TAC o HolLight.CONJUNCT1) THEN
      ASM_REWRITE_TAC [PATH_IMAGE_LINEPATH, SEGMENT_SYM, INTER_ACI] THEN
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ_ALT] FINITE_SUBSET)) THEN
      REWRITE_TAC [FINITE_SEGMENT, FINITE_INSERT, FINITE_EMPTY] THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    REWRITE_TAC [PATH_IMAGE_LINEPATH] THEN STRIP_TAC THEN STRIP_TAC THEN
    MP_TAC (← HolLight.ISPEC ([[CONS (b:real^2) (CONS c p)]]) ARC_POLYGONAL_PATH_IMP_DISTINCT) THEN
    ASM_SIMP_TAC [POLYGONAL_PATH_CONS_CONS] THEN
    REWRITE_TAC [Session.listDefs.PAIRWISE, Session.listDefs.ALL] THEN REWRITE_TAC [(← HolLight.GSYM Session.listThms1.ALL_MEM)] THEN
    REWRITE_TAC [h7] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN ([[(b:real^2)$2 < (a:real^2)$2 /\
                (b:real^2)$2 < (c:real^2)$2 /\
                (!v. MEM v p ==> (b:real^2)$2 < (v:real^2)$2)]]) STRIP_ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC [REAL_LT_LE] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV HolLight.SYM_CONV) THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [Session.listDefs.MEM] THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[~collinear{a:real^2,b,c}]]) ASSUME_TAC THENL
     [REWRITE_TAC [COLLINEAR_BETWEEN_CASES, BETWEEN_IN_SEGMENT] THEN
      SUBGOAL_THEN ([[FINITE(segment[a:real^2,b] INTER segment[b,c])]]) MP_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC ([[{a:real^2,b}]]) THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY],
        ALL_TAC] THEN
      ONCE_REWRITE_TAC [(← HolLight.GSYM CONTRAPOS_THM)] THEN REWRITE_TAC [] THEN
      STRIP_TAC THENL
       [SUBGOAL_THEN ([[segment[a:real^2,b] INTER segment[b,c] = segment[a,b] ]]) (fun th => ASM_REWRITE_TAC [FINITE_SEGMENT, th]) THEN
        REWRITE_TAC [h8] THEN
        ASM_REWRITE_TAC [SUBSET_SEGMENT, ENDS_IN_SEGMENT],
        DISCH_TAC THEN UNDISCH_TAC ([[b IN segment[c:real^2,a] ]]) THEN
        ASM_REWRITE_TAC [SEGMENT_CLOSED_OPEN, IN_UNION, IN_INSERT] THEN
        ASM_REWRITE_TAC [IN_SEGMENT, NOT_IN_EMPTY] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[u:real]]) MP_TAC) THEN
        REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN (MP_TAC o HolLight.AP_TERM ([[\x:real^2. x$2]])) THEN
        REWRITE_TAC [VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT] THEN
        MATCH_MP_TAC h9 THEN
        ASM_SIMP_TAC [REAL_LT_LMUL_EQ, REAL_SUB_LT],
        SUBGOAL_THEN ([[segment[a:real^2,b] INTER segment[b,c] = segment[b,c] ]]) (fun th => ASM_REWRITE_TAC [FINITE_SEGMENT, th]) THEN
        REWRITE_TAC [h10] THEN
        ASM_REWRITE_TAC [SUBSET_SEGMENT, ENDS_IN_SEGMENT]],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[?e. &0 < e /\
         e <= (a:real^2)$2 - (b:real^2)$2 /\
         e <= (c:real^2)$2 - (b:real^2)$2 /\
         !v. MEM v p ==> e <= (v:real^2)$2 - (b:real^2)$2]]) STRIP_ASSUME_TAC THENL
     [MP_TAC (← HolLight.ISPEC ([[IMAGE (\v. (v:real^2)$2 - (b:real^2)$2)
                        (set_of_list(CONS a (CONS b (CONS c p)))
                          DELETE b)]]) INF_FINITE) THEN
      ASM_SIMP_TAC [FINITE_SET_OF_LIST, FINITE_IMAGE, FINITE_DELETE] THEN
      ANTS_TAC THENL
       [REWRITE_TAC [IMAGE_EQ_EMPTY] THEN
        REWRITE_TAC [set_of_list, (← HolLight.GSYM MEMBER_NOT_EMPTY)] THEN
        EXISTS_TAC ([[a:real^2]]) THEN ASM_REWRITE_TAC [IN_DELETE, IN_INSERT],
        ALL_TAC] THEN
      REWRITE_TAC [FORALL_IN_IMAGE] THEN REWRITE_TAC [IN_IMAGE] THEN
      ASM_REWRITE_TAC [set_of_list, FORALL_IN_INSERT, IMP_CONJ, IN_DELETE] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[d:real^2]]) MP_TAC) THEN
      DISCH_THEN (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) THEN
      DISCH_TAC THEN DISCH_TAC THEN REWRITE_TAC [IN_SET_OF_LIST] THEN
      DISCH_TAC THEN EXISTS_TAC ([[(d:real^2)$2 - (b:real^2)$2]]) THEN
      ASM_REWRITE_TAC [REAL_SUB_LT] THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [IN_INSERT, IN_SET_OF_LIST]) THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    MAP_EVERY ABBREV_TAC [([[a':real^2 = (&1 - e / (a$2 - b$2)) % b + e / (a$2 - b$2) % a]]),
      ([[c':real^2 = (&1 - e / (c$2 - b$2)) % b + e / (c$2 - b$2) % c]])] THEN
    SUBGOAL_THEN ([[a' IN segment[b:real^2,a] /\ c' IN segment[b,c] ]]) STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["a'", "c'"] THEN
      REWRITE_TAC [IN_SEGMENT] THEN
      REWRITE_TAC [h11] THEN
      ASM_REWRITE_TAC [VECTOR_MUL_EQ_0, VECTOR_SUB_EQ, REAL_SUB_0] THEN
      ONCE_REWRITE_TAC [h12] THEN
      REWRITE_TAC [UNWIND_THM1] THEN
      ASM_SIMP_TAC [REAL_LT_IMP_LE, REAL_LE_DIV, REAL_SUB_LE,
                   REAL_LE_LDIV_EQ, REAL_SUB_LT, REAL_MUL_LID],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[~(a':real^2 = b) /\ ~(c':real^2 = b)]]) STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["a'", "c'"] THEN
      REWRITE_TAC [h13] THEN
      ASM_REWRITE_TAC [VECTOR_MUL_EQ_0, VECTOR_SUB_EQ] THEN
      ASM_SIMP_TAC [REAL_EQ_LDIV_EQ, REAL_SUB_LT] THEN
      ASM_SIMP_TAC [REAL_MUL_LZERO, REAL_LT_IMP_NZ],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[~collinear{a':real^2,b,c'}]]) ASSUME_TAC THENL
     [UNDISCH_TAC ([[~collinear{a:real^2,b,c}]]) THEN
      REWRITE_TAC [CONTRAPOS_THM] THEN ONCE_REWRITE_TAC [COLLINEAR_3] THEN
      MAP_EVERY EXPAND_TAC ["a'", "c'"] THEN
      REWRITE_TAC [h14] THEN
      REWRITE_TAC [(← HolLight.GSYM DOT_CAUCHY_SCHWARZ_EQUAL), DOT_LMUL, DOT_RMUL] THEN
      MATCH_MP_TAC h15 THEN
      ASM_SIMP_TAC [REAL_EQ_LDIV_EQ, REAL_SUB_LT] THEN
      ASM_SIMP_TAC [REAL_MUL_LZERO, REAL_LT_IMP_NZ],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[~(a':real^2 = c')]]) ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC ([[~collinear{a':real^2,b,c'}]]) THEN
      ASM_REWRITE_TAC [INSERT_AC, COLLINEAR_2],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[~affine_dependent{a':real^2,b,c'}]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [AFFINE_DEPENDENT_IMP_COLLINEAR_3], ALL_TAC] THEN
    MP_TAC (← HolLight.ISPEC ([[{a':real^2,b,c'}]]) INTERIOR_CONVEX_HULL_EQ_EMPTY) THEN
    REWRITE_TAC [DIMINDEX_2, HAS_SIZE, ARITH, FINITE_INSERT, FINITE_EMPTY] THEN
    SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY] THEN
    ASM_REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY, ARITH] THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[convex hull {a,b,c} INTER {x:real^2 | x$2 - b$2 <= e} =
                convex hull {a',b,c'}]]) ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC [h16] THEN
        REWRITE_TAC [CONVEX_HULL_3_ALT] THEN
        REWRITE_TAC [SUBSET, IN_INTER, FORALL_IN_GSPEC, IMP_CONJ] THEN
        REWRITE_TAC [IN_ELIM_THM, h17] THEN
        MAP_EVERY X_GEN_TAC [([[s:real]]), ([[t:real]])] THEN
        REPLICATE_TAC 3 DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["a'", "c'"] THEN
        REWRITE_TAC [h18] THEN
        REWRITE_TAC [VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT] THEN
        REWRITE_TAC [REAL_ADD_SUB, VECTOR_SUB_COMPONENT] THEN STRIP_TAC THEN
        EXISTS_TAC ([[(s * ((a:real^2)$2 - (b:real^2)$2)) / e]]) THEN
        EXISTS_TAC ([[(t * ((c:real^2)$2 - (b:real^2)$2)) / e]]) THEN
        ASM_SIMP_TAC [REAL_LE_DIV, REAL_LE_MUL, REAL_SUB_LT, REAL_LT_IMP_LE] THEN
        REWRITE_TAC [h19] THEN
        ASM_SIMP_TAC [REAL_LE_LDIV_EQ, REAL_MUL_LID] THEN
        REWRITE_TAC [VECTOR_MUL_ASSOC] THEN BINOP_TAC THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC h20 THEN
        ASM_REWRITE_TAC [],
        MATCH_MP_TAC HULL_MINIMAL THEN
        REWRITE_TAC [INSERT_SUBSET, EMPTY_SUBSET, IN_INTER, IN_ELIM_THM] THEN
        ASM_SIMP_TAC [HULL_INC, IN_INSERT, REAL_SUB_REFL, REAL_LT_IMP_LE] THEN
        SIMP_TAC [REAL_LE_SUB_RADD, CONVEX_INTER, CONVEX_HALFSPACE_COMPONENT_LE,
                 CONVEX_CONVEX_HULL] THEN
        REPEAT CONJ_TAC THENL
         [UNDISCH_TAC ([[a' IN segment[b:real^2,a] ]]) THEN
          SPEC_TAC (([[a':real^2]]), ([[x:real^2]])) THEN REWRITE_TAC [(← HolLight.GSYM SUBSET)] THEN
          REWRITE_TAC [SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
          SET_TAC [],
          EXPAND_TAC "a'",
          UNDISCH_TAC ([[c' IN segment[b:real^2,c] ]]) THEN
          SPEC_TAC (([[c':real^2]]), ([[x:real^2]])) THEN REWRITE_TAC [(← HolLight.GSYM SUBSET)] THEN
          REWRITE_TAC [SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
          SET_TAC [],
          EXPAND_TAC "c'"] THEN
        REWRITE_TAC [VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT] THEN
        REWRITE_TAC [h21] THEN
        ASM_SIMP_TAC [REAL_DIV_LMUL, REAL_LT_IMP_NZ, REAL_SUB_LT] THEN
        REWRITE_TAC [REAL_LE_REFL]],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[interior(convex hull {a,b,c}) INTER {x:real^2 | x$2 - b$2 < e} =
    interior(convex hull {a',b,c'})]]) ASSUME_TAC THENL
     [REWRITE_TAC [REAL_LT_SUB_RADD, (← HolLight.GSYM INTERIOR_HALFSPACE_COMPONENT_LE)] THEN
      ASM_REWRITE_TAC [(← HolLight.GSYM INTERIOR_INTER), (← HolLight.GSYM REAL_LE_SUB_RADD)],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[?d:real^2. d IN interior(convex hull {a',b,c'}) /\ ~(d$1 = b$1)]]) STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC ([[~(interior(convex hull {a':real^2,b,c'}) = {})]]) THEN
      REWRITE_TAC [(← HolLight.GSYM MEMBER_NOT_EMPTY), LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC ([[x:real^2]]) THEN DISCH_TAC THEN
      ASM_CASES_TAC ([[(x:real^2)$1 = (b:real^2)$1]]) THENL
       [ALL_TAC, EXISTS_TAC ([[x:real^2]]) THEN ASM_REWRITE_TAC []] THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [IN_INTERIOR]) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[k:real]]) MP_TAC) THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN REWRITE_TAC [SUBSET] THEN
      DISCH_THEN (fun th => ASSUME_TAC th THEN MP_TAC th) THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC ([[x + k / &2 % basis 1:real^2]])) THEN ANTS_TAC THENL
       [REWRITE_TAC [IN_BALL, h22] THEN
        SIMP_TAC [NORM_MUL, NORM_BASIS, DIMINDEX_GE_1, ARITH] THEN
        UNDISCH_TAC ([[&0 < k]]) THEN REAL_ARITH_TAC2,
        DISCH_TAC] THEN
      EXISTS_TAC ([[x + k / &2 % basis 1:real^2]]) THEN
      REWRITE_TAC [VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT] THEN
      ASM_SIMP_TAC [BASIS_COMPONENT, DIMINDEX_GE_1, ARITH, REAL_MUL_RID] THEN
      ASM_SIMP_TAC [h23] THEN
      REWRITE_TAC [IN_INTERIOR] THEN EXISTS_TAC ([[k / &2]]) THEN
      ASM_REWRITE_TAC [REAL_HALF, SUBSET] THEN X_GEN_TAC ([[y:real^2]]) THEN
      REWRITE_TAC [IN_BALL] THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC [IN_BALL] THEN MATCH_MP_TAC h24 THEN
      EXISTS_TAC ([[k / &2 % basis 1:real^2]]) THEN ASM_REWRITE_TAC [NORM_MUL] THEN
      SIMP_TAC [NORM_BASIS, DIMINDEX_GE_1, LE_REFL] THEN
      UNDISCH_TAC ([[&0 < k]]) THEN REAL_ARITH_TAC2,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[path_image(polygonal_path(CONS a (CONS b (CONS c p))))
     SUBSET {x:real^2 | x$2 >= b$2}]]) MP_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC ([[convex hull(set_of_list(CONS (a:real^2) (CONS b (CONS c p))))]]) THEN
      SIMP_TAC [PATH_IMAGE_POLYGONAL_PATH_SUBSET_CONVEX_HULL, Session.listThms1.NOT_CONS_NIL] THEN
      MATCH_MP_TAC HULL_MINIMAL THEN
      REWRITE_TAC [CONVEX_HALFSPACE_COMPONENT_GE] THEN
      REWRITE_TAC [set_of_list, INSERT_SUBSET, IN_ELIM_THM, EMPTY_SUBSET] THEN
      ASM_SIMP_TAC [SUBSET, IN_SET_OF_LIST, real_ge, IN_ELIM_THM, REAL_LT_IMP_LE,
                   REAL_LE_REFL],
      GEN_REWRITE_TAC HolLight.LAND_CONV [SUBSET] THEN
      ASM_SIMP_TAC [POLYGONAL_PATH_CONS_CONS, Session.listThms1.NOT_CONS_NIL] THEN
      REWRITE_TAC [IN_ELIM_THM, real_ge] THEN DISCH_TAC] THEN
    SUBGOAL_THEN ([[(:real^2) DIFF {x | x$2 >= b$2} SUBSET
    outside(path_image
                 (linepath(a,b) ++ linepath(b,c) ++ polygonal_path(CONS c p)))]]) MP_TAC THENL
     [MATCH_MP_TAC OUTSIDE_SUBSET_CONVEX THEN
      REWRITE_TAC [CONVEX_HALFSPACE_COMPONENT_GE] THEN
      ASM_REWRITE_TAC [SUBSET, real_ge, IN_ELIM_THM],
      REWRITE_TAC [SUBSET, real_ge, IN_ELIM_THM, IN_UNIV,
                  IN_DIFF, REAL_NOT_LE] THEN
      DISCH_TAC] THEN
    ABBREV_TAC ([[d':real^2 = d - (&1 + (d:real^2)$2 - (b:real^2)$2) % basis 2]]) THEN
    SUBGOAL_THEN ([[(d':real^2) IN outside(path_image
        (linepath(a,b) ++ linepath(b,c) ++ polygonal_path(CONS c p)))]]) ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "d'" THEN
      REWRITE_TAC [VECTOR_SUB_COMPONENT, VECTOR_MUL_COMPONENT] THEN
      SIMP_TAC [BASIS_COMPONENT, DIMINDEX_2, ARITH] THEN REAL_ARITH_TAC2,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[(a':real^2)$2 - (b:real^2)$2 = e /\
                (c':real^2)$2 - (b:real^2)$2 = e]]) STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["a'", "c'"] THEN
      REWRITE_TAC [VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT] THEN
      REWRITE_TAC [h25] THEN
      ASM_SIMP_TAC [REAL_DIV_RMUL, h26],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[(b:real^2)$2 < (d:real^2)$2 /\ (d:real^2)$2 < (b:real^2)$2 + e]]) STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC ([[(d:real^2) IN interior(convex hull {a',b,c'})]]) THEN
      ASM_SIMP_TAC [INTERIOR_CONVEX_HULL_3_MINIMAL] THEN
      REWRITE_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[r:real]]), ([[s:real]]), ([[t:real]])] THEN
      REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN
      REWRITE_TAC [VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT] THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [REAL_EQ_SUB_RADD]) THEN ASM_REWRITE_TAC [] THEN
      FIRST_ASSUM (SUBST1_TAC o HolLight.MATCH_MP h27) THEN
      REWRITE_TAC [h28,
                  h29] THEN
      ASM_SIMP_TAC [REAL_LT_LMUL_EQ, REAL_LT_ADD, REAL_LT_RMUL_EQ] THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[(d':real^2)$2 + &1 = (b:real^2)$2]]) ASSUME_TAC THENL
     [EXPAND_TAC "d'" THEN REWRITE_TAC [VECTOR_SUB_COMPONENT] THEN
      SIMP_TAC [VECTOR_MUL_COMPONENT, BASIS_COMPONENT, DIMINDEX_2, ARITH] THEN
      REAL_ARITH_TAC2,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[convex hull {a':real^2,b,c'} SUBSET convex hull {a,b,c}]]) ASSUME_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN
      REWRITE_TAC [CONVEX_CONVEX_HULL, INSERT_SUBSET, EMPTY_SUBSET] THEN
      SIMP_TAC [HULL_INC, IN_INSERT] THEN CONJ_TAC THENL
       [UNDISCH_TAC ([[(a':real^2) IN segment[b,a] ]]) THEN
        SPEC_TAC (([[a':real^2]]), ([[x:real^2]])),
        UNDISCH_TAC ([[(c':real^2) IN segment[b,c] ]]) THEN
        SPEC_TAC (([[c':real^2]]), ([[x:real^2]]))] THEN
      REWRITE_TAC [(← HolLight.GSYM SUBSET)] THEN REWRITE_TAC [SEGMENT_CONVEX_HULL] THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[~(d' IN convex hull {a:real^2,b,c})]]) ASSUME_TAC THENL
     [MATCH_MP_TAC h30 THEN
      EXISTS_TAC ([[{x | (x:real^2)$2 >= (b:real^2)$2}]]) THEN
      SIMP_TAC [SUBSET_HULL, CONVEX_HALFSPACE_COMPONENT_GE] THEN
      ASM_REWRITE_TAC [INSERT_SUBSET, EMPTY_SUBSET, IN_ELIM_THM, real_ge] THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[~(d' IN convex hull {a':real^2,b,c'})]]) ASSUME_TAC THENL
     [HolLight.ASM SET_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN ([[~(segment[d:real^2,d'] INTER frontier(convex hull {a',b,c'}) = {})]]) MP_TAC THENL
     [MATCH_MP_TAC CONNECTED_INTER_FRONTIER THEN
      REWRITE_TAC [CONNECTED_SEGMENT, (← HolLight.GSYM MEMBER_NOT_EMPTY)] THEN CONJ_TAC THENL
       [EXISTS_TAC ([[d:real^2]]) THEN REWRITE_TAC [ENDS_IN_SEGMENT, IN_INTER] THEN
        ASM_MESON_TAC [INTERIOR_SUBSET, SUBSET],
        EXISTS_TAC ([[d':real^2]]) THEN ASM_REWRITE_TAC [ENDS_IN_SEGMENT, IN_DIFF]],
      ALL_TAC] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM MEMBER_NOT_EMPTY)] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[x:real^2]]) MP_TAC) THEN REWRITE_TAC [IN_INTER] THEN
    ASM_CASES_TAC ([[x:real^2 = d]]) THENL
     [ASM_REWRITE_TAC [IN_DIFF, frontier], ALL_TAC] THEN
    ASM_CASES_TAC ([[x:real^2 = d']]) THENL
     [ASM_REWRITE_TAC [IN_DIFF, frontier] THEN
      SUBGOAL_THEN ([[closure(convex hull {a':real^2,b,c'}) = convex hull {a',b,c'}]]) (fun th => ASM_REWRITE_TAC [th]) THEN
      MATCH_MP_TAC CLOSURE_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MESON_TAC [COMPACT_CONVEX_HULL, FINITE_IMP_COMPACT, FINITE_RULES],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [SEGMENT_CLOSED_OPEN, IN_UNION, IN_INSERT, NOT_IN_EMPTY] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN ([[(d':real^2)$1 = (d:real^2)$1]]) ASSUME_TAC THENL
     [EXPAND_TAC "d'" THEN REWRITE_TAC [VECTOR_SUB_COMPONENT] THEN
      SIMP_TAC [VECTOR_MUL_COMPONENT, BASIS_COMPONENT, DIMINDEX_2, ARITH] THEN
      REAL_ARITH_TAC2,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[(x:real^2)$1 = (d:real^2)$1]]) ASSUME_TAC THENL
     [MP_TAC (← HolLight.ISPECL [([[d:real^2]]), ([[d':real^2]]), ([[x:real^2]])] SEGMENT_VERTICAL) THEN
      ASM_REWRITE_TAC [SEGMENT_CLOSED_OPEN, IN_UNION] THEN ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[~(x:real^2 = b)]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN ([[(x:real^2)$2 < (b:real^2)$2 + e]]) ASSUME_TAC THENL
     [MP_TAC (← HolLight.ISPECL [([[d:real^2]]), ([[d':real^2]]), ([[x:real^2]])] SEGMENT_VERTICAL) THEN
      ASM_REWRITE_TAC [SEGMENT_CLOSED_OPEN, IN_UNION] THEN ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[~(x:real^2 = a) /\ ~(x = c)]]) STRIP_ASSUME_TAC THENL
     [REWRITE_TAC [CART_EQ, DIMINDEX_2, FORALL_2] THEN ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[(x:real^2) IN (segment(b,a) UNION segment(b,c))]]) ASSUME_TAC THENL
     [UNDISCH_TAC ([[(x:real^2) IN frontier(convex hull {a':real^2,b,c'})]]) THEN
      ASM_SIMP_TAC [open_segment, IN_UNION, IN_DIFF, IN_INSERT, NOT_IN_EMPTY] THEN
      REWRITE_TAC [FRONTIER_OF_TRIANGLE] THEN MATCH_MP_TAC h31 THEN
      ASM_REWRITE_TAC [SUBSET_SEGMENT, ENDS_IN_SEGMENT] THEN DISCH_TAC THEN
      MP_TAC (← HolLight.ISPECL [([[c':real^2]]), ([[a':real^2]]), ([[x:real^2]])] SEGMENT_HORIZONTAL) THEN
      ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[segment[d:real^2,d'] INTER path_image(polygonal_path(CONS c p)) = {}]]) ASSUME_TAC THENL
     [MATCH_MP_TAC h32 THEN
      EXISTS_TAC ([[{x:real^2 | x$2 >= (b:real^2)$2 + e}]]) THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC ([[convex hull(set_of_list(CONS c p)) :real^2->bool]]) THEN
        SIMP_TAC [PATH_IMAGE_POLYGONAL_PATH_SUBSET_CONVEX_HULL, Session.listThms1.NOT_CONS_NIL] THEN
        MATCH_MP_TAC HULL_MINIMAL THEN
        REWRITE_TAC [CONVEX_HALFSPACE_COMPONENT_GE,
                    set_of_list, INSERT_SUBSET] THEN
        REWRITE_TAC [SUBSET, IN_SET_OF_LIST, IN_ELIM_THM] THEN
        ASM_SIMP_TAC [real_ge, h33],
        REWRITE_TAC [h34] THEN
        X_GEN_TAC ([[y:real^2]]) THEN DISCH_TAC THEN
        MP_TAC (← HolLight.ISPECL [([[d:real^2]]), ([[d':real^2]]), ([[y:real^2]])] SEGMENT_VERTICAL) THEN
        ASM_REWRITE_TAC [IN_ELIM_THM, real_ge] THEN ASM_REAL_ARITH_TAC],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[(d:real^2) IN interior(convex hull {a,b,c})]]) ASSUME_TAC THENL
     [UNDISCH_TAC ([[(d:real^2) IN interior(convex hull {a', b, c'})]]) THEN
      SPEC_TAC (([[d:real^2]]), ([[d:real^2]])) THEN REWRITE_TAC [(← HolLight.GSYM SUBSET)] THEN
      MATCH_MP_TAC SUBSET_INTERIOR THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[~(d':real^2 = d)]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [IN_SEGMENT], ALL_TAC] THEN
    SUBGOAL_THEN ([[!y:real^2. y IN segment[d,d'] /\
               y IN (segment (b,a) UNION segment (b,c))
               ==> y = x]]) ASSUME_TAC THENL
     [GEN_TAC THEN STRIP_TAC THEN
      SUBGOAL_THEN ([[collinear {d:real^2,x,y}]]) MP_TAC THENL
       [REWRITE_TAC [COLLINEAR_AFFINE_HULL] THEN
        MAP_EVERY EXISTS_TAC [([[d:real^2]]), ([[d':real^2]])] THEN
        REWRITE_TAC [INSERT_SUBSET, EMPTY_SUBSET] THEN
        REPEAT CONJ_TAC THEN MATCH_MP_TAC (← HolLight.REWRITE_RULE [SUBSET] CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
        ASM_REWRITE_TAC [(← HolLight.GSYM SEGMENT_CONVEX_HULL), ENDS_IN_SEGMENT] THEN
        ASM_REWRITE_TAC [SEGMENT_CLOSED_OPEN, IN_UNION],
        ALL_TAC] THEN
      REWRITE_TAC [COLLINEAR_BETWEEN_CASES, BETWEEN_IN_SEGMENT] THEN
      ASM_SIMP_TAC [SEGMENT_CLOSED_OPEN, IN_UNION, IN_INSERT, NOT_IN_EMPTY] THEN
      ASM_CASES_TAC ([[x:real^2 = y]]) THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN ([[(x:real^2) IN frontier(convex hull {a,b,c}) /\
      (y:real^2) IN frontier(convex hull {a,b,c})]]) MP_TAC THENL
       [REWRITE_TAC [FRONTIER_OF_TRIANGLE] THEN
        REWRITE_TAC [SEGMENT_CLOSED_OPEN, IN_UNION] THEN
        RULE_ASSUM_TAC (HolLight.REWRITE_RULE [IN_UNION]) THEN ASM_MESON_TAC [SEGMENT_SYM],
        REWRITE_TAC [frontier, IN_DIFF]] THEN
      ASM_CASES_TAC ([[y:real^2 = d]]) THEN ASM_REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THENL
       [MAP_EVERY UNDISCH_TAC [([[(d:real^2) IN segment (x,y)]]),
          ([[(y:real^2) IN segment [d,d'] ]]),
          ([[(x:real^2) IN segment(d,d')]])] THEN
        ASM_REWRITE_TAC [IN_SEGMENT] THEN
        REPLICATE_TAC 2 (STRIP_TAC THEN ASM_REWRITE_TAC []) THEN
        ASM_REWRITE_TAC [VECTOR_MUL_EQ_0, VECTOR_SUB_EQ, h35] THEN
        DISCH_THEN (CHOOSE_THEN MP_TAC) THEN
        REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        ASM_SIMP_TAC [REAL_SUB_LE, REAL_LE_MUL, REAL_LT_IMP_LE, h36] THEN
        REWRITE_TAC [REAL_ENTIRE] THEN ASM_REAL_ARITH_TAC,
        UNDISCH_TAC ([[~(x IN interior(convex hull {a:real^2, b, c}))]]) THEN
        UNDISCH_TAC ([[x IN segment (y:real^2,d)]]) THEN
        SPEC_TAC (([[x:real^2]]), ([[x:real^2]])) THEN ASM_REWRITE_TAC [(← HolLight.GSYM SUBSET)] THEN
        ONCE_REWRITE_TAC [SEGMENT_SYM] THEN
        MATCH_MP_TAC IN_INTERIOR_CLOSURE_CONVEX_SEGMENT THEN
        ASM_REWRITE_TAC [CONVEX_CONVEX_HULL],
        UNDISCH_TAC ([[~(y IN interior(convex hull {a:real^2, b, c}))]]) THEN
        UNDISCH_TAC ([[y IN segment (d:real^2,x)]]) THEN
        SPEC_TAC (([[y:real^2]]), ([[y:real^2]])) THEN ASM_REWRITE_TAC [(← HolLight.GSYM SUBSET)] THEN
        MATCH_MP_TAC IN_INTERIOR_CLOSURE_CONVEX_SEGMENT THEN
        ASM_REWRITE_TAC [CONVEX_CONVEX_HULL]],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[pathfinish(polygonal_path p) = (a:real^2)]]) ASSUME_TAC THENL
     [ASM_REWRITE_TAC [PATHFINISH_POLYGONAL_PATH], ALL_TAC] THEN
    SUBGOAL_THEN ([[segment(a:real^2,b) INTER segment(b,c) = {}]]) ASSUME_TAC THENL
     [UNDISCH_TAC ([[segment[a:real^2,b] INTER segment[b,c] SUBSET {a, b}]]) THEN
      REWRITE_TAC [SUBSET, EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
      MATCH_MP_TAC MONO_FORALL THEN
      REWRITE_TAC [open_segment, IN_DIFF, IN_INSERT, NOT_IN_EMPTY] THEN
      MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[(d:real^2) IN inside(path_image
      (linepath(a,b) ++ linepath(b,c) ++ polygonal_path(CONS c p)))]]) ASSUME_TAC THENL
     [UNDISCH_TAC ([[x IN segment(b:real^2,a) UNION segment (b,c)]]) THEN
      REWRITE_TAC [IN_UNION] THEN STRIP_TAC THENL
       [MP_TAC (← HolLight.ISPECL [([[a:real^2]]), ([[b:real^2]]), ([[d:real^2]]), ([[d':real^2]]),
                   ([[linepath(b:real^2,c) ++ polygonal_path(CONS c p)]]),
                   ([[x:real^2]])] PARITY_LEMMA) THEN
        SUBGOAL_THEN ([[path_image((linepath(b:real^2,c) ++ polygonal_path(CONS c p)) ++
                   linepath(a,b)) =
        path_image(linepath(a,b) ++ linepath(b:real^2,c) ++
                   polygonal_path(CONS c p))]]) SUBST1_TAC THENL
         [MATCH_MP_TAC PATH_IMAGE_SYM THEN
          REWRITE_TAC [PATHSTART_JOIN, PATHFINISH_JOIN] THEN
          REWRITE_TAC [PATHSTART_LINEPATH, PATHFINISH_LINEPATH] THEN
          UNDISCH_TAC ([[pathfinish(linepath(a,b) ++
          linepath (b,c) ++ polygonal_path(CONS c p)):real^2 = a]]) THEN
          ASM_REWRITE_TAC [PATHFINISH_JOIN, PATHFINISH_POLYGONAL_PATH],
          ALL_TAC] THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
         [HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
              let x1 ← ExceptT.mk (HolLight.PART_MATCH (HolCore.Equal.lhs o HolCore.Kernel.rand) SIMPLE_PATH_SYM w)
              pure (MP_TAC x1)) THEN
          ASM_REWRITE_TAC [PATHSTART_JOIN, PATHFINISH_JOIN] THEN
          ASM_REWRITE_TAC [PATHSTART_LINEPATH, PATHFINISH_LINEPATH] THEN
          REWRITE_TAC [PATHFINISH_POLYGONAL_PATH] THEN
          ASM_REWRITE_TAC [Session.listThms1.NOT_CONS_NIL, Session.listDefs.LAST],
          REWRITE_TAC [PATHSTART_JOIN, PATHSTART_LINEPATH],
          REWRITE_TAC [PATHFINISH_JOIN, PATHFINISH_POLYGONAL_PATH] THEN
          ASM_REWRITE_TAC [Session.listThms1.NOT_CONS_NIL, Session.listDefs.LAST],
          MATCH_MP_TAC h37 THEN
          SUBST1_TAC (← HolLight.ISPECL [([[a:real^2]]), ([[b:real^2]])] (← HolLight.CONJUNCT2 SEGMENT_SYM)) THEN
          ASM_REWRITE_TAC [] THEN
          RULE_ASSUM_TAC (HolLight.REWRITE_RULE [SEGMENT_CLOSED_OPEN]) THEN HolLight.ASM SET_TAC [],
          SIMP_TAC [PATH_IMAGE_JOIN, PATHFINISH_LINEPATH, PATH_IMAGE_LINEPATH,
                   PATHSTART_POLYGONAL_PATH, Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD] THEN
          ASM_REWRITE_TAC [h38] THEN
          REWRITE_TAC [EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
          X_GEN_TAC ([[y:real^2]]) THEN
          DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
          SUBGOAL_THEN ([[(y:real^2)$1 = (d:real^2)$1]]) ASSUME_TAC THENL
           [MP_TAC (← HolLight.ISPECL [([[d:real^2]]), ([[d':real^2]]), ([[y:real^2]])] SEGMENT_VERTICAL) THEN
            ASM_REWRITE_TAC [SEGMENT_CLOSED_OPEN, IN_UNION] THEN
            ASM_REAL_ARITH_TAC,
            ALL_TAC] THEN
          ASM_REWRITE_TAC [SEGMENT_CLOSED_OPEN, IN_UNION,
                          IN_INSERT, NOT_IN_EMPTY] THEN
          ASM_CASES_TAC ([[y:real^2 = b]]) THENL [ASM_MESON_TAC [], ALL_TAC] THEN
          RULE_ASSUM_TAC (HolLight.SUBS [(← HolLight.ISPECL [([[a:real^2]]), ([[b:real^2]])] (← HolLight.CONJUNCT2 SEGMENT_SYM))]) THEN
          ASM_CASES_TAC ([[y:real^2 = c]]) THENL [ALL_TAC, HolLight.ASM SET_TAC []] THEN
          UNDISCH_THEN ([[y:real^2 = c]]) SUBST_ALL_TAC THEN
          MP_TAC (← HolLight.ISPECL [([[d:real^2]]), ([[d':real^2]]), ([[c:real^2]])] SEGMENT_VERTICAL) THEN
          ASM_REWRITE_TAC [SEGMENT_CLOSED_OPEN, IN_UNION] THEN
          ASM_REAL_ARITH_TAC],
        MP_TAC (← HolLight.ISPECL [([[b:real^2]]), ([[c:real^2]]), ([[d:real^2]]), ([[d':real^2]]),
                   ([[polygonal_path(CONS c p) ++ linepath(a:real^2,b)]]),
                   ([[x:real^2]])] PARITY_LEMMA) THEN
        SUBGOAL_THEN ([[path_image((polygonal_path (CONS c p) ++ linepath (a,b)) ++
                   linepath(b:real^2,c)) =
        path_image(linepath(a,b) ++ linepath(b:real^2,c) ++
                   polygonal_path(CONS c p))]]) SUBST1_TAC THENL
         [ASM_SIMP_TAC [PATH_IMAGE_JOIN, PATHSTART_JOIN, PATHFINISH_JOIN,
                       PATHSTART_LINEPATH, PATHFINISH_LINEPATH,
                       PATHSTART_POLYGONAL_PATH, PATHFINISH_POLYGONAL_PATH,
                       Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD, Session.listDefs.LAST] THEN
          REWRITE_TAC [UNION_ACI],
          ALL_TAC] THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
         [HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
              let x1 ← ExceptT.mk (HolLight.PART_MATCH (HolCore.Equal.lhs o HolCore.Kernel.rand) (← HolLight.GSYM SIMPLE_PATH_ASSOC) w)
              pure (MP_TAC x1)) THEN
          ANTS_TAC THENL
           [ALL_TAC,
            DISCH_THEN SUBST1_TAC THEN
            HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
                let x1 ← ExceptT.mk (HolLight.PART_MATCH (HolCore.Equal.lhs o HolCore.Kernel.rand) SIMPLE_PATH_SYM w)
                pure (MP_TAC x1)) THEN
            ANTS_TAC THENL
             [ALL_TAC,
              DISCH_THEN SUBST1_TAC THEN
              HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
                  let x1 ← ExceptT.mk (HolLight.PART_MATCH (HolCore.Equal.lhs o HolCore.Kernel.rand) (← HolLight.GSYM SIMPLE_PATH_ASSOC) w)
                  pure (MP_TAC x1)) THEN
              ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC]] THEN
          ASM_SIMP_TAC [(← HolLight.GSYM SIMPLE_PATH_ASSOC), PATHSTART_JOIN,
                       PATHFINISH_JOIN,
                       PATHSTART_LINEPATH, PATHFINISH_LINEPATH,
                       PATHSTART_POLYGONAL_PATH, PATHFINISH_POLYGONAL_PATH,
                       Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD, Session.listDefs.LAST],
          REWRITE_TAC [PATHSTART_JOIN, PATHSTART_POLYGONAL_PATH] THEN
          REWRITE_TAC [Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD],
          REWRITE_TAC [PATHFINISH_JOIN, PATHFINISH_LINEPATH],
          MATCH_MP_TAC h39 THEN
          SUBST1_TAC (← HolLight.ISPECL [([[a:real^2]]), ([[b:real^2]])] (← HolLight.CONJUNCT2 SEGMENT_SYM)) THEN
          ASM_REWRITE_TAC [] THEN
          RULE_ASSUM_TAC (HolLight.REWRITE_RULE [SEGMENT_CLOSED_OPEN]) THEN HolLight.ASM SET_TAC [],
          ASM_SIMP_TAC [PATH_IMAGE_JOIN, PATHSTART_LINEPATH, Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD,
                       PATH_IMAGE_LINEPATH, PATHFINISH_POLYGONAL_PATH, Session.listDefs.LAST] THEN
          ASM_REWRITE_TAC [h40] THEN
          REWRITE_TAC [EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
          X_GEN_TAC ([[y:real^2]]) THEN
          DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
          SUBGOAL_THEN ([[(y:real^2)$1 = (d:real^2)$1]]) ASSUME_TAC THENL
           [MP_TAC (← HolLight.ISPECL [([[d:real^2]]), ([[d':real^2]]), ([[y:real^2]])] SEGMENT_VERTICAL) THEN
            ASM_REWRITE_TAC [SEGMENT_CLOSED_OPEN, IN_UNION] THEN
            ASM_REAL_ARITH_TAC,
            ALL_TAC] THEN
          ASM_REWRITE_TAC [SEGMENT_CLOSED_OPEN, IN_UNION,
                          IN_INSERT, NOT_IN_EMPTY] THEN
          ASM_CASES_TAC ([[y:real^2 = b]]) THENL [ASM_MESON_TAC [], ALL_TAC] THEN
          RULE_ASSUM_TAC (HolLight.SUBS [(← HolLight.ISPECL [([[a:real^2]]), ([[b:real^2]])] (← HolLight.CONJUNCT2 SEGMENT_SYM))]) THEN
          ONCE_REWRITE_TAC [SEGMENT_SYM] THEN
          ASM_CASES_TAC ([[y:real^2 = a]]) THENL [ALL_TAC, HolLight.ASM SET_TAC []] THEN
          UNDISCH_THEN ([[y:real^2 = a]]) SUBST_ALL_TAC THEN
          MP_TAC (← HolLight.ISPECL [([[d:real^2]]), ([[d':real^2]]), ([[a:real^2]])] SEGMENT_VERTICAL) THEN
          ASM_REWRITE_TAC [SEGMENT_CLOSED_OPEN, IN_UNION] THEN
          ASM_REAL_ARITH_TAC]],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[~affine_dependent{a:real^2,b,c}]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [AFFINE_DEPENDENT_IMP_COLLINEAR_3], ALL_TAC] THEN
    ASM_CASES_TAC ([[path_image(polygonal_path(CONS c p)) INTER
    convex hull {a,b,c} SUBSET {a:real^2,c}]]) THENL
     [MAP_EVERY EXISTS_TAC [([[a:real^2]]), ([[c:real^2]])] THEN
      ASM_REWRITE_TAC [Session.listDefs.MEM] THEN X_GEN_TAC ([[y:real^2]]) THEN DISCH_TAC THEN
      MATCH_MP_TAC INSIDE_SAME_COMPONENT THEN
      EXISTS_TAC ([[d:real^2]]) THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [connected_component] THEN
      EXISTS_TAC ([[segment[d:real^2,y] ]]) THEN
      REWRITE_TAC [CONNECTED_SEGMENT, ENDS_IN_SEGMENT] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC ([[convex hull {a:real^2,b,c} DIFF (segment[a,b] UNION segment[b,c])]]) THEN
      CONJ_TAC THENL
       [ALL_TAC,
        SIMP_TAC [PATH_IMAGE_JOIN, PATHSTART_JOIN, PATHFINISH_LINEPATH,
          PATHSTART_LINEPATH, PATHSTART_POLYGONAL_PATH, Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD] THEN
        REWRITE_TAC [PATH_IMAGE_LINEPATH] THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h41) THEN
        REWRITE_TAC [INSERT_SUBSET, EMPTY_SUBSET, IN_UNION, ENDS_IN_SEGMENT]] THEN
      REWRITE_TAC [SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
      REWRITE_TAC [INSERT_SUBSET, EMPTY_SUBSET] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC [IN_DIFF] THEN CONJ_TAC THENL
         [ASM_MESON_TAC [INTERIOR_SUBSET, SUBSET], ALL_TAC] THEN
        SUBGOAL_THEN ([[~(d IN frontier(convex hull {a:real^2,b,c}))]]) MP_TAC THENL
         [ASM_REWRITE_TAC [frontier, IN_DIFF],
          REWRITE_TAC [FRONTIER_OF_TRIANGLE, SEGMENT_CONVEX_HULL] THEN SET_TAC []],
        REWRITE_TAC [IN_DIFF, IN_UNION] THEN REPEAT STRIP_TAC THENL
         [UNDISCH_TAC ([[y IN segment(a:real^2,c)]]) THEN
          REWRITE_TAC [open_segment, IN_DIFF, SEGMENT_CONVEX_HULL] THEN
          MATCH_MP_TAC h42 THEN
          MATCH_MP_TAC HULL_MONO THEN SET_TAC [],
          UNDISCH_TAC ([[~collinear{a:real^2,b,c}]]) THEN REWRITE_TAC [] THEN
          ONCE_REWRITE_TAC [h43] THEN
          MATCH_MP_TAC COLLINEAR_3_TRANS THEN EXISTS_TAC ([[y:real^2]]) THEN
          MAP_EVERY UNDISCH_TAC [([[y IN convex hull {a:real^2, b}]]), ([[y IN segment(a:real^2,c)]])] THEN
          REWRITE_TAC [open_segment, (← HolLight.GSYM SEGMENT_CONVEX_HULL), IN_DIFF] THEN
          REWRITE_TAC [DE_MORGAN_THM, IN_INSERT, NOT_IN_EMPTY] THEN
          DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
          ASM_REWRITE_TAC [IMP_IMP, (← HolLight.GSYM BETWEEN_IN_SEGMENT)] THEN
          DISCH_THEN (CONJUNCTS_THEN (MP_TAC o
            HolLight.MATCH_MP BETWEEN_IMP_COLLINEAR)) THEN
          REWRITE_TAC [INSERT_AC, IMP_IMP],
          UNDISCH_TAC ([[~collinear{a:real^2,b,c}]]) THEN REWRITE_TAC [] THEN
          ONCE_REWRITE_TAC [h44] THEN
          MATCH_MP_TAC COLLINEAR_3_TRANS THEN EXISTS_TAC ([[y:real^2]]) THEN
          MAP_EVERY UNDISCH_TAC [([[y IN convex hull {b:real^2, c}]]), ([[y IN segment(a:real^2,c)]])] THEN
          REWRITE_TAC [open_segment, (← HolLight.GSYM SEGMENT_CONVEX_HULL), IN_DIFF] THEN
          REWRITE_TAC [DE_MORGAN_THM, IN_INSERT, NOT_IN_EMPTY] THEN
          DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
          ASM_REWRITE_TAC [IMP_IMP, (← HolLight.GSYM BETWEEN_IN_SEGMENT)] THEN
          DISCH_THEN (CONJUNCTS_THEN (MP_TAC o
            HolLight.MATCH_MP BETWEEN_IMP_COLLINEAR)) THEN
          REWRITE_TAC [INSERT_AC, IMP_IMP]],
        REWRITE_TAC [h45] THEN
        MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC THENL
         [MP_TAC (← HolLight.ISPECL [([[convex hull {a:real^2,b,c}]]), ([[convex hull{a:real^2,b}]])] FACE_OF_STILLCONVEX) THEN
          REWRITE_TAC [CONVEX_CONVEX_HULL] THEN MATCH_MP_TAC h46 THEN
          ASM_SIMP_TAC [FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
          EXISTS_TAC ([[{a:real^2,b}]]) THEN SET_TAC [],
          MP_TAC (← HolLight.ISPECL [([[convex hull {a:real^2,b,c}]]), ([[convex hull{b:real^2,c}]])] FACE_OF_STILLCONVEX) THEN
          REWRITE_TAC [CONVEX_CONVEX_HULL] THEN MATCH_MP_TAC h47 THEN
          ASM_SIMP_TAC [FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
          EXISTS_TAC ([[{b:real^2,c}]]) THEN SET_TAC []]],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[?n:real^2.
        ~(n = vec 0) /\ orthogonal n (c - a) /\
        &0 < n dot (c - b)]]) STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN ([[?n:real^2. ~(n = vec 0) /\ orthogonal n (c - a)]]) STRIP_ASSUME_TAC THENL
       [ONCE_REWRITE_TAC [ORTHOGONAL_SYM] THEN
        MATCH_MP_TAC ORTHOGONAL_TO_VECTOR_EXISTS THEN
        REWRITE_TAC [DIMINDEX_2, LE_REFL],
        ALL_TAC] THEN
      REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC h48 THENL
       [EXISTS_TAC ([[n:real^2]]) THEN ASM_REWRITE_TAC [],
        EXISTS_TAC ([[--n:real^2]]) THEN ASM_REWRITE_TAC [DOT_LNEG] THEN
        ASM_REWRITE_TAC [VECTOR_NEG_EQ_0, ORTHOGONAL_LNEG],
        UNDISCH_TAC ([[~collinear{a:real^2,b,c}]]) THEN
        ONCE_REWRITE_TAC [h49] THEN
        MATCH_MP_TAC h50 THEN
        ONCE_REWRITE_TAC [COLLINEAR_3] THEN
        MATCH_MP_TAC ORTHOGONAL_TO_ORTHOGONAL_2D THEN
        EXISTS_TAC ([[n:real^2]]) THEN
        ONCE_REWRITE_TAC [(← HolLight.GSYM ORTHOGONAL_RNEG)] THEN
        ASM_REWRITE_TAC [VECTOR_NEG_SUB] THEN
        ASM_REWRITE_TAC [orthogonal]],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[n dot (a - b:real^2) = n dot (c - b)]]) ASSUME_TAC THENL
     [REWRITE_TAC [DOT_RSUB, real_sub, REAL_EQ_ADD_RCANCEL] THEN
      ONCE_REWRITE_TAC [h51] THEN
      ASM_REWRITE_TAC [(← HolLight.GSYM DOT_RSUB), (← HolLight.GSYM orthogonal)],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!y:real^2. y IN convex hull {a,b,c} /\ ~(y = b) ==> &0 < n dot (y - b)]]) ASSUME_TAC THENL
     [REWRITE_TAC [CONVEX_HULL_3_ALT, FORALL_IN_GSPEC, IMP_CONJ] THEN
      REWRITE_TAC [h52] THEN
      ASM_REWRITE_TAC [DOT_RADD, DOT_RMUL] THEN
      MAP_EVERY X_GEN_TAC [([[r:real]]), ([[s:real]])] THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC [h53] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC [] THEN
      ASM_CASES_TAC ([[r = &1 /\ s = &0]]) THENL [ALL_TAC, ASM_REAL_ARITH_TAC] THEN
      UNDISCH_TAC ([[~(a + r % (b - a) + s % (c - a):real^2 = b)]]) THEN
      ASM_REWRITE_TAC [REAL_LT_REFL, REAL_SUB_LT] THEN VECTOR_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!y:real^2. y IN convex hull {a,b,c} ==> &0 <= n dot (y - b)]]) ASSUME_TAC THENL
     [GEN_TAC THEN ASM_CASES_TAC ([[y:real^2 = b]]) THEN
      ASM_REWRITE_TAC [VECTOR_SUB_REFL, DOT_RZERO, REAL_LE_REFL] THEN
      ASM_MESON_TAC [REAL_LT_IMP_LE],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!y:real^2. y IN convex hull {a,b,c} ==> n dot (y - b) <= n dot (c - b)]]) ASSUME_TAC THENL
     [REWRITE_TAC [CONVEX_HULL_3_ALT, FORALL_IN_GSPEC] THEN
      REWRITE_TAC [h54] THEN
      ASM_REWRITE_TAC [DOT_RADD, DOT_RMUL, h55] THEN
      ASM_SIMP_TAC [REAL_LE_MUL, REAL_LT_IMP_LE],
      ALL_TAC] THEN
    MP_TAC (← HolLight.ISPECL [([[\x:real^2. n dot (x - b)]]),
    ([[path_image (polygonal_path(CONS c p)) INTER convex hull {a:real^2,b,c}]])] CONTINUOUS_ATTAINS_INF) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC COMPACT_INTER THEN
        SIMP_TAC [COMPACT_PATH_IMAGE, PATH_POLYGONAL_PATH] THEN
        SIMP_TAC [COMPACT_CONVEX_HULL, FINITE_IMP_COMPACT,
                 FINITE_INSERT, FINITE_EMPTY],
        HolLight.ASM SET_TAC [],
        SUBGOAL_THEN ([[(\x:real^2. n dot (x - b)) = (\x. n dot x) o (\x. x - b)]]) SUBST1_TAC THENL [REWRITE_TAC [o_DEF], ALL_TAC] THEN
        REWRITE_TAC [o_ASSOC] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        REWRITE_TAC [CONTINUOUS_ON_LIFT_DOT] THEN
        SIMP_TAC [CONTINUOUS_ON_SUB, CONTINUOUS_ON_CONST, CONTINUOUS_ON_ID]],
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN ([[?mx:real^2.
      ~(mx = a) /\ ~(mx = c) /\
      mx IN path_image(polygonal_path(CONS c p)) INTER convex hull {a, b, c} /\
      (!y. y IN
           path_image(polygonal_path(CONS c p)) INTER convex hull {a, b, c}
           ==> n dot (mx - b) <= n dot (y - b))]]) STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM (X_CHOOSE_THEN ([[mx:real^2]]) STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN ([[n dot (mx - b:real^2) <= n dot (c - b)]]) MP_TAC THENL
       [HolLight.ASM SET_TAC [], ALL_TAC] THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [REAL_LE_LT] THEN STRIP_TAC THENL
       [EXISTS_TAC ([[mx:real^2]]) THEN ASM_MESON_TAC [REAL_LT_REFL], ALL_TAC] THEN
      UNDISCH_TAC ([[~(path_image(polygonal_path(CONS c p)) INTER
                   convex hull {a, b, c} SUBSET {a:real^2, c})]]) THEN
      REWRITE_TAC [SUBSET, NOT_FORALL_THM, NOT_IMP, IN_INSERT, NOT_IN_EMPTY] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[my:real^2]]) THEN
      REWRITE_TAC [DE_MORGAN_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      X_GEN_TAC ([[y:real^2]]) THEN REWRITE_TAC [IN_INTER] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC ([[n dot (mx - b:real^2)]]) THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN HolLight.ASM SET_TAC [],
        FIRST_X_ASSUM MATCH_MP_TAC THEN HolLight.ASM SET_TAC []],
      FIRST_X_ASSUM (CHOOSE_THEN ((fun _ => ALL_TAC)))] THEN
    ABBREV_TAC ([[m = (n:real^2) dot (mx - b)]]) THEN
    SUBGOAL_THEN ([[&0 < m]]) ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      CONJ_TAC THENL [HolLight.ASM SET_TAC [], DISCH_THEN SUBST_ALL_TAC] THEN
      UNDISCH_TAC ([[segment[b:real^2,c] INTER path_image (polygonal_path (CONS c p))
      SUBSET {c}]]) THEN
      REWRITE_TAC [SUBSET, IN_INTER] THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC ([[b:real^2]])) THEN
      ASM_REWRITE_TAC [IN_SING, ENDS_IN_SEGMENT] THEN HolLight.ASM SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[?z:real^2. MEM z p /\
               z IN (convex hull {a,b,c} DIFF {a,c}) /\
               n dot (z - b) = m]]) STRIP_ASSUME_TAC THENL
     [ALL_TAC,
      MAP_EVERY EXISTS_TAC [([[b:real^2]]), ([[z:real^2]])] THEN
      ASM_REWRITE_TAC [Session.listDefs.MEM] THEN
      MATCH_MP_TAC h56 THEN
      CONJ_TAC THENL [ASM_MESON_TAC [REAL_LT_REFL], DISCH_TAC] THEN
      X_GEN_TAC ([[w:real^2]]) THEN DISCH_TAC THEN
      MATCH_MP_TAC INSIDE_SAME_COMPONENT THEN
      EXISTS_TAC ([[d:real^2]]) THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN ([[~(z:real^2 = a) /\ ~(z = c)]]) STRIP_ASSUME_TAC THENL
       [HolLight.ASM SET_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN ([[(z:real^2) IN path_image(polygonal_path(CONS c p)) /\
      (z:real^2) IN path_image(polygonal_path p)]]) STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC (← HolLight.REWRITE_RULE [SUBSET] VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH) THEN
        ASM_REWRITE_TAC [IN_SET_OF_LIST, Session.listDefs.MEM],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[~(z IN segment[a:real^2,b]) /\ ~(z IN segment[b,c])]]) STRIP_ASSUME_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN ([[~collinear{b:real^2,a,z} /\ ~collinear{b,c,z}]]) STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC [COLLINEAR_3_AFFINE_HULL] THEN
        MATCH_MP_TAC h57 THEN
        EXISTS_TAC ([[convex hull {a:real^2,b,c}]]) THEN
        CONJ_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
        ASM_SIMP_TAC [(← HolLight.GSYM AFFINE_INDEPENDENT_CONVEX_AFFINE_HULL),
                     INSERT_SUBSET, EMPTY_SUBSET, IN_INSERT] THEN
        ASM_REWRITE_TAC [(← HolLight.GSYM SEGMENT_CONVEX_HULL)] THEN
        ONCE_REWRITE_TAC [SEGMENT_SYM] THEN ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[segment(b:real^2,z) INTER segment[a,b] = {} /\
      segment(b,z) INTER segment[b,c] = {}]]) STRIP_ASSUME_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
        CONJ_TAC THEN X_GEN_TAC ([[v:real^2]]) THEN STRIP_TAC THENL
         [UNDISCH_TAC ([[~collinear{b:real^2,a,z}]]),
          UNDISCH_TAC ([[~collinear{b:real^2,c,z}]])] THEN
        REWRITE_TAC [] THEN
        ONCE_REWRITE_TAC [h58] THEN
        MATCH_MP_TAC COLLINEAR_3_TRANS THEN
        EXISTS_TAC ([[v:real^2]]) THEN
        UNDISCH_TAC ([[v IN segment(b:real^2,z)]]) THEN
        REWRITE_TAC [open_segment, IN_DIFF, IN_INSERT, NOT_IN_EMPTY] THEN
        REWRITE_TAC [DE_MORGAN_THM, IMP_CONJ] THENL
         [UNDISCH_TAC ([[v IN segment[a:real^2,b] ]]),
          UNDISCH_TAC ([[v IN segment[b:real^2,c] ]])] THEN
        ONCE_REWRITE_TAC [IMP_IMP] THEN REWRITE_TAC [(← HolLight.GSYM BETWEEN_IN_SEGMENT)] THEN
        DISCH_THEN (CONJUNCTS_THEN (MP_TAC o HolLight.MATCH_MP BETWEEN_IMP_COLLINEAR)) THEN
        REWRITE_TAC [INSERT_AC] THEN SIMP_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[segment[b:real^2,z] SUBSET convex hull {a,b,c}]]) ASSUME_TAC THENL
       [REWRITE_TAC [SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
        REWRITE_TAC [CONVEX_CONVEX_HULL, INSERT_SUBSET, EMPTY_SUBSET] THEN
        SIMP_TAC [HULL_INC, IN_INSERT] THEN HolLight.ASM SET_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[segment(b:real^2,z) SUBSET convex hull {a,b,c}]]) ASSUME_TAC THENL
       [REWRITE_TAC [open_segment] THEN HolLight.ASM SET_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN ([[segment(b:real^2,z) INTER path_image(polygonal_path(CONS c p)) = {}]]) ASSUME_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
        X_GEN_TAC ([[v:real^2]]) THEN STRIP_TAC THEN
        SUBGOAL_THEN ([[m <= n dot (v - b:real^2)]]) MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN HolLight.ASM SET_TAC [], ALL_TAC] THEN
        REWRITE_TAC [REAL_NOT_LE] THEN
        UNDISCH_TAC ([[v IN segment(b:real^2,z)]]) THEN REWRITE_TAC [IN_SEGMENT] THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        DISCH_THEN (X_CHOOSE_THEN ([[t:real]]) STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC [DOT_RMUL, h59] THEN
        ONCE_REWRITE_TAC [h60] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC [REAL_SUB_LT],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[segment(b:real^2,z) SUBSET interior(convex hull {a,b,c})]]) ASSUME_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC ([[(convex hull {a:real^2,b,c}) DIFF frontier(convex hull {a,b,c})]]) THEN
        CONJ_TAC THENL
         [ALL_TAC,
          REWRITE_TAC [frontier] THEN MATCH_MP_TAC h61 THEN
          REWRITE_TAC [CLOSURE_SUBSET]] THEN
        REWRITE_TAC [FRONTIER_OF_TRIANGLE] THEN MATCH_MP_TAC h62 THEN
        ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
        X_GEN_TAC ([[v:real^2]]) THEN REWRITE_TAC [IN_SEGMENT] THEN
        DISCH_THEN (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) MP_TAC) THEN
        DISCH_THEN (X_CHOOSE_THEN ([[s:real]]) STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC [NOT_EXISTS_THM] THEN X_GEN_TAC ([[t:real]]) THEN
        REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN (MP_TAC o HolLight.AP_TERM ([[\x:real^2. n dot (x - b)]])) THEN
        REWRITE_TAC [h63] THEN
        ASM_REWRITE_TAC [VECTOR_SUB_REFL, VECTOR_ADD_LID, VECTOR_MUL_RZERO] THEN
        ASM_REWRITE_TAC [DOT_RADD, DOT_RMUL] THEN MATCH_MP_TAC h64 THEN
        ASM_SIMP_TAC [REAL_LT_MUL, REAL_SUB_LT] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        SIMP_TAC [IN_INTER, IN_INSERT, HULL_INC] THEN MATCH_MP_TAC (← HolLight.REWRITE_RULE [SUBSET] VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH) THEN
        REWRITE_TAC [set_of_list, IN_INSERT],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[?y:real^2. y IN segment(b,z) /\ y IN interior(convex hull {a',b,c'})]]) STRIP_ASSUME_TAC THENL
       [REWRITE_TAC [INTER, (← HolLight.GSYM (← HolLight.ASSUME ([[interior(convex hull {a, b, c}) INTER {x:real^2 | x$2 - b$2 < e} =
        interior(convex hull {a', b, c'})]])))] THEN
        REWRITE_TAC [IN_ELIM_THM] THEN MATCH_MP_TAC h65 THEN
        ASM_REWRITE_TAC [] THEN ASM_REWRITE_TAC [IN_SEGMENT] THEN EXISTS_TAC ([[b + min (&1 / &2) (e / &2 / norm(z - b)) % (z - b):real^2]]) THEN
        CONJ_TAC THENL
         [EXISTS_TAC ([[min (&1 / &2) (e / &2 / norm (z - b:real^2))]]) THEN
          REPEAT CONJ_TAC THENL [ALL_TAC, REAL_ARITH_TAC2, VECTOR_ARITH_TAC] THEN
          REWRITE_TAC [REAL_LT_MIN] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
          ASM_SIMP_TAC [REAL_HALF, REAL_LT_DIV, NORM_POS_LT, VECTOR_SUB_EQ],
          REWRITE_TAC [VECTOR_ADD_COMPONENT, REAL_ADD_SUB] THEN
          MATCH_MP_TAC h66 THEN
          SIMP_TAC [COMPONENT_LE_NORM, DIMINDEX_2, ARITH] THEN
          ASM_REWRITE_TAC [NORM_MUL] THEN
          ASM_SIMP_TAC [(← HolLight.GSYM REAL_LE_RDIV_EQ), NORM_POS_LT, VECTOR_SUB_EQ] THEN
          MATCH_MP_TAC h67 THEN
          MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_DIV THEN
          ASM_REWRITE_TAC [REAL_HALF, NORM_POS_LT, VECTOR_SUB_EQ]],
        ALL_TAC] THEN
      MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN EXISTS_TAC ([[y:real^2]]) THEN
      CONJ_TAC THENL
       [REWRITE_TAC [connected_component] THEN
        EXISTS_TAC ([[interior(convex hull {a':real^2,b,c'})]]) THEN
        ASM_REWRITE_TAC [] THEN
        SIMP_TAC [CONVEX_CONNECTED, CONVEX_INTERIOR, CONVEX_CONVEX_HULL] THEN
        SIMP_TAC [PATH_IMAGE_JOIN, PATHSTART_JOIN, PATHSTART_LINEPATH,
           PATHFINISH_LINEPATH, PATHSTART_POLYGONAL_PATH, Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD] THEN
        REWRITE_TAC [h68] THEN
        REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC h69 THEN
          EXISTS_TAC ([[interior(convex hull {a:real^2,b,c})]]) THEN
          ASM_SIMP_TAC [SUBSET_INTERIOR] THEN
          MP_TAC (← HolLight.ISPECL [([[a:real^2]]), ([[b:real^2]]), ([[c:real^2]])] FRONTIER_OF_TRIANGLE) THEN
          REWRITE_TAC [PATH_IMAGE_LINEPATH, frontier] THEN
          MATCH_MP_TAC h70 THEN
          EXISTS_TAC ([[convex hull {a:real^2,b,c}]]) THEN
          REWRITE_TAC [INTERIOR_SUBSET, CLOSURE_SUBSET],
          MATCH_MP_TAC h71 THEN
          EXISTS_TAC ([[interior(convex hull {a:real^2,b,c})]]) THEN
          ASM_SIMP_TAC [SUBSET_INTERIOR] THEN
          MP_TAC (← HolLight.ISPECL [([[a:real^2]]), ([[b:real^2]]), ([[c:real^2]])] FRONTIER_OF_TRIANGLE) THEN
          REWRITE_TAC [PATH_IMAGE_LINEPATH, frontier] THEN
          MATCH_MP_TAC h72 THEN
          EXISTS_TAC ([[convex hull {a:real^2,b,c}]]) THEN
          REWRITE_TAC [INTERIOR_SUBSET, CLOSURE_SUBSET],
          MATCH_MP_TAC h73 THEN
          EXISTS_TAC ([[{x | (x:real^2)$2 - (b:real^2)$2 < e}]]) THEN
          CONJ_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
          REWRITE_TAC [h74] THEN
          REWRITE_TAC [SUBSET, IN_DIFF, IN_ELIM_THM, REAL_NOT_LT, IN_UNIV] THEN
          MP_TAC (← HolLight.ISPEC ([[CONS (c:real^2) p]]) PATH_IMAGE_POLYGONAL_PATH_SUBSET_CONVEX_HULL) THEN
          REWRITE_TAC [Session.listThms1.NOT_CONS_NIL] THEN
          MATCH_MP_TAC h75 THEN
          REWRITE_TAC [h76] THEN
          SIMP_TAC [SUBSET_HULL, CONVEX_HALFSPACE_COMPONENT_GE] THEN
          REWRITE_TAC [set_of_list, h77] THEN
          ASM_REWRITE_TAC [INSERT_SUBSET, IN_ELIM_THM] THEN
          ASM_REWRITE_TAC [SUBSET, IN_SET_OF_LIST, IN_ELIM_THM]],
        REWRITE_TAC [connected_component] THEN
        EXISTS_TAC ([[segment(b:real^2,z)]]) THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [CONNECTED_SEGMENT] THEN
        SIMP_TAC [PATH_IMAGE_JOIN, PATHSTART_JOIN, PATHSTART_LINEPATH,
           PATHFINISH_LINEPATH, PATHSTART_POLYGONAL_PATH, Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD] THEN
        REWRITE_TAC [PATH_IMAGE_LINEPATH] THEN HolLight.ASM SET_TAC []]] THEN
    SUBGOAL_THEN ([[?u v:real^2.
        MEM u (CONS c p) /\ MEM v (CONS c p) /\
        mx IN segment[u,v] /\
        segment[u,v] SUBSET path_image(polygonal_path(CONS c p)) /\
        ~(a IN segment[u,v] /\ c IN segment[u,v]) /\
        n dot (u - b) <= m]]) STRIP_ASSUME_TAC THENL
     [MP_TAC (← HolLight.ISPECL [([[CONS (c:real^2) p]]), ([[mx:real^2]])] PATH_IMAGE_POLYGONAL_PATH_SUBSET_SEGMENTS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [Session.listDefs.LENGTH, h78] THEN
        HolLight.ASM SET_TAC [],
        ALL_TAC] THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[u:real^2]]), ([[v:real^2]])] THEN
      ASM_REWRITE_TAC [PATHSTART_POLYGONAL_PATH, PATHFINISH_POLYGONAL_PATH] THEN
      ASM_REWRITE_TAC [Session.listThms1.NOT_CONS_NIL, Session.listDefs.LAST, Session.listDefs.HD] THEN STRIP_TAC THEN
      SUBGOAL_THEN ([[n dot (u - b) <= m \/ n dot (v - b:real^2) <= m]]) STRIP_ASSUME_TAC THENL
       [REWRITE_TAC [(← HolLight.GSYM REAL_NOT_LT), (← HolLight.GSYM DE_MORGAN_THM)] THEN STRIP_TAC THEN
        UNDISCH_TAC ([[n dot (mx - b:real^2) = m]]) THEN
        UNDISCH_TAC ([[(mx:real^2) IN segment[u,v] ]]) THEN
        REWRITE_TAC [IN_SEGMENT] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [h79] THEN
        MATCH_MP_TAC h80 THEN
        REWRITE_TAC [(← HolLight.GSYM DOT_LNEG)] THEN REWRITE_TAC [DOT_RADD, DOT_RMUL] THEN
        MATCH_MP_TAC REAL_CONVEX_BOUND_LT THEN
        ASM_REWRITE_TAC [DOT_LNEG, REAL_LT_NEG2] THEN ASM_REAL_ARITH_TAC,
        MAP_EVERY EXISTS_TAC [([[u:real^2]]), ([[v:real^2]])] THEN ASM_REWRITE_TAC [] THEN
        ONCE_REWRITE_TAC [CONJ_SYM] THEN ASM_REWRITE_TAC [],
        MAP_EVERY EXISTS_TAC [([[v:real^2]]), ([[u:real^2]])] THEN
        ONCE_REWRITE_TAC [SEGMENT_SYM] THEN ASM_REWRITE_TAC [] THEN
        ONCE_REWRITE_TAC [CONJ_SYM] THEN ASM_REWRITE_TAC []],
      ALL_TAC] THEN
    ASM_CASES_TAC ([[n dot (u - b:real^2) < n dot (c - b)]]) THENL
     [SUBGOAL_THEN ([[~(u:real^2 = a) /\ ~(u = c)]]) STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC [REAL_LT_REFL], ALL_TAC] THEN
      UNDISCH_TAC ([[MEM (u:real^2) (CONS c p)]]) THEN
      ASM_REWRITE_TAC [Session.listDefs.MEM] THEN DISCH_TAC THEN EXISTS_TAC ([[u:real^2]]) THEN
      ASM_REWRITE_TAC [IN_DIFF, IN_INSERT, NOT_IN_EMPTY] THEN
      ASM_CASES_TAC ([[mx:real^2 = u]]) THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
      MATCH_MP_TAC h81 THEN CONJ_TAC THENL
       [DISCH_TAC THEN ASM_REWRITE_TAC [(← HolLight.GSYM REAL_LE_ANTISYM)] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [IN_INTER] THEN
        MATCH_MP_TAC (← HolLight.REWRITE_RULE [SUBSET] VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH) THEN
        ASM_REWRITE_TAC [IN_SET_OF_LIST, Session.listDefs.MEM],
        ALL_TAC] THEN
      MP_TAC (← HolLight.ISPECL [([[segment(u:real^2,mx)]]), ([[convex hull {a:real^2,b,c}]])] CONNECTED_INTER_FRONTIER) THEN
      REWRITE_TAC [CONNECTED_SEGMENT] THEN MATCH_MP_TAC h82 THEN
      REPEAT CONJ_TAC THENL
       [DISCH_TAC THEN
        SUBGOAL_THEN ([[closure(segment(u:real^2,mx)) SUBSET convex hull {a,b,c}]]) MP_TAC THENL
         [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC [] THEN
          MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
          MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
          SIMP_TAC [FINITE_IMP_COMPACT, FINITE_INSERT, FINITE_EMPTY],
          ASM_REWRITE_TAC [SUBSET, CLOSURE_SEGMENT] THEN
          DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC [ENDS_IN_SEGMENT]],
        REWRITE_TAC [FRONTIER_OF_TRIANGLE] THEN
        MATCH_MP_TAC h83 THEN
        MAP_EVERY EXISTS_TAC [([[a:real^2]]), ([[b:real^2]]), ([[c:real^2]]), ([[segment[u:real^2,v] ]]),
          ([[path_image(polygonal_path(CONS (c:real^2) p))]])] THEN
        ASM_REWRITE_TAC [ENDS_IN_SEGMENT, SUBSET_SEGMENT] THEN CONJ_TAC THENL
         [MP_TAC (← HolLight.ISPEC ([[CONS (c:real^2) p]]) PATH_IMAGE_POLYGONAL_PATH_SUBSET_CONVEX_HULL) THEN
          REWRITE_TAC [Session.listThms1.NOT_CONS_NIL] THEN MATCH_MP_TAC h84 THEN
          MATCH_MP_TAC h85 THEN
          EXISTS_TAC ([[{x:real^2 | (x:real^2)$2 >= (b:real^2)$2 + e}]]) THEN
          ASM_REWRITE_TAC [IN_ELIM_THM, real_ge, REAL_NOT_LE, REAL_LT_ADDR] THEN
          MATCH_MP_TAC HULL_MINIMAL THEN
          REWRITE_TAC [(← HolLight.GSYM real_ge), CONVEX_HALFSPACE_COMPONENT_GE] THEN
          REWRITE_TAC [SUBSET, set_of_list, FORALL_IN_INSERT, IN_ELIM_THM] THEN
          ASM_REWRITE_TAC [IN_SET_OF_LIST, h86],
          REWRITE_TAC [EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
          X_GEN_TAC ([[y:real^2]]) THEN REWRITE_TAC [IN_SEGMENT] THEN
          DISCH_THEN (CONJUNCTS_THEN MP_TAC) THEN
          DISCH_THEN (X_CHOOSE_THEN ([[s:real]]) STRIP_ASSUME_TAC) THEN
          ASM_REWRITE_TAC [NOT_EXISTS_THM] THEN X_GEN_TAC ([[t:real]]) THEN
          REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
          DISCH_THEN (MP_TAC o HolLight.AP_TERM ([[\x:real^2. n dot (x - b)]])) THEN
          REWRITE_TAC [h87] THEN
          ASM_REWRITE_TAC [DOT_RADD, DOT_RMUL] THEN MATCH_MP_TAC h88 THEN
          ASM_SIMP_TAC [REAL_LT_LMUL, REAL_SUB_LT] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN
          CONJ_TAC THENL [ASM_REAL_ARITH_TAC, FIRST_X_ASSUM MATCH_MP_TAC] THEN
          SIMP_TAC [IN_INTER, HULL_INC, IN_INSERT] THEN
          MATCH_MP_TAC (← HolLight.REWRITE_RULE [SUBSET] VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH) THEN
          REWRITE_TAC [set_of_list, IN_INSERT]],
        ALL_TAC] THEN
      ASM_CASES_TAC ([[mx IN interior(convex hull {a:real^2,b,c})]]) THENL
       [UNDISCH_TAC ([[mx IN interior(convex hull {a:real^2,b,c})]]) THEN
        REWRITE_TAC [IN_INTERIOR_CBALL, SUBSET, IN_CBALL] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[ee:real]]) STRIP_ASSUME_TAC) THEN
        REWRITE_TAC [(← HolLight.GSYM MEMBER_NOT_EMPTY), IN_INTER] THEN
        ONCE_REWRITE_TAC [SEGMENT_SYM] THEN ASM_REWRITE_TAC [IN_SEGMENT] THEN
        REWRITE_TAC [h89] THEN
        EXISTS_TAC ([[min (&1 / &2) (ee / norm(u - mx:real^2))]]) THEN
        REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC h90 THEN
          ASM_SIMP_TAC [REAL_LT_DIV, NORM_POS_LT, VECTOR_SUB_EQ],
          REAL_ARITH_TAC2,
          FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [SessionMultiLib.Vectors.dist, h91] THEN
          ASM_SIMP_TAC [NORM_MUL, (← HolLight.GSYM REAL_LE_RDIV_EQ), NORM_POS_LT,
                       VECTOR_SUB_EQ] THEN
          REWRITE_TAC [NORM_SUB] THEN MATCH_MP_TAC h92 THEN
          ASM_SIMP_TAC [REAL_LT_DIV, NORM_POS_LT, VECTOR_SUB_EQ]],
        ALL_TAC] THEN
      MP_TAC (← HolLight.ISPEC ([[{a:real^2,b,c}]]) AFFINE_INDEPENDENT_SPAN_EQ) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [] THEN
        SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY] THEN
        ASM_REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY, DIMINDEX_2] THEN
        CONV_TAC NUM_REDUCE_CONV,
        ALL_TAC] THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [EXTENSION] THEN
      REWRITE_TAC [AFFINE_HULL_3, IN_UNIV] THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC ([[u:real^2]])) THEN
      REWRITE_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[r:real]]), ([[s:real]]), ([[t:real]])] THEN STRIP_TAC THEN
      SUBGOAL_THEN ([[mx IN convex hull {a:real^2,b,c}]]) MP_TAC THENL
       [HolLight.ASM SET_TAC [], ALL_TAC] THEN
      ONCE_REWRITE_TAC [SEGMENT_SYM] THEN REWRITE_TAC [CONVEX_HULL_3] THEN
      REWRITE_TAC [(← HolLight.GSYM MEMBER_NOT_EMPTY), IN_ELIM_THM] THEN
      ONCE_REWRITE_TAC [INTER_COMM] THEN
      REWRITE_TAC [IN_INTER, EXISTS_IN_GSPEC] THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[rx:real]]), ([[sx:real]]), ([[tx:real]])] THEN
      ASM_CASES_TAC ([[rx = &0]]) THENL
       [ASM_REWRITE_TAC [REAL_LE_REFL, REAL_ADD_LID] THEN
        REWRITE_TAC [VECTOR_MUL_LZERO, VECTOR_ADD_LID] THEN STRIP_TAC THEN
        UNDISCH_TAC ([[segment[b:real^2,c] INTER path_image(polygonal_path(CONS c p))
         SUBSET {c}]]) THEN
        REWRITE_TAC [SUBSET] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[mx:real^2]])) THEN
        MATCH_MP_TAC h93 THEN
        REWRITE_TAC [IN_SING] THEN CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
        REWRITE_TAC [IN_INTER, SEGMENT_CONVEX_HULL] THEN
        CONJ_TAC THENL [ALL_TAC, HolLight.ASM SET_TAC []] THEN
        REWRITE_TAC [CONVEX_HULL_2, IN_ELIM_THM] THEN ASM_MESON_TAC [],
        ALL_TAC] THEN
      ASM_CASES_TAC ([[rx = &1]]) THENL
       [ASM_REWRITE_TAC [] THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        SUBGOAL_THEN ([[sx = &0 /\ tx = &0]]) ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC, ASM_REWRITE_TAC []] THEN
        ASM_REWRITE_TAC [VECTOR_MUL_LZERO, VECTOR_MUL_LID, VECTOR_ADD_RID],
        ALL_TAC] THEN
      ASM_CASES_TAC ([[tx = &0]]) THENL
       [ASM_REWRITE_TAC [REAL_LE_REFL, REAL_ADD_RID] THEN
        REWRITE_TAC [VECTOR_MUL_LZERO, VECTOR_ADD_RID] THEN STRIP_TAC THEN
        UNDISCH_TAC ([[segment[a:real^2,b] INTER path_image(polygonal_path(CONS c p))
         SUBSET {a,b}]]) THEN
        REWRITE_TAC [SUBSET] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[mx:real^2]])) THEN
        MATCH_MP_TAC h94 THEN CONJ_TAC THENL
         [REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY, DE_MORGAN_THM] THEN
          CONJ_TAC THENL [ASM_MESON_TAC [], DISCH_THEN SUBST_ALL_TAC] THEN
          UNDISCH_TAC ([[n dot (b - b:real^2) = m]]) THEN
          REWRITE_TAC [VECTOR_SUB_REFL, DOT_RZERO] THEN
          ASM_REAL_ARITH_TAC,
          ALL_TAC] THEN
        REWRITE_TAC [IN_INTER, SEGMENT_CONVEX_HULL] THEN
        CONJ_TAC THENL [ALL_TAC, HolLight.ASM SET_TAC []] THEN
        REWRITE_TAC [CONVEX_HULL_2, IN_ELIM_THM] THEN ASM_MESON_TAC [],
        ALL_TAC] THEN
      ASM_CASES_TAC ([[tx = &1]]) THENL
       [ASM_REWRITE_TAC [] THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        SUBGOAL_THEN ([[sx = &0 /\ rx = &0]]) ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC, ASM_REWRITE_TAC []] THEN
       ASM_REWRITE_TAC [VECTOR_MUL_LZERO, VECTOR_MUL_LID, VECTOR_ADD_LID],
       ALL_TAC] THEN
      ASM_CASES_TAC ([[sx = &1]]) THENL
       [ASM_REWRITE_TAC [] THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        SUBGOAL_THEN ([[rx = &0 /\ tx = &0]]) ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC, ASM_REWRITE_TAC []] THEN
       ASM_REWRITE_TAC [VECTOR_MUL_LZERO, VECTOR_MUL_LID, VECTOR_ADD_LID,
                       VECTOR_ADD_RID] THEN
       DISCH_THEN SUBST_ALL_TAC THEN
       UNDISCH_TAC ([[n dot (b - b:real^2) = m]]) THEN
       REWRITE_TAC [VECTOR_SUB_REFL, DOT_RZERO] THEN
       ASM_REAL_ARITH_TAC,
       ALL_TAC] THEN
      ASM_CASES_TAC ([[sx = &0]]) THENL
       [ALL_TAC,
        STRIP_TAC THEN
        UNDISCH_TAC ([[~(mx IN interior(convex hull {a:real^2, b, c}))]]) THEN
        MATCH_MP_TAC h95 THEN
        ASM_SIMP_TAC [INTERIOR_CONVEX_HULL_3] THEN
        REWRITE_TAC [IN_ELIM_THM] THEN
        MAP_EVERY EXISTS_TAC [([[rx:real]]), ([[sx:real]]), ([[tx:real]])] THEN
        REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC] THEN
      UNDISCH_THEN ([[sx = &0]]) SUBST_ALL_TAC THEN
      REWRITE_TAC [VECTOR_MUL_LZERO, VECTOR_ADD_LID, REAL_LE_REFL] THEN
      REWRITE_TAC [REAL_ADD_LID] THEN STRIP_TAC THEN
      SUBGOAL_THEN ([[&0 < rx /\ rx < &1 /\ &0 < tx /\ tx < &1]]) STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      ASM_REWRITE_TAC [IN_SEGMENT] THEN
      SUBGOAL_THEN ([[?q. q * (rx - r) <= rx /\
          q * (tx - t) <= tx /\
          &0 < q /\ q < &1]]) STRIP_ASSUME_TAC THENL
       [EXISTS_TAC ([[min (&1 / &2)
            (min (if rx:real = r then &1 / &2 else rx / abs(rx - r))
                 (if tx:real = t then &1 / &2 else tx / abs(tx - t)))]]) THEN
        REWRITE_TAC [REAL_LT_MIN, REAL_MIN_LT] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
         [ASM_CASES_TAC ([[r:real = rx]]) THENL
           [ASM_REWRITE_TAC [REAL_SUB_REFL, REAL_MUL_RZERO], ALL_TAC] THEN
          MATCH_MP_TAC h96 THEN
          REWRITE_TAC [REAL_ABS_MUL] THEN
          ASM_SIMP_TAC [(← HolLight.GSYM REAL_LE_RDIV_EQ), h97] THEN
          MATCH_MP_TAC h98 THEN
          CONV_TAC REAL_RAT_REDUCE_CONV THEN
          COND_CASES_TAC THEN ASM_SIMP_TAC [REAL_LE_DIV, REAL_ABS_POS] THEN
          CONV_TAC REAL_RAT_REDUCE_CONV,
          ASM_CASES_TAC ([[t:real = tx]]) THENL
           [ASM_REWRITE_TAC [REAL_SUB_REFL, REAL_MUL_RZERO], ALL_TAC] THEN
          MATCH_MP_TAC h99 THEN
          REWRITE_TAC [REAL_ABS_MUL] THEN
          ASM_SIMP_TAC [(← HolLight.GSYM REAL_LE_RDIV_EQ), h100] THEN
          MATCH_MP_TAC h101 THEN
          CONV_TAC REAL_RAT_REDUCE_CONV THEN
          COND_CASES_TAC THEN ASM_SIMP_TAC [REAL_LE_DIV, REAL_ABS_POS] THEN
          CONV_TAC REAL_RAT_REDUCE_CONV,
          COND_CASES_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
          MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC,
          COND_CASES_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
          MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC],
        ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [([[(&1 - q) * rx + q * r]]),
        ([[q * s:real]]),
        ([[(&1 - q) * tx + q * t:real]])] THEN
      REWRITE_TAC [CONJ_ASSOC] THEN CONJ_TAC THENL
       [ALL_TAC,
        EXISTS_TAC ([[q:real]]) THEN ASM_REWRITE_TAC [] THEN VECTOR_ARITH_TAC] THEN
      REWRITE_TAC [h102] THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ALL_TAC, REAL_ARITH_TAC2] THEN
      REWRITE_TAC [h103] THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN
      UNDISCH_TAC ([[n dot (u - b:real^2) < n dot (c - b)]]) THEN
      ASM_REWRITE_TAC [h104] THEN
      REWRITE_TAC [REAL_SUB_REFL, VECTOR_MUL_LZERO, VECTOR_ADD_RID] THEN
      ASM_REWRITE_TAC [DOT_RADD, DOT_RMUL] THEN
      REWRITE_TAC [h105] THEN
      ASM_SIMP_TAC [REAL_LT_MUL_EQ] THEN ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[n dot (u - b) = m /\ n dot (c - b) = m]]) MP_TAC THENL
     [MATCH_MP_TAC h106 THEN
      EXISTS_TAC ([[mx:real^2]]) THEN ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      SIMP_TAC [IN_INTER, HULL_INC, IN_INSERT] THEN
      MATCH_MP_TAC (← HolLight.REWRITE_RULE [SUBSET] VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH) THEN
      REWRITE_TAC [set_of_list, IN_INSERT],
      ALL_TAC] THEN
    DISCH_THEN (CONJUNCTS_THEN (fun th => SUBST_ALL_TAC th THEN ASSUME_TAC th)) THEN
    MAP_EVERY (HolCore.Lib.C UNDISCH_THEN ((fun _ => ALL_TAC))) [([[m <= m]]), ([[~(m < m)]])] THEN
    SUBGOAL_THEN ([[collinear {a:real^2,mx,c} /\ collinear {a,u,c}]]) STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN ([[!y:real^2. n dot (y - b) = m ==> collinear {a,y,c}]]) (fun th => CONJ_TAC THEN MATCH_MP_TAC th THEN ASM_REWRITE_TAC []) THEN
      X_GEN_TAC ([[y:real^2]]) THEN DISCH_TAC THEN
      ONCE_REWRITE_TAC [h107] THEN
      ONCE_REWRITE_TAC [COLLINEAR_3] THEN
      MATCH_MP_TAC ORTHOGONAL_TO_ORTHOGONAL_2D THEN
      EXISTS_TAC ([[n:real^2]]) THEN ASM_REWRITE_TAC [] THEN
      ONCE_REWRITE_TAC [(← HolLight.GSYM ORTHOGONAL_RNEG)] THEN
      ASM_REWRITE_TAC [VECTOR_NEG_SUB] THEN
      MAP_EVERY UNDISCH_TAC [([[n dot (y - b:real^2) = m]]), ([[n dot (c - b:real^2) = m]])] THEN
      REWRITE_TAC [orthogonal, DOT_RSUB] THEN REAL_ARITH_TAC2,
      ALL_TAC] THEN
    ASM_CASES_TAC ([[mx:real^2 = u]]) THENL
     [UNDISCH_THEN ([[mx:real^2 = u]]) SUBST_ALL_TAC THEN
      UNDISCH_TAC ([[MEM (u:real^2) (CONS c p)]]) THEN
      ASM_REWRITE_TAC [Session.listDefs.MEM] THEN DISCH_TAC THEN EXISTS_TAC ([[u:real^2]]) THEN
      ASM_REWRITE_TAC [IN_DIFF, IN_INSERT, NOT_IN_EMPTY] THEN
      HolLight.ASM SET_TAC [],
      ALL_TAC] THEN
    ASM_CASES_TAC ([[mx:real^2 = v]]) THENL
     [UNDISCH_THEN ([[mx:real^2 = v]]) SUBST_ALL_TAC THEN
      UNDISCH_TAC ([[MEM (v:real^2) (CONS c p)]]) THEN
      ASM_REWRITE_TAC [Session.listDefs.MEM] THEN DISCH_TAC THEN EXISTS_TAC ([[v:real^2]]) THEN
      ASM_REWRITE_TAC [IN_DIFF, IN_INSERT, NOT_IN_EMPTY] THEN
      HolLight.ASM SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[collinear {a:real^2,c,mx,u}]]) ASSUME_TAC THENL
     [ASM_SIMP_TAC [COLLINEAR_4_3] THEN
      ONCE_REWRITE_TAC [h108] THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[collinear {a:real^2,u,v}]]) ASSUME_TAC THENL
     [MATCH_MP_TAC COLLINEAR_3_TRANS THEN EXISTS_TAC ([[mx:real^2]]) THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [MATCH_MP_TAC COLLINEAR_SUBSET THEN
        EXISTS_TAC ([[{a:real^2,c,mx,u}]]) THEN ASM_REWRITE_TAC [] THEN SET_TAC [],
        MATCH_MP_TAC BETWEEN_IMP_COLLINEAR THEN
        ASM_REWRITE_TAC [BETWEEN_IN_SEGMENT]],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[collinear {c:real^2,u,v}]]) ASSUME_TAC THENL
     [MATCH_MP_TAC COLLINEAR_3_TRANS THEN EXISTS_TAC ([[mx:real^2]]) THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [MATCH_MP_TAC COLLINEAR_SUBSET THEN
        EXISTS_TAC ([[{a:real^2,c,mx,u}]]) THEN ASM_REWRITE_TAC [] THEN SET_TAC [],
        MATCH_MP_TAC BETWEEN_IMP_COLLINEAR THEN
        ASM_REWRITE_TAC [BETWEEN_IN_SEGMENT]],
      ALL_TAC] THEN
    ASM_CASES_TAC ([[u:real^2 = v]]) THENL
     [UNDISCH_THEN ([[u:real^2 = v]]) SUBST_ALL_TAC THEN
      ASM_MESON_TAC [SEGMENT_REFL, IN_SING],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[collinear {a:real^2,v,c}]]) ASSUME_TAC THENL
     [MATCH_MP_TAC COLLINEAR_3_TRANS THEN EXISTS_TAC ([[u:real^2]]) THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [INSERT_AC]) THEN
      ASM_REWRITE_TAC [INSERT_AC],
      ALL_TAC] THEN
    MP_TAC (← HolLight.ISPECL [([[a:real^2]]), ([[c:real^2]]), ([[u:real^2]]), ([[v:real^2]]),
                   ([[mx:real^2]])] between_lemma) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
            let x1 ← ExceptT.mk (HolLight.PART_MATCH (HolCore.Equal.lhs o HolCore.Kernel.rand) COLLINEAR_TRIPLES w)
            pure (MP_TAC x1)) THEN
        ASM_REWRITE_TAC [FORALL_IN_INSERT, NOT_IN_EMPTY] THEN
        DISCH_THEN SUBST1_TAC THEN
        ONCE_REWRITE_TAC [h109] THEN
        ASM_REWRITE_TAC [],
        ASM_REWRITE_TAC [open_segment, IN_DIFF, IN_INSERT, NOT_IN_EMPTY] THEN
        MP_TAC (← HolLight.ISPECL [([[{a:real^2,b,c}]]), ([[{a:real^2,c}]])] AFFINE_INDEPENDENT_CONVEX_AFFINE_HULL) THEN
        ASM_REWRITE_TAC [SEGMENT_CONVEX_HULL] THEN
        ANTS_TAC THENL [SET_TAC [], DISCH_THEN SUBST1_TAC] THEN
        REWRITE_TAC [IN_INTER] THEN CONJ_TAC THENL [ALL_TAC, HolLight.ASM SET_TAC []] THEN
        ASM_SIMP_TAC [(← HolLight.GSYM COLLINEAR_3_AFFINE_HULL)] THEN
        MATCH_MP_TAC COLLINEAR_SUBSET THEN
        EXISTS_TAC ([[{a:real^2,c,mx,u}]]) THEN
        ASM_REWRITE_TAC [] THEN SET_TAC []],
      ALL_TAC] THEN
    STRIP_TAC THENL
     [EXISTS_TAC ([[u:real^2]]) THEN
      MP_TAC (← HolLight.ASSUME ([[u IN segment(a:real^2,c)]])) THEN
      REWRITE_TAC [open_segment, IN_DIFF, IN_INSERT, NOT_IN_EMPTY] THEN
      REWRITE_TAC [DE_MORGAN_THM] THEN STRIP_TAC THEN
      UNDISCH_TAC ([[MEM (u:real^2) (CONS c p)]]) THEN
      ASM_REWRITE_TAC [Session.listDefs.MEM] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC ([[(u:real^2) IN segment[a,c] ]]) THEN
      REWRITE_TAC [SEGMENT_CONVEX_HULL] THEN
      SPEC_TAC (([[u:real^2]]), ([[u:real^2]])) THEN REWRITE_TAC [(← HolLight.GSYM SUBSET)] THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC [],
      EXISTS_TAC ([[v:real^2]]) THEN
      MP_TAC (← HolLight.ASSUME ([[v IN segment(a:real^2,c)]])) THEN
      REWRITE_TAC [open_segment, IN_DIFF, IN_INSERT, NOT_IN_EMPTY] THEN
      REWRITE_TAC [DE_MORGAN_THM] THEN STRIP_TAC THEN
      UNDISCH_TAC ([[MEM (v:real^2) (CONS c p)]]) THEN
      ASM_REWRITE_TAC [Session.listDefs.MEM] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC ([[(v:real^2) IN segment[a,c] ]]) THEN
        REWRITE_TAC [SEGMENT_CONVEX_HULL] THEN
        SPEC_TAC (([[v:real^2]]), ([[v:real^2]])) THEN REWRITE_TAC [(← HolLight.GSYM SUBSET)] THEN
        MATCH_MP_TAC HULL_MONO THEN SET_TAC [],
        UNDISCH_TAC ([[collinear {a:real^2, v, c}]]) THEN
        ONCE_REWRITE_TAC [h110] THEN
        ASM_SIMP_TAC [COLLINEAR_3_AFFINE_HULL] THEN
        REWRITE_TAC [AFFINE_HULL_2, IN_ELIM_THM] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [h111] THEN
        ASM_REWRITE_TAC [DOT_RADD, DOT_RMUL, REAL_SUB_REFL] THEN
        ASM_REWRITE_TAC [REAL_MUL_LZERO, REAL_ADD_RID, (← HolLight.GSYM REAL_ADD_RDISTRIB),
                        REAL_MUL_LID]],
      UNDISCH_TAC ([[segment[a:real^2,c] SUBSET segment[u,v] ]]) THEN
      ASM_REWRITE_TAC [SUBSET_SEGMENT]])
  : ExceptT String IO thm).run
#eval POLYGON_CHOP_IN_TWO

/- ------------------------------------------------------------------------- -/
/- Hence the final Pick theorem by induction on number of polygon segments.  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 51
def PICK : thm := keep "PICK" fun _ => (do
  let h40 ← ar (← ExceptT.mk [[SUC(SUC n) = n + 2]])
  let h39 ← sr (← ExceptT.mk [[P a /\ P b
    ==> {x | x IN s UNION {a,b} /\ P x} =
        a INSERT b INSERT {x | x IN s /\ P x}]])
  let h38 ← sr (← ExceptT.mk [[~(a IN s) /\ ~(b IN s) ==> (s UNION {a,b}) DIFF {a,b} = s]])
  let h37 ← rr (← ExceptT.mk [[x = y + &2 ==> &2 * x + &2 = &2 * y + &2 + &2 + &2]])
  let h36 ← sr (← ExceptT.mk [[P a /\ P b /\ a IN q /\ b IN q /\ a IN r /\ b IN r
      ==> (q INTER r) SUBSET {a,b}
          ==> {x | x IN q /\ P x} INTER {x | x IN r /\ P x} = {a,b}]])
  let h35 ← sr (← ExceptT.mk [[s SUBSET inside(q UNION r)
      ==> s = c DIFF {a,b} /\ a IN q /\ b IN q /\ a IN r /\ b IN r /\
          inside(q UNION r) INTER (q UNION r) = {} /\
          P a /\ P b /\ a IN c /\ b IN c
          ==> {x | x IN c /\ P x} INTER {x | x IN q /\ P x} = {a,b} /\
              {x | x IN c /\ P x} INTER {x | x IN r /\ P x} = {a,b}]])
  let h34 ← rr (← ExceptT.mk [[&2 * ab + qr = &2 * x + qab + rab + &2
    ==> ((ab + q) - qab) + ((ab + r) - rab) =
        &2 * x + ((q + r) - qr) + &2]])
  let h33 ← ar (← ExceptT.mk [[x:num <= y ==> x <= y + z]])
  let h32 ← sr (← ExceptT.mk [[{x | x IN (s UNION t) /\ P x} =
    {x | x IN s /\ P x} UNION {x | x IN t /\ P x}]])
  let h31 ← rr (← ExceptT.mk [[q + r = &2 * x + y + &2
    ==> (iq + q / &2 - &1) + (ir + r / &2 - &1) =
        ((iq + ir + x) + y / &2 - &1)]])
  let h30 ← sr (← ExceptT.mk [[inside(s UNION t) INTER (s UNION t) = {}
      ==> {x | x IN inside(s UNION t) INTER (s DIFF ab) /\ P x} = {}]])
  let h29 ← ms [CARD_CLAUSES] (← ExceptT.mk [[s = {} ==> CARD s = 0]])
  let h28 ← sr (← ExceptT.mk [[s UNION segment[a,b] = segment[a,b] UNION s]])
  let h27 ← sr (← ExceptT.mk [[{x | x IN s /\ P x} INTER {x | x IN t /\ P x} =
      {x | x IN (s INTER t) /\ P x}]])
  let h26 ← ar (← ExceptT.mk [[pr = 0 /\ qrp = 0 ==> (q + (r + p) - pr) - qrp = q + r + p]])
  let h25 ← sr (← ExceptT.mk [[s UNION segment[a,b] = segment[a,b] UNION s]])
  let h24 ← sr (← ExceptT.mk [[{x | x IN (s UNION t) /\ P x} =
    {x | x IN s /\ P x} UNION {x | x IN t /\ P x}]])
  let h23 ← sr (← ExceptT.mk [[s SUBSET i
        ==> inside(q UNION r) INTER (q UNION r) = {} /\
            inside(q UNION r) = i /\
            ~(s = {})
            ==> ~((s UNION {a,b}) INTER inside(q UNION r) = {})]])
  let h22 ← sr (← ExceptT.mk [[a IN u /\ b IN u /\ inside(t UNION u) INTER (t UNION u) = {}
        ==> s SUBSET inside(t UNION u)
            ==> u INTER (s UNION {a,b}) = {a,b}]])
  let h21 ← sr (← ExceptT.mk [[a IN t /\ b IN t /\ inside(t UNION u) INTER (t UNION u) = {}
        ==> s SUBSET inside(t UNION u)
            ==> t INTER (s UNION {a,b}) = {a,b}]])
  let h20 ← sr (← ExceptT.mk [[s INTER t SUBSET {a,b} /\
        a IN s /\ b IN s /\ a IN t /\ b IN t
        ==> s INTER t = {a,b}]])
  let h19 ← sr (← ExceptT.mk [[inside(s UNION t) INTER (s UNION t) = {}
      ==> t INTER inside(s UNION t) = {}]])
  let h18 ← sr (← ExceptT.mk [[s SUBSET i
      ==> c INTER i = {}
          ==> (s UNION {a,b}) INTER c SUBSET {a,b}]])
  let h17 ← sr (← ExceptT.mk [[inside(s UNION t) INTER (s UNION t) = {}
      ==> s INTER inside(s UNION t) = {}]])
  let h16 ← sr (← ExceptT.mk [[s SUBSET i
      ==> c INTER i = {}
          ==> (s UNION {a,b}) INTER c SUBSET {b,a}]])
  let h15 ← sr (← ExceptT.mk [[inside(t UNION s') INTER (t UNION s') = {} /\ ~(s = {}) /\ s SUBSET s'
      ==> ~(s SUBSET inside(t UNION s'))]])
  let h14 ← ar (← ExceptT.mk [[3 <= SUC(SUC(SUC n))]])
  let h13 ← sr (← ExceptT.mk [[inside(s' UNION t) INTER (s' UNION t) = {} /\ ~(s = {}) /\ s SUBSET s'
      ==> ~(s SUBSET inside(s' UNION t))]])
  let h12 ← ar (← ExceptT.mk [[3 <= SUC(SUC(SUC n))]])
  let h11 ← sr (← ExceptT.mk [[(a INSERT s) UNION t = a INSERT (s UNION t)]])
  let h10 ← ar (← ExceptT.mk [[2 <= SUC(SUC n)]])
  let h9 ← ar (← ExceptT.mk [[n < SUC n]])
  let h8 ← ar (← ExceptT.mk [[5 <= p ==> 2 <= p]])
  let h7 ← sr (← ExceptT.mk [[a IN s /\ b IN s ==> s UNION {a} = b INSERT s]])
  let h6 ← ar (← ExceptT.mk [[5 <= p ==> 3 <= p]])
  let h5 ← sr (← ExceptT.mk [[s INTER t = t <=> t SUBSET s]])
  let h4 ← sr (← ExceptT.mk [[s INTER t = s <=> s SUBSET t]])
  let h3 ← tt (← ExceptT.mk [[~p ==> p ==> q]])
  let h2 ← ar (← ExceptT.mk [[~(SUC(SUC(SUC(SUC(SUC n)))) <= 4)]])
  let h1 ← ar (← ExceptT.mk [[LENGTH(p:(real^2)list) <= 4 \/ 5 <= LENGTH p]])
  prove ([[!p:(real^2)list.
        (!x. MEM x p ==> integral_vector x) /\
        simple_path (polygonal_path p) /\
        pathfinish (polygonal_path p) = pathstart (polygonal_path p)
        ==> measure(inside(path_image(polygonal_path p))) =
                &(CARD {x | x IN inside(path_image(polygonal_path p)) /\
                            integral_vector x}) +
                &(CARD {x | x IN path_image(polygonal_path p) /\
                            integral_vector x}) / &2 - &1]])
   (GEN_TAC THEN WF_INDUCT_TAC ([[LENGTH(p:(real^2)list)]]) THEN DISJ_CASES_TAC h1 THENL
     [UNDISCH_TAC ([[LENGTH(p:(real^2)list) <= 4]]) THEN
      POP_ASSUM ((fun _ => ALL_TAC)) THEN SPEC_TAC (([[p:(real^2)list]]), ([[p:(real^2)list]])) THEN
      MATCH_MP_TAC list_INDUCT THEN
      REWRITE_TAC [polygonal_path, SIMPLE_PATH_LINEPATH_EQ] THEN
      X_GEN_TAC ([[a:real^2]]) THEN MATCH_MP_TAC list_INDUCT THEN
      REWRITE_TAC [polygonal_path, SIMPLE_PATH_LINEPATH_EQ] THEN
      X_GEN_TAC ([[b:real^2]]) THEN MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
       [REWRITE_TAC [polygonal_path, SIMPLE_PATH_LINEPATH_EQ,
                    PATHSTART_LINEPATH, PATHFINISH_LINEPATH] THEN
        MESON_TAC [],
        ALL_TAC] THEN
      X_GEN_TAC ([[c:real^2]]) THEN MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
       [REPLICATE_TAC 4 (DISCH_THEN ((fun _ => ALL_TAC))) THEN
        REWRITE_TAC [polygonal_path] THEN
        REWRITE_TAC [PATHSTART_JOIN, PATHFINISH_JOIN, PATHSTART_LINEPATH,
                    PATHFINISH_LINEPATH] THEN
        ASM_CASES_TAC ([[c:real^2 = a]]) THEN ASM_REWRITE_TAC [] THEN
        ASM_SIMP_TAC [SIMPLE_PATH_JOIN_LOOP_EQ, PATHSTART_LINEPATH,
                     PATHFINISH_LINEPATH] THEN
        REWRITE_TAC [ARC_LINEPATH_EQ] THEN
        REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        REWRITE_TAC [PATH_IMAGE_LINEPATH] THEN
        SUBST1_TAC (← HolLight.ISPECL [([[b:real^2]]), ([[a:real^2]])] (← HolLight.CONJUNCT1 SEGMENT_SYM)) THEN
        REWRITE_TAC [INTER_IDEMPOT] THEN DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ_ALT] FINITE_SUBSET)) THEN
        ASM_REWRITE_TAC [FINITE_SEGMENT, FINITE_INSERT, FINITE_EMPTY],
        ALL_TAC] THEN
      X_GEN_TAC ([[d:real^2]]) THEN MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
       [REPLICATE_TAC 5 (DISCH_THEN ((fun _ => ALL_TAC))),
        REWRITE_TAC [Session.listDefs.LENGTH, h2]] THEN
      REWRITE_TAC [polygonal_path, PATHSTART_JOIN, PATHFINISH_JOIN] THEN
      REWRITE_TAC [(← HolLight.GSYM IN_SET_OF_LIST), set_of_list] THEN
      REWRITE_TAC [FORALL_IN_INSERT, NOT_IN_EMPTY] THEN
      REWRITE_TAC [PATHSTART_LINEPATH, PATHFINISH_LINEPATH] THEN
      ASM_CASES_TAC ([[d:real^2 = a]]) THEN ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM SUBST1_TAC THEN
      DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
      SIMP_TAC [SIMPLE_PATH_JOIN_LOOP_EQ, PATH_IMAGE_JOIN, PATHSTART_LINEPATH,
        ARC_JOIN_EQ, PATHSTART_JOIN, PATHFINISH_JOIN, PATHFINISH_LINEPATH] THEN
      REWRITE_TAC [PATH_IMAGE_LINEPATH] THEN REWRITE_TAC [INSIDE_OF_TRIANGLE] THEN
      REWRITE_TAC [(← HolLight.GSYM FRONTIER_OF_TRIANGLE)] THEN
      SIMP_TAC [MEASURE_INTERIOR, NEGLIGIBLE_CONVEX_FRONTIER,
               CONVEX_CONVEX_HULL, FINITE_IMP_BOUNDED_CONVEX_HULL,
               FINITE_INSERT, FINITE_EMPTY] THEN
      ASM_SIMP_TAC [PICK_TRIANGLE] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [ARC_LINEPATH_EQ] THEN
      MATCH_MP_TAC h3 THEN REWRITE_TAC [UNION_OVER_INTER] THEN
      REWRITE_TAC [UNION_SUBSET] THEN STRIP_TAC THEN
      SUBGOAL_THEN ([[segment[b:real^2,c] INTER segment [c,a] = segment[b,c] \/
      segment[b,c] INTER segment [c,a] = segment[c,a] \/
      segment[a,b] INTER segment [b,c] = segment[b,c] ]]) (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THENL
       [REWRITE_TAC [h4,
                    h5] THEN
        FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [COLLINEAR_BETWEEN_CASES]) THEN
        REWRITE_TAC [SUBSET_SEGMENT, BETWEEN_IN_SEGMENT, ENDS_IN_SEGMENT] THEN
        REWRITE_TAC [SEGMENT_SYM, DISJ_ACI],
        UNDISCH_TAC ([[segment [b,c] SUBSET {c:real^2}]]),
        UNDISCH_TAC ([[segment [c,a] SUBSET {c:real^2}]]),
        UNDISCH_TAC ([[segment [b,c] SUBSET {a:real^2, b}]])] THEN
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ_ALT] FINITE_SUBSET)) THEN
      ASM_REWRITE_TAC [FINITE_SEGMENT, FINITE_INSERT, FINITE_EMPTY],
      STRIP_TAC] THEN
    MP_TAC (← HolLight.ISPEC ([[p:(real^2)list]]) POLYGON_CHOP_IN_TWO) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [([[a:real^2]]), ([[b:real^2]])] THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[?p':(real^2)list.
        HD p' = a /\
        LENGTH p' = LENGTH p /\
        path_image(polygonal_path p') = path_image(polygonal_path p) /\
        set_of_list p' = set_of_list p /\
        simple_path(polygonal_path p') /\
        pathfinish(polygonal_path p') = pathstart(polygonal_path p')]]) STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC ROTATE_LIST_TO_FRONT_0 THEN
      EXISTS_TAC ([[p:(real^2)list]]) THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [ASM_SIMP_TAC [h6] THEN
        REWRITE_TAC [PATHSTART_POLYGONAL_PATH, PATHFINISH_POLYGONAL_PATH] THEN
        GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [Session.listDefs.LENGTH] THEN
        ASM_ARITH_TAC,
        ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC [([[pathfinish(polygonal_path(p:(real^2)list)) =
       pathstart(polygonal_path p)]]),
        ([[5 <= LENGTH(p:(real^2)list)]])] THEN
      ASM_CASES_TAC ([[p:(real^2)list = [] ]]) THEN
      ASM_REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN
      ASM_REWRITE_TAC [PATHSTART_POLYGONAL_PATH, PATHFINISH_POLYGONAL_PATH] THEN
      DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
      X_GEN_TAC ([[l:(real^2)list]]) THEN
      REWRITE_TAC [Session.listThms2.APPEND_EQ_NIL, Session.listThms1.NOT_CONS_NIL] THEN
      ASM_CASES_TAC ([[l:(real^2)list = [] ]]) THENL
       [ASM_MESON_TAC [Session.listThms1.LENGTH_EQ_NIL], ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (STRIP_ASSUME_TAC o HolLight.GSYM) THEN
      ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN ([[~(TL l:(real^2)list = [])]]) ASSUME_TAC THENL
       [DISCH_THEN (MP_TAC o HolLight.AP_TERM ([[LENGTH:(real^2)list->num]])) THEN
        ASM_SIMP_TAC [Session.listDefs.LENGTH, Session.listThms2.LENGTH_TL] THEN ASM_ARITH_TAC,
        ALL_TAC] THEN
      ASM_SIMP_TAC [Session.listThms2.LAST_APPEND, Session.listThms1.LENGTH_APPEND, Session.listThms2.LENGTH_TL, Session.listThms1.NOT_CONS_NIL] THEN
      ASM_REWRITE_TAC [Session.listDefs.LAST, Session.listThms2.HD_APPEND, Session.listDefs.LENGTH] THEN REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC,
        MATCH_MP_TAC PATH_IMAGE_POLYGONAL_PATH_ROTATE THEN
        ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
        MAP_EVERY UNDISCH_TAC [([[HD(l:(real^2)list) = LAST l]]), ([[5 <= LENGTH(p:(real^2)list)]]),
          ([[~(l:(real^2)list = [])]])] THEN
        ASM_REWRITE_TAC [] THEN
        SPEC_TAC (([[l:(real^2)list]]), ([[l:(real^2)list]])) THEN
        LIST_INDUCT_TAC THEN REWRITE_TAC [Session.listDefs.HD, Session.listDefs.TL, Session.listDefs.APPEND] THEN
        REWRITE_TAC [SET_OF_LIST_APPEND, set_of_list] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC h7 THEN
        ASM_REWRITE_TAC [Session.listDefs.LAST] THEN ONCE_ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [Session.listDefs.LAST] THEN UNDISCH_TAC ([[5 <= LENGTH(CONS (h:real^2) t)]]) THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN
        REWRITE_TAC [IN_SET_OF_LIST, Session.listThms2.MEM_EXISTS_EL, Session.listDefs.LENGTH] THEN
        DISCH_TAC THEN CONJ_TAC THENL
         [EXISTS_TAC ([[0]]) THEN REWRITE_TAC [Session.listDefs.EL] THEN ASM_ARITH_TAC,
          EXISTS_TAC ([[LENGTH(t:(real^2)list) - 1]]) THEN
          ASM_SIMP_TAC [Session.listThms2.LAST_EL] THEN ASM_ARITH_TAC],
        MP_TAC (← HolLight.ISPEC ([[l:(real^2)list]]) SIMPLE_PATH_POLYGONAL_PATH_ROTATE) THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!x:real^2. MEM x p <=> MEM x p']]) (fun th => REWRITE_TAC [th] THEN
                RULE_ASSUM_TAC (HolLight.REWRITE_RULE [th])) THENL [ASM_REWRITE_TAC [(← HolLight.GSYM IN_SET_OF_LIST)], ALL_TAC] THEN
    MAP_EVERY (HolCore.Lib.C UNDISCH_THEN (SUBST_ALL_TAC o HolLight.SYM)) [([[set_of_list(p':(real^2)list) = set_of_list p]]),
      ([[path_image(polygonal_path(p':(real^2)list)) =
     path_image (polygonal_path p)]]),
      ([[LENGTH(p':(real^2)list) = LENGTH(p:(real^2)list)]])] THEN
    MAP_EVERY (HolCore.Lib.C UNDISCH_THEN ((fun _ => ALL_TAC))) [([[simple_path(polygonal_path(p:(real^2)list))]]),
      ([[pathfinish(polygonal_path(p:(real^2)list)) =
     pathstart(polygonal_path p)]])] THEN
    POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist HolLight.CONJ o HolLight.rev) THEN
    SPEC_TAC (([[p':(real^2)list]]), ([[p:(real^2)list]])) THEN
    GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[?q r. 2 <= LENGTH q /\ 2 <= LENGTH r /\
          LENGTH q + LENGTH r = LENGTH p + 1 /\
          set_of_list q UNION set_of_list r = set_of_list p /\
          pathstart(polygonal_path q) = pathstart(polygonal_path p) /\
          pathfinish(polygonal_path q) = (b:real^2) /\
          pathstart(polygonal_path r) = b /\
          pathfinish(polygonal_path r) = pathfinish(polygonal_path p) /\
          simple_path(polygonal_path q ++ polygonal_path r) /\
          path_image(polygonal_path q ++ polygonal_path r) =
          path_image(polygonal_path p)]]) STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN ([[simple_path(polygonal_path p) /\
      2 <= LENGTH p /\ MEM (b:real^2) p /\
      ~(pathstart(polygonal_path p) = b) /\
      ~(pathfinish(polygonal_path p) = b)]]) MP_TAC THENL
       [ASM_SIMP_TAC [h8] THEN
        ASM_REWRITE_TAC [PATHSTART_POLYGONAL_PATH, CONJ_ASSOC] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [Session.listDefs.MEM],
        POP_ASSUM_LIST ((fun _ => ALL_TAC))] THEN
      WF_INDUCT_TAC ([[LENGTH(p:(real^2)list)]]) THEN POP_ASSUM MP_TAC THEN
      SPEC_TAC (([[p:(real^2)list]]), ([[p:(real^2)list]])) THEN
      MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN
      X_GEN_TAC ([[a:real^2]]) THEN
      MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN
      X_GEN_TAC ([[x:real^2]]) THEN
      MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
       [REWRITE_TAC [polygonal_path, PATHSTART_LINEPATH, PATHFINISH_LINEPATH,
                    Session.listDefs.MEM] THEN
        MESON_TAC [],
        REWRITE_TAC [Session.listDefs.LENGTH, ARITH]] THEN
      MAP_EVERY X_GEN_TAC [([[y:real^2]]), ([[l:(real^2)list]])] THEN
      REPLICATE_TAC 3 (DISCH_THEN ((fun _ => ALL_TAC))) THEN DISCH_TAC THEN
      REWRITE_TAC [polygonal_path] THEN
      REWRITE_TAC [PATHSTART_JOIN, PATHFINISH_JOIN] THEN
      REWRITE_TAC [PATHSTART_LINEPATH, PATHFINISH_LINEPATH] THEN
      ONCE_REWRITE_TAC [Session.listDefs.MEM] THEN
      ASM_CASES_TAC ([[a:real^2 = b]]) THEN ASM_REWRITE_TAC [] THEN
      ONCE_REWRITE_TAC [Session.listDefs.MEM] THEN
      ASM_CASES_TAC ([[x:real^2 = b]]) THEN ASM_REWRITE_TAC [] THENL
       [FIRST_X_ASSUM (fun (th : thm) => if Hol100.CheckPred.holds HolCore.Basics.is_forall (concl th) then ALL_TAC else FAIL_TAC "check") THEN STRIP_TAC THEN
        EXISTS_TAC ([[[a:real^2;b] ]]) THEN
        EXISTS_TAC ([[CONS (b:real^2) (CONS y l)]]) THEN
        ASM_REWRITE_TAC [polygonal_path, Session.listDefs.LENGTH] THEN
        REWRITE_TAC [PATHSTART_POLYGONAL_PATH, Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD] THEN
        REWRITE_TAC [PATHSTART_LINEPATH, PATHFINISH_LINEPATH] THEN
        REPEAT (CONJ_TAC THENL [ARITH_TAC, ALL_TAC]) THEN
        REWRITE_TAC [set_of_list] THEN SET_TAC [],
        ALL_TAC] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[CONS (x:real^2) (CONS y l)]])) THEN
      REWRITE_TAC [Session.listDefs.LENGTH, h9] THEN ANTS_TAC THENL
       [REWRITE_TAC [h10] THEN
        ONCE_REWRITE_TAC [Session.listDefs.MEM] THEN ASM_REWRITE_TAC [] THEN
        FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] SIMPLE_PATH_JOIN_IMP)) THEN
        ASM_REWRITE_TAC [PATHSTART_POLYGONAL_PATH, Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD] THEN
        SIMP_TAC [PATHFINISH_LINEPATH, ARC_IMP_SIMPLE_PATH],
        ALL_TAC] THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[q:(real^2)list]]), ([[r:(real^2)list]])] THEN
      STRIP_TAC THEN MAP_EVERY EXISTS_TAC [([[CONS (a:real^2) q]]), ([[r:(real^2)list]])] THEN
      ASM_REWRITE_TAC [Session.listDefs.LENGTH, Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD] THEN
      REPLICATE_TAC 2 (CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC]) THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC [set_of_list, h11],
        ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC [PATHSTART_POLYGONAL_PATH, Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD],
        ALL_TAC] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC ([[pathfinish(polygonal_path q) = (b:real^2)]]) THEN
        REWRITE_TAC [PATHFINISH_POLYGONAL_PATH, Session.listDefs.LAST, Session.listThms1.NOT_CONS_NIL] THEN
        UNDISCH_TAC ([[2 <= LENGTH(q:(real^2)list)]]) THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [Session.listDefs.LENGTH, ARITH],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[polygonal_path(CONS (a:real^2) q) =
      linepath(a,x) ++ polygonal_path q]]) SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [([[pathstart(polygonal_path q) =
         pathstart(polygonal_path (CONS (x:real^2) (CONS y l)))]]),
          ([[2 <= LENGTH(q:(real^2)list)]])] THEN
        SPEC_TAC (([[q:(real^2)list]]), ([[q:(real^2)list]])) THEN
        POP_ASSUM_LIST ((fun _ => ALL_TAC)) THEN
        MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN
        GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
        REWRITE_TAC [Session.listDefs.LENGTH, ARITH, polygonal_path] THEN
        SIMP_TAC [PATHSTART_POLYGONAL_PATH, Session.listDefs.HD, Session.listThms1.NOT_CONS_NIL],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[pathstart(polygonal_path(CONS x (CONS y l))) = (x:real^2)]]) (fun th => SUBST_ALL_TAC th THEN ASSUME_TAC th) THENL
       [REWRITE_TAC [PATHSTART_POLYGONAL_PATH, Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD], ALL_TAC] THEN
      CONJ_TAC THENL
       [HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
            let x1 ← ExceptT.mk (HolLight.PART_MATCH (HolCore.Kernel.rand o HolCore.Kernel.rand) SIMPLE_PATH_ASSOC w)
            pure (MP_TAC x1)) THEN
        ASM_REWRITE_TAC [PATHSTART_LINEPATH, PATHFINISH_LINEPATH] THEN
        REWRITE_TAC [PATHSTART_POLYGONAL_PATH, Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD] THEN
        DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN
        UNDISCH_TAC ([[simple_path(linepath(a:real^2,x) ++
                               polygonal_path (CONS x (CONS y l)))]]) THEN
        ASM_CASES_TAC ([[pathfinish(polygonal_path r) = (a:real^2)]]) THENL
         [SUBGOAL_THEN ([[pathfinish(polygonal_path(CONS (x:real^2) (CONS y l))) = a]]) ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
          ASM_SIMP_TAC [SIMPLE_PATH_JOIN_LOOP_EQ, PATHFINISH_LINEPATH,
                       PATHSTART_JOIN, PATHFINISH_JOIN, PATHSTART_LINEPATH] THEN
          STRIP_TAC THEN MATCH_MP_TAC SIMPLE_PATH_IMP_ARC THEN
          ASM_REWRITE_TAC [PATHSTART_JOIN, PATHFINISH_JOIN] THEN
          ASM_MESON_TAC [ARC_LINEPATH_EQ],
          SUBGOAL_THEN ([[~(pathfinish(polygonal_path(CONS (x:real^2) (CONS y l))) = a)]]) ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
          ASM_SIMP_TAC [SIMPLE_PATH_EQ_ARC, PATHSTART_JOIN, PATHSTART_LINEPATH,
                       PATHFINISH_JOIN] THEN
          ASM_SIMP_TAC [ARC_JOIN_EQ, PATHFINISH_LINEPATH, PATHSTART_JOIN] THEN
          REWRITE_TAC [ARC_LINEPATH_EQ] THEN STRIP_TAC THEN
          SUBGOAL_THEN ([[arc(polygonal_path q ++ polygonal_path r:real^1->real^2)]]) MP_TAC THENL
           [ALL_TAC,
            ASM_SIMP_TAC [ARC_JOIN_EQ, PATHFINISH_LINEPATH, PATHSTART_JOIN]] THEN
          MATCH_MP_TAC SIMPLE_PATH_IMP_ARC THEN
          ASM_REWRITE_TAC [PATHSTART_JOIN, PATHFINISH_JOIN] THEN
          FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP ARC_DISTINCT_ENDS) THEN
          REWRITE_TAC [PATHSTART_POLYGONAL_PATH, Session.listDefs.HD, Session.listThms1.NOT_CONS_NIL]],
        ASM_SIMP_TAC [PATH_IMAGE_JOIN, PATHFINISH_JOIN, PATHFINISH_LINEPATH] THEN
        SIMP_TAC [PATH_IMAGE_JOIN, PATHFINISH_LINEPATH, Session.listThms1.NOT_CONS_NIL, Session.listDefs.HD,
                 PATHSTART_POLYGONAL_PATH] THEN
        UNDISCH_THEN ([[path_image(polygonal_path q ++ polygonal_path r) =
        path_image(polygonal_path(CONS (x:real^2) (CONS y l)))]]) (SUBST1_TAC o HolLight.SYM) THEN
        ASM_SIMP_TAC [PATH_IMAGE_JOIN, PATHFINISH_JOIN, PATHFINISH_LINEPATH] THEN
        SET_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[pathstart(polygonal_path p) = (a:real^2)]]) SUBST_ALL_TAC THENL
     [UNDISCH_TAC ([[5 <= LENGTH(p:(real^2)list)]]) THEN
      REWRITE_TAC [PATHSTART_POLYGONAL_PATH] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [Session.listDefs.LENGTH, ARITH],
      ALL_TAC] THEN
    UNDISCH_THEN ([[pathfinish (polygonal_path p) = (a:real^2)]]) SUBST_ALL_TAC THEN
    UNDISCH_THEN ([[path_image(polygonal_path q ++ polygonal_path r):real^2->bool =
                path_image(polygonal_path p)]]) (SUBST_ALL_TAC o HolLight.SYM) THEN
    SUBGOAL_THEN ([[(!x:real^2. MEM x q ==> integral_vector x) /\
    (!x:real^2. MEM x r ==> integral_vector x)]]) STRIP_ASSUME_TAC THENL
     [REWRITE_TAC [(← HolLight.GSYM IN_SET_OF_LIST)] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [(← HolLight.GSYM IN_SET_OF_LIST), IN_UNION] THEN
      UNDISCH_THEN ([[(set_of_list q UNION set_of_list r):real^2->bool = set_of_list p]]) (SUBST_ALL_TAC o HolLight.SYM) THEN
      ASM_REWRITE_TAC [IN_UNION],
      ALL_TAC] THEN
    ABBREV_TAC ([[n = LENGTH(p:(real^2)list)]]) THEN
    SUBGOAL_THEN ([[integral_vector(a:real^2) /\ integral_vector(b:real^2)]]) STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    MAP_EVERY (HolCore.Lib.C UNDISCH_THEN ((fun _ => ALL_TAC))) [([[!x:real^2. MEM x p ==> integral_vector x]]),
      ([[MEM (a:real^2) p]]),
      ([[MEM (b:real^2) p]]),
      ([[HD p = (a:real^2)]]),
      ([[(set_of_list q UNION set_of_list r):real^2->bool = set_of_list p]]),
      ([[simple_path(polygonal_path p :real^1->real^2)]])] THEN
    SUBGOAL_THEN ([[3 <= LENGTH(q:(real^2)list)]]) ASSUME_TAC THENL
     [REPEAT (FIRST_X_ASSUM (fun (th : thm) => if Hol100.CheckPred.holds HolCore.Basics.is_forall (concl th) then ALL_TAC else FAIL_TAC "check")) THEN
      REPEAT (POP_ASSUM MP_TAC) THEN
      SPEC_TAC (([[q:(real^2)list]]), ([[q:(real^2)list]])) THEN
      MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN
      X_GEN_TAC ([[a0:real^2]]) THEN
      MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN
      X_GEN_TAC ([[a1:real^2]]) THEN MATCH_MP_TAC list_INDUCT THEN
      REWRITE_TAC [Session.listDefs.LENGTH, ARITH, h12] THEN
      REWRITE_TAC [polygonal_path, PATHSTART_LINEPATH, PATHFINISH_LINEPATH] THEN
      REPEAT STRIP_TAC THEN
      UNDISCH_THEN ([[a0:real^2 = a]]) SUBST_ALL_TAC THEN
      UNDISCH_THEN ([[a1:real^2 = b]]) SUBST_ALL_TAC THEN
      UNDISCH_TAC ([[segment(a:real^2,b) SUBSET
                 inside(path_image(linepath(a,b) ++ polygonal_path r))]]) THEN
      ASM_SIMP_TAC [PATH_IMAGE_JOIN, PATH_IMAGE_LINEPATH, PATHFINISH_LINEPATH] THEN
      MATCH_MP_TAC h13 THEN
      REWRITE_TAC [INSIDE_NO_OVERLAP] THEN
      ASM_REWRITE_TAC [SEGMENT_OPEN_SUBSET_CLOSED, SEGMENT_EQ_EMPTY],
      UNDISCH_THEN ([[2 <= LENGTH(q:(real^2)list)]]) ((fun _ => ALL_TAC))] THEN
    SUBGOAL_THEN ([[3 <= LENGTH(r:(real^2)list)]]) ASSUME_TAC THENL
     [REPEAT (FIRST_X_ASSUM (fun (th : thm) => if Hol100.CheckPred.holds HolCore.Basics.is_forall (concl th) then ALL_TAC else FAIL_TAC "check")) THEN
      REPEAT (POP_ASSUM MP_TAC) THEN
      SPEC_TAC (([[r:(real^2)list]]), ([[r:(real^2)list]])) THEN
      MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN
      X_GEN_TAC ([[a0:real^2]]) THEN
      MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN
      X_GEN_TAC ([[a1:real^2]]) THEN MATCH_MP_TAC list_INDUCT THEN
      REWRITE_TAC [Session.listDefs.LENGTH, ARITH, h14] THEN
      REWRITE_TAC [polygonal_path, PATHSTART_LINEPATH, PATHFINISH_LINEPATH] THEN
      REPEAT STRIP_TAC THEN
      UNDISCH_THEN ([[a0:real^2 = b]]) SUBST_ALL_TAC THEN
      UNDISCH_THEN ([[a1:real^2 = a]]) SUBST_ALL_TAC THEN
      UNDISCH_TAC ([[segment(a:real^2,b) SUBSET
                 inside(path_image(polygonal_path q ++ linepath(b,a)))]]) THEN
      ASM_SIMP_TAC [PATH_IMAGE_JOIN, PATH_IMAGE_LINEPATH, PATHSTART_LINEPATH] THEN
      ONCE_REWRITE_TAC [(← HolLight.CONJUNCT1 SEGMENT_SYM)] THEN
      MATCH_MP_TAC h15 THEN
      REWRITE_TAC [INSIDE_NO_OVERLAP] THEN
      ASM_REWRITE_TAC [SEGMENT_OPEN_SUBSET_CLOSED, SEGMENT_EQ_EMPTY],
      UNDISCH_THEN ([[2 <= LENGTH(r:(real^2)list)]]) ((fun _ => ALL_TAC))] THEN
    FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.ISPEC ([[CONS (a:real^2) r]]) th) THEN
      MP_TAC (← HolLight.ISPEC ([[CONS (b:real^2) q]]) th))) THEN
    REWRITE_TAC [Session.listDefs.LENGTH] THEN ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
    SUBGOAL_THEN ([[polygonal_path(CONS (b:real^2) q) = linepath(b,a) ++ polygonal_path q]]) SUBST_ALL_TAC THENL
     [POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist HolLight.CONJ) THEN
      SPEC_TAC (([[q:(real^2)list]]), ([[q:(real^2)list]])) THEN
      MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN
      GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
      REWRITE_TAC [Session.listDefs.LENGTH, ARITH, polygonal_path] THEN
      SIMP_TAC [PATHSTART_POLYGONAL_PATH, Session.listDefs.HD, Session.listThms1.NOT_CONS_NIL],
      ALL_TAC] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [Session.listDefs.MEM, PATHSTART_JOIN, PATHFINISH_JOIN] THEN
      CONJ_TAC THENL [ASM_MESON_TAC [], REWRITE_TAC [PATHSTART_LINEPATH]] THEN
      UNDISCH_TAC ([[simple_path(polygonal_path q ++ polygonal_path r :real^1->real^2)]]) THEN
      ASM_SIMP_TAC [SIMPLE_PATH_JOIN_LOOP_EQ, PATHSTART_LINEPATH,
                   PATHFINISH_LINEPATH, ARC_LINEPATH_EQ] THEN
      STRIP_TAC THEN REWRITE_TAC [PATH_IMAGE_LINEPATH] THEN
      ONCE_REWRITE_TAC [SEGMENT_SYM] THEN
      REWRITE_TAC [SEGMENT_CLOSED_OPEN] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h16) THEN
      ASM_SIMP_TAC [PATH_IMAGE_JOIN] THEN
      MATCH_MP_TAC h17 THEN
      REWRITE_TAC [INSIDE_NO_OVERLAP],
      STRIP_TAC] THEN
    REWRITE_TAC [Session.listDefs.LENGTH] THEN ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
    SUBGOAL_THEN ([[polygonal_path(CONS (a:real^2) r) = linepath(a,b) ++ polygonal_path r]]) SUBST_ALL_TAC THENL
     [POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist HolLight.CONJ) THEN
      SPEC_TAC (([[r:(real^2)list]]), ([[r:(real^2)list]])) THEN
      MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [Session.listDefs.LENGTH, ARITH] THEN
      GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
      REWRITE_TAC [Session.listDefs.LENGTH, ARITH, polygonal_path] THEN
      SIMP_TAC [PATHSTART_POLYGONAL_PATH, Session.listDefs.HD, Session.listThms1.NOT_CONS_NIL],
      ALL_TAC] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [Session.listDefs.MEM, PATHSTART_JOIN, PATHFINISH_JOIN] THEN
      CONJ_TAC THENL [ASM_MESON_TAC [], REWRITE_TAC [PATHSTART_LINEPATH]] THEN
      UNDISCH_TAC ([[simple_path(polygonal_path q ++ polygonal_path r :real^1->real^2)]]) THEN
      ASM_SIMP_TAC [SIMPLE_PATH_JOIN_LOOP_EQ, PATHSTART_LINEPATH,
                   PATHFINISH_LINEPATH, ARC_LINEPATH_EQ] THEN
      STRIP_TAC THEN REWRITE_TAC [PATH_IMAGE_LINEPATH] THEN
      REWRITE_TAC [SEGMENT_CLOSED_OPEN] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h18) THEN
      ASM_SIMP_TAC [PATH_IMAGE_JOIN] THEN
      MATCH_MP_TAC h19 THEN
      REWRITE_TAC [INSIDE_NO_OVERLAP],
      STRIP_TAC] THEN
    MP_TAC (← HolLight.ISPECL [([[polygonal_path q:real^1->real^2]]),
                   ([[reversepath(polygonal_path r):real^1->real^2]]),
                   ([[linepath(a:real^2,b)]]), ([[a:real^2]]), ([[b:real^2]])] SPLIT_INSIDE_SIMPLE_CLOSED_CURVE) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC [PATHSTART_LINEPATH, PATHFINISH_LINEPATH,
                      PATHSTART_REVERSEPATH, PATHFINISH_REVERSEPATH,
                      SIMPLE_PATH_LINEPATH_EQ] THEN
      UNDISCH_TAC ([[simple_path(polygonal_path q ++ polygonal_path r :real^1->real^2)]]) THEN
      ASM_SIMP_TAC [SIMPLE_PATH_JOIN_LOOP_EQ, PATH_IMAGE_LINEPATH] THEN
      ASM_SIMP_TAC [PATH_IMAGE_REVERSEPATH, ARC_IMP_SIMPLE_PATH,
       SIMPLE_PATH_REVERSEPATH] THEN
      STRIP_TAC THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC h20 THEN
        ASM_MESON_TAC [PATHSTART_IN_PATH_IMAGE, PATHFINISH_IN_PATH_IMAGE],
        REWRITE_TAC [SEGMENT_CLOSED_OPEN] THEN
        UNDISCH_TAC ([[segment(a:real^2,b) SUBSET
        inside(path_image(polygonal_path q ++ polygonal_path r))]]) THEN
        ASM_SIMP_TAC [PATH_IMAGE_JOIN] THEN MATCH_MP_TAC h21 THEN
        REWRITE_TAC [INSIDE_NO_OVERLAP] THEN
        ASM_MESON_TAC [PATHSTART_IN_PATH_IMAGE, PATHFINISH_IN_PATH_IMAGE],
        REWRITE_TAC [SEGMENT_CLOSED_OPEN] THEN
        UNDISCH_TAC ([[segment(a:real^2,b) SUBSET
        inside(path_image(polygonal_path q ++ polygonal_path r))]]) THEN
        ASM_SIMP_TAC [PATH_IMAGE_JOIN] THEN MATCH_MP_TAC h22 THEN
        REWRITE_TAC [INSIDE_NO_OVERLAP] THEN
        ASM_MESON_TAC [PATHSTART_IN_PATH_IMAGE, PATHFINISH_IN_PATH_IMAGE],
        REWRITE_TAC [SEGMENT_CLOSED_OPEN] THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h23) THEN
        ASM_REWRITE_TAC [INSIDE_NO_OVERLAP, SEGMENT_EQ_EMPTY] THEN
        ASM_SIMP_TAC [PATH_IMAGE_JOIN]],
      ALL_TAC] THEN
    REPEAT (FIRST_X_ASSUM (fun (th : thm) => HolLight.tactic_of do
        let q ← ExceptT.mk [[measure:(real^2->bool)->real]]
        pure (if HolCore.Basics.free_in q (concl th) then MP_TAC th else FAIL_TAC "check"))) THEN
    UNDISCH_TAC ([[segment(a:real^2,b) SUBSET
    inside(path_image (polygonal_path q ++ polygonal_path r))]]) THEN
    ASM_SIMP_TAC [PATH_IMAGE_JOIN, PATHSTART_LINEPATH, PATHFINISH_LINEPATH] THEN
    REWRITE_TAC [PATH_IMAGE_REVERSEPATH, PATH_IMAGE_LINEPATH] THEN
    SUBST1_TAC (← HolLight.ISPECL [([[b:real^2]]), ([[a:real^2]])] (← HolLight.CONJUNCT1 SEGMENT_SYM)) THEN
    REPEAT STRIP_TAC THEN SUBST1_TAC (← HolLight.SYM (← HolLight.ASSUME ([[inside(path_image(polygonal_path q) UNION segment [a,b]) UNION
    inside(path_image(polygonal_path r) UNION segment [a,b]) UNION
    (segment [a:real^2,b] DIFF {a, b}) =
    inside
     (path_image(polygonal_path q) UNION path_image(polygonal_path r))]]))) THEN
    REWRITE_TAC [h24] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC ([[measure(inside(path_image(polygonal_path q) UNION segment[a:real^2,b])) +
    measure(inside(path_image (polygonal_path r) UNION segment [a,b]) UNION
            segment [a,b] DIFF {a, b})]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MEASURE_NEGLIGIBLE_UNION THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MEASURABLE_INSIDE THEN
        MATCH_MP_TAC COMPACT_UNION THEN
        SIMP_TAC [COMPACT_PATH_IMAGE, COMPACT_SEGMENT, PATH_POLYGONAL_PATH],
        MATCH_MP_TAC MEASURABLE_UNION THEN CONJ_TAC THENL
         [MATCH_MP_TAC MEASURABLE_INSIDE THEN
          MATCH_MP_TAC COMPACT_UNION THEN
          SIMP_TAC [COMPACT_PATH_IMAGE, COMPACT_SEGMENT, PATH_POLYGONAL_PATH],
          MATCH_MP_TAC MEASURABLE_DIFF THEN CONJ_TAC THEN
          MATCH_MP_TAC MEASURABLE_COMPACT THEN REWRITE_TAC [COMPACT_SEGMENT] THEN
          MATCH_MP_TAC FINITE_IMP_COMPACT THEN
          REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY]],
        ASM_REWRITE_TAC [UNION_OVER_INTER, UNION_EMPTY] THEN
        MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC ([[segment[a:real^2,b] ]]) THEN
        REWRITE_TAC [NEGLIGIBLE_SEGMENT_2] THEN SET_TAC []],
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC ([[measure(inside(path_image(polygonal_path q) UNION segment[a:real^2,b])) +
    measure(inside(path_image(polygonal_path r) UNION segment[a,b]))]]) THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN MATCH_MP_TAC MEASURE_NEGLIGIBLE_SYMDIFF THEN
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC ([[segment[a:real^2,b] ]]) THEN
      REWRITE_TAC [NEGLIGIBLE_SEGMENT_2] THEN SET_TAC [],
      ALL_TAC] THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_ADD)] THEN
    ONCE_REWRITE_TAC [h25] THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN ([[CARD({x | x IN inside(segment[a,b] UNION path_image(polygonal_path q)) /\
              integral_vector x} UNION
         {x | x IN inside(segment[a,b] UNION path_image(polygonal_path r)) /\
              integral_vector x} UNION
         {x | x IN segment[a,b] DIFF {a, b} /\ integral_vector x}) =
    CARD {x | x IN inside(segment[a,b] UNION path_image(polygonal_path q)) /\
              integral_vector x} +
    CARD {x | x IN inside(segment[a,b] UNION path_image(polygonal_path r)) /\
              integral_vector x} +
    CARD {x:real^2 | x IN segment[a,b] DIFF {a, b} /\ integral_vector x}]]) SUBST1_TAC THENL
     [(gsimp 5) [CARD_UNION_GEN, FINITE_BOUNDED_INTEGER_POINTS, FINITE_UNION,
        BOUNDED_INSIDE, BOUNDED_UNION, BOUNDED_SEGMENT,
        BOUNDED_PATH_IMAGE, BOUNDED_DIFF, PATH_POLYGONAL_PATH] THEN
      MATCH_MP_TAC h26 THEN
      REWRITE_TAC [UNION_OVER_INTER] THEN
      REWRITE_TAC [h27] THEN
      RULE_ASSUM_TAC (HolLight.ONCE_REWRITE_RULE [h28]) THEN
      ASM_REWRITE_TAC [NOT_IN_EMPTY, EMPTY_GSPEC, UNION_EMPTY] THEN CONJ_TAC THEN
      MATCH_MP_TAC h29 THEN
      MATCH_MP_TAC h30 THEN
      REWRITE_TAC [INSIDE_NO_OVERLAP],
      ALL_TAC] THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_ADD)] THEN MATCH_MP_TAC h31 THEN
    REWRITE_TAC [h32] THEN
    (gsimp 5) [CARD_UNION_GEN, FINITE_BOUNDED_INTEGER_POINTS, BOUNDED_SEGMENT,
      BOUNDED_PATH_IMAGE, PATH_POLYGONAL_PATH, (← HolLight.GSYM REAL_OF_NUM_SUB),
      INTER_SUBSET, CARD_SUBSET, h33] THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_ADD)] THEN MATCH_MP_TAC h34 THEN
    SUBGOAL_THEN ([[{x | x IN segment[a,b] /\ integral_vector x} INTER
    {x | x IN path_image(polygonal_path q) /\ integral_vector x} = {a,b} /\
    {x:real^2 | x IN segment[a,b] /\ integral_vector x} INTER
    {x | x IN path_image(polygonal_path r) /\ integral_vector x} = {a,b}]]) (CONJUNCTS_THEN SUBST1_TAC) THENL
     [FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h35) THEN
      ASM_REWRITE_TAC [open_segment, INSIDE_NO_OVERLAP, ENDS_IN_SEGMENT] THEN
      ASM_MESON_TAC [PATHSTART_IN_PATH_IMAGE, PATHFINISH_IN_PATH_IMAGE],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[{x:real^2 | x IN path_image(polygonal_path q) /\ integral_vector x} INTER
    {x | x IN path_image(polygonal_path r) /\ integral_vector x} = {a,b}]]) SUBST1_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] SIMPLE_PATH_JOIN_IMP)) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (HolCore.Lib.last (α := thm)) o HolLight.CONJUNCTS) THEN
      MATCH_MP_TAC h36 THEN
      ASM_MESON_TAC [PATHSTART_IN_PATH_IMAGE, PATHFINISH_IN_PATH_IMAGE],
      ALL_TAC] THEN
    SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY] THEN
    ASM_REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC h37 THEN
    REWRITE_TAC [SEGMENT_CLOSED_OPEN] THEN
    SUBGOAL_THEN ([[(segment(a,b) UNION {a, b}) DIFF {a, b} = segment(a:real^2,b)]]) SUBST1_TAC THENL
     [MATCH_MP_TAC h38 THEN
      REWRITE_TAC [open_segment, IN_DIFF] THEN SET_TAC [],
      ALL_TAC] THEN
    ASM_SIMP_TAC [h39] THEN
    SIMP_TAC [CARD_CLAUSES, FINITE_BOUNDED_INTEGER_POINTS,
             BOUNDED_SEGMENT, FINITE_INSERT] THEN
    ASM_REWRITE_TAC [IN_INSERT, IN_ELIM_THM, ENDS_NOT_IN_SEGMENT] THEN
    REWRITE_TAC [REAL_OF_NUM_ADD, h40])
  : ExceptT String IO thm).run
#eval PICK

end Hol100.Pick
