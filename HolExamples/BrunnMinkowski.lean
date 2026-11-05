/- File: HolExamples/BrunnMinkowski.lean
Translation of HOL Light's Examples/brunn_minkowski.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolExamples.Common
import SessionMultiLib.RealAnalysis
open HolCore.Kernel Session HolLight.Syntax HolExamples
open SessionLibrary.Card SessionLibrary.Floor SessionLibrary.Products
open SessionMultiLib.Misc SessionMultiLib.Vectors SessionMultiLib.Determinants
open SessionMultiLib.Metric SessionMultiLib.Topology SessionMultiLib.Convex
open SessionMultiLib.Integration SessionMultiLib.Measure SessionMultiLib.Transcendentals
open SessionMultiLib.RealAnalysis
namespace HolExamples.BrunnMinkowski

/- Helpers: the session's `prove` lifted into `ExceptT String IO`, so tactic
   scripts read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)
private def rf (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_FIELD tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)
private def sr (tm : term) : ExceptT String IO thm := ExceptT.mk (SET_RULE tm)
private def va (tm : term) : ExceptT String IO thm := ExceptT.mk (VECTOR_ARITH tm)
private def na (tm : term) : ExceptT String IO thm := ExceptT.mk (NORM_ARITH tm)
private def ms (ths : List thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (MESON ths tm)
/- `ttac o check p o concl`: apply `ttac` to a theorem whose conclusion
   satisfies `p`, otherwise fail. -/
private def ifConcl (p : term → Bool) (ttac : thm → HolCore.Tactics.tactic) :
    thm → HolCore.Tactics.tactic :=
  fun th g => if p (concl th) then ttac th g else return .error "check"

-- ========================================================================= --
-- Brunn-Minkowski theorem and related results.                              --
-- ========================================================================= --

#eval phrase 1
-- needs "Multivariate/realanalysis.ml";;
#eval SessionMultiLib.RealAnalysis.ensureRealAnalysis

-- ------------------------------------------------------------------------- --
-- First, the special case of a box.                                         --
-- ------------------------------------------------------------------------- --

#eval phrase 2
def BRUNN_MINKOWSKI_INTERVAL : thm := keep "BRUNN_MINKOWSKI_INTERVAL" fun _ => (do
  -- OCaml builds the tactic right to left: the build-time rules run
  -- bottom-first, so their traces print in that order.
  let h5 ← rf
    (← ExceptT.mk [[a < b /\ c < d
    ==> (b - a) * inv((b + d) - (a + c)) +
    (d - c) * inv((b + d) - (a + c)) = &1]])
  let h4 ← rr (← ExceptT.mk [[a < b /\ c < d ==> &0 < (b + d) - (a + c)]])
  let h3 ← rr (← ExceptT.mk [[a <= b /\ c <= d ==> a + c <= b + d]])
  let h2 ← rr (← ExceptT.mk [[a <= b /\ c <= d ==> a + c <= b + d]])
  let h1 ← rr (← ExceptT.mk [[a <= b /\ c <= d ==> a + c <= b + d]])
  prove ([[!a b c d:real^N.
    ~(interval[a,b] = {}) /\ ~(interval[c,d] = {})
    ==> root (dimindex(:N))
             (measure {x + y | x IN interval[a,b] /\ y IN interval[c,d]})
        >= root (dimindex(:N)) (measure(interval[a,b])) +
           root (dimindex(:N)) (measure(interval[c,d]))]])
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [SUMS_INTERVALS, real_ge] THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [INTERVAL_NE_EMPTY]) THEN
    ASM_CASES_TAC ([[measure(interval[a:real^N,b]) = &0]]) THENL
     [ASM_SIMP_TAC [ROOT_0, DIMINDEX_GE_1, LE_1, REAL_ADD_LID,
                   ROOT_MONO_LE_EQ, MEASURE_POS_LE, MEASURABLE_INTERVAL] THEN
      ASM_SIMP_TAC [MEASURE_INTERVAL, CONTENT_CLOSED_INTERVAL,
                   VECTOR_ADD_COMPONENT,
                   h1] THEN
      MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN
      X_GEN_TAC ([[i:num]]) THEN DISCH_TAC THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[i:num]]))) THEN
      ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC2,
      FIRST_X_ASSUM (ifConcl HolCore.Basics.is_neg MP_TAC) THEN
      SIMP_TAC [MEASURABLE_MEASURE_EQ_0, MEASURABLE_INTERVAL] THEN
      REWRITE_TAC [NEGLIGIBLE_INTERVAL, INTERVAL_NE_EMPTY] THEN STRIP_TAC] THEN
    ASM_CASES_TAC ([[measure(interval[c:real^N,d]) = &0]]) THENL
     [ASM_SIMP_TAC [ROOT_0, DIMINDEX_GE_1, LE_1, REAL_ADD_RID,
                   ROOT_MONO_LE_EQ, MEASURE_POS_LE, MEASURABLE_INTERVAL] THEN
      ASM_SIMP_TAC [MEASURE_INTERVAL, CONTENT_CLOSED_INTERVAL,
                   VECTOR_ADD_COMPONENT,
                   h2] THEN
      MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN
      X_GEN_TAC ([[i:num]]) THEN DISCH_TAC THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[i:num]]))) THEN
      ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC2,
      FIRST_X_ASSUM (ifConcl HolCore.Basics.is_neg MP_TAC) THEN
      SIMP_TAC [MEASURABLE_MEASURE_EQ_0, MEASURABLE_INTERVAL] THEN
      REWRITE_TAC [NEGLIGIBLE_INTERVAL, INTERVAL_NE_EMPTY] THEN STRIP_TAC] THEN
    ASM_SIMP_TAC [MEASURE_INTERVAL, CONTENT_CLOSED_INTERVAL, VECTOR_ADD_COMPONENT,
                 h3] THEN
    GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.GSYM REAL_MUL_LID)] THEN
    HolCore.Lib.W (MP_TAC o HolLight.PART_MATCH (HolCore.Kernel.rand o HolCore.Kernel.rand)
      REAL_LE_LDIV_EQ o HolLight.snd) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC ROOT_POS_LT THEN
      ASM_SIMP_TAC [(← HolLight.GSYM REAL_LE_LDIV_EQ), PRODUCT_POS_LT_NUMSEG, IN_NUMSEG,
                   h4,
                   DIMINDEX_GE_1, LE_1],
      DISCH_THEN (SUBST1_TAC o HolLight.SYM)] THEN
    REWRITE_TAC [real_div, REAL_ADD_RDISTRIB] THEN REWRITE_TAC [(← HolLight.GSYM real_div)] THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_ROOT_DIV)] THEN
    REWRITE_TAC [(← HolLight.GSYM PRODUCT_DIV_NUMSEG)] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     ([[sum (1..dimindex(:N))
          (\i. ((b:real^N)$i - (a:real^N)$i) /
               ((b$i + d$i) - (a$i + c$i))) / &(dimindex(:N)) +
      sum (1..dimindex(:N))
          (\i. ((d:real^N)$i - (c:real^N)$i) /
               ((b$i + d$i) - (a$i + c$i))) / &(dimindex(:N))]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
      HolCore.Lib.W (MP_TAC o HolLight.PART_MATCH (HolCore.Equal.lhand o HolCore.Kernel.rand)
        REAL_ROOT_LE o HolLight.snd) THEN
      (ANTS_TAC THENL
        [SIMP_TAC [REAL_OF_NUM_LT, REAL_OF_NUM_EQ, DIMINDEX_GE_1, LE_1,
                  REAL_LE_RDIV_EQ, REAL_MUL_LZERO] THEN
         MATCH_MP_TAC SUM_POS_LE_NUMSEG,
         DISCH_THEN SUBST1_TAC THEN  MATCH_MP_TAC AGM THEN
         SIMP_TAC [HAS_SIZE_NUMSEG_1, DIMINDEX_GE_1, LE_1, IN_NUMSEG]]) THEN
       X_GEN_TAC ([[i:num]]) THEN DISCH_TAC THEN REWRITE_TAC [REAL_SUB_LE] THEN
       MATCH_MP_TAC REAL_LE_DIV THEN
       REPEAT (FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[i:num]]))) THEN
       ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC2,
       REWRITE_TAC [real_div, (← HolLight.GSYM REAL_ADD_RDISTRIB)] THEN
       REWRITE_TAC [(← HolLight.GSYM SUM_ADD_NUMSEG)] THEN
       ASM_SIMP_TAC [h5] THEN
       REWRITE_TAC [SUM_CONST_NUMSEG, ADD_SUB] THEN
       ASM_SIMP_TAC [REAL_MUL_RID, REAL_MUL_RINV, REAL_LE_REFL,
                    REAL_OF_NUM_EQ, DIMINDEX_NONZERO]])
  : ExceptT String IO thm).run
#eval BRUNN_MINKOWSKI_INTERVAL

-- ------------------------------------------------------------------------- --
-- Now for a finite union of boxes.                                          --
-- ------------------------------------------------------------------------- --

#eval phrase 3
def BRUNN_MINKOWSKI_ELEMENTARY : thm := keep "BRUNN_MINKOWSKI_ELEMENTARY" fun _ => (do
  let h88 ← rf
    (← ExceptT.mk [[tn / t = sn / s /\ tp / t = sp / s /\
    &0 < sp /\ &0 < sn /\ &0 < s /\ &0 < t
    ==> tn / sn = t / s /\ tp / sp = t / s]])
  let h87 ← rf (← ExceptT.mk [[&0 < s ==> s + t = s * (&1 + t / s)]])
  let h86 ← sr (← ExceptT.mk [[s SUBSET t ==> s INTER u SUBSET t INTER u]])
  let h85 ← sr (← ExceptT.mk [[s SUBSET t ==> s INTER u SUBSET u INTER t]])
  let h84 ← sr
    (← ExceptT.mk [[{x | P x /\ Q x} = {x | P x} INTER {x | Q x}]])
  let h83 ← sr (← ExceptT.mk [[s INTER u DIFF t INTER u = (s DIFF t) INTER u]])
  let h82 ← sr
    (← ExceptT.mk [[s SUBSET t /\ t DIFF s SUBSET u
    ==> (s DIFF t UNION t DIFF s) SUBSET u]])
  let h81 ← sr (← ExceptT.mk [[x INSERT (s DELETE x) = x INSERT s]])
  let h80 ← sr (← ExceptT.mk [[s = {} UNION s]])
  let h79 ← sr (← ExceptT.mk [[{x | x IN s /\ ~(x = a)} = s DELETE a]])
  let h78 ← sr (← ExceptT.mk [[{f x |x| x IN s /\ ~(f x = a)} =
    {t | t IN IMAGE f s /\ ~(t = a)}]])
  let h77 ← rr
    (← ExceptT.mk [[x <= a' + b' ==> a' <= a /\ b' <= b ==> x <= a + b]])
  let h76 ← rr (← ExceptT.mk [[&0 <= x <=> x >= &0]])
  let h75 ← rr (← ExceptT.mk [[&0 <= x <=> x >= &0]])
  let h74 ← sr (← ExceptT.mk [[{f x |x| x IN s /\ ~(f x = a)} =
    {t | t IN IMAGE f s /\ ~(t = a)}]])
  let h73 ← sr (← ExceptT.mk [[x INSERT (s DELETE x) = x INSERT s]])
  let h72 ← sr (← ExceptT.mk [[s = {} UNION s]])
  let h71 ← sr (← ExceptT.mk [[{x | x IN s /\ ~(x = a)} = s DELETE a]])
  let h70 ← sr
    (← ExceptT.mk [[interior(s) INTER interior(s') = {} /\
    interior(s INTER t) SUBSET interior s /\
    interior(s' INTER t) SUBSET interior s'
    ==> interior(s INTER t) INTER interior(s' INTER t) = {}]])
  let h69 ← sr
    (← ExceptT.mk [[s SUBSET t ==> s INTER u SUBSET t INTER u]])
  let h68 ← sr (← ExceptT.mk [[{f x |x| x IN s /\ ~(f x = a)} =
    {t | t IN IMAGE f s /\ ~(t = a)}]])
  let h67 ← sr
    (← ExceptT.mk [[interior(s) INTER interior(s') = {} /\
    interior(s INTER t) SUBSET interior s /\
    interior(s' INTER t) SUBSET interior s'
    ==> interior(s INTER t) INTER interior(s' INTER t) = {}]])
  let h66 ← sr
    (← ExceptT.mk [[x IN s ==> x SUBSET UNIONS s]])
  let h65 ← sr (← ExceptT.mk [[{f x |x| x IN s /\ ~(f x = a)} =
    {t | t IN IMAGE f s /\ ~(t = a)}]])
  let h64 ← sr
    (← ExceptT.mk [[~(s = {}) /\ s SUBSET t ==> ~(s INTER t = {})]])
  let h63 ← sr (← ExceptT.mk [[{f x |x| x IN s /\ ~(f x = a)} =
    {t | t IN IMAGE f s /\ ~(t = a)}]])
  let h62 ← ar
    (← ExceptT.mk [[CARD {x | x IN IMAGE f s /\ P x} <= CARD(IMAGE f s) /\
    CARD(IMAGE f s) <= CARD s
    ==> CARD {x | x IN IMAGE f s /\ P x} <= CARD s]])
  let h61 ← sr (← ExceptT.mk [[{f x |x| x IN s /\ ~(f x = a)} =
    {t | t IN IMAGE f s /\ ~(t = a)}]])
  let h60 ← tt (← ExceptT.mk [[p ==> q ==> r <=> q ==> p ==> r]])
  let h59 ← sr (← ExceptT.mk [[x INSERT (s DELETE x) = x INSERT s]])
  let h58 ← sr (← ExceptT.mk [[s = {} UNION s]])
  let h57 ← sr (← ExceptT.mk [[{x | x IN s /\ ~(x = a)} = s DELETE a]])
  let h56 ← sr
    (← ExceptT.mk [[interior(s) INTER interior(s') = {} /\
    interior(s INTER t) SUBSET interior s /\
    interior(s' INTER t) SUBSET interior s'
    ==> interior(s INTER t) INTER interior(s' INTER t) = {}]])
  let h55 ← sr
    (← ExceptT.mk [[s SUBSET t ==> s INTER u SUBSET t INTER u]])
  let h54 ← sr (← ExceptT.mk [[{f x |x| x IN s /\ ~(f x = a)} =
    {t | t IN IMAGE f s /\ ~(t = a)}]])
  let h53 ← sr
    (← ExceptT.mk [[interior(s) INTER interior(s') = {} /\
    interior(s INTER t) SUBSET interior s /\
    interior(s' INTER t) SUBSET interior s'
    ==> interior(s INTER t) INTER interior(s' INTER t) = {}]])
  let h52 ← sr
    (← ExceptT.mk [[x IN s ==> x SUBSET UNIONS s]])
  let h51 ← sr (← ExceptT.mk [[{f x |x| x IN s /\ ~(f x = a)} =
    {t | t IN IMAGE f s /\ ~(t = a)}]])
  let h50 ← sr
    (← ExceptT.mk [[~(s = {}) /\ s SUBSET t ==> ~(s INTER t = {})]])
  let h49 ← sr (← ExceptT.mk [[{f x |x| x IN s /\ ~(f x = a)} =
    {t | t IN IMAGE f s /\ ~(t = a)}]])
  let h48 ← ar
    (← ExceptT.mk [[CARD {x | x IN IMAGE f s /\ P x} <= CARD(IMAGE f s) /\
    CARD(IMAGE f s) <= CARD s
    ==> CARD {x | x IN IMAGE f s /\ P x} <= CARD s]])
  let h47 ← sr (← ExceptT.mk [[{f x |x| x IN s /\ ~(f x = a)} =
    {t | t IN IMAGE f s /\ ~(t = a)}]])
  let h46 ← rr (← ExceptT.mk [[x <= &0 /\ y <= &0 ==> x + y <= &0]])
  let h45 ← sr
    (← ExceptT.mk [[s SUBSET {x | P x} /\ t SUBSET {x | Q x}
    ==> (s INTER t) SUBSET {x | P x /\ Q x}]])
  let h44 ← sr
    (← ExceptT.mk [[(!x. P x \/ Q x)
    ==> s = (s INTER {x | P x}) UNION (s INTER {x | Q x})]])
  let h43 ← sr
    (← ExceptT.mk [[s SUBSET s' ==> {x + y:real^N | x IN s /\ y IN t} SUBSET
    {x + y:real^N | x IN s' /\ y IN t}]])
  let h42 ← sr (← ExceptT.mk [[{f x |x| x IN s /\ ~(f x = a)} =
    {t | t IN IMAGE f s /\ ~(t = a)}]])
  let h41 ← sr
    (← ExceptT.mk [[{a + x + y:real^N | x IN s /\ y IN t} =
    IMAGE (\z. a + z) {x + y | x IN s /\ y IN t}]])
  let h40 ← va (← ExceptT.mk [[x + a + y:real^N = a + x + y]])
  let h39 ← sr
    (← ExceptT.mk [[{f x y | x IN s /\ y IN IMAGE g t} =
    {f x (g y) | x IN s /\ y IN t}]])
  let h38 ← rr
    (← ExceptT.mk [[a' = a ==> a' >= b ==> a >= b]])
  let h37 ← rr (← ExceptT.mk [[x <= a /\ x >= a <=> x = a]])
  let h36 ← ms [NEGLIGIBLE_SUBSET, INTER_SUBSET]
    (← ExceptT.mk [[negligible t ==> negligible(s INTER t)]])
  let h35 ← sr (← ExceptT.mk [[(t INTER {x | P x}) INTER (t INTER {x | Q x}) =
    t INTER {x | P x /\ Q x}]])
  let h34 ← sr
    (← ExceptT.mk [[(!x. P x \/ Q x)
    ==> s INTER {x | P x} UNION s INTER {x | Q x} = s]])
  let h33 ← rf
    (← ExceptT.mk [[&0 < s /\ &0 < t /\ t' / t = s' / s  /\ s' + s'' = s /\ t' + t'' = t
    ==> t' / t = s' / s /\ t'' / t = s'' / s]])
  let h32 ← sr
    (← ExceptT.mk [[!g. (!x. f(x) IN s' <=> x IN s) /\ (!x. g(f x) = x)
    ==> IMAGE f t INTER s' = IMAGE f (t INTER s)]])
  let h31 ← ms []
    (← ExceptT.mk [[(!x y. Q x y ==> R x y)
    ==> (!x y. P x /\ P y /\ Q x y ==> R x y)]])
  let h30 ← va (← ExceptT.mk [[x - a:real^N = --a + x]])
  let h29 ← rr (← ExceptT.mk [[abs x <= b ==> x <= b]])
  let h28 ← rr
    (← ExceptT.mk [[u <= &1 ==> x = &1 ==> u <= x]])
  let h27 ← rr (← ExceptT.mk [[abs x <= b ==> --b <= x]])
  let h26 ← rr
    (← ExceptT.mk [[&0 <= u ==> x = &0 ==> x <= u]])
  let h25 ← sr
    (← ExceptT.mk [[{a + x + y:real^N | x IN s /\ y IN t} =
    IMAGE (\z. a + z) {x + y | x IN s /\ y IN t}]])
  let h24 ← sr
    (← ExceptT.mk [[{f x y | x IN IMAGE g s /\ y IN t} =
    {f (g x) y | x IN s /\ y IN t}]])
  let h23 ← va (← ExceptT.mk [[x - a:real^N = --a + x]])
  let h22 ← rr
    (← ExceptT.mk [[a = a' /\ b = b' ==> a >= b + c ==> a' >= b' + c]])
  let h21 ← va (← ExceptT.mk [[x - a:real^N = --a + x]])
  let h20 ← va (← ExceptT.mk [[x - a:real^N = --a + x]])
  let h19 ← va (← ExceptT.mk [[x - a:real^N = --a + x]])
  let h18 ← va (← ExceptT.mk [[x - a:real^N = --a + x]])
  let h17 ← va (← ExceptT.mk [[x - a:real^N = y - a <=> x = y]])
  let h16 ← sr
    (← ExceptT.mk [[(!x y. f x = f y ==> x = y) /\ ~(s = t)
    ==> ~(IMAGE f s = IMAGE f t)]])
  let h15 ← ms []
    (← ExceptT.mk [[(!x y. Q x y ==> R x y)
    ==> (!x y. P x /\ P y /\ Q x y ==> R x y)]])
  let h14 ← rr
    (← ExceptT.mk [[min v z <= a /\ a <= max u w
    ==> u < v /\ w < z
    ==> u <= a /\ v <= a /\ a <= w /\ a <= z \/
    w <= a /\ z <= a /\ a <= u /\ a <= v]])
  let h13 ← tt (← ExceptT.mk [[p /\ q /\ r <=> r /\ p /\ q]])
  let h12 ← tt (← ExceptT.mk [[~(a /\ b) <=> a ==> ~b]])
  let h11 ← sr
    (← ExceptT.mk [[{x | x IN s /\ ~Q x} UNION {x | x IN s /\ Q x} = s]])
  let h10 ← sr
    (← ExceptT.mk [[s' UNION s'' = s
    ==> (s' DIFF s) UNION (s DIFF s') SUBSET s'']])
  let h9 ← sr
    (← ExceptT.mk [[s' SUBSET s
    ==> {f x y | x IN s' /\ y IN t} SUBSET
    {f x y | x IN s /\ y IN t}]])
  let h8 ← rr
    (← ExceptT.mk [[c' <= c /\ a' = a
    ==> c' >= a' + b ==> c >= a + b]])
  let h7 ← sr
    (← ExceptT.mk [[{x | x IN s /\ ~Q x} UNION {x | x IN s /\ Q x} = s]])
  let h6 ← ar (← ExceptT.mk [[~(2 <= n) <=> n = 0 \/ n = 1]])
  let h5 ← rr
    (← ExceptT.mk [[x = y ==> x >= a + b ==> y >= b + a]])
  let h4 ← ms []
    (← ExceptT.mk [[(!d d' s s'. P d d' s s' ==> P d' d s' s) /\
    (!d d' s s'. ~(2 <= CARD d) /\ ~(2 <= CARD d') ==> P d d' s s') /\
    (!d d' s s'. negligible s ==>  P d d' s s') /\
    (!d d' s s'. 2 <= CARD d /\ ~(negligible s) /\ ~(negligible s')
    ==> P d d' s s')
    ==> !d d' s s'.  P d d' s s']])
  let h3 ← ms []
    (← ExceptT.mk [[(!m. m < n ==> !a b c d. f a b = m /\ stuff a b c d ==> other a b c d) <=>
    (!a b c d. f a b:num < n /\ stuff a b c d ==> other a b c d)]])
  let h2 ← tt (← ExceptT.mk [[p ==> q /\ r ==> s <=> q /\ p /\ r ==> s]])
  let h1 ← sr (← ExceptT.mk [[{f x y |x,y| F} = {}]])
  prove ([[!s t:real^N->bool.
    (s = {} <=> t = {}) /\ (?d. d division_of s) /\ (?d. d division_of t)
    ==> root (dimindex(:N)) (measure {x + y | x IN s /\ y IN t})
        >= root (dimindex(:N)) (measure s) + root (dimindex(:N)) (measure t)]])
   (REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [([[s:real^N->bool]]), ([[t:real^N->bool]]),
      ([[d1:(real^N->bool)->bool]]), ([[d2:(real^N->bool)->bool]])] THEN
    ASM_CASES_TAC ([[t:real^N->bool = {}]]) THENL
     [ASM_SIMP_TAC [NOT_IN_EMPTY, h1] THEN
      SIMP_TAC [MEASURE_EMPTY, ROOT_0, DIMINDEX_NONZERO] THEN
      STRIP_TAC THEN REAL_ARITH_TAC2,
      ASM_REWRITE_TAC [] THEN POP_ASSUM MP_TAC THEN
      ONCE_REWRITE_TAC [h2]] THEN
    X_CHOOSE_THEN ([[n:num]]) MP_TAC (← HolLight.ISPEC
     ([[CARD(d1:(real^N->bool)->bool) + CARD(d2:(real^N->bool)->bool)]])
     (← HolLight.GSYM EXISTS_REFL)) THEN
    REWRITE_TAC [IMP_IMP, (← HolLight.GSYM CONJ_ASSOC)] THEN
    MAP_EVERY (fun t => SPEC_TAC (t, t))
     [([[t:real^N->bool]]), ([[s:real^N->bool]]),
      ([[d2:(real^N->bool)->bool]]), ([[d1:(real^N->bool)->bool]]), ([[n:num]])] THEN
    MATCH_MP_TAC num_WF THEN X_GEN_TAC ([[n:num]]) THEN
    REWRITE_TAC [h3] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC h4 THEN
    REPEAT CONJ_TAC THENL
     [REPEAT GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
      CONJ_TAC THENL [REWRITE_TAC [ADD_SYM, CONJ_ACI], ALL_TAC] THEN
      MATCH_MP_TAC h5 THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN MESON_TAC [VECTOR_ADD_SYM],
      REPEAT GEN_TAC THEN
      ASM_CASES_TAC ([[FINITE(d1:(real^N->bool)->bool) /\
                     FINITE(d2:(real^N->bool)->bool)]])
      THENL [ALL_TAC, REWRITE_TAC [division_of] THEN ASM_MESON_TAC []] THEN
      ASM_SIMP_TAC [CARD_EQ_0, h6] THEN
      ASM_CASES_TAC ([[d1:(real^N->bool)->bool = {}]]) THENL
       [ASM_REWRITE_TAC [EMPTY_DIVISION_OF] THEN MESON_TAC [], ALL_TAC] THEN
      ASM_CASES_TAC ([[d2:(real^N->bool)->bool = {}]]) THENL
       [ASM_REWRITE_TAC [EMPTY_DIVISION_OF] THEN MESON_TAC [], ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       ([[(d1:(real^N->bool)->bool) HAS_SIZE 1 /\
        (d2:(real^N->bool)->bool) HAS_SIZE 1]])
      MP_TAC THENL [ASM_REWRITE_TAC [HAS_SIZE], ALL_TAC] THEN
      CONV_TAC (HolLight.LAND_CONV (HolLight.BINOP_CONV HAS_SIZE_CONV)) THEN
      DISCH_THEN (CONJUNCTS_THEN2
       (X_CHOOSE_THEN ([[u:real^N->bool]]) SUBST_ALL_TAC)
       (X_CHOOSE_THEN ([[v:real^N->bool]]) SUBST_ALL_TAC)) THEN
      STRIP_TAC THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [division_of, UNIONS_1, IN_SING]) THEN
      REPEAT (FIRST_X_ASSUM
       (CONJUNCTS_THEN2 MP_TAC
         (SUBST_ALL_TAC o HolLight.SYM o HolLight.CONJUNCT2) o HolLight.CONJUNCT2)) THEN
      REWRITE_TAC [FORALL_UNWIND_THM2] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC BRUNN_MINKOWSKI_INTERVAL THEN
      ASM_MESON_TAC [],
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN ([[measure(s:real^N->bool) = &0]]) SUBST1_TAC THENL
       [ASM_SIMP_TAC [MEASURE_EQ_0], ALL_TAC] THEN
      SIMP_TAC [ROOT_0, DIMINDEX_NONZERO, REAL_ADD_LID, real_ge] THEN
      MATCH_MP_TAC ROOT_MONO_LE THEN REWRITE_TAC [DIMINDEX_NONZERO] THEN
      SUBGOAL_THEN ([[?a:real^N. a IN s]]) STRIP_ASSUME_TAC THENL
       [HolLight.ASM SET_TAC [], ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC ([[measure(IMAGE (\x:real^N. a + x) t)]]) THEN CONJ_TAC THENL
       [REWRITE_TAC [MEASURE_TRANSLATION, REAL_LE_REFL], ALL_TAC] THEN
      MATCH_MP_TAC MEASURE_SUBSET THEN
      REWRITE_TAC [MEASURABLE_TRANSLATION_EQ] THEN
      CONJ_TAC THENL [ASM_MESON_TAC [MEASURABLE_ELEMENTARY], ALL_TAC] THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN
      CONJ_TAC THENL [ALL_TAC, HolLight.ASM SET_TAC []] THEN
      MATCH_MP_TAC MEASURABLE_COMPACT THEN MATCH_MP_TAC COMPACT_SUMS THEN
      ASM_MESON_TAC [ELEMENTARY_COMPACT],
      REWRITE_TAC [IMP_IMP, (← HolLight.GSYM CONJ_ASSOC)]] THEN
    SUBGOAL_THEN
     ([[!d1 d2 s t i j k.
          CARD d1 + CARD d2 = n /\
          1 <= k /\ k <= dimindex(:N) /\ ~(i = j) /\
          i IN d1 /\ i SUBSET {x:real^N | x$k <= &0} /\
          j IN d1 /\ j SUBSET {x | x$k >= &0} /\
          ~(negligible i) /\ ~(negligible j) /\
          ~(s = {}) /\ ~(t = {}) /\ ~(negligible s) /\ ~(negligible t) /\
          d1 division_of s /\ d2 division_of t
          ==> root(dimindex (:N)) (measure {x + y | x IN s /\ y IN t}) >=
              root(dimindex (:N)) (measure s) + root(dimindex (:N)) (measure t)]])
    MP_TAC THENL
     [ALL_TAC,
      POP_ASSUM (LABEL_TAC "*") THEN DISCH_THEN (LABEL_TAC "+") THEN
      REPEAT STRIP_TAC THEN
      ASM_CASES_TAC ([[?i:real^N->bool. i IN d1 /\ interior i = {}]]) THENL
       [REMOVE_THEN "+" (HolCore.Lib.K ALL_TAC) THEN REMOVE_THEN "*" MP_TAC THEN
        DISCH_THEN (MP_TAC o HolLight.SPECL
         [([[{i:real^N->bool | i IN d1 /\ ~(interior i = {})}]]),
          ([[d2:(real^N->bool)->bool]]),
          ([[UNIONS {i:real^N->bool | i IN d1 /\ ~(interior i = {})}]]),
          ([[t:real^N->bool]])]) THEN
        ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
         [REPEAT CONJ_TAC THENL
           [EXPAND_TAC "n" THEN REWRITE_TAC [LT_ADD_RCANCEL] THEN
            MATCH_MP_TAC CARD_PSUBSET THEN CONJ_TAC THENL
             [HolLight.ASM SET_TAC [], ASM_MESON_TAC [DIVISION_OF_FINITE]],
            DISCH_TAC THEN
            SUBGOAL_THEN
             ([[negligible(UNIONS {i | i IN d1 /\ ~(interior i = {})} UNION
                         UNIONS {i:real^N->bool | i IN d1 /\ interior i = {}})]])
            MP_TAC THENL
             [ASM_REWRITE_TAC [UNION_EMPTY] THEN
              MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN CONJ_TAC THENL
               [MATCH_MP_TAC FINITE_RESTRICT THEN
                ASM_MESON_TAC [DIVISION_OF_FINITE],
                REWRITE_TAC [IN_ELIM_THM, IMP_CONJ] THEN
                FIRST_ASSUM (fun th => HolLight.tactic_of do
                  pure (GEN_REWRITE_TAC HolCore.Lib.I [(← HolLight.MATCH_MP FORALL_IN_DIVISION th)])) THEN
                REWRITE_TAC [INTERIOR_CLOSED_INTERVAL, NEGLIGIBLE_INTERVAL]],
              REWRITE_TAC [(← HolLight.GSYM UNIONS_UNION), h7] THEN
              RULE_ASSUM_TAC (HolLight.REWRITE_RULE [division_of]) THEN ASM_REWRITE_TAC []],
            MATCH_MP_TAC DIVISION_OF_SUBSET THEN
            EXISTS_TAC ([[d1:(real^N->bool)->bool]]) THEN
            CONJ_TAC THENL [ASM_MESON_TAC [division_of], SET_TAC []]],
          MATCH_MP_TAC h8 THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC ROOT_MONO_LE THEN REWRITE_TAC [DIMINDEX_NONZERO] THEN
            MATCH_MP_TAC MEASURE_SUBSET THEN REPEAT CONJ_TAC THENL
             [MATCH_MP_TAC MEASURABLE_COMPACT THEN MATCH_MP_TAC COMPACT_SUMS THEN
              CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [ELEMENTARY_COMPACT]] THEN
              MATCH_MP_TAC COMPACT_UNIONS THEN
              RULE_ASSUM_TAC (HolLight.REWRITE_RULE [division_of]) THEN
              ASM_SIMP_TAC [FINITE_RESTRICT, IN_ELIM_THM] THEN
              ASM_MESON_TAC [COMPACT_INTERVAL],
              MATCH_MP_TAC MEASURABLE_COMPACT THEN MATCH_MP_TAC COMPACT_SUMS THEN
              ASM_MESON_TAC [ELEMENTARY_COMPACT],
              MATCH_MP_TAC h9 THEN
              SUBGOAL_THEN ([[s:real^N->bool = UNIONS d1]]) SUBST1_TAC THENL
               [ASM_MESON_TAC [division_of],
                MATCH_MP_TAC SUBSET_UNIONS THEN SET_TAC []]],
            AP_TERM_TAC THEN
            MATCH_MP_TAC MEASURE_NEGLIGIBLE_SYMDIFF THEN
            MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
            EXISTS_TAC ([[UNIONS {i:real^N->bool | i IN d1 /\ interior i = {}}]]) THEN
            CONJ_TAC THENL
             [MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN CONJ_TAC THENL
               [MATCH_MP_TAC FINITE_RESTRICT THEN
                ASM_MESON_TAC [DIVISION_OF_FINITE],
                REWRITE_TAC [IN_ELIM_THM, IMP_CONJ] THEN
                FIRST_ASSUM (fun th => HolLight.tactic_of do
                  pure (GEN_REWRITE_TAC HolCore.Lib.I [(← HolLight.MATCH_MP FORALL_IN_DIVISION th)])) THEN
                REWRITE_TAC [INTERIOR_CLOSED_INTERVAL, NEGLIGIBLE_INTERVAL]],
              MATCH_MP_TAC h10 THEN
              REWRITE_TAC [(← HolLight.GSYM UNIONS_UNION), h11] THEN
              RULE_ASSUM_TAC (HolLight.REWRITE_RULE [division_of]) THEN
              ASM_REWRITE_TAC []]]],
        FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [NOT_EXISTS_THM]) THEN
        REWRITE_TAC [h12] THEN DISCH_TAC THEN
        REMOVE_THEN "*" (HolCore.Lib.K ALL_TAC) THEN
        SUBGOAL_THEN
         ([[?d:(real^N->bool)->bool. d SUBSET d1 /\ d HAS_SIZE 2]])
        MP_TAC THENL
         [FIRST_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP CHOOSE_SUBSET o
            HolLight.MATCH_MP DIVISION_OF_FINITE) THEN ASM_REWRITE_TAC [],
          ALL_TAC] THEN
        CONV_TAC (HolLight.LAND_CONV (HolLight.ONCE_DEPTH_CONV HAS_SIZE_CONV)) THEN
        REWRITE_TAC [RIGHT_AND_EXISTS_THM] THEN
        ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[i:real^N->bool]]) MP_TAC) THEN
        ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[j:real^N->bool]]) MP_TAC) THEN
        ONCE_REWRITE_TAC [h13] THEN
        REWRITE_TAC [UNWIND_THM2, INSERT_SUBSET, EMPTY_SUBSET] THEN STRIP_TAC THEN
        MP_TAC (← HolLight.ASSUME ([[d1 division_of (s:real^N->bool)]])) THEN
        REWRITE_TAC [division_of] THEN
        DISCH_THEN (MP_TAC o HolCore.Lib.el (α := thm) 2 o HolLight.CONJUNCTS) THEN
        DISCH_THEN (MP_TAC o HolLight.SPECL [([[i:real^N->bool]]), ([[j:real^N->bool]])]) THEN
        ASM_REWRITE_TAC [] THEN
        SUBGOAL_THEN
         ([[?u v w z. i = interval[u:real^N,v] /\ j = interval[w:real^N,z] ]])
        STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [DIVISION_OF], ALL_TAC] THEN
        ASM_REWRITE_TAC [(← HolLight.GSYM INTERIOR_INTER), INTER_INTERVAL] THEN
        REWRITE_TAC [INTERIOR_CLOSED_INTERVAL, INTERVAL_EQ_EMPTY] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[k:num]]) MP_TAC) THEN
        REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        SIMP_TAC [LAMBDA_BETA, (← HolLight.ASSUME ([[1 <= k]])),
                  (← HolLight.ASSUME ([[k <= dimindex(:N)]]))] THEN
        GEN_REWRITE_TAC HolLight.LAND_CONV [REAL_LE_BETWEEN] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[a:real]]) MP_TAC) THEN
        DISCH_THEN (MP_TAC o HolLight.MATCH_MP h14) THEN
        ANTS_TAC THENL
         [UNDISCH_TAC ([[!i:real^N->bool. i IN d1 ==> ~(interior i = {})]]) THEN
          DISCH_THEN (fun th => HolLight.tactic_of do
            pure (MP_TAC (← HolLight.ISPEC ([[interval[u:real^N,v] ]]) th) THEN
                  MP_TAC (← HolLight.ISPEC ([[interval[w:real^N,z] ]]) th))) THEN
          REWRITE_TAC [INTERIOR_CLOSED_INTERVAL, INTERVAL_NE_EMPTY] THEN
          ASM_MESON_TAC [],
          ALL_TAC] THEN
        STRIP_TAC THEN
        FIRST_X_ASSUM (MP_TAC o HolLight.SPECL
           [([[IMAGE (IMAGE (\x:real^N. x - a % basis k)) d1]]),
            ([[d2:(real^N->bool)->bool]]),
            ([[IMAGE (\x:real^N. x - a % basis k) s]]),
            ([[t:real^N->bool]])])
        THENL
         [DISCH_THEN (MP_TAC o HolLight.SPECL
           [([[IMAGE (\x:real^N. x - a % basis k) i]]),
            ([[IMAGE (\x:real^N. x - a % basis k) j]]), ([[k:num]])]),
          DISCH_THEN (MP_TAC o HolLight.SPECL
           [([[IMAGE (\x:real^N. x - a % basis k) j]]),
            ([[IMAGE (\x:real^N. x - a % basis k) i]]), ([[k:num]])])] THEN
        (ASM_REWRITE_TAC [] THEN ANTS_TAC THEN REPEAT CONJ_TAC THENL
          [EXPAND_TAC "n" THEN AP_THM_TAC THEN AP_TERM_TAC THEN
           MATCH_MP_TAC CARD_IMAGE_INJ THEN
           CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [DIVISION_OF_FINITE]] THEN
           MATCH_MP_TAC h15 THEN
           REWRITE_TAC [INJECTIVE_IMAGE] THEN VECTOR_ARITH_TAC,
           MATCH_MP_TAC h16 THEN
           REWRITE_TAC [h17] THEN
           ASM_MESON_TAC [],
           MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_MESON_TAC [],
           REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN
           ASM_SIMP_TAC [VECTOR_SUB_COMPONENT, VECTOR_MUL_COMPONENT,
            BASIS_COMPONENT, REAL_MUL_RID, REAL_LE_SUB_RADD, REAL_ADD_LID] THEN
           REWRITE_TAC [IN_INTERVAL] THEN ASM_MESON_TAC [REAL_LE_TRANS],
           MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_MESON_TAC [],
           REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM, real_ge] THEN
           ASM_SIMP_TAC [VECTOR_SUB_COMPONENT, VECTOR_MUL_COMPONENT,
            BASIS_COMPONENT, REAL_MUL_RID, REAL_LE_SUB_LADD, REAL_ADD_LID] THEN
           REWRITE_TAC [IN_INTERVAL] THEN ASM_MESON_TAC [REAL_LE_TRANS],
           REWRITE_TAC [h18] THEN
           ASM_REWRITE_TAC [NEGLIGIBLE_TRANSLATION_EQ] THEN
           ASM_MESON_TAC [NEGLIGIBLE_INTERVAL, INTERIOR_CLOSED_INTERVAL],
           REWRITE_TAC [h19] THEN
           ASM_REWRITE_TAC [NEGLIGIBLE_TRANSLATION_EQ] THEN
           ASM_MESON_TAC [NEGLIGIBLE_INTERVAL, INTERIOR_CLOSED_INTERVAL],
           ASM_REWRITE_TAC [IMAGE_EQ_EMPTY],
           REWRITE_TAC [h20] THEN
           ASM_REWRITE_TAC [NEGLIGIBLE_TRANSLATION_EQ],
           REWRITE_TAC [h21] THEN
           ASM_REWRITE_TAC [DIVISION_OF_TRANSLATION],
           MATCH_MP_TAC h22 THEN
           REWRITE_TAC [h23] THEN
           REWRITE_TAC [MEASURE_TRANSLATION] THEN
           REWRITE_TAC [(← HolLight.GSYM VECTOR_ADD_ASSOC), h24] THEN
           REWRITE_TAC [h25] THEN
           REWRITE_TAC [MEASURE_TRANSLATION]])]] THEN
    SUBGOAL_THEN
     ([[!d1 d2 s t i j k.
          CARD d1 + CARD d2 = n /\
          1 <= k /\ k <= dimindex(:N) /\ ~(i = j) /\
          i IN d1 /\ i SUBSET {x:real^N | x$k <= &0} /\ ~(negligible i) /\
          j IN d1 /\ j SUBSET {x | x$k >= &0} /\ ~(negligible j) /\
          measure(t INTER {x | x$k <= &0}) / measure t =
          measure(s INTER {x | x$k <= &0}) / measure s /\
          measure(t INTER {x | x$k >= &0}) / measure t =
          measure(s INTER {x | x$k >= &0}) / measure s /\
          ~(s = {}) /\ ~(t = {}) /\ ~(negligible s) /\ ~(negligible t) /\
          d1 division_of s /\ d2 division_of t
          ==> root(dimindex (:N)) (measure {x + y | x IN s /\ y IN t}) >=
              root(dimindex (:N)) (measure s) + root(dimindex (:N)) (measure t)]])
    MP_TAC THENL
     [ALL_TAC,
      POP_ASSUM (HolCore.Lib.K ALL_TAC) THEN DISCH_TAC THEN
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN ([[&0 < measure(s:real^N->bool) /\ &0 < measure(t:real^N->bool)]])
      STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC [MEASURABLE_MEASURE_POS_LT, MEASURABLE_ELEMENTARY],
        ALL_TAC] THEN
      SUBGOAL_THEN
       ([[?a. measure(t INTER {x:real^N | x$k <= a}) / measure t =
            measure(s INTER {x:real^N | x$k <= &0}) / measure s]])
      STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN
         ([[&0 <= measure(s INTER {x:real^N | x$k <= &0}) / measure s /\
          measure(s INTER {x:real^N | x$k <= &0}) / measure s <= &1]])
        MP_TAC THENL
         [ASM_SIMP_TAC [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ, REAL_MUL_LZERO] THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC MEASURE_POS_LE,
            REWRITE_TAC [REAL_MUL_LID] THEN MATCH_MP_TAC MEASURE_SUBSET THEN
            REPEAT CONJ_TAC THENL
             [ALL_TAC,
              ASM_MESON_TAC [MEASURABLE_ELEMENTARY],
              SET_TAC []]] THEN
          MATCH_MP_TAC MEASURABLE_COMPACT THEN
          MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
          REWRITE_TAC [CLOSED_HALFSPACE_COMPONENT_LE] THEN
          ASM_MESON_TAC [ELEMENTARY_COMPACT],
          SPEC_TAC (([[measure(s INTER {x:real^N | x$k <= &0}) / measure s]]),
                   ([[u:real]]))] THEN
        X_GEN_TAC ([[u:real]]) THEN STRIP_TAC THEN
        SUBGOAL_THEN ([[?b:real. &0 < b /\ !x:real^N. x IN t ==> abs(x$k) <= b]])
        STRIP_ASSUME_TAC THENL
         [SUBGOAL_THEN ([[bounded(t:real^N->bool)]]) MP_TAC THENL
           [ASM_MESON_TAC [ELEMENTARY_BOUNDED], REWRITE_TAC [BOUNDED_POS]] THEN
          MATCH_MP_TAC MONO_EXISTS THEN
          ASM_MESON_TAC [COMPONENT_LE_NORM, REAL_LE_TRANS],
          ALL_TAC] THEN
        SUBGOAL_THEN
         ([[?a. a IN real_interval[--b,b] /\
              measure (t INTER {x:real^N | x$k <= a}) / measure t = u]])
         (fun th => MESON_TAC [th]) THEN
        MATCH_MP_TAC REAL_IVT_INCREASING THEN REPEAT CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC,
          ALL_TAC,
          FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h26) THEN
          REWRITE_TAC [real_div, REAL_ENTIRE] THEN DISJ1_TAC THEN
          MATCH_MP_TAC MEASURE_EQ_0 THEN
          MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
          EXISTS_TAC ([[{x:real^N | x$k = --b}]]) THEN
          ASM_SIMP_TAC [NEGLIGIBLE_STANDARD_HYPERPLANE] THEN
          SIMP_TAC [SUBSET, IN_INTER, IN_ELIM_THM, (← HolLight.GSYM REAL_LE_ANTISYM)] THEN
          ASM_MESON_TAC [h27],
          FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h28) THEN
          ASM_SIMP_TAC [REAL_EQ_LDIV_EQ, REAL_MUL_LID] THEN
          AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_INTER, IN_ELIM_THM] THEN
          ASM_MESON_TAC [h29]] THEN
        REWRITE_TAC [real_div] THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_RMUL THEN
        REWRITE_TAC [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
        GEN_TAC THEN DISCH_TAC THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
        MATCH_MP_TAC REAL_CONTINUOUS_MEASURE_IN_HALFSPACE_LE THEN
        ASM_MESON_TAC [MEASURABLE_ELEMENTARY],
        ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPECL
       [([[d1:(real^N->bool)->bool]]),
        ([[IMAGE (IMAGE (\x:real^N. x - a % basis k)) d2]]),
        ([[s:real^N->bool]]),
        ([[IMAGE (\x:real^N. x - a % basis k) t]]),
        ([[i:real^N->bool]]), ([[j:real^N->bool]]), ([[k:num]])]) THEN
      ASM_REWRITE_TAC [] THEN
      ONCE_REWRITE_TAC [h30] THEN
      ASM_REWRITE_TAC [NEGLIGIBLE_TRANSLATION_EQ, DIVISION_OF_TRANSLATION] THEN
      ASM_REWRITE_TAC [IMAGE_EQ_EMPTY] THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [EXPAND_TAC "n" THEN AP_TERM_TAC THEN
          MATCH_MP_TAC CARD_IMAGE_INJ THEN
          CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [DIVISION_OF_FINITE]] THEN
          MATCH_MP_TAC h31 THEN
          REWRITE_TAC [INJECTIVE_IMAGE] THEN VECTOR_ARITH_TAC,
          ALL_TAC] THEN
        SUBGOAL_THEN
         ([[IMAGE (\x. --(a % basis k) + x) t INTER {x:real^N | x$k >= &0} =
          IMAGE (\x. --(a % basis k) + x) (t INTER {x | x$k >= a}) /\
          IMAGE (\x. --(a % basis k) + x) t INTER {x:real^N | x$k <= &0} =
          IMAGE (\x. --(a % basis k) + x) (t INTER {x | x$k <= a})]])
        (CONJUNCTS_THEN SUBST1_TAC) THENL
         [CONJ_TAC THEN
          MATCH_MP_TAC h32 THEN
          ASM_SIMP_TAC [IN_ELIM_THM, VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT,
                       BASIS_COMPONENT, VECTOR_NEG_COMPONENT] THEN
          EXISTS_TAC ([[\x:real^N. a % basis k + x]]) THEN
          (CONJ_TAC THENL [REAL_ARITH_TAC2, VECTOR_ARITH_TAC]),
          ALL_TAC] THEN
        REWRITE_TAC [MEASURE_TRANSLATION] THEN MATCH_MP_TAC h33 THEN
        ASM_REWRITE_TAC [] THEN CONJ_TAC THEN
        MATCH_MP_TAC MEASURE_NEGLIGIBLE_UNION_EQ THEN
        (REPEAT CONJ_TAC THENL
          [MATCH_MP_TAC MEASURABLE_COMPACT THEN
           MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
           REWRITE_TAC [CLOSED_HALFSPACE_COMPONENT_LE,
                       CLOSED_HALFSPACE_COMPONENT_GE] THEN
           ASM_MESON_TAC [ELEMENTARY_COMPACT],
           MATCH_MP_TAC MEASURABLE_COMPACT THEN
           MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
           REWRITE_TAC [CLOSED_HALFSPACE_COMPONENT_LE,
                       CLOSED_HALFSPACE_COMPONENT_GE] THEN
           ASM_MESON_TAC [ELEMENTARY_COMPACT],
           MATCH_MP_TAC h34 THEN
           REAL_ARITH_TAC2,
           REWRITE_TAC [h35] THEN
           MATCH_MP_TAC h36 THEN
           REWRITE_TAC [h37] THEN
           ASM_SIMP_TAC [NEGLIGIBLE_STANDARD_HYPERPLANE]]),
        REWRITE_TAC [MEASURE_TRANSLATION] THEN MATCH_MP_TAC h38 THEN AP_TERM_TAC THEN
        REWRITE_TAC [h39] THEN
        ONCE_REWRITE_TAC [h40] THEN
        REWRITE_TAC [h41] THEN
        REWRITE_TAC [MEASURE_TRANSLATION]]] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [real_ge] THEN
    SUBGOAL_THEN ([[measurable(s:real^N->bool) /\ measurable(t:real^N->bool)]])
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [MEASURABLE_ELEMENTARY], ALL_TAC] THEN
    SUBGOAL_THEN ([[measurable {x + y:real^N | x IN s /\ y IN t}]]) ASSUME_TAC THENL
     [MATCH_MP_TAC MEASURABLE_COMPACT THEN MATCH_MP_TAC COMPACT_SUMS THEN
      ASM_MESON_TAC [ELEMENTARY_COMPACT],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[&0 < measure(s:real^N->bool) /\ &0 < measure(t:real^N->bool)]])
    STRIP_ASSUME_TAC THENL
      [ASM_MESON_TAC [MEASURABLE_MEASURE_POS_LT], ALL_TAC] THEN
    SUBGOAL_THEN ([[FINITE(d1:(real^N->bool)->bool) /\
                  FINITE(d2:(real^N->bool)->bool)]])
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [DIVISION_OF_FINITE], ALL_TAC] THEN
    HolCore.Lib.W (MP_TAC o HolLight.PART_MATCH (HolCore.Equal.lhs o HolCore.Kernel.rand)
      REAL_LE_ROOT o HolLight.snd) THEN
    ASM_SIMP_TAC [DIMINDEX_NONZERO, MEASURE_POS_LE, ROOT_POS_LE, REAL_LE_ADD] THEN
    DISCH_THEN SUBST1_TAC THEN
    ABBREV_TAC ([[dl = {l INTER {x:real^N | x$k <= &0} |l|
                      l IN d1 DELETE j /\ ~(l INTER {x | x$k <= &0} = {})}]]) THEN
    ABBREV_TAC ([[dr = {l INTER {x:real^N | x$k >= &0} |l|
                      l IN d1 DELETE i /\ ~(l INTER {x | x$k >= &0} = {})}]]) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     ([[measure {x + y:real^N | x IN UNIONS dl /\ y IN (t INTER {x | x$k <= &0})} +
      measure {x + y | x IN UNIONS dr /\ y IN (t INTER {x | x$k >= &0})}]]) THEN
    CONJ_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       ([[measure {x + y:real^N | x IN (s INTER {x | x$k <= &0}) /\
                                y IN (t INTER {x | x$k <= &0})} +
        measure {x + y:real^N | x IN (s INTER {x | x$k >= &0}) /\
                                y IN (t INTER {x | x$k >= &0})}]]) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
        (MATCH_MP_TAC MEASURE_SUBSET THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC MEASURABLE_COMPACT THEN MATCH_MP_TAC COMPACT_SUMS THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC COMPACT_UNIONS THEN
            MAP_EVERY EXPAND_TAC ["dl", "dr"] THEN
            ONCE_REWRITE_TAC [h42] THEN
            ASM_SIMP_TAC [IN_DELETE, FINITE_DELETE, FINITE_IMAGE,
                         FINITE_RESTRICT, IMP_CONJ] THEN
            REWRITE_TAC [IN_ELIM_THM, IMP_CONJ, FORALL_IN_IMAGE, IN_DELETE] THEN
            FIRST_ASSUM (fun th => HolLight.tactic_of do
              pure (GEN_REWRITE_TAC HolCore.Lib.I [(← HolLight.MATCH_MP FORALL_IN_DIVISION th)])) THEN
            ASM_SIMP_TAC [INTERVAL_SPLIT, COMPACT_INTERVAL],
            MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
            REWRITE_TAC [CLOSED_HALFSPACE_COMPONENT_LE,
                        CLOSED_HALFSPACE_COMPONENT_GE] THEN
            ASM_MESON_TAC [ELEMENTARY_COMPACT]],
          MATCH_MP_TAC MEASURABLE_COMPACT THEN MATCH_MP_TAC COMPACT_SUMS THEN
          CONJ_TAC THEN MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
          REWRITE_TAC [CLOSED_HALFSPACE_COMPONENT_LE,
                      CLOSED_HALFSPACE_COMPONENT_GE] THEN
          ASM_MESON_TAC [ELEMENTARY_COMPACT],
          MATCH_MP_TAC h43 THEN
          MAP_EVERY EXPAND_TAC ["dl", "dr"] THEN
          REWRITE_TAC [SUBSET, FORALL_IN_UNIONS] THEN
          REWRITE_TAC [FORALL_IN_GSPEC, IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
          SIMP_TAC [IN_DELETE, IN_INTER, IN_ELIM_THM] THEN
          RULE_ASSUM_TAC (HolLight.REWRITE_RULE [division_of]) THEN
          ASM_MESON_TAC [IN_UNIONS]]),
        ALL_TAC] THEN
      SUBGOAL_THEN
       ([[s = (s INTER {x:real^N | x$k <= &0}) UNION (s INTER {x | x$k >= &0}) /\
        t = (t INTER {x:real^N | x$k <= &0}) UNION (t INTER {x | x$k >= &0})]])
      MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC h44 THEN
        REAL_ARITH_TAC2,
        DISCH_THEN (fun th =>
          GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.ONCE_DEPTH_CONV) [th])] THEN
      HolCore.Lib.W (MP_TAC o HolLight.PART_MATCH (HolCore.Kernel.rand o HolCore.Kernel.rand)
         MEASURE_NEGLIGIBLE_UNION o HolCore.Equal.lhand o HolLight.snd) THEN
      ANTS_TAC THENL
       [REPEAT (CONJ_TAC THENL
         [MATCH_MP_TAC MEASURABLE_COMPACT THEN MATCH_MP_TAC COMPACT_SUMS THEN
          CONJ_TAC THEN MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
          REWRITE_TAC [CLOSED_HALFSPACE_COMPONENT_LE,
                      CLOSED_HALFSPACE_COMPONENT_GE] THEN
          ASM_MESON_TAC [ELEMENTARY_COMPACT],
          ALL_TAC]) THEN
        MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
        EXISTS_TAC ([[{x:real^N | x$k = &0}]]) THEN
        ASM_SIMP_TAC [NEGLIGIBLE_STANDARD_HYPERPLANE] THEN
        REWRITE_TAC [(← HolLight.GSYM REAL_LE_ANTISYM)] THEN MATCH_MP_TAC h45 THEN
        REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN
        SIMP_TAC [IN_INTER, IN_ELIM_THM, REAL_LE_ADD, VECTOR_ADD_COMPONENT,
          real_ge, h46],
        DISCH_THEN (SUBST1_TAC o HolLight.SYM)] THEN
      MATCH_MP_TAC MEASURE_SUBSET THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MEASURABLE_UNION THEN CONJ_TAC THEN
        MATCH_MP_TAC MEASURABLE_COMPACT THEN MATCH_MP_TAC COMPACT_SUMS THEN
        CONJ_TAC THEN MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
        REWRITE_TAC [CLOSED_HALFSPACE_COMPONENT_LE,
                    CLOSED_HALFSPACE_COMPONENT_GE] THEN
        ASM_MESON_TAC [ELEMENTARY_COMPACT],
        MATCH_MP_TAC MEASURABLE_COMPACT THEN MATCH_MP_TAC COMPACT_SUMS THEN
        CONJ_TAC THEN MATCH_MP_TAC COMPACT_UNION THEN CONJ_TAC THEN
        MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
        REWRITE_TAC [CLOSED_HALFSPACE_COMPONENT_LE,
                    CLOSED_HALFSPACE_COMPONENT_GE] THEN
        ASM_MESON_TAC [ELEMENTARY_COMPACT],
        SET_TAC []]] THEN
    SUBGOAL_THEN
     ([[&0 < measure(s INTER {x:real^N | x$k <= &0}) /\
      &0 < measure(s INTER {x:real^N | x$k >= &0})]])
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC [MEASURABLE_MEASURE_POS_LT, MEASURABLE_INTER_HALFSPACE_LE,
                   MEASURABLE_INTER_HALFSPACE_GE] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC ([[~negligible(i:real^N->bool)]]),
        UNDISCH_TAC ([[~negligible(j:real^N->bool)]])] THEN
      REWRITE_TAC [CONTRAPOS_THM] THEN MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_CONJ_ALT]
        NEGLIGIBLE_SUBSET) THEN
      ASM_REWRITE_TAC [SUBSET_INTER] THEN
      UNDISCH_TAC ([[d1 division_of (s:real^N->bool)]]) THEN
      REWRITE_TAC [division_of] THEN HolLight.ASM SET_TAC [],
      ALL_TAC] THEN
    FIRST_X_ASSUM (fun th => HolLight.tactic_of do
      pure (MP_TAC (← HolLight.SPECL [([[dl:(real^N->bool)->bool]]),
                    ([[{l INTER {x:real^N | x$k <= &0} |l|
                      l IN d2 /\ ~(l INTER {x | x$k <= &0} = {})}]]),
                    ([[UNIONS dl :real^N->bool]]),
                     ([[t INTER {x:real^N | x$k <= &0}]])] th) THEN
      MP_TAC (← HolLight.SPECL [([[dr:(real^N->bool)->bool]]),
                    ([[{l INTER {x:real^N | x$k >= &0} |l|
                      l IN d2 /\ ~(l INTER {x | x$k >= &0} = {})}]]),
                    ([[UNIONS dr :real^N->bool]]),
                     ([[t INTER {x:real^N | x$k >= &0}]])] th))) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [EXPAND_TAC "n" THEN MATCH_MP_TAC LTE_ADD2 THEN
        MAP_EVERY EXPAND_TAC ["dl", "dr"] THEN
        ONCE_REWRITE_TAC [h47] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC LET_TRANS THEN
          EXISTS_TAC ([[CARD(d1 DELETE (i:real^N->bool))]]) THEN CONJ_TAC THENL
           [ALL_TAC, MATCH_MP_TAC CARD_PSUBSET THEN HolLight.ASM SET_TAC []],
          ALL_TAC] THEN
        MATCH_MP_TAC h48 THEN
        ASM_SIMP_TAC [CARD_IMAGE_LE, FINITE_DELETE] THEN
        MATCH_MP_TAC CARD_SUBSET THEN
        ASM_SIMP_TAC [FINITE_IMAGE, FINITE_DELETE] THEN SET_TAC [],
        REWRITE_TAC [(← HolLight.GSYM MEMBER_NOT_EMPTY), IN_UNIONS] THEN
        ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
        EXISTS_TAC ([[j INTER {x:real^N | x$k >= &0}]]) THEN
        REWRITE_TAC [RIGHT_EXISTS_AND_THM, MEMBER_NOT_EMPTY] THEN
        MAP_EVERY EXPAND_TAC ["dl", "dr"] THEN
        ONCE_REWRITE_TAC [h49] THEN
        REWRITE_TAC [IN_ELIM_THM, IN_IMAGE, IN_DELETE, (← HolLight.GSYM CONJ_ASSOC)] THEN
        CONJ_TAC THENL
         [EXISTS_TAC ([[j:real^N->bool]]) THEN ASM_REWRITE_TAC [],
          MATCH_MP_TAC h50 THEN
          ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [division_of]],
        DISCH_TAC THEN
        UNDISCH_TAC ([[measure (t INTER {x:real^N | x$k >= &0}) / measure t =
                     measure (s INTER {x:real^N | x$k >= &0}) / measure s]]) THEN
        ASM_SIMP_TAC [MEASURE_EMPTY, REAL_EQ_RDIV_EQ] THEN
        REWRITE_TAC [real_div, REAL_MUL_LZERO] THEN
        CONV_TAC (HolLight.RAND_CONV HolLight.SYM_CONV) THEN ASM_SIMP_TAC [REAL_LT_IMP_NZ],
        REWRITE_TAC [division_of] THEN
        MAP_EVERY EXPAND_TAC ["dl", "dr"] THEN
        ONCE_REWRITE_TAC [h51] THEN
        ASM_SIMP_TAC [FINITE_RESTRICT, FINITE_IMAGE, FINITE_DELETE] THEN
        REWRITE_TAC [IN_ELIM_THM, IMP_CONJ, FORALL_IN_IMAGE, IN_DELETE] THEN
        REWRITE_TAC [RIGHT_FORALL_IMP_THM, FORALL_IN_IMAGE, IN_DELETE] THEN
        CONJ_TAC THENL
         [FIRST_ASSUM (fun th => HolLight.tactic_of do
              pure (GEN_REWRITE_TAC HolCore.Lib.I [(← HolLight.MATCH_MP FORALL_IN_DIVISION th)])) THEN
          REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
          ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
           [ALL_TAC, ASM_SIMP_TAC [INTERVAL_SPLIT] THEN MESON_TAC []] THEN
          MATCH_MP_TAC h52 THEN
          HolLight.ASM SET_TAC [],
          REPEAT STRIP_TAC THEN
          MATCH_MP_TAC h53 THEN
          SIMP_TAC [SUBSET_INTERIOR, INTER_SUBSET] THEN
          ASM_MESON_TAC [division_of]],
        REWRITE_TAC [division_of] THEN
        MAP_EVERY EXPAND_TAC ["dl", "dr"] THEN
        ONCE_REWRITE_TAC [h54] THEN
        ASM_SIMP_TAC [FINITE_RESTRICT, FINITE_IMAGE, FINITE_DELETE] THEN
        REWRITE_TAC [IN_ELIM_THM, IMP_CONJ, FORALL_IN_IMAGE, IN_DELETE] THEN
        REWRITE_TAC [RIGHT_FORALL_IMP_THM, FORALL_IN_IMAGE, IN_DELETE] THEN
        REPEAT CONJ_TAC THENL
         [FIRST_ASSUM (fun th => HolLight.tactic_of do
              pure (GEN_REWRITE_TAC HolCore.Lib.I [(← HolLight.MATCH_MP FORALL_IN_DIVISION th)])) THEN
          REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
          ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
           [ALL_TAC, ASM_SIMP_TAC [INTERVAL_SPLIT] THEN MESON_TAC []] THEN
          MATCH_MP_TAC h55 THEN
          RULE_ASSUM_TAC (HolLight.REWRITE_RULE [division_of]) THEN ASM_MESON_TAC [],
          REPEAT STRIP_TAC THEN
          MATCH_MP_TAC h56 THEN
          SIMP_TAC [SUBSET_INTERIOR, INTER_SUBSET] THEN
          ASM_MESON_TAC [division_of],
          REWRITE_TAC [h57] THEN
          GEN_REWRITE_TAC HolLight.LAND_CONV [h58] THEN
          REWRITE_TAC [(← HolLight.GSYM UNIONS_INSERT)] THEN
          REWRITE_TAC [h59] THEN
          REWRITE_TAC [UNIONS_INSERT, UNION_EMPTY] THEN
          REWRITE_TAC [(← HolLight.GSYM SIMPLE_IMAGE), (← HolLight.GSYM INTER_UNIONS)] THEN
          AP_THM_TAC THEN AP_TERM_TAC THEN ASM_MESON_TAC [division_of]]],
      ALL_TAC] THEN
    ONCE_REWRITE_TAC [h60] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [EXPAND_TAC "n" THEN MATCH_MP_TAC LTE_ADD2 THEN
        MAP_EVERY EXPAND_TAC ["dl", "dr"] THEN
        ONCE_REWRITE_TAC [h61] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC LET_TRANS THEN
          EXISTS_TAC ([[CARD(d1 DELETE (j:real^N->bool))]]) THEN CONJ_TAC THENL
           [ALL_TAC, MATCH_MP_TAC CARD_PSUBSET THEN HolLight.ASM SET_TAC []],
          ALL_TAC] THEN
        MATCH_MP_TAC h62 THEN
        ASM_SIMP_TAC [CARD_IMAGE_LE, FINITE_DELETE] THEN
        MATCH_MP_TAC CARD_SUBSET THEN
        ASM_SIMP_TAC [FINITE_IMAGE, FINITE_DELETE] THEN SET_TAC [],
        REWRITE_TAC [(← HolLight.GSYM MEMBER_NOT_EMPTY), IN_UNIONS] THEN
        ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
        EXISTS_TAC ([[i INTER {x:real^N | x$k <= &0}]]) THEN
        REWRITE_TAC [RIGHT_EXISTS_AND_THM, MEMBER_NOT_EMPTY] THEN
        MAP_EVERY EXPAND_TAC ["dl", "dr"] THEN
        ONCE_REWRITE_TAC [h63] THEN
        REWRITE_TAC [IN_ELIM_THM, IN_IMAGE, IN_DELETE, (← HolLight.GSYM CONJ_ASSOC)] THEN
        CONJ_TAC THENL
         [EXISTS_TAC ([[i:real^N->bool]]) THEN ASM_REWRITE_TAC [],
          MATCH_MP_TAC h64 THEN
          ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [division_of]],
        DISCH_TAC THEN
        UNDISCH_TAC ([[measure (t INTER {x:real^N | x$k <= &0}) / measure t =
                     measure (s INTER {x:real^N | x$k <= &0}) / measure s]]) THEN
        ASM_SIMP_TAC [MEASURE_EMPTY, REAL_EQ_RDIV_EQ] THEN
        REWRITE_TAC [real_div, REAL_MUL_LZERO] THEN
        CONV_TAC (HolLight.RAND_CONV HolLight.SYM_CONV) THEN ASM_SIMP_TAC [REAL_LT_IMP_NZ],
        REWRITE_TAC [division_of] THEN
        MAP_EVERY EXPAND_TAC ["dl", "dr"] THEN
        ONCE_REWRITE_TAC [h65] THEN
        ASM_SIMP_TAC [FINITE_RESTRICT, FINITE_IMAGE, FINITE_DELETE] THEN
        REWRITE_TAC [IN_ELIM_THM, IMP_CONJ, FORALL_IN_IMAGE, IN_DELETE] THEN
        REWRITE_TAC [RIGHT_FORALL_IMP_THM, FORALL_IN_IMAGE, IN_DELETE] THEN
        CONJ_TAC THENL
         [FIRST_ASSUM (fun th => HolLight.tactic_of do
              pure (GEN_REWRITE_TAC HolCore.Lib.I [(← HolLight.MATCH_MP FORALL_IN_DIVISION th)])) THEN
          REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
          ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
           [ALL_TAC, ASM_SIMP_TAC [INTERVAL_SPLIT] THEN MESON_TAC []] THEN
          MATCH_MP_TAC h66 THEN
          HolLight.ASM SET_TAC [],
          REPEAT STRIP_TAC THEN
          MATCH_MP_TAC h67 THEN
          SIMP_TAC [SUBSET_INTERIOR, INTER_SUBSET] THEN
          ASM_MESON_TAC [division_of]],
        REWRITE_TAC [division_of] THEN
        MAP_EVERY EXPAND_TAC ["dl", "dr"] THEN
        ONCE_REWRITE_TAC [h68] THEN
        ASM_SIMP_TAC [FINITE_RESTRICT, FINITE_IMAGE, FINITE_DELETE] THEN
        REWRITE_TAC [IN_ELIM_THM, IMP_CONJ, FORALL_IN_IMAGE, IN_DELETE] THEN
        REWRITE_TAC [RIGHT_FORALL_IMP_THM, FORALL_IN_IMAGE, IN_DELETE] THEN
        REPEAT CONJ_TAC THENL
         [FIRST_ASSUM (fun th => HolLight.tactic_of do
              pure (GEN_REWRITE_TAC HolCore.Lib.I [(← HolLight.MATCH_MP FORALL_IN_DIVISION th)])) THEN
          REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
          ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
           [ALL_TAC, ASM_SIMP_TAC [INTERVAL_SPLIT] THEN MESON_TAC []] THEN
          MATCH_MP_TAC h69 THEN
          RULE_ASSUM_TAC (HolLight.REWRITE_RULE [division_of]) THEN ASM_MESON_TAC [],
          REPEAT STRIP_TAC THEN
          MATCH_MP_TAC h70 THEN
          SIMP_TAC [SUBSET_INTERIOR, INTER_SUBSET] THEN
          ASM_MESON_TAC [division_of],
          REWRITE_TAC [h71] THEN
          GEN_REWRITE_TAC HolLight.LAND_CONV [h72] THEN
          REWRITE_TAC [(← HolLight.GSYM UNIONS_INSERT)] THEN
          REWRITE_TAC [h73] THEN
          REWRITE_TAC [UNIONS_INSERT, UNION_EMPTY] THEN
          REWRITE_TAC [(← HolLight.GSYM SIMPLE_IMAGE), (← HolLight.GSYM INTER_UNIONS)] THEN
          AP_THM_TAC THEN AP_TERM_TAC THEN ASM_MESON_TAC [division_of]]],
      ALL_TAC] THEN
    REWRITE_TAC [real_ge, IMP_IMP] THEN
    SUBGOAL_THEN
     ([[compact(UNIONS dl:real^N->bool) /\ compact(UNIONS dr:real^N->bool)]])
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC COMPACT_UNIONS THEN
      MAP_EVERY EXPAND_TAC ["dl", "dr"] THEN
      ONCE_REWRITE_TAC [h74] THEN
      ASM_SIMP_TAC [FINITE_RESTRICT, FINITE_IMAGE, FINITE_DELETE] THEN
      REWRITE_TAC [IMP_CONJ, IN_ELIM_THM, FORALL_IN_IMAGE, IN_DELETE] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
      REWRITE_TAC [CLOSED_HALFSPACE_COMPONENT_LE,
                  CLOSED_HALFSPACE_COMPONENT_GE] THEN
      ASM_MESON_TAC [division_of, COMPACT_INTERVAL],
      ALL_TAC] THEN
    SUBGOAL_THEN
     ([[measurable(UNIONS dl:real^N->bool) /\
      measurable(UNIONS dr:real^N->bool)]])
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [MEASURABLE_COMPACT], ALL_TAC] THEN
    SUBGOAL_THEN
      ([[measurable { x + y:real^N |
                    x IN UNIONS dl /\ y IN t INTER {x | x$k <= &0}} /\
       measurable { x + y:real^N |
                    x IN UNIONS dr /\ y IN t INTER {x | &0 <= x$k}}]])
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC MEASURABLE_COMPACT THEN
      MATCH_MP_TAC COMPACT_SUMS THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
      REWRITE_TAC [h75,
        CLOSED_HALFSPACE_COMPONENT_LE, CLOSED_HALFSPACE_COMPONENT_GE] THEN
      ASM_MESON_TAC [ELEMENTARY_COMPACT],
      ALL_TAC] THEN
    HolLight.ASM (fun ths => HolLight.tactic_of do
        pure (CONV_TAC (← ExceptT.mk (HolCore.Simp.GEN_SIMPLIFY_CONV Session.B
          (HolCore.Simp.TOP_DEPTH_SQCONV Session.B) (← ExceptT.mk (Session.basic_ss [])) 5 ths))))
     [REAL_LE_ROOT, DIMINDEX_NONZERO, REAL_LE_ADD, ROOT_POS_LE,
      MEASURE_POS_LE, MEASURABLE_INTER_HALFSPACE_LE,
      MEASURABLE_INTER_HALFSPACE_GE, h76] THEN
    MATCH_MP_TAC h77 THEN
    SUBGOAL_THEN
     ([[measure(UNIONS dl :real^N->bool) =
      measure(s INTER {x:real^N | x$k <= &0}) /\
      measure(UNIONS dr :real^N->bool) =
      measure(s INTER {x:real^N | x$k >= &0})]])
     (CONJUNCTS_THEN SUBST1_TAC)
    THENL
     [MAP_EVERY EXPAND_TAC ["dl", "dr"] THEN
      ONCE_REWRITE_TAC [h78] THEN
      REWRITE_TAC [h79] THEN
      CONJ_TAC THEN
      GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV) [h80] THEN
      REWRITE_TAC [(← HolLight.GSYM UNIONS_INSERT)] THEN
      REWRITE_TAC [h81] THEN
      REWRITE_TAC [UNIONS_INSERT, UNION_EMPTY] THEN
      REWRITE_TAC [(← HolLight.GSYM SIMPLE_IMAGE), (← HolLight.GSYM INTER_UNIONS)] THEN
      MATCH_MP_TAC MEASURE_NEGLIGIBLE_SYMDIFF THEN
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC ([[{x:real^N | x$k = &0}]]) THEN
      ASM_SIMP_TAC [NEGLIGIBLE_STANDARD_HYPERPLANE] THEN
      MATCH_MP_TAC h82 THEN
      REWRITE_TAC [h83] THEN
      (SUBGOAL_THEN ([[s:real^N->bool = UNIONS d1]]) SUBST1_TAC THENL
        [ASM_MESON_TAC [division_of], ALL_TAC] THEN
       CONJ_TAC THENL [SET_TAC [], ALL_TAC]) THEN
      REWRITE_TAC [(← HolLight.GSYM REAL_LE_ANTISYM), real_ge, h84]
      THENL
       [MATCH_MP_TAC h85,
        MATCH_MP_TAC h86] THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [real_ge]) THEN
      FIRST_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP
       (← HolLight.REWRITE_RULE [IMP_CONJ_ALT] SUBSET_TRANS)) THEN
      SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN
     ([[root (dimindex (:N)) (measure (s INTER {x:real^N | x$k <= &0})) +
      root (dimindex (:N)) (measure (t INTER {x:real^N | x$k <= &0})) =
      root (dimindex (:N)) (measure (s INTER {x | x$k <= &0})) *
      (&1 + root (dimindex (:N)) (measure (t INTER {x | x$k <= &0})) /
            root (dimindex (:N)) (measure (s INTER {x | x$k <= &0}))) /\
     root (dimindex (:N)) (measure (s INTER {x:real^N | x$k >= &0})) +
      root (dimindex (:N)) (measure (t INTER {x:real^N | x$k >= &0})) =
      root (dimindex (:N)) (measure (s INTER {x | x$k >= &0})) *
      (&1 + root (dimindex (:N)) (measure (t INTER {x | x$k >= &0})) /
            root (dimindex (:N)) (measure (s INTER {x | x$k >= &0})))]])
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THEN
      MATCH_MP_TAC h87 THEN
      ASM_SIMP_TAC [ROOT_POS_LT, DIMINDEX_NONZERO],
      ALL_TAC] THEN
    ASM_SIMP_TAC [DIMINDEX_NONZERO, (← HolLight.GSYM REAL_ROOT_DIV), MEASURE_POS_LE,
      MEASURABLE_INTER_HALFSPACE_LE, MEASURABLE_INTER_HALFSPACE_GE] THEN
    SUBGOAL_THEN
     ([[measure(t INTER {x:real^N | x$k <= &0}) /
      measure(s INTER {x:real^N | x$k <= &0}) = measure t / measure s /\
      measure(t INTER {x:real^N | x$k >= &0}) /
      measure(s INTER {x:real^N | x$k >= &0}) = measure t / measure s]])
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [MATCH_MP_TAC h88 THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_ADD_RDISTRIB), REAL_POW_MUL] THEN
    ASM_SIMP_TAC [REAL_POW_ROOT, DIMINDEX_NONZERO, MEASURE_POS_LE,
             MEASURABLE_INTER_HALFSPACE_LE, MEASURABLE_INTER_HALFSPACE_GE] THEN
    SUBGOAL_THEN
     ([[measure (s INTER {x | x$k <= &0}) + measure (s INTER {x | x$k >= &0}) =
      root (dimindex(:N)) (measure(s:real^N->bool)) pow (dimindex(:N))]])
    SUBST1_TAC THENL
     [ASM_SIMP_TAC [REAL_POW_ROOT, DIMINDEX_NONZERO, REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC MEASURE_NEGLIGIBLE_UNION_EQ THEN
      ASM_SIMP_TAC [MEASURABLE_INTER_HALFSPACE_LE,
                   MEASURABLE_INTER_HALFSPACE_GE] THEN
      CONJ_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_UNION, IN_INTER, IN_ELIM_THM] THEN
        X_GEN_TAC ([[x:real^N]]) THEN ASM_CASES_TAC ([[(x:real^N) IN s]]) THEN
        ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC2,
        MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
        EXISTS_TAC ([[{x:real^N | x$k = &0}]]) THEN
        ASM_SIMP_TAC [NEGLIGIBLE_STANDARD_HYPERPLANE] THEN
        REWRITE_TAC [(← HolLight.GSYM REAL_LE_ANTISYM), real_ge] THEN SET_TAC []],
      ASM_SIMP_TAC [(← HolLight.GSYM REAL_ROOT_MUL), MEASURE_POS_LE, DIMINDEX_NONZERO,
                   REAL_LE_DIV, (← HolLight.GSYM REAL_POW_MUL),
                   REAL_ADD_LDISTRIB, REAL_MUL_RID] THEN
      ASM_SIMP_TAC [REAL_DIV_LMUL, REAL_LT_IMP_NZ, REAL_LE_REFL]])
  : ExceptT String IO thm).run
#eval BRUNN_MINKOWSKI_ELEMENTARY

-- ------------------------------------------------------------------------- --
-- Now for open sets.                                                        --
-- ------------------------------------------------------------------------- --

#eval phrase 4
def BRUNN_MINKOWSKI_OPEN : thm := keep "BRUNN_MINKOWSKI_OPEN" fun _ => (do
  let h4 ← rr
    (← ExceptT.mk [[s1 <= r1 /\ s2 <= r2 /\ rs <= s
    ==> rs >= r1 + r2 ==> s1 + s2 <= s]])
  let h3 ← rr (← ExceptT.mk [[e < s ==> ~(s - e < &0)]])
  let h2 ← rr (← ExceptT.mk [[measure(s:real^N->bool) = measure s - &0]])
  let h1 ← sr (← ExceptT.mk [[{x + y:real^N | x IN {} /\ y IN {}} = {}]])
  prove ([[!s t:real^N->bool.
    (s = {} <=> t = {}) /\ bounded s /\ open s /\ bounded t /\ open t
    ==> root (dimindex(:N)) (measure {x + y | x IN s /\ y IN t})
        >= root (dimindex(:N)) (measure s) + root (dimindex(:N)) (measure t)]])
   (REPEAT GEN_TAC THEN ASM_CASES_TAC ([[t:real^N->bool = {}]]) THEN
    ASM_SIMP_TAC [h1,
                 REAL_LE_REFL, MEASURE_EMPTY, ROOT_0, DIMINDEX_NONZERO,
                 real_ge, REAL_ADD_LID] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC (← HolLight.ISPEC ([[atreal(&0) within {e | &0 <= e}]]) SessionMultiLib.RealAnalysis.REALLIM_UBOUND) THEN
    EXISTS_TAC ([[\e. root (dimindex(:N)) (measure(s:real^N->bool) - e) +
                    root (dimindex(:N)) (measure(t:real^N->bool) - e)]]) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
      EXISTS_TAC
       ([[\e. (measure(s:real^N->bool) - e) rpow (inv(&(dimindex(:N)))) +
            (measure(t:real^N->bool) - e) rpow (inv(&(dimindex(:N))))]]) THEN
      REWRITE_TAC [] THEN CONJ_TAC THENL
       [REWRITE_TAC [EVENTUALLY_WITHINREAL] THEN
        EXISTS_TAC ([[min (measure(s:real^N->bool)) (measure(t:real^N->bool))]]) THEN
        ASM_SIMP_TAC [REAL_LT_MIN, IN_ELIM_THM, REAL_SUB_RZERO,
                     MEASURE_OPEN_POS_LT] THEN
        REPEAT STRIP_TAC THEN BINOP_TAC THEN CONV_TAC HolLight.SYM_CONV THEN
        MATCH_MP_TAC REAL_ROOT_RPOW THEN
        REWRITE_TAC [DIMINDEX_NONZERO] THEN ASM_REAL_ARITH_TAC,
        ASM_SIMP_TAC [REAL_ROOT_RPOW, MEASURE_OPEN_POS_LT, DIMINDEX_NONZERO,
                     REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THEN
        GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV)
         [h2] THEN
        REWRITE_TAC [(← HolLight.GSYM REAL_CONTINUOUS_WITHINREAL)] THEN
        REWRITE_TAC [(← HolLight.GSYM (← ExceptT.mk (REWRITE_CONV [o_DEF]
          ([[(\x. x rpow y) o (\e. s - e)]]))))] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_COMPOSE THEN
        ASM_SIMP_TAC [REAL_CONTINUOUS_SUB, REAL_CONTINUOUS_WITHIN_ID,
                     REAL_CONTINUOUS_CONST] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_WITHIN_RPOW THEN
        REWRITE_TAC [REAL_LE_INV_EQ, REAL_POS]],
      HolCore.Lib.W (MP_TAC o HolLight.PART_MATCH (HolCore.Equal.lhand o HolCore.Kernel.rand)
        TRIVIAL_LIMIT_WITHIN_REALINTERVAL o
        HolCore.Kernel.rand o HolLight.snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC [is_realinterval, IN_ELIM_THM] THEN REAL_ARITH_TAC2,
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [EXTENSION, IN_SING] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[&1]])) THEN REWRITE_TAC [IN_ELIM_THM] THEN
        REAL_ARITH_TAC2],
      REWRITE_TAC [EVENTUALLY_WITHINREAL] THEN
      EXISTS_TAC ([[min (measure(s:real^N->bool)) (measure(t:real^N->bool))]]) THEN
      ASM_SIMP_TAC [REAL_LT_MIN, IN_ELIM_THM, REAL_SUB_RZERO,
                   MEASURE_OPEN_POS_LT] THEN
      X_GEN_TAC ([[e:real]]) THEN REWRITE_TAC [real_abs] THEN
      ASM_CASES_TAC ([[&0 <= e]]) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
      MAP_EVERY (fun l => HolLight.tactic_of do
          pure (MP_TAC (← HolLight.ISPECL l OPEN_MEASURABLE_INNER_DIVISION)))
      [ [([[t:real^N->bool]]), ([[e:real]])], [([[s:real^N->bool]]), ([[e:real]])] ] THEN
      ASM_SIMP_TAC [MEASURABLE_OPEN, (← HolLight.GSYM REAL_LT_SUB_RADD)] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[D:(real^N->bool)->bool]]) STRIP_ASSUME_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[E:(real^N->bool)->bool]]) STRIP_ASSUME_TAC) THEN
      MP_TAC (← HolLight.ISPECL [([[UNIONS D:real^N->bool]]), ([[UNIONS E:real^N->bool]])]
          BRUNN_MINKOWSKI_ELEMENTARY) THEN
      ANTS_TAC THENL
       [ASM_MESON_TAC [MEASURE_EMPTY, h3],
        ALL_TAC] THEN
      MATCH_MP_TAC h4 THEN
      REPEAT CONJ_TAC THEN MATCH_MP_TAC ROOT_MONO_LE THEN
      ASM_SIMP_TAC [DIMINDEX_NONZERO, REAL_SUB_LE, REAL_LT_IMP_LE] THEN
      SUBGOAL_THEN
       ([[measurable {x + y :real^N | x IN UNIONS D /\ y IN UNIONS E}]])
      ASSUME_TAC THENL
       [MATCH_MP_TAC MEASURABLE_COMPACT THEN MATCH_MP_TAC COMPACT_SUMS THEN
        ASM_MESON_TAC [ELEMENTARY_COMPACT],
        MATCH_MP_TAC MEASURE_SUBSET] THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ALL_TAC, HolLight.ASM SET_TAC []] THEN
      MATCH_MP_TAC MEASURABLE_OPEN THEN
      ASM_SIMP_TAC [BOUNDED_SUMS, OPEN_SUMS]])
  : ExceptT String IO thm).run
#eval BRUNN_MINKOWSKI_OPEN

-- ------------------------------------------------------------------------- --
-- Now for convex sets.                                                      --
-- ------------------------------------------------------------------------- --

#eval phrase 5
def BRUNN_MINKOWSKI_CONVEX : thm := keep "BRUNN_MINKOWSKI_CONVEX" fun _ => (do
  let h1 ← sr
    (← ExceptT.mk [[s' SUBSET s /\ t' SUBSET t
    ==> {x + y:real^N | x IN s' /\ y IN t'} SUBSET
    {x + y | x IN s /\ y IN t}]])
  prove ([[!s t:real^N->bool.
    (s = {} <=> t = {}) /\ bounded s /\ convex s /\ bounded t /\ convex t
    ==> root (dimindex(:N)) (measure {x + y | x IN s /\ y IN t})
        >= root (dimindex(:N)) (measure s) + root (dimindex(:N)) (measure t)]])
   (REPEAT GEN_TAC THEN ASM_CASES_TAC ([[t:real^N->bool = {}]]) THEN
    ASM_SIMP_TAC [BRUNN_MINKOWSKI_OPEN, OPEN_EMPTY] THEN STRIP_TAC THEN
    ASM_SIMP_TAC [(← HolLight.GSYM MEASURE_INTERIOR), NEGLIGIBLE_CONVEX_FRONTIER, real_ge] THEN
    ASM_CASES_TAC ([[interior s:real^N->bool = {}]]) THENL
     [ASM_SIMP_TAC [MEASURE_EMPTY, ROOT_0, DIMINDEX_NONZERO, REAL_ADD_LID] THEN
      MATCH_MP_TAC ROOT_MONO_LE THEN
      ASM_SIMP_TAC [DIMINDEX_NONZERO, MEASURE_POS_LE, MEASURABLE_INTERIOR] THEN
      SUBGOAL_THEN ([[?a:real^N. a IN s]]) STRIP_ASSUME_TAC THENL
       [HolLight.ASM SET_TAC [], ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC ([[measure(IMAGE (\x:real^N. a + x) t)]]) THEN CONJ_TAC THENL
       [ASM_SIMP_TAC [MEASURE_TRANSLATION, MEASURE_INTERIOR,
                     NEGLIGIBLE_CONVEX_FRONTIER, REAL_LE_REFL],
        MATCH_MP_TAC MEASURE_SUBSET THEN
        ASM_SIMP_TAC [MEASURABLE_TRANSLATION_EQ, MEASURABLE_CONVEX,
                     CONVEX_SUMS, BOUNDED_SUMS] THEN
        HolLight.ASM SET_TAC []],
      ALL_TAC] THEN
    ASM_CASES_TAC ([[interior t:real^N->bool = {}]]) THENL
     [ASM_SIMP_TAC [MEASURE_EMPTY, ROOT_0, DIMINDEX_NONZERO, REAL_ADD_RID] THEN
      MATCH_MP_TAC ROOT_MONO_LE THEN
      ASM_SIMP_TAC [DIMINDEX_NONZERO, MEASURE_POS_LE, MEASURABLE_INTERIOR] THEN
      SUBGOAL_THEN ([[?a:real^N. a IN t]]) STRIP_ASSUME_TAC THENL
       [HolLight.ASM SET_TAC [], ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC ([[measure(IMAGE (\x:real^N. a + x) s)]]) THEN CONJ_TAC THENL
       [ASM_SIMP_TAC [MEASURE_TRANSLATION, MEASURE_INTERIOR,
                     NEGLIGIBLE_CONVEX_FRONTIER, REAL_LE_REFL],
        MATCH_MP_TAC MEASURE_SUBSET THEN
        ASM_SIMP_TAC [MEASURABLE_TRANSLATION_EQ, MEASURABLE_CONVEX,
                     CONVEX_SUMS, BOUNDED_SUMS] THEN
        GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [VECTOR_ADD_SYM] THEN
        HolLight.ASM SET_TAC []],
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
      ([[root (dimindex (:N))
            (measure {x + y:real^N | x IN interior s /\ y IN interior t})]]) THEN
    ASM_SIMP_TAC [(← HolLight.GSYM real_ge), BRUNN_MINKOWSKI_OPEN, BOUNDED_INTERIOR,
                 OPEN_INTERIOR] THEN
    REWRITE_TAC [real_ge] THEN MATCH_MP_TAC ROOT_MONO_LE THEN
    REWRITE_TAC [DIMINDEX_NONZERO] THEN MATCH_MP_TAC MEASURE_SUBSET THEN
    ASM_SIMP_TAC [DIMINDEX_NONZERO, MEASURE_POS_LE, BOUNDED_SUMS,
       MEASURABLE_CONVEX, BOUNDED_INTERIOR, CONVEX_SUMS, CONVEX_INTERIOR] THEN
    MATCH_MP_TAC h1 THEN
    REWRITE_TAC [INTERIOR_SUBSET])
  : ExceptT String IO thm).run
#eval BRUNN_MINKOWSKI_CONVEX

-- ------------------------------------------------------------------------- --
-- Now for compact sets.                                                     --
-- ------------------------------------------------------------------------- --

#eval phrase 6
def INTERS_SUMS_CLOSED_BALL_SEQUENTIAL : thm := keep "INTERS_SUMS_CLOSED_BALL_SEQUENTIAL" fun _ => (do
  let h1 ← na (← ExceptT.mk [[dist(y + e:real^N,y) = norm e]])
  prove ([[!s:real^N->bool.
          closed s
          ==> INTERS {{x + d | x IN s /\ d IN ball(vec 0,inv(&n + &1))} |
                      n IN (:num)} = s]])
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN
    REWRITE_TAC [INTERS_GSPEC, IN_ELIM_THM, IN_UNIV] THEN
    X_GEN_TAC ([[x:real^N]]) THEN EQ_TAC THENL
     [ASM_CASES_TAC ([[(x:real^N) IN s]]) THEN ASM_REWRITE_TAC [] THEN
      MP_TAC (← HolLight.ISPECL [([[s:real^N->bool]]), ([[x:real^N]])] SEPARATE_POINT_CLOSED) THEN
      ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC ([[d:real]]) THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [REAL_ARCH_INV] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[n:num]]) STRIP_ASSUME_TAC) THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC ([[n:num]])) THEN REWRITE_TAC [NOT_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[y:real^N]]), ([[e:real^N]])] THEN
      REWRITE_TAC [IN_BALL_0] THEN STRIP_TAC THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[y:real^N]])) THEN
      ASM_REWRITE_TAC [h1] THEN
      SUBGOAL_THEN ([[inv(&n + &1) <= inv(&n)]]) MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN
        REWRITE_TAC [REAL_OF_NUM_ADD, REAL_OF_NUM_LE, REAL_OF_NUM_LT] THEN
        ASM_ARITH_TAC,
        ASM_REAL_ARITH_TAC],
      DISCH_TAC THEN X_GEN_TAC ([[n:num]]) THEN
      MAP_EVERY EXISTS_TAC [([[x:real^N]]), ([[vec 0:real^N]])] THEN
      ASM_REWRITE_TAC [CENTRE_IN_BALL, VECTOR_ADD_RID, REAL_LT_INV_EQ] THEN
      REAL_ARITH_TAC2])
  : ExceptT String IO thm).run
#eval INTERS_SUMS_CLOSED_BALL_SEQUENTIAL

#eval phrase 7
def MEASURE_SUMS_COMPACT_EPSILON : thm := keep "MEASURE_SUMS_COMPACT_EPSILON" fun _ => (do
  let h3 ← sr
    (← ExceptT.mk [[t' SUBSET t
    ==> {x + y:real^N | x IN s /\ y IN t'} SUBSET
    {x + y | x IN s /\ y IN t}]])
  let h2 ← rr
    (← ExceptT.mk [[m <= m1 /\ m1 <= m2
    ==> abs(m2 - m) < e ==> abs(m1 - m) < e]])
  let h1 ← sr
    (← ExceptT.mk [[t' SUBSET t
    ==> {x + y:real^N | x IN s /\ y IN t'} SUBSET
    {x + y | x IN s /\ y IN t}]])
  prove ([[!s:real^N->bool.
          compact s
          ==> ((\e. measure {x + d | x IN s /\ d IN ball(vec 0,e)}) --->
               measure s)
              (atreal (&0) within {e | &0 <= e})]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPEC
     ([[\n. {x + d:real^N | x IN s /\ d IN ball(vec 0,inv(&n + &1))}]])
     HAS_MEASURE_NESTED_INTERS) THEN
    ASM_SIMP_TAC [INTERS_SUMS_CLOSED_BALL_SEQUENTIAL, COMPACT_IMP_CLOSED] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC [MEASURABLE_OPEN, BOUNDED_SUMS, OPEN_SUMS,
                   COMPACT_IMP_BOUNDED, BOUNDED_BALL, OPEN_BALL] THEN
      GEN_TAC THEN MATCH_MP_TAC h1 THEN
      MATCH_MP_TAC SUBSET_BALL THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC [REAL_OF_NUM_ADD, REAL_OF_NUM_LE, REAL_OF_NUM_LT] THEN
      ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [(← HolLight.GSYM (← HolLight.REWRITE_RULE [o_DEF] TENDSTO_REAL))] THEN
    REWRITE_TAC [SessionMultiLib.RealAnalysis.REALLIM_SEQUENTIALLY, REALLIM_WITHINREAL] THEN
    STRIP_TAC THEN X_GEN_TAC ([[e:real]]) THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[e:real]])) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_TAC ([[N:num]])) THEN EXISTS_TAC ([[inv(&N + &1)]]) THEN
    ASM_REWRITE_TAC [REAL_LT_INV_EQ] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC2, ALL_TAC] THEN
    X_GEN_TAC ([[d:real]]) THEN REWRITE_TAC [IN_ELIM_THM, REAL_SUB_RZERO] THEN
    ASM_CASES_TAC ([[abs d = d]]) THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN STRIP_TAC, ASM_REAL_ARITH_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[N:num]])) THEN REWRITE_TAC [LE_REFL] THEN
    MATCH_MP_TAC h2 THEN
    CONJ_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
    ASM_SIMP_TAC [MEASURABLE_OPEN, BOUNDED_SUMS, OPEN_SUMS,
                 COMPACT_IMP_BOUNDED, BOUNDED_BALL, OPEN_BALL]
    THENL
     [REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC ([[x:real^N]]) THEN
      DISCH_TAC THEN MAP_EVERY EXISTS_TAC [([[x:real^N]]), ([[vec 0:real^N]])] THEN
      ASM_REWRITE_TAC [CENTRE_IN_BALL, VECTOR_ADD_RID],
      MATCH_MP_TAC h3 THEN
      MATCH_MP_TAC SUBSET_BALL THEN ASM_SIMP_TAC [REAL_LT_IMP_LE]])
  : ExceptT String IO thm).run
#eval MEASURE_SUMS_COMPACT_EPSILON

#eval phrase 8
def BRUNN_MINKOWSKI_COMPACT : thm := keep "BRUNN_MINKOWSKI_COMPACT" fun _ => (do
  -- The local lemmas are proved (in order) while the tactic is built,
  -- before the goal is parsed; their build-time rules run first.
  let h1 ← na
    (← ExceptT.mk [[norm(d:real^N) < e /\ norm(k) < e ==> norm(d + k) < &2 * e]])
  let lemma1 ← prove
   ([[{ x + y:real^N | x IN {x + d | x IN s /\ d IN ball(vec 0,e)} /\
                      y IN {y + d | y IN t /\ d IN ball(vec 0,e)}} =
     { z + d | z IN {x + y | x IN s /\ y IN t} /\ d IN ball(vec 0,&2 * e) }]])
   (MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC [SUBSET, FORALL_IN_GSPEC, RIGHT_FORALL_IMP_THM, IMP_CONJ] THEN
    REWRITE_TAC [IN_ELIM_THM, IN_BALL_0] THEN CONJ_TAC THENL
     [X_GEN_TAC ([[x:real^N]]) THEN DISCH_TAC THEN
      X_GEN_TAC ([[d:real^N]]) THEN DISCH_TAC THEN
      X_GEN_TAC ([[y:real^N]]) THEN DISCH_TAC THEN
      X_GEN_TAC ([[k:real^N]]) THEN DISCH_TAC THEN
      EXISTS_TAC ([[x + y:real^N]]) THEN EXISTS_TAC ([[d + k:real^N]]) THEN
      CONJ_TAC THENL [ALL_TAC, VECTOR_ARITH_TAC] THEN
      ASM_SIMP_TAC [h1] THEN
      EXISTS_TAC ([[x:real^N]]) THEN EXISTS_TAC ([[y:real^N]]) THEN
      ASM_REWRITE_TAC [] THEN VECTOR_ARITH_TAC,
      X_GEN_TAC ([[x:real^N]]) THEN DISCH_TAC THEN
      X_GEN_TAC ([[y:real^N]]) THEN DISCH_TAC THEN
      X_GEN_TAC ([[d:real^N]]) THEN DISCH_TAC THEN
      EXISTS_TAC ([[x + inv(&2) % d:real^N]]) THEN
      EXISTS_TAC ([[y + inv(&2) % d:real^N]]) THEN
      CONJ_TAC THENL [ALL_TAC, VECTOR_ARITH_TAC] THEN CONJ_TAC THENL
       [EXISTS_TAC ([[x:real^N]]), EXISTS_TAC ([[y:real^N]])] THEN
      EXISTS_TAC ([[inv(&2) % d:real^N]]) THEN
      ASM_REWRITE_TAC [NORM_MUL] THEN ASM_REAL_ARITH_TAC])
  let lemma2 ← prove
   ([[(f ---> l) (atreal (&0) within {e | &0 <= e})
     ==> ((\e. f(&2 * e)) ---> l) (atreal (&0) within {e | &0 <= e})]])
   (REWRITE_TAC [REALLIM_WITHINREAL] THEN DISCH_TAC THEN
    X_GEN_TAC ([[e:real]]) THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[e:real]])) THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [IN_ELIM_THM, REAL_SUB_RZERO] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[d:real]]) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC ([[d / &2]]) THEN ASM_REWRITE_TAC [REAL_HALF] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC)
  prove ([[!s t:real^N->bool.
    (s = {} <=> t = {}) /\ compact s /\ compact t
    ==> root (dimindex(:N)) (measure {x + y | x IN s /\ y IN t})
        >= root (dimindex(:N)) (measure s) + root (dimindex(:N)) (measure t)]])
   (REPEAT GEN_TAC THEN ASM_CASES_TAC ([[t:real^N->bool = {}]]) THEN
    ASM_SIMP_TAC [BRUNN_MINKOWSKI_OPEN, OPEN_EMPTY, BOUNDED_EMPTY] THEN
    STRIP_TAC THEN REWRITE_TAC [real_ge] THEN
    MATCH_MP_TAC (← HolLight.ISPEC ([[atreal (&0) within {e | &0 <= e}]]) SessionMultiLib.RealAnalysis.REALLIM_LE) THEN
    EXISTS_TAC
     ([[\e. root (dimindex(:N))
               (measure {x + d:real^N | x IN s /\ d IN ball(vec 0,e)}) +
          root (dimindex(:N))
               (measure {x + d:real^N | x IN t /\ d IN ball(vec 0,e)})]]) THEN
    EXISTS_TAC
     ([[\e. root (dimindex(:N))
               (measure { x + y:real^N |
                     x IN {x + d | x IN s /\ d IN ball(vec 0,e)} /\
                     y IN {y + d | y IN t /\ d IN ball(vec 0,e)}})]]) THEN
    REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
     [HolLight.ASM (fun ths => HolLight.tactic_of do
          pure (CONV_TAC (← ExceptT.mk (HolCore.Simp.GEN_SIMPLIFY_CONV Session.B
            (HolCore.Simp.TOP_DEPTH_SQCONV Session.B) (← ExceptT.mk (Session.basic_ss [])) 5 ths))))
       [REAL_ROOT_RPOW, DIMINDEX_NONZERO, MEASURE_POS_LE, MEASURABLE_COMPACT,
        MEASURABLE_OPEN, BOUNDED_SUMS, OPEN_SUMS,
        COMPACT_IMP_BOUNDED, BOUNDED_BALL, OPEN_BALL] THEN
      MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REALLIM_RPOW THEN
      REWRITE_TAC [REAL_LE_INV_EQ, REAL_POS] THEN
      MATCH_MP_TAC MEASURE_SUMS_COMPACT_EPSILON THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [lemma1] THEN MATCH_MP_TAC lemma2 THEN
      HolLight.ASM (fun ths => HolLight.tactic_of do
          pure (CONV_TAC (← ExceptT.mk (HolCore.Simp.GEN_SIMPLIFY_CONV Session.B
            (HolCore.Simp.TOP_DEPTH_SQCONV Session.B) (← ExceptT.mk (Session.basic_ss [])) 6 ths))))
       [REAL_ROOT_RPOW, DIMINDEX_NONZERO, MEASURE_POS_LE, MEASURABLE_COMPACT,
        MEASURABLE_OPEN, BOUNDED_SUMS, OPEN_SUMS, COMPACT_SUMS,
        COMPACT_IMP_BOUNDED, BOUNDED_BALL, OPEN_BALL] THEN
      MATCH_MP_TAC REALLIM_RPOW THEN
      REWRITE_TAC [REAL_LE_INV_EQ, REAL_POS] THEN
      MATCH_MP_TAC MEASURE_SUMS_COMPACT_EPSILON THEN
      ASM_SIMP_TAC [COMPACT_SUMS],
      HolCore.Lib.W (MP_TAC o HolLight.PART_MATCH (HolCore.Equal.lhand o HolCore.Kernel.rand)
        TRIVIAL_LIMIT_WITHIN_REALINTERVAL o
        HolCore.Kernel.rand o HolLight.snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC [is_realinterval, IN_ELIM_THM] THEN REAL_ARITH_TAC2,
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [EXTENSION, IN_SING] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[&1]])) THEN REWRITE_TAC [IN_ELIM_THM] THEN
        REAL_ARITH_TAC2],
      MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC ([[e:real]]) THEN
      REWRITE_TAC [(← HolLight.GSYM real_ge)] THEN
      MATCH_MP_TAC BRUNN_MINKOWSKI_OPEN THEN
      SIMP_TAC [OPEN_SUMS, OPEN_BALL] THEN
      ASM_SIMP_TAC [BOUNDED_SUMS, BOUNDED_BALL, COMPACT_IMP_BOUNDED] THEN
      HolLight.ASM SET_TAC []])
  : ExceptT String IO thm).run
#eval BRUNN_MINKOWSKI_COMPACT

-- ------------------------------------------------------------------------- --
-- Finally, for an arbitrary measurable set. In this general case, the       --
-- measurability of the sum-set is needed as an additional hypothesis.       --
-- ------------------------------------------------------------------------- --

#eval phrase 9
def BRUNN_MINKOWSKI_MEASURABLE : thm := keep "BRUNN_MINKOWSKI_MEASURABLE" fun _ => (do
  let h3 ← rr
    (← ExceptT.mk [[s1 <= r1 /\ s2 <= r2 /\ rs <= s
    ==> rs >= r1 + r2 ==> s1 + s2 <= s]])
  let h2 ← rr (← ExceptT.mk [[e < s ==> ~(s - e < &0)]])
  let h1 ← rr (← ExceptT.mk [[measure(s:real^N->bool) = measure s - &0]])
  prove ([[!s t:real^N->bool.
    (s = {} <=> t = {}) /\ measurable s /\ measurable t /\
    measurable {x + y | x IN s /\ y IN t}
    ==> root (dimindex(:N)) (measure {x + y | x IN s /\ y IN t})
        >= root (dimindex(:N)) (measure s) + root (dimindex(:N)) (measure t)]])
   (REPEAT GEN_TAC THEN ASM_CASES_TAC ([[t:real^N->bool = {}]]) THEN
    ASM_SIMP_TAC [BRUNN_MINKOWSKI_OPEN, OPEN_EMPTY, BOUNDED_EMPTY] THEN
    STRIP_TAC THEN REWRITE_TAC [real_ge] THEN
    ASM_CASES_TAC ([[measure(s:real^N->bool) = &0]]) THENL
     [ASM_SIMP_TAC [ROOT_0, DIMINDEX_NONZERO, REAL_ADD_LID] THEN
      MATCH_MP_TAC ROOT_MONO_LE THEN
      ASM_SIMP_TAC [DIMINDEX_NONZERO, MEASURE_POS_LE] THEN
      SUBGOAL_THEN ([[?a:real^N. a IN s]]) STRIP_ASSUME_TAC THENL
       [HolLight.ASM SET_TAC [], ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC ([[measure(IMAGE (\x:real^N. a + x) t)]]) THEN CONJ_TAC THENL
       [ASM_SIMP_TAC [MEASURE_TRANSLATION, REAL_LE_REFL],
        MATCH_MP_TAC MEASURE_SUBSET THEN
        ASM_REWRITE_TAC [MEASURABLE_TRANSLATION_EQ] THEN
        HolLight.ASM SET_TAC []],
      ALL_TAC] THEN
    ASM_CASES_TAC ([[measure(t:real^N->bool) = &0]]) THENL
     [ASM_SIMP_TAC [ROOT_0, DIMINDEX_NONZERO, REAL_ADD_RID] THEN
      MATCH_MP_TAC ROOT_MONO_LE THEN
      ASM_SIMP_TAC [DIMINDEX_NONZERO, MEASURE_POS_LE] THEN
      SUBGOAL_THEN ([[?a:real^N. a IN t]]) STRIP_ASSUME_TAC THENL
       [HolLight.ASM SET_TAC [], ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC ([[measure(IMAGE (\x:real^N. a + x) s)]]) THEN CONJ_TAC THENL
       [ASM_SIMP_TAC [MEASURE_TRANSLATION, REAL_LE_REFL],
        MATCH_MP_TAC MEASURE_SUBSET THEN
        ASM_REWRITE_TAC [MEASURABLE_TRANSLATION_EQ] THEN
        GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [VECTOR_ADD_SYM] THEN
        HolLight.ASM SET_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN
     ([[&0 < measure(s:real^N->bool) /\
      &0 < measure(t:real^N->bool)]])
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC [MEASURABLE_MEASURE_POS_LT, MEASURABLE_MEASURE_EQ_0],
      ALL_TAC] THEN
    MATCH_MP_TAC (← HolLight.ISPEC ([[atreal(&0) within {e | &0 <= e}]]) SessionMultiLib.RealAnalysis.REALLIM_UBOUND) THEN
    EXISTS_TAC ([[\e. root (dimindex(:N)) (measure(s:real^N->bool) - e) +
                    root (dimindex(:N)) (measure(t:real^N->bool) - e)]]) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
      EXISTS_TAC
       ([[\e. (measure(s:real^N->bool) - e) rpow (inv(&(dimindex(:N)))) +
            (measure(t:real^N->bool) - e) rpow (inv(&(dimindex(:N))))]]) THEN
      REWRITE_TAC [] THEN CONJ_TAC THENL
       [REWRITE_TAC [EVENTUALLY_WITHINREAL] THEN
        EXISTS_TAC ([[min (measure(s:real^N->bool)) (measure(t:real^N->bool))]]) THEN
        ASM_SIMP_TAC [REAL_LT_MIN, IN_ELIM_THM, REAL_SUB_RZERO,
                     MEASURE_OPEN_POS_LT] THEN
        REPEAT STRIP_TAC THEN BINOP_TAC THEN CONV_TAC HolLight.SYM_CONV THEN
        MATCH_MP_TAC REAL_ROOT_RPOW THEN
        REWRITE_TAC [DIMINDEX_NONZERO] THEN ASM_REAL_ARITH_TAC,
        ASM_SIMP_TAC [REAL_ROOT_RPOW, MEASURE_OPEN_POS_LT, DIMINDEX_NONZERO,
                     REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THEN
        GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV)
         [h1] THEN
        REWRITE_TAC [(← HolLight.GSYM REAL_CONTINUOUS_WITHINREAL)] THEN
        REWRITE_TAC [(← HolLight.GSYM (← ExceptT.mk (REWRITE_CONV [o_DEF]
          ([[(\x. x rpow y) o (\e. s - e)]]))))] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_COMPOSE THEN
        ASM_SIMP_TAC [REAL_CONTINUOUS_SUB, REAL_CONTINUOUS_WITHIN_ID,
                     REAL_CONTINUOUS_CONST] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_WITHIN_RPOW THEN
        REWRITE_TAC [REAL_LE_INV_EQ, REAL_POS]],
      HolCore.Lib.W (MP_TAC o HolLight.PART_MATCH (HolCore.Equal.lhand o HolCore.Kernel.rand)
        TRIVIAL_LIMIT_WITHIN_REALINTERVAL o
        HolCore.Kernel.rand o HolLight.snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC [is_realinterval, IN_ELIM_THM] THEN REAL_ARITH_TAC2,
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [EXTENSION, IN_SING] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[&1]])) THEN REWRITE_TAC [IN_ELIM_THM] THEN
        REAL_ARITH_TAC2],
      REWRITE_TAC [EVENTUALLY_WITHINREAL] THEN
      EXISTS_TAC ([[min (measure(s:real^N->bool)) (measure(t:real^N->bool))]]) THEN
      ASM_SIMP_TAC [REAL_LT_MIN, IN_ELIM_THM, REAL_SUB_RZERO] THEN
      X_GEN_TAC ([[e:real]]) THEN REWRITE_TAC [real_abs] THEN
      ASM_CASES_TAC ([[&0 <= e]]) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
      MAP_EVERY (fun l => HolLight.tactic_of do
          pure (MP_TAC (← HolLight.ISPECL l MEASURABLE_INNER_COMPACT)))
      [ [([[t:real^N->bool]]), ([[e:real]])], [([[s:real^N->bool]]), ([[e:real]])] ] THEN
      ASM_SIMP_TAC [MEASURABLE_OPEN, (← HolLight.GSYM REAL_LT_SUB_RADD)] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[s':real^N->bool]]) STRIP_ASSUME_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[t':real^N->bool]]) STRIP_ASSUME_TAC) THEN
      MP_TAC (← HolLight.ISPECL [([[s':real^N->bool]]), ([[t':real^N->bool]])]
          BRUNN_MINKOWSKI_COMPACT) THEN
      ANTS_TAC THENL
       [ASM_MESON_TAC [MEASURE_EMPTY, h2],
        ALL_TAC] THEN
      MATCH_MP_TAC h3 THEN
      REPEAT CONJ_TAC THEN MATCH_MP_TAC ROOT_MONO_LE THEN
      ASM_SIMP_TAC [DIMINDEX_NONZERO, REAL_SUB_LE, REAL_LT_IMP_LE] THEN
      ASM_SIMP_TAC [MEASURE_POS_LE, COMPACT_SUMS, MEASURABLE_COMPACT] THEN
      MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_SIMP_TAC [MEASURE_POS_LE, COMPACT_SUMS, MEASURABLE_COMPACT] THEN
      HolLight.ASM SET_TAC []])
  : ExceptT String IO thm).run
#eval BRUNN_MINKOWSKI_MEASURABLE

end HolExamples.BrunnMinkowski
