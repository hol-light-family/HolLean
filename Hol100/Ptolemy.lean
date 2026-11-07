/- File: Hol100/Ptolemy.lean
Translation of HOL Light's 100/ptolemy.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionMultiLib.Transcendentals
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Permutations SessionLibrary.Floor SessionLibrary.Iter SessionLibrary.Wo SessionLibrary.Products SessionLibrary.Frag SessionLibrary.Prime SessionLibrary.Card SessionLibrary.Matroids SessionMultiLib.Misc SessionLibrary.GroupTheory SessionMultiLib.Vectors SessionMultiLib.Metric SessionMultiLib.Determinants SessionMultiLib.Homology SessionMultiLib.Topology SessionMultiLib.Convex SessionMultiLib.Complexes SessionMultiLib.Paths SessionMultiLib.Polytope SessionMultiLib.Degree SessionMultiLib.Derivatives SessionMultiLib.Integration SessionMultiLib.Measure SessionMultiLib.Canal SessionMultiLib.Transcendentals
namespace Hol100.Ptolemy

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)
/-- `find_term` with an IO predicate (`can` of an IO rule). -/
private partial def find_termIO (p : term → IO Bool) (tm : term) : IO (Except String term) := do
  if ← p tm then return .ok tm
  else if is_abs tm then
    match HolCore.Basics.body tm with
    | .ok bod => find_termIO p bod
    | .error _ => return .error "find_term"
  else if is_comb tm then
    match dest_comb tm with
    | .ok (l, r) =>
        match ← find_termIO p l with
        | .ok found => return .ok found
        | .error _  => find_termIO p r
    | .error _ => return .error "find_term"
  else return .error "find_term"
private def va (tm : term) : ExceptT String IO thm := ExceptT.mk (VECTOR_ARITH tm)

/- ========================================================================= -/
/- Ptolemy's theorem.                                                        -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Multivariate/transcendentals.ml";;
#eval SessionMultiLib.Transcendentals.ensureTranscendentals

/- ------------------------------------------------------------------------- -/
/- Some 2-vector special cases.                                              -/
/- ------------------------------------------------------------------------- -/

#eval phrase 2
def DOT_VECTOR : thm := keep "DOT_VECTOR" fun _ => (do
  prove ([[(vector [x1;y1] :real^2) dot (vector [x2;y2]) = x1 * x2 + y1 * y2]])
   (REWRITE_TAC [dot, DIMINDEX_2, SUM_2, VECTOR_2])
  : ExceptT String IO thm).run
#eval DOT_VECTOR

/- ------------------------------------------------------------------------- -/
/- Lemma about distance between points with polar coordinates.               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 3
def DIST_SEGMENT_LEMMA : thm := keep "DIST_SEGMENT_LEMMA" fun _ => (do
  let h5 ← rr (← ExceptT.mk [[(&2 * x - &2 * y) / &2 = x - y]])
  let h4 ← rr (← ExceptT.mk [[a2 = &2 * a2 / &2]])
  let h3 ← rr (← ExceptT.mk [[a1 = &2 * a1 / &2]])
  let h2 ← va (← ExceptT.mk [[(r % x) dot (r % x) = (r pow 2) * (x dot x)]])
  let h1 ← va (← ExceptT.mk [[(c + r % x) - (c + r % y) = r % (x - y)]])
  prove ([[!a1 a2. &0 <= a1 /\ a1 <= a2 /\ a2 <= &2 * pi /\ &0 <= radius
           ==> dist(centre + radius % vector [cos(a1);sin(a1)] :real^2,
                    centre + radius % vector [cos(a2);sin(a2)]) =
               &2 * radius *  sin((a2 - a1) / &2)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [SessionMultiLib.Vectors.dist, vector_norm] THEN
    MATCH_MP_TAC SQRT_UNIQUE THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC [REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC SIN_POS_PI_LE THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [h1] THEN
    REWRITE_TAC [h2] THEN
    REWRITE_TAC [DOT_LSUB, DOT_RSUB, DOT_VECTOR] THEN
    SUBST1_TAC h3 THEN
    SUBST1_TAC h4 THEN
    REWRITE_TAC [h5] THEN
    REWRITE_TAC [SIN_SUB, SIN_DOUBLE, COS_DOUBLE] THEN
    MP_TAC (← HolLight.SPEC ([[a1 / &2]]) SIN_CIRCLE) THEN MP_TAC (← HolLight.SPEC ([[a2 / &2]]) SIN_CIRCLE) THEN
    CONV_TAC REAL_RING)
  : ExceptT String IO thm).run
#eval DIST_SEGMENT_LEMMA

/- ------------------------------------------------------------------------- -/
/- Hence the overall theorem.                                                -/
/- ------------------------------------------------------------------------- -/

#eval phrase 4
def PTOLEMY : thm := keep "PTOLEMY" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[(x - y) / &2 = x / &2 - y / &2]])
  prove ([[!A B C D:real^2 a b c d centre radius.
        A = centre + radius % vector [cos(a);sin(a)] /\
        B = centre + radius % vector [cos(b);sin(b)] /\
        C = centre + radius % vector [cos(c);sin(c)] /\
        D = centre + radius % vector [cos(d);sin(d)] /\
        &0 <= radius /\
        &0 <= a /\ a <= b /\ b <= c /\ c <= d /\ d <= &2 * pi
        ==> dist(A,C) * dist(B,D) =
            dist(A,B) * dist(C,D) + dist(A,D) * dist(B,C)]])
   (REPEAT STRIP_TAC THEN
    REPEAT (FIRST_X_ASSUM (SUBST1_TAC o check (HolCore.Kernel.is_var o HolCore.Equal.lhs o concl))) THEN
    REPEAT (HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
        let t ← ExceptT.mk (find_termIO (fun t => do pure ((← HolLight.PART_MATCH (HolCore.Equal.lhs o HolCore.Kernel.rand) DIST_SEGMENT_LEMMA t) matches .ok _)) w)
        pure (MP_TAC (← HolLight.PART_MATCH (HolCore.Equal.lhs o HolCore.Kernel.rand) DIST_SEGMENT_LEMMA t) THEN
       ANTS_TAC THENL
        [ASM_REAL_ARITH_TAC,
         DISCH_THEN SUBST1_TAC]))) THEN
    REWRITE_TAC [h1] THEN
    MAP_EVERY (fun t => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPEC t SIN_CIRCLE))) [([[a / &2]]), ([[b / &2]]), ([[c / &2]]), ([[d / &2]])] THEN
    REWRITE_TAC [SIN_SUB, SIN_ADD, COS_ADD, SIN_PI, COS_PI] THEN
    CONV_TAC REAL_RING)
  : ExceptT String IO thm).run
#eval PTOLEMY

end Hol100.Ptolemy
