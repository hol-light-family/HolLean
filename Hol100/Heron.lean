/- File: Hol100/Heron.lean
Translation of HOL Light's 100/heron.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionMultiLib.Measure
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Permutations SessionLibrary.Wo SessionLibrary.Products SessionLibrary.Floor SessionLibrary.Frag SessionLibrary.Iter SessionLibrary.Prime SessionLibrary.Card SessionLibrary.Matroids SessionMultiLib.Misc SessionLibrary.GroupTheory SessionMultiLib.Vectors SessionMultiLib.Metric SessionMultiLib.Determinants SessionMultiLib.Homology SessionMultiLib.Topology SessionMultiLib.Convex SessionMultiLib.Paths SessionMultiLib.Polytope SessionMultiLib.Degree SessionMultiLib.Derivatives SessionMultiLib.Integration SessionMultiLib.Measure
namespace Hol100.Heron

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- ========================================================================= -/
/- Heron's formula for the area of a triangle.                               -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Multivariate/measure.ml";;
#eval SessionMultiLib.Measure.ensureMeasure

#eval phrase 2
#eval Session.prioritize_real

/- ------------------------------------------------------------------------- -/
/- Eliminate square roots from formula by the usual method.                  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 3
-- let SQRT_ELIM_TAC = ...;;
def SQRT_ELIM_TAC : HolCore.Tactics.tactic := fun (asl, w) => HolLight.tactic_of (do
  let sqrt_tm ← ExceptT.mk [[sqrt:real->real]]
  let is_sqrt (tm : term) : Bool :=
    is_comb tm && (match HolCore.Kernel.rator tm with | .ok r => r == sqrt_tm | .error _ => false)
  let stms := HolCore.Lib.setify (HolCore.Basics.find_terms is_sqrt w)
  let gvs ← ExceptT.lift (stms.mapM fun t => HolCore.Basics.genvar (type_of t))
  pure (MAP_EVERY (MP_TAC o (fun t => HolLight.SPEC t SQRT_POW_2) o HolCore.Kernel.rand) stms THEN
        EVERY ((stms.zip gvs).map fun (s, v) => SPEC_TAC (s, v)))) (asl, w)
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- Main result.                                                              -/
/- ------------------------------------------------------------------------- -/

#eval phrase 4
def HERON : thm := keep "HERON" fun _ => (do
  prove ([[!A B C:real^2.
        let a = dist(C,B)
        and b = dist(A,C)
        and c = dist(B,A) in
        let s = (a + b + c) / &2 in
        measure(convex hull {A,B,C}) = sqrt(s * (s - a) * (s - b) * (s - c))]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [LET_DEF, LET_END_DEF] THEN
    REWRITE_TAC [MEASURE_TRIANGLE] THEN
    CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC SQRT_UNIQUE THEN
    SIMP_TAC [REAL_LE_DIV, REAL_ABS_POS, REAL_POS] THEN
    REWRITE_TAC [REAL_POW_DIV, REAL_POW2_ABS] THEN
    REWRITE_TAC [SessionMultiLib.Vectors.dist, vector_norm] THEN
    REWRITE_TAC [dot, SUM_2, DIMINDEX_2] THEN
    SIMP_TAC [VECTOR_SUB_COMPONENT, ARITH, DIMINDEX_2] THEN
    SQRT_ELIM_TAC THEN SIMP_TAC [REAL_LE_SQUARE, REAL_LE_ADD] THEN
    CONV_TAC REAL_RING)
  : ExceptT String IO thm).run
#eval HERON

end Hol100.Heron
