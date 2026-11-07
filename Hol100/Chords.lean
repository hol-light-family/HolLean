/- File: Hol100/Chords.lean
Translation of HOL Light's 100/chords.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionMultiLib.Convex
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Floor SessionLibrary.Wo SessionLibrary.Permutations SessionLibrary.Products SessionLibrary.Iter SessionLibrary.Card SessionLibrary.Matroids SessionMultiLib.Misc SessionMultiLib.Vectors SessionMultiLib.Metric SessionMultiLib.Determinants SessionMultiLib.Topology SessionMultiLib.Convex
namespace Hol100.Chords

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def sr (tm : term) : ExceptT String IO thm := ExceptT.mk (SET_RULE tm)

/- ========================================================================= -/
/- #55: Theorem on product of segments of chords.                            -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Multivariate/convex.ml";;
#eval SessionMultiLib.Convex.ensureConvex

#eval phrase 2
#eval Session.prioritize_real

/- ------------------------------------------------------------------------- -/
/- Geometric concepts.                                                       -/
/- ------------------------------------------------------------------------- -/

#eval phrase 3
def BETWEEN_THM : thm := keep "BETWEEN_THM" fun _ => (do
  let h1 ← sr (← ExceptT.mk [[{a,b} = {b,a}]])
  prove ([[between x (a,b) <=>
       ?u. &0 <= u /\ u <= &1 /\ x = u % a + (&1 - u) % b]])
   (REWRITE_TAC [BETWEEN_IN_CONVEX_HULL] THEN
    ONCE_REWRITE_TAC [h1] THEN
    REWRITE_TAC [CONVEX_HULL_2_ALT, IN_ELIM_THM] THEN
    AP_TERM_TAC THEN ABS_TAC THEN REWRITE_TAC [CONJ_ASSOC] THEN
    AP_TERM_TAC THEN VECTOR_ARITH_TAC)
  : ExceptT String IO thm).run
#eval BETWEEN_THM

#eval phrase 4
def length : thm := keep "length" fun _ => new_definition
 [[length(A:real^2,B:real^2) = norm(B - A)]]
#eval length

/- ------------------------------------------------------------------------- -/
/- One more special reduction theorem to avoid square roots.                 -/
/- ------------------------------------------------------------------------- -/

#eval phrase 5
def lemma : thm := keep "lemma" fun _ => (do
  prove ([[!x y. &0 <= x /\ &0 <= y ==> (x pow 2 = y pow 2 <=> x = y)]])
   (REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC [REAL_POW_2] THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (← HolLight.SPECL [([[x:real]]), ([[y:real]])] REAL_LT_TOTAL) THEN
    ASM_MESON_TAC [REAL_LT_MUL2, REAL_LT_REFL])
  : ExceptT String IO thm).run
#eval lemma

#eval phrase 6
def NORM_CROSS : thm := keep "NORM_CROSS" fun _ => (do
  prove ([[norm(a) * norm(b) = norm(c) * norm(d) <=>
   (a dot a) * (b dot b) = (c dot c) * (d dot d)]])
   (REWRITE_TAC [(← HolLight.GSYM NORM_POW_2), (← HolLight.GSYM REAL_POW_MUL)] THEN
    MATCH_MP_TAC (← HolLight.GSYM lemma) THEN SIMP_TAC [NORM_POS_LE, REAL_LE_MUL])
  : ExceptT String IO thm).run
#eval NORM_CROSS

/- ------------------------------------------------------------------------- -/
/- Now the main theorem.                                                     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 7
def SEGMENT_CHORDS : thm := keep "SEGMENT_CHORDS" fun _ => (do
  prove ([[!centre radius q r s t b.
        between b (q,r) /\ between b (s,t) /\
        length(q,centre) = radius /\ length(r,centre) = radius /\
        length(s,centre) = radius /\ length(t,centre) = radius
        ==> length(q,b) * length(b,r) = length(s,b) * length(b,t)]])
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [length, NORM_CROSS, BETWEEN_THM] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN ([[u:real]]) STRIP_ASSUME_TAC) MP_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN ([[v:real]]) STRIP_ASSUME_TAC) MP_TAC) THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN (MP_TAC o HolLight.AP_TERM ([[\x. x pow 2]]))) THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SYM) THEN REWRITE_TAC [NORM_POW_2] THEN
    ABBREV_TAC ([[rad = radius pow 2]]) THEN POP_ASSUM_LIST ((fun _ => ALL_TAC)) THEN
    SIMP_TAC [dot, SUM_2, VECTOR_SUB_COMPONENT, DIMINDEX_2, VECTOR_ADD_COMPONENT,
             CART_EQ, FORALL_2, VECTOR_MUL_COMPONENT, ARITH] THEN
    CONV_TAC REAL_RING)
  : ExceptT String IO thm).run
#eval SEGMENT_CHORDS

end Hol100.Chords
