/- File: Hol100/Polyhedron.lean
Translation of HOL Light's 100/polyhedron.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionMultiLib.Polytope
import SessionLibrary.Binomial
import Hol100.InclusionExclusion
import Hol100.Combinations
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Binomial SessionLibrary.Frag SessionLibrary.Iter SessionLibrary.Floor SessionLibrary.Wo SessionLibrary.Prime SessionLibrary.Products SessionLibrary.Permutations SessionLibrary.Card Hol100.InclusionExclusion SessionLibrary.Matroids Hol100.Combinations SessionMultiLib.Misc SessionLibrary.GroupTheory SessionMultiLib.Vectors SessionMultiLib.Metric SessionMultiLib.Determinants SessionMultiLib.Homology SessionMultiLib.Topology SessionMultiLib.Convex SessionMultiLib.Paths SessionMultiLib.Polytope
namespace Hol100.Polyhedron

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def ia (tm : term) : ExceptT String IO thm := ExceptT.mk (INT_ARITH tm)
private def ms (ths : List thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (MESON ths tm)
private def na (tm : term) : ExceptT String IO thm := ExceptT.mk (NORM_ARITH tm)
private def rg (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_RING tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)
private def sr (tm : term) : ExceptT String IO thm := ExceptT.mk (SET_RULE tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)
private def va (tm : term) : ExceptT String IO thm := ExceptT.mk (VECTOR_ARITH tm)

/- ========================================================================= -/
/- Formalization of Jim Lawrence's proof of Euler's relation.                -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Multivariate/polytope.ml";;
#eval SessionMultiLib.Polytope.ensurePolytope

#eval phrase 2
-- needs "Library/binomial.ml";;
#eval SessionLibrary.Binomial.ensureBinomial

#eval phrase 3
-- needs "100/inclusion_exclusion.ml";;
#eval Hol100.InclusionExclusion.ensure

#eval phrase 4
-- needs "100/combinations.ml";;
#eval Hol100.Combinations.ensure

#eval phrase 5
#eval Session.prioritize_real

/- ------------------------------------------------------------------------- -/
/- Interpret which "side" of a hyperplane a point is on.                     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 6
def hyperplane_side : thm := keep "hyperplane_side" fun _ => new_definition
 [[hyperplane_side (a,b) (x:real^N) = real_sgn (a dot x - b)]]
#eval hyperplane_side

/- ------------------------------------------------------------------------- -/
/- Equivalence relation imposed by a hyperplane arrangement.                 -/
/- ------------------------------------------------------------------------- -/

#eval phrase 7
def hyperplane_equiv : thm := keep "hyperplane_equiv" fun _ => new_definition
 [[hyperplane_equiv A x y <=>
        !h. h IN A ==> hyperplane_side h x = hyperplane_side h y]]
#eval hyperplane_equiv

#eval phrase 8
def HYPERPLANE_EQUIV_REFL : thm := keep "HYPERPLANE_EQUIV_REFL" fun _ => (do
  prove ([[!A x. hyperplane_equiv A x x]])
   (REWRITE_TAC [hyperplane_equiv])
  : ExceptT String IO thm).run
#eval HYPERPLANE_EQUIV_REFL

#eval phrase 9
def HYPERPLANE_EQUIV_SYM : thm := keep "HYPERPLANE_EQUIV_SYM" fun _ => (do
  prove ([[!A x y. hyperplane_equiv A x y <=> hyperplane_equiv A y x]])
   (REWRITE_TAC [hyperplane_equiv, EQ_SYM_EQ])
  : ExceptT String IO thm).run
#eval HYPERPLANE_EQUIV_SYM

#eval phrase 10
def HYPERPLANE_EQUIV_TRANS : thm := keep "HYPERPLANE_EQUIV_TRANS" fun _ => (do
  prove ([[!A x y z.
        hyperplane_equiv A x y /\ hyperplane_equiv A y z
        ==> hyperplane_equiv A x z]])
   (REWRITE_TAC [hyperplane_equiv] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval HYPERPLANE_EQUIV_TRANS

#eval phrase 11
def HYPERPLANE_EQUIV_UNION : thm := keep "HYPERPLANE_EQUIV_UNION" fun _ => (do
  prove ([[!A B x y. hyperplane_equiv (A UNION B) x y <=>
                hyperplane_equiv A x y /\ hyperplane_equiv B x y]])
   (REWRITE_TAC [hyperplane_equiv, IN_UNION] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval HYPERPLANE_EQUIV_UNION

/- ------------------------------------------------------------------------- -/
/- Cells of a hyperplane arrangement.                                        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 12
def hyperplane_cell : thm := keep "hyperplane_cell" fun _ => new_definition
 [[hyperplane_cell A c <=> ?x. c = hyperplane_equiv A x]]
#eval hyperplane_cell

#eval phrase 13
def HYPERPLANE_CELL : thm := keep "HYPERPLANE_CELL" fun _ => (do
  prove ([[hyperplane_cell A c <=> ?x. c = {y | hyperplane_equiv A x y}]])
   (REWRITE_TAC [EXTENSION, hyperplane_cell, IN_ELIM_THM, IN] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval HYPERPLANE_CELL

#eval phrase 14
def NOT_HYPERPLANE_CELL_EMPTY : thm := keep "NOT_HYPERPLANE_CELL_EMPTY" fun _ => (do
  prove ([[!A. ~(hyperplane_cell A {})]])
   (REWRITE_TAC [hyperplane_cell, EXTENSION, NOT_IN_EMPTY] THEN
    MESON_TAC [HYPERPLANE_EQUIV_REFL, IN])
  : ExceptT String IO thm).run
#eval NOT_HYPERPLANE_CELL_EMPTY

#eval phrase 15
def NONEMPTY_HYPERPLANE_CELL : thm := keep "NONEMPTY_HYPERPLANE_CELL" fun _ => (do
  prove ([[!A c. hyperplane_cell A c ==> ~(c = {})]])
   (MESON_TAC [NOT_HYPERPLANE_CELL_EMPTY])
  : ExceptT String IO thm).run
#eval NONEMPTY_HYPERPLANE_CELL

#eval phrase 16
def UNIONS_HYPERPLANE_CELLS : thm := keep "UNIONS_HYPERPLANE_CELLS" fun _ => (do
  prove ([[!A. UNIONS {c | hyperplane_cell A c} = (:real^N)]])
   (REWRITE_TAC [EXTENSION, IN_UNIONS, IN_UNIV, IN_ELIM_THM] THEN
    REWRITE_TAC [hyperplane_cell] THEN MESON_TAC [HYPERPLANE_EQUIV_REFL, IN])
  : ExceptT String IO thm).run
#eval UNIONS_HYPERPLANE_CELLS

#eval phrase 17
def DISJOINT_HYPERPLANE_CELLS : thm := keep "DISJOINT_HYPERPLANE_CELLS" fun _ => (do
  prove ([[!A c1 c2. hyperplane_cell A c1 /\ hyperplane_cell A c2 /\ ~(c1 = c2)
             ==> DISJOINT c1 c2]])
   (REWRITE_TAC [hyperplane_cell] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o check (HolCore.Basics.is_neg o concl)) THEN
    ASM_REWRITE_TAC [IN_DISJOINT, IN, EXTENSION] THEN
    ASM_MESON_TAC [HYPERPLANE_EQUIV_TRANS, HYPERPLANE_EQUIV_SYM])
  : ExceptT String IO thm).run
#eval DISJOINT_HYPERPLANE_CELLS

#eval phrase 18
def DISJOINT_HYPERPLANE_CELLS_EQ : thm := keep "DISJOINT_HYPERPLANE_CELLS_EQ" fun _ => (do
  let h1 ← sr (← ExceptT.mk [[DISJOINT s s <=> s = {}]])
  prove ([[!A c1 c2. hyperplane_cell A c1 /\ hyperplane_cell A c2
             ==> (DISJOINT c1 c2 <=> ~(c1 = c2))]])
   (MESON_TAC [NONEMPTY_HYPERPLANE_CELL, DISJOINT_HYPERPLANE_CELLS,
              h1])
  : ExceptT String IO thm).run
#eval DISJOINT_HYPERPLANE_CELLS_EQ

#eval phrase 19
def HYPERPLANE_CELL_EMPTY : thm := keep "HYPERPLANE_CELL_EMPTY" fun _ => (do
  prove ([[hyperplane_cell {} c <=> c = (:real^N)]])
   (REWRITE_TAC [HYPERPLANE_CELL, NOT_IN_EMPTY, hyperplane_equiv] THEN
    SET_TAC [])
  : ExceptT String IO thm).run
#eval HYPERPLANE_CELL_EMPTY

#eval phrase 20
def HYPERPLANE_CELL_SING_CASES : thm := keep "HYPERPLANE_CELL_SING_CASES" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[x - y < &0 <=> x < y]])
  prove ([[!a b c:real^N->bool.
        hyperplane_cell {(a,b)} c
        ==>  c = {x | a dot x = b} \/
             c = {x | a dot x < b} \/
             c = {x | a dot x > b}]])
   (REWRITE_TAC [HYPERPLANE_CELL, hyperplane_equiv] THEN
    REWRITE_TAC [FORALL_UNWIND_THM2, IN_SING, hyperplane_side] THEN
    REPEAT GEN_TAC THEN DISCH_THEN (X_CHOOSE_THEN ([[y:real^N]]) MP_TAC) THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV o HolLight.ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC (← HolLight.SPEC ([[(a:real^N) dot y - b]]) REAL_SGN_CASES) THEN
    ASM_REWRITE_TAC [REAL_SGN_EQ] THEN
    SIMP_TAC [REAL_SUB_0, REAL_SUB_LT, real_gt,
             h1])
  : ExceptT String IO thm).run
#eval HYPERPLANE_CELL_SING_CASES

#eval phrase 21
def HYPERPLANE_CELL_SING : thm := keep "HYPERPLANE_CELL_SING" fun _ => (do
  let h4 ← ms [] (← ExceptT.mk [[(?x. f x = a) ==> (?x. !y. f y = a <=> f x = f y)]])
  let h3 ← rr (← ExceptT.mk [[a < b <=> a - b < &0]])
  let h2 ← rr (← ExceptT.mk [[a > b <=> a - b > &0]])
  let h1 ← rr (← ExceptT.mk [[a dot x = b <=> a dot x - b = &0]])
  prove ([[!a b c.
        hyperplane_cell {(a,b)} c <=>
        if a = vec 0 then c = (:real^N)
        else c = {x | a dot x = b} \/
             c = {x | a dot x < b} \/
             c = {x | a dot x > b}]])
   (REPEAT GEN_TAC THEN COND_CASES_TAC THENL
     [REWRITE_TAC [hyperplane_cell, hyperplane_equiv, EXTENSION, IN_UNIV] THEN
      REWRITE_TAC [IN] THEN REWRITE_TAC [hyperplane_equiv] THEN
      ASM_SIMP_TAC [IN_SING, FORALL_UNWIND_THM2] THEN
      REWRITE_TAC [hyperplane_side, DOT_LZERO],
      EQ_TAC THEN REWRITE_TAC [HYPERPLANE_CELL_SING_CASES] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [hyperplane_cell, EXTENSION, IN_ELIM_THM] THEN
      REWRITE_TAC [IN] THEN REWRITE_TAC [hyperplane_equiv] THEN
      ASM_SIMP_TAC [IN_SING, FORALL_UNWIND_THM2] THEN
      REWRITE_TAC [hyperplane_side] THEN
      ONCE_REWRITE_TAC [h1,
                       h2,
                       h3] THEN
      ONCE_REWRITE_TAC [(← HolLight.GSYM REAL_SGN_EQ)] THEN REWRITE_TAC [REAL_SUB_0] THEN
      MATCH_MP_TAC h4 THEN
      REWRITE_TAC [REAL_SGN_EQ] THENL
       [EXISTS_TAC ([[b / (a dot a) % a:real^N]]),
        EXISTS_TAC ([[(b - &1) / (a dot a) % a:real^N]]),
        EXISTS_TAC ([[(b + &1) / (a dot a) % a:real^N]])] THEN
      ASM_SIMP_TAC [DOT_RMUL, REAL_DIV_RMUL, DOT_EQ_0] THEN REAL_ARITH_TAC2])
  : ExceptT String IO thm).run
#eval HYPERPLANE_CELL_SING

#eval phrase 22
def HYPERPLANE_CELL_UNION : thm := keep "HYPERPLANE_CELL_UNION" fun _ => (do
  let h2 ← ms [] (← ExceptT.mk [[(?c1 c2. (?x. c1 = f x) /\ (?y. c2 = g y) /\ P c1 c2) <=>
    (?x y. P (f x) (g y))]])
  let h1 ← sr (← ExceptT.mk [[{x | P x /\ Q x} = {x | P x} INTER {x | Q x}]])
  prove ([[!A B c:real^N->bool.
        hyperplane_cell (A UNION B) c <=>
        ~(c = {}) /\
        ?c1 c2. hyperplane_cell A c1 /\
                hyperplane_cell B c2 /\
                c = c1 INTER c2]])
   (REPEAT GEN_TAC THEN ASM_CASES_TAC ([[c:real^N->bool = {}]]) THENL
     [ASM_MESON_TAC [NONEMPTY_HYPERPLANE_CELL], ASM_REWRITE_TAC []] THEN
    REWRITE_TAC [HYPERPLANE_CELL, HYPERPLANE_EQUIV_UNION] THEN
    REWRITE_TAC [h1] THEN
    REWRITE_TAC [h2] THEN
    EQ_TAC THENL [MESON_TAC [], REWRITE_TAC [LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC [([[a:real^N]]), ([[b:real^N]])] THEN
    DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC [(← HolLight.GSYM MEMBER_NOT_EMPTY)] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC ([[x:real^N]]) THEN REWRITE_TAC [EXTENSION, IN_INTER, IN_ELIM_THM] THEN
    MESON_TAC [HYPERPLANE_EQUIV_TRANS, HYPERPLANE_EQUIV_SYM])
  : ExceptT String IO thm).run
#eval HYPERPLANE_CELL_UNION

#eval phrase 23
def FINITE_HYPERPLANE_CELLS : thm := keep "FINITE_HYPERPLANE_CELLS" fun _ => (do
  let h1 ← sr (← ExceptT.mk [[a INSERT s = {a} UNION s]])
  prove ([[!A. FINITE A ==> FINITE {c:real^N->bool | hyperplane_cell A c}]])
   (MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [HYPERPLANE_CELL_EMPTY, SING_GSPEC, FINITE_SING] THEN
    REWRITE_TAC [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [([[a:real^N]]), ([[b:real]]), ([[A:(real^N#real)->bool]])] THEN
    STRIP_TAC THEN ONCE_REWRITE_TAC [h1] THEN
    REWRITE_TAC [HYPERPLANE_CELL_UNION] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC ([[{ c1 INTER c2:real^N->bool |
                c1 IN {c | hyperplane_cell A c} /\
                c2 IN {c | hyperplane_cell {(a,b)} c}}]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN
      ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC ([[{{x:real^N | a dot x = b},{x | a dot x < b},{x | a dot x > b}}]]) THEN
      REWRITE_TAC [SUBSET, IN_SING, HYPERPLANE_CELL_SING_CASES, IN_ELIM_THM,
                  IN_INSERT, NOT_IN_EMPTY, FINITE_INSERT, FINITE_EMPTY],
      REWRITE_TAC [IN_ELIM_THM, SUBSET] THEN MESON_TAC [INTER_COMM]])
  : ExceptT String IO thm).run
#eval FINITE_HYPERPLANE_CELLS

#eval phrase 24
def FINITE_RESTRICT_HYPERPLANE_CELLS : thm := keep "FINITE_RESTRICT_HYPERPLANE_CELLS" fun _ => (do
  prove ([[!P A. FINITE A ==> FINITE {c:real^N->bool | hyperplane_cell A c /\ P c}]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC ([[{c:real^N->bool | hyperplane_cell A c}]]) THEN
    ASM_SIMP_TAC [FINITE_HYPERPLANE_CELLS] THEN SET_TAC [])
  : ExceptT String IO thm).run
#eval FINITE_RESTRICT_HYPERPLANE_CELLS

#eval phrase 25
def FINITE_SET_OF_HYPERPLANE_CELLS : thm := keep "FINITE_SET_OF_HYPERPLANE_CELLS" fun _ => (do
  prove ([[!A C. FINITE A /\ (!c:real^N->bool. c IN C ==> hyperplane_cell A c)
         ==> FINITE C]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC ([[{c:real^N->bool | hyperplane_cell A c}]]) THEN
    ASM_SIMP_TAC [FINITE_HYPERPLANE_CELLS] THEN HolLight.ASM SET_TAC [])
  : ExceptT String IO thm).run
#eval FINITE_SET_OF_HYPERPLANE_CELLS

#eval phrase 26
def PAIRWISE_DISJOINT_HYPERPLANE_CELLS : thm := keep "PAIRWISE_DISJOINT_HYPERPLANE_CELLS" fun _ => (do
  prove ([[!A C. (!c. c IN C ==> hyperplane_cell A c)
         ==> pairwise DISJOINT C]])
   (REWRITE_TAC [pairwise] THEN MESON_TAC [DISJOINT_HYPERPLANE_CELLS])
  : ExceptT String IO thm).run
#eval PAIRWISE_DISJOINT_HYPERPLANE_CELLS

#eval phrase 27
def HYPERPLANE_CELL_INTER_OPEN_AFFINE : thm := keep "HYPERPLANE_CELL_INTER_OPEN_AFFINE" fun _ => (do
  let h1 ← sr (← ExceptT.mk [[a INSERT s = {a} UNION s]])
  prove ([[!A c:real^N->bool.
        FINITE A /\ hyperplane_cell A c
        ==> ?s t. open s /\ affine t /\ c = s INTER t]])
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
     [REWRITE_TAC [HYPERPLANE_CELL_EMPTY] THEN REPEAT STRIP_TAC THEN
      REPEAT (EXISTS_TAC ([[(:real^N)]])) THEN
      ASM_REWRITE_TAC [AFFINE_UNIV, OPEN_UNIV, INTER_UNIV],
      ALL_TAC] THEN
    REWRITE_TAC [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [([[a:real^N]]), ([[b:real]]), ([[A:real^N#real->bool]])] THEN
    STRIP_TAC THEN ONCE_REWRITE_TAC [h1] THEN
    REWRITE_TAC [HYPERPLANE_CELL_UNION] THEN X_GEN_TAC ([[c':real^N->bool]]) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [([[c1:real^N->bool]]), ([[c:real^N->bool]])] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[c:real^N->bool]])) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [([[s:real^N->bool]]), ([[t:real^N->bool]])] THEN
    STRIP_TAC THEN REWRITE_TAC [HYPERPLANE_CELL_SING] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THENL
     [MAP_EVERY EXISTS_TAC [([[s:real^N->bool]]), ([[t:real^N->bool]])] THEN
      ASM_REWRITE_TAC [INTER_UNIV],
      MAP_EVERY EXISTS_TAC [([[s:real^N->bool]]), ([[{x:real^N | a dot x = b} INTER t]])] THEN
      ASM_REWRITE_TAC [INTER_ACI] THEN MATCH_MP_TAC AFFINE_INTER THEN
      ASM_REWRITE_TAC [AFFINE_HYPERPLANE],
      MAP_EVERY EXISTS_TAC [([[{x:real^N | a dot x < b} INTER s]]), ([[t:real^N->bool]])] THEN
      ASM_REWRITE_TAC [INTER_ACI] THEN MATCH_MP_TAC OPEN_INTER THEN
      ASM_REWRITE_TAC [OPEN_HALFSPACE_LT],
      MAP_EVERY EXISTS_TAC [([[{x:real^N | a dot x > b} INTER s]]), ([[t:real^N->bool]])] THEN
      ASM_REWRITE_TAC [INTER_ACI] THEN MATCH_MP_TAC OPEN_INTER THEN
      ASM_REWRITE_TAC [OPEN_HALFSPACE_GT]])
  : ExceptT String IO thm).run
#eval HYPERPLANE_CELL_INTER_OPEN_AFFINE

#eval phrase 28
def HYPERPLANE_CELL_RELATIVELY_OPEN : thm := keep "HYPERPLANE_CELL_RELATIVELY_OPEN" fun _ => (do
  prove ([[!A c:real^N->bool.
        FINITE A /\ hyperplane_cell A c
        ==> open_in (subtopology euclidean (affine hull c)) c]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP HYPERPLANE_CELL_INTER_OPEN_AFFINE) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [([[s:real^N->bool]]), ([[t:real^N->bool]])] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_CASES_TAC ([[s INTER t:real^N->bool = {}]]) THEN
    ASM_REWRITE_TAC [OPEN_IN_EMPTY] THEN
    SUBGOAL_THEN ([[affine hull (s INTER t:real^N->bool) = t]]) SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC ([[affine hull t:real^N->bool]]) THEN
      ASM_REWRITE_TAC [AFFINE_HULL_EQ] THEN
      MATCH_MP_TAC (← HolLight.ONCE_REWRITE_RULE [INTER_COMM] AFFINE_HULL_CONVEX_INTER_OPEN) THEN
      ASM_SIMP_TAC [AFFINE_IMP_CONVEX],
      ONCE_REWRITE_TAC [INTER_COMM] THEN ASM_SIMP_TAC [OPEN_IN_OPEN_INTER]])
  : ExceptT String IO thm).run
#eval HYPERPLANE_CELL_RELATIVELY_OPEN

#eval phrase 29
def HYPERPLANE_CELL_RELATIVE_INTERIOR : thm := keep "HYPERPLANE_CELL_RELATIVE_INTERIOR" fun _ => (do
  prove ([[!A c:real^N->bool.
        FINITE A /\ hyperplane_cell A c
        ==> relative_interior c = c]])
   (MESON_TAC [RELATIVE_INTERIOR_OPEN_IN, HYPERPLANE_CELL_RELATIVELY_OPEN])
  : ExceptT String IO thm).run
#eval HYPERPLANE_CELL_RELATIVE_INTERIOR

#eval phrase 30
def HYPERPLANE_CELL_CONVEX : thm := keep "HYPERPLANE_CELL_CONVEX" fun _ => (do
  let h3 ← rr (← ExceptT.mk [[a - b < &0 <=> a < b]])
  let h2 ← rr (← ExceptT.mk [[a - b > &0 <=> a > b]])
  let h1 ← sr (← ExceptT.mk [[f x = f y <=> y IN {y | f x = f y}]])
  prove ([[!A c:real^N->bool. hyperplane_cell A c ==> convex c]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [HYPERPLANE_CELL] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[c:real^N]]) SUBST1_TAC) THEN
    REWRITE_TAC [hyperplane_equiv] THEN
    ONCE_REWRITE_TAC [h1] THEN
    REWRITE_TAC [(← HolLight.GSYM INTERS_IMAGE)] THEN MATCH_MP_TAC CONVEX_INTERS THEN
    REWRITE_TAC [FORALL_IN_IMAGE] THEN REWRITE_TAC [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [([[a:real^N]]), ([[b:real]])] THEN DISCH_TAC THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV HolLight.SYM_CONV) THEN REWRITE_TAC [hyperplane_side] THEN
    REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC (← HolLight.SPEC ([[(a:real^N) dot c - b]]) REAL_SGN_CASES) THEN
    ASM_REWRITE_TAC [REAL_SGN_EQ] THEN
    SIMP_TAC [REAL_SUB_0, h2,
             h3] THEN
    REWRITE_TAC [CONVEX_HALFSPACE_LT, CONVEX_HALFSPACE_GT,
                CONVEX_HYPERPLANE])
  : ExceptT String IO thm).run
#eval HYPERPLANE_CELL_CONVEX

#eval phrase 31
def HYPERPLANE_CELL_INTERS : thm := keep "HYPERPLANE_CELL_INTERS" fun _ => (do
  prove ([[!A C. (!c:real^N->bool. c IN C ==> hyperplane_cell A c) /\
         ~(C = {}) /\ ~(INTERS C = {})
         ==> hyperplane_cell A (INTERS C)]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [HYPERPLANE_CELL, (← HolLight.GSYM MEMBER_NOT_EMPTY)] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[z:real^N]]) THEN
    REWRITE_TAC [IN_INTERS] THEN DISCH_TAC THEN
    GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN
    REWRITE_TAC [IN_INTERS, IN_ELIM_THM] THEN
    X_GEN_TAC ([[x:real^N]]) THEN EQ_TAC THEN DISCH_TAC THENL
     [FIRST_X_ASSUM (X_CHOOSE_TAC ([[c:real^N->bool]])),
      X_GEN_TAC ([[c:real^N->bool]]) THEN DISCH_TAC] THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[c:real^N->bool]]))) THEN
    ASM_REWRITE_TAC [] THEN REPEAT DISCH_TAC THEN
    FIRST_X_ASSUM (CHOOSE_THEN SUBST_ALL_TAC) THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [IN_ELIM_THM]) THEN SIMP_TAC [IN_ELIM_THM] THEN
    ASM_MESON_TAC [HYPERPLANE_EQUIV_SYM, HYPERPLANE_EQUIV_TRANS])
  : ExceptT String IO thm).run
#eval HYPERPLANE_CELL_INTERS

#eval phrase 32
def HYPERPLANE_CELL_INTER : thm := keep "HYPERPLANE_CELL_INTER" fun _ => (do
  prove ([[!A s t:real^N->bool.
        hyperplane_cell A s /\ hyperplane_cell A t /\ ~(s INTER t = {})
        ==> hyperplane_cell A (s INTER t)]])
   (REWRITE_TAC [(← HolLight.GSYM INTERS_2)] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HYPERPLANE_CELL_INTERS THEN
    ASM_REWRITE_TAC [FORALL_IN_INSERT, NOT_IN_EMPTY, NOT_INSERT_EMPTY])
  : ExceptT String IO thm).run
#eval HYPERPLANE_CELL_INTER

/- ------------------------------------------------------------------------- -/
/- A cell complex is considered to be a union of such cells.                 -/
/- ------------------------------------------------------------------------- -/

#eval phrase 33
def hyperplane_cellcomplex : thm := keep "hyperplane_cellcomplex" fun _ => new_definition
 [[hyperplane_cellcomplex A s <=>
        ?t. (!c. c IN t ==> hyperplane_cell A c) /\
            s = UNIONS t]]
#eval hyperplane_cellcomplex

#eval phrase 34
def HYPERPLANE_CELLCOMPLEX_EMPTY : thm := keep "HYPERPLANE_CELLCOMPLEX_EMPTY" fun _ => (do
  prove ([[!A:real^N#real->bool. hyperplane_cellcomplex A {}]])
   (GEN_TAC THEN REWRITE_TAC [hyperplane_cellcomplex] THEN
    EXISTS_TAC ([[{}:(real^N->bool)->bool]]) THEN
    REWRITE_TAC [NOT_IN_EMPTY, UNIONS_0])
  : ExceptT String IO thm).run
#eval HYPERPLANE_CELLCOMPLEX_EMPTY

#eval phrase 35
def HYPERPLANE_CELL_CELLCOMPLEX : thm := keep "HYPERPLANE_CELL_CELLCOMPLEX" fun _ => (do
  prove ([[!A c:real^N->bool. hyperplane_cell A c ==> hyperplane_cellcomplex A c]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [hyperplane_cellcomplex] THEN
    EXISTS_TAC ([[{c:real^N->bool}]]) THEN
    ASM_SIMP_TAC [IN_SING, UNIONS_1])
  : ExceptT String IO thm).run
#eval HYPERPLANE_CELL_CELLCOMPLEX

#eval phrase 36
def HYPERPLANE_CELLCOMPLEX_UNIONS : thm := keep "HYPERPLANE_CELLCOMPLEX_UNIONS" fun _ => (do
  prove ([[!A C. (!s:real^N->bool. s IN C ==> hyperplane_cellcomplex A s)
         ==> hyperplane_cellcomplex A (UNIONS C)]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [hyperplane_cellcomplex] THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC ([[f:(real^N->bool)->(real^N->bool)->bool]]) THEN DISCH_TAC THEN
    EXISTS_TAC ([[UNIONS (IMAGE (f:(real^N->bool)->(real^N->bool)->bool) C)]]) THEN
    REWRITE_TAC [FORALL_IN_UNIONS, IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC [FORALL_IN_IMAGE] THEN
    CONJ_TAC THENL [ASM_MESON_TAC [], REWRITE_TAC [UNIONS_IMAGE]] THEN
    GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN REWRITE_TAC [IN_UNIONS, IN_ELIM_THM] THEN
    HolLight.ASM SET_TAC [])
  : ExceptT String IO thm).run
#eval HYPERPLANE_CELLCOMPLEX_UNIONS

#eval phrase 37
def HYPERPLANE_CELLCOMPLEX_UNION : thm := keep "HYPERPLANE_CELLCOMPLEX_UNION" fun _ => (do
  prove ([[!A s t.
        hyperplane_cellcomplex A s /\ hyperplane_cellcomplex A t
        ==> hyperplane_cellcomplex A (s UNION t)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [(← HolLight.GSYM UNIONS_2)] THEN
    MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_UNIONS THEN
    ASM_REWRITE_TAC [FORALL_IN_INSERT, NOT_IN_EMPTY])
  : ExceptT String IO thm).run
#eval HYPERPLANE_CELLCOMPLEX_UNION

#eval phrase 38
def HYPERPLANE_CELLCOMPLEX_UNIV : thm := keep "HYPERPLANE_CELLCOMPLEX_UNIV" fun _ => (do
  prove ([[!A. hyperplane_cellcomplex A (:real^N)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [(← HolLight.GSYM UNIONS_HYPERPLANE_CELLS)] THEN
    MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_UNIONS THEN
    REWRITE_TAC [IN_ELIM_THM, HYPERPLANE_CELL_CELLCOMPLEX])
  : ExceptT String IO thm).run
#eval HYPERPLANE_CELLCOMPLEX_UNIV

#eval phrase 39
def HYPERPLANE_CELLCOMPLEX_INTERS : thm := keep "HYPERPLANE_CELLCOMPLEX_INTERS" fun _ => (do
  let lemma ← prove ([[UNIONS s = UNIONS {t | t IN s /\ ~(t = {})}]])
     (REWRITE_TAC [UNIONS_GSPEC] THEN GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN
      REWRITE_TAC [IN_UNIONS, IN_ELIM_THM] THEN MESON_TAC [NOT_IN_EMPTY])
  prove ([[!A C. (!s:real^N->bool. s IN C ==> hyperplane_cellcomplex A s)
         ==> hyperplane_cellcomplex A (INTERS C)]])
   (REPEAT GEN_TAC THEN ASM_CASES_TAC ([[C:(real^N->bool)->bool = {}]]) THEN
    ASM_REWRITE_TAC [INTERS_0, HYPERPLANE_CELLCOMPLEX_UNIV] THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [hyperplane_cellcomplex] THEN
    REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC ([[f:(real^N->bool)->(real^N->bool)->bool]]) THEN
    DISCH_TAC THEN SUBGOAL_THEN ([[C = {UNIONS((f:(real^N->bool)->(real^N->bool)->bool) s) | s IN C}]]) SUBST1_TAC THENL
     [GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM] THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    REWRITE_TAC [INTERS_OVER_UNIONS] THEN ONCE_REWRITE_TAC [lemma] THEN
    MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_UNIONS THEN
    REWRITE_TAC [FORALL_IN_GSPEC, IMP_CONJ] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HYPERPLANE_CELL_CELLCOMPLEX THEN
    MATCH_MP_TAC HYPERPLANE_CELL_INTERS THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC [], HolLight.ASM SET_TAC []])
  : ExceptT String IO thm).run
#eval HYPERPLANE_CELLCOMPLEX_INTERS

#eval phrase 40
def HYPERPLANE_CELLCOMPLEX_INTER : thm := keep "HYPERPLANE_CELLCOMPLEX_INTER" fun _ => (do
  prove ([[!A s t.
        hyperplane_cellcomplex A s /\ hyperplane_cellcomplex A t
        ==> hyperplane_cellcomplex A (s INTER t)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [(← HolLight.GSYM INTERS_2)] THEN
    MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_INTERS THEN
    ASM_REWRITE_TAC [FORALL_IN_INSERT, NOT_IN_EMPTY])
  : ExceptT String IO thm).run
#eval HYPERPLANE_CELLCOMPLEX_INTER

#eval phrase 41
def HYPERPLANE_CELLCOMPLEX_COMPL : thm := keep "HYPERPLANE_CELLCOMPLEX_COMPL" fun _ => (do
  prove ([[!A s. hyperplane_cellcomplex A s
         ==> hyperplane_cellcomplex A ((:real^N) DIFF s)]])
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [hyperplane_cellcomplex] THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC ([[C:(real^N->bool)->bool]]) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [UNIONS_INTERS, COMPL_COMPL] THEN
    MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_INTERS THEN
    REWRITE_TAC [FORALL_IN_GSPEC] THEN
    X_GEN_TAC ([[c:real^N->bool]]) THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[(:real^N) DIFF c = UNIONS {c' | hyperplane_cell A c' /\ ~(c' = c)}]]) SUBST1_TAC THENL
     [SUBST1_TAC (← HolLight.SYM (← HolLight.ISPEC ([[A:real^N#real->bool]]) UNIONS_HYPERPLANE_CELLS)) THEN
      GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN
      REWRITE_TAC [IN_DIFF, UNIONS_GSPEC, IN_ELIM_THM] THEN
      X_GEN_TAC ([[x:real^N]]) THEN REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN
      AP_TERM_TAC THEN GEN_REWRITE_TAC HolCore.Lib.I [FUN_EQ_THM] THEN
      X_GEN_TAC ([[c':real^N->bool]]) THEN REWRITE_TAC [] THEN
      MP_TAC (← HolLight.ISPECL [([[A:real^N#real->bool]]), ([[c:real^N->bool]]), ([[c':real^N->bool]])] DISJOINT_HYPERPLANE_CELLS_EQ) THEN
      ASM_SIMP_TAC [] THEN SET_TAC [],
      MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_UNIONS THEN
      ASM_SIMP_TAC [HYPERPLANE_CELL_CELLCOMPLEX, IN_ELIM_THM]])
  : ExceptT String IO thm).run
#eval HYPERPLANE_CELLCOMPLEX_COMPL

#eval phrase 42
def HYPERPLANE_CELLCOMPLEX_DIFF : thm := keep "HYPERPLANE_CELLCOMPLEX_DIFF" fun _ => (do
  let h1 ← sr (← ExceptT.mk [[s DIFF t = s INTER (UNIV DIFF t)]])
  prove ([[!A s t.
        hyperplane_cellcomplex A s /\ hyperplane_cellcomplex A t
        ==> hyperplane_cellcomplex A (s DIFF t)]])
   (ONCE_REWRITE_TAC [h1] THEN
    SIMP_TAC [HYPERPLANE_CELLCOMPLEX_COMPL, HYPERPLANE_CELLCOMPLEX_INTER])
  : ExceptT String IO thm).run
#eval HYPERPLANE_CELLCOMPLEX_DIFF

#eval phrase 43
def HYPERPLANE_CELLCOMPLEX_MONO : thm := keep "HYPERPLANE_CELLCOMPLEX_MONO" fun _ => (do
  prove ([[!A B s:real^N->bool.
        hyperplane_cellcomplex A s /\ A SUBSET B
        ==> hyperplane_cellcomplex B s]])
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [hyperplane_cellcomplex]) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[C:(real^N->bool)->bool]]) STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_UNIONS THEN
    X_GEN_TAC ([[c:real^N->bool]]) THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[c:real^N->bool]])) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[B:(real^N#real)->bool = A UNION (B DIFF A)]]) SUBST1_TAC THENL
     [HolLight.ASM SET_TAC [], ALL_TAC] THEN
    REWRITE_TAC [hyperplane_cellcomplex, HYPERPLANE_CELL_UNION] THEN
    EXISTS_TAC ([[{c' INTER c:real^N->bool |c'| hyperplane_cell (B DIFF A) c' /\
                                            ~(c' INTER c = {})}]]) THEN
    REWRITE_TAC [FORALL_IN_GSPEC] THEN CONJ_TAC THENL
     [X_GEN_TAC ([[c':real^N->bool]]) THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      MAP_EVERY EXISTS_TAC [([[c:real^N->bool]]), ([[c':real^N->bool]])] THEN
      ASM_REWRITE_TAC [INTER_COMM],
      GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN
      REWRITE_TAC [UNIONS_GSPEC, IN_ELIM_THM, IN_INTER] THEN
      X_GEN_TAC ([[x:real^N]]) THEN EQ_TAC THENL [DISCH_TAC, MESON_TAC []] THEN
      MP_TAC (← HolLight.ISPEC ([[B DIFF A:(real^N#real)->bool]]) UNIONS_HYPERPLANE_CELLS) THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [EXTENSION] THEN
      REWRITE_TAC [IN_UNIONS, IN_ELIM_THM, IN_UNIV] THEN HolLight.ASM SET_TAC []])
  : ExceptT String IO thm).run
#eval HYPERPLANE_CELLCOMPLEX_MONO

#eval phrase 44
def FINITE_HYPERPLANE_CELLCOMPLEXES : thm := keep "FINITE_HYPERPLANE_CELLCOMPLEXES" fun _ => (do
  prove ([[!A. FINITE A ==> FINITE {c:real^N->bool | hyperplane_cellcomplex A c}]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC ([[IMAGE UNIONS {t | t SUBSET {c:real^N->bool | hyperplane_cell A c}}]]) THEN
    ASM_SIMP_TAC [FINITE_IMAGE, FINITE_POWERSET, FINITE_HYPERPLANE_CELLS] THEN
    REWRITE_TAC [SUBSET, IN_IMAGE, IN_ELIM_THM, hyperplane_cellcomplex] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval FINITE_HYPERPLANE_CELLCOMPLEXES

#eval phrase 45
def FINITE_RESTRICT_HYPERPLANE_CELLCOMPLEXES : thm := keep "FINITE_RESTRICT_HYPERPLANE_CELLCOMPLEXES" fun _ => (do
  prove ([[!P A. FINITE A
         ==> FINITE {c:real^N->bool | hyperplane_cellcomplex A c /\ P c}]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC ([[{c:real^N->bool | hyperplane_cellcomplex A c}]]) THEN
    ASM_SIMP_TAC [FINITE_HYPERPLANE_CELLCOMPLEXES] THEN SET_TAC [])
  : ExceptT String IO thm).run
#eval FINITE_RESTRICT_HYPERPLANE_CELLCOMPLEXES

#eval phrase 46
-- let FINITE_SET_OF_HYPERPLANE_CELLS = ... (rebinds FINITE_SET_OF_HYPERPLANE_CELLS)
def FINITE_SET_OF_HYPERPLANE_CELLS_2 : thm := keep "FINITE_SET_OF_HYPERPLANE_CELLS_2" fun _ => (do
  prove ([[!A C. FINITE A /\ (!c:real^N->bool. c IN C ==> hyperplane_cellcomplex A c)
         ==> FINITE C]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC ([[{c:real^N->bool | hyperplane_cellcomplex A c}]]) THEN
    ASM_SIMP_TAC [FINITE_HYPERPLANE_CELLCOMPLEXES] THEN HolLight.ASM SET_TAC [])
  : ExceptT String IO thm).run
#eval FINITE_SET_OF_HYPERPLANE_CELLS_2

#eval phrase 47
def CELL_SUBSET_CELLCOMPLEX : thm := keep "CELL_SUBSET_CELLCOMPLEX" fun _ => (do
  let h1 ← sr (← ExceptT.mk [[c IN C ==> c SUBSET UNIONS C]])
  prove ([[!A s c:real^N->bool.
        hyperplane_cell A c /\ hyperplane_cellcomplex A s
        ==> (c SUBSET s <=> ~(DISJOINT c s))]])
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [hyperplane_cellcomplex]) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[C:(real^N->bool)->bool]]) STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN EQ_TAC THENL
     [ASM_CASES_TAC ([[c:real^N->bool = {}]]) THENL
       [ASM_MESON_TAC [NONEMPTY_HYPERPLANE_CELL], HolLight.ASM SET_TAC []],
      REWRITE_TAC [DISJOINT, INTER_UNIONS, (← HolLight.GSYM MEMBER_NOT_EMPTY)] THEN
      REWRITE_TAC [UNIONS_GSPEC, IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[x:real^N]]), ([[c':real^N->bool]])] THEN
      REWRITE_TAC [IN_INTER] THEN STRIP_TAC THEN
      MP_TAC (← HolLight.ISPECL [([[A:(real^N#real)->bool]]), ([[c:real^N->bool]]),
        ([[c':real^N->bool]])] DISJOINT_HYPERPLANE_CELLS_EQ) THEN
      ASM_SIMP_TAC [] THEN
      ASM_CASES_TAC ([[c':real^N->bool = c]]) THENL
       [DISCH_THEN ((fun _ => ALL_TAC)), HolLight.ASM SET_TAC []] THEN
      MATCH_MP_TAC h1 THEN
      ASM_MESON_TAC []])
  : ExceptT String IO thm).run
#eval CELL_SUBSET_CELLCOMPLEX

/- ------------------------------------------------------------------------- -/
/- Euler characteristic.                                                     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 48
def euler_characteristic : thm := keep "euler_characteristic" fun _ => new_definition
 [[euler_characteristic A (s:real^N->bool) =
        sum {c | hyperplane_cell A c /\ c SUBSET s}
            (\c. (-- &1) pow (num_of_int(aff_dim c)))]]
#eval euler_characteristic

#eval phrase 49
def EULER_CHARACTERISTIC_EMPTY : thm := keep "EULER_CHARACTERISTIC_EMPTY" fun _ => (do
  let h1 ← ms [] (← ExceptT.mk [[~(?x. x IN s) ==> (!x. x IN s ==> P x)]])
  prove ([[euler_characteristic A {} = &0]])
   (REWRITE_TAC [euler_characteristic, SUBSET_EMPTY] THEN
    MATCH_MP_TAC SUM_EQ_0 THEN
    MATCH_MP_TAC h1 THEN
    REWRITE_TAC [IN_ELIM_THM] THEN MESON_TAC [NONEMPTY_HYPERPLANE_CELL])
  : ExceptT String IO thm).run
#eval EULER_CHARACTERISTIC_EMPTY

#eval phrase 50
def EULER_CHARACTERISTIC_CELL_UNIONS : thm := keep "EULER_CHARACTERISTIC_CELL_UNIONS" fun _ => (do
  let h1 ← ms [] (← ExceptT.mk [[s = t ==> sum s f = sum t f]])
  prove ([[!A C. (!c:real^N->bool. c IN C ==> hyperplane_cell A c)
         ==> euler_characteristic A (UNIONS C) =
             sum C (\c. (-- &1) pow (num_of_int(aff_dim c)))]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [euler_characteristic] THEN
    MATCH_MP_TAC h1 THEN
    REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC ([[c:real^N->bool]]) THEN
    EQ_TAC THENL [ALL_TAC, HolLight.ASM SET_TAC []] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    SUBGOAL_THEN ([[~(c:real^N->bool = {})]]) MP_TAC THENL
     [ASM_MESON_TAC [NONEMPTY_HYPERPLANE_CELL], ALL_TAC] THEN
    REWRITE_TAC [MEMBER_NOT_EMPTY, SUBSET, IN_UNIONS] THEN
    REWRITE_TAC [(← HolLight.GSYM MEMBER_NOT_EMPTY), LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC ([[x:real^N]]) THEN DISCH_TAC THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[x:real^N]])) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[c':real^N->bool]]) STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN ([[~(DISJOINT (c:real^N->bool) c')]]) MP_TAC THENL
     [HolLight.ASM SET_TAC [], ASM_MESON_TAC [DISJOINT_HYPERPLANE_CELLS_EQ]])
  : ExceptT String IO thm).run
#eval EULER_CHARACTERISTIC_CELL_UNIONS

#eval phrase 51
def EULER_CHARACTERISTIC_CELL : thm := keep "EULER_CHARACTERISTIC_CELL" fun _ => (do
  prove ([[!A c. hyperplane_cell A c
         ==> euler_characteristic A c =  (-- &1) pow (num_of_int(aff_dim c))]])
   (REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV) [(← HolLight.GSYM UNIONS_1)] THEN
    ASM_SIMP_TAC [EULER_CHARACTERISTIC_CELL_UNIONS, IN_SING, SUM_SING])
  : ExceptT String IO thm).run
#eval EULER_CHARACTERISTIC_CELL

#eval phrase 52
def EULER_CHARACTERISTIC_CELLCOMPLEX_UNION : thm := keep "EULER_CHARACTERISTIC_CELLCOMPLEX_UNION" fun _ => (do
  prove ([[!A s t:real^N->bool.
        FINITE A /\
        hyperplane_cellcomplex A s /\
        hyperplane_cellcomplex A t /\
        DISJOINT s t
        ==> euler_characteristic A (s UNION t) =
            euler_characteristic A s + euler_characteristic A t]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [euler_characteristic] THEN
    CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC SUM_UNION_EQ THEN
    ASM_SIMP_TAC [FINITE_RESTRICT_HYPERPLANE_CELLS] THEN
    REWRITE_TAC [EXTENSION, IN_INTER, IN_ELIM_THM, NOT_IN_EMPTY, IN_UNION] THEN
    CONJ_TAC THEN X_GEN_TAC ([[c:real^N->bool]]) THENL
     [ASM_CASES_TAC ([[c:real^N->bool = {}]]) THENL
       [ASM_MESON_TAC [NONEMPTY_HYPERPLANE_CELL], HolLight.ASM SET_TAC []],
      ASM_CASES_TAC ([[hyperplane_cell A (c:real^N->bool)]]) THEN
      ASM_REWRITE_TAC [] THEN
      MP_TAC (← HolLight.ISPEC ([[A:(real^N#real)->bool]]) CELL_SUBSET_CELLCOMPLEX) THEN
      ASM_SIMP_TAC [HYPERPLANE_CELLCOMPLEX_UNION] THEN SET_TAC []])
  : ExceptT String IO thm).run
#eval EULER_CHARACTERISTIC_CELLCOMPLEX_UNION

#eval phrase 53
def EULER_CHARACTERISTIC_CELLCOMPLEX_UNIONS : thm := keep "EULER_CHARACTERISTIC_CELLCOMPLEX_UNIONS" fun _ => (do
  prove ([[!A C. FINITE A /\
         (!c:real^N->bool. c IN C ==> hyperplane_cellcomplex A c) /\
         pairwise DISJOINT C
         ==> euler_characteristic A (UNIONS C) =
             sum C (\c. euler_characteristic A c)]])
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_CASES_TAC ([[FINITE(C:(real^N->bool)->bool)]]) THENL
     [UNDISCH_TAC ([[FINITE(C:(real^N->bool)->bool)]]),
      ASM_MESON_TAC [FINITE_SET_OF_HYPERPLANE_CELLS_2]] THEN
    SPEC_TAC (([[C:(real^N->bool)->bool]]), ([[C:(real^N->bool)->bool]])) THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [EULER_CHARACTERISTIC_EMPTY, SUM_CLAUSES, UNIONS_0] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [UNIONS_INSERT] THEN
    HolCore.Lib.W (MP_TAC o HolLight.PART_MATCH (HolCore.Equal.lhs o HolCore.Kernel.rand) EULER_CHARACTERISTIC_CELLCOMPLEX_UNION o
          HolCore.Equal.lhs o HolLight.snd) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
       [HolLight.ASM SET_TAC [],
        MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_UNIONS THEN HolLight.ASM SET_TAC [],
        FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [pairwise]) THEN
        REWRITE_TAC [DISJOINT, INTER_UNIONS, IMP_CONJ, RIGHT_FORALL_IMP_THM,
                    FORALL_IN_INSERT, EMPTY_UNIONS, FORALL_IN_GSPEC] THEN
        ASM_MESON_TAC [INTER_COMM]],
      DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [pairwise]) THEN
      ASM_REWRITE_TAC [pairwise] THEN HolLight.ASM SET_TAC []])
  : ExceptT String IO thm).run
#eval EULER_CHARACTERISTIC_CELLCOMPLEX_UNIONS

#eval phrase 54
def EULER_CHARACTERISTIC : thm := keep "EULER_CHARACTERISTIC" fun _ => (do
  prove ([[!A s:real^N->bool.
        FINITE A
        ==> euler_characteristic A s =
            sum (0..dimindex(:N))
                (\d. (-- &1) pow d *
                     &(CARD {c | hyperplane_cell A c /\ c SUBSET s /\
                                 aff_dim c = &d}))]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [euler_characteristic] THEN
    MP_TAC (← HolLight.ISPECL [([[\c:real^N->bool. aff_dim c]]),
                   ([[\c:real^N->bool. (-- &1) pow (num_of_int(aff_dim c))]]),
                   ([[{c:real^N->bool | hyperplane_cell A c /\ c SUBSET s}]]),
                   ([[IMAGE int_of_num (0..dimindex(:N))]])] SUM_GROUP) THEN
    SIMP_TAC [SUM_IMAGE, INT_OF_NUM_EQ, o_DEF, NUM_OF_INT_OF_NUM] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC [FINITE_RESTRICT_HYPERPLANE_CELLS] THEN
      GEN_REWRITE_TAC HolCore.Lib.I [SUBSET] THEN
      REWRITE_TAC [FORALL_IN_IMAGE, IN_ELIM_THM] THEN
      X_GEN_TAC ([[c:real^N->bool]]) THEN STRIP_TAC THEN
      REWRITE_TAC [IN_IMAGE, IN_NUMSEG, LE_0] THEN
      REWRITE_TAC [(← HolLight.GSYM INT_OF_NUM_LE), INT_EXISTS_POS] THEN
      EXISTS_TAC ([[aff_dim(c:real^N->bool)]]) THEN
      REWRITE_TAC [AFF_DIM_LE_UNIV, AFF_DIM_POS_LE] THEN
      ASM_MESON_TAC [NONEMPTY_HYPERPLANE_CELL],
      DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN
      REWRITE_TAC [IN_ELIM_THM, (← HolLight.GSYM CONJ_ASSOC)] THEN
      ASM_SIMP_TAC [SUM_CONST, FINITE_RESTRICT_HYPERPLANE_CELLS] THEN
      REWRITE_TAC [REAL_MUL_AC]])
  : ExceptT String IO thm).run
#eval EULER_CHARACTERISTIC

/- ------------------------------------------------------------------------- -/
/- Show that the characteristic is invariant w.r.t. hyperplane arrangement.  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 55
def HYPERPLANE_CELLS_DISTINCT_LEMMA : thm := keep "HYPERPLANE_CELLS_DISTINCT_LEMMA" fun _ => (do
  prove ([[!a b. {x | a dot x = b} INTER {x | a dot x < b} = {} /\
         {x | a dot x = b} INTER {x | a dot x > b} = {} /\
         {x | a dot x < b} INTER {x | a dot x = b} = {} /\
         {x | a dot x < b} INTER {x | a dot x > b} = {} /\
         {x | a dot x > b} INTER {x | a dot x = b} = {} /\
         {x | a dot x > b} INTER {x | a dot x < b} = {}]])
   (REWRITE_TAC [EXTENSION, IN_INTER, IN_ELIM_THM, NOT_IN_EMPTY] THEN
    REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval HYPERPLANE_CELLS_DISTINCT_LEMMA

#eval phrase 56
def EULER_CHARACTERSTIC_LEMMA : thm := keep "EULER_CHARACTERSTIC_LEMMA" fun _ => (do
  let h13 ← sr (← ExceptT.mk [[s INTER t = {} /\ ~(c INTER s = {}) ==> ~(c INTER s = c INTER t)]])
  let h12 ← tt (← ExceptT.mk [[(a \/ b) /\ c <=> a /\ c \/ b /\ c]])
  let h11 ← ms [] (← ExceptT.mk [[s = t ==> sum s f = sum t f]])
  let h10 ← rr (← ExceptT.mk [[b - x < b <=> &0 < x]])
  let h9 ← rr (← ExceptT.mk [[b - x * y > b <=> &0 < x * --y]])
  let h8 ← rr (← ExceptT.mk [[b - x * y > b <=> &0 < x * --y]])
  let h7 ← rr (← ExceptT.mk [[abs e / &2 < e <=> &0 < e]])
  let h6 ← va (← ExceptT.mk [[x - a % (y - z):real^N = x + a % (z - y)]])
  let h5 ← na (← ExceptT.mk [[dist(u - a:real^N,u) = norm a]])
  let h4 ← va (← ExceptT.mk [[v + a % (u - v):real^N = (&1 - a) % v + a % u]])
  -- the MAP_EVERY body below, evaluated eagerly once per list element
  let mt ← tt (← ExceptT.mk [[(a \/ b) /\ c <=> a /\ c \/ b /\ c]])
  let mm ← ms [] (← ExceptT.mk [[s = t ==> sum s f = sum t f]])
  let _ ← tt (← ExceptT.mk [[(a \/ b) /\ c <=> a /\ c \/ b /\ c]])
  let _ ← ms [] (← ExceptT.mk [[s = t ==> sum s f = sum t f]])
  let _ ← tt (← ExceptT.mk [[(a \/ b) /\ c <=> a /\ c \/ b /\ c]])
  let _ ← ms [] (← ExceptT.mk [[s = t ==> sum s f = sum t f]])
  let h3 ← ms [] (← ExceptT.mk [[s = t ==> sum s f = sum t f]])
  let h2 ← sr (← ExceptT.mk [[x INSERT s = {x} UNION s]])
  let h1 ← sr (← ExceptT.mk [[x INSERT s = {x} UNION s]])
  prove ([[!A h s:real^N->bool.
        FINITE A /\ hyperplane_cellcomplex A s
        ==> euler_characteristic (h INSERT A) s = euler_characteristic A s]])
   (REWRITE_TAC [FORALL_PAIR_THM] THEN MAP_EVERY X_GEN_TAC [([[A:(real^N#real)->bool]]), ([[a:real^N]]), ([[b:real]]), ([[s:real^N->bool]])] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC [hyperplane_cellcomplex] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[C:(real^N->bool)->bool]]) STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN ([[!c:real^N->bool. c IN C ==> hyperplane_cellcomplex A c /\
                                hyperplane_cellcomplex ((a,b) INSERT A) c]]) ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_SIMP_TAC [HYPERPLANE_CELL_CELLCOMPLEX] THEN
      MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_MONO THEN
      EXISTS_TAC ([[A:(real^N#real)->bool]]) THEN
      ASM_SIMP_TAC [HYPERPLANE_CELL_CELLCOMPLEX] THEN SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[pairwise DISJOINT (C:(real^N->bool)->bool)]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [PAIRWISE_DISJOINT_HYPERPLANE_CELLS], ALL_TAC] THEN
    ASM_SIMP_TAC [EULER_CHARACTERISTIC_CELLCOMPLEX_UNIONS, FINITE_INSERT] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC ([[c:real^N->bool]]) THEN DISCH_TAC THEN
    ASM_CASES_TAC ([[hyperplane_cell ((a,b) INSERT A) (c:real^N->bool)]]) THEN
    ASM_SIMP_TAC [EULER_CHARACTERISTIC_CELL] THEN
    SUBGOAL_THEN ([[~(a:real^N = vec 0)]]) ASSUME_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o check (HolCore.Basics.is_neg o concl)) THEN
      SIMP_TAC [CONTRAPOS_THM] THEN DISCH_THEN ((fun _ => ALL_TAC)) THEN
      ONCE_REWRITE_TAC [h1] THEN
      REWRITE_TAC [HYPERPLANE_CELL_UNION] THEN
      REWRITE_TAC [HYPERPLANE_CELL_SING, RIGHT_EXISTS_AND_THM, UNWIND_THM2] THEN
      CONJ_TAC THENL [ASM_MESON_TAC [NONEMPTY_HYPERPLANE_CELL], ALL_TAC] THEN
      ONCE_REWRITE_TAC [CONJ_SYM] THEN REWRITE_TAC [INTER_UNIV, UNWIND_THM1] THEN
      ASM_SIMP_TAC [],
      ALL_TAC] THEN
    REWRITE_TAC [euler_characteristic] THEN
    ONCE_REWRITE_TAC [h2] THEN
    REWRITE_TAC [HYPERPLANE_CELL_UNION] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC ([[sum {c' INTER c |c'| hyperplane_cell {(a,b)} c' /\ ~(c' INTER c = {})}
        (\c:real^N->bool. (-- &1) pow (num_of_int(aff_dim c)))]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC h3 THEN
      GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM] THEN
      X_GEN_TAC ([[c':real^N->bool]]) THEN EQ_TAC THENL
       [DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[c1:real^N->bool]]) THEN
        DISCH_THEN (X_CHOOSE_THEN ([[c2:real^N->bool]]) STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN ([[~(DISJOINT c2 (c:real^N->bool))]]) ASSUME_TAC THENL
         [HolLight.ASM SET_TAC [], ASM_MESON_TAC [DISJOINT_HYPERPLANE_CELLS_EQ]],
        DISCH_THEN (X_CHOOSE_THEN ([[c1:real^N->bool]]) STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC [INTER_SUBSET] THEN
        MAP_EVERY EXISTS_TAC [([[c1:real^N->bool]]), ([[c:real^N->bool]])] THEN
        ASM_SIMP_TAC []],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [HYPERPLANE_CELL_SING] THEN
    SUBGOAL_THEN ([[~(c:real^N->bool = {})]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [NONEMPTY_HYPERPLANE_CELL], ALL_TAC] THEN
    MAP_EVERY (fun t => HolLight.tactic_of do
        pure (ASM_CASES_TAC t THENL
      [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC ([[sum {c} (\c:real^N->bool. (-- &1) pow num_of_int (aff_dim c))]]) THEN
       CONJ_TAC THENL [ALL_TAC, SIMP_TAC [SUM_SING]] THEN
       MATCH_MP_TAC mm THEN
       GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN X_GEN_TAC ([[c':real^N->bool]]) THEN
       REWRITE_TAC [IN_SING, IN_ELIM_THM] THEN
       REWRITE_TAC [mt] THEN
       REWRITE_TAC [EXISTS_OR_THM, UNWIND_THM2, (← HolLight.GSYM CONJ_ASSOC)] THEN
       EQ_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
       MP_TAC (← HolLight.ISPECL [([[a:real^N]]), ([[b:real]])] HYPERPLANE_CELLS_DISTINCT_LEMMA) THEN
       HolLight.ASM SET_TAC [],
       ALL_TAC])) [([[c SUBSET {x:real^N | a dot x < b}]]),
      ([[c SUBSET {x:real^N | a dot x > b}]]),
      ([[c SUBSET {x:real^N | a dot x = b}]])] THEN
    SUBGOAL_THEN ([[~(c INTER {x:real^N | a dot x = b} = {})]]) ASSUME_TAC THENL
     [SUBGOAL_THEN ([[?u v:real^N. u IN c /\ ~(a dot u < b) /\ v IN c /\ ~(a dot v > b)]]) MP_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
      REWRITE_TAC [real_gt, REAL_NOT_LT, (← HolLight.GSYM MEMBER_NOT_EMPTY)] THEN
      REWRITE_TAC [IN_INTER, IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[u:real^N]]), ([[v:real^N]])] THEN SIMP_TAC [REAL_LE_LT] THEN
      ASM_CASES_TAC ([[(a:real^N) dot u = b]]) THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      ASM_CASES_TAC ([[(a:real^N) dot v = b]]) THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
      EXISTS_TAC ([[v + (b - a dot v) / (a dot u - a dot v) % (u - v):real^N]]) THEN
      SUBGOAL_THEN ([[(a:real^N) dot v < a dot u]]) ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      ASM_SIMP_TAC [DOT_RADD, DOT_RMUL, DOT_RSUB, REAL_DIV_RMUL, REAL_SUB_LT,
                   REAL_LT_IMP_NZ, REAL_SUB_ADD2] THEN
      REWRITE_TAC [h4] THEN
      MATCH_MP_TAC IN_CONVEX_SET THEN
      ASM_SIMP_TAC [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ, REAL_SUB_LT] THEN
      CONJ_TAC THENL [ALL_TAC, ASM_REAL_ARITH_TAC] THEN
      ASM_MESON_TAC [HYPERPLANE_CELL_CONVEX],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[~(c INTER {x:real^N | a dot x < b} = {}) /\
                ~(c INTER {x:real^N | a dot x > b} = {})]]) STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN ([[?u v:real^N.
         u IN c /\ a dot u = b /\ v IN c /\ ~(a dot v = b) /\ ~(u = v)]]) STRIP_ASSUME_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN ([[open_in (subtopology euclidean (affine hull c)) (c:real^N->bool)]]) MP_TAC THENL [ASM_MESON_TAC [HYPERPLANE_CELL_RELATIVELY_OPEN], ALL_TAC] THEN
      REWRITE_TAC [open_in] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o HolLight.SPEC ([[u:real^N]]))) THEN
      ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC ([[e:real]]) THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o HolLight.SPEC ([[u - e / &2 / norm(v - u) % (v - u):real^N]]))) THEN
      ANTS_TAC THENL
       [REWRITE_TAC [h5] THEN
        REWRITE_TAC [h6] THEN
        REWRITE_TAC [NORM_MUL, REAL_ABS_DIV, REAL_ABS_NUM, REAL_ABS_NORM] THEN
        ASM_SIMP_TAC [REAL_DIV_RMUL, NORM_EQ_0, VECTOR_SUB_EQ] THEN
        ASM_REWRITE_TAC [h7] THEN
        MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN
        ASM_SIMP_TAC [AFFINE_AFFINE_HULL, HULL_INC],
        DISCH_TAC] THEN
      REWRITE_TAC [(← HolLight.GSYM MEMBER_NOT_EMPTY), IN_INTER, IN_ELIM_THM] THEN
      SUBGOAL_THEN ([[(a:real^N) dot v < b \/ a dot v > b]]) STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC,
        CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
        EXISTS_TAC ([[u - e / &2 / norm(v - u) % (v - u):real^N]]) THEN
        ASM_REWRITE_TAC [DOT_RSUB, DOT_RMUL] THEN
        REWRITE_TAC [h8] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN
        ASM_SIMP_TAC [REAL_LT_DIV, REAL_HALF, NORM_POS_LT, VECTOR_SUB_EQ] THEN
        ASM_REAL_ARITH_TAC,
        CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []]] THEN
      EXISTS_TAC ([[u - e / &2 / norm(v - u) % (v - u):real^N]]) THEN
      ASM_REWRITE_TAC [DOT_RSUB, DOT_RMUL] THEN
      REWRITE_TAC [h9,
                  h10] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC [REAL_LT_DIV, REAL_HALF, NORM_POS_LT, VECTOR_SUB_EQ] THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC ([[sum {{x | a dot x = b} INTER c,
         {x | a dot x > b} INTER c,
         {x | a dot x < b} INTER c}
        (\c:real^N->bool. (-- &1) pow (num_of_int(aff_dim c)))]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC h11 THEN
      GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM] THEN
      X_GEN_TAC ([[c':real^N->bool]]) THEN
      REWRITE_TAC [h12] THEN
      REWRITE_TAC [EXISTS_OR_THM, UNWIND_THM2, (← HolLight.GSYM CONJ_ASSOC)] THEN
      ONCE_REWRITE_TAC [INTER_COMM] THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN CONV_TAC HolLight.TAUT,
      ALL_TAC] THEN
    SIMP_TAC [SUM_CLAUSES, FINITE_INSERT, FINITE_EMPTY,
             IN_INSERT, NOT_IN_EMPTY] THEN
    ONCE_REWRITE_TAC [INTER_COMM] THEN
    ASM_SIMP_TAC [HYPERPLANE_CELLS_DISTINCT_LEMMA, REAL_ADD_RID, h13] THEN
    SUBGOAL_THEN ([[aff_dim (c INTER {x:real^N | a dot x < b}) = aff_dim c /\
    aff_dim (c INTER {x:real^N | a dot x > b}) = aff_dim c]]) (CONJUNCTS_THEN SUBST1_TAC) THENL
     [ONCE_REWRITE_TAC [(← HolLight.GSYM AFF_DIM_AFFINE_HULL)] THEN CONJ_TAC THEN
      AP_TERM_TAC THEN MATCH_MP_TAC AFFINE_HULL_CONVEX_INTER_OPEN THEN
      ASM_REWRITE_TAC [OPEN_HALFSPACE_LT, OPEN_HALFSPACE_GT] THEN
      ASM_MESON_TAC [HYPERPLANE_CELL_CONVEX],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[aff_dim c = aff_dim(c INTER {x:real^N | a dot x = b}) + &1]]) SUBST1_TAC THENL
     [MP_TAC (← HolLight.ISPECL [([[A:real^N#real->bool]]), ([[c:real^N->bool]])] HYPERPLANE_CELL_INTER_OPEN_AFFINE) THEN
      ASM_SIMP_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[s:real^N->bool]]), ([[t:real^N->bool]])] THEN
      STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      ONCE_REWRITE_TAC [(← HolLight.GSYM AFF_DIM_AFFINE_HULL)] THEN
      SUBGOAL_THEN ([[affine hull (s INTER t) = affine hull t /\
      affine hull ((s INTER t) INTER {x:real^N | a dot x = b}) =
      affine hull (t INTER {x:real^N | a dot x = b})]]) (CONJUNCTS_THEN SUBST1_TAC) THENL
       [REWRITE_TAC [INTER_ASSOC] THEN CONJ_TAC THEN
        GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [INTER_COMM] THEN
        MATCH_MP_TAC AFFINE_HULL_CONVEX_INTER_OPEN THEN
        ASM_SIMP_TAC [CONVEX_INTER, CONVEX_HYPERPLANE, AFFINE_IMP_CONVEX] THEN
        HolLight.ASM SET_TAC [],
        REWRITE_TAC [AFF_DIM_AFFINE_HULL] THEN
        ASM_SIMP_TAC [AFF_DIM_AFFINE_INTER_HYPERPLANE] THEN
        REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC [INT_SUB_ADD]) THEN
        HolLight.ASM SET_TAC []],
      SUBGOAL_THEN ([[&0 <= aff_dim (c INTER {x:real^N | a dot x = b})]]) MP_TAC THENL [REWRITE_TAC [AFF_DIM_POS_LE] THEN HolLight.ASM SET_TAC [], ALL_TAC] THEN
      SPEC_TAC (([[aff_dim (c INTER {x:real^N | a dot x = b})]]), ([[i:int]])) THEN
      REWRITE_TAC [(← HolLight.GSYM INT_FORALL_POS)] THEN
      REWRITE_TAC [NUM_OF_INT_OF_NUM, INT_OF_NUM_ADD] THEN
      REWRITE_TAC [REAL_POW_ADD] THEN REAL_ARITH_TAC2])
  : ExceptT String IO thm).run
#eval EULER_CHARACTERSTIC_LEMMA

#eval phrase 57
def EULER_CHARACTERSTIC_INVARIANT : thm := keep "EULER_CHARACTERSTIC_INVARIANT" fun _ => (do
  let h1 ← sr (← ExceptT.mk [[s UNION (x INSERT t) = x INSERT (s UNION t)]])
  prove ([[!A B h s:real^N->bool.
        FINITE A /\ FINITE B /\
        hyperplane_cellcomplex A s /\ hyperplane_cellcomplex B s
        ==> euler_characteristic A s = euler_characteristic B s]])
   (SUBGOAL_THEN ([[!A s:real^N->bool.
        FINITE A /\ hyperplane_cellcomplex A s
        ==> !B. FINITE B
                ==> euler_characteristic (A UNION B) s =
                    euler_characteristic A s]]) ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN
      MATCH_MP_TAC FINITE_INDUCT_STRONG THEN ASM_REWRITE_TAC [UNION_EMPTY] THEN
      MAP_EVERY X_GEN_TAC [([[h:real^N#real]]), ([[B:real^N#real->bool]])] THEN
      DISCH_THEN (CONJUNCTS_THEN2 (SUBST1_TAC o HolLight.SYM) STRIP_ASSUME_TAC) THEN
      REWRITE_TAC [h1] THEN
      MATCH_MP_TAC EULER_CHARACTERSTIC_LEMMA THEN
      ASM_REWRITE_TAC [FINITE_UNION] THEN
      MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_MONO THEN
      EXISTS_TAC ([[A:real^N#real->bool]]) THEN ASM_REWRITE_TAC [] THEN SET_TAC [],
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [RIGHT_IMP_FORALL_THM, IMP_IMP]) THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC ([[euler_characteristic (A UNION B) (s:real^N->bool)]]) THEN
      ASM_MESON_TAC [UNION_COMM]])
  : ExceptT String IO thm).run
#eval EULER_CHARACTERSTIC_INVARIANT

#eval phrase 58
def EULER_CHARACTERISTIC_INCLUSION_EXCLUSION : thm := keep "EULER_CHARACTERISTIC_INCLUSION_EXCLUSION" fun _ => (do
  prove ([[!A s:(real^N->bool)->bool.
        FINITE A /\ FINITE s /\ (!k. k IN s ==> hyperplane_cellcomplex A k)
        ==> euler_characteristic A (UNIONS s) =
            sum {t | t SUBSET s /\ ~(t = {})}
                (\t. (-- &1) pow (CARD t + 1) *
                     euler_characteristic A (INTERS t))]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[hyperplane_cellcomplex A :(real^N->bool)->bool]]),
      ([[euler_characteristic A :(real^N->bool)->real]]),
      ([[s:(real^N->bool)->bool]])] INCLUSION_EXCLUSION_REAL_RESTRICTED) THEN
    ASM_SIMP_TAC [EULER_CHARACTERISTIC_CELLCOMPLEX_UNION] THEN
    SIMP_TAC [HYPERPLANE_CELLCOMPLEX_EMPTY, HYPERPLANE_CELLCOMPLEX_INTER,
             HYPERPLANE_CELLCOMPLEX_UNION, HYPERPLANE_CELLCOMPLEX_DIFF])
  : ExceptT String IO thm).run
#eval EULER_CHARACTERISTIC_INCLUSION_EXCLUSION

/- ------------------------------------------------------------------------- -/
/- Euler-type relation for full-dimensional proper polyhedral cones.         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 59
def EULER_POLYHEDRAL_CONE : thm := keep "EULER_POLYHEDRAL_CONE" fun _ => (do
  let h42 ← rr (← ExceptT.mk [[x = &0 ==> x = &1 + y ==> --y = &1]])
  let h41 ← rr (← ExceptT.mk [[(x * --(&1) pow 1) * y = --(y * x)]])
  let h40 ← tt (← ExceptT.mk [[(p ==> r) ==> (p /\ q <=> p /\ r /\ q)]])
  let h39 ← ar (← ExceptT.mk [[1 <= n <=> ~(n = 0)]])
  let h38 ← rg (← ExceptT.mk [[s = &1 ==> s * t = t]])
  let h37 ← sr (← ExceptT.mk [[!t. t SUBSET s /\ t = UNIV ==> s = UNIV]])
  let h36 ← ms [NUM_OF_INT_OF_NUM] (← ExceptT.mk [[i = &n ==> num_of_int i = n]])
  let h35 ← ms [] (← ExceptT.mk [[(!h. P h ==> (Q h <=> R h))
        ==> (!h. P h) ==> ((!h. Q h) <=> (!h. R h))]])
  let h34 ← ms [] (← ExceptT.mk [[(!h. P h ==> (Q h <=> R h))
          ==> ((!h. P h ==> Q h) <=> (!h. P h ==> R h))]])
  let h33 ← tt (← ExceptT.mk [[(c ==> b) /\ (a <=> c) ==> (a <=> b /\ c)]])
  let h32 ← va (← ExceptT.mk [[--x:real^N = y <=> x = --y]])
  let h31 ← rr (← ExceptT.mk [[x = (--(&1)) pow (dimindex(:N)) /\
    y = (--(&1)) pow (dimindex(:N))
    ==> x = s + y ==> s = &0]])
  let h30 ← sr (← ExceptT.mk [[s UNION (UNIV DIFF s) = UNIV]])
  let h29 ← sr (← ExceptT.mk [[DISJOINT s (UNIV DIFF s)]])
  let h28 ← tt (← ExceptT.mk [[~q /\ (p ==> r) ==> ~r ==> (p <=> q)]])
  let h27 ← tt (← ExceptT.mk [[a ==> (a /\ b <=> b)]])
  let h26 ← sr (← ExceptT.mk [[(!x. x IN s ==> f x = x) ==> s = {f x | x IN s}]])
  let h25 ← sr (← ExceptT.mk [[{f x | x | F} = {}]])
  let h24 ← ms [OPEN_IN_SUBTOPOLOGY_REFL] (← ExceptT.mk [[s SUBSET topspace tp /\ t = s
            ==> open_in (subtopology tp t) s]])
  let h23 ← tt (← ExceptT.mk [[~p ==> p ==> q]])
  let h22 ← tt (← ExceptT.mk [[a /\ ~(a /\ b) <=> a /\ ~b]])
  let h21 ← tt (← ExceptT.mk [[(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)]])
  let h20 ← sr (← ExceptT.mk [[{x | x IN s /\ P x} SUBSET s]])
  let h19 ← ms [] (← ExceptT.mk [[(!h. P h ==> (Q h <=> R h))
        ==> (!h. P h) ==> ((!h. Q h) <=> (!h. R h))]])
  let h18 ← na (← ExceptT.mk [[dist(x:real^N,x + r) = norm r]])
  let h17 ← rr (← ExceptT.mk [[~(x:real = &0) ==> ~(x <= &0) \/ x < &0]])
  let h16 ← sr (← ExceptT.mk [[~(s SUBSET t) <=> ?y. y IN s /\ ~(y IN t)]])
  let h15 ← tt (← ExceptT.mk [[(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)]])
  let h14 ← sr (← ExceptT.mk [[s SUBSET t ==> ~(s = t) ==> s PSUBSET t]])
  let h13 ← tt (← ExceptT.mk [[a /\ b /\ (~c ==> d) ==> ~(a /\ b /\ c) ==> d]])
  let h12 ← ms [HAS_SIZE] (← ExceptT.mk [[(?f. FINITE f /\ P f) <=> (?n f. f HAS_SIZE n /\ P f)]])
  let h11 ← rr (← ExceptT.mk [[--x <= &0 <=> &0 <= x]])
  let h10 ← sr (← ExceptT.mk [[(!x. x IN s ==> f x = x) ==> {f x | x IN s} = s]])
  let h9 ← sr (← ExceptT.mk [[s = s' /\ (!x. x IN s ==> (x IN t <=> x IN t'))
            ==> s INTER t = s' INTER t']])
  let h8 ← sr (← ExceptT.mk [[s SUBSET f /\ s = t ==> s = f INTER t]])
  let h7 ← sr (← ExceptT.mk [[(!x. x IN s ==> f x = x) ==> {f x | x IN s} = s]])
  let h6 ← sr (← ExceptT.mk [[(!x. x IN s ==> f x = x) ==> s = {f x | x IN s}]])
  let h5 ← sr (← ExceptT.mk [[{f x | x | F} = {}]])
  let h4 ← rr (← ExceptT.mk [[e * x <= x <=> &0 <= x * (&1 - e)]])
  let h3 ← rr (← ExceptT.mk [[(&0 <= x ==> y <= x) /\ (&0 <= --x ==> &0 <= --y) /\ &0 <= b
          ==> x <= b ==> y <= b]])
  let h2 ← rr (← ExceptT.mk [[&0 <= b /\ ~(&0 < b) ==> b = &0]])
  let h1 ← sr (← ExceptT.mk [[!s. s = UNIV /\ s SUBSET t ==> t = UNIV]])
  prove ([[!s. polyhedron s /\ conic s /\ ~(interior s = {}) /\ ~(s = (:real^N))
       ==> sum (0..dimindex(:N))
               (\d. (-- &1) pow d *
                    &(CARD {f | f face_of s /\ aff_dim f = &d })) = &0]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[affine hull s = (:real^N)]]) ASSUME_TAC THENL
     [MATCH_MP_TAC h1 THEN
      EXISTS_TAC ([[affine hull (interior s:real^N->bool)]]) THEN
      SIMP_TAC [INTERIOR_SUBSET, HULL_MONO] THEN
      MATCH_MP_TAC AFFINE_HULL_OPEN THEN ASM_REWRITE_TAC [OPEN_INTERIOR],
      ALL_TAC] THEN
    FIRST_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [POLYHEDRON_INTER_AFFINE_MINIMAL]) THEN
    ASM_REWRITE_TAC [INTER_UNIV, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC ([[H:(real^N->bool)->bool]]) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (ASSUME_TAC o HolLight.SYM) STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN ([[(vec 0:real^N) IN s]]) ASSUME_TAC THENL
     [ASM_SIMP_TAC [CONIC_CONTAINS_0] THEN
      ASM_MESON_TAC [SUBSET_EMPTY, INTERIOR_SUBSET],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!h:real^N->bool. h IN H ==> ?a. ~(a = vec 0) /\ h = {x | a dot x <= &0}]]) MP_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN
      FIRST_ASSUM (MP_TAC o HolLight.SPEC ([[h:real^N->bool]])) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC [], MATCH_MP_TAC MONO_EXISTS] THEN
      X_GEN_TAC ([[a:real^N]]) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[b:real]]) STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN ([[b = &0]]) SUBST_ALL_TAC THENL [ALL_TAC, ASM_REWRITE_TAC []] THEN
      MATCH_MP_TAC h2 THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN ([[(vec 0:real^N) IN INTERS H]]) MP_TAC THENL
         [HolLight.ASM SET_TAC [], REWRITE_TAC [IN_INTERS]] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[h:real^N->bool]])) THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [IN_ELIM_THM, DOT_RZERO],
        DISCH_TAC THEN
        FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[H DELETE (h:real^N->bool)]])) THEN
        ANTS_TAC THENL [HolLight.ASM SET_TAC [], REWRITE_TAC [PSUBSET_ALT]] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[x:real^N]]) STRIP_ASSUME_TAC o HolLight.CONJUNCT2) THEN
        SUBGOAL_THEN ([[?e. &0 < e /\ e < &1 /\
                        (e % x:real^N) IN h]]) STRIP_ASSUME_TAC THENL
         [EXISTS_TAC ([[min (&1 / &2) (b / ((a:real^N) dot x))]]) THEN
          ASM_REWRITE_TAC [IN_ELIM_THM, DOT_RMUL] THEN
          SUBGOAL_THEN ([[&0 < (a:real^N) dot x]]) ASSUME_TAC THENL
           [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC ([[b:real]]) THEN
            ASM_REWRITE_TAC [] THEN
            UNDISCH_TAC ([[~((x:real^N) IN s)]]) THEN EXPAND_TAC "s" THEN
            ONCE_REWRITE_TAC [(← HolLight.GSYM CONTRAPOS_THM)] THEN
            REWRITE_TAC [REAL_NOT_LT] THEN DISCH_TAC THEN
            SUBGOAL_THEN ([[H:(real^N->bool)->bool = h INSERT (H DELETE h)]]) SUBST1_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
            REWRITE_TAC [INTERS_INSERT, IN_INTER] THEN
            ASM_REWRITE_TAC [IN_ELIM_THM],
            ASM_SIMP_TAC [REAL_LT_MIN, REAL_LT_DIV, REAL_MIN_LT] THEN
            CONV_TAC REAL_RAT_REDUCE_CONV THEN
            ASM_SIMP_TAC [(← HolLight.GSYM REAL_LE_RDIV_EQ)] THEN REAL_ARITH_TAC2],
          UNDISCH_TAC ([[~((x:real^N) IN s)]]) THEN REWRITE_TAC [] THEN
          SUBGOAL_THEN ([[x:real^N = inv e % e % x]]) SUBST1_TAC THENL
           [ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_LINV, REAL_LT_IMP_NZ,
                         VECTOR_MUL_LID],
            ALL_TAC] THEN
          RULE_ASSUM_TAC (HolLight.REWRITE_RULE [conic]) THEN
          FIRST_ASSUM MATCH_MP_TAC THEN
          ASM_SIMP_TAC [REAL_LT_IMP_LE, REAL_LE_INV_EQ] THEN
          EXPAND_TAC "s" THEN
          SUBGOAL_THEN ([[H:(real^N->bool)->bool = h INSERT (H DELETE h)]]) SUBST1_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
          REWRITE_TAC [INTERS_INSERT, IN_INTER] THEN
          CONJ_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
          UNDISCH_TAC ([[(x:real^N) IN INTERS (H DELETE h)]]) THEN
          REWRITE_TAC [IN_INTERS] THEN MATCH_MP_TAC MONO_FORALL THEN
          X_GEN_TAC ([[k:real^N->bool]]) THEN REWRITE_TAC [IN_DELETE] THEN
          DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
          FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[k:real^N->bool]])) THEN
          ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
          MAP_EVERY X_GEN_TAC [([[a':real^N]]), ([[b':real]])] THEN
          STRIP_TAC THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN
          MATCH_MP_TAC h3 THEN
          REWRITE_TAC [DOT_RMUL, (← HolLight.GSYM REAL_MUL_RNEG)] THEN
          REWRITE_TAC [h4] THEN
          ASM_SIMP_TAC [REAL_LE_MUL, REAL_LT_IMP_LE, REAL_SUB_LE] THEN
          SUBGOAL_THEN ([[(vec 0:real^N) IN INTERS H]]) MP_TAC THENL
           [HolLight.ASM SET_TAC [], REWRITE_TAC [IN_INTERS]] THEN
          DISCH_THEN (MP_TAC o HolLight.SPEC ([[k:real^N->bool]])) THEN ASM_REWRITE_TAC [] THEN
          REWRITE_TAC [IN_ELIM_THM, DOT_RZERO]]],
      FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o HolLight.SPEC ([[h:real^N->bool]]))] THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC ([[fa:(real^N->bool)->real^N]]) THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.BINDER_CONV o HolCore.Lib.funpow 2 HolLight.RAND_CONV) [EQ_SYM_EQ] THEN
    DISCH_TAC THEN ABBREV_TAC ([[A = IMAGE (\h. (fa:(real^N->bool)->real^N) h,&0) H]]) THEN
    SUBGOAL_THEN ([[FINITE(A:real^N#real->bool)]]) ASSUME_TAC THENL
     [EXPAND_TAC "A" THEN MATCH_MP_TAC FINITE_IMAGE THEN ASM_SIMP_TAC [],
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC ([[euler_characteristic A (s:real^N->bool)]]) THEN CONJ_TAC THENL
     [ASM_SIMP_TAC [EULER_CHARACTERISTIC] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      X_GEN_TAC ([[d:num]]) THEN STRIP_TAC THEN REWRITE_TAC [] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC BIJECTIONS_CARD_EQ THEN
      ASM_SIMP_TAC [FINITE_RESTRICT_HYPERPLANE_CELLS] THEN
      EXISTS_TAC ([[relative_interior:(real^N->bool)->(real^N->bool)]]) THEN
      EXISTS_TAC ([[closure:(real^N->bool)->(real^N->bool)]]) THEN
      REWRITE_TAC [IN_ELIM_THM] THEN CONJ_TAC THENL
       [X_GEN_TAC ([[f:real^N->bool]]) THEN STRIP_TAC THEN
        SUBGOAL_THEN ([[closure(relative_interior f):real^N->bool = f]]) ASSUME_TAC THENL
         [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC ([[closure f:real^N->bool]]) THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC CONVEX_CLOSURE_RELATIVE_INTERIOR THEN
            ASM_MESON_TAC [FACE_OF_IMP_CONVEX],
            REWRITE_TAC [CLOSURE_EQ] THEN MATCH_MP_TAC FACE_OF_IMP_CLOSED THEN
            ASM_MESON_TAC [POLYHEDRON_IMP_CLOSED, POLYHEDRON_IMP_CONVEX]],
          ALL_TAC] THEN
        ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
         [ALL_TAC,
          ONCE_REWRITE_TAC [(← HolLight.GSYM AFF_DIM_AFFINE_HULL)] THEN
          ONCE_REWRITE_TAC [(← HolLight.GSYM AFFINE_HULL_CLOSURE)] THEN
          ASM_REWRITE_TAC [AFF_DIM_AFFINE_HULL] THEN
          ASM_MESON_TAC [RELATIVE_INTERIOR_SUBSET, SUBSET_TRANS,
                        FACE_OF_IMP_SUBSET]] THEN
        SUBGOAL_THEN ([[~(f:real^N->bool = {})]]) ASSUME_TAC THENL
         [ASM_REWRITE_TAC [(← HolLight.GSYM AFF_DIM_POS_LE), INT_POS], ALL_TAC] THEN
        SUBGOAL_THEN ([[?J. J SUBSET H /\
            f = INTERS {{x:real^N | fa h dot x <= &0} | h IN H} INTER
                INTERS {{x | fa(h:real^N->bool) dot x = &0} | h IN J}]]) ASSUME_TAC THENL
         [ASM_CASES_TAC ([[f:real^N->bool = s]]) THENL
           [EXISTS_TAC ([[{}:(real^N->bool)->bool]]) THEN
            REWRITE_TAC [EMPTY_SUBSET, NOT_IN_EMPTY, INTERS_0, INTER_UNIV,
                        h5] THEN
            ASM_REWRITE_TAC [] THEN
            REWRITE_TAC [(← HolLight.SYM (← HolLight.ASSUME ([[INTERS H = (s:real^N->bool)]])))] THEN
            AP_TERM_TAC THEN MATCH_MP_TAC h6 THEN
            ASM_SIMP_TAC [],
            ALL_TAC] THEN
          EXISTS_TAC ([[{h:real^N->bool | h IN H /\
                     f SUBSET s INTER {x:real^N | fa h dot x = &0}}]]) THEN
          CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN
          MP_TAC (← HolLight.ISPECL [([[s:real^N->bool]]), ([[H:(real^N->bool)->bool]]),
                         ([[fa:(real^N->bool)->real^N]]),
                         ([[\h:real^N->bool. &0]])] FACE_OF_POLYHEDRON_EXPLICIT) THEN
          ASM_SIMP_TAC [INTER_UNIV] THEN
          DISCH_THEN (MP_TAC o HolLight.SPEC ([[f:real^N->bool]])) THEN ASM_REWRITE_TAC [] THEN
          SUBGOAL_THEN ([[INTERS {{x:real^N | fa(h:real^N->bool) dot x <= &0} | h IN H} = s]]) ASSUME_TAC THENL
           [EXPAND_TAC "s" THEN AP_TERM_TAC THEN MATCH_MP_TAC h7 THEN
            ASM_SIMP_TAC [],
           ALL_TAC] THEN
          ASM_CASES_TAC ([[{h:real^N->bool | h IN H /\
                           f SUBSET s INTER {x:real^N | fa h dot x = &0}} =
                       {}]]) THENL
           [ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
            ASM_REWRITE_TAC [IMAGE_CLAUSES, INTERS_0] THEN
            FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP FACE_OF_IMP_SUBSET) THEN
            HolLight.ASM SET_TAC [],
            ALL_TAC] THEN
          DISCH_THEN (fun th => GEN_REWRITE_TAC HolLight.LAND_CONV [th]) THEN
          ASM_REWRITE_TAC [] THEN GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN
          X_GEN_TAC ([[y:real^N]]) THEN REWRITE_TAC [IN_INTER, IN_INTERS] THEN
          REWRITE_TAC [FORALL_IN_GSPEC, IN_INTER] THEN
          ASM_CASES_TAC ([[(y:real^N) IN s]]) THEN ASM_REWRITE_TAC [] THEN
          HolLight.ASM SET_TAC [],
          ALL_TAC] THEN
        ABBREV_TAC ([[H' = IMAGE (\h:real^N->bool. {x:real^N | --(fa h) dot x <= &0}) H]]) THEN
        SUBGOAL_THEN ([[?J. FINITE J /\
            J SUBSET (H UNION H') /\
            f:real^N->bool = affine hull f INTER INTERS J]]) MP_TAC THENL
         [FIRST_X_ASSUM (X_CHOOSE_THEN ([[J:(real^N->bool)->bool]]) STRIP_ASSUME_TAC) THEN
          EXISTS_TAC ([[H UNION IMAGE (\h:real^N->bool.
             {x:real^N | --(fa h) dot x <= &0}) J]]) THEN
          REPEAT CONJ_TAC THENL
           [ASM_REWRITE_TAC [FINITE_UNION] THEN MATCH_MP_TAC FINITE_IMAGE THEN
            ASM_MESON_TAC [FINITE_SUBSET],
            EXPAND_TAC "H'" THEN HolLight.ASM SET_TAC [],
            MATCH_MP_TAC h8 THEN
            REWRITE_TAC [HULL_SUBSET] THEN
            FIRST_X_ASSUM (fun th => GEN_REWRITE_TAC HolLight.LAND_CONV [th]) THEN
            REWRITE_TAC [(← HolLight.GSYM REAL_LE_ANTISYM)] THEN
            REWRITE_TAC [INTERS_UNION] THEN MATCH_MP_TAC h9 THEN
            CONJ_TAC THENL
             [AP_TERM_TAC THEN MATCH_MP_TAC h10 THEN
              ASM_SIMP_TAC [],
              ALL_TAC] THEN
            X_GEN_TAC ([[y:real^N]]) THEN REWRITE_TAC [IN_INTERS] THEN
            REWRITE_TAC [FORALL_IN_IMAGE, FORALL_IN_GSPEC] THEN
            REWRITE_TAC [IN_ELIM_THM, DOT_LNEG] THEN
            REWRITE_TAC [h11] THEN
            HolLight.ASM SET_TAC []],
          ALL_TAC] THEN
        GEN_REWRITE_TAC HolLight.LAND_CONV [h12] THEN
        GEN_REWRITE_TAC HolLight.LAND_CONV [num_WOP] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[nn:num]]) (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
        DISCH_THEN (X_CHOOSE_THEN ([[J:(real^N->bool)->bool]]) STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN ([[!J'. J' PSUBSET J
             ==> (f:real^N->bool) PSUBSET (affine hull f INTER INTERS J')]]) ASSUME_TAC THENL
         [REPEAT STRIP_TAC THEN
          FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[CARD(J':(real^N->bool)->bool)]])) THEN
          ANTS_TAC THENL [ASM_MESON_TAC [CARD_PSUBSET, HAS_SIZE], ALL_TAC] THEN
          REWRITE_TAC [NOT_EXISTS_THM, HAS_SIZE] THEN
          DISCH_THEN (MP_TAC o HolLight.SPEC ([[J':(real^N->bool)->bool]])) THEN
          MATCH_MP_TAC h13 THEN
          CONJ_TAC THENL
           [ASM_MESON_TAC [PSUBSET, FINITE_SUBSET, HAS_SIZE], ALL_TAC] THEN
          CONJ_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
          MATCH_MP_TAC h14 THEN
          FIRST_X_ASSUM (fun th => GEN_REWRITE_TAC HolLight.LAND_CONV [th]) THEN
          HolLight.ASM SET_TAC [],
          ALL_TAC] THEN
        SUBGOAL_THEN ([[!h:real^N->bool. h IN J
          ==> ?a. {x | a dot x <= &0} = h /\
                  (h IN H /\ a = fa h \/ ?h'. h' IN H /\ a = --(fa h'))]]) MP_TAC THENL
         [X_GEN_TAC ([[h:real^N->bool]]) THEN DISCH_TAC THEN
          SUBGOAL_THEN ([[(h:real^N->bool) IN (H UNION H')]]) MP_TAC THENL
           [HolLight.ASM SET_TAC [], EXPAND_TAC "H'"] THEN
          UNDISCH_THEN ([[(h:real^N->bool) IN J]]) ((fun _ => ALL_TAC)) THEN
          SPEC_TAC (([[h:real^N->bool]]), ([[h:real^N->bool]])) THEN
          REWRITE_TAC [IN_UNION, h15,
                      FORALL_AND_THM, FORALL_IN_IMAGE] THEN
          CONJ_TAC THEN X_GEN_TAC ([[h:real^N->bool]]) THEN DISCH_TAC THENL
           [EXISTS_TAC ([[(fa:(real^N->bool)->real^N) h]]) THEN
            ASM_SIMP_TAC [],
            EXISTS_TAC ([[--((fa:(real^N->bool)->real^N) h)]]) THEN
            REWRITE_TAC [] THEN DISJ2_TAC THEN ASM_MESON_TAC []],
          ALL_TAC] THEN
        GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
        REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
        X_GEN_TAC ([[ga:(real^N->bool)->real^N]]) THEN DISCH_TAC THEN
        MP_TAC (← HolLight.ISPECL [([[f:real^N->bool]]), ([[J:(real^N->bool)->bool]]),
          ([[ga:(real^N->bool)->real^N]]), ([[\h:real^N->bool. &0]])] RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT) THEN
        ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
         [REPEAT CONJ_TAC THENL
           [ASM_MESON_TAC [HAS_SIZE],
            ASM_MESON_TAC [],
            ASM_SIMP_TAC [] THEN ASM_MESON_TAC [VECTOR_NEG_EQ_0, SUBSET]],
          DISCH_TAC THEN ASM_REWRITE_TAC []] THEN
        SUBGOAL_THEN ([[!h:real^N->bool. h IN J ==> h IN H /\ ga h:real^N = fa h]]) ASSUME_TAC THENL
         [SUBGOAL_THEN ([[~(relative_interior f:real^N->bool = {})]]) MP_TAC THENL
           [ASM_MESON_TAC [RELATIVE_INTERIOR_EQ_EMPTY, FACE_OF_IMP_CONVEX],
            REWRITE_TAC [(← HolLight.GSYM MEMBER_NOT_EMPTY)]] THEN
          DISCH_THEN (X_CHOOSE_TAC ([[z:real^N]])) THEN
          SUBGOAL_THEN ([[(z:real^N) IN f /\ z IN s]]) STRIP_ASSUME_TAC THENL
           [ASM_MESON_TAC [SUBSET, FACE_OF_IMP_SUBSET, RELATIVE_INTERIOR_SUBSET],
            ALL_TAC] THEN
          X_GEN_TAC ([[h:real^N->bool]]) THEN DISCH_TAC THEN
          FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[h:real^N->bool]])) THEN
          ASM_REWRITE_TAC [] THEN
          DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
          DISCH_THEN (DISJ_CASES_THEN MP_TAC) THEN REWRITE_TAC [] THEN
          DISCH_THEN (X_CHOOSE_THEN ([[h':real^N->bool]]) STRIP_ASSUME_TAC) THEN
          UNDISCH_TAC ([[(z:real^N) IN relative_interior f]]) THEN
          ASM_REWRITE_TAC [IN_ELIM_THM] THEN
          DISCH_THEN (MP_TAC o HolLight.SPEC ([[h:real^N->bool]])) THEN
          ASM_REWRITE_TAC [DOT_LNEG] THEN
          UNDISCH_TAC ([[(z:real^N) IN s]]) THEN EXPAND_TAC "s" THEN
          REWRITE_TAC [IN_INTERS] THEN
          DISCH_THEN (MP_TAC o HolLight.SPEC ([[h':real^N->bool]])) THEN ASM_REWRITE_TAC [] THEN
          FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[h':real^N->bool]])) THEN
          ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV) [(← HolLight.SYM (← HolLight.CONJUNCT2 th))])) THEN
          REWRITE_TAC [IN_ELIM_THM] THEN REAL_ARITH_TAC2,
          ALL_TAC] THEN
        FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.SYM th)] THEN
          MP_TAC (← HolLight.SYM th))) THEN
        FIRST_X_ASSUM (X_CHOOSE_THEN ([[K:(real^N->bool)->bool]]) MP_TAC) THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        DISCH_THEN (fun th => HolLight.tactic_of do
        pure (ASSUME_TAC (← HolLight.SYM th) THEN
          GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [th])) THEN
        REWRITE_TAC [IN_INTER, IN_INTERS, FORALL_IN_GSPEC, (← HolLight.GSYM CONJ_ASSOC)] THEN
        REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN
        SUBGOAL_THEN ([[~(relative_interior f:real^N->bool = {})]]) ASSUME_TAC THENL
         [ASM_MESON_TAC [RELATIVE_INTERIOR_EQ_EMPTY, FACE_OF_IMP_CONVEX],
          ALL_TAC] THEN
        SUBGOAL_THEN ([[DISJOINT (J:(real^N->bool)->bool) K]]) ASSUME_TAC THENL
         [UNDISCH_TAC ([[~(relative_interior f:real^N->bool = {})]]) THEN
          FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV o HolLight.LAND_CONV) [(← HolLight.SYM th)])) THEN
          REWRITE_TAC [IN_DISJOINT, (← HolLight.GSYM MEMBER_NOT_EMPTY), IN_ELIM_THM] THEN
          ASM_MESON_TAC [REAL_LT_REFL],
          ALL_TAC] THEN
        SUBGOAL_THEN ([[relative_interior f =
          INTERS {(if (h:real^N->bool) IN J then {x | fa h dot x < &0}
                   else if h IN K then {x:real^N | fa h dot x = &0}
                   else if relative_interior f SUBSET {x | fa h dot x = &0}
                   then {x | fa h dot x = &0}
                   else {x | fa h dot x < &0}) | h IN H}]]) ASSUME_TAC THENL
         [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
           [ALL_TAC,
            FIRST_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.SYM th)])) THEN
            GEN_REWRITE_TAC HolCore.Lib.I [SUBSET] THEN
            REWRITE_TAC [IN_INTERS, FORALL_IN_GSPEC, AND_FORALL_THM] THEN
            X_GEN_TAC ([[x:real^N]]) THEN REWRITE_TAC [IN_ELIM_THM] THEN
            MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC ([[h:real^N->bool]]) THEN
            ASM_CASES_TAC ([[(h:real^N->bool) IN H]]) THENL
             [ALL_TAC, DISCH_THEN ((fun _ => ALL_TAC)) THEN HolLight.ASM SET_TAC []] THEN
            ASM_REWRITE_TAC [] THEN
            ASM_CASES_TAC ([[(h:real^N->bool) IN J]]) THEN
            ASM_SIMP_TAC [IN_ELIM_THM, REAL_LT_IMP_LE] THENL
             [HolLight.ASM SET_TAC [], ALL_TAC] THEN
            ASM_CASES_TAC ([[(h:real^N->bool) IN K]]) THEN
            ASM_SIMP_TAC [IN_ELIM_THM, REAL_LE_REFL] THEN
            COND_CASES_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN
            REAL_ARITH_TAC2] THEN
          GEN_REWRITE_TAC HolCore.Lib.I [SUBSET] THEN X_GEN_TAC ([[x:real^N]]) THEN
          DISCH_TAC THEN REWRITE_TAC [IN_INTERS, FORALL_IN_GSPEC] THEN
          X_GEN_TAC ([[h:real^N->bool]]) THEN DISCH_TAC THEN
          REPEAT (COND_CASES_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC]) THEN
          REWRITE_TAC [IN_ELIM_THM, REAL_LT_LE] THEN
          CONJ_TAC THENL [HolLight.ASM SET_TAC [], DISCH_TAC] THEN
          FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [h16]) THEN
          REWRITE_TAC [IN_ELIM_THM, NOT_EXISTS_THM] THEN
          X_GEN_TAC ([[y:real^N]]) THEN STRIP_TAC THEN
          FIRST_X_ASSUM (DISJ_CASES_TAC o HolLight.MATCH_MP h17) THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
          MP_TAC (← HolLight.ASSUME ([[(x:real^N) IN relative_interior f]])) THEN
          REWRITE_TAC [IN_RELATIVE_INTERIOR_CBALL] THEN
          DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
          REWRITE_TAC [NOT_EXISTS_THM] THEN X_GEN_TAC ([[e:real]]) THEN
          DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
          REWRITE_TAC [SUBSET, IN_INTER, IN_CBALL] THEN
          SUBGOAL_THEN ([[~(y:real^N = x)]]) ASSUME_TAC THENL
           [ASM_MESON_TAC [REAL_LT_REFL], ALL_TAC] THEN
          DISCH_THEN (MP_TAC o HolLight.SPEC ([[x + e / norm(y - x) % (x - y):real^N]])) THEN
          SUBGOAL_THEN ([[(x:real^N) IN affine hull f /\ y IN affine hull f]]) STRIP_ASSUME_TAC THENL
           [ASM_MESON_TAC [RELATIVE_INTERIOR_SUBSET, SUBSET, HULL_SUBSET],
            ASM_SIMP_TAC [IN_AFFINE_ADD_MUL_DIFF, AFFINE_AFFINE_HULL]] THEN
          REWRITE_TAC [h18] THEN
          REWRITE_TAC [NOT_IMP] THEN CONJ_TAC THENL
           [ASM_SIMP_TAC [NORM_MUL, REAL_ABS_DIV, REAL_ABS_NORM, NORM_SUB,
                         REAL_DIV_RMUL, NORM_EQ_0, VECTOR_SUB_EQ] THEN
            ASM_REAL_ARITH_TAC,
            DISCH_TAC] THEN
          SUBGOAL_THEN ([[(x + e / norm(y - x) % (x - y):real^N) IN s]]) MP_TAC THENL
           [ASM_MESON_TAC [SUBSET, FACE_OF_IMP_SUBSET], ALL_TAC] THEN
          EXPAND_TAC "s" THEN REWRITE_TAC [IN_INTERS] THEN
          DISCH_THEN (MP_TAC o HolLight.SPEC ([[h:real^N->bool]])) THEN
          ASM_REWRITE_TAC [] THEN
          FIRST_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.RAND_CONV) [(← HolLight.SYM (← HolLight.CONJUNCT2 (← HolLight.MATCH_MP th (← HolLight.ASSUME ([[(h:real^N->bool) IN H]])))))])) THEN
          ASM_REWRITE_TAC [IN_ELIM_THM, DOT_RADD, REAL_ADD_LID, DOT_RMUL] THEN
          ASM_REWRITE_TAC [DOT_RSUB, REAL_SUB_LZERO, REAL_NOT_LE] THEN
          MATCH_MP_TAC REAL_LT_MUL THEN
          ASM_SIMP_TAC [REAL_LT_DIV, NORM_POS_LT, VECTOR_SUB_EQ] THEN
          ASM_REAL_ARITH_TAC,
          ALL_TAC] THEN
        UNDISCH_TAC ([[~(relative_interior f:real^N->bool = {})]]) THEN
        REWRITE_TAC [(← HolLight.GSYM MEMBER_NOT_EMPTY), hyperplane_cell] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[z:real^N]]) THEN
        GEN_REWRITE_TAC HolLight.RAND_CONV [EXTENSION] THEN
        ONCE_ASM_REWRITE_TAC [] THEN EXPAND_TAC "A" THEN
        REWRITE_TAC [IN_INTERS, FORALL_IN_GSPEC] THEN
        DISCH_THEN (fun th => X_GEN_TAC ([[x:real^N]]) THEN MP_TAC th) THEN
        GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.RAND_CONV) [IN] THEN
        REWRITE_TAC [hyperplane_equiv, FORALL_IN_IMAGE] THEN
        MATCH_MP_TAC h19 THEN
        X_GEN_TAC ([[h:real^N->bool]]) THEN
        ASM_CASES_TAC ([[(h:real^N->bool) IN H]]) THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [hyperplane_side, REAL_SUB_RZERO] THEN
        REPEAT (COND_CASES_TAC THEN
          SIMP_TAC [IN_ELIM_THM] THENL [MESON_TAC [REAL_SGN_EQ], ALL_TAC]) THEN
        MESON_TAC [REAL_SGN_EQ],
        X_GEN_TAC ([[c:real^N->bool]]) THEN STRIP_TAC THEN
        ONCE_REWRITE_TAC [(← HolLight.GSYM AFF_DIM_AFFINE_HULL)] THEN
        REWRITE_TAC [AFFINE_HULL_CLOSURE] THEN
        ASM_REWRITE_TAC [AFF_DIM_AFFINE_HULL] THEN CONJ_TAC THENL
         [ALL_TAC,
          MATCH_MP_TAC EQ_TRANS THEN
          EXISTS_TAC ([[relative_interior c:real^N->bool]]) THEN CONJ_TAC THENL
           [MATCH_MP_TAC CONVEX_RELATIVE_INTERIOR_CLOSURE THEN
            ASM_MESON_TAC [HYPERPLANE_CELL_CONVEX],
            ASM_MESON_TAC [HYPERPLANE_CELL_RELATIVE_INTERIOR]]] THEN
        SUBGOAL_THEN ([[?J. J SUBSET H /\
            c = INTERS {{x | (fa(h:real^N->bool)) dot x < &0} | h IN J} INTER
                INTERS {{x:real^N | (fa h) dot x = &0} | h IN (H DIFF J)}]]) MP_TAC THENL
         [FIRST_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [HYPERPLANE_CELL]) THEN
          EXPAND_TAC "A" THEN REWRITE_TAC [hyperplane_equiv, FORALL_IN_IMAGE] THEN
          DISCH_THEN (X_CHOOSE_THEN ([[z:real^N]]) MP_TAC) THEN
          REWRITE_TAC [hyperplane_side, REAL_SUB_RZERO] THEN
          GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV o HolLight.ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
          DISCH_THEN (ASSUME_TAC o HolLight.SYM) THEN EXISTS_TAC ([[{h:real^N->bool | h IN H /\
                            real_sgn(fa h dot (z:real^N)) = -- &1}]]) THEN
          REWRITE_TAC [h20] THEN
          REWRITE_TAC [(← HolLight.GSYM INTERS_UNION)] THEN EXPAND_TAC "c" THEN
          GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN X_GEN_TAC ([[y:real^N]]) THEN
          REWRITE_TAC [IN_ELIM_THM, IN_INTERS] THEN REWRITE_TAC [IN_UNION] THEN
          REWRITE_TAC [h21,
                      FORALL_AND_THM] THEN
          REWRITE_TAC [FORALL_IN_GSPEC] THEN
          REWRITE_TAC [IN_DIFF, IN_ELIM_THM] THEN
          REWRITE_TAC [h22] THEN
          REWRITE_TAC [AND_FORALL_THM] THEN AP_TERM_TAC THEN
          REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC ([[h:real^N->bool]]) THEN
          ASM_CASES_TAC ([[(h:real^N->bool) IN H]]) THEN ASM_REWRITE_TAC [] THEN
          REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (← HolLight.SPEC ([[(fa:(real^N->bool)->real^N) h dot z]]) REAL_SGN_CASES) THEN
          ASM_REWRITE_TAC [] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
          REWRITE_TAC [REAL_SGN_EQ] THEN
          SUBGOAL_THEN ([[?x:real^N. x IN c /\ x IN s]]) MP_TAC THENL
           [ASM_MESON_TAC [MEMBER_NOT_EMPTY, SUBSET, NONEMPTY_HYPERPLANE_CELL],
            MATCH_MP_TAC h23] THEN
          MAP_EVERY EXPAND_TAC ["s", "c"] THEN
          REWRITE_TAC [IN_INTERS, IN_ELIM_THM, NOT_EXISTS_THM] THEN
          X_GEN_TAC ([[x:real^N]]) THEN REWRITE_TAC [AND_FORALL_THM] THEN
          DISCH_THEN (MP_TAC o HolLight.SPEC ([[h:real^N->bool]])) THEN
          ASM_REWRITE_TAC [REAL_SGN_EQ] THEN
          DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
          FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[h:real^N->bool]])) THEN
          ASM_REWRITE_TAC [] THEN
          DISCH_THEN (SUBST1_TAC o HolLight.SYM o HolLight.CONJUNCT2) THEN
          REWRITE_TAC [IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC,
          DISCH_THEN (STRIP_ASSUME_TAC o HolLight.GSYM)] THEN
        EXPAND_TAC "c" THEN
        HolCore.Lib.W (MP_TAC o HolLight.PART_MATCH (HolCore.Equal.lhand o HolCore.Kernel.rand) CLOSURE_INTER_CONVEX o
          HolCore.Equal.lhand o HolLight.snd) THEN
        ANTS_TAC THENL
         [SIMP_TAC [CONVEX_INTERS, FORALL_IN_GSPEC, CONVEX_HALFSPACE_LT,
                   CONVEX_HYPERPLANE] THEN
          HolCore.Lib.W (MP_TAC o HolLight.PART_MATCH (HolCore.Equal.lhand o HolCore.Kernel.rand) RELATIVE_INTERIOR_OPEN o
            HolCore.Equal.lhand o HolCore.Equal.lhand o HolCore.Kernel.rand o HolLight.snd) THEN
          ANTS_TAC THENL
           [MATCH_MP_TAC OPEN_INTERS THEN
            ONCE_REWRITE_TAC [SIMPLE_IMAGE] THEN
            REWRITE_TAC [FORALL_IN_IMAGE, OPEN_HALFSPACE_LT] THEN
            MATCH_MP_TAC FINITE_IMAGE THEN ASM_MESON_TAC [FINITE_SUBSET],
            DISCH_THEN SUBST1_TAC] THEN
          HolCore.Lib.W (MP_TAC o HolLight.PART_MATCH (HolCore.Equal.lhand o HolCore.Kernel.rand) RELATIVE_INTERIOR_OPEN_IN o
            HolCore.Kernel.rand o HolCore.Equal.lhand o HolCore.Kernel.rand o HolLight.snd) THEN
          ANTS_TAC THENL
           [MATCH_MP_TAC h24 THEN
            REWRITE_TAC [SUBSET_UNIV, TOPSPACE_EUCLIDEAN] THEN
            REWRITE_TAC [AFFINE_HULL_EQ] THEN
            SIMP_TAC [AFFINE_INTERS, AFFINE_HYPERPLANE, FORALL_IN_GSPEC],
            DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [] THEN
            ASM_MESON_TAC [NONEMPTY_HYPERPLANE_CELL]],
          ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN
        SIMP_TAC [CLOSURE_INTERS_CONVEX_OPEN, FORALL_IN_GSPEC,
                 CONVEX_HALFSPACE_LT, OPEN_HALFSPACE_LT] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [EMPTY_FACE_OF, INTER_EMPTY] THEN
        SUBGOAL_THEN ([[IMAGE closure {{x | fa h dot x < &0} | h IN J} =
        {{x | (fa:(real^N->bool)->real^N) h dot x <= &0} | h IN J}]]) SUBST1_TAC THENL
         [ONCE_REWRITE_TAC [SIMPLE_IMAGE] THEN
          REWRITE_TAC [(← HolLight.GSYM IMAGE_o), o_DEF] THEN MATCH_MP_TAC IMAGE_EQ THEN
          GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [] THEN
          MATCH_MP_TAC CLOSURE_HALFSPACE_LT THEN HolLight.ASM SET_TAC [],
          ALL_TAC] THEN
        SUBGOAL_THEN ([[closure (INTERS {{x | fa h dot x = &0} | h IN H DIFF J}) =
       INTERS {{x | (fa:(real^N->bool)->real^N) h dot x = &0} | h IN H DIFF J}]]) SUBST1_TAC THENL
         [REWRITE_TAC [CLOSURE_EQ] THEN
          SIMP_TAC [CLOSED_INTERS, FORALL_IN_GSPEC, CLOSED_HYPERPLANE],
          ALL_TAC] THEN
        ASM_CASES_TAC ([[J:(real^N->bool)->bool = H]]) THENL
         [ASM_REWRITE_TAC [DIFF_EQ_EMPTY, INTER_UNIV, NOT_IN_EMPTY,
                          h25, INTERS_0] THEN
          FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP FACE_OF_REFL o
           HolLight.MATCH_MP POLYHEDRON_IMP_CONVEX) THEN
          MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          EXPAND_TAC "s" THEN AP_TERM_TAC THEN
          MATCH_MP_TAC h26 THEN
          ASM_SIMP_TAC [],
          ALL_TAC] THEN
        SUBGOAL_THEN ([[INTERS {{x | fa(h:real^N->bool) dot x <= &0} | h IN J} INTER
        INTERS {{x:real^N | fa h dot x = &0} | h IN H DIFF J} =
        INTERS {s INTER {x | fa h dot x = &0} | h IN H DIFF J}]]) SUBST1_TAC THENL
         [ONCE_REWRITE_TAC [SIMPLE_IMAGE] THEN REWRITE_TAC [INTERS_IMAGE] THEN
          GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN X_GEN_TAC ([[y:real^N]]) THEN
          REWRITE_TAC [IN_INTER, IN_ELIM_THM] THEN
          ASM_CASES_TAC ([[(y:real^N) IN s]]) THEN ASM_REWRITE_TAC [] THENL
           [MATCH_MP_TAC h27 THEN
            UNDISCH_TAC ([[(y:real^N) IN s]]) THEN EXPAND_TAC "s" THEN
            REWRITE_TAC [IN_INTERS] THEN MATCH_MP_TAC MONO_FORALL THEN
            X_GEN_TAC ([[h:real^N->bool]]) THEN
            DISCH_THEN (fun th => DISCH_TAC THEN MP_TAC th) THEN
            ANTS_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
            FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[h:real^N->bool]])) THEN
            ANTS_TAC THENL [HolLight.ASM SET_TAC [], SET_TAC []],
            UNDISCH_TAC ([[~((y:real^N) IN s)]]) THEN MATCH_MP_TAC h28 THEN
            CONJ_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
            EXPAND_TAC "s" THEN REWRITE_TAC [IN_INTERS, AND_FORALL_THM] THEN
            MATCH_MP_TAC MONO_FORALL THEN
            X_GEN_TAC ([[h:real^N->bool]]) THEN
            DISCH_THEN (fun th => DISCH_TAC THEN MP_TAC th) THEN
            FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[h:real^N->bool]])) THEN
            ANTS_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
            DISCH_THEN (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.RAND_CONV) [(← HolLight.GSYM (← HolLight.CONJUNCT2 th))])) THEN
            ASM_REWRITE_TAC [IN_DIFF, IN_ELIM_THM] THEN
            ASM_CASES_TAC ([[(h:real^N->bool) IN J]]) THEN
            ASM_SIMP_TAC [REAL_LE_REFL]],
          ALL_TAC] THEN
        MATCH_MP_TAC FACE_OF_INTERS THEN
        CONJ_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
        REWRITE_TAC [FORALL_IN_GSPEC] THEN
        X_GEN_TAC ([[h:real^N->bool]]) THEN REWRITE_TAC [IN_DIFF] THEN STRIP_TAC THEN
        MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE THEN
        ASM_SIMP_TAC [POLYHEDRON_IMP_CONVEX] THEN X_GEN_TAC ([[y:real^N]]) THEN
        EXPAND_TAC "s" THEN REWRITE_TAC [IN_INTERS] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[h:real^N->bool]])) THEN ASM_REWRITE_TAC [] THEN
        FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[h:real^N->bool]])) THEN
        ANTS_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
        DISCH_THEN (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV) [(← HolLight.GSYM (← HolLight.CONJUNCT2 th))])) THEN
        REWRITE_TAC [IN_ELIM_THM]],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!h. h IN H ==> hyperplane_cellcomplex A ((:real^N) DIFF h)]]) ASSUME_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_MONO THEN
      EXISTS_TAC ([[{((fa:(real^N->bool)->real^N) h,&0)}]]) THEN CONJ_TAC THENL
       [MATCH_MP_TAC HYPERPLANE_CELL_CELLCOMPLEX THEN
        ASM_SIMP_TAC [HYPERPLANE_CELL_SING] THEN REPEAT DISJ2_TAC THEN
        FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[h:real^N->bool]])) THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [(← HolLight.SYM (← HolLight.CONJUNCT2 th))])) THEN
        REWRITE_TAC [EXTENSION, IN_DIFF, IN_ELIM_THM, IN_UNIV] THEN
        REAL_ARITH_TAC2,
        EXPAND_TAC "A" THEN
        REWRITE_TAC [IN_IMAGE, SUBSET, FORALL_UNWIND_THM2, IN_SING] THEN
        ASM_MESON_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!h:real^N->bool. h IN H ==> hyperplane_cellcomplex A h]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [HYPERPLANE_CELLCOMPLEX_COMPL,
                    COMPL_COMPL],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[hyperplane_cellcomplex A (s:real^N->bool)]]) ASSUME_TAC THENL
     [EXPAND_TAC "s" THEN MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_INTERS THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    MP_TAC (← HolLight.ISPECL [([[A:real^N#real->bool]]),
                   ([[INTERS H:real^N->bool]]),
                   ([[(:real^N) DIFF INTERS H]])] EULER_CHARACTERISTIC_CELLCOMPLEX_UNION) THEN
    REWRITE_TAC [h29] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC [HYPERPLANE_CELLCOMPLEX_DIFF, HYPERPLANE_CELLCOMPLEX_UNIV],
      REWRITE_TAC [h30]] THEN
    REWRITE_TAC [DIFF_INTERS] THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC h31 THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC ([[euler_characteristic {} (:real^N)]]) THEN CONJ_TAC THENL
       [MATCH_MP_TAC EULER_CHARACTERSTIC_INVARIANT THEN
        ASM_REWRITE_TAC [FINITE_EMPTY] THEN CONJ_TAC THENL
         [MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_MONO THEN
          EXISTS_TAC ([[{}:real^N#real->bool]]) THEN REWRITE_TAC [EMPTY_SUBSET],
          ALL_TAC] THEN
        MATCH_MP_TAC HYPERPLANE_CELL_CELLCOMPLEX THEN
        REWRITE_TAC [HYPERPLANE_CELL_EMPTY],
        SIMP_TAC [EULER_CHARACTERISTIC_CELL, HYPERPLANE_CELL_EMPTY] THEN
        REWRITE_TAC [AFF_DIM_UNIV, NUM_OF_INT_OF_NUM]],
      ALL_TAC] THEN
    HolCore.Lib.W (MP_TAC o HolLight.PART_MATCH (HolCore.Equal.lhs o HolCore.Kernel.rand) EULER_CHARACTERISTIC_INCLUSION_EXCLUSION o
      HolCore.Equal.lhand o HolLight.snd) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [FORALL_IN_GSPEC] THEN ONCE_REWRITE_TAC [SIMPLE_IMAGE] THEN
      ASM_SIMP_TAC [FINITE_IMAGE],
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC ([[sum {t | t SUBSET {(:real^N) DIFF t | t IN H} /\ ~(t = {})}
             (\t. -- &1 pow (CARD t + 1) * (--(&1)) pow (dimindex(:N)))]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC [FORALL_IN_GSPEC] THEN
      REWRITE_TAC [SIMPLE_IMAGE, IMP_CONJ, FORALL_SUBSET_IMAGE] THEN
      X_GEN_TAC ([[J:(real^N->bool)->bool]]) THEN DISCH_TAC THEN
      REWRITE_TAC [IMAGE_EQ_EMPTY] THEN DISCH_TAC THEN AP_TERM_TAC THEN
      ABBREV_TAC ([[B = IMAGE (\h:real^N->bool. fa h:real^N,&0) J]]) THEN
      SUBGOAL_THEN ([[(B:real^N#real->bool) SUBSET A]]) ASSUME_TAC THENL
       [HolLight.ASM SET_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN ([[INTERS (IMAGE (\t. (:real^N) DIFF t) H) =
      IMAGE (--) (interior s)]]) ASSUME_TAC THENL
       [MP_TAC (← HolLight.ISPECL [([[s:real^N->bool]]), ([[H:(real^N->bool)->bool]]),
                       ([[fa:(real^N->bool)->real^N]]),
                       ([[\h:real^N->bool. &0]])] RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT) THEN
        ASM_SIMP_TAC [INTER_UNIV] THEN
        ASM_SIMP_TAC [RELATIVE_INTERIOR_INTERIOR] THEN
        DISCH_THEN ((fun _ => ALL_TAC)) THEN
        CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
        REWRITE_TAC [h32, EXISTS_REFL] THEN
        X_GEN_TAC ([[x:real^N]]) THEN REWRITE_TAC [IN_INTERS, IN_ELIM_THM] THEN
        REWRITE_TAC [FORALL_IN_IMAGE, IN_DIFF, IN_UNIV] THEN
        MATCH_MP_TAC h33 THEN
        CONJ_TAC THENL
         [EXPAND_TAC "s" THEN REWRITE_TAC [IN_INTERS] THEN
          MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC ([[h:real^N->bool]]) THEN
          ASM_CASES_TAC ([[(h:real^N->bool) IN H]]) THEN ASM_REWRITE_TAC [] THEN
          HolLight.ASM SET_TAC [REAL_LT_IMP_LE],
          MATCH_MP_TAC h34 THEN
          X_GEN_TAC ([[h:real^N->bool]]) THEN DISCH_TAC THEN
          FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [(← HolLight.SYM (← HolLight.CONJUNCT2 (← HolLight.MATCH_MP th (← HolLight.ASSUME ([[(h:real^N->bool) IN H]])))))])) THEN
          REWRITE_TAC [IN_ELIM_THM, DOT_RNEG] THEN REAL_ARITH_TAC2],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[hyperplane_cell B (INTERS (IMAGE (\t. (:real^N) DIFF t) J))]]) ASSUME_TAC THENL
       [SUBGOAL_THEN ([[~(INTERS (IMAGE (\t. (:real^N) DIFF t) J) = {})]]) MP_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
        REWRITE_TAC [hyperplane_cell, (← HolLight.GSYM MEMBER_NOT_EMPTY), IN_INTERS] THEN
        REWRITE_TAC [FORALL_IN_IMAGE] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[z:real^N]]) THEN
        REWRITE_TAC [IN_UNIV, IN_DIFF] THEN
        GEN_REWRITE_TAC HolLight.RAND_CONV [EXTENSION] THEN
        DISCH_THEN (fun th => X_GEN_TAC ([[x:real^N]]) THEN MP_TAC th) THEN
        REWRITE_TAC [IN_INTERS, FORALL_IN_IMAGE, IN_DIFF, IN_UNIV] THEN
        GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.RAND_CONV) [IN] THEN
        REWRITE_TAC [hyperplane_equiv] THEN EXPAND_TAC "B" THEN
        REWRITE_TAC [FORALL_IN_IMAGE, hyperplane_side] THEN
        MATCH_MP_TAC h35 THEN
        X_GEN_TAC ([[h:real^N->bool]]) THEN
        ASM_CASES_TAC ([[(h:real^N->bool) IN J]]) THEN ASM_REWRITE_TAC [] THEN
        SUBGOAL_THEN ([[(h:real^N->bool) IN H]]) ASSUME_TAC THENL
         [HolLight.ASM SET_TAC [], ALL_TAC] THEN
        FIRST_X_ASSUM (MP_TAC o HolLight.CONJUNCT2 o HolCore.Lib.C HolLight.MATCH_MP (← HolLight.ASSUME ([[(h:real^N->bool) IN H]]))) THEN
        DISCH_THEN (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [(← HolLight.SYM th)] THEN
          GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [(← HolLight.SYM th)])) THEN
        REWRITE_TAC [IN_ELIM_THM, REAL_SUB_RZERO, REAL_NOT_LE] THEN
        MESON_TAC [REAL_SGN_EQ, real_gt],
        ALL_TAC] THEN
      MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC ([[euler_characteristic B (INTERS (IMAGE (\t. (:real^N) DIFF t) J))]]) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC EULER_CHARACTERSTIC_INVARIANT THEN
        ASM_SIMP_TAC [HYPERPLANE_CELL_CELLCOMPLEX] THEN
        CONJ_TAC THENL [ASM_MESON_TAC [FINITE_SUBSET], ALL_TAC] THEN
        MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_MONO THEN
        EXISTS_TAC ([[B:real^N#real->bool]]) THEN
        ASM_SIMP_TAC [HYPERPLANE_CELL_CELLCOMPLEX],
        ALL_TAC] THEN
      ASM_SIMP_TAC [EULER_CHARACTERISTIC_CELL] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC h36 THEN
      REWRITE_TAC [AFF_DIM_EQ_FULL] THEN
      MATCH_MP_TAC h37 THEN
      EXISTS_TAC ([[affine hull (INTERS (IMAGE (\t. (:real^N) DIFF t) H))]]) THEN
      CONJ_TAC THENL [MATCH_MP_TAC HULL_MONO THEN HolLight.ASM SET_TAC [], ALL_TAC] THEN
      MATCH_MP_TAC AFFINE_HULL_OPEN THEN ASM_REWRITE_TAC [] THEN
      ASM_SIMP_TAC [IMAGE_EQ_EMPTY, OPEN_NEGATIONS, OPEN_INTERIOR],
      ALL_TAC] THEN
    REWRITE_TAC [SUM_RMUL] THEN
    MATCH_MP_TAC h38 THEN
    MP_TAC (← HolLight.ISPECL [([[\t:(real^N->bool)->bool. CARD t]]),
                   ([[\t:(real^N->bool)->bool. (-- &1) pow (CARD t + 1)]]),
                   ([[{t |  t SUBSET
                     {(:real^N) DIFF t | t IN H} /\ ~(t = {})}]]),
                   ([[1..CARD(H:(real^N->bool)->bool)]])] SUM_GROUP) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC ([[{t |  t SUBSET {(:real^N) DIFF t | t IN H}}]]) THEN
        CONJ_TAC THENL [ALL_TAC, SET_TAC []] THEN
        MATCH_MP_TAC FINITE_POWERSET THEN REWRITE_TAC [SIMPLE_IMAGE] THEN
        ASM_SIMP_TAC [FINITE_IMAGE],
        GEN_REWRITE_TAC HolCore.Lib.I [SUBSET] THEN REWRITE_TAC [FORALL_IN_IMAGE] THEN
        REWRITE_TAC [FORALL_IN_GSPEC, IN_NUMSEG] THEN
        REWRITE_TAC [SIMPLE_IMAGE, FORALL_SUBSET_IMAGE, IMP_CONJ] THEN
        X_GEN_TAC ([[J:(real^N->bool)->bool]]) THEN DISCH_TAC THEN
        REWRITE_TAC [IMAGE_EQ_EMPTY] THEN DISCH_TAC THEN
        SUBGOAL_THEN ([[FINITE(J:(real^N->bool)->bool)]]) ASSUME_TAC THENL
         [ASM_MESON_TAC [FINITE_SUBSET], ALL_TAC] THEN
        ASM_SIMP_TAC [CARD_EQ_0, FINITE_IMAGE, h39,
                     IMAGE_EQ_EMPTY] THEN
        MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC ([[CARD(J:(real^N->bool)->bool)]]) THEN
        ASM_SIMP_TAC [CARD_SUBSET, CARD_IMAGE_LE]],
      REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o HolLight.SYM)] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC ([[sum (1..CARD(H:(real^N->bool)->bool))
        (\n. -- &1 pow (n + 1) * &(binom(CARD H,n)))]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC ([[n:num]]) THEN
      REWRITE_TAC [IN_NUMSEG] THEN DISCH_TAC THEN
      SIMP_TAC [IN_ELIM_THM] THEN
      HolCore.Lib.W (MP_TAC o HolLight.PART_MATCH (HolCore.Equal.lhs o HolCore.Kernel.rand) SUM_CONST o HolCore.Equal.lhand o HolLight.snd) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC ([[{t |  t SUBSET {(:real^N) DIFF t | t IN H}}]]) THEN
        CONJ_TAC THENL [ALL_TAC, SET_TAC []] THEN
        MATCH_MP_TAC FINITE_POWERSET THEN REWRITE_TAC [SIMPLE_IMAGE] THEN
        ASM_SIMP_TAC [FINITE_IMAGE],
        DISCH_THEN SUBST1_TAC] THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [REAL_MUL_SYM] THEN AP_TERM_TAC THEN
      AP_TERM_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC ([[CARD {t | t SUBSET {(:real^N) DIFF t | t IN H} /\
                          t HAS_SIZE n}]]) THEN
      CONJ_TAC THENL
       [AP_TERM_TAC THEN GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN
        X_GEN_TAC ([[t:(real^N->bool)->bool]]) THEN
        REWRITE_TAC [IN_ELIM_THM] THEN
        ASM_CASES_TAC ([[t:(real^N->bool)->bool = {}]]) THEN
        ASM_REWRITE_TAC [HAS_SIZE, CARD_CLAUSES, FINITE_EMPTY] THENL
         [ASM_ARITH_TAC, ALL_TAC] THEN
        MATCH_MP_TAC h40 THEN
        SPEC_TAC (([[t:(real^N->bool)->bool]]), ([[u:(real^N->bool)->bool]])) THEN
        REWRITE_TAC [SIMPLE_IMAGE, FORALL_SUBSET_IMAGE] THEN
        ASM_MESON_TAC [FINITE_IMAGE, FINITE_SUBSET],
        ALL_TAC] THEN
      MP_TAC (← HolLight.ISPECL [([[CARD(H:(real^N->bool)->bool)]]),
                     ([[n:num]]), ([[{(:real^N) DIFF t | t IN H}]])] NUMBER_OF_COMBINATIONS) THEN
      ANTS_TAC THENL [ALL_TAC, SIMP_TAC [HAS_SIZE]] THEN
      REWRITE_TAC [SIMPLE_IMAGE] THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
      ASM_REWRITE_TAC [(← HolLight.GSYM FINITE_HAS_SIZE)] THEN SET_TAC [],
      ALL_TAC] THEN
    MP_TAC (← HolLight.ISPECL [([[CARD(H:(real^N->bool)->bool)]]), ([[--(&1)]]), ([[&1]])] REAL_BINOMIAL_THEOREM) THEN
    REWRITE_TAC [REAL_POW_ONE, REAL_MUL_RID, REAL_ADD_LINV] THEN
    SIMP_TAC [SUM_CLAUSES_LEFT, REAL_POW_ADD, REAL_POW_ONE, LE_0] THEN
    REWRITE_TAC [h41] THEN
    REWRITE_TAC [real_pow, SUM_NEG, ADD_CLAUSES, REAL_MUL_RID] THEN
    REWRITE_TAC [binom] THEN MATCH_MP_TAC h42 THEN
    REWRITE_TAC [REAL_POW_ZERO] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    UNDISCH_TAC ([[CARD(H:(real^N->bool)->bool) = 0]]) THEN
    ASM_SIMP_TAC [CARD_EQ_0] THEN DISCH_THEN SUBST_ALL_TAC THEN HolLight.ASM SET_TAC [])
  : ExceptT String IO thm).run
#eval EULER_POLYHEDRAL_CONE

/- ------------------------------------------------------------------------- -/
/- Euler-Poincare relation for special (n-1)-dimensional polytope.           -/
/- ------------------------------------------------------------------------- -/

#eval phrase 60
def EULER_POINCARE_LEMMA : thm := keep "EULER_POINCARE_LEMMA" fun _ => (do
  let h23 ← va (← ExceptT.mk [[c % x:real^N = vec 0 + c % (x - vec 0)]])
  let h22 ← sr (← ExceptT.mk [[x IN s /\ s SUBSET P hull s ==> x IN P hull s]])
  let h21 ← sr (← ExceptT.mk [[!t. ~(x IN t) /\ s SUBSET t ==> ~(x IN s)]])
  let h20 ← tt (← ExceptT.mk [[~p /\ q ==> ~(p <=> q)]])
  let h19 ← ia (← ExceptT.mk [[f < a /\ a <= f + &1 ==> a:int = f + &1]])
  let h18 ← sr (← ExceptT.mk [[a IN s /\ ~(s = {a}) ==> ?y. y IN s /\ ~(y = a)]])
  let h17 ← ia (← ExceptT.mk [[&0:int < &d + &1]])
  let h16 ← rr (← ExceptT.mk [[a + b = cx ==> &0 <= a ==> b <= &1 * cx]])
  let h15 ← rr (← ExceptT.mk [[inv(cx) * x:real = x / cx]])
  let h14 ← va (← ExceptT.mk [[x % b:real^N = y % a + z % b <=> (x - z) % b = y % a]])
  let h13 ← va (← ExceptT.mk [[x % a:real^N = y % a + z % b <=> (x - y) % a = z % b]])
  let h12 ← rr (← ExceptT.mk [[&0 < b /\ &0 <= a ==> ~(&0 = a + b)]])
  let h11 ← rr (← ExceptT.mk [[&0 < a /\ &0 <= b ==> ~(&0 = a + b)]])
  let h10 ← tt (← ExceptT.mk [[(a ==> ~b) ==> a /\ b ==> c]])
  let h9 ← ia (← ExceptT.mk [[&0:int < &d + &1]])
  let h8 ← sr (← ExceptT.mk [[a IN s /\ ~(s = {a}) ==> ?y. y IN s /\ ~(y = a)]])
  let h7 ← rr (← ExceptT.mk [[s = --t ==> (&0 + &1) + s = &0 ==> t = &1]])
  let h6 ← rr (← ExceptT.mk [[&0 < b /\ &0 <= a ==> ~(&0 = a + b)]])
  let h5 ← rr (← ExceptT.mk [[&0 < a /\ &0 <= b ==> ~(&0 = a + b)]])
  let h4 ← sr (← ExceptT.mk [[s PSUBSET t ==> s' = s /\ t' = t ==> s' PSUBSET t']])
  let h3 ← ia (← ExceptT.mk [[a:int < b ==> a = n ==> ~(b = n)]])
  let h2 ← sr (← ExceptT.mk [[s SUBSET h' ==> h SUBSET h' /\ ~(h PSUBSET h') ==> s SUBSET h]])
  let h1 ← ia (← ExceptT.mk [[--(&1):int = x - &1 <=> x = &0]])
  prove ([[!p:real^N->bool.
        2 <= dimindex(:N) /\ polytope p /\ affine hull p = {x | x$1 = &1}
        ==> sum (0..dimindex(:N)-1)
               (\d. (-- &1) pow d *
                    &(CARD {f | f face_of p /\ aff_dim f = &d })) = &1]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[basis 1:real^N]]), ([[&1]])] AFF_DIM_HYPERPLANE) THEN
    SIMP_TAC [BASIS_NONZERO, DOT_BASIS, DIMINDEX_GE_1, LE_REFL] THEN
    FIRST_ASSUM (SUBST1_TAC o HolLight.SYM) THEN REWRITE_TAC [AFF_DIM_AFFINE_HULL] THEN
    ASM_CASES_TAC ([[p:real^N->bool = {}]]) THENL
     [ASM_REWRITE_TAC [AFF_DIM_EMPTY] THEN
      REWRITE_TAC [h1] THEN
      SIMP_TAC [INT_OF_NUM_EQ, LE_1, DIMINDEX_GE_1],
      DISCH_TAC] THEN
    ABBREV_TAC ([[s:real^N->bool = conic hull p]]) THEN
    MP_TAC (← HolLight.ISPEC ([[s:real^N->bool]]) EULER_POLYHEDRAL_CONE) THEN
    SUBGOAL_THEN ([[!f. f SUBSET {x:real^N | x$1 = &1}
        ==> (conic hull f) INTER {x:real^N | x$1 = &1} = f]]) ASSUME_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
      ASM_SIMP_TAC [HULL_SUBSET, SUBSET_INTER] THEN
      REWRITE_TAC [SUBSET, CONIC_HULL_EXPLICIT, IN_INTER, IMP_CONJ] THEN
      REWRITE_TAC [FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [([[c:real]]), ([[x:real^N]])] THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [SUBSET]) THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC ([[x:real^N]])) THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN
      ASM_SIMP_TAC [VECTOR_MUL_COMPONENT, REAL_MUL_RID, VECTOR_MUL_LID],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[polyhedron(s:real^N->bool)]]) ASSUME_TAC THENL
     [EXPAND_TAC "s" THEN
      FIRST_X_ASSUM (X_CHOOSE_THEN ([[k:real^N->bool]]) MP_TAC o
        HolLight.GEN_REWRITE_RULE HolCore.Lib.I [polytope]) THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN (fun th => SUBST1_TAC th THEN ASSUME_TAC th) THEN
      MP_TAC (← HolLight.ISPEC ([[k:real^N->bool]]) CONVEX_CONE_HULL_SEPARATE_NONEMPTY) THEN
      ANTS_TAC THENL [ASM_MESON_TAC [CONVEX_HULL_EQ_EMPTY], ALL_TAC] THEN
      DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN
      MATCH_MP_TAC POLYHEDRON_CONVEX_CONE_HULL THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    FIRST_ASSUM (ASSUME_TAC o HolLight.MATCH_MP POLYHEDRON_IMP_CONVEX) THEN
    SUBGOAL_THEN ([[conic(s:real^N->bool)]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [CONIC_CONIC_HULL], ALL_TAC] THEN
    SUBGOAL_THEN ([[~(s = (:real^N))]]) ASSUME_TAC THENL
     [DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[p:real^N->bool]])) THEN
      ANTS_TAC THENL [ASM_MESON_TAC [HULL_SUBSET], ALL_TAC] THEN
      ASM_REWRITE_TAC [INTER_UNIV] THEN DISCH_THEN (ASSUME_TAC o HolLight.SYM) THEN
      UNDISCH_TAC ([[polytope(p:real^N->bool)]]) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP POLYTOPE_IMP_BOUNDED) THEN
      REWRITE_TAC [BOUNDED_POS, NOT_EXISTS_THM] THEN X_GEN_TAC ([[B:real]]) THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC ([[(lambda i. if i = 1 then &1 else B + &1):real^N]])) THEN
      SIMP_TAC [LAMBDA_BETA, DIMINDEX_GE_1, LE_REFL, IN_ELIM_THM] THEN
      REWRITE_TAC [REAL_NOT_LE] THEN
      MP_TAC (← HolLight.ISPECL [([[(lambda i. if i = 1 then &1 else B + &1):real^N]]), ([[2]])] COMPONENT_LE_NORM) THEN
      ASM_SIMP_TAC [ARITH, LAMBDA_BETA, DIMINDEX_GE_1, LE_REFL] THEN
      REAL_ARITH_TAC2,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[~(s:real^N->bool = {})]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [CONIC_HULL_EQ_EMPTY], ALL_TAC] THEN
    MP_TAC (← HolLight.ISPEC ([[s:real^N->bool]]) CONIC_CONTAINS_0) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[~(interior(s:real^N->bool) = {})]]) ASSUME_TAC THENL
     [DISCH_TAC THEN MP_TAC (← HolLight.ISPEC ([[s:real^N->bool]]) EMPTY_INTERIOR_SUBSET_HYPERPLANE) THEN
      ASM_REWRITE_TAC [NOT_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[a:real^N]]), ([[b:real]])] THEN STRIP_TAC THEN
      SUBGOAL_THEN ([[s SUBSET {x:real^N | x$1 = &1}]]) MP_TAC THENL
       [FIRST_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h2) THEN
        CONJ_TAC THENL
         [FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.SYM th)])) THEN
          MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [AFFINE_HYPERPLANE] THEN
          MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC ([[s:real^N->bool]]) THEN
          ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [HULL_SUBSET],
          DISCH_TAC THEN
          MP_TAC (← HolLight.ISPECL [([[a:real^N]]), ([[b:real]])] AFF_DIM_HYPERPLANE) THEN
          MP_TAC (← HolLight.ISPECL [([[basis 1:real^N]]), ([[&1]])] AFF_DIM_HYPERPLANE) THEN
          ASM_SIMP_TAC [BASIS_NONZERO, DOT_BASIS, DIMINDEX_GE_1, LE_REFL] THEN
          MATCH_MP_TAC h3 THEN
          MATCH_MP_TAC AFF_DIM_PSUBSET THEN FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h4) THEN
          REWRITE_TAC [AFFINE_HULL_EQ, AFFINE_HYPERPLANE] THEN
          MP_TAC (← HolLight.ISPECL [([[basis 1:real^N]]), ([[&1]])] AFFINE_HYPERPLANE) THEN
          SIMP_TAC [BASIS_NONZERO, DOT_BASIS, DIMINDEX_GE_1, LE_REFL]],
        REWRITE_TAC [SUBSET, NOT_FORALL_THM, NOT_IMP] THEN
        EXISTS_TAC ([[vec 0:real^N]]) THEN
        ASM_REWRITE_TAC [IN_ELIM_THM, VEC_COMPONENT] THEN REAL_ARITH_TAC2],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN ([[!x:real^N. x IN s /\ ~(x = vec 0) ==> &0 < x$1]]) ASSUME_TAC THENL
     [EXPAND_TAC "s" THEN REWRITE_TAC [CONIC_HULL_EXPLICIT, IMP_CONJ] THEN
      REWRITE_TAC [FORALL_IN_GSPEC, VECTOR_MUL_EQ_0, DE_MORGAN_THM] THEN
      MAP_EVERY X_GEN_TAC [([[c:real]]), ([[x:real^N]])] THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC [VECTOR_MUL_COMPONENT] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      SUBGOAL_THEN ([[(x:real^N) IN affine hull p]]) MP_TAC THENL
       [ASM_MESON_TAC [HULL_SUBSET, SUBSET], ASM_REWRITE_TAC []] THEN
      SIMP_TAC [IN_ELIM_THM, REAL_LT_01],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!x:real^N. x IN s ==> &0 <= x$1]]) ASSUME_TAC THENL
     [X_GEN_TAC ([[x:real^N]]) THEN DISCH_TAC THEN
      ASM_CASES_TAC ([[x:real^N = vec 0]]) THEN
      ASM_SIMP_TAC [VEC_COMPONENT, REAL_POS, REAL_LT_IMP_LE],
      ALL_TAC] THEN
    HolCore.Lib.W (MP_TAC o HolLight.PART_MATCH (HolCore.Equal.lhs o HolCore.Kernel.rand) SUM_CLAUSES_LEFT o
      HolCore.Equal.lhand o HolCore.Equal.lhand o HolLight.snd) THEN
    REWRITE_TAC [LE_0] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [AFF_DIM_EQ_0, real_pow, REAL_MUL_LID] THEN
    SUBGOAL_THEN ([[{f | f face_of s /\ (?a:real^N. f = {a})} = {{vec 0}}]]) (fun th => REWRITE_TAC [th]) THENL
     [GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM, IN_SING] THEN
      X_GEN_TAC ([[f:real^N->bool]]) THEN EQ_TAC THENL
       [DISCH_THEN (CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_TAC ([[a:real^N]]))) THEN
        ASM_REWRITE_TAC [FACE_OF_SING] THEN
        ASM_MESON_TAC [EXTREME_POINT_OF_CONIC],
        DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL [ALL_TAC, MESON_TAC []] THEN
        ASM_REWRITE_TAC [FACE_OF_SING, extreme_point_of, IN_SEGMENT] THEN
        MAP_EVERY X_GEN_TAC [([[a:real^N]]), ([[b:real^N]])] THEN STRIP_TAC THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        REWRITE_TAC [NOT_EXISTS_THM] THEN X_GEN_TAC ([[u:real]]) THEN
        REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        REWRITE_TAC [CART_EQ] THEN DISCH_THEN (MP_TAC o HolLight.SPEC ([[1]])) THEN
        REWRITE_TAC [LE_REFL, DIMINDEX_GE_1, VEC_COMPONENT] THEN
        REWRITE_TAC [VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT] THEN
        SUBGOAL_THEN ([[&0 < (a:real^N)$1 \/ &0 < (b:real^N)$1]]) DISJ_CASES_TAC THENL
         [ASM_MESON_TAC [],
          MATCH_MP_TAC h5,
          MATCH_MP_TAC h6] THEN
        ASM_SIMP_TAC [REAL_LE_MUL, REAL_LT_IMP_LE, REAL_LT_MUL, REAL_SUB_LT]],
      ALL_TAC] THEN
    SIMP_TAC [CARD_CLAUSES, FINITE_EMPTY, NOT_IN_EMPTY, (← HolLight.GSYM REAL_OF_NUM_SUC)] THEN
    MATCH_MP_TAC h7 THEN
    SUBGOAL_THEN ([[dimindex(:N) = (dimindex(:N)-1)+1]]) (fun th => GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [th]) THENL [ASM_ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [SUM_OFFSET, (← HolLight.GSYM SUM_NEG)] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC ([[d:num]]) THEN STRIP_TAC THEN
    REWRITE_TAC [REAL_POW_ADD, REAL_POW_1, REAL_MUL_RNEG, REAL_MUL_LNEG] THEN
    AP_TERM_TAC THEN REWRITE_TAC [REAL_MUL_RID] THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC BIJECTIONS_CARD_EQ THEN
    EXISTS_TAC ([[\f:real^N->bool. f INTER {x | x$1 = &1}]]) THEN
    EXISTS_TAC ([[\f:real^N->bool. conic hull f]]) THEN
    REWRITE_TAC [FORALL_IN_GSPEC] THEN CONJ_TAC THENL
     [DISJ1_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC ([[{f:real^N->bool | f face_of s}]]) THEN
      ASM_SIMP_TAC [FINITE_POLYHEDRON_FACES] THEN SET_TAC [],
      REWRITE_TAC [IN_ELIM_THM, (← HolLight.GSYM INT_OF_NUM_ADD)]] THEN
    SUBGOAL_THEN ([[!f:real^N->bool. f face_of p ==> conic hull f INTER {x | x$1 = &1} = f]]) ASSUME_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC ([[affine hull p:real^N->bool]]) THEN CONJ_TAC THENL
       [ASM_MESON_TAC [FACE_OF_IMP_SUBSET, HULL_SUBSET, SUBSET_TRANS],
        ASM_REWRITE_TAC [SUBSET_REFL]],
      ASM_SIMP_TAC []] THEN
    SUBGOAL_THEN ([[!f:real^N->bool. f face_of s ==> f INTER {x | x$1 = &1} face_of p]]) ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN ([[p = conic hull p INTER {x:real^N | x$1 = &1}]]) SUBST1_TAC THENL [ASM_MESON_TAC [FACE_OF_REFL, POLYTOPE_IMP_CONVEX], ALL_TAC] THEN
      MATCH_MP_TAC FACE_OF_SLICE THEN
      ASM_REWRITE_TAC [CONVEX_STANDARD_HYPERPLANE],
      ASM_SIMP_TAC []] THEN
    SUBGOAL_THEN ([[!f. f face_of s  /\ &0 < aff_dim f
        ==> conic hull (f INTER {x:real^N | x$1 = &1}) = f]]) ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [REWRITE_TAC [SUBSET, CONIC_HULL_EXPLICIT, FORALL_IN_GSPEC] THEN
        REWRITE_TAC [IN_INTER, IN_ELIM_THM] THEN
        ASM_MESON_TAC [FACE_OF_CONIC, conic],
        REWRITE_TAC [SUBSET, CONIC_HULL_EXPLICIT] THEN X_GEN_TAC ([[x:real^N]]) THEN
        DISCH_TAC THEN REWRITE_TAC [IN_ELIM_THM, IN_INTER] THEN
        ASM_CASES_TAC ([[x:real^N = vec 0]]) THENL
         [SUBGOAL_THEN ([[?y:real^N. y IN f /\ ~(y = vec 0)]]) STRIP_ASSUME_TAC THENL
           [MATCH_MP_TAC h8 THEN
            ASM_MESON_TAC [AFF_DIM_EQ_0, INT_LT_REFL],
            SUBGOAL_THEN ([[&0 < (y:real^N)$1]]) ASSUME_TAC THENL
             [ASM_MESON_TAC [FACE_OF_IMP_SUBSET, SUBSET], ALL_TAC] THEN
            EXISTS_TAC ([[&0]]) THEN ASM_REWRITE_TAC [REAL_POS, VECTOR_MUL_LZERO] THEN
            EXISTS_TAC ([[inv(y$1) % y:real^N]]) THEN
            ASM_SIMP_TAC [VECTOR_MUL_COMPONENT, REAL_MUL_LINV,
                         REAL_LT_IMP_NZ] THEN
            ASM_MESON_TAC [FACE_OF_CONIC, conic, REAL_LE_INV_EQ, REAL_LT_IMP_LE]],
          SUBGOAL_THEN ([[&0 < (x:real^N)$1]]) ASSUME_TAC THENL
           [ASM_MESON_TAC [FACE_OF_IMP_SUBSET, SUBSET], ALL_TAC] THEN
          EXISTS_TAC ([[(x:real^N)$1]]) THEN EXISTS_TAC ([[inv(x$1) % x:real^N]]) THEN
          ASM_SIMP_TAC [VECTOR_MUL_COMPONENT, REAL_MUL_LINV, REAL_LT_IMP_LE,
            REAL_LT_IMP_NZ, VECTOR_MUL_ASSOC, REAL_MUL_RINV, VECTOR_MUL_LID] THEN
          ASM_MESON_TAC [FACE_OF_CONIC, conic, REAL_LE_INV_EQ, REAL_LT_IMP_LE]]],
      ASM_SIMP_TAC [h9]] THEN
    SUBGOAL_THEN ([[!f:real^N->bool. f face_of p ==> (conic hull f) face_of s]]) ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_CASES_TAC ([[f:real^N->bool = {}]]) THEN
      ASM_REWRITE_TAC [CONIC_HULL_EMPTY, EMPTY_FACE_OF] THEN
      REWRITE_TAC [face_of] THEN REPEAT CONJ_TAC THENL
       [EXPAND_TAC "s" THEN MATCH_MP_TAC HULL_MONO THEN
        ASM_MESON_TAC [FACE_OF_IMP_SUBSET],
        ASM_MESON_TAC [CONVEX_CONIC_HULL, FACE_OF_IMP_CONVEX],
        ALL_TAC] THEN
      EXPAND_TAC "s" THEN REWRITE_TAC [CONIC_HULL_EXPLICIT, IMP_CONJ] THEN
      REWRITE_TAC [RIGHT_FORALL_IMP_THM, FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [([[ca:real]]), ([[a:real^N]])] THEN STRIP_TAC THEN
      MAP_EVERY X_GEN_TAC [([[cb:real]]), ([[b:real^N]])] THEN STRIP_TAC THEN
      MAP_EVERY X_GEN_TAC [([[cx:real]]), ([[x:real^N]])] THEN STRIP_TAC THEN
      ASM_CASES_TAC ([[cx % x:real^N = vec 0]]) THENL
       [ASM_REWRITE_TAC [IN_SEGMENT] THEN
        MATCH_MP_TAC h10 THEN
        DISCH_TAC THEN DISCH_THEN (X_CHOOSE_THEN ([[u:real]]) MP_TAC) THEN
        REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        REWRITE_TAC [CART_EQ] THEN DISCH_THEN (MP_TAC o HolLight.SPEC ([[1]])) THEN
        REWRITE_TAC [LE_REFL, DIMINDEX_GE_1, VEC_COMPONENT] THEN
        REWRITE_TAC [VECTOR_ADD_COMPONENT] THEN
        ONCE_REWRITE_TAC [VECTOR_MUL_COMPONENT] THEN
        SUBGOAL_THEN ([[&0 < (ca % a:real^N)$1 \/ &0 < (cb % b:real^N)$1]]) DISJ_CASES_TAC THENL
         [SUBGOAL_THEN ([[(ca % a:real^N) IN s /\ (cb % b:real^N) IN s]]) (fun th => ASM_MESON_TAC [th]) THEN
          ASM_MESON_TAC [conic, HULL_SUBSET, SUBSET],
          MATCH_MP_TAC h11,
          MATCH_MP_TAC h12] THEN
        ASM_SIMP_TAC [REAL_LE_MUL, REAL_LT_IMP_LE, REAL_LT_MUL, REAL_SUB_LT] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC [REAL_LT_IMP_LE, REAL_SUB_LT] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_MESON_TAC [conic, HULL_SUBSET, SUBSET],
        ALL_TAC] THEN
      UNDISCH_TAC ([[~(cx % x:real^N = vec 0)]]) THEN
      REWRITE_TAC [VECTOR_MUL_EQ_0, DE_MORGAN_THM] THEN STRIP_TAC THEN
      ASM_CASES_TAC ([[x:real^N = a]]) THENL
       [REWRITE_TAC [IN_SEGMENT] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN ([[u:real]]) MP_TAC)) THEN
        REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        ASM_REWRITE_TAC [VECTOR_MUL_ASSOC, h13] THEN
        DISCH_THEN (fun th => MP_TAC th THEN MP_TAC th) THEN
        GEN_REWRITE_TAC HolLight.LAND_CONV [CART_EQ] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[1]])) THEN
        REWRITE_TAC [LE_REFL, DIMINDEX_GE_1, VECTOR_MUL_COMPONENT] THEN
        SUBGOAL_THEN ([[(a:real^N) IN affine hull p /\ b IN affine hull p]]) MP_TAC THENL
         [ASM_MESON_TAC [FACE_OF_IMP_SUBSET, HULL_SUBSET, SUBSET], ALL_TAC] THEN
        ASM_REWRITE_TAC [IN_ELIM_THM] THEN
        DISCH_THEN (CONJUNCTS_THEN SUBST1_TAC) THEN
        REWRITE_TAC [REAL_MUL_RID] THEN DISCH_THEN SUBST1_TAC THEN
        ASM_SIMP_TAC [VECTOR_MUL_LCANCEL, REAL_ENTIRE, REAL_LT_IMP_NZ] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC [] THENL
         [CONJ_TAC THENL
           [MAP_EVERY EXISTS_TAC [([[ca:real]]), ([[a:real^N]])] THEN
            ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [],
            MAP_EVERY EXISTS_TAC [([[&0]]), ([[x:real^N]])] THEN
            ASM_REWRITE_TAC [VECTOR_MUL_LZERO, REAL_LE_REFL]],
          CONJ_TAC THENL [EXISTS_TAC ([[ca:real]]), EXISTS_TAC ([[cb:real]])] THEN
          EXISTS_TAC ([[x:real^N]]) THEN ASM_REWRITE_TAC []],
        ALL_TAC] THEN
      ASM_CASES_TAC ([[x:real^N = b]]) THENL
       [REWRITE_TAC [IN_SEGMENT] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN ([[u:real]]) MP_TAC)) THEN
        REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        ASM_REWRITE_TAC [VECTOR_MUL_ASSOC, h14] THEN
        DISCH_THEN (fun th => MP_TAC th THEN MP_TAC th) THEN
        GEN_REWRITE_TAC HolLight.LAND_CONV [CART_EQ] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[1]])) THEN
        REWRITE_TAC [LE_REFL, DIMINDEX_GE_1, VECTOR_MUL_COMPONENT] THEN
        SUBGOAL_THEN ([[(a:real^N) IN affine hull p /\ b IN affine hull p]]) MP_TAC THENL
         [ASM_MESON_TAC [FACE_OF_IMP_SUBSET, HULL_SUBSET, SUBSET], ALL_TAC] THEN
        ASM_REWRITE_TAC [IN_ELIM_THM] THEN
        DISCH_THEN (CONJUNCTS_THEN SUBST1_TAC) THEN
        REWRITE_TAC [REAL_MUL_RID] THEN DISCH_THEN SUBST1_TAC THEN
        ASM_SIMP_TAC [VECTOR_MUL_LCANCEL, REAL_ENTIRE,
                     REAL_LT_IMP_NE, REAL_SUB_0] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC [] THENL
         [CONJ_TAC THENL
           [MAP_EVERY EXISTS_TAC [([[&0]]), ([[x:real^N]])] THEN
            ASM_REWRITE_TAC [VECTOR_MUL_LZERO, REAL_LE_REFL],
            MAP_EVERY EXISTS_TAC [([[cb:real]]), ([[b:real^N]])] THEN
            ASM_REWRITE_TAC [] THEN ASM_MESON_TAC []],
          CONJ_TAC THENL [EXISTS_TAC ([[ca:real]]), EXISTS_TAC ([[cb:real]])] THEN
          EXISTS_TAC ([[x:real^N]]) THEN ASM_REWRITE_TAC []],
        ALL_TAC] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN ([[(x:real^N) IN segment(a,b)]]) ASSUME_TAC THENL
       [FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [IN_OPEN_SEGMENT]) THEN
        ASM_REWRITE_TAC [IN_OPEN_SEGMENT] THEN
        DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
        REWRITE_TAC [IN_SEGMENT] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[u:real]]) MP_TAC) THEN
        REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN (fun th => MP_TAC th THEN MP_TAC th) THEN
        GEN_REWRITE_TAC HolLight.LAND_CONV [CART_EQ] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[1]])) THEN
        REWRITE_TAC [LE_REFL, DIMINDEX_GE_1, VECTOR_ADD_COMPONENT,
                    VECTOR_MUL_COMPONENT] THEN
        SUBGOAL_THEN ([[(x:real^N) IN affine hull p /\
                    a IN affine hull p /\ b IN affine hull p]]) MP_TAC THENL
         [ASM_MESON_TAC [FACE_OF_IMP_SUBSET, HULL_SUBSET, SUBSET], ALL_TAC] THEN
        ASM_REWRITE_TAC [IN_ELIM_THM] THEN
        DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
        REWRITE_TAC [REAL_MUL_RID] THEN DISCH_THEN (ASSUME_TAC o HolLight.SYM) THEN
        DISCH_THEN (MP_TAC o HolLight.AP_TERM ([[(%) (inv cx) :real^N->real^N]])) THEN
        ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_LINV, VECTOR_MUL_LID] THEN
        DISCH_THEN ((fun _ => ALL_TAC)) THEN EXISTS_TAC ([[inv(cx) * u * cb]]) THEN
        REWRITE_TAC [h15] THEN
        ASM_SIMP_TAC [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ, REAL_LT_LE] THEN
        REPEAT CONJ_TAC THENL
         [REWRITE_TAC [REAL_MUL_LZERO] THEN MATCH_MP_TAC REAL_LE_MUL THEN
          ASM_REAL_ARITH_TAC,
          FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h16) THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC,
          REWRITE_TAC [VECTOR_MUL_ASSOC, VECTOR_ADD_LDISTRIB] THEN
          BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          MAP_EVERY UNDISCH_TAC [([[(&1 - u) * ca + u * cb = cx]]), ([[~(cx = &0)]])] THEN
          CONV_TAC REAL_FIELD],
        FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [face_of]) THEN
        REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN (MP_TAC o HolLight.SPECL [([[a:real^N]]), ([[b:real^N]]), ([[x:real^N]])]) THEN
        ASM_REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC []],
      ASM_SIMP_TAC []] THEN
    SUBGOAL_THEN ([[!f:real^N->bool. f face_of p /\ ~(f = {})
                     ==> aff_dim(conic hull f) = aff_dim f + &1]]) (LABEL_TAC "*") THENL
     [ALL_TAC,
      CONJ_TAC THEN X_GEN_TAC ([[f:real^N->bool]]) THEN STRIP_TAC THENL
       [REMOVE_THEN "*" (MP_TAC o HolLight.SPEC ([[f INTER {x:real^N | x$1 = &1}]])) THEN
        ASM_SIMP_TAC [h17, INT_EQ_ADD_RCANCEL] THEN
        ANTS_TAC THENL [ALL_TAC, SIMP_TAC []] THEN
        SUBGOAL_THEN ([[?y:real^N. y IN f /\ ~(y = vec 0)]]) STRIP_ASSUME_TAC THENL
         [MATCH_MP_TAC h18 THEN
          CONJ_TAC THENL
           [MP_TAC (← HolLight.ISPECL [([[s:real^N->bool]]), ([[f:real^N->bool]])] FACE_OF_CONIC) THEN
            ASM_SIMP_TAC [CONIC_CONTAINS_0] THEN REPEAT DISCH_TAC,
            DISCH_TAC] THEN
          UNDISCH_TAC ([[aff_dim(f:real^N->bool) = &d + &1]]) THEN
          ASM_REWRITE_TAC [AFF_DIM_SING, AFF_DIM_EMPTY] THEN INT_ARITH_TAC,
          REWRITE_TAC [(← HolLight.GSYM MEMBER_NOT_EMPTY), IN_INTER, IN_ELIM_THM] THEN
          SUBGOAL_THEN ([[&0 < (y:real^N)$1]]) ASSUME_TAC THENL
           [ASM_MESON_TAC [FACE_OF_IMP_SUBSET, SUBSET], ALL_TAC] THEN
          EXISTS_TAC ([[inv(y$1) % y:real^N]]) THEN
          ASM_SIMP_TAC [VECTOR_MUL_COMPONENT, REAL_MUL_LINV,
                       REAL_LT_IMP_NZ] THEN
          MP_TAC (← HolLight.ISPECL [([[s:real^N->bool]]), ([[f:real^N->bool]])] FACE_OF_CONIC) THEN
          ASM_SIMP_TAC [CONIC_CONTAINS_0] THEN
          REWRITE_TAC [conic] THEN DISCH_THEN MATCH_MP_TAC THEN
          ASM_SIMP_TAC [REAL_LE_INV_EQ, REAL_LT_IMP_LE]],
        REMOVE_THEN "*" (MP_TAC o HolLight.SPEC ([[f:real^N->bool]])) THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
        DISCH_TAC THEN UNDISCH_TAC ([[aff_dim(f:real^N->bool) = &d]]) THEN
        ASM_REWRITE_TAC [AFF_DIM_EMPTY] THEN INT_ARITH_TAC]] THEN
    X_GEN_TAC ([[f:real^N->bool]]) THEN STRIP_TAC THEN
    MATCH_MP_TAC h19 THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC AFF_DIM_PSUBSET THEN
      SIMP_TAC [PSUBSET, HULL_MONO, HULL_SUBSET] THEN
      REWRITE_TAC [EXTENSION, NOT_FORALL_THM] THEN EXISTS_TAC ([[vec 0:real^N]]) THEN
      MATCH_MP_TAC h20 THEN CONJ_TAC THENL
       [MATCH_MP_TAC h21 THEN
        EXISTS_TAC ([[affine hull p:real^N->bool]]) THEN CONJ_TAC THENL
         [ASM_REWRITE_TAC [IN_ELIM_THM, VEC_COMPONENT] THEN REAL_ARITH_TAC2,
          MATCH_MP_TAC HULL_MONO THEN ASM_MESON_TAC [FACE_OF_IMP_SUBSET]],
        MATCH_MP_TAC h22 THEN
        ASM_SIMP_TAC [CONIC_CONTAINS_0, HULL_SUBSET, CONIC_CONIC_HULL] THEN
        ASM_REWRITE_TAC [CONIC_HULL_EQ_EMPTY]],
      MATCH_MP_TAC INT_LE_TRANS THEN
      EXISTS_TAC ([[aff_dim((vec 0:real^N) INSERT (affine hull f))]]) THEN
      CONJ_TAC THENL
       [ALL_TAC,
        REWRITE_TAC [AFF_DIM_INSERT, AFF_DIM_AFFINE_HULL] THEN INT_ARITH_TAC] THEN
      ONCE_REWRITE_TAC [(← HolLight.GSYM AFF_DIM_AFFINE_HULL)] THEN
      MATCH_MP_TAC AFF_DIM_SUBSET THEN MATCH_MP_TAC HULL_MINIMAL THEN
      REWRITE_TAC [AFFINE_AFFINE_HULL, SUBSET, CONIC_HULL_EXPLICIT] THEN
      REWRITE_TAC [FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [([[c:real]]), ([[x:real^N]])] THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC [h23] THEN
      MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN
      ASM_SIMP_TAC [AFFINE_AFFINE_HULL, HULL_INC, IN_INSERT]])
  : ExceptT String IO thm).run
#eval EULER_POINCARE_LEMMA

#eval phrase 61
def EULER_POINCARE_SPECIAL : thm := keep "EULER_POINCARE_SPECIAL" fun _ => (do
  let h4 ← ms [] (← ExceptT.mk [[(!x y. Q x y ==> x = y)
        ==> (!x y. P x /\ P y /\ Q x y ==> x = y)]])
  let h3 ← sr (← ExceptT.mk [[{y | y IN IMAGE f s /\ P y} =
                          {f x |x| x IN s /\ P(f x)}]])
  let h2 ← sr (← ExceptT.mk [[{f | f face_of s /\ P f} =
                          {f | f IN {f | f face_of s} /\ P f}]])
  let h1 ← va (← ExceptT.mk [[a + x:real^N = y <=> x = y - a]])
  prove ([[!p:real^N->bool.
        2 <= dimindex(:N) /\ polytope p /\ affine hull p = {x | x$1 = &0}
        ==> sum (0..dimindex(:N)-1)
               (\d. (-- &1) pow d *
                    &(CARD {f | f face_of p /\ aff_dim f = &d })) = &1]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPEC ([[IMAGE (\x:real^N. basis 1 + x) p]]) EULER_POINCARE_LEMMA) THEN
    ASM_REWRITE_TAC [POLYTOPE_TRANSLATION_EQ, AFFINE_HULL_TRANSLATION] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
      REWRITE_TAC [EXISTS_REFL, h1] THEN
      SIMP_TAC [IN_ELIM_THM, VECTOR_ADD_COMPONENT, BASIS_COMPONENT,
               DIMINDEX_GE_1, LE_REFL] THEN REAL_ARITH_TAC2,
      REWRITE_TAC [h2] THEN
      REWRITE_TAC [FACES_OF_TRANSLATION] THEN
      REWRITE_TAC [h3] THEN
      REWRITE_TAC [AFF_DIM_TRANSLATION_EQ, IN_ELIM_THM] THEN
      DISCH_THEN (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.SYM th)])) THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC ([[d:num]]) THEN STRIP_TAC THEN
      REWRITE_TAC [] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.RAND_CONV) [SIMPLE_IMAGE_GEN] THEN
      CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
       [REWRITE_TAC [] THEN MATCH_MP_TAC h4 THEN
        REWRITE_TAC [INJECTIVE_IMAGE] THEN VECTOR_ARITH_TAC,
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC ([[{f:real^N->bool | f face_of p}]]) THEN
        ASM_SIMP_TAC [FINITE_POLYTOPE_FACES] THEN SET_TAC []]])
  : ExceptT String IO thm).run
#eval EULER_POINCARE_SPECIAL

/- ------------------------------------------------------------------------- -/
/- Now Euler-Poincare for a general full-dimensional polytope.               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 62
def EULER_POINCARE_FULL : thm := keep "EULER_POINCARE_FULL" fun _ => (do
  let h8 ← ms [] (← ExceptT.mk [[(!x y. Q x y ==> x = y)
        ==> (!x y. P x /\ P y /\ Q x y ==> x = y)]])
  let h7 ← sr (← ExceptT.mk [[{y | y IN IMAGE f s /\ P y} =
                              {f x |x| x IN s /\ P(f x)}]])
  let h6 ← sr (← ExceptT.mk [[{f | f face_of s /\ P f} =
                          {f | f IN {f | f face_of s} /\ P f}]])
  let h5 ← ar (← ExceptT.mk [[1 <= n /\ i <= n + 1 ==> i - 1 <= n]])
  let h4 ← ar (← ExceptT.mk [[1 <= i /\ ~(i = 1) ==> 1 <= i - 1]])
  let h3 ← ar (← ExceptT.mk [[1 <= n /\ i <= n + 1 ==> i - 1 <= n]])
  let h2 ← ar (← ExceptT.mk [[1 <= i /\ ~(i = 1) ==> 1 <= i - 1]])
  let h1 ← ar (← ExceptT.mk [[2 <= n + 1 <=> 1 <= n]])
  prove ([[!p:real^N->bool.
        polytope p /\ aff_dim p = &(dimindex(:N))
        ==> sum (0..dimindex(:N))
                (\d. (-- &1) pow d *
                     &(CARD {f | f face_of p /\ aff_dim f = &d })) = &1]])
   (REPEAT STRIP_TAC THEN ABBREV_TAC ([[f:real^N->real^(N,1)finite_sum =
          \x. lambda i. if i = 1 then &0 else x$(i-1)]]) THEN
    ABBREV_TAC ([[s = IMAGE (f:real^N->real^(N,1)finite_sum) p]]) THEN
    MP_TAC (← HolLight.ISPEC ([[s:real^(N,1)finite_sum->bool]]) EULER_POINCARE_SPECIAL) THEN
    REWRITE_TAC [DIMINDEX_FINITE_SUM, DIMINDEX_1, ADD_SUB] THEN
    REWRITE_TAC [DIMINDEX_GE_1, h1] THEN
    SUBGOAL_THEN ([[linear(f:real^N->real^(N,1)finite_sum)]]) ASSUME_TAC THENL
     [EXPAND_TAC "f" THEN REWRITE_TAC [linear] THEN
      SIMP_TAC [CART_EQ, VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT,
               LAMBDA_BETA] THEN
      REAL_ARITH_TAC2,
      ALL_TAC] THEN
    EXPAND_TAC "s" THEN
    ASM_SIMP_TAC [POLYTOPE_LINEAR_IMAGE, AFFINE_HULL_LINEAR_IMAGE] THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [AFF_DIM_EQ_FULL]) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM, IN_UNIV] THEN
      X_GEN_TAC ([[y:real^(N,1)finite_sum]]) THEN EQ_TAC THENL
       [DISCH_THEN (X_CHOOSE_THEN ([[x:real^N]]) SUBST1_TAC) THEN
        EXPAND_TAC "f" THEN SIMP_TAC [LAMBDA_BETA, LE_REFL, DIMINDEX_GE_1],
        DISCH_TAC THEN
        EXISTS_TAC ([[(lambda i. (y:real^(N,1)finite_sum)$(i+1)):real^N]]) THEN
        EXPAND_TAC "f" THEN
        REWRITE_TAC [CART_EQ, DIMINDEX_FINITE_SUM, DIMINDEX_1] THEN
        X_GEN_TAC ([[i:num]]) THEN STRIP_TAC THEN
        ASM_SIMP_TAC [CART_EQ, LAMBDA_BETA, DIMINDEX_FINITE_SUM, DIMINDEX_1,
         DIMINDEX_GE_1, h2,
         h3] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN AP_TERM_TAC THEN
        ASM_ARITH_TAC],
      DISCH_THEN (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.SYM th)])) THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC ([[d:num]]) THEN STRIP_TAC THEN
      REWRITE_TAC [] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN ([[!x y. (f:real^N->real^(N,1)finite_sum) x = f y <=> x = y]]) ASSUME_TAC THENL
       [EXPAND_TAC "f" THEN
        ASM_SIMP_TAC [CART_EQ, LAMBDA_BETA, DIMINDEX_FINITE_SUM, DIMINDEX_1,
          DIMINDEX_GE_1, h4,
          h5] THEN
        REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC ([[i:num]]) THENL
         [REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[i + 1]])) THEN
          ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
          REWRITE_TAC [ADD_SUB] THEN
          COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
          STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC],
        ALL_TAC] THEN
      EXPAND_TAC "s" THEN
      MP_TAC (← HolLight.ISPECL [([[f:real^N->real^(N,1)finite_sum]]), ([[p:real^N->bool]])] FACES_OF_LINEAR_IMAGE) THEN
      ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
      REWRITE_TAC [h6] THEN
      ASM_REWRITE_TAC [h7] THEN
      ASM_SIMP_TAC [AFF_DIM_INJECTIVE_LINEAR_IMAGE] THEN
      REWRITE_TAC [IN_ELIM_THM] THEN
      GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.RAND_CONV) [SIMPLE_IMAGE_GEN] THEN
      CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
       [REWRITE_TAC [] THEN MATCH_MP_TAC h8 THEN
        ASM_REWRITE_TAC [INJECTIVE_IMAGE],
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC ([[{f:real^N->bool | f face_of p}]]) THEN
        ASM_SIMP_TAC [FINITE_POLYTOPE_FACES] THEN SET_TAC []]])
  : ExceptT String IO thm).run
#eval EULER_POINCARE_FULL

/- ------------------------------------------------------------------------- -/
/- In particular the Euler relation in 3D.                                   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 63
def EULER_RELATION : thm := keep "EULER_RELATION" fun _ => (do
  let h2 ← rr (← ExceptT.mk [[((x + --y) + z) + -- &1:real = &1 <=>
                            x + z = y + &2]])
  let h1 ← sr (← ExceptT.mk [[P a /\ (!x. P x ==> x = a) ==> {x | P x} = {a}]])
  prove ([[!p:real^3->bool.
        polytope p /\ aff_dim p = &3
        ==> (CARD {v | v face_of p /\ aff_dim(v) = &0} +
             CARD {f | f face_of p /\ aff_dim(f) = &2}) -
            CARD {e | e face_of p /\ aff_dim(e) = &1} = 2]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPEC ([[p:real^3->bool]]) EULER_POINCARE_FULL) THEN
    ASM_REWRITE_TAC [DIMINDEX_3] THEN
    REWRITE_TAC [HolLight.TOP_DEPTH_CONV num_CONV ([[3]]), SUM_CLAUSES_NUMSEG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC [REAL_MUL_LID, REAL_MUL_LNEG] THEN
    SUBGOAL_THEN ([[{f:real^3->bool | f face_of p /\ aff_dim f = &3} = {p}]]) (fun th => SIMP_TAC [th, NOT_IN_EMPTY, FINITE_EMPTY, CARD_CLAUSES]) THENL
     [MATCH_MP_TAC h1 THEN
      ASM_SIMP_TAC [FACE_OF_REFL, POLYTOPE_IMP_CONVEX] THEN
      X_GEN_TAC ([[f:real^3->bool]]) THEN STRIP_TAC THEN
      MP_TAC (← HolLight.ISPECL [([[f:real^3->bool]]), ([[p:real^3->bool]])] FACE_OF_AFF_DIM_LT) THEN
      ASM_SIMP_TAC [POLYTOPE_IMP_CONVEX, INT_LT_REFL],
      REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_SUC), REAL_ADD_LID] THEN
      REWRITE_TAC [h2] THEN
      REWRITE_TAC [REAL_OF_NUM_ADD, REAL_OF_NUM_EQ] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [ADD_SUB2]])
  : ExceptT String IO thm).run
#eval EULER_RELATION

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py; keep it in step with the `#eval`s above. -/
def ensure : IO Unit := once "Hol100.Polyhedron" do
  replay (
          SessionMultiLib.Polytope.ensurePolytope)
  replay (
          SessionLibrary.Binomial.ensureBinomial)
  replay (
          Hol100.InclusionExclusion.ensure)
  replay (
          Hol100.Combinations.ensure)
  replay (
          Session.prioritize_real)
  replay (
          hyperplane_side)
  replay (
          hyperplane_equiv)
  replay (
          HYPERPLANE_EQUIV_REFL)
  replay (
          HYPERPLANE_EQUIV_SYM)
  replay (
          HYPERPLANE_EQUIV_TRANS)
  replay (
          HYPERPLANE_EQUIV_UNION)
  replay (
          hyperplane_cell)
  replay (
          HYPERPLANE_CELL)
  replay (
          NOT_HYPERPLANE_CELL_EMPTY)
  replay (
          NONEMPTY_HYPERPLANE_CELL)
  replay (
          UNIONS_HYPERPLANE_CELLS)
  replay (
          DISJOINT_HYPERPLANE_CELLS)
  replay (
          DISJOINT_HYPERPLANE_CELLS_EQ)
  replay (
          HYPERPLANE_CELL_EMPTY)
  replay (
          HYPERPLANE_CELL_SING_CASES)
  replay (
          HYPERPLANE_CELL_SING)
  replay (
          HYPERPLANE_CELL_UNION)
  replay (
          FINITE_HYPERPLANE_CELLS)
  replay (
          FINITE_RESTRICT_HYPERPLANE_CELLS)
  replay (
          FINITE_SET_OF_HYPERPLANE_CELLS)
  replay (
          PAIRWISE_DISJOINT_HYPERPLANE_CELLS)
  replay (
          HYPERPLANE_CELL_INTER_OPEN_AFFINE)
  replay (
          HYPERPLANE_CELL_RELATIVELY_OPEN)
  replay (
          HYPERPLANE_CELL_RELATIVE_INTERIOR)
  replay (
          HYPERPLANE_CELL_CONVEX)
  replay (
          HYPERPLANE_CELL_INTERS)
  replay (
          HYPERPLANE_CELL_INTER)
  replay (
          hyperplane_cellcomplex)
  replay (
          HYPERPLANE_CELLCOMPLEX_EMPTY)
  replay (
          HYPERPLANE_CELL_CELLCOMPLEX)
  replay (
          HYPERPLANE_CELLCOMPLEX_UNIONS)
  replay (
          HYPERPLANE_CELLCOMPLEX_UNION)
  replay (
          HYPERPLANE_CELLCOMPLEX_UNIV)
  replay (
          HYPERPLANE_CELLCOMPLEX_INTERS)
  replay (
          HYPERPLANE_CELLCOMPLEX_INTER)
  replay (
          HYPERPLANE_CELLCOMPLEX_COMPL)
  replay (
          HYPERPLANE_CELLCOMPLEX_DIFF)
  replay (
          HYPERPLANE_CELLCOMPLEX_MONO)
  replay (
          FINITE_HYPERPLANE_CELLCOMPLEXES)
  replay (
          FINITE_RESTRICT_HYPERPLANE_CELLCOMPLEXES)
  replay (
          FINITE_SET_OF_HYPERPLANE_CELLS_2)
  replay (
          CELL_SUBSET_CELLCOMPLEX)
  replay (
          euler_characteristic)
  replay (
          EULER_CHARACTERISTIC_EMPTY)
  replay (
          EULER_CHARACTERISTIC_CELL_UNIONS)
  replay (
          EULER_CHARACTERISTIC_CELL)
  replay (
          EULER_CHARACTERISTIC_CELLCOMPLEX_UNION)
  replay (
          EULER_CHARACTERISTIC_CELLCOMPLEX_UNIONS)
  replay (
          EULER_CHARACTERISTIC)
  replay (
          HYPERPLANE_CELLS_DISTINCT_LEMMA)
  replay (
          EULER_CHARACTERSTIC_LEMMA)
  replay (
          EULER_CHARACTERSTIC_INVARIANT)
  replay (
          EULER_CHARACTERISTIC_INCLUSION_EXCLUSION)
  replay (
          EULER_POLYHEDRAL_CONE)
  replay (
          EULER_POINCARE_LEMMA)
  replay (
          EULER_POINCARE_SPECIAL)
  replay (
          EULER_POINCARE_FULL)
  replay (
          EULER_RELATION)
-- @@ENSURE END

end Hol100.Polyhedron
