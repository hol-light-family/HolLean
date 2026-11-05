/- File: HolExamples/ComplexPolygon.lean
Translation of HOL Light's Examples/complexpolygon.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolExamples.Common
import SessionMultiLib.Transcendentals
open HolCore.Kernel Session HolLight.Syntax HolExamples
open SessionLibrary.Card SessionLibrary.Prime SessionLibrary.GroupTheory
open SessionMultiLib.Misc SessionMultiLib.Vectors SessionMultiLib.Determinants
open SessionMultiLib.Metric SessionMultiLib.Topology SessionMultiLib.Convex
open SessionMultiLib.Complexes SessionMultiLib.Transcendentals
namespace HolExamples.ComplexPolygon

/- Helpers: the session's `prove` lifted into `ExceptT String IO`, so tactic
   scripts read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)
private def nd (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.new_definition tm)

-- ========================================================================= --
-- Some formalization around a cute puzzle on stackexchange.                 --
--                                                                           --
-- See https://math.stackexchange.com/questions/4892153, in particular the   --
-- observation from Dario extending Carl Schildkraut's proof to equivalence. --
--                                                                           --
-- A polygon with its vertices on the unit circle is closed under complex    --
-- multiplication iff the vertices are n'th roots of unity for some n.       --
-- ========================================================================= --

#eval phrase 1
-- needs "Multivariate/transcendentals.ml";;
#eval SessionMultiLib.Transcendentals.ensureTranscendentals

-- ------------------------------------------------------------------------- --
-- Actually set up the circle group of unimodular complex numbers.           --
-- ------------------------------------------------------------------------- --

#eval phrase 2
def circle_group : thm := keep "circle_group" fun _ => (do
  nd ([[circle_group = group({z| norm z = &1},Cx(&1),complex_inv,complex_mul)]])
  : ExceptT String IO thm).run
#eval circle_group

#eval phrase 3
def CIRCLE_GROUP : thm := keep "CIRCLE_GROUP" fun _ => (do
  prove ([[group_carrier circle_group = {z | norm z = &1} /\
   group_id circle_group = Cx(&1) /\
   group_inv circle_group = complex_inv /\
   group_mul circle_group = complex_mul]])
   (REWRITE_TAC [group_carrier, group_id, group_inv, group_mul, (← HolLight.GSYM PAIR_EQ)] THEN
    REWRITE_TAC [circle_group, (← HolLight.GSYM (← HolLight.CONJUNCT2 group_tybij))] THEN
    REWRITE_TAC [IN_ELIM_THM, COMPLEX_MUL_LID, COMPLEX_MUL_RID] THEN
    SIMP_TAC [COMPLEX_NORM_INV, COMPLEX_NORM_MUL, COMPLEX_NORM_CX] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [COMPLEX_MUL_ASSOC] THEN
    X_GEN_TAC ([[z:complex]]) THEN ASM_CASES_TAC ([[z = Cx(&0)]]) THEN
    ASM_REWRITE_TAC [COMPLEX_NORM_0, REAL_OF_NUM_EQ, ARITH_EQ] THEN
    DISCH_THEN (fun _ => ALL_TAC) THEN POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_FIELD)
  : ExceptT String IO thm).run
#eval CIRCLE_GROUP

#eval phrase 4
def ABELIAN_CIRCLE_GROUP : thm := keep "ABELIAN_CIRCLE_GROUP" fun _ => (do
  prove ([[abelian_group circle_group]])
   (REWRITE_TAC [abelian_group, CIRCLE_GROUP, COMPLEX_MUL_SYM])
  : ExceptT String IO thm).run
#eval ABELIAN_CIRCLE_GROUP

#eval phrase 5
def GROUP_POW_CIRCLE_GROUP : thm := keep "GROUP_POW_CIRCLE_GROUP" fun _ => (do
  prove ([[!z n. group_pow circle_group z n = z pow n]])
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [group_pow, CIRCLE_GROUP, complex_pow])
  : ExceptT String IO thm).run
#eval GROUP_POW_CIRCLE_GROUP

#eval phrase 6
def FINITE_SUBGROUP_OF_CIRCLE_GROUP : thm := keep "FINITE_SUBGROUP_OF_CIRCLE_GROUP" fun _ => (do
  -- OCaml builds the tactic right to left: the build-time rules run
  -- bottom-first.
  let b5 ← HolLight.ISPECL [([[subgroup_generated circle_group s]]), ([[z:complex]])]
                  GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER
  let b4c ← HolLight.CONJUNCT2 SUBGROUP_GENERATED
  let b4 ← HolLight.ISPECL [([[subgroup_generated circle_group s]]), ([[w:complex]]),
                            ([[n:num]])] GROUP_POW_EQ_ID
  let b3 ← HolLight.SPEC ([[n:num]]) FINITE_CARD_COMPLEX_ROOTS_UNITY
  let b2 ← HolLight.ISPECL [([[subgroup_generated circle_group s]]), ([[z:complex]])]
        FINITE_GROUP_ELEMENT_ORDER_NONZERO
  let b1 ← HolLight.ISPEC ([[subgroup_generated circle_group s]])
        ABELIAN_GROUP_ORDER_DIVIDES_MAXIMAL
  prove ([[!s:complex->bool.
        FINITE s /\ s subgroup_of circle_group
        ==> ?n. 1 <= n /\ s = {z | z pow n = Cx(&1)}]])
   (REPEAT STRIP_TAC THEN
    MP_TAC b1 THEN
    ASM_SIMP_TAC [CYCLIC_GROUP_ELEMENT_ORDER, CARRIER_SUBGROUP_GENERATED_SUBGROUP,
                 ABELIAN_SUBGROUP_GENERATED, ABELIAN_CIRCLE_GROUP] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[z:complex]]) STRIP_ASSUME_TAC) THEN
    ABBREV_TAC
     ([[n = group_element_order (subgroup_generated circle_group s) z]]) THEN
    EXISTS_TAC ([[n:num]]) THEN
    MP_TAC b2 THEN
    ASM_SIMP_TAC [CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
    DISCH_TAC THEN ASM_SIMP_TAC [LE_1] THEN MATCH_MP_TAC CARD_SUBSET_LE THEN
    MP_TAC b3 THEN
    ASM_SIMP_TAC [LE_1] THEN STRIP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN
      X_GEN_TAC ([[w:complex]]) THEN DISCH_TAC THEN
      MP_TAC b4 THEN
      ASM_SIMP_TAC [CARRIER_SUBGROUP_GENERATED_SUBGROUP, CIRCLE_GROUP,
                   b4c, GROUP_POW_SUBGROUP_GENERATED,
                   GROUP_POW_CIRCLE_GROUP],
      TRANS_TAC LE_TRANS ([[n:num]]) THEN ASM_REWRITE_TAC [] THEN
      MP_TAC b5 THEN
      ASM_SIMP_TAC [CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
      ASM_MESON_TAC [CARD_EQ_0, NOT_IN_EMPTY, DIVIDES_LE_IMP]])
  : ExceptT String IO thm).run
#eval FINITE_SUBGROUP_OF_CIRCLE_GROUP

-- ------------------------------------------------------------------------- --
-- The nice observation from Dario combined with Carl Schildkraut's          --
-- ------------------------------------------------------------------------- --

#eval phrase 7
def DARIO_LEMMA1 : thm := keep "DARIO_LEMMA1" fun _ => (do
  -- Build-time rules, bottom-first.
  let b4 ← HolLight.REWRITE_RULE [SUBSET, RIGHT_IMP_FORALL_THM] HULL_MONO
  let b3 ← HolLight.ISPECL [([[complex_mul]]), ([[s:complex->bool]]), ([[s:complex->bool]]),
                   ([[w:complex]]), ([[z:complex]])] BILINEAR_IN_CONVEX_HULL
  let b2 ← tt ([[~q ==> (~p ==> q) ==> p]])
  let b1 ← HolLight.ISPECL [([[Cx(&0)]]), ([[s:complex->bool]]), ([[w * z:complex]])]
        SIMPLEX_FURTHEST_LT_EXISTS
  prove ([[!s:complex->bool.
      (!z. z IN s ==> norm z = &1)
      ==> ((!w z. w IN convex hull s /\ z IN convex hull s
                  ==> w * z IN convex hull s) <=>
           (!w z. w IN s /\ z IN s ==> w * z IN s))]])
   (REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
     [MP_TAC b1 THEN
      ASM_SIMP_TAC [HULL_INC, COMPLEX_SUB_RZERO] THEN
      MATCH_MP_TAC b2 THEN
      ASM_SIMP_TAC [COMPLEX_NORM_MUL, REAL_MUL_LID] THEN
      ASM_MESON_TAC [REAL_LT_REFL],
      MP_TAC b3 THEN
      ASM_REWRITE_TAC [BILINEAR_COMPLEX_MUL] THEN
      MATCH_MP_TAC b4 THEN
      HolLight.ASM SET_TAC []])
  : ExceptT String IO thm).run
#eval DARIO_LEMMA1

-- ------------------------------------------------------------------------- --
-- The other lemma                                                           --
-- ------------------------------------------------------------------------- --

#eval phrase 8
def DARIO_LEMMA2 : thm := keep "DARIO_LEMMA2" fun _ => (do
  let b1 ← HolLight.ISPECL [([[circle_group]]), ([[s:complex->bool]])]
     FINITE_SUBGROUP_OF_SETWISE
  prove ([[!s:complex->bool.
        FINITE s /\ ~(s = {}) /\ (!z. z IN s ==> norm z = &1)
        ==> ((!w z. w IN s /\ z IN s ==> w * z IN s) <=>
             s subgroup_of circle_group)]])
   (REPEAT STRIP_TAC THEN
    MP_TAC b1 THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [group_setmul, SUBSET, FORALL_IN_GSPEC, CIRCLE_GROUP] THEN
    ASM_REWRITE_TAC [IN_ELIM_THM])
  : ExceptT String IO thm).run
#eval DARIO_LEMMA2

-- ------------------------------------------------------------------------- --
-- And so the finale.                                                        --
-- ------------------------------------------------------------------------- --

#eval phrase 9
def DARIO : thm := keep "DARIO" fun _ => (do
  prove ([[!s:complex->bool.
      FINITE s /\ ~(s = {}) /\ (!z. z IN s ==> norm z = &1)
      ==> ((!w z. w IN convex hull s /\ z IN convex hull s
                  ==> w * z IN convex hull s) <=>
           ?n. 1 <= n /\ s = {z | z pow n = Cx(&1)})]])
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [DARIO_LEMMA1] THEN EQ_TAC THENL
     [ASM_SIMP_TAC [DARIO_LEMMA2, FINITE_SUBGROUP_OF_CIRCLE_GROUP],
      STRIP_TAC THEN
      ASM_SIMP_TAC [IN_ELIM_THM, COMPLEX_POW_MUL, COMPLEX_MUL_LID]])
  : ExceptT String IO thm).run
#eval DARIO

end HolExamples.ComplexPolygon
