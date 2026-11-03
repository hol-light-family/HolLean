/- ========================================================================= -/
/- L_p spaces for functions R^n -> R^m (lpspaces.ml).                        -/
/- ========================================================================= -/
/- File: HolMultiLib/LpSpaces.lean

  Original (c) Copyright, John Harrison 1998-2008 (see lpspaces.ml).
  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Multivariate/lpspaces.ml`, in the style of
  HolMultiLib/Measure.lean: pure, the proofs translated by hand, one `let`
  per OCaml `let`, in file order.  The load-time effects are at their file
  positions.  What lpspaces.ml uses from earlier files is passed in `LpSpacesDeps`.
  SessionMultiLib/LpSpaces.lean supplies it.
-/

import HolMultiLib.RealAnalysis

open HolCore HolCore.Lib
open HolCore.Kernel hiding ASSUME INST
open HolCore.Equal (ioconv lhs rhs lhand)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolLight HolLight.Syntax

namespace HolMultiLib.LpSpaces

/- The theorems lpspaces.ml uses that the deps chain does not carry, grouped by the
   file that proves them. -/

structure QMeasureThms where
  (ABSOLUTELY_INTEGRABLE_MEASURABLE
   ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET INTEGRABLE_ON_CONST
   INTEGRAL_CONST_GEN INTEGRAL_DROP_LE_MEASURABLE MEASURABLE_ON_LIFT_MUL
   MEASURABLE_ON_VSUM : thm)
  deriving Inhabited

structure QTopologyThms where
  (SERIES_LIFT_ABSCONV_IMP_CONV : thm)
  deriving Inhabited

structure LpSpacesDeps where
  ra : HolMultiLib.RealAnalysis.RealAnalysisDeps
  rza : HolMultiLib.RealAnalysis.RZA
  rzb : HolMultiLib.RealAnalysis.RZB
  rzc : HolMultiLib.RealAnalysis.RZC
  rzd : HolMultiLib.RealAnalysis.RZD
  rze : HolMultiLib.RealAnalysis.RZE
  rzf : HolMultiLib.RealAnalysis.RZF
  rzg : HolMultiLib.RealAnalysis.RZG
  rzh : HolMultiLib.RealAnalysis.RZH
  rzi : HolMultiLib.RealAnalysis.RZI
  rzj : HolMultiLib.RealAnalysis.RZJ
  rzk : HolMultiLib.RealAnalysis.RZK
  rzl : HolMultiLib.RealAnalysis.RZL
  rzm : HolMultiLib.RealAnalysis.RZM
  rzn : HolMultiLib.RealAnalysis.RZN
  rzo : HolMultiLib.RealAnalysis.RZO
  rzp : HolMultiLib.RealAnalysis.RZP
  rzq : HolMultiLib.RealAnalysis.RZQ
  rzr : HolMultiLib.RealAnalysis.RZR
  rzs : HolMultiLib.RealAnalysis.RZS
  rzt : HolMultiLib.RealAnalysis.RZT
  rzu : HolMultiLib.RealAnalysis.RZU
  rzv : HolMultiLib.RealAnalysis.RZV
  rzw : HolMultiLib.RealAnalysis.RZW
  rzx : HolMultiLib.RealAnalysis.RZX
  rzy : HolMultiLib.RealAnalysis.RZY
  rzz : HolMultiLib.RealAnalysis.RZZ
  rzaa : HolMultiLib.RealAnalysis.RZAA
  rzab : HolMultiLib.RealAnalysis.RZAB
  rzac : HolMultiLib.RealAnalysis.RZAC
  rzad : HolMultiLib.RealAnalysis.RZAD
  rzae : HolMultiLib.RealAnalysis.RZAE
  rzaf : HolMultiLib.RealAnalysis.RZAF
  rzag : HolMultiLib.RealAnalysis.RZAG
  rzah : HolMultiLib.RealAnalysis.RZAH
  rzai : HolMultiLib.RealAnalysis.RZAI
  rzaj : HolMultiLib.RealAnalysis.RZAJ
  rzak : HolMultiLib.RealAnalysis.RZAK
  rzal : HolMultiLib.RealAnalysis.RZAL
  rzam : HolMultiLib.RealAnalysis.RZAM
  rzan : HolMultiLib.RealAnalysis.RZAN
  rzao : HolMultiLib.RealAnalysis.RZAO
  rzap : HolMultiLib.RealAnalysis.RZAP
  rzaq : HolMultiLib.RealAnalysis.RZAQ
  rzar : HolMultiLib.RealAnalysis.RZAR
  rzas : HolMultiLib.RealAnalysis.RZAS
  rzat : HolMultiLib.RealAnalysis.RZAT
  rzau : HolMultiLib.RealAnalysis.RZAU
  rzav : HolMultiLib.RealAnalysis.RZAV
  rzaw : HolMultiLib.RealAnalysis.RZAW
  rzax : HolMultiLib.RealAnalysis.RZAX
  rzay : HolMultiLib.RealAnalysis.RZAY
  rzaz : HolMultiLib.RealAnalysis.RZAZ
  rzba : HolMultiLib.RealAnalysis.RZBA
  rzbb : HolMultiLib.RealAnalysis.RZBB
  rzbc : HolMultiLib.RealAnalysis.RZBC
  rzbd : HolMultiLib.RealAnalysis.RZBD
  rzbe : HolMultiLib.RealAnalysis.RZBE
  rzbf : HolMultiLib.RealAnalysis.RZBF
  rzbg : HolMultiLib.RealAnalysis.RZBG
  rzbh : HolMultiLib.RealAnalysis.RZBH
  rzbi : HolMultiLib.RealAnalysis.RZBI
  rzbj : HolMultiLib.RealAnalysis.RZBJ
  rzbk : HolMultiLib.RealAnalysis.RZBK
  rzbl : HolMultiLib.RealAnalysis.RZBL
  rzbm : HolMultiLib.RealAnalysis.RZBM
  rzbn : HolMultiLib.RealAnalysis.RZBN
  rzbo : HolMultiLib.RealAnalysis.RZBO
  rzbp : HolMultiLib.RealAnalysis.RZBP
  rzbq : HolMultiLib.RealAnalysis.RZBQ
  rzbr : HolMultiLib.RealAnalysis.RZBR
  rzbs : HolMultiLib.RealAnalysis.RZBS
  rzbt : HolMultiLib.RealAnalysis.RZBT
  rzbu : HolMultiLib.RealAnalysis.RZBU
  rzbv : HolMultiLib.RealAnalysis.RZBV
  rzbw : HolMultiLib.RealAnalysis.RZBW
  rzbx : HolMultiLib.RealAnalysis.RZBX
  rzby : HolMultiLib.RealAnalysis.RZBY
  rzbz : HolMultiLib.RealAnalysis.RZBZ
  rzca : HolMultiLib.RealAnalysis.RZCA
  rzcb : HolMultiLib.RealAnalysis.RZCB
  rzcc : HolMultiLib.RealAnalysis.RZCC
  rzcd : HolMultiLib.RealAnalysis.RZCD
  -- theorems
  qmeasure : QMeasureThms
  qtopology : QTopologyThms

/- ------------------------------------------------------------------------- -/
/- prioritize_complex(); the space L_p of measurable functions f with |f|^p  -/
/- integrable (on s).                                                        -/
/- (lpspaces.ml 1-297)                                                      -/
/- ------------------------------------------------------------------------- -/

structure LSA where
  lspace : thm
  LSPACE_ALT : thm
  LSPACE_ZERO : thm
  LSPACE_CONST : thm
  LSPACE_0 : thm
  LSPACE_CMUL : thm
  LSPACE_NEG : thm
  LSPACE_ADD : thm
  LSPACE_SUB : thm
  LSPACE_IMP_INTEGRABLE : thm
  LSPACE_NORM : thm
  LSPACE_VSUM : thm
  LSPACE_MAX : thm
  LSPACE_MIN : thm
  LSPACE_BOUNDED_MEASURABLE : thm
  LSPACE_BOUNDED_MEASURABLE_SIMPLE : thm
  LSPACE_INTEGRABLE_PRODUCT : thm
  LSPACE_1 : thm
  LSPACE_MONO : thm
  LSPACE_INCLUSION : thm
  LSPACE_SUBSET : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupLSA [HolBase] (D : LpSpacesDeps) : ExceptT String IO LSA := do
  -- @@SCOPE BEGIN
  let { REAL_CONTINUOUS_ON, .. } := D.rzj
  let { REAL_CONTINUOUS_ON_RPOW, .. } := D.rzs
  let { YOUNG_INEQUALITY, .. } := D.rzag
  let { MEASURABLE_ON_LIFT_RPOW, .. } := D.rzbu
  let { ABSOLUTELY_INTEGRABLE_MEASURABLE,
        ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET, INTEGRABLE_ON_CONST,
        .. } := D.qmeasure
  let { REAL_ABS_RPOW, REAL_MAX_RPOW, RPOW_1_LE, RPOW_LE2, RPOW_MONO_LE, RPOW_MUL,
        RPOW_POS_LE, RPOW_POW, RPOW_ZERO, .. } := D.ra.tsab
  let { INTEGRABLE_IMP_MEASURABLE, MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE,
        MEASURABLE_ON_ADD, MEASURABLE_ON_CMUL, MEASURABLE_ON_COMPOSE_CONTINUOUS_0,
        MEASURABLE_ON_DROP_MUL, MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET,
        MEASURABLE_ON_MAX, MEASURABLE_ON_MIN, MEASURABLE_ON_NORM, .. } := D.ra.qmeasure
  let { prioritize_complex, .. } := D.ra.ts.cn.cxa
  let { ABSOLUTELY_INTEGRABLE_EQ_INTEGRABLE_POS, ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE,
        ABSOLUTELY_INTEGRABLE_MAX_1, .. } := D.ra.ts.cn.ms.qintegration1
  let { INTEGRABLE_0, INTEGRABLE_ADD, INTEGRABLE_CMUL, .. } := D.ra.ts.cn.ms.qintegration2
  let { NONNEGATIVE_ABSOLUTELY_INTEGRABLE, .. } := D.ra.ts.cn.ms.qintegration3
  let { IMAGE_LIFT_UNIV, .. } := D.ra.ts.cn.ms.qvec
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON, MESON_TAC, new_definition, REAL_ARITH,
        SET_TAC, VECTOR_ARITH, .. } := D.ra.ts.cn.cx.cvx
  let { REAL_POW_1, .. } := D.ra.ts.cn.cx.cpx
  let { ARITH_EQ, CARD_NUMSEG_1, DIMINDEX_1, ETA_AX, FINITE_INDUCT_STRONG, FINITE_NUMSEG,
        .. } := D.ra.ts.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, FUN_EQ_THM, IMP_CONJ, IMP_CONJ_ALT, IMP_IMP,
        .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_INSERT, IN_NUMSEG, LAMBDA_BETA, MONO_EXISTS, NOT_IN_EMPTY,
        REAL_ABS_MUL, REAL_ADD_SYM, .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_LE_ADDL, REAL_LE_LMUL, REAL_LE_LT, REAL_LE_TOTAL, REAL_LE_TRANS,
        REAL_LT_IMP_LE, REAL_LT_IMP_NZ, .. } := D.ra.ts.cn.cx.cvx.core4
  let { REAL_MUL_SYM, REAL_POS, REAL_WLOG_LE, RIGHT_FORALL_IMP_THM, SUBSET,
        .. } := D.ra.ts.cn.cx.cvx.core5
  let { o_THM, real_abs, real_div, real_pow, SUM_BOUND, SUM_CLAUSES,
        .. } := D.ra.ts.cn.cx.cvx.core6
  let { COMPONENT_LE_NORM, .. } := D.ra.ts.cn.cx.cvx.vec1
  let { DROP_ADD, DROP_VEC, FORALL_1, LIFT_ADD, LIFT_CMUL, LIFT_DROP, LIFT_NUM, NORM_0,
        .. } := D.ra.ts.cn.cx.cvx.vec2
  let { NORM_LE_L1, NORM_LIFT, NORM_MUL, NORM_POS_LE, NORM_TRIANGLE, REAL_ABS_NORM,
        .. } := D.ra.ts.cn.cx.cvx.vec3
  let { drop, VECTOR_SUB, VSUM_CLAUSES, .. } := D.ra.ts.cn.cx.cvx.vec4
  let { BOUNDED_POS, .. } := D.ra.ts.cn.cx.cvx.top1
  let { VEC_EQ, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qvec
  -- @@SCOPE END

  prioritize_complex

  let lspace ← new_definition
   r"lspace s p =
   {f:real^M->real^N | f measurable_on s /\
                       (\x. lift(norm(f x) rpow p)) integrable_on s}"

  let LSPACE_ALT ← prove
   r"lspace s p =
   {f | (f:real^M->real^N) measurable_on s /\
        (\x. lift(norm(f x) rpow p)) absolutely_integrable_on s}"
   (REWRITE_TAC [lspace] THEN
    SIMP_TAC [ABSOLUTELY_INTEGRABLE_EQ_INTEGRABLE_POS,
              LIFT_DROP, RPOW_POS_LE, NORM_POS_LE])

  let LSPACE_ZERO ← prove
   r"!s. lspace s (&0) =
          if measurable s then {f:real^M->real^N | f measurable_on s} else {}"
   (REWRITE_TAC [lspace, RPOW_POW, real_pow, NORM_0, LIFT_NUM] THEN
    GEN_TAC THEN REWRITE_TAC [INTEGRABLE_ON_CONST, VEC_EQ, ARITH_EQ] THEN
    ASM_CASES_TAC (← q r"measurable(s:real^M->bool)") THEN
    ASM_REWRITE_TAC [] THEN SET_TAC [])

  let LSPACE_CONST ← prove
   r"!s p c. measurable s ==> (\x. c) IN lspace s p"
   (SIMP_TAC [lspace, IN_ELIM_THM, INTEGRABLE_ON_CONST,
              INTEGRABLE_IMP_MEASURABLE])

  let LSPACE_0 ← prove
   r"!s p. ~(p = &0) ==> (\x. vec 0) IN lspace s p"
   (SIMP_TAC [lspace, IN_ELIM_THM, NORM_0, RPOW_ZERO, LIFT_NUM] THEN
    SIMP_TAC [INTEGRABLE_IMP_MEASURABLE, INTEGRABLE_0])

  let LSPACE_CMUL ← prove
   r"!s p c f:real^M->real^N.
        f IN lspace s p ==> (\x. c % f x) IN lspace s p"
   (REPEAT GEN_TAC THEN REWRITE_TAC [lspace, IN_ELIM_THM] THEN
    SIMP_TAC [NORM_MUL, RPOW_MUL, NORM_POS_LE, LIFT_CMUL] THEN
    SIMP_TAC [MEASURABLE_ON_CMUL, INTEGRABLE_CMUL])

  let LSPACE_NEG ← prove
   r"!s p f:real^M->real^N. f IN lspace s p ==> (\x. --(f x)) IN lspace s p"
   (REWRITE_TAC [← VECTOR_ARITH (← q r"--x:real^N = --(&1) % x"), LSPACE_CMUL])

  let LSPACE_ADD ← prove
   r"!s p f g:real^M->real^N.
      &0 <= p /\ f IN lspace s p /\ g IN lspace s p
      ==> (\x. f(x) + g(x)) IN lspace s p"
   (REPEAT GEN_TAC THEN REWRITE_TAC [REAL_LE_LT] THEN ASM_CASES_TAC (← q r"p = &0") THEN
    ASM_REWRITE_TAC [] THENL
     [REWRITE_TAC [LSPACE_ZERO] THEN
      ASM_CASES_TAC (← q r"measurable(s:real^M->bool)") THEN
      ASM_REWRITE_TAC [NOT_IN_EMPTY, IN_ELIM_THM, MEASURABLE_ON_ADD],
      ALL_TAC] THEN
    REWRITE_TAC [lspace, IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC [MEASURABLE_ON_ADD] THEN
    MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC (← q r"\x. lift(&2 rpow p * (norm((f:real^M->real^N) x) rpow p +
                                      norm((g:real^M->real^N) x) rpow p))") THEN
    REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN
       (← q r"(\x:real^M. lift(norm(f x + g x:real^N) rpow p)) =
        (lift o (\y. y rpow p) o drop) o (\x. lift(norm(f x + g x)))")
      SUBST1_TAC THENL [REWRITE_TAC [FUN_EQ_THM, o_THM, LIFT_DROP], ALL_TAC] THEN
      MATCH_MP_TAC MEASURABLE_ON_COMPOSE_CONTINUOUS_0 THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MEASURABLE_ON_NORM THEN
        MATCH_MP_TAC MEASURABLE_ON_ADD THEN ASM_REWRITE_TAC [],
        ONCE_REWRITE_TAC [← GSYM IMAGE_LIFT_UNIV] THEN
        REWRITE_TAC [← GSYM REAL_CONTINUOUS_ON] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_RPOW THEN ASM_REAL_ARITH_TAC,
        ASM_SIMP_TAC [o_THM, DROP_VEC, RPOW_ZERO, REAL_LT_IMP_NZ] THEN
        REWRITE_TAC [LIFT_NUM]],
      REWRITE_TAC [LIFT_CMUL, LIFT_ADD] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
      MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC [],
      X_GEN_TAC (← q r"x:real^M") THEN DISCH_TAC THEN
      REWRITE_TAC [NORM_LIFT, REAL_ABS_NORM, LIFT_DROP] THEN
      MATCH_MP_TAC (← REAL_ARITH
       (← q r"(&0 <= norm(f + g:real^N) rpow p /\ &0 <= norm f /\ &0 <= norm g /\
         norm(f + g) rpow p <= (norm f + norm g) rpow p) /\
        (&0 <= norm f /\ &0 <= norm g ==> (norm f + norm g) rpow p <= e)
        ==> abs(norm(f + g) rpow p) <= e")) THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC [NORM_POS_LE, RPOW_POS_LE, RPOW_LE2, NORM_TRIANGLE, RPOW_LE2,
                      REAL_LT_IMP_LE],
        SPEC_TAC (← q r"norm((g:real^M->real^N) x)", ← q r"z:real") THEN
        SPEC_TAC (← q r"norm((f:real^M->real^N) x)", ← q r"w:real") THEN
        MATCH_MP_TAC REAL_WLOG_LE THEN
        CONJ_TAC THENL [MESON_TAC [REAL_ADD_SYM], ALL_TAC] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC (← q r"(&2 * z) rpow p") THEN CONJ_TAC THENL
         [MATCH_MP_TAC RPOW_LE2 THEN ASM_REAL_ARITH_TAC,
          ASM_SIMP_TAC [RPOW_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
          ASM_SIMP_TAC [REAL_LE_ADDL, RPOW_POS_LE, REAL_POS]]]])

  let LSPACE_SUB ← prove
   r"!s p f g:real^M->real^N.
      &0 <= p /\ f IN lspace s p /\ g IN lspace s p
      ==> (\x. f(x) - g(x)) IN lspace s p"
   (SIMP_TAC [VECTOR_SUB, LSPACE_ADD, LSPACE_NEG])

  let LSPACE_IMP_INTEGRABLE ← prove
   r"!s p f. f IN lspace s p ==> (\x. lift(norm(f x) rpow p)) integrable_on s"
   (SIMP_TAC [lspace, IN_ELIM_THM])

  let LSPACE_NORM ← prove
   r"!s p f. f IN lspace s p ==> (\x. lift(norm(f x))) IN lspace s p"
   (REWRITE_TAC [lspace, IN_ELIM_THM] THEN
    SIMP_TAC [NORM_LIFT, REAL_ABS_NORM, MEASURABLE_ON_NORM])

  let LSPACE_VSUM ← prove
   r"!s p f:A->real^M->real^N t.
        &0 < p /\ FINITE t /\ (!i. i IN t ==> (f i) IN lspace s p)
        ==> (\x. vsum t (\i. f i x)) IN lspace s p"
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC [SUM_CLAUSES, VSUM_CLAUSES, LSPACE_0, REAL_LT_IMP_NZ] THEN
    ASM_SIMP_TAC [LSPACE_ADD, REAL_LT_IMP_LE, ETA_AX, IN_INSERT])

  let LSPACE_MAX ← prove
   r"!s p k f:real^M->real^N g:real^M->real^N.
      f IN lspace s p /\ g IN lspace s p /\ &0 < p
      ==> ((\x. lambda i. max (f x$i) (g x$i)):real^M->real^N) IN lspace s p"
   (REWRITE_TAC [lspace, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [MEASURABLE_ON_MAX] THEN
    MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC
     (← q r"\x. lift(&(dimindex(:N)) rpow p *
               max (norm((f:real^M->real^N) x) rpow p)
                   (norm((g:real^M->real^N) x) rpow p))") THEN
    ASM_SIMP_TAC [MEASURABLE_ON_LIFT_RPOW, MEASURABLE_ON_NORM,
                  MEASURABLE_ON_MAX] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_MAX_1 THEN
      CONJ_TAC THEN MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
      ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC [IMP_IMP, DIMINDEX_1, FORALL_1, ← GSYM drop, LIFT_DROP] THEN
      SIMP_TAC [RPOW_POS_LE, NORM_POS_LE],
      X_GEN_TAC (← q r"x:real^M") THEN DISCH_TAC THEN
      ASM_SIMP_TAC [REAL_MAX_RPOW, NORM_POS_LE, REAL_LT_IMP_LE] THEN
      REWRITE_TAC [← GSYM RPOW_MUL, NORM_LIFT, REAL_ABS_RPOW, REAL_ABS_NORM] THEN
      REWRITE_TAC [LIFT_DROP] THEN MATCH_MP_TAC RPOW_LE2 THEN
      ASM_SIMP_TAC [REAL_LT_IMP_LE, NORM_POS_LE] THEN
      W (MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] REAL_LE_TRANS) THEN
      GEN_REWRITE_TAC
        (RAND_CONV o LAND_CONV o RAND_CONV) [← GSYM CARD_NUMSEG_1] THEN
      MATCH_MP_TAC SUM_BOUND THEN
      SIMP_TAC [FINITE_NUMSEG, IN_NUMSEG, LAMBDA_BETA] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC (← REAL_ARITH
       (← q r"abs(x) <= y /\ abs(x') <= y' ==> abs(max x x') <= max y y'")) THEN
      ASM_SIMP_TAC [COMPONENT_LE_NORM]])

  let LSPACE_MIN ← prove
   r"!s p k f:real^M->real^N g:real^M->real^N.
      f IN lspace s p /\ g IN lspace s p /\ &0 < p
      ==> ((\x. lambda i. min (f x$i) (g x$i)):real^M->real^N) IN lspace s p"
   (REWRITE_TAC [lspace, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [MEASURABLE_ON_MIN] THEN
    MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC
     (← q r"\x. lift(&(dimindex(:N)) rpow p *
               max (norm((f:real^M->real^N) x) rpow p)
                   (norm((g:real^M->real^N) x) rpow p))") THEN
    ASM_SIMP_TAC [MEASURABLE_ON_LIFT_RPOW, MEASURABLE_ON_NORM,
                  MEASURABLE_ON_MIN] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_MAX_1 THEN
      CONJ_TAC THEN MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
      ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC [IMP_IMP, DIMINDEX_1, FORALL_1, ← GSYM drop, LIFT_DROP] THEN
      SIMP_TAC [RPOW_POS_LE, NORM_POS_LE],
      X_GEN_TAC (← q r"x:real^M") THEN DISCH_TAC THEN
      ASM_SIMP_TAC [REAL_MAX_RPOW, NORM_POS_LE, REAL_LT_IMP_LE] THEN
      REWRITE_TAC [← GSYM RPOW_MUL, NORM_LIFT, REAL_ABS_RPOW, REAL_ABS_NORM] THEN
      REWRITE_TAC [LIFT_DROP] THEN MATCH_MP_TAC RPOW_LE2 THEN
      ASM_SIMP_TAC [REAL_LT_IMP_LE, NORM_POS_LE] THEN
      W (MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] REAL_LE_TRANS) THEN
      GEN_REWRITE_TAC
        (RAND_CONV o LAND_CONV o RAND_CONV) [← GSYM CARD_NUMSEG_1] THEN
      MATCH_MP_TAC SUM_BOUND THEN
      SIMP_TAC [FINITE_NUMSEG, IN_NUMSEG, LAMBDA_BETA] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC (← REAL_ARITH
       (← q r"abs(x) <= y /\ abs(x') <= y' ==> abs(min x x') <= max y y'")) THEN
      ASM_SIMP_TAC [COMPONENT_LE_NORM]])

  let LSPACE_BOUNDED_MEASURABLE ← prove
   r"!s p f:real^M->real^N g:real^M->real^P.
        &0 < p /\ f measurable_on s /\ g IN lspace s p /\
        (!x. x IN s ==> norm(f x) <= norm(g x))
        ==> f IN lspace s p"
   (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [lspace, IN_ELIM_THM] THEN
    MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC (← q r"\x. lift(norm((g:real^M->real^P) x) rpow p)") THEN
    ASM_SIMP_TAC [LSPACE_IMP_INTEGRABLE] THEN
    ASM_SIMP_TAC [MEASURABLE_ON_LIFT_RPOW, MEASURABLE_ON_NORM] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [NORM_LIFT, LIFT_DROP] THEN
    REWRITE_TAC [REAL_ABS_RPOW, REAL_ABS_NORM] THEN
    ASM_SIMP_TAC [RPOW_LE2, REAL_LT_IMP_LE, NORM_POS_LE])

  let LSPACE_BOUNDED_MEASURABLE_SIMPLE ← prove
   r"!s p f:real^M->real^N.
        &0 < p /\ f measurable_on s /\ measurable s /\ bounded(IMAGE f s)
        ==> f IN lspace s p"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (← HolLight.INST_TYPE [(← qty "1", ← qty "P")] LSPACE_BOUNDED_MEASURABLE) THEN
    MATCH_MP_TAC (← MESON [] (← q r"(?x. P(\a. lift x)) ==> (?x. P x)")) THEN
    ASM_SIMP_TAC [LSPACE_CONST, NORM_LIFT] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [BOUNDED_POS]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC [FORALL_IN_IMAGE] THEN
    SIMP_TAC [real_abs, REAL_LT_IMP_LE])

  let LSPACE_INTEGRABLE_PRODUCT ← prove
   r"!s p q f:real^M->real^N g:real^M->real^N.
        &0 < p /\ &0 < q /\ inv(p) + inv(q) = &1 /\
        f IN lspace s p /\ g IN lspace s q
        ==> (\x. lift(norm(f x) * norm(g x))) integrable_on s"
   (REWRITE_TAC [lspace, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC (← q r"\x. lift(norm((f:real^M->real^N) x) rpow p / p) +
                    lift(norm((g:real^M->real^N) x) rpow q / q)") THEN
    REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC [LIFT_CMUL] THEN
      GEN_REWRITE_TAC (LAND_CONV o ABS_CONV o LAND_CONV)
          [← GSYM LIFT_DROP] THEN
      MATCH_MP_TAC MEASURABLE_ON_DROP_MUL THEN
      CONJ_TAC THEN MATCH_MP_TAC MEASURABLE_ON_NORM THEN ASM_REWRITE_TAC [],
      MATCH_MP_TAC INTEGRABLE_ADD THEN
      REWRITE_TAC [← ONCE_REWRITE_RULE [REAL_MUL_SYM] real_div] THEN
      REWRITE_TAC [LIFT_CMUL] THEN CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
      ASM_REWRITE_TAC [],
      REWRITE_TAC [NORM_LIFT, REAL_ABS_MUL, REAL_ABS_NORM, LIFT_DROP,
                   DROP_ADD] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC YOUNG_INEQUALITY THEN
      ASM_REWRITE_TAC [NORM_POS_LE]])

  let LSPACE_1 ← prove
   r"!f:real^M->real^N s. f IN lspace s (&1) <=> f absolutely_integrable_on s"
   (REWRITE_TAC [ABSOLUTELY_INTEGRABLE_MEASURABLE, lspace, IN_ELIM_THM] THEN
    REWRITE_TAC [RPOW_POW, REAL_POW_1])

  let LSPACE_MONO ← prove
   r"!f:real^M->real^N s p q.
        f IN lspace s q /\ measurable s /\ &0 < p /\ p <= q
        ==> f IN lspace s p"
   (REWRITE_TAC [lspace, IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC (← q r"\x. lift(max (&1) (norm((f:real^M->real^N) x) rpow q))") THEN
    ASM_SIMP_TAC [MEASURABLE_ON_LIFT_RPOW, MEASURABLE_ON_NORM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_MAX_1 THEN
      CONJ_TAC THEN MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
      ASM_SIMP_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, INTEGRABLE_ON_CONST] THEN
      REWRITE_TAC [IMP_IMP, DIMINDEX_1, FORALL_1, ← GSYM drop, LIFT_DROP] THEN
      SIMP_TAC [RPOW_POS_LE, NORM_POS_LE, REAL_POS],
      X_GEN_TAC (← q r"x:real^M") THEN DISCH_TAC THEN
      REWRITE_TAC [NORM_LIFT, LIFT_DROP, REAL_ABS_RPOW, REAL_ABS_NORM] THEN
      DISJ_CASES_TAC (← ISPECL [← q r"&1", ← q r"norm((f:real^M->real^N) x)"]
        REAL_LE_TOTAL)
      THENL
       [MATCH_MP_TAC (← REAL_ARITH (← q r"x <= y ==> x <= max z y")) THEN
        MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REWRITE_TAC [],
        MATCH_MP_TAC (← REAL_ARITH (← q r"x <= y ==> x <= max y z")) THEN
        MATCH_MP_TAC RPOW_1_LE THEN REWRITE_TAC [NORM_POS_LE] THEN
        ASM_REAL_ARITH_TAC]])

  let LSPACE_INCLUSION ← prove
   r"!s p q. measurable s /\ &0 < p /\ p <= q
           ==> (lspace s q :(real^M->real^N)->bool) SUBSET (lspace s p)"
   (REWRITE_TAC [SUBSET] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC LSPACE_MONO THEN EXISTS_TAC (← q r"q:real") THEN
    ASM_REWRITE_TAC [])

  let LSPACE_SUBSET ← prove
   r"!(f:real^M->real^N) s t p.
        f IN lspace t p /\ lebesgue_measurable s /\ s SUBSET t
        ==> f IN lspace s p"
   (REWRITE_TAC [LSPACE_ALT, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_MESON_TAC [MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET,
                   ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET])

  pure { lspace, LSPACE_ALT, LSPACE_ZERO, LSPACE_CONST, LSPACE_0, LSPACE_CMUL,
         LSPACE_NEG, LSPACE_ADD, LSPACE_SUB, LSPACE_IMP_INTEGRABLE, LSPACE_NORM,
         LSPACE_VSUM, LSPACE_MAX, LSPACE_MIN, LSPACE_BOUNDED_MEASURABLE,
         LSPACE_BOUNDED_MEASURABLE_SIMPLE, LSPACE_INTEGRABLE_PRODUCT, LSPACE_1,
         LSPACE_MONO, LSPACE_INCLUSION, LSPACE_SUBSET }

/- ------------------------------------------------------------------------- -/
/- The corresponding seminorm; Hoelder's inequality.                         -/
/- (lpspaces.ml 298-458)                                                    -/
/- ------------------------------------------------------------------------- -/

structure LSB where
  lnorm : thm
  LNORM_0 : thm
  LNORM_CONST : thm
  LNORM_MONO : thm
  LNORM_NEG : thm
  LNORM_MUL : thm
  LNORM_EQ_0 : thm
  LNORM_POS_LE : thm
  LNORM_NORM : thm
  LNORM_RPOW : thm
  INTEGRAL_LNORM_RPOW : thm
  HOELDER_INEQUALITY : thm
  HOELDER_INEQUALITY_FULL : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupLSB [HolBase] (D : LpSpacesDeps) (BLSA : LSA) : ExceptT String IO LSB := do
  -- @@SCOPE BEGIN
  let { lspace, LSPACE_IMP_INTEGRABLE, LSPACE_INTEGRABLE_PRODUCT, .. } := BLSA
  let { YOUNG_INEQUALITY, .. } := D.rzag
  let { INTEGRAL_CONST_GEN, .. } := D.qmeasure
  let { RPOW_EQ_0, RPOW_INV, RPOW_LE2, RPOW_MUL, RPOW_POS_LE, RPOW_POS_LT, RPOW_POW,
        RPOW_RPOW, RPOW_ZERO, .. } := D.ra.tsab
  let { HAS_INTEGRAL_NEGLIGIBLE_EQ, INTEGRABLE_ADD, INTEGRABLE_CMUL, INTEGRAL_0,
        INTEGRAL_ADD, .. } := D.ra.ts.cn.ms.qintegration2
  let { INTEGRAL_CMUL, INTEGRAL_DROP_LE, INTEGRAL_DROP_LE_AE, INTEGRAL_DROP_POS,
        INTEGRAL_EQ_HAS_INTEGRAL, NEGLIGIBLE_SUBSET, .. } := D.ra.ts.cn.ms.qintegration3
  let { MESON_TAC, new_definition, REAL_ARITH, .. } := D.ra.ts.cn.cx.cvx
  let { REAL_POW_1, .. } := D.ra.ts.cn.cx.cpx
  let { lift, .. } := D.ra.ts.cn.ms.ig.qvec
  let { CART_EQ, DIMINDEX_1, EXTENSION, .. } := D.ra.ts.cn.cx.cvx.core1
  let { IMP_CONJ, .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, LAMBDA_BETA, MONO_FORALL, REAL_ABS_INV, REAL_ABS_POS,
        .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_ENTIRE, REAL_INV_EQ_0, REAL_INV_MUL, REAL_LE_INV_EQ, REAL_LE_LDIV_EQ,
        REAL_LE_MUL, REAL_LE_REFL, REAL_LE_TRANS, REAL_LT_IMP_NZ, REAL_LT_MUL,
        .. } := D.ra.ts.cn.cx.cvx.core4
  let { REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_RID, REAL_MUL_RINV,
        REAL_MUL_SYM, SUBSET, .. } := D.ra.ts.cn.cx.cvx.core5
  let { real_abs, real_div, .. } := D.ra.ts.cn.cx.cvx.core6
  let { DROP_ADD, DROP_CMUL, DROP_EQ, DROP_VEC, FORALL_1, LIFT_ADD, LIFT_CMUL, LIFT_DROP,
        LIFT_EQ, LIFT_NUM, NORM_0, NORM_EQ_0, .. } := D.ra.ts.cn.cx.cvx.vec2
  let { NORM_LIFT, NORM_MUL, NORM_NEG, NORM_POS_LE, REAL_ABS_NORM,
        .. } := D.ra.ts.cn.cx.cvx.vec3
  let { VEC_COMPONENT, VECTOR_MUL_ASSOC, .. } := D.ra.ts.cn.cx.cvx.vec4
  -- @@SCOPE END

  let lnorm ← new_definition
   r"lnorm s p f = drop(integral s (\x. lift(norm(f x) rpow p))) rpow (inv p)"

  let LNORM_0 ← prove
   r"!s p. ~(p = &0) ==> lnorm s p (\x. vec 0) = &0"
   (REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [lnorm, NORM_0, RPOW_ZERO] THEN
    ASM_REWRITE_TAC [LIFT_NUM, INTEGRAL_0, DROP_VEC, RPOW_ZERO, REAL_INV_EQ_0])

  let LNORM_CONST ← prove
   r"!s p c:real^N.
      measurable s /\ &0 < p
      ==> lnorm s p (\x:real^M. c) = measure s rpow (inv p) * norm c"
   (SIMP_TAC [lnorm, INTEGRAL_CONST_GEN, DROP_CMUL, LIFT_DROP] THEN
    SIMP_TAC [RPOW_RPOW, NORM_POS_LE, RPOW_MUL] THEN
    SIMP_TAC [REAL_MUL_RINV, REAL_LT_IMP_NZ, RPOW_POW, REAL_POW_1])

  let LNORM_MONO ← prove
   r"!f:real^M->real^N g:real^M->real^P s t p.
        &0 <= p /\ f IN lspace s p /\ g IN lspace s p /\
        negligible t /\ (!x. x IN s DIFF t ==> norm(f x) <= norm(g x))
        ==> lnorm s p f <= lnorm s p g"
   (REWRITE_TAC [lspace, lnorm, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC RPOW_LE2 THEN ASM_REWRITE_TAC [REAL_LE_INV_EQ] THEN
    ASM_SIMP_TAC [INTEGRAL_DROP_POS, LIFT_DROP, RPOW_POS_LE, NORM_POS_LE] THEN
    MATCH_MP_TAC INTEGRAL_DROP_LE_AE THEN
    EXISTS_TAC (← q r"t:real^M->bool") THEN ASM_REWRITE_TAC [LIFT_DROP] THEN
    ASM_SIMP_TAC [RPOW_LE2, NORM_POS_LE])

  let LNORM_NEG ← prove
   r"!s p f:real^M->real^N. lnorm s p (\x. --(f x)) = lnorm s p f"
   (REWRITE_TAC [lnorm, NORM_NEG])

  let LNORM_MUL ← prove
   r"!s p f c. f IN lspace s p /\ ~(p = &0)
             ==> lnorm s p (\x. c % f x) = abs(c) * lnorm s p f"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [lnorm, NORM_MUL, RPOW_MUL, LIFT_CMUL] THEN
    ASM_SIMP_TAC [INTEGRAL_CMUL, LSPACE_IMP_INTEGRABLE] THEN
    REWRITE_TAC [DROP_CMUL, RPOW_MUL] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC [RPOW_RPOW, REAL_ABS_POS, REAL_MUL_RINV] THEN
    REWRITE_TAC [RPOW_POW, REAL_POW_1])

  let LNORM_EQ_0 ← prove
   r"!s p f. ~(p = &0) /\ f IN lspace s p
           ==> (lnorm s p f = &0 <=>
                negligible {x | x IN s /\ ~(f x = vec 0)})"
   (REWRITE_TAC [lspace, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [lnorm, RPOW_EQ_0, REAL_INV_EQ_0] THEN
    REWRITE_TAC [← GSYM LIFT_EQ, LIFT_NUM, LIFT_DROP] THEN
    ASM_SIMP_TAC [INTEGRAL_EQ_HAS_INTEGRAL] THEN
    SIMP_TAC [HAS_INTEGRAL_NEGLIGIBLE_EQ, lift, LAMBDA_BETA, NORM_POS_LE,
              RPOW_POS_LE] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN
    SIMP_TAC [IN_ELIM_THM, CART_EQ, LAMBDA_BETA] THEN
    REWRITE_TAC [FORALL_1, DIMINDEX_1, VEC_COMPONENT] THEN
    ASM_REWRITE_TAC [RPOW_EQ_0, NORM_EQ_0, CART_EQ, VEC_COMPONENT])

  let LNORM_POS_LE ← prove
   r"!s p f. f IN lspace s p ==> &0 <= lnorm s p f"
   (SIMP_TAC [lspace, IN_ELIM_THM, lnorm] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC RPOW_POS_LE THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    ASM_SIMP_TAC [LIFT_DROP, NORM_POS_LE, RPOW_POS_LE])

  let LNORM_NORM ← prove
   r"!s p f. lnorm s p (\x. lift(norm(f x))) = lnorm s p f"
   (REWRITE_TAC [lnorm, NORM_LIFT, REAL_ABS_NORM])

  let LNORM_RPOW ← prove
   r"!s p f:real^M->real^N.
        f IN lspace s p /\ ~(p = &0)
        ==> (lnorm s p f) rpow p =
            drop(integral s (\x. lift(norm(f x) rpow p)))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [lnorm] THEN
    ASM_SIMP_TAC [INTEGRAL_DROP_POS, LIFT_DROP, NORM_POS_LE, RPOW_RPOW,
                  LSPACE_IMP_INTEGRABLE, RPOW_POS_LE] THEN
    ASM_SIMP_TAC [REAL_MUL_LINV, RPOW_POW, REAL_POW_1])

  let INTEGRAL_LNORM_RPOW ← prove
   r"!s p f:real^M->real^N.
        f IN lspace s p /\ ~(p = &0)
        ==> integral s (\x. lift(norm(f x) rpow p)) =
            lift((lnorm s p f) rpow p)"
   (SIMP_TAC [← GSYM DROP_EQ, LIFT_DROP, LNORM_RPOW])

  let HOELDER_INEQUALITY ← prove
   r"!s p q f:real^M->real^N g:real^M->real^N.
        &0 < p /\ &0 < q /\ inv(p) + inv(q) = &1 /\
        f IN lspace s p /\ g IN lspace s q
        ==> drop(integral s (\x. lift(norm(f x) * norm(g x))))
              <= lnorm s p f * lnorm s q g"
   (MP_TAC LSPACE_INTEGRABLE_PRODUCT THEN
    REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"&0 <= lnorm s p (f:real^M->real^N) /\
                  &0 <= lnorm s q (g:real^M->real^N)")
    MP_TAC THENL [ASM_SIMP_TAC [LNORM_POS_LE], REWRITE_TAC [IMP_CONJ]] THEN
    REPEAT
     (GEN_REWRITE_TAC LAND_CONV [← REAL_ARITH (← q r"&0 <= x <=> x = &0 \/ &0 < x")] THEN
      DISCH_THEN (DISJ_CASES_THEN2 MP_TAC ASSUME_TAC) THENL
       [ASM_SIMP_TAC [LNORM_EQ_0, REAL_LT_IMP_NZ] THEN REPEAT DISCH_TAC THEN
        MATCH_MP_TAC (← REAL_ARITH (← q r"&0 <= y /\ x = &0 ==> x <= y")) THEN
        ASM_SIMP_TAC [REAL_LE_MUL, LNORM_POS_LE, ← GSYM LIFT_EQ, LIFT_DROP] THEN
        ASM_SIMP_TAC [INTEGRAL_EQ_HAS_INTEGRAL, LIFT_NUM] THEN
        SIMP_TAC [HAS_INTEGRAL_NEGLIGIBLE_EQ, lift, LAMBDA_BETA, NORM_POS_LE,
                  REAL_LE_MUL] THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
            NEGLIGIBLE_SUBSET)) THEN
        SIMP_TAC [CART_EQ, SUBSET, IN_ELIM_THM, LAMBDA_BETA] THEN
        REWRITE_TAC [DIMINDEX_1, FORALL_1, VEC_COMPONENT] THEN
        REWRITE_TAC [REAL_ENTIRE, CART_EQ, NORM_EQ_0, VEC_COMPONENT] THEN
        MESON_TAC [],
        ALL_TAC]) THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_LID] THEN
    ASM_SIMP_TAC [← GSYM REAL_LE_LDIV_EQ, REAL_LT_MUL] THEN
    REWRITE_TAC [← ONCE_REWRITE_RULE [REAL_MUL_SYM] real_div] THEN
    REWRITE_TAC [← GSYM DROP_CMUL] THEN ASM_SIMP_TAC [← GSYM INTEGRAL_CMUL] THEN
    REWRITE_TAC [REAL_INV_MUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"drop(integral s
     (\x. lift(norm(inv(lnorm s p f) % (f:real^M->real^N) x) rpow p / p +
               norm(inv(lnorm s q g) % (g:real^M->real^N) x) rpow q / q)))") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_LE THEN
      ASM_SIMP_TAC [LIFT_DROP, INTEGRABLE_CMUL] THEN CONJ_TAC THENL
       [REWRITE_TAC [LIFT_ADD] THEN MATCH_MP_TAC INTEGRABLE_ADD THEN
        REWRITE_TAC [NORM_MUL, RPOW_MUL] THEN
        REWRITE_TAC [← ONCE_REWRITE_RULE [REAL_MUL_SYM] real_div] THEN
        ASM_SIMP_TAC [LSPACE_IMP_INTEGRABLE, INTEGRABLE_CMUL, LIFT_CMUL],
        REWRITE_TAC [DROP_CMUL, LIFT_DROP, NORM_MUL, REAL_ABS_INV] THEN
        ASM_SIMP_TAC [real_abs, LNORM_POS_LE, REAL_LT_IMP_NZ] THEN
        ONCE_REWRITE_TAC [← REAL_ARITH
         (← q r"(a * b) * (c * d:real) = (a * c) * (b * d)")] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC YOUNG_INEQUALITY THEN
        ASM_SIMP_TAC [REAL_LE_MUL, NORM_POS_LE, LNORM_POS_LE, REAL_LE_INV_EQ]],
      REWRITE_TAC [LIFT_ADD, NORM_MUL, LIFT_CMUL, RPOW_MUL] THEN
      REWRITE_TAC [← ONCE_REWRITE_RULE [REAL_MUL_SYM] real_div] THEN
      REWRITE_TAC [LIFT_CMUL, VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC [INTEGRAL_ADD, INTEGRABLE_CMUL, INTEGRAL_CMUL,
                    LSPACE_IMP_INTEGRABLE, REAL_ABS_INV] THEN
      ASM_SIMP_TAC [← REAL_ARITH (← q r"&0 < x ==> abs x = x"), RPOW_INV] THEN
      ASM_SIMP_TAC [INTEGRAL_LNORM_RPOW, REAL_LT_IMP_NZ] THEN
      REWRITE_TAC [DROP_ADD, DROP_CMUL, LIFT_DROP] THEN
      ASM_SIMP_TAC [← GSYM REAL_MUL_ASSOC, REAL_MUL_LINV, REAL_LT_IMP_NZ,
                    RPOW_POS_LT] THEN
      ASM_REWRITE_TAC [REAL_MUL_RID, REAL_LE_REFL]])

  let HOELDER_INEQUALITY_FULL ← prove
   r"!s p q f:real^M->real^N g:real^M->real^N.
        &0 < p /\ &0 < q /\ inv(p) + inv(q) = &1 /\
        f IN lspace s p /\ g IN lspace s q
        ==> (\x. lift(norm(f x) * norm(g x))) integrable_on s /\
            drop(integral s (\x. lift(norm(f x) * norm(g x))))
              <= lnorm s p f * lnorm s q g"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP LSPACE_INTEGRABLE_PRODUCT) THEN
    ASM_SIMP_TAC [HOELDER_INEQUALITY])

  pure { lnorm, LNORM_0, LNORM_CONST, LNORM_MONO, LNORM_NEG, LNORM_MUL, LNORM_EQ_0,
         LNORM_POS_LE, LNORM_NORM, LNORM_RPOW, INTEGRAL_LNORM_RPOW, HOELDER_INEQUALITY,
         HOELDER_INEQUALITY_FULL }

/- ------------------------------------------------------------------------- -/
/- Minkowski's inequality; a Hoelder-based bound on integral, theorem 222    -/
/- in Hardy-Littlewood-Polya.                                                -/
/- (lpspaces.ml 459-620)                                                    -/
/- ------------------------------------------------------------------------- -/

structure LSC where
  LNORM_TRIANGLE : thm
  VSUM_LNORM : thm
  HOELDER_BOUND : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupLSC [HolBase] (D : LpSpacesDeps) (BLSA : LSA) (BLSB : LSB) : ExceptT String IO LSC := do
  -- @@SCOPE BEGIN
  let { lspace, LSPACE_1, LSPACE_ADD, LSPACE_CONST, LSPACE_IMP_INTEGRABLE, LSPACE_MONO,
        LSPACE_NORM, LSPACE_VSUM, .. } := BLSA
  let { HOELDER_INEQUALITY_FULL, lnorm, LNORM_0, LNORM_CONST, LNORM_NORM, LNORM_POS_LE,
        LNORM_RPOW, .. } := BLSB
  let { MEASURABLE_ON_LIFT_RPOW, .. } := D.rzbu
  let { INTEGRAL_DROP_LE_MEASURABLE, MEASURABLE_ON_LIFT_MUL, .. } := D.qmeasure
  let { REAL_ABS_RPOW, RPOW_ADD, RPOW_ADD_ALT, RPOW_LE2, RPOW_MUL, RPOW_POS_LE,
        RPOW_POS_LT, RPOW_POW, RPOW_RPOW, .. } := D.ra.tsab
  let { MEASURABLE_ON_ADD, MEASURABLE_ON_NORM, MEASURE_POS_LE, .. } := D.ra.qmeasure
  let { ABSOLUTELY_INTEGRABLE_LE, .. } := D.ra.ts.cn.ms.qintegration1
  let { INTEGRABLE_ADD, INTEGRAL_ADD, .. } := D.ra.ts.cn.ms.qintegration2
  let { INTEGRAL_DROP_POS, .. } := D.ra.ts.cn.ms.qintegration3
  let { REAL_ABS_LE, .. } := D.ra.ts.cn.ms.qsession
  let { ASM_REAL_ARITH_TAC, MESON, REAL_ARITH, REAL_FIELD, .. } := D.ra.ts.cn.cx.cvx
  let { REAL_LE_LCANCEL_IMP, REAL_POW_1, .. } := D.ra.ts.cn.cx.cpx
  let { NORM_BASIS_1, .. } := D.ra.ts.cn.ms.ig.qvec
  let { ETA_AX, FINITE_INDUCT_STRONG, .. } := D.ra.ts.cn.cx.cvx.core1
  let { IMP_CONJ, .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_INSERT, REAL_ADD_RDISTRIB, .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_INV_1, REAL_INV_DIV, REAL_LE_ADD, REAL_LE_ADD2, REAL_LE_LMUL, REAL_LE_MUL,
        REAL_LE_REFL, REAL_LE_RMUL, REAL_LT_DIV, .. } := D.ra.ts.cn.cx.cvx.core4
  let { REAL_MUL_LID, REAL_MUL_RID, REAL_MUL_SYM, REAL_SUB_LT, REAL_SUB_REFL,
        RIGHT_FORALL_IMP_THM, .. } := D.ra.ts.cn.cx.cvx.core5
  let { real_div, real_pow, SUM_CLAUSES, .. } := D.ra.ts.cn.cx.cvx.core6
  let { DROP_ADD, LIFT_DROP, NORM_1, .. } := D.ra.ts.cn.cx.cvx.vec2
  let { NORM_LIFT, NORM_POS_LE, NORM_TRIANGLE, REAL_ABS_NORM, .. } := D.ra.ts.cn.cx.cvx.vec3
  let { VSUM_CLAUSES, .. } := D.ra.ts.cn.cx.cvx.vec4
  -- @@SCOPE END

  let LNORM_TRIANGLE ← prove
   r"!s p f:real^M->real^N g:real^M->real^N.
        f IN lspace s p /\ g IN lspace s p /\ &1 <= p
        ==> lnorm s p (\x. f x + g x) <= lnorm s p f + lnorm s p g"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"p = &1") THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      ASM_SIMP_TAC [lnorm,
        ← MESON [RPOW_POW, REAL_POW_1, REAL_INV_1] (← q r"x rpow (inv(&1)) = x"),
        ← GSYM DROP_ADD, ← GSYM INTEGRAL_ADD, LSPACE_IMP_INTEGRABLE] THEN
      MATCH_MP_TAC INTEGRAL_DROP_LE_MEASURABLE THEN
      ASM_SIMP_TAC [LSPACE_IMP_INTEGRABLE, INTEGRABLE_ADD] THEN
      REWRITE_TAC [RPOW_POW, REAL_POW_1, LIFT_DROP, DROP_ADD] THEN
      REWRITE_TAC [NORM_POS_LE, NORM_TRIANGLE] THEN
      MATCH_MP_TAC MEASURABLE_ON_NORM THEN MATCH_MP_TAC MEASURABLE_ON_ADD THEN
      RULE_ASSUM_TAC (REWRITE_RULE [lspace, IN_ELIM_THM]) THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"&1 < p") ASSUME_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    SUBGOAL_THEN (← q r"&0 <= lnorm s p (\x. (f:real^M->real^N) x + g x)") MP_TAC THENL
     [ASM_SIMP_TAC [LNORM_POS_LE, LSPACE_ADD, ← REAL_ARITH (← q r"&1 <= p ==> &0 <= p")],
      GEN_REWRITE_TAC LAND_CONV [← REAL_ARITH (← q r"&0 <= x <=> x = &0 \/ &0 < x")] THEN
      STRIP_TAC THEN ASM_SIMP_TAC [LNORM_POS_LE, REAL_LE_ADD]] THEN
    MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
    EXISTS_TAC (← q r"lnorm s p (\x. (f:real^M->real^N) x + g x) rpow (p - &1)") THEN
    ASM_SIMP_TAC [RPOW_POS_LT] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← GSYM REAL_POW_1] THEN
    ASM_SIMP_TAC [← GSYM RPOW_POW, ← GSYM RPOW_ADD] THEN
    ASM_SIMP_TAC [LSPACE_ADD, LNORM_RPOW, ← REAL_ARITH (← q r"p - &1 + &1 = p"),
                  ← REAL_ARITH (← q r"&1 <= p ==> &0 <= p /\ ~(p = &0)")] THEN
    CONV_TAC (LAND_CONV (SUBS_CONV [← REAL_ARITH (← q r"p = &1 + (p - &1)")])) THEN
    ASM_SIMP_TAC [RPOW_ADD_ALT, NORM_POS_LE, ← REAL_ARITH
     (← q r"&1 <= p ==> &1 + p - &1 = &0 ==> p - &1 = &0")] THEN
    REWRITE_TAC [RPOW_POW, REAL_POW_1] THEN
    MP_TAC (← ISPECL
     [← q r"s:real^M->bool", ← q r"p:real", ← q r"p / (p - &1)",
      ← q r"\x. lift(norm((g:real^M->real^N) x))",
      ← q r"\x. lift(norm((f:real^M->real^N)(x) + g(x)) rpow (p - &1))"]
          HOELDER_INEQUALITY_FULL) THEN
    MP_TAC (← ISPECL
     [← q r"s:real^M->bool", ← q r"p:real", ← q r"p / (p - &1)",
      ← q r"\x. lift(norm((f:real^M->real^N) x))",
      ← q r"\x. lift(norm((f:real^M->real^N)(x) + g(x)) rpow (p - &1))"]
          HOELDER_INEQUALITY_FULL) THEN
    ASM_SIMP_TAC [LSPACE_NORM, REAL_LT_DIV, REAL_SUB_LT,
                  ← REAL_ARITH (← q r"&1 < p ==> &0 < p"),
                  ← REAL_FIELD (← q r"&1 < p ==> inv(p) + inv(p / (p - &1)) = &1")] THEN
    MATCH_MP_TAC (← TAUT
      (← q r"p /\ (q ==> r ==> s) ==> (p ==> q) ==> (p ==> r) ==> s")) THEN
    CONJ_TAC THENL
     [SIMP_TAC [lspace, IN_ELIM_THM, NORM_LIFT, REAL_ABS_NORM, REAL_ABS_RPOW,
                RPOW_RPOW, NORM_POS_LE] THEN
      ASM_SIMP_TAC [← REAL_FIELD (← q r"&1 < p ==> (p - &1) * p / (p - &1) = p")] THEN
      ASM_SIMP_TAC [LSPACE_IMP_INTEGRABLE, LSPACE_ADD,
                    ← REAL_ARITH (← q r"&1 < p ==> &0 <= p")] THEN
      MATCH_MP_TAC MEASURABLE_ON_LIFT_RPOW THEN
      CONJ_TAC THENL [ALL_TAC, ASM_REAL_ARITH_TAC] THEN
      SUBGOAL_THEN (← q r"((\x. f x + g x):real^M->real^N) IN lspace s p") MP_TAC THENL
       [ASM_SIMP_TAC [LSPACE_ADD, ← REAL_ARITH (← q r"&1 < p ==> &0 <= p")],
        SIMP_TAC [lspace, IN_ELIM_THM, MEASURABLE_ON_NORM]],
      ALL_TAC] THEN
    REWRITE_TAC [NORM_LIFT, REAL_ABS_NORM, LNORM_NORM, REAL_ABS_RPOW] THEN
    MATCH_MP_TAC (← TAUT
     (← q r"(p1 /\ p2 ==> b1 /\ b2 ==> c) ==> p1 /\ b1 ==> p2 /\ b2 ==> c")) THEN
    STRIP_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP REAL_LE_ADD2) THEN
    ASM_SIMP_TAC [← GSYM DROP_ADD, ← GSYM INTEGRAL_ADD] THEN
    SUBGOAL_THEN
     (← q r"lnorm s (p / (p - &1)) (\x. lift(norm (f x + g x) rpow (p - &1))) =
      lnorm s p (\x. (f:real^M->real^N) x + g x) rpow (p - &1)")
    SUBST1_TAC THENL
     [REWRITE_TAC [lnorm] THEN
      ASM_SIMP_TAC [RPOW_RPOW, INTEGRAL_DROP_POS, LIFT_DROP, NORM_POS_LE,
                    NORM_LIFT, REAL_ABS_NORM, REAL_ABS_RPOW] THEN
      ASM_SIMP_TAC [← REAL_FIELD (← q r"&1 < p ==> (p - &1) * p / (p - &1) = p")] THEN
      REWRITE_TAC [REAL_INV_DIV] THEN REWRITE_TAC [real_div] THEN
      ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN MATCH_MP_TAC (← GSYM RPOW_RPOW) THEN
      MATCH_MP_TAC INTEGRAL_DROP_POS THEN
      ASM_SIMP_TAC [LIFT_DROP, RPOW_POS_LE, NORM_POS_LE, LSPACE_IMP_INTEGRABLE,
                    LSPACE_ADD, ← REAL_ARITH (← q r"&1 < p ==> &0 <= p")],
      ALL_TAC] THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"i2 <= i1 ==> i1 <= f * y + g * y ==> i2 <= y * (f + g)")) THEN
    MATCH_MP_TAC INTEGRAL_DROP_LE_MEASURABLE THEN
    ASM_SIMP_TAC [INTEGRABLE_ADD] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_ON_LIFT_MUL THEN CONJ_TAC THENL
       [ALL_TAC,
        MATCH_MP_TAC MEASURABLE_ON_LIFT_RPOW THEN
        CONJ_TAC THENL [ALL_TAC, ASM_REAL_ARITH_TAC]] THEN
      (SUBGOAL_THEN (← q r"((\x. f x + g x):real^M->real^N) IN lspace s p") MP_TAC THENL
        [ASM_SIMP_TAC [LSPACE_ADD, ← REAL_ARITH (← q r"&1 < p ==> &0 <= p")],
         SIMP_TAC [lspace, IN_ELIM_THM, MEASURABLE_ON_NORM]]),
      REWRITE_TAC [← GSYM REAL_ADD_RDISTRIB, LIFT_DROP, DROP_ADD] THEN
      SIMP_TAC [NORM_TRIANGLE, REAL_LE_RMUL, NORM_POS_LE, RPOW_POS_LE,
                REAL_LE_MUL]])

  let VSUM_LNORM ← prove
   r"!s p f:A->real^M->real^N t.
        &1 <= p /\ FINITE t /\ (!i. i IN t ==> (f i) IN lspace s p)
        ==> lnorm s p (\x. vsum t (\i. f i x)) <= sum t (\i. lnorm s p (f i))"
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC [SUM_CLAUSES, VSUM_CLAUSES, LNORM_0, REAL_LE_REFL,
                  ← REAL_ARITH (← q r"&1 <= p ==> ~(p = &0)")] THEN
    MAP_EVERY X_GEN_TAC [← q r"i:A", ← q r"u:A->bool"] THEN
    REWRITE_TAC [IN_INSERT] THEN
    DISCH_THEN (fun th => DISCH_TAC THEN MP_TAC th) THEN
    ASM_SIMP_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    MATCH_MP_TAC (← REAL_ARITH (← q r"a <= x + y ==> y <= z ==> a <= x + z")) THEN
    W (MP_TAC o PART_MATCH (lhand o rand) LNORM_TRIANGLE o lhand o snd) THEN
    ASM_SIMP_TAC [ETA_AX, LSPACE_VSUM, ← REAL_ARITH (← q r"&1 <= p ==> &0 < p")])

  -- A Hoelder-based bound on integral, theorem 222 in Hardy-Littlewood-Polya.

  let HOELDER_BOUND ← prove
   r"!(f:real^M->real^N) s p.
        &1 <= p /\ measurable s /\ f IN lspace s p
        ==> f absolutely_integrable_on s /\
            norm(integral s f) rpow p
            <= measure s rpow (p - &1) *
               norm(integral s (\x. lift(norm(f x) rpow p)))"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [← REAL_ARITH (← q r"&1 <= p <=> p = &1 \/ &1 < p")] THEN
    ASM_CASES_TAC (← q r"p = &1") THEN ASM_REWRITE_TAC [] THENL
     [REWRITE_TAC [LSPACE_1, RPOW_POW, REAL_POW_1, REAL_SUB_REFL] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [real_pow, REAL_MUL_LID] THEN
      REWRITE_TAC [NORM_1] THEN
      MATCH_MP_TAC (← REAL_ARITH (← q r"x <= a ==> x <= abs a")) THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_LE THEN ASM_REWRITE_TAC [],
      STRIP_TAC] THEN
    MATCH_MP_TAC (← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")) THEN CONJ_TAC THENL
     [REWRITE_TAC [← GSYM LSPACE_1] THEN
      MATCH_MP_TAC LSPACE_MONO THEN EXISTS_TAC (← q r"p:real") THEN
      ASM_SIMP_TAC [] THEN ASM_REAL_ARITH_TAC,
      DISCH_TAC] THEN
    MP_TAC (← ISPECL [← q r"s:real^M->bool", ← q r"p / (p - &1)", ← q r"p:real",
                      ← q r"(\x. basis 1):real^M->real^N", ← q r"f:real^M->real^N"]
          HOELDER_INEQUALITY_FULL) THEN
    ASM_SIMP_TAC [LSPACE_CONST, LNORM_CONST, ← REAL_ARITH (← q r"&1 < p ==> &0 < p")] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_DIV, ALL_TAC] THEN
      UNDISCH_TAC (← q r"&1 < p") THEN CONV_TAC REAL_FIELD,
      REWRITE_TAC [NORM_BASIS_1, REAL_MUL_RID, REAL_MUL_LID]] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"p:real") o MATCH_MP (← REWRITE_RULE
     [← TAUT (← q r"p /\ q /\ r ==> s <=> q ==> p /\ r ==> s")] RPOW_LE2)) THEN
    ASM_SIMP_TAC [RPOW_MUL, RPOW_RPOW, MEASURE_POS_LE,
                  LNORM_RPOW, ← REAL_ARITH (← q r"&1 < p ==> &0 <= p /\ ~(p = &0)"),
                  ← REAL_FIELD (← q r"&1 < p ==> inv(p / (p - &1)) * p = p - &1"),
                  INTEGRAL_DROP_POS, LIFT_DROP, NORM_POS_LE] THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"a':real <= a /\ b <= b' ==> a <= b ==> a' <= b'")) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RPOW_LE2 THEN
      ASM_SIMP_TAC [NORM_POS_LE, ← REAL_ARITH (← q r"&1 < p ==> &0 <= p")] THEN
      ASM_SIMP_TAC [ABSOLUTELY_INTEGRABLE_LE],
      MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC [MEASURE_POS_LE, RPOW_POS_LE] THEN
      REWRITE_TAC [NORM_1, REAL_ABS_LE]])

  pure { LNORM_TRIANGLE, VSUM_LNORM, HOELDER_BOUND }

/- ------------------------------------------------------------------------- -/
/- The complex L^2 inner product (f|g) = INT f cnj(g) on an arbitrary set:   -/
/- symmetry, self product, Cauchy-Schwarz, sesquilinearity, closure.         -/
/- (lpspaces.ml 621-878)                                                    -/
/- ------------------------------------------------------------------------- -/

structure LSD where
  lproduct : thm
  LPRODUCT_SYM : thm
  CXDROP_LINEAR : thm
  CX_DROP_INTEGRAL : thm
  LPRODUCT_SELF : thm
  LPRODUCT_SELF_LNORM : thm
  LPRODUCT_CAUCHY_SCHWARZ : thm
  LPRODUCT_RMUL : thm
  LPRODUCT_RSUM : thm
  LPRODUCT_LMUL : thm
  LPRODUCT_LSUM : thm
  LSPACE_COMPLEX_LMUL : thm
  MEASURABLE_ON_CNJ : thm
  L2_CNJ_PRODUCT_INTEGRABLE : thm
  LSPACE_CNJ : thm
  LPRODUCT_LSUB : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupLSD [HolBase] (D : LpSpacesDeps) (BLSA : LSA) (BLSB : LSB) : ExceptT String IO LSD := do
  -- @@SCOPE BEGIN
  let { lspace, LSPACE_INTEGRABLE_PRODUCT, .. } := BLSA
  let { HOELDER_INEQUALITY, LNORM_RPOW, .. } := BLSB
  let { MEASURABLE_ON_COMPLEX_MUL, .. } := D.rzbs
  let { RPOW_MUL, RPOW_POW, .. } := D.ra.tsab
  let { MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE,
        MEASURABLE_ON_COMPOSE_CONTINUOUS, .. } := D.ra.qmeasure
  let { INTEGRAL_COMPLEX_LMUL, .. } := D.ra.ts.kno
  let { MEASURABLE_ON_UNIV, .. } := D.ra.ts.qmeasure
  let { SIMPLE_COMPLEX_ARITH_TAC, .. } := D.ra.ts.cn.cxa
  let { COMPLEX_MUL_SYM, .. } := D.ra.ts.cn.cxb
  let { COMPLEX_CMUL, COMPLEX_VEC_0, CX_ADD, CX_MUL, CX_POW, .. } := D.ra.ts.cn.cxc
  let { COMPLEX_RING, .. } := D.ra.ts.cn.cxd
  let { COMPLEX_NORM_MUL, .. } := D.ra.ts.cn.cxf
  let { CNJ_CNJ, CNJ_CX, CNJ_MUL, COMPLEX_MUL_CNJ, COMPLEX_NORM_CNJ, .. } := D.ra.ts.cn.cxg
  let { LINEAR_CNJ, .. } := D.ra.ts.cn.cxh
  let { CNJ_VSUM, VSUM_COMPLEX_LMUL, VSUM_COMPLEX_RMUL, .. } := D.ra.ts.cn.cxi
  let { MEASURABLE_ON_CONST, .. } := D.ra.ts.cn.qmeasure
  let { ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE, .. } := D.ra.ts.cn.ms.qintegration1
  let { INTEGRABLE_CMUL, .. } := D.ra.ts.cn.ms.qintegration2
  let { INTEGRAL_EQ, INTEGRAL_LINEAR, INTEGRAL_NORM_BOUND_INTEGRAL, INTEGRAL_SUB,
        INTEGRAL_VSUM, .. } := D.ra.ts.cn.ms.qintegration3
  let { new_definition, REAL_ARITH, REAL_RAT_REDUCE_CONV, .. } := D.ra.ts.cn.cx.cvx
  let { FUN_EQ_THM, .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_LE_REFL, REAL_LE_TRANS, .. } := D.ra.ts.cn.cx.cvx.core4
  let { o_DEF, o_THM, .. } := D.ra.ts.cn.cx.cvx.core6
  let { DROP_ADD, DROP_CMUL, LIFT_CMUL, LIFT_DROP, .. } := D.ra.ts.cn.cx.cvx.vec2
  let { linear, .. } := D.ra.ts.cn.cx.cvx.vec4
  let { LINEAR_CONTINUOUS_ON, .. } := D.ra.ts.cn.cx.cvx.top4
  -- @@SCOPE END

  let lproduct ← new_definition
   r"lproduct (s:real^N->bool) (f:real^N->complex) (g:real^N->complex) =
    integral s (\x. f x * cnj(g x))"

  -- Conjugate symmetry:  (f|g) = cnj(g|f)  (integrand assumed integrable).

  let LPRODUCT_SYM ← prove
   r"!s (f:real^N->complex) g.
     (\x. f x * cnj(g x)) integrable_on s
     ==> lproduct s f g = cnj(lproduct s g f)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [lproduct] THEN
    SUBGOAL_THEN (← q r"(\x. (g:real^N->complex) x * cnj(f x)) = (\x. cnj(f x * cnj(g x)))")
      SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM, CNJ_MUL, CNJ_CNJ] THEN REWRITE_TAC [COMPLEX_MUL_SYM],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"\x. (f:real^N->complex) x * cnj(g x)", ← q r"s:real^N->bool",
                      ← q r"cnj"]
      INTEGRAL_LINEAR) THEN
    ASM_REWRITE_TAC [LINEAR_CNJ, o_DEF] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [CNJ_CNJ])

  -- Cx(drop .) commutes with the integral of a real^1-valued integrand.
  -- (Reusable bridge: real-valued integral -> its complex embedding.)

  let CXDROP_LINEAR ← prove
   r"linear (\y:real^1. Cx(drop y))"
   (REWRITE_TAC [linear, DROP_ADD, DROP_CMUL, COMPLEX_CMUL, CX_ADD, CX_MUL] THEN
    CONV_TAC COMPLEX_RING)

  let CX_DROP_INTEGRAL ← prove
   r"!s (gg:real^N->real^1). gg integrable_on s
     ==> integral s (\x. Cx(drop(gg x))) = Cx(drop(integral s gg))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"gg:real^N->real^1", ← q r"s:real^N->bool",
                      ← q r"\y:real^1. Cx(drop y)"]
      INTEGRAL_LINEAR) THEN
    ASM_REWRITE_TAC [CXDROP_LINEAR, o_DEF])

  -- Self inner product:  (f|f) = Cx(INT |f|^2)  (real, nonneg).

  let LPRODUCT_SELF ← prove
   r"!s (f:real^N->complex).
     (\x. lift(norm(f x) pow 2)) integrable_on s
     ==> lproduct s f f = Cx(drop(integral s (\x. lift(norm(f x) pow 2))))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [lproduct] THEN
    SUBGOAL_THEN (← q r"(\x. (f:real^N->complex) x * cnj(f x)) =
                  (\x. Cx(drop(lift(norm(f x) pow 2))))") SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM, LIFT_DROP, COMPLEX_MUL_CNJ, CX_POW], ALL_TAC] THEN
    ASM_SIMP_TAC [CX_DROP_INTEGRAL])

  -- Self inner product against the norm:  (f|f) = Cx(||f||_2^2).  The bridge
  -- tying lproduct to lnorm (via LNORM_RPOW), specialised to p = 2.
  let LPRODUCT_SELF_LNORM ← prove
   r"!s (f:real^N->complex). f IN lspace s (&2)
     ==> lproduct s f f = Cx((lnorm s (&2) f) pow 2)"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"(\x. lift(norm((f:real^N->complex) x) pow 2)) integrable_on s")
     ASSUME_TAC THENL
     [FIRST_ASSUM (MP_TAC o REWRITE_RULE [lspace, IN_ELIM_THM]) THEN
      SIMP_TAC [RPOW_POW], ALL_TAC] THEN
    ASM_SIMP_TAC [LPRODUCT_SELF] THEN AP_TERM_TAC THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"&2", ← q r"f:real^N->complex"]
      LNORM_RPOW) THEN
    ASM_REWRITE_TAC [← REAL_ARITH (← q r"~(&2 = &0)")] THEN
    REWRITE_TAC [RPOW_POW] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REFL_TAC)

  -- Complex Cauchy-Schwarz:  |(f|g)| <= ||f||_2 ||g||_2  (f,g in L^2).
  -- Chains through the real-valued HOELDER_INEQUALITY (p=q=2) above via
  -- norm(INT .) <= INT norm(.) and norm(f cnj g) = ||f|| ||g||.

  let LPRODUCT_CAUCHY_SCHWARZ ← prove
   r"!s (f:real^N->complex) g.
     f IN lspace s (&2) /\ g IN lspace s (&2) /\
     (\x. f x * cnj(g x)) integrable_on s
     ==> norm(lproduct s f g) <= lnorm s (&2) f * lnorm s (&2) g"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [lproduct] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     (← q r"drop(integral s
        (\x. lift(norm((f:real^N->complex) x) * norm((g:real^N->complex) x))))") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [MP_TAC (← ISPECL
          [← q r"s:real^N->bool", ← q r"&2", ← q r"&2",
           ← q r"f:real^N->complex", ← q r"g:real^N->complex"]
          LSPACE_INTEGRABLE_PRODUCT) THEN ASM_REWRITE_TAC [] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV,
        GEN_TAC THEN DISCH_TAC THEN
        REWRITE_TAC [LIFT_DROP, COMPLEX_NORM_MUL, COMPLEX_NORM_CNJ, REAL_LE_REFL]],
      MP_TAC (← ISPECL
        [← q r"s:real^N->bool", ← q r"&2", ← q r"&2",
         ← q r"f:real^N->complex", ← q r"g:real^N->complex"]
        HOELDER_INEQUALITY) THEN
      ASM_REWRITE_TAC [] THEN CONV_TAC REAL_RAT_REDUCE_CONV])

  -- Right-conjugate-linearity of the pairing:  scaling the second argument
  -- by a complex constant pulls out its conjugate; summing the second
  -- argument over a finite family distributes.

  let LPRODUCT_RMUL ← prove
   r"!s (f:real^N->complex) (h:real^N->complex) c.
     (\x. f x * cnj(h x)) integrable_on s
     ==> lproduct s f (\x. c * h x) = cnj c * lproduct s f h"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [lproduct] THEN
    SUBGOAL_THEN (← q r"(\x. (f:real^N->complex) x * cnj(c * h x)) =
                  (\x. cnj c * (f x * cnj(h x)))")
     SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM, CNJ_MUL] THEN CONV_TAC COMPLEX_RING, ALL_TAC] THEN
    ASM_SIMP_TAC [INTEGRAL_COMPLEX_LMUL])

  let LPRODUCT_RSUM ← prove
   r"!s (f:real^N->complex) (g:A->real^N->complex) k.
     FINITE k /\ (!i. i IN k ==> (\x. f x * cnj(g i x)) integrable_on s)
     ==> lproduct s f (\x. vsum k (\i. g i x)) =
         vsum k (\i. lproduct s f (g i))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [lproduct] THEN
    SUBGOAL_THEN
     (← q r"(\x. (f:real^N->complex) x * cnj(vsum k (\i. (g:A->real^N->complex) i x))) =
      (\x. vsum k (\i. f x * cnj(g i x)))")
     SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"x:real^N") THEN
      ASM_SIMP_TAC [CNJ_VSUM, ← GSYM VSUM_COMPLEX_LMUL], ALL_TAC] THEN
    MP_TAC (← BETA_RULE (← ISPECL
      [← q r"\(i:A) (x:real^N). (f:real^N->complex) x * cnj(g i x)",
       ← q r"s:real^N->bool", ← q r"k:A->bool"] INTEGRAL_VSUM)) THEN
    ASM_REWRITE_TAC [])

  -- Left-linearity (first argument), the duals of LPRODUCT_RMUL/RSUM.  All
  -- four together give full sesquilinearity.

  let LPRODUCT_LMUL ← prove
   r"!s (f:real^N->complex) (g:real^N->complex) c.
     (\x. f x * cnj(g x)) integrable_on s
     ==> lproduct s (\x. c * f x) g = c * lproduct s f g"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [lproduct] THEN
    SUBGOAL_THEN (← q r"(\x. (c * (f:real^N->complex) x) * cnj(g x)) =
                  (\x. c * (f x * cnj(g x)))")
     SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM] THEN CONV_TAC COMPLEX_RING, ALL_TAC] THEN
    ASM_SIMP_TAC [INTEGRAL_COMPLEX_LMUL])

  let LPRODUCT_LSUM ← prove
   r"!s (g:A->real^N->complex) (h:real^N->complex) k.
     FINITE k /\ (!i. i IN k ==> (\x. g i x * cnj(h x)) integrable_on s)
     ==> lproduct s (\x. vsum k (\i. g i x)) h =
         vsum k (\i. lproduct s (g i) h)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [lproduct] THEN
    SUBGOAL_THEN
     (← q r"(\x. vsum k (\i. (g:A->real^N->complex) i x) * cnj(h x)) =
      (\x. vsum k (\i. g i x * cnj(h x)))")
     SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"x:real^N") THEN
      ASM_SIMP_TAC [← GSYM VSUM_COMPLEX_RMUL], ALL_TAC] THEN
    MP_TAC (← BETA_RULE (← ISPECL
      [← q r"\(i:A) (x:real^N). (g:A->real^N->complex) i x * cnj(h x)",
       ← q r"s:real^N->bool", ← q r"k:A->bool"] INTEGRAL_VSUM)) THEN
    ASM_REWRITE_TAC [])

  -- L^p is closed under complex-scalar multiplication and under conjugation;
  -- conjugation preserves measurability (on any set, via the zero-extension
  -- bridge MEASURABLE_ON_UNIV); and the product f cnj(g) of two L^2 functions
  -- is integrable.

  let LSPACE_COMPLEX_LMUL ← prove
   r"!(h:real^N->complex) (c:complex) p.
     h IN lspace (:real^N) p ==> (\x. c * h x) IN lspace (:real^N) p"
   (REPEAT GEN_TAC THEN REWRITE_TAC [lspace, IN_ELIM_THM] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_ON_COMPLEX_MUL THEN
      ASM_REWRITE_TAC [MEASURABLE_ON_CONST], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"(\x. lift(norm((c:complex) * h x) rpow p)) =
      (\x. (norm c rpow p) % lift(norm((h:real^N->complex) x) rpow p))")
     SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM, COMPLEX_NORM_MUL, RPOW_MUL, LIFT_CMUL], ALL_TAC] THEN
    MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC [])

  -- Conjugation preserves measurability on an ARBITRARY set s (not just the
  -- whole space): reduce to the zero-extension via MEASURABLE_ON_UNIV, using
  -- cnj(vec 0) = vec 0, then apply whole-space conjugation-measurability.
  let MEASURABLE_ON_CNJ ← prove
   r"!(g:real^N->complex) s. g measurable_on s
     ==> (\x. cnj(g x)) measurable_on s"
   (REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [← GSYM MEASURABLE_ON_UNIV] THEN REWRITE_TAC [] THEN
    SUBGOAL_THEN
     (← q r"(\x. if x IN s then cnj((g:real^N->complex) x) else vec 0) =
      cnj o (\x. if x IN s then g x else vec 0)")
     SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM, o_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC [COMPLEX_VEC_0, CNJ_CX], ALL_TAC] THEN
    MATCH_MP_TAC MEASURABLE_ON_COMPOSE_CONTINUOUS THEN
    ASM_REWRITE_TAC [MEASURABLE_ON_UNIV] THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC [LINEAR_CNJ])

  let L2_CNJ_PRODUCT_INTEGRABLE ← prove
   r"!s (f:real^N->complex) (g:real^N->complex).
     f IN lspace s (&2) /\ g IN lspace s (&2)
     ==> (\x. f x * cnj(g x)) integrable_on s"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
    EXISTS_TAC
     (← q r"\x:real^N. lift(norm((f:real^N->complex) x) * norm((g:real^N->complex) x))") THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_ON_COMPLEX_MUL THEN CONJ_TAC THENL
       [RULE_ASSUM_TAC (REWRITE_RULE [lspace, IN_ELIM_THM]) THEN ASM_REWRITE_TAC [],
        MATCH_MP_TAC MEASURABLE_ON_CNJ THEN
        RULE_ASSUM_TAC (REWRITE_RULE [lspace, IN_ELIM_THM]) THEN ASM_REWRITE_TAC []],
      MP_TAC (← ISPECL
        [← q r"s:real^N->bool", ← q r"&2", ← q r"&2", ← q r"f:real^N->complex",
         ← q r"g:real^N->complex"]
        LSPACE_INTEGRABLE_PRODUCT) THEN
      ASM_REWRITE_TAC [← REAL_ARITH (← q r"&0 < &2"),
                       ← REAL_ARITH (← q r"inv(&2)+inv(&2)= &1")],
      GEN_TAC THEN DISCH_TAC THEN
      REWRITE_TAC [LIFT_DROP, COMPLEX_NORM_MUL, COMPLEX_NORM_CNJ, REAL_LE_REFL]])

  let LSPACE_CNJ ← prove
   r"!(f:real^N->complex) s. f IN lspace s (&2)
     ==> (\x. cnj(f x)) IN lspace s (&2)"
   (REWRITE_TAC [lspace, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [MEASURABLE_ON_CNJ, COMPLEX_NORM_CNJ])

  -- Left-subtractivity of the inner product: <a|c> - <b|c> = <a-b|c>.

  let LPRODUCT_LSUB ← prove
   r"!(a:real^N->complex) b c (s:real^N->bool).
     a IN lspace s (&2) /\ b IN lspace s (&2) /\ c IN lspace s (&2)
     ==> lproduct s a c - lproduct s b c =
         lproduct s (\x. a x - b x) c"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [lproduct] THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"a:real^N->complex",
                      ← q r"c:real^N->complex"]
      L2_CNJ_PRODUCT_INTEGRABLE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"b:real^N->complex",
                      ← q r"c:real^N->complex"]
      L2_CNJ_PRODUCT_INTEGRABLE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    ASM_SIMP_TAC [← GSYM INTEGRAL_SUB] THEN
    MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
    REWRITE_TAC [] THEN SIMPLE_COMPLEX_ARITH_TAC)

  pure { lproduct, LPRODUCT_SYM, CXDROP_LINEAR, CX_DROP_INTEGRAL, LPRODUCT_SELF,
         LPRODUCT_SELF_LNORM, LPRODUCT_CAUCHY_SCHWARZ, LPRODUCT_RMUL, LPRODUCT_RSUM,
         LPRODUCT_LMUL, LPRODUCT_LSUM, LSPACE_COMPLEX_LMUL, MEASURABLE_ON_CNJ,
         L2_CNJ_PRODUCT_INTEGRABLE, LSPACE_CNJ, LPRODUCT_LSUB }

/- ------------------------------------------------------------------------- -/
/- Continuity of the inner product under L^2 convergence in either slot.     -/
/- (lpspaces.ml 879-966)                                                    -/
/- ------------------------------------------------------------------------- -/

structure LSE where
  LPRODUCT_L2LIM : thm
  LPRODUCT_L2LIM_RSLOT : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupLSE [HolBase] (D : LpSpacesDeps) (BLSA : LSA) (BLSB : LSB) (BLSD : LSD) : ExceptT String IO LSE := do
  -- @@SCOPE BEGIN
  let { LSPACE_SUB, .. } := BLSA
  let { LNORM_POS_LE, .. } := BLSB
  let { L2_CNJ_PRODUCT_INTEGRABLE, LPRODUCT_CAUCHY_SCHWARZ, LPRODUCT_LSUB, LPRODUCT_SYM,
        .. } := BLSD
  let { LIM_CNJ, .. } := D.ra.ts.knm
  let { ASM_ARITH_TAC, ASM_REAL_ARITH_TAC, .. } := D.ra.ts.cn.cx.cvx
  let { ETA_AX, .. } := D.ra.ts.cn.cx.cvx.core1
  let { FUN_EQ_THM, GE, .. } := D.ra.ts.cn.cx.cvx.core2
  let { REAL_DIV_RMUL, .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_LE_LMUL, REAL_LET_TRANS, REAL_LT_DIV, REAL_LT_IMP_NZ,
        .. } := D.ra.ts.cn.cx.cvx.core4
  let { REAL_POS, .. } := D.ra.ts.cn.cx.cvx.core5
  let { dist, .. } := D.ra.ts.cn.cx.cvx.vec4
  let { LIM_SEQUENTIALLY, .. } := D.ra.ts.cn.cx.cvx.top4
  let { REAL_LT_RMUL, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qses
  -- @@SCOPE END

  -- Continuity of the inner product under L^2 convergence in the first slot:
  -- if gn ---> g in L^2 norm (all in L^2) and h is a fixed L^2 function, then
  -- <gn|h> ---> <g|h>.  The workhorse for extending bilinear identities from
  -- a dense class to all of L^2.

  let LPRODUCT_L2LIM ← prove
   r"!(gn:num->real^N->complex) (g:real^N->complex) (h:real^N->complex)
     (s:real^N->bool).
     (!n. gn n IN lspace s (&2)) /\ g IN lspace s (&2) /\
     h IN lspace s (&2) /\
     (!e. &0 < e ==> ?M. !n. n >= M
          ==> lnorm s (&2) (\x. gn n x - g x) < e)
     ==> ((\n. lproduct s (gn n) h) --> lproduct s g h)
         sequentially"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [LIM_SEQUENTIALLY, dist] THEN X_GEN_TAC (← q r"e:real") THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"&0 <= lnorm s (&2) (h:real^N->complex)") ASSUME_TAC THENL
     [ASM_SIMP_TAC [LNORM_POS_LE], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"&0 < lnorm s (&2) (h:real^N->complex) + &1") ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC
      (← q r"e / (lnorm s (&2) (h:real^N->complex) + &1)")) THEN
    ASM_SIMP_TAC [REAL_LT_DIV] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"M:num")) THEN EXISTS_TAC (← q r"M:num") THEN
    X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN
    SUBGOAL_THEN
     (← q r"lproduct s (gn n) h - lproduct s g h =
      lproduct s (\x. (gn:num->real^N->complex) n x - g x) h")
     SUBST1_TAC THENL
     [MATCH_MP_TAC LPRODUCT_LSUB THEN ASM_REWRITE_TAC [ETA_AX], ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC (← q r"lnorm s (&2) (\x. (gn:num->real^N->complex) n x - g x) *
                lnorm s (&2) (h:real^N->complex)") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LPRODUCT_CAUCHY_SCHWARZ THEN ASM_REWRITE_TAC [] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC [REAL_POS, ETA_AX],
        MATCH_MP_TAC L2_CNJ_PRODUCT_INTEGRABLE THEN
        ASM_SIMP_TAC [LSPACE_SUB, REAL_POS, ETA_AX]],
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC (← q r"lnorm s (&2) (\x. (gn:num->real^N->complex) n x - g x) *
                  (lnorm s (&2) (h:real^N->complex) + &1)") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC LNORM_POS_LE THEN ASM_SIMP_TAC [LSPACE_SUB, REAL_POS, ETA_AX],
          ASM_REAL_ARITH_TAC],
        SUBGOAL_THEN (← q r"e = (e / (lnorm s (&2) (h:real^N->complex) + &1)) *
                          (lnorm s (&2) h + &1)") SUBST1_TAC THENL
         [ASM_SIMP_TAC [REAL_DIV_RMUL, REAL_LT_IMP_NZ], ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC [] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [GE] THEN
        ASM_ARITH_TAC]])

  -- Continuity of the inner product in the SECOND slot: mn -> m in L^2
  -- (with d a fixed L^2 function) ==> <d|mn> -> <d|m>.  Via conjugate
  -- symmetry (LPRODUCT_SYM) and first-slot continuity (LPRODUCT_L2LIM).

  let LPRODUCT_L2LIM_RSLOT ← prove
   r"!(mn:num->real^N->complex) (m:real^N->complex) (d:real^N->complex)
     (s:real^N->bool).
     (!n. mn n IN lspace s (&2)) /\ m IN lspace s (&2) /\
     d IN lspace s (&2) /\
     (!e. &0 < e ==> ?M. !n. n >= M
          ==> lnorm s (&2) (\x. mn n x - m x) < e)
     ==> ((\n. lproduct s d (mn n)) --> lproduct s d m)
         sequentially"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"(\n. lproduct s d (mn n)) =
      (\n. cnj(lproduct s ((mn:num->real^N->complex) n) d))")
     SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"k:num") THEN
      MATCH_MP_TAC LPRODUCT_SYM THEN
      MATCH_MP_TAC L2_CNJ_PRODUCT_INTEGRABLE THEN ASM_SIMP_TAC [ETA_AX],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"lproduct s d m = cnj(lproduct s (m:real^N->complex) d)")
     SUBST1_TAC THENL
     [MATCH_MP_TAC LPRODUCT_SYM THEN
      MATCH_MP_TAC L2_CNJ_PRODUCT_INTEGRABLE THEN ASM_SIMP_TAC [ETA_AX],
      ALL_TAC] THEN
    REWRITE_TAC [LIM_CNJ] THEN
    MATCH_MP_TAC LPRODUCT_L2LIM THEN ASM_REWRITE_TAC [])

  pure { LPRODUCT_L2LIM, LPRODUCT_L2LIM_RSLOT }

/- ------------------------------------------------------------------------- -/
/- Completeness (Riesz-Fischer): summable series in L_p on the whole index   -/
/- set.                                                                      -/
/- (lpspaces.ml 967-1224)                                                   -/
/- ------------------------------------------------------------------------- -/

structure LSF where
  LSPACE_SUMMABLE_UNIV : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupLSF [HolBase] (D : LpSpacesDeps) (BLSA : LSA) (BLSB : LSB) (BLSC : LSC) : ExceptT String IO LSF := do
  -- @@SCOPE BEGIN
  let { lspace, LSPACE_IMP_INTEGRABLE, LSPACE_NORM, LSPACE_SUB, LSPACE_VSUM, .. } := BLSA
  let { INTEGRAL_LNORM_RPOW, lnorm, LNORM_NORM, LNORM_POS_LE, .. } := BLSB
  let { VSUM_LNORM, .. } := BLSC
  let { REAL_PARTIAL_SUMS_LE_INFSUM, REAL_SUMS_INFSUM, .. } := D.rzc
  let { REAL_CONTINUOUS_CONTINUOUS_ATREAL, .. } := D.rzn
  let { REAL_CONTINUOUS_AT_RPOW, .. } := D.rzr
  let { LIM_NULL_RPOW, .. } := D.rzs
  let { REAL_INTEGRAL_0, .. } := D.rzal
  let { MEASURABLE_ON_LIFT_RPOW, .. } := D.rzbu
  let { MEASURABLE_ON_VSUM, .. } := D.qmeasure
  let { SERIES_LIFT_ABSCONV_IMP_CONV, .. } := D.qtopology
  let { REAL_ABS_RPOW, RPOW_LE2, RPOW_MUL, RPOW_POS_LE, RPOW_POW, RPOW_RPOW,
        .. } := D.ra.tsab
  let { MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE, MEASURABLE_ON_LIMIT,
        MEASURABLE_ON_NORM, .. } := D.ra.qmeasure
  let { summable, .. } := D.ra.ts.cn.qtopology
  let { BEPPO_LEVI_MONOTONE_CONVERGENCE_INCREASING, DOMINATED_CONVERGENCE,
        .. } := D.ra.ts.cn.ms.qintegration1
  let { INTEGRABLE_0, INTEGRABLE_CMUL, INTEGRABLE_SPIKE, INTEGRABLE_SPIKE_SET, INTEGRAL_0,
        .. } := D.ra.ts.cn.ms.qintegration2
  let { INTEGRAL_SPIKE_SET, NEGLIGIBLE_EMPTY, NEGLIGIBLE_SUBSET,
        .. } := D.ra.ts.cn.ms.qintegration3
  let { LIM_CONTINUOUS_FUNCTION, .. } := D.ra.ts.cn.ms.qtopology2
  let { VSUM_NORM_TRIANGLE, .. } := D.ra.ts.cn.ms.qvec
  let { ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, NORM_ARITH, REAL_ARITH, SET_RULE,
        SET_TAC, .. } := D.ra.ts.cn.cx.cvx
  let { LE_0, REAL_POW_1, .. } := D.ra.ts.cn.cx.cpx
  let { NORM_REAL, .. } := D.ra.ts.cn.ms.ig.qvec
  let { DIFF_EMPTY, EQ_TRANS, ETA_AX, FINITE_NUMSEG, FORALL_IN_GSPEC,
        .. } := D.ra.ts.cn.cx.cvx.core1
  let { FUN_EQ_THM, IMP_CONJ, IMP_CONJ_ALT, IMP_IMP, IN_DIFF, INTER_UNIV,
        .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_NUMSEG, LEFT_IMP_EXISTS_THM, MONO_EXISTS, MONO_FORALL, MONO_IMP,
        .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_LE_ADDR, REAL_LE_INV_EQ, REAL_LE_REFL, REAL_LE_TRANS, REAL_LT_INV_EQ,
        .. } := D.ra.ts.cn.cx.cvx.core4
  let { REAL_MUL_LINV, REAL_MUL_RINV, RIGHT_IMP_EXISTS_THM, SKOLEM_THM, SUBSET,
        .. } := D.ra.ts.cn.cx.cvx.core5
  let { o_DEF, real_abs, SUM_CLAUSES_NUMSEG, SUM_SUBSET_SIMPLE,
        .. } := D.ra.ts.cn.cx.cvx.core6
  let { DIST_0, .. } := D.ra.ts.cn.cx.cvx.vec1
  let { DROP_CMUL, DROP_VSUM, LIFT_DROP, .. } := D.ra.ts.cn.cx.cvx.vec2
  let { NORM_LIFT, NORM_POS_LE, REAL_ABS_NORM, .. } := D.ra.ts.cn.cx.cvx.vec3
  let { drop, .. } := D.ra.ts.cn.cx.cvx.vec4
  let { EVENTUALLY_MONO, EVENTUALLY_SEQUENTIALLY, EVENTUALLY_TRUE,
        TRIVIAL_LIMIT_SEQUENTIALLY, .. } := D.ra.ts.cn.cx.cvx.met
  let { bounded, .. } := D.ra.ts.cn.cx.cvx.top5
  let { ALWAYS_EVENTUALLY, .. } := D.ra.ts.cn.ms.ig.dv.qmetric
  let { LIM_DROP_LBOUND, LIM_NORM_UBOUND, LIM_NULL, LIM_NULL_NORM, sums,
        .. } := D.ra.ts.cn.ms.ig.dv.qtopology2
  let { SUM_POS_LE_NUMSEG, .. } := D.ra.ts.cn.ms.ig.dv.dg.qsession
  let { tendsto, .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology2
  let { LIFT_SUM, .. } := D.ra.ts.cn.ms.ig.dv.dg.qvec
  -- @@SCOPE END

  let LSPACE_SUMMABLE_UNIV ← prove
   r"!f:num->real^M->real^N p s.
        &1 <= p /\
        (!i. f i IN lspace s p) /\
        real_summable (:num) (\i. lnorm s p (f i))
        ==> ?g. g IN lspace s p /\
                !e. &0 < e  ==> eventually
                                  (\n. lnorm s p (\x. vsum (0..n) (\i. f i x) -
                                                      g(x)) < e)
                                  sequentially"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE id [← GSYM REAL_SUMS_INFSUM]) THEN
    ABBREV_TAC (← q r"M = real_infsum (:num) (\i. lnorm s p (f i:real^M->real^N))") THEN
    DISCH_TAC THEN
    ABBREV_TAC
     (← q r"g = \n x:real^M. vsum(0..n) (\i. lift(norm(f i x:real^N)))") THEN
    SUBGOAL_THEN (← q r"!n:num. lnorm s p (g n:real^M->real^1) <= M") ASSUME_TAC THENL
     [GEN_TAC THEN EXPAND_TAC "g" THEN
      W (MP_TAC o PART_MATCH (lhand o rand) VSUM_LNORM o lhand o snd) THEN
      ASM_SIMP_TAC [FINITE_NUMSEG, LSPACE_NORM, ETA_AX] THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] REAL_LE_TRANS) THEN
      REWRITE_TAC [LNORM_NORM] THEN EXPAND_TAC "M" THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [← SET_RULE (← q r"s = UNIV INTER s")] THEN
      REWRITE_TAC [ETA_AX] THEN MATCH_MP_TAC REAL_PARTIAL_SUMS_LE_INFSUM THEN
      ASM_SIMP_TAC [LNORM_POS_LE],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!n:num. (g n:real^M->real^1) IN lspace s p") ASSUME_TAC THENL
     [GEN_TAC THEN EXPAND_TAC "g" THEN REWRITE_TAC [] THEN
      MATCH_MP_TAC LSPACE_VSUM THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC, REWRITE_TAC [FINITE_NUMSEG]] THEN
      ASM_SIMP_TAC [LSPACE_NORM, ETA_AX],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!n:num x:real^M. &0 <= drop(g n x)") ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN EXPAND_TAC "g" THEN
      SIMP_TAC [DROP_VSUM, FINITE_NUMSEG, LIFT_DROP] THEN
      MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
      REWRITE_TAC [o_DEF, LIFT_DROP, NORM_POS_LE],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"\i:num x:real^M. lift(drop(g i x) rpow p)", ← q r"s:real^M->bool"]
          BEPPO_LEVI_MONOTONE_CONVERGENCE_INCREASING) THEN
    REWRITE_TAC [LIFT_DROP] THEN ANTS_TAC THENL
     [MATCH_MP_TAC (← TAUT (← q r"b /\ a /\ c ==> a /\ b /\ c")) THEN CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN EXPAND_TAC "g" THEN
        SIMP_TAC [DROP_VSUM, FINITE_NUMSEG] THEN
        MATCH_MP_TAC RPOW_LE2 THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
          REWRITE_TAC [o_DEF, LIFT_DROP, NORM_POS_LE],
          SIMP_TAC [SUM_CLAUSES_NUMSEG, LE_0, REAL_LE_ADDR] THEN
          REWRITE_TAC [o_DEF, LIFT_DROP, NORM_POS_LE],
          ASM_REAL_ARITH_TAC],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"!k x. drop((g:num->real^M->real^1) k x) = norm(g k x)")
       (fun th => REWRITE_TAC [th])
      THENL
       [REPEAT GEN_TAC THEN REWRITE_TAC [NORM_REAL, ← GSYM drop] THEN
        ASM_REWRITE_TAC [real_abs],
        ALL_TAC] THEN
      ASM_SIMP_TAC [LSPACE_IMP_INTEGRABLE, ETA_AX] THEN
      REWRITE_TAC [bounded] THEN EXISTS_TAC (← q r"M rpow p") THEN
        REWRITE_TAC [FORALL_IN_GSPEC] THEN X_GEN_TAC (← q r"n:num") THEN
        DISCH_THEN (K ALL_TAC) THEN
      ASM_SIMP_TAC [INTEGRAL_LNORM_RPOW, ETA_AX,
                    ← REAL_ARITH (← q r"&1 <= p ==> ~(p = &0)")] THEN
      REWRITE_TAC [NORM_LIFT, REAL_ABS_RPOW] THEN
      MATCH_MP_TAC RPOW_LE2 THEN
      ASM_SIMP_TAC [← REAL_ARITH (← q r"&1 <= p ==> &0 <= p")] THEN
      MATCH_MP_TAC (← REAL_ARITH
       (← q r"&0 <= x /\ x <= a ==> &0 <= abs x /\ abs x <= a")) THEN
      ASM_SIMP_TAC [LNORM_POS_LE],
      ALL_TAC] THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"hp:real^M->real^1", ← q r"k:real^M->bool"] THEN
    STRIP_TAC THEN
    ABBREV_TAC (← q r"h:real^M->real^1 = \x. lift(drop(hp x) rpow (inv p))") THEN
    SUBGOAL_THEN
     (← q r"!x. x IN s DIFF k ==> ((\i. g i x) --> ((h:real^M->real^1) x)) sequentially")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"x:real^M") THEN DISCH_TAC THEN
      MP_TAC (← ISPECL
       [← q r"lift o (\x. x rpow (inv p)) o drop",
        ← q r"sequentially", ← q r"\i. lift(drop((g:num->real^M->real^1) i x) rpow p)",
        ← q r"(hp:real^M->real^1) x"]
          LIM_CONTINUOUS_FUNCTION) THEN
      ASM_SIMP_TAC [] THEN ANTS_TAC THENL
       [GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [← GSYM LIFT_DROP] THEN
        REWRITE_TAC [← GSYM REAL_CONTINUOUS_CONTINUOUS_ATREAL] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_AT_RPOW THEN
        REWRITE_TAC [REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC,
        ALL_TAC] THEN
      EXPAND_TAC "h" THEN REWRITE_TAC [o_DEF, LIFT_DROP] THEN
      ASM_SIMP_TAC [RPOW_RPOW, REAL_MUL_RINV,
                    ← REAL_ARITH (← q r"&1 <= p ==> ~(p = &0)")] THEN
      REWRITE_TAC [RPOW_POW, REAL_POW_1, LIFT_DROP, ETA_AX],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!x. x IN s DIFF k ==> summable (:num) (\i. (f:num->real^M->real^N) i x)")
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC SERIES_LIFT_ABSCONV_IMP_CONV THEN
      REWRITE_TAC [summable] THEN EXISTS_TAC (← q r"(h:real^M->real^1) x") THEN
      REWRITE_TAC [sums, INTER_UNIV] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [FUN_EQ_THM]) THEN
      ASM_SIMP_TAC [],
      ALL_TAC] THEN
    REWRITE_TAC [summable] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [SKOLEM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"l:real^M->real^N") THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     (← q r"!n x. x IN s DIFF k
            ==> norm(vsum (0..n) (\i. (f:num->real^M->real^N) i x)) <= drop(h x)")
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MATCH_MP_TAC VSUM_NORM_TRIANGLE THEN
      REWRITE_TAC [FINITE_NUMSEG] THEN
      GEN_REWRITE_TAC LAND_CONV [← GSYM LIFT_DROP] THEN
      SIMP_TAC [LIFT_SUM, FINITE_NUMSEG] THEN
      MATCH_MP_TAC (← ISPEC (← q r"sequentially") LIM_DROP_LBOUND) THEN
      EXISTS_TAC (← q r"\n. vsum (0..n)
                     (\i. lift(norm((f:num->real^M->real^N) i x)))") THEN
      REWRITE_TAC [TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
       [RULE_ASSUM_TAC (REWRITE_RULE [FUN_EQ_THM]) THEN ASM_SIMP_TAC [IN_DIFF],
        REWRITE_TAC [EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC (← q r"n:num") THEN
        X_GEN_TAC (← q r"m:num") THEN DISCH_TAC THEN
        SIMP_TAC [DROP_VSUM, FINITE_NUMSEG, o_DEF, LIFT_DROP] THEN
        MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
        REWRITE_TAC [SUBSET, IN_NUMSEG, NORM_POS_LE, FINITE_NUMSEG] THEN
        UNDISCH_TAC (← q r"n:num <= m") THEN ARITH_TAC],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!x. x IN s DIFF k ==> norm((l:real^M->real^N) x) <= drop(h x)")
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MATCH_MP_TAC (← ISPEC (← q r"sequentially") LIM_NORM_UBOUND) THEN
      EXISTS_TAC (← q r"\n. vsum ((:num) INTER (0..n))
                           (\i. (f:num->real^M->real^N) i x)") THEN
      ASM_SIMP_TAC [IN_DIFF, ← GSYM sums, TRIVIAL_LIMIT_SEQUENTIALLY] THEN
      MATCH_MP_TAC ALWAYS_EVENTUALLY THEN ASM_SIMP_TAC [INTER_UNIV],
      ALL_TAC] THEN
    MATCH_MP_TAC (← TAUT (← q r"a /\ (a ==> b) ==> a /\ b")) THEN CONJ_TAC THENL
     [REWRITE_TAC [lspace, IN_ELIM_THM] THEN
      MATCH_MP_TAC (← TAUT (← q r"a /\ (a ==> b) ==> a /\ b")) THEN CONJ_TAC THENL
       [MATCH_MP_TAC MEASURABLE_ON_LIMIT THEN
        EXISTS_TAC (← q r"\n x. vsum (0..n) (\i. (f:num->real^M->real^N) i x)") THEN
        EXISTS_TAC (← q r"k:real^M->bool") THEN ASM_REWRITE_TAC [] THEN
        ONCE_REWRITE_TAC [← SET_RULE (← q r"0..n = UNIV INTER (0..n)")] THEN
        ASM_REWRITE_TAC [← GSYM sums] THEN GEN_TAC THEN
        REWRITE_TAC [INTER_UNIV] THEN MATCH_MP_TAC MEASURABLE_ON_VSUM THEN
        RULE_ASSUM_TAC (REWRITE_RULE [lspace, IN_ELIM_THM]) THEN
        ASM_REWRITE_TAC [FINITE_NUMSEG],
        DISCH_TAC] THEN
      MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
      EXISTS_TAC
       (← q r"\x. if x IN k then lift(norm(l x:real^N) rpow p)
            else (hp:real^M->real^1) x") THEN
      ASM_SIMP_TAC [MEASURABLE_ON_LIFT_RPOW, MEASURABLE_ON_NORM, ETA_AX,
                    ← REAL_ARITH (← q r"&1 <= p ==> &0 < p")] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC (← q r"(hp:real^M->real^1) integrable_on s") THEN
        MATCH_MP_TAC INTEGRABLE_SPIKE THEN
        EXISTS_TAC (← q r"k:real^M->bool") THEN ASM_SIMP_TAC [IN_DIFF],
        REWRITE_TAC [NORM_LIFT, REAL_ABS_RPOW, REAL_ABS_NORM] THEN
        GEN_TAC THEN DISCH_TAC THEN COND_CASES_TAC THEN
        REWRITE_TAC [LIFT_DROP, REAL_LE_REFL] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC (← q r"drop(h(x:real^M)) rpow p") THEN CONJ_TAC THENL
         [MATCH_MP_TAC RPOW_LE2 THEN ASM_SIMP_TAC [NORM_POS_LE, IN_DIFF] THEN
          ASM_REAL_ARITH_TAC,
          EXPAND_TAC "h" THEN REWRITE_TAC [LIFT_DROP] THEN
          MATCH_MP_TAC (← REAL_ARITH (← q r"x = y pow 1 ==> x <= y")) THEN
          MATCH_MP_TAC EQ_TRANS THEN
          EXISTS_TAC (← q r"drop(hp(x:real^M)) rpow (inv p * p)") THEN CONJ_TAC THENL
           [MATCH_MP_TAC RPOW_RPOW THEN
            MATCH_MP_TAC (← ISPEC (← q r"sequentially") LIM_DROP_LBOUND) THEN
            EXISTS_TAC (← q r"\k. lift(drop((g:num->real^M->real^1) k x) rpow p)") THEN
            ASM_SIMP_TAC [IN_DIFF, TRIVIAL_LIMIT_SEQUENTIALLY] THEN
            ASM_SIMP_TAC [LIFT_DROP, RPOW_POS_LE, EVENTUALLY_TRUE],
            ASM_SIMP_TAC [REAL_MUL_LINV, ← REAL_ARITH (← q r"&1 <= p ==> ~(p = &0)")] THEN
            REWRITE_TAC [RPOW_POW]]]],
      DISCH_TAC] THEN
    SUBGOAL_THEN (← q r"!x:real^M. x IN s DIFF k ==> &0 <= drop(h x)") ASSUME_TAC THENL
     [ASM_MESON_TAC [REAL_LE_TRANS, NORM_POS_LE], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!x:real^M. x IN s DIFF k ==> &0 <= drop(hp x)") ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MATCH_MP_TAC (← ISPEC (← q r"sequentially") LIM_DROP_LBOUND) THEN
      EXISTS_TAC (← q r"\k. lift(drop((g:num->real^M->real^1) k x) rpow p)") THEN
      ASM_SIMP_TAC [TRIVIAL_LIMIT_SEQUENTIALLY, LIFT_DROP, RPOW_POS_LE] THEN
      REWRITE_TAC [EVENTUALLY_TRUE],
      ALL_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"\n x. lift(norm(vsum (0..n) (\i. (f:num->real^M->real^N) i x) - l x)
                      rpow p)",
      ← q r"(\x. vec 0):real^M->real^1",
      ← q r"\x:real^M. &2 rpow p % lift(drop(h x) rpow p)",
      ← q r"s DIFF k:real^M->bool"]
     DOMINATED_CONVERGENCE) THEN
    REWRITE_TAC [lnorm, INTEGRAL_0, REAL_INTEGRAL_0, INTEGRABLE_0] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [X_GEN_TAC (← q r"n:num") THEN
        MATCH_MP_TAC (← REWRITE_RULE [IMP_IMP] INTEGRABLE_SPIKE_SET) THEN
        EXISTS_TAC (← q r"s:real^M->bool") THEN CONJ_TAC THENL
         [FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
            NEGLIGIBLE_SUBSET)) THEN SET_TAC [],
          MATCH_MP_TAC LSPACE_IMP_INTEGRABLE THEN
          MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC [ETA_AX] THEN
          CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
          MATCH_MP_TAC LSPACE_VSUM THEN
          ASM_REWRITE_TAC [FINITE_NUMSEG] THEN ASM_REAL_ARITH_TAC],
        MATCH_MP_TAC INTEGRABLE_CMUL THEN EXPAND_TAC "h" THEN
        REWRITE_TAC [LIFT_DROP] THEN
        MATCH_MP_TAC (← REWRITE_RULE [IMP_IMP] INTEGRABLE_SPIKE) THEN
        EXISTS_TAC (← q r"hp:real^M->real^1") THEN
        EXISTS_TAC (← q r"{}:real^M->bool") THEN
        ASM_SIMP_TAC [DIFF_EMPTY, NEGLIGIBLE_EMPTY, RPOW_RPOW] THEN
        ASM_SIMP_TAC [REAL_MUL_LINV, ← REAL_ARITH (← q r"&1 <= p ==> ~(p = &0)")] THEN
        REWRITE_TAC [LIFT_DROP, RPOW_POW, REAL_POW_1] THEN
        UNDISCH_TAC (← q r"(hp:real^M->real^1) integrable_on s") THEN
        MATCH_MP_TAC INTEGRABLE_SPIKE_SET THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
          NEGLIGIBLE_SUBSET)) THEN SET_TAC [],
        REWRITE_TAC [DROP_CMUL, ← GSYM RPOW_MUL, LIFT_DROP] THEN
        REPEAT STRIP_TAC THEN REWRITE_TAC [NORM_REAL, ← GSYM drop] THEN
        REWRITE_TAC [REAL_ABS_NORM, LIFT_DROP, REAL_ABS_RPOW] THEN
        MATCH_MP_TAC RPOW_LE2 THEN REWRITE_TAC [NORM_POS_LE] THEN
        CONJ_TAC THENL [ALL_TAC, ASM_REAL_ARITH_TAC] THEN
        MATCH_MP_TAC (← NORM_ARITH
         (← q r"norm(x:real^N) <= a /\ norm(y) <= a ==> norm(x - y) <= &2 * a")) THEN
        ASM_SIMP_TAC [],
        X_GEN_TAC (← q r"x:real^M") THEN STRIP_TAC THEN
        MATCH_MP_TAC LIM_NULL_RPOW THEN
        CONJ_TAC THENL [REWRITE_TAC [o_DEF], ASM_REAL_ARITH_TAC] THEN
        REWRITE_TAC [← GSYM LIM_NULL_NORM] THEN REWRITE_TAC [← GSYM LIM_NULL] THEN
        RULE_ASSUM_TAC (REWRITE_RULE [sums, INTER_UNIV]) THEN
        ASM_SIMP_TAC []],
      GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o LAND_CONV o ABS_CONV)
       [← GSYM LIFT_DROP] THEN
      DISCH_THEN (MP_TAC o MATCH_MP
       (← REWRITE_RULE [IMP_CONJ, o_DEF] LIM_NULL_RPOW)) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"inv p:real")) THEN
      ASM_REWRITE_TAC [REAL_LT_INV_EQ] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      REWRITE_TAC [tendsto, DIST_0, NORM_REAL, ← GSYM drop, LIFT_DROP] THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC [] THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] EVENTUALLY_MONO) THEN
      SUBGOAL_THEN
       (← q r"!f:real^M->real^1. integral (s DIFF k) f = integral s f")
      MP_TAC THENL [ALL_TAC, SIMP_TAC [← REAL_ARITH (← q r"abs(x) < e ==> x < e")]] THEN
      GEN_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE_SET THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
        NEGLIGIBLE_SUBSET)) THEN SET_TAC []])

  pure { LSPACE_SUMMABLE_UNIV }

/- ------------------------------------------------------------------------- -/
/- Completeness (Riesz-Fischer), continued.                                  -/
/- (lpspaces.ml 1225-1343)                                                  -/
/- ------------------------------------------------------------------------- -/

structure LSG where
  LSPACE_SUMMABLE : thm
  RIESZ_FISCHER : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupLSG [HolBase] (D : LpSpacesDeps) (BLSA : LSA) (BLSB : LSB) (BLSC : LSC) (BLSF : LSF) : ExceptT String IO LSG := do
  -- @@SCOPE BEGIN
  let { LSPACE_0, LSPACE_ADD, LSPACE_NEG, LSPACE_SUB, LSPACE_VSUM, .. } := BLSA
  let { LNORM_0, LNORM_NEG, LNORM_POS_LE, .. } := BLSB
  let { LNORM_TRIANGLE, .. } := BLSC
  let { LSPACE_SUMMABLE_UNIV, .. } := BLSF
  let { tendsto_real, .. } := D.rza
  let { real_summable, .. } := D.rzc
  let { REAL_SUMMABLE_RESTRICT, .. } := D.rzd
  let { REAL_SUMMABLE_COMPARISON, REAL_SUMMABLE_GP, .. } := D.rze
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, INDUCT_TAC, REAL_ARITH, REAL_RAT_REDUCE_CONV,
        SET_RULE, VECTOR_ARITH, .. } := D.ra.ts.cn.cx.cvx
  let { LE_0, VSUM_DIFFS_ALT, .. } := D.ra.ts.cn.cx.cpx
  let { ADD1, EQ_IMP, ETA_AX, FINITE_NUMSEG, .. } := D.ra.ts.cn.cx.cvx.core1
  let { FUN_EQ_THM, GE, IMP_CONJ, .. } := D.ra.ts.cn.cx.cvx.core2
  let { LE_TRANS, MONO_EXISTS, MONO_FORALL, MONO_IMP, .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_INV_POW, REAL_LT_INV_EQ, REAL_LT_POW2, .. } := D.ra.ts.cn.cx.cvx.core4
  let { REAL_SUB_RZERO, SKOLEM_THM, .. } := D.ra.ts.cn.cx.cvx.core5
  let { REAL_HALF, .. } := D.ra.ts.cn.cx.cvx.misc
  let { VSUM_RESTRICT_SET, .. } := D.ra.ts.cn.cx.cvx.vec4
  let { EVENTUALLY_MONO, EVENTUALLY_SEQUENTIALLY, .. } := D.ra.ts.cn.cx.cvx.met
  let { prove_recursive_functions_exist, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt
  let { num_RECURSION, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qses
  -- @@SCOPE END

  let LSPACE_SUMMABLE ← prove
   r"!f:num->real^M->real^N p s t.
        &1 <= p /\
        (!i. i IN t ==> f i IN lspace s p) /\
        real_summable t (\i. lnorm s p (f i))
        ==> ?g. g IN lspace s p /\
                ((\n. lnorm s p (\x. vsum (t INTER (0..n)) (\i. f i x) - g x))
                 ---> &0) sequentially"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_SUMMABLE_RESTRICT] THEN
    REWRITE_TAC [] THEN STRIP_TAC THEN
    MP_TAC (← ISPECL
      [← q r"(\n:num x. if n IN t then f n x else vec 0):num->real^M->real^N",
       ← q r"p:real", ← q r"s:real^M->bool"] LSPACE_SUMMABLE_UNIV) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC (← q r"i:num") THEN ASM_CASES_TAC (← q r"(i:num) IN t") THEN
        ASM_SIMP_TAC [LSPACE_0, ETA_AX, ← REAL_ARITH (← q r"&1 <= p ==> ~(p = &0)")],
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [real_summable]) THEN
        REWRITE_TAC [real_summable] THEN MATCH_MP_TAC MONO_EXISTS THEN
        GEN_TAC THEN MATCH_MP_TAC EQ_IMP THEN
        AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
        ASM_SIMP_TAC [ETA_AX, LNORM_0, ← REAL_ARITH (← q r"&1 <= p ==> ~(p = &0)")]],
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"g:real^M->real^N") THEN
      ASM_CASES_TAC (← q r"(g:real^M->real^N) IN lspace s p") THEN
      ASM_REWRITE_TAC [tendsto_real] THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC [] THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] EVENTUALLY_MONO) THEN
      X_GEN_TAC (← q r"n:num") THEN REWRITE_TAC [REAL_SUB_RZERO] THEN
      MATCH_MP_TAC (← REAL_ARITH (← q r"&0 <= x /\ x = y ==> x < e ==> abs y < e")) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LNORM_POS_LE THEN MATCH_MP_TAC LSPACE_SUB THEN
        ASM_SIMP_TAC [← REAL_ARITH (← q r"&1 <= p ==> &0 <= p")] THEN
        MATCH_MP_TAC LSPACE_VSUM THEN
        ASM_SIMP_TAC [FINITE_NUMSEG, ← REAL_ARITH (← q r"&1 <= p ==> &0 < p")] THEN
        X_GEN_TAC (← q r"i:num") THEN ASM_CASES_TAC (← q r"(i:num) IN t") THEN
        ASM_SIMP_TAC [ETA_AX, LSPACE_0, ← REAL_ARITH (← q r"&1 <= p ==> ~(p = &0)")],
        AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN
        X_GEN_TAC (← q r"x:real^M") THEN REWRITE_TAC [← GSYM VSUM_RESTRICT_SET] THEN
        REWRITE_TAC [← SET_RULE (← q r"s INTER t = {x | x IN t /\ x IN s}")]]])

  let RIESZ_FISCHER ← prove
   r"!f:num->real^M->real^N p s.
        &1 <= p /\ (!n. (f n) IN lspace s p) /\
        (!e. &0 < e
             ==> ?N. !m n. m >= N /\ n >= N
                           ==> lnorm s p (\x. f m x - f n x) < e)
        ==> ?g. g IN lspace s p /\
                !e. &0 < e
                    ==> ?N. !n. n >= N
                                ==> lnorm s p (\x. f n x - g x) < e"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"?k:num->num.
          (!n. k n < k (SUC n)) /\
          (!n. lnorm s p ((\x. f (k(SUC n)) x - f (k n) x):real^M->real^N)
               < inv(&2 pow n))")
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o GEN (← q r"n:num") o SPEC (← q r"inv(&2 pow n)")) THEN
      REWRITE_TAC [REAL_LT_INV_EQ, REAL_LT_POW2, SKOLEM_THM] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"N:num->num")) THEN
      MP_TAC (← prove_recursive_functions_exist num_RECURSION
       (← q r"k 0 = N 0 /\
        !n. k(SUC n) = MAX (k n + 1) (MAX (N n) (N(SUC n)))")) THEN
      MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [← ARITH_RULE (← q r"n < MAX (n + 1) m")] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
      CONJ_TAC THENL [ARITH_TAC, SPEC_TAC (← q r"n:num", ← q r"n:num")] THEN
      INDUCT_TAC THEN ASM_REWRITE_TAC [] THEN ARITH_TAC,
      ALL_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"\n x. f (k(SUC n)) x - (f:num->real^M->real^N) (k n) x",
      ← q r"p:real", ← q r"s:real^M->bool"] LSPACE_SUMMABLE_UNIV) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC [LSPACE_SUB, ETA_AX, ← REAL_ARITH (← q r"&1 <= p ==> &0 <= p")] THEN
      MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
      EXISTS_TAC (← q r"\n. inv(&2) pow n") THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_SUMMABLE_GP THEN CONV_TAC REAL_RAT_REDUCE_CONV,
        EXISTS_TAC (← q r"0") THEN X_GEN_TAC (← q r"n:num") THEN DISCH_THEN (K ALL_TAC) THEN
        REWRITE_TAC [← GSYM REAL_INV_POW] THEN
        MATCH_MP_TAC (← REAL_ARITH (← q r"&0 <= x /\ x < y ==> abs x <= y")) THEN
        ASM_SIMP_TAC [LNORM_POS_LE, LSPACE_SUB, ETA_AX,
                      ← REAL_ARITH (← q r"&1 <= p ==> &0 <= p")]],
      DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^M->real^N") MP_TAC) THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*")) THEN
      EXISTS_TAC (← q r"\x. (g:real^M->real^N) x + f (k 0:num) x") THEN
      ASM_SIMP_TAC [LSPACE_ADD, ETA_AX, ← REAL_ARITH (← q r"&1 <= p ==> &0 <= p")] THEN
      X_GEN_TAC (← q r"e:real") THEN DISCH_TAC THEN
      REMOVE_THEN "*" (MP_TAC o SPEC (← q r"e / &2")) THEN
      ASM_REWRITE_TAC [REAL_HALF, EVENTUALLY_SEQUENTIALLY] THEN
      REWRITE_TAC [ADD1, VSUM_DIFFS_ALT, LE_0] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"N1:num") (LABEL_TAC "+")) THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"e / &2")) THEN
      ASM_REWRITE_TAC [REAL_HALF, GE] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"N2:num")) THEN
      EXISTS_TAC (← q r"MAX N1 N2") THEN X_GEN_TAC (← q r"n:num") THEN
      REWRITE_TAC [← ARITH_RULE (← q r"MAX N1 N2 <= n <=> N1 <= n /\ N2 <= n")] THEN
      STRIP_TAC THEN REMOVE_THEN "+" (MP_TAC o SPEC (← q r"n:num")) THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [← q r"k(n + 1):num", ← q r"n:num"]) THEN
      ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
       [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"n + 1") THEN
        CONJ_TAC THENL [ASM_ARITH_TAC, SPEC_TAC (← q r"n + 1", ← q r"m:num")] THEN
        INDUCT_TAC THEN REWRITE_TAC [LE_0] THEN
        MATCH_MP_TAC (← ARITH_RULE
         (← q r"m <= k m /\ k m < k(SUC m) ==> SUC m <= k(SUC m)")) THEN
        ASM_REWRITE_TAC [],
        REPEAT DISCH_TAC THEN
        ONCE_REWRITE_TAC [← VECTOR_ARITH
         (← q r"f n x - (g x + f (k 0) x):real^N =
          (f (k (n + 1)) x - f (k 0) x - g x) +
          --(f (k (n + 1)) x - f n x)")] THEN
        W (MP_TAC o PART_MATCH (lhand o rand) LNORM_TRIANGLE o lhand o snd) THEN
        ASM_SIMP_TAC [LSPACE_SUB, LSPACE_NEG, ETA_AX,
                      ← REAL_ARITH (← q r"&1 <= p ==> &0 <= p")] THEN
        MATCH_MP_TAC (← REAL_ARITH
         (← q r"x < e / &2 /\ y < e / &2 ==> z <= x + y ==> z < e")) THEN
        ASM_SIMP_TAC [LNORM_NEG, LSPACE_SUB, ETA_AX,
                      ← REAL_ARITH (← q r"&1 <= p ==> &0 <= p")]]])

  pure { LSPACE_SUMMABLE, RIESZ_FISCHER }

/- ------------------------------------------------------------------------- -/
/- A sort of dominated convergence theorem for L_p spaces.                   -/
/- (lpspaces.ml 1344-1477)                                                  -/
/- ------------------------------------------------------------------------- -/

structure LSH where
  LSPACE_DOMINATED_CONVERGENCE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupLSH [HolBase] (D : LpSpacesDeps) (BLSA : LSA) (BLSB : LSB) : ExceptT String IO LSH := do
  -- @@SCOPE BEGIN
  let { lspace, LSPACE_IMP_INTEGRABLE, LSPACE_SUB, .. } := BLSA
  let { lnorm, .. } := BLSB
  let { TENDSTO_REAL, .. } := D.rza
  let { REAL_CONTINUOUS_CONTINUOUS_ATREAL, .. } := D.rzn
  let { REAL_CONTINUOUS_AT_RPOW, .. } := D.rzr
  let { REAL_ABS_RPOW, RPOW_LE2, RPOW_MUL, RPOW_ZERO, .. } := D.ra.tsab
  let { MEASURABLE_ON_LIMIT, .. } := D.ra.qmeasure
  let { CONTINUOUS_AT_COMPOSE, .. } := D.ra.ts.qtopology
  let { DOMINATED_CONVERGENCE, .. } := D.ra.ts.cn.ms.qintegration1
  let { INTEGRABLE_CMUL, INTEGRABLE_SPIKE_SET, INTEGRAL_0,
        .. } := D.ra.ts.cn.ms.qintegration2
  let { INTEGRAL_SPIKE_SET, NEGLIGIBLE_SUBSET, .. } := D.ra.ts.cn.ms.qintegration3
  let { LIM_CONTINUOUS_FUNCTION, .. } := D.ra.ts.cn.ms.qtopology2
  let { ASM_REAL_ARITH_TAC, NORM_ARITH, SET_TAC, .. } := D.ra.ts.cn.cx.cvx
  let { ETA_AX, .. } := D.ra.ts.cn.cx.cvx.core1
  let { IMP_CONJ, IMP_CONJ_ALT, IN_DIFF, .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_INV_EQ_0, REAL_LE_INV_EQ, REAL_LT_IMP_LE, REAL_LT_IMP_NZ,
        .. } := D.ra.ts.cn.cx.cvx.core4
  let { o_DEF, o_THM, .. } := D.ra.ts.cn.cx.cvx.core6
  let { DROP_VEC, LIFT_CMUL, LIFT_DROP, LIFT_NUM, NORM_0, .. } := D.ra.ts.cn.cx.cvx.vec2
  let { NORM_LIFT, NORM_MUL, NORM_POS_LE, REAL_ABS_NORM, .. } := D.ra.ts.cn.cx.cvx.vec3
  let { VECTOR_SUB_EQ, .. } := D.ra.ts.cn.cx.cvx.vec4
  let { TRIVIAL_LIMIT_SEQUENTIALLY, .. } := D.ra.ts.cn.cx.cvx.met
  let { CONTINUOUS_AT_LIFT_NORM, .. } := D.ra.ts.cn.cx.cvx.top2
  let { ALWAYS_EVENTUALLY, .. } := D.ra.ts.cn.ms.ig.dv.qmetric
  let { LIM_EVENTUALLY, LIM_NORM_UBOUND, LIM_NULL, LIM_TRANSFORM,
        .. } := D.ra.ts.cn.ms.ig.dv.qtopology2
  -- @@SCOPE END

  let LSPACE_DOMINATED_CONVERGENCE ← prove
   r"!f:num->real^M->real^N g h:real^M->real^N s p k.
        &0 < p /\
        (!n. (f n) IN lspace s p) /\ h IN lspace s p /\
        (!n x. x IN s ==> norm(f n x) <= norm(h x)) /\
        negligible k /\
        (!x. x IN s DIFF k ==> ((\n. f n x) --> g(x)) sequentially)
        ==> g IN lspace s p /\
            ((\n. lnorm s p (\x. f n x - g x)) ---> &0) sequentially"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← ISPECL
     [← q r"\n x. lift(norm((f:num->real^M->real^N) n x) rpow p)",
      ← q r"\x. lift(norm((g:real^M->real^N) x) rpow p)",
      ← q r"\x. lift(norm((h:real^M->real^N) x) rpow p)",
      ← q r"s DIFF k:real^M->bool"] DOMINATED_CONVERGENCE) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [X_GEN_TAC (← q r"k:num") THEN
        FIRST_ASSUM (MP_TAC o MATCH_MP LSPACE_IMP_INTEGRABLE o SPEC (← q r"k:num")) THEN
        MATCH_MP_TAC INTEGRABLE_SPIKE_SET THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
            NEGLIGIBLE_SUBSET)) THEN SET_TAC [],
        FIRST_ASSUM (MP_TAC o MATCH_MP LSPACE_IMP_INTEGRABLE) THEN
        MATCH_MP_TAC INTEGRABLE_SPIKE_SET THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
            NEGLIGIBLE_SUBSET)) THEN SET_TAC [],
        MAP_EVERY X_GEN_TAC [← q r"k:num", ← q r"x:real^M"] THEN
        REWRITE_TAC [IN_DIFF] THEN STRIP_TAC THEN
        REWRITE_TAC [NORM_LIFT, REAL_ABS_RPOW, REAL_ABS_NORM, LIFT_DROP] THEN
        MATCH_MP_TAC RPOW_LE2 THEN ASM_SIMP_TAC [NORM_POS_LE, REAL_LT_IMP_LE],
        X_GEN_TAC (← q r"x:real^M") THEN DISCH_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:real^M")) THEN ASM_REWRITE_TAC [] THEN
        DISCH_THEN (MP_TAC o ISPEC
         (← q r"(lift o (\x. x rpow p) o  drop) o (lift o (norm:real^N->real))") o
           MATCH_MP (← REWRITE_RULE [IMP_CONJ_ALT] LIM_CONTINUOUS_FUNCTION)) THEN
        ASM_SIMP_TAC [o_THM, DROP_VEC, RPOW_ZERO, REAL_LT_IMP_NZ, LIFT_NUM] THEN
        REWRITE_TAC [o_THM, LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
        MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
        REWRITE_TAC [CONTINUOUS_AT_LIFT_NORM] THEN
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [← GSYM LIFT_DROP] THEN
        REWRITE_TAC [← GSYM REAL_CONTINUOUS_CONTINUOUS_ATREAL] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_AT_RPOW THEN
        REWRITE_TAC [REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC],
      STRIP_TAC] THEN
    MATCH_MP_TAC (← TAUT (← q r"a /\ (a ==> b) ==> a /\ b")) THEN CONJ_TAC THENL
     [REWRITE_TAC [lspace, IN_ELIM_THM] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MEASURABLE_ON_LIMIT THEN
        EXISTS_TAC (← q r"f:num->real^M->real^N") THEN
        EXISTS_TAC (← q r"k:real^M->bool") THEN ASM_REWRITE_TAC [] THEN
        RULE_ASSUM_TAC (REWRITE_RULE [lspace, IN_ELIM_THM]) THEN ASM_REWRITE_TAC [],
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE
         [← TAUT (← q r"a ==> b ==> c <=> b ==> a ==> c")] INTEGRABLE_SPIKE_SET)) THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
          NEGLIGIBLE_SUBSET)) THEN SET_TAC []],
      DISCH_TAC] THEN
    SUBGOAL_THEN
     (← q r"!x. x IN s DIFF k
          ==> norm((g:real^M->real^N) x) <= norm((h:real^M->real^N) x)")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"x:real^M") THEN STRIP_TAC THEN
      MATCH_MP_TAC (← ISPEC (← q r"sequentially") LIM_NORM_UBOUND) THEN
      EXISTS_TAC (← q r"\n. (f:num->real^M->real^N) n x") THEN
      ASM_SIMP_TAC [TRIVIAL_LIMIT_SEQUENTIALLY] THEN
      MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
      RULE_ASSUM_TAC (REWRITE_RULE [IN_DIFF]) THEN ASM_SIMP_TAC [],
      ALL_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"\n x. lift(norm((f:num->real^M->real^N) n x - g x) rpow p)",
      ← q r"(\x. vec 0):real^M->real^1",
      ← q r"\x. lift(norm(&2 % (h:real^M->real^N) x) rpow p)",
      ← q r"s DIFF k:real^M->bool"] DOMINATED_CONVERGENCE) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [X_GEN_TAC (← q r"k:num") THEN
        SUBGOAL_THEN (← q r"(\x. (f:num->real^M->real^N) k x - g x) IN lspace s p")
        MP_TAC THENL
         [ASM_SIMP_TAC [LSPACE_SUB, REAL_LT_IMP_LE, ETA_AX], ALL_TAC] THEN
        DISCH_THEN (MP_TAC o MATCH_MP LSPACE_IMP_INTEGRABLE) THEN
        REWRITE_TAC [] THEN MATCH_MP_TAC INTEGRABLE_SPIKE_SET THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
            NEGLIGIBLE_SUBSET)) THEN SET_TAC [],
        REWRITE_TAC [NORM_MUL, RPOW_MUL, LIFT_CMUL] THEN
        MATCH_MP_TAC INTEGRABLE_CMUL THEN
        UNDISCH_TAC (← q r"(h:real^M->real^N) IN lspace s p") THEN
        DISCH_THEN (MP_TAC o MATCH_MP LSPACE_IMP_INTEGRABLE) THEN
        MATCH_MP_TAC INTEGRABLE_SPIKE_SET THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
            NEGLIGIBLE_SUBSET)) THEN SET_TAC [],
        MAP_EVERY X_GEN_TAC [← q r"k:num", ← q r"x:real^M"] THEN
        REWRITE_TAC [IN_DIFF] THEN STRIP_TAC THEN
        REWRITE_TAC [NORM_LIFT, REAL_ABS_RPOW, REAL_ABS_NORM, LIFT_DROP] THEN
        MATCH_MP_TAC RPOW_LE2 THEN ASM_SIMP_TAC [NORM_POS_LE, REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC (← NORM_ARITH
          (← q r"norm(x:real^N) <= norm(z) /\ norm(y) <= norm z
           ==> norm(x - y) <= norm(&2 % z:real^N)")) THEN
        ASM_SIMP_TAC [IN_DIFF],
        X_GEN_TAC (← q r"x:real^M") THEN DISCH_TAC THEN
        UNDISCH_TAC
         (← q r"!x. x IN s DIFF k
              ==> ((\n. (f:num->real^M->real^N) n x) --> g x) sequentially") THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"x:real^M")) THEN ASM_REWRITE_TAC [] THEN
        GEN_REWRITE_TAC LAND_CONV [LIM_NULL] THEN
        DISCH_THEN (MP_TAC o ISPEC
         (← q r"(lift o (\x. x rpow p) o  drop) o (lift o (norm:real^N->real))") o
           MATCH_MP (← REWRITE_RULE [IMP_CONJ_ALT] LIM_CONTINUOUS_FUNCTION)) THEN
        ASM_SIMP_TAC [o_THM, DROP_VEC, RPOW_ZERO, REAL_LT_IMP_NZ, LIFT_NUM] THEN
        ASM_SIMP_TAC [NORM_0, RPOW_ZERO, REAL_LT_IMP_NZ, LIFT_DROP, LIFT_NUM] THEN
        DISCH_THEN MATCH_MP_TAC THEN
        MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
        REWRITE_TAC [CONTINUOUS_AT_LIFT_NORM] THEN
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [← GSYM LIFT_DROP] THEN
        REWRITE_TAC [← GSYM REAL_CONTINUOUS_CONTINUOUS_ATREAL] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_AT_RPOW THEN
        REWRITE_TAC [REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC],
      DISCH_THEN (MP_TAC o CONJUNCT2)] THEN
    REWRITE_TAC [INTEGRAL_0, TENDSTO_REAL, lnorm, o_DEF, LIFT_DROP, LIFT_NUM] THEN
    DISCH_THEN (MP_TAC o ISPEC (← q r"lift o (\x. x rpow inv p) o  drop") o
       MATCH_MP (← REWRITE_RULE [IMP_CONJ_ALT] LIM_CONTINUOUS_FUNCTION)) THEN
    ASM_SIMP_TAC [o_THM, DROP_VEC, RPOW_ZERO, REAL_LT_IMP_NZ, LIFT_NUM] THEN
    ASM_SIMP_TAC [REAL_INV_EQ_0, REAL_LT_IMP_NZ, LIFT_NUM] THEN ANTS_TAC THENL
     [GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [← GSYM LIFT_DROP] THEN
      REWRITE_TAC [← GSYM REAL_CONTINUOUS_CONTINUOUS_ATREAL] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_AT_RPOW THEN
      REWRITE_TAC [REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] LIM_TRANSFORM) THEN
    MATCH_MP_TAC LIM_EVENTUALLY THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
    X_GEN_TAC (← q r"k:num") THEN REWRITE_TAC [VECTOR_SUB_EQ] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC INTEGRAL_SPIKE_SET THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
            NEGLIGIBLE_SUBSET)) THEN SET_TAC [])

  pure { LSPACE_DOMINATED_CONVERGENCE }

/- ------------------------------------------------------------------------- -/
/- Approximation of functions in L_p by bounded ones and continuous ones,    -/
/- and (for bounded domain sets) by purely polynomial ones.                  -/
/- (lpspaces.ml 1478-1724)                                                  -/
/- ------------------------------------------------------------------------- -/

structure LSI where
  LSPACE_APPROXIMATE_BOUNDED : thm
  LSPACE_APPROXIMATE_CONTINUOUS : thm
  LSPACE_APPROXIMATE_VECTOR_POLYNOMIAL_FUNCTION : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupLSI [HolBase] (D : LpSpacesDeps) (BLSA : LSA) (BLSB : LSB) (BLSC : LSC) (BLSH : LSH) : ExceptT String IO LSI := do
  -- @@SCOPE BEGIN
  let { lspace, LSPACE_BOUNDED_MEASURABLE, LSPACE_BOUNDED_MEASURABLE_SIMPLE, LSPACE_CONST,
        LSPACE_MAX, LSPACE_MIN, LSPACE_NEG, LSPACE_SUB, .. } := BLSA
  let { LNORM_CONST, LNORM_MONO, LNORM_NEG, .. } := BLSB
  let { LNORM_TRIANGLE, .. } := BLSC
  let { LSPACE_DOMINATED_CONVERGENCE, .. } := BLSH
  let { REALLIM_SEQUENTIALLY, .. } := D.rzb
  let { CONTINUOUS_ON_VECTOR_POLYNOMIAL_FUNCTION, .. } := D.rzbj
  let { STONE_WEIERSTRASS_VECTOR_POLYNOMIAL_FUNCTION, .. } := D.rzbk
  let { RPOW_POS_LE, .. } := D.ra.tsab
  let { INTEGRABLE_IMP_MEASURABLE, lebesgue_measurable, MEASURABLE_IMP_LEBESGUE_MEASURABLE,
        MEASURABLE_INTEGRABLE, measurable_on, MEASURABLE_ON_RESTRICT, MEASURE_POS_LE,
        .. } := D.ra.qmeasure
  let { CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET, MEASURABLE_ON_UNIV,
        .. } := D.ra.ts.qmeasure
  let { CONTINUOUS_IMP_MEASURABLE_ON, .. } := D.ra.ts.cn.qmeasure
  let { NEGLIGIBLE_EMPTY, .. } := D.ra.ts.cn.ms.qintegration3
  let { CONTINUOUS_ON_MIN, .. } := D.ra.ts.cn.ms.qtopology1
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, basic_ss, GEN_SIMPLIFY_CONV, MESON, NORM_ARITH,
        REAL_ARITH, REAL_ARITH_TAC, TOP_DEPTH_SQCONV, VECTOR_ARITH, VECTOR_ARITH_TAC,
        .. } := D.ra.ts.cn.cx.cvx
  let { REAL_SUP_LE_FINITE, .. } := D.ra.ts.cn.ms.ig.qsession
  let { indicator, NORM_BOUND_COMPONENT_LE, .. } := D.ra.ts.cn.ms.ig.qvec
  let { CARD_NUMSEG_1, CART_EQ, DIFF_EMPTY, DIMINDEX_GE_1, EQ_IMP, ETA_AX, FINITE_IMAGE,
        FINITE_NUMSEG, .. } := D.ra.ts.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, FUN_EQ_THM, IMAGE_EQ_EMPTY, IMAGE_SUBSET, IMP_CONJ_ALT, IMP_IMP,
        IN_DIFF, .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_NUMSEG, LAMBDA_BETA, LE_REFL, LEFT_IMP_EXISTS_THM, MONO_EXISTS,
        MONO_FORALL, MONO_IMP, NOT_LT, NUMSEG_EMPTY, REAL_ABS_DIV, REAL_ABS_NUM,
        REAL_ARCH_SIMPLE, .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_LE_LDIV_EQ, REAL_LE_LMUL_EQ, REAL_LE_TRANS, REAL_LET_TRANS, REAL_LT_DIV,
        REAL_LT_IMP_LE, .. } := D.ra.ts.cn.cx.cvx.core4
  let { REAL_OF_NUM_LE, REAL_SUB_RZERO, SUBSET, .. } := D.ra.ts.cn.cx.cvx.core5
  let { SUBSET_UNIV, SUM_BOUND, .. } := D.ra.ts.cn.cx.cvx.core6
  let { REAL_HALF, .. } := D.ra.ts.cn.cx.cvx.misc
  let { NORM_LE_L1, NORM_LIFT, .. } := D.ra.ts.cn.cx.cvx.vec3
  let { VEC_COMPONENT, VECTOR_MUL_COMPONENT, VECTOR_NEG_COMPONENT, VECTOR_NEG_SUB,
        VECTOR_SUB_COMPONENT, .. } := D.ra.ts.cn.cx.cvx.vec4
  let { EVENTUALLY_SEQUENTIALLY, .. } := D.ra.ts.cn.cx.cvx.met
  let { BOUNDED_POS, BOUNDED_SUBSET, .. } := D.ra.ts.cn.cx.cvx.top1
  let { CLOSURE_SUBSET, COMPACT_CLOSURE, COMPACT_CONTINUOUS_IMAGE, COMPACT_IMP_BOUNDED,
        .. } := D.ra.ts.cn.cx.cvx.top2
  let { CONTINUOUS_ON_CONST, CONTINUOUS_ON_SUBSET, .. } := D.ra.ts.cn.cx.cvx.top3
  let { LIM_SEQUENTIALLY, .. } := D.ra.ts.cn.cx.cvx.top4
  let { bounded, .. } := D.ra.ts.cn.cx.cvx.top5
  let { LIM_EVENTUALLY, .. } := D.ra.ts.cn.ms.ig.dv.qtopology2
  let { CONTINUOUS_ON_MAX, .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology1
  let { NORM_LE_COMPONENTWISE, .. } := D.ra.ts.cn.ms.ig.dv.dg.qvec
  -- @@SCOPE END

  let LSPACE_APPROXIMATE_BOUNDED ← prove
   r"!f:real^M->real^N s p e.
        &0 < p /\ measurable s /\ f IN lspace s p /\ &0 < e
        ==> ?g. g IN lspace s p /\
                bounded (IMAGE g s) /\
                lnorm s p (\x. f x - g x) < e"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL
     [← q r"(\n x. (lambda i. max (--(&n)) (min (&n) ((f:real^M->real^N)(x)$i))))
       :num->real^M->real^N",
      ← q r"f:real^M->real^N",
      ← q r"f:real^M->real^N",
      ← q r"s:real^M->bool", ← q r"p:real", ← q r"{}:real^M->bool"]
          LSPACE_DOMINATED_CONVERGENCE) THEN
    ASM_REWRITE_TAC [NEGLIGIBLE_EMPTY] THEN
    MATCH_MP_TAC (← TAUT
     (← q r"b /\ c /\ a /\ (a /\ d ==> e)
      ==> (a /\ b /\ c ==> d) ==> e")) THEN
    REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC NORM_LE_COMPONENTWISE THEN
      SIMP_TAC [LAMBDA_BETA] THEN REAL_ARITH_TAC,
      X_GEN_TAC (← q r"x:real^M") THEN REWRITE_TAC [DIFF_EMPTY] THEN DISCH_TAC THEN
      MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC [EVENTUALLY_SEQUENTIALLY] THEN
      MP_TAC (← ISPEC
        (← q r"sup(IMAGE (\i. abs((f:real^M->real^N) x$i)) (1..dimindex(:N)))")
        REAL_ARCH_SIMPLE) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"N:num") THEN
      SIMP_TAC [REAL_SUP_LE_FINITE, FINITE_NUMSEG, NUMSEG_EMPTY,
                NOT_LT, DIMINDEX_GE_1, FINITE_IMAGE, IMAGE_EQ_EMPTY] THEN
      SIMP_TAC [FORALL_IN_IMAGE, IN_NUMSEG, CART_EQ, LAMBDA_BETA] THEN
      DISCH_TAC THEN X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN
      X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN
      MATCH_MP_TAC (← REAL_ARITH
       (← q r"abs(x) <= n ==> max (--n) (min n x) = x")) THEN
      ASM_MESON_TAC [REAL_OF_NUM_LE, REAL_LE_TRANS],
      X_GEN_TAC (← q r"n:num") THEN
      MP_TAC (← ISPECL
       [← q r"s:real^M->bool", ← q r"p:real", ← q r"vec n:real^N"] LSPACE_CONST) THEN
      ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC (← q r"(f:real^M->real^N) IN lspace s p") THEN
      REWRITE_TAC [IMP_IMP] THEN
      DISCH_THEN (MP_TAC o MATCH_MP (← REWRITE_RULE
       [← TAUT (← q r"a /\ b /\ c ==> d <=> a /\ b ==> c ==> d")] LSPACE_MIN)) THEN
      ASM_REWRITE_TAC [] THEN
      MP_TAC (← ISPECL
       [← q r"s:real^M->bool", ← q r"p:real", ← q r"--vec n:real^N"] LSPACE_CONST) THEN
      ASM_REWRITE_TAC [IMP_IMP] THEN
      DISCH_THEN (MP_TAC o MATCH_MP (← REWRITE_RULE
       [← TAUT (← q r"a /\ b /\ c ==> d <=> a /\ b ==> c ==> d")] LSPACE_MAX)) THEN
      ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC (← MESON [] (← q r"x = y ==> x IN s ==> y IN s")) THEN
      SIMP_TAC [FUN_EQ_THM, CART_EQ, LAMBDA_BETA, VEC_COMPONENT,
                VECTOR_NEG_COMPONENT] THEN REAL_ARITH_TAC,
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      REWRITE_TAC [REALLIM_SEQUENTIALLY] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"e:real")) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"n:num") (MP_TAC o SPEC (← q r"n:num"))) THEN
      REWRITE_TAC [LE_REFL, REAL_SUB_RZERO] THEN DISCH_TAC THEN
      EXISTS_TAC
       (← q r"(\x. (lambda i. max (-- &n) (min (&n) ((f:real^M->real^N) x$i))))
        :real^M->real^N") THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [REWRITE_TAC [bounded, FORALL_IN_IMAGE] THEN
        EXISTS_TAC (← q r"&(dimindex(:N)) * &n") THEN
        X_GEN_TAC (← q r"x:real^M") THEN DISCH_TAC THEN
        W (MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] REAL_LE_TRANS) THEN
        GEN_REWRITE_TAC
          (RAND_CONV o LAND_CONV o RAND_CONV) [← GSYM CARD_NUMSEG_1] THEN
        MATCH_MP_TAC SUM_BOUND THEN
        SIMP_TAC [FINITE_NUMSEG, IN_NUMSEG, LAMBDA_BETA] THEN REAL_ARITH_TAC,
        MATCH_MP_TAC (← REAL_ARITH (← q r"abs(x) < e ==> x < e")) THEN
        ONCE_REWRITE_TAC [← GSYM LNORM_NEG] THEN
        ASM_REWRITE_TAC [VECTOR_NEG_SUB]]])

  let LSPACE_APPROXIMATE_CONTINUOUS ← prove
   r"!f:real^M->real^N s p e.
        &1 <= p /\ measurable s /\ f IN lspace s p /\ &0 < e
        ==> ?g. g continuous_on (:real^M) /\
                g IN lspace s p /\
                lnorm s p (\x. f x - g x) < e"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP (← REAL_ARITH (← q r"&1 <= p ==> &0 < p"))) THEN
    MP_TAC (← ISPECL [← q r"f:real^M->real^N", ← q r"s:real^M->bool", ← q r"p:real",
                      ← q r"e / &2"]
          LSPACE_APPROXIMATE_BOUNDED) THEN
    ASM_REWRITE_TAC [REAL_HALF] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"h:real^M->real^N") STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [BOUNDED_POS]) THEN
    REWRITE_TAC [FORALL_IN_IMAGE] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"B:real") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     (← q r"?k g. negligible k /\
            (!n. g n continuous_on (:real^M)) /\
            (!n x. x IN s ==> norm(g n x:real^N) <= norm(B % vec 1:real^N)) /\
            (!x. x IN (s DIFF k)  ==> ((\n. g n x) --> h x) sequentially)")
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN (← q r"(h:real^M->real^N) measurable_on s") MP_TAC THENL
       [RULE_ASSUM_TAC (REWRITE_RULE [lspace, IN_ELIM_THM]) THEN ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      REWRITE_TAC [measurable_on] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC (← q r"k:real^M->bool") THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"g:num->real^M->real^N") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"(\n x. lambda i. max (--B) (min B (((g n x):real^N)$i))):
                  num->real^M->real^N") THEN
      ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC (← q r"n:num") THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"n:num")) THEN
        MP_TAC (← ISPECL [← q r"(:real^M)", ← q r"(lambda i. B):real^N"]
                  CONTINUOUS_ON_CONST) THEN
        REWRITE_TAC [IMP_IMP] THEN
        DISCH_THEN (MP_TAC o MATCH_MP CONTINUOUS_ON_MIN) THEN
        MP_TAC (← ISPECL [← q r"(:real^M)", ← q r"(lambda i. --B):real^N"]
                  CONTINUOUS_ON_CONST) THEN
        REWRITE_TAC [IMP_IMP] THEN
        DISCH_THEN (MP_TAC o MATCH_MP CONTINUOUS_ON_MAX) THEN
        MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        SIMP_TAC [FUN_EQ_THM, CART_EQ, LAMBDA_BETA],
        REPEAT STRIP_TAC THEN MATCH_MP_TAC NORM_LE_COMPONENTWISE THEN
        SIMP_TAC [LAMBDA_BETA, VEC_COMPONENT, VECTOR_MUL_COMPONENT] THEN
        REAL_ARITH_TAC,
        X_GEN_TAC (← q r"x:real^M") THEN REWRITE_TAC [IN_DIFF] THEN STRIP_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:real^M")) THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [LIM_SEQUENTIALLY] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q r"ee:real") THEN
        MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC [] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"N:num") THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q r"n:num") THEN
        MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC [] THEN
        MATCH_MP_TAC (← NORM_ARITH
         (← q r"norm(c - a:real^N) <= norm(b - a)
          ==> dist(b,a) < ee ==> dist(c,a) < ee")) THEN
        MATCH_MP_TAC NORM_LE_COMPONENTWISE THEN
        SIMP_TAC [LAMBDA_BETA, VECTOR_SUB_COMPONENT] THEN
        X_GEN_TAC (← q r"k:num") THEN STRIP_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:real^M")) THEN ASM_REWRITE_TAC [] THEN
        DISCH_THEN (MP_TAC o MATCH_MP NORM_BOUND_COMPONENT_LE) THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"k:num")) THEN ASM_REWRITE_TAC [] THEN
        REAL_ARITH_TAC],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!n. ((g:num->real^M->real^N) n) IN lspace s p") ASSUME_TAC THENL
     [X_GEN_TAC (← q r"n:num") THEN
      MATCH_MP_TAC (← HolLight.INST_TYPE [(← qty "N", ← qty "P")] LSPACE_BOUNDED_MEASURABLE) THEN
      EXISTS_TAC (← q r"(\x. B % vec 1):real^M->real^N") THEN
      ASM_SIMP_TAC [LSPACE_CONST] THEN
      ONCE_REWRITE_TAC [← GSYM MEASURABLE_ON_UNIV] THEN
      MATCH_MP_TAC (← REWRITE_RULE [lebesgue_measurable, indicator]
          MEASURABLE_ON_RESTRICT) THEN
      ASM_SIMP_TAC [CONTINUOUS_IMP_MEASURABLE_ON, ETA_AX] THEN
      MATCH_MP_TAC INTEGRABLE_IMP_MEASURABLE THEN
      ASM_REWRITE_TAC [← GSYM MEASURABLE_INTEGRABLE],
      ALL_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"g:num->real^M->real^N", ← q r"h:real^M->real^N",
      ← q r"(\x. B % vec 1):real^M->real^N",
      ← q r"s:real^M->bool", ← q r"p:real", ← q r"k:real^M->bool"]
          LSPACE_DOMINATED_CONVERGENCE) THEN
    ASM_SIMP_TAC [LSPACE_CONST] THEN
    REWRITE_TAC [REALLIM_SEQUENTIALLY, REAL_SUB_RZERO] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"e / &2")) THEN ASM_REWRITE_TAC [REAL_HALF] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"n:num") (MP_TAC o SPEC (← q r"n:num"))) THEN
    REWRITE_TAC [LE_REFL] THEN DISCH_TAC THEN
    EXISTS_TAC (← q r"(g:num->real^M->real^N) n") THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN
     (← q r"(\x. f x - (g:num->real^M->real^N) n x) =
      (\x. (f x - h x) + --(g n x - h x))")
    SUBST1_TAC THENL [SIMP_TAC [FUN_EQ_THM] THEN VECTOR_ARITH_TAC, ALL_TAC] THEN
    W (MP_TAC o PART_MATCH (lhand o rand) LNORM_TRIANGLE o lhand o snd) THEN
    ASM_SIMP_TAC [LSPACE_SUB, ETA_AX, REAL_LT_IMP_LE, LSPACE_NEG] THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"y < e / &2 /\ z < e / &2 ==> x <= y + z ==> x < e")) THEN
    ASM_SIMP_TAC [LNORM_NEG, ← REAL_ARITH (← q r"abs x < e ==> x < e")])

  let LSPACE_APPROXIMATE_VECTOR_POLYNOMIAL_FUNCTION ← prove
   r"!f:real^M->real^N s p e.
        &1 <= p /\ bounded s /\ measurable s /\ f IN lspace s p /\ &0 < e
        ==> ?g. vector_polynomial_function g /\
                g IN lspace s p /\
                lnorm s p (\x. f x - g x) < e"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL
     [← q r"f:real^M->real^N", ← q r"s:real^M->bool", ← q r"p:real", ← q r"e / &2"]
          LSPACE_APPROXIMATE_CONTINUOUS) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM, REAL_HALF] THEN
    X_GEN_TAC (← q r"g:real^M->real^N") THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"g:real^M->real^N", ← q r"closure s:real^M->bool",
                      ← q r"e / &2 / (measure(s:real^M->bool) rpow (inv p) + &1)"]
          STONE_WEIERSTRASS_VECTOR_POLYNOMIAL_FUNCTION) THEN
    ASM_REWRITE_TAC [REAL_HALF, COMPACT_CLOSURE] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC [CONTINUOUS_ON_SUBSET, SUBSET_UNIV],
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC [REAL_HALF] THEN
        MATCH_MP_TAC (← REAL_ARITH (← q r"&0 <= x ==> &0 < x + &1")) THEN
        ASM_SIMP_TAC [RPOW_POS_LE, MEASURE_POS_LE]],
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"h:real^M->real^N") THEN
      STRIP_TAC THEN ASM_REWRITE_TAC []] THEN
    MATCH_MP_TAC (← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")) THEN CONJ_TAC THENL
     [MATCH_MP_TAC LSPACE_BOUNDED_MEASURABLE_SIMPLE THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ASM_REWRITE_TAC []] THEN
      ASM_SIMP_TAC [CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET,
                    MEASURABLE_IMP_LEBESGUE_MEASURABLE,
                    CONTINUOUS_ON_VECTOR_POLYNOMIAL_FUNCTION] THEN
      MATCH_MP_TAC BOUNDED_SUBSET THEN
      EXISTS_TAC (← q r"IMAGE (h:real^M->real^N) (closure s)") THEN
      SIMP_TAC [IMAGE_SUBSET, CLOSURE_SUBSET] THEN
      MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_SIMP_TAC [CONTINUOUS_ON_VECTOR_POLYNOMIAL_FUNCTION, COMPACT_CLOSURE],
      DISCH_TAC] THEN
    TRANS_TAC REAL_LET_TRANS
     (← q r"lnorm s p (\x. (f:real^M->real^N) x - g x) +
      lnorm s p (\x. g x - h x)") THEN
    CONJ_TAC THENL
     [W (MP_TAC o PART_MATCH (rand o rand) LNORM_TRIANGLE o rand o snd) THEN
      ASM_SIMP_TAC [LSPACE_SUB, ← REAL_ARITH (← q r"&1 <= p ==> &0 <= p")] THEN
      REWRITE_TAC [← VECTOR_ARITH (← q r"(f - g) + (g - h):real^N = f - h")],
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REAL_ARITH
       (← q r"x < e / &2 ==> y <= e / &2 ==> x + y < e")))] THEN
    TRANS_TAC REAL_LE_TRANS
     (← q r"lnorm (s:real^M->bool) p
            (\x. lift(e / &2 / (measure s rpow inv p + &1)))") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LNORM_MONO THEN EXISTS_TAC (← q r"{}:real^M->bool") THEN
      REWRITE_TAC [NEGLIGIBLE_EMPTY, DIFF_EMPTY] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      ASM_SIMP_TAC [LSPACE_SUB, LSPACE_CONST, ← REAL_ARITH (← q r"&1 <= p ==> &0 <= p"),
                    NORM_LIFT, ← REAL_ARITH (← q r"x < y ==> x <= abs y"),
                    ← REWRITE_RULE [SUBSET] CLOSURE_SUBSET],
      ASM_SIMP_TAC [LNORM_CONST, ← REAL_ARITH (← q r"&1 <= p ==> &0 < p")] THEN
      REWRITE_TAC [NORM_LIFT, REAL_ABS_DIV, REAL_ABS_NUM] THEN
      ASM_SIMP_TAC [← REAL_ARITH
        (← q r"&0 < e ==> x * abs e / &2 / y = (x * e / &2) / y")] THEN
      ASM (fun ths => tactic_of do
          pure (CONV_TAC (← ExceptT.mk (GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV
            (← ExceptT.mk (basic_ss [])) 4 ths))))
       [MEASURE_POS_LE, RPOW_POS_LE, REAL_LE_LDIV_EQ,
        ← REAL_ARITH (← q r"abs x = if &0 < x then x else --x"),
        ← REAL_ARITH (← q r"&0 <= x ==> &0 < x + &1")] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"m * e / &2 <= e / &2 * n <=> e * m <= e * n")] THEN
      ASM_SIMP_TAC [REAL_LE_LMUL_EQ] THEN REAL_ARITH_TAC])

  pure { LSPACE_APPROXIMATE_BOUNDED, LSPACE_APPROXIMATE_CONTINUOUS,
         LSPACE_APPROXIMATE_VECTOR_POLYNOMIAL_FUNCTION }

end HolMultiLib.LpSpaces
