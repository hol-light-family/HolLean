/- File: Hol100/Green.lean
Translation of HOL Light's 100/green.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionMultiLib.Cauchy
import SessionMultiLib.LpSpaces
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Binomial SessionLibrary.Iter SessionLibrary.Permutations SessionLibrary.Wo SessionLibrary.Products SessionLibrary.Floor SessionLibrary.Frag SessionLibrary.Prime SessionLibrary.Card SessionLibrary.Matroids SessionMultiLib.Misc SessionLibrary.GroupTheory SessionMultiLib.Vectors SessionMultiLib.Metric SessionMultiLib.Determinants SessionMultiLib.Homology SessionMultiLib.Topology SessionMultiLib.Convex SessionMultiLib.ComplexAlgebra SessionMultiLib.Complexes SessionMultiLib.Paths SessionMultiLib.Polytope SessionMultiLib.Degree SessionMultiLib.Derivatives SessionMultiLib.Integration SessionMultiLib.Measure SessionMultiLib.Canal SessionMultiLib.Transcendentals SessionMultiLib.RealAnalysis SessionMultiLib.LpSpaces SessionMultiLib.MoreTop SessionMultiLib.Cauchy
namespace Hol100.Green

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def cf (tm : term) : ExceptT String IO thm := ExceptT.mk (COMPLEX_FIELD tm)
private def cr (tm : term) : ExceptT String IO thm := ExceptT.mk (COMPLEX_RING tm)
private def rf (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_FIELD tm)
private def rg (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_RING tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)
private def sr (tm : term) : ExceptT String IO thm := ExceptT.mk (SET_RULE tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)
private def va (tm : term) : ExceptT String IO thm := ExceptT.mk (VECTOR_ARITH tm)

/- ========================================================================= -/
/- Green's theorem for rectifiable Jordan curves via the Cauchy transform.   -/
/-                                                                           -/
/- MAIN RESULT (COMPLEX_GREEN):                                              -/
/-   For f locally C^1 near the curve, g a rectifiable closed path:          -/
/-     (1/2i) path_integral g f                                              -/
/-       = integral_C winding_number(g,z) * dbar(f)(z) dA(z)                 -/
/-                                                                           -/
/- COROLLARIES:                                                              -/
/-   COMPLEX_GREEN_ALT    -- with Cx(Re(winding_number)) (technical form)    -/
/-   COMPLEX_GREEN_INSIDE -- integral restricted to inside(path_image g)     -/
/-   GREEN_THEOREM_CURL   -- real curl form with partial derivatives         -/
/-   GREEN_AREA_ABS       -- orientation-free area via path integral         -/
/-                                                                           -/
/- HIGH-LEVEL PROOF STRATEGY                                                 -/
/-                                                                           -/
/- The approach avoids the usual regularity theory for the Riemann mapping   -/
/- or smoothing/approximation of the boundary curve. Instead, it uses the    -/
/- Cauchy transform (the convolution operator Tf(w) = integral f(z)/(z-w))   -/
/- as a left inverse of the d-bar operator, inspired by Kostya_I's answer:   -/
/-   https://mathoverflow.net/questions/307713                               -/
/- The technique is rooted in the Cauchy transform / dbar framework of       -/
/- Ahlfors, "Lectures on Quasiconformal Mappings" (1966, 2nd ed. 2006),      -/
/- and appears in Bonk's UCLA complex analysis lecture notes, Ch. 20:        -/
/-   https://www.math.ucla.edu/~mbonk/complana.pdf                           -/
/- The key steps are:                                                        -/
/-                                                                           -/
/- 1. POMPEIU FORMULA (CAUCHY_TRANSFORM_INVERTS_DBAR):                       -/
/-    For f in C^1_c(C), integral dbar(f)(z)/(z-w) dA(z) = -pi*f(w).         -/
/-    Proved via polar coordinates and integration by parts.                 -/
/-    See Ahlfors, "Complex Analysis", Ch.5; Bonk, lecture notes, Lemma 20.  -/
/-                                                                           -/
/- 2. FUBINI EXCHANGE (FUBINI_PATH_AREA):                                    -/
/-    Swap the path integral and area integral:                              -/
/-      integral_C (integral_gamma f(z)/(z-w) |dw|) dA(z)                    -/
/-        = integral_gamma (integral_C f(z)/(z-w) dA(z)) |dw|                -/
/-    Uses product-space absolute integrability (Lp estimates + Holder).     -/
/-                                                                           -/
/- 3. SMOOTH EXTENSION (SMOOTH_EXTENSION_FROM_OPEN):                         -/
/-    Given f locally C^1 near the curve, extend to a C^1 function with      -/
/-    compact support on all of C. Uses Hermite cutoff functions composed    -/
/-    with a finite ball cover (Lebesgue number lemma).                      -/
/-                                                                           -/
/- 4. ASSEMBLY (COMPLEX_GREEN_ALT):                                          -/
/-    Combine Pompeiu + Fubini: the path integral of f equals an area        -/
/-    integral of winding_number * dbar(f). The winding number appears       -/
/-    because the Cauchy kernel 1/(z-w) integrated along the path gives      -/
/-    2*pi*i*winding_number(g,w) by definition. The smooth extension step    -/
/-    reduces the local C^1 case to the global C^1 case.                     -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Multivariate/cauchy.ml";;
#eval SessionMultiLib.Cauchy.ensureCauchy

#eval phrase 2
-- needs "Multivariate/lpspaces.ml";;
#eval SessionMultiLib.LpSpaces.ensureLpSpaces

#eval phrase 3
#eval Session.prioritize_real

/- ========================================================================= -/
/- The Wirtinger (d-bar) derivative.                                         -/
/-                                                                           -/
/- For a real-differentiable function f: C -> C with Jacobian J at z:        -/
/-   df/dz-bar = (1/2)(J11 - J22 + i*(J21 + J12))                            -/
/-             = (1/2)(df/dx + i*df/dy)                                      -/
/-                                                                           -/
/- f is holomorphic iff df/dz-bar = 0 (Cauchy-Riemann equations).            -/
/- ========================================================================= -/
/- The d-bar derivative in terms of the Jacobian matrix                      -/

#eval phrase 4
def wirtinger_dbar : thm := keep "wirtinger_dbar" fun _ => new_definition
 [[wirtinger_dbar (f:complex->complex) (z:complex) =
    complex((jacobian f (at z))$1$1 - (jacobian f (at z))$2$2,
            (jacobian f (at z))$2$1 + (jacobian f (at z))$1$2) / Cx(&2)]]
#eval wirtinger_dbar

/- The holomorphic Wirtinger derivative df/dz                                -/

#eval phrase 5
def wirtinger_dz : thm := keep "wirtinger_dz" fun _ => new_definition
 [[wirtinger_dz (f:complex->complex) (z:complex) =
    complex((jacobian f (at z))$1$1 + (jacobian f (at z))$2$2,
            (jacobian f (at z))$2$1 - (jacobian f (at z))$1$2) / Cx(&2)]]
#eval wirtinger_dz

/- ------------------------------------------------------------------------- -/
/- Key property: wirtinger_dbar = 0 iff f is holomorphic.                    -/
/- This is exactly the Cauchy-Riemann equations.                             -/
/- ------------------------------------------------------------------------- -/

#eval phrase 6
def WIRTINGER_DBAR_EQ_ZERO : thm := keep "WIRTINGER_DBAR_EQ_ZERO" fun _ => (do
  prove ([[!f z. f differentiable (at z)
         ==> (wirtinger_dbar f z = Cx(&0) <=>
              f complex_differentiable (at z))]])
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [wirtinger_dbar, COMPLEX_EQ, RE_DIV_CX, IM_DIV_CX, RE, IM,
                RE_CX, IM_CX] THEN
    REWRITE_TAC [CAUCHY_RIEMANN] THEN
    ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval WIRTINGER_DBAR_EQ_ZERO

/- ------------------------------------------------------------------------- -/
/- When f is holomorphic, wirtinger_dz agrees with complex_derivative.       -/
/- ------------------------------------------------------------------------- -/

#eval phrase 7
def WIRTINGER_DZ_COMPLEX_DERIVATIVE : thm := keep "WIRTINGER_DZ_COMPLEX_DERIVATIVE" fun _ => (do
  prove ([[!f z. f complex_differentiable (at z)
         ==> wirtinger_dz f z = complex_derivative f z]])
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP COMPLEX_DERIVATIVE_JACOBIAN) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o
      HolLight.GEN_REWRITE_RULE HolCore.Lib.I [CAUCHY_RIEMANN]) THEN
    REWRITE_TAC [wirtinger_dz] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC [COMPLEX_EQ, RE_DIV_CX, IM_DIV_CX, RE, IM] THEN
    REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval WIRTINGER_DZ_COMPLEX_DERIVATIVE

/- ------------------------------------------------------------------------- -/
/- The Jacobian can be recovered from wirtinger_dz and wirtinger_dbar.       -/
/- This is the real content: the Jacobian acts as                            -/
/-   J(h) = dz(f) * h + dbar(f) * cnj(h)                                     -/
/- which connects the real derivative to the Wirtinger operators.            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 8
def FRECHET_WIRTINGER : thm := keep "FRECHET_WIRTINGER" fun _ => (do
  prove ([[!f f' z. (f has_derivative f') (at z)
            ==> !h:complex. f'(h) =
                    wirtinger_dz f z * h + wirtinger_dbar f z * cnj h]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[(f:complex->complex) differentiable (at z)]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [differentiable], ALL_TAC] THEN
    SUBGOAL_THEN ([[f' = (\h:complex. jacobian (f:complex->complex) (at z) ** h)]]) SUBST1_TAC THENL
     [MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
      EXISTS_TAC ([[f:complex->complex]]) THEN
      EXISTS_TAC ([[z:complex]]) THEN
      ASM_REWRITE_TAC [(← HolLight.GSYM JACOBIAN_WORKS)],
      ALL_TAC] THEN
    REWRITE_TAC [wirtinger_dz, wirtinger_dbar] THEN
    REWRITE_TAC [COMPLEX_EQ] THEN
    REWRITE_TAC [cnj, complex_mul, complex_add, RE, IM,
                RE_DIV_CX, IM_DIV_CX,
                matrix_vector_mul, DIMINDEX_2, SUM_2] THEN
    REWRITE_TAC [RE_DEF, IM_DEF] THEN
    SIMP_TAC [LAMBDA_BETA, DIMINDEX_2, ARITH] THEN
    REWRITE_TAC [(← HolLight.GSYM RE_DEF), (← HolLight.GSYM IM_DEF)] THEN
    REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval FRECHET_WIRTINGER

/- ------------------------------------------------------------------------- -/
/- Wirtinger d-bar of z-bar is 1 (conjugation).                              -/
/- This is a key test: d/dz-bar(z-bar) = 1.                                  -/
/- We need the Jacobian of the conjugation function.                         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 9
def HAS_DERIVATIVE_CNJ : thm := keep "HAS_DERIVATIVE_CNJ" fun _ => (do
  prove ([[!z. (cnj has_derivative cnj) (at z)]])
   (GEN_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    REWRITE_TAC [LINEAR_CNJ])
  : ExceptT String IO thm).run
#eval HAS_DERIVATIVE_CNJ

/- ------------------------------------------------------------------------- -/
/- Wirtinger d-bar of specific simple functions.                             -/
/- We compute d-bar(z-bar) = 1, which is needed for the area formula.        -/
/- This requires computing the Jacobian of conjugation.                      -/
/- ------------------------------------------------------------------------- -/
/- Jacobian of conjugation: cnj(x + iy) = x - iy, so J = [[1,0],[0,-1]]      -/

#eval phrase 10
def JACOBIAN_CNJ : thm := keep "JACOBIAN_CNJ" fun _ => (do
  prove ([[!z. jacobian cnj (at z) = (vector[vector[&1;&0]; vector[&0;-- &1] ]:real^2^2)]])
   (GEN_TAC THEN REWRITE_TAC [jacobian] THEN
    SUBGOAL_THEN ([[frechet_derivative cnj (at z) = cnj]]) SUBST1_TAC THENL
     [MATCH_MP_TAC HAS_FRECHET_DERIVATIVE_UNIQUE_AT THEN
      REWRITE_TAC [HAS_DERIVATIVE_CNJ], ALL_TAC] THEN
    SUBGOAL_THEN ([[cnj = (\x:complex.
       (vector[vector[&1;&0]; vector[&0;-- &1] ]:real^2^2) ** x)]]) SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC ([[w:complex]]) THEN
      REWRITE_TAC [COMPLEX_EQ] THEN
      REWRITE_TAC [cnj, matrix_vector_mul, DIMINDEX_2, SUM_2] THEN
      REWRITE_TAC [RE_DEF, IM_DEF] THEN
      SIMP_TAC [LAMBDA_BETA, DIMINDEX_2, ARITH, VECTOR_2] THEN
      REWRITE_TAC [(← HolLight.GSYM RE_DEF), (← HolLight.GSYM IM_DEF), RE, IM] THEN
      REAL_ARITH_TAC2,
      REWRITE_TAC [MATRIX_OF_MATRIX_VECTOR_MUL]])
  : ExceptT String IO thm).run
#eval JACOBIAN_CNJ

#eval phrase 11
def WIRTINGER_DBAR_CNJ : thm := keep "WIRTINGER_DBAR_CNJ" fun _ => (do
  prove ([[wirtinger_dbar cnj = \z. Cx(&1)]])
   (REWRITE_TAC [FUN_EQ_THM, wirtinger_dbar, JACOBIAN_CNJ, VECTOR_2] THEN
    REWRITE_TAC [CX_DEF] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC [complex_div, COMPLEX_EQ, RE, IM, complex_mul,
                complex_inv, RE_CX, IM_CX] THEN
    REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval WIRTINGER_DBAR_CNJ

#eval phrase 12
def WIRTINGER_DBAR_I : thm := keep "WIRTINGER_DBAR_I" fun _ => (do
  prove ([[wirtinger_dbar I = \z. Cx(&0)]])
   (SIMP_TAC [I_DEF, FUN_EQ_THM, DIFFERENTIABLE_ID, WIRTINGER_DBAR_EQ_ZERO,
             COMPLEX_DIFFERENTIABLE_ID])
  : ExceptT String IO thm).run
#eval WIRTINGER_DBAR_I

/- ------------------------------------------------------------------------- -/
/- Wirtinger d-bar is continuous when the Jacobian is continuous.            -/
/- This is needed for the Fubini step in the Gauss-Green proof.              -/
/- ------------------------------------------------------------------------- -/

#eval phrase 13
def WIRTINGER_DBAR_FRECHET : thm := keep "WIRTINGER_DBAR_FRECHET" fun _ => (do
  prove ([[!f:complex->complex z.
        wirtinger_dbar f z =
        (frechet_derivative f (at z) (Cx(&1)) +
         ii * frechet_derivative f (at z) ii) / Cx(&2)]])
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [wirtinger_dbar, jacobian, COMPLEX_EQ] THEN
    REWRITE_TAC [complex_add, complex_mul, RE, IM,
                RE_DIV_CX, IM_DIV_CX, ii, CX_DEF, complex] THEN
    REWRITE_TAC [RE_DEF, IM_DEF] THEN
    SIMP_TAC [MATRIX_COMPONENT, DIMINDEX_2, ARITH] THEN
    SIMP_TAC [LAMBDA_BETA, DIMINDEX_2, ARITH, VECTOR_2] THEN
    REWRITE_TAC [COMPLEX_BASIS] THEN
    REWRITE_TAC [(← HolLight.GSYM RE_DEF), (← HolLight.GSYM IM_DEF), ii, CX_DEF, complex] THEN
    REWRITE_TAC [RE_DEF, IM_DEF] THEN
    SIMP_TAC [VECTOR_2, LAMBDA_BETA, DIMINDEX_2, ARITH] THEN
    REWRITE_TAC [(← HolLight.GSYM RE_DEF), (← HolLight.GSYM IM_DEF)] THEN
    REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval WIRTINGER_DBAR_FRECHET

#eval phrase 14
def WIRTINGER_DBAR_CONTINUOUS : thm := keep "WIRTINGER_DBAR_CONTINUOUS" fun _ => (do
  prove ([[!f:complex->complex s.
        (!h. (\z. frechet_derivative f (at z) h) continuous_on s)
        ==> (\z. wirtinger_dbar f z) continuous_on s]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [WIRTINGER_DBAR_FRECHET] THEN
    REWRITE_TAC [complex_div] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_RMUL THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[Cx(&1)]])) THEN REWRITE_TAC [],
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[ii]])) THEN REWRITE_TAC []])
  : ExceptT String IO thm).run
#eval WIRTINGER_DBAR_CONTINUOUS

/- Wirtinger d-bar has bounded support when f does                           -/

#eval phrase 15
def WIRTINGER_DBAR_BOUNDED_SUPPORT : thm := keep "WIRTINGER_DBAR_BOUNDED_SUPPORT" fun _ => (do
  prove ([[!f:complex->complex.
        f differentiable_on (:complex) /\
        bounded (support (+) f (:complex))
        ==> bounded (support (+) (wirtinger_dbar f) (:complex))]])
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC ([[closure(support (+) (f:complex->complex) (:complex))]]) THEN
    ASM_SIMP_TAC [BOUNDED_CLOSURE] THEN
    REWRITE_TAC [SUBSET] THEN X_GEN_TAC ([[z:complex]]) THEN
    REWRITE_TAC [IN_SUPPORT, IN_UNIV, NEUTRAL_VECTOR_ADD] THEN
    DISCH_TAC THEN
    REWRITE_TAC [CLOSURE_APPROACHABLE] THEN
    X_GEN_TAC ([[e:real]]) THEN DISCH_TAC THEN
    ASM_CASES_TAC ([[?y:complex. y IN support (+) (f:complex->complex) (:complex) /\
                 dist(z,y) < e]]) THENL
     [ASM_MESON_TAC [SessionMultiLib.Vectors.DIST_SYM], ALL_TAC] THEN
    SUBGOAL_THEN ([[!y:complex. dist(y,z) < e ==> (f:complex->complex) y = vec 0]]) ASSUME_TAC THENL
     [X_GEN_TAC ([[y:complex]]) THEN DISCH_TAC THEN
      UNDISCH_TAC ([[~(?y:complex. y IN support (+) (f:complex->complex) (:complex) /\
                     dist(z:complex,y) < e)]]) THEN
      REWRITE_TAC [NOT_EXISTS_THM, DE_MORGAN_THM,
                  IN_SUPPORT, IN_UNIV, NEUTRAL_VECTOR_ADD, REAL_NOT_LT] THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC ([[y:complex]])) THEN
      ASM_MESON_TAC [SessionMultiLib.Vectors.DIST_SYM, REAL_NOT_LE], ALL_TAC] THEN
    SUBGOAL_THEN ([[frechet_derivative (f:complex->complex) (at z) = (\h. vec 0)]]) ASSUME_TAC THENL
     [MATCH_MP_TAC HAS_FRECHET_DERIVATIVE_UNIQUE_AT THEN
      MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
      MAP_EVERY EXISTS_TAC [([[(\x:complex. vec 0):complex->complex]]), ([[e:real]])] THEN
      ASM_REWRITE_TAC [HAS_DERIVATIVE_CONST] THEN
      GEN_TAC THEN DISCH_TAC THEN CONV_TAC HolLight.SYM_CONV THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    UNDISCH_TAC ([[~(wirtinger_dbar (f:complex->complex) z = vec 0)]]) THEN
    REWRITE_TAC [WIRTINGER_DBAR_FRECHET] THEN
    ASM_REWRITE_TAC [COMPLEX_VEC_0, COMPLEX_MUL_RZERO] THEN
    REWRITE_TAC [COMPLEX_ADD_LID, complex_div, COMPLEX_MUL_LZERO])
  : ExceptT String IO thm).run
#eval WIRTINGER_DBAR_BOUNDED_SUPPORT

/- ========================================================================= -/
/- The Cauchy transform inverts the d-bar operator (Pompeiu formula).        -/
/-                                                                           -/
/- The Cauchy transform of g is Tg(w) = (1/pi) int g(z)/(z-w) dA(z).         -/
/- For f in C^1_c(C), T(dbar f) = -f, or equivalently:                       -/
/-   integral (dbar f)(z) / (z - w) dA(z) = -pi * f(w)                       -/
/-                                                                           -/
/- This is the key identity CAUCHY_TRANSFORM_INVERTS_DBAR below.             -/
/- See Ahlfors, "Complex Analysis" Ch.4 Sec.6; Bonk, lecture notes,          -/
/- Lemma 20.2; Ahlfors QC Ch.5.                                              -/
/-                                                                           -/
/- Proof approach: polar coordinates centered at w, integration by parts.    -/
/- We state the theorem with explicit hypotheses rather than defining        -/
/- the Cauchy transform or C^1_c as HOL Light constants.                     -/
/- ========================================================================= -/
/- ----- Proof sketch for CAUCHY_TRANSFORM_INVERTS_DBAR -----                -/
/-                                                                           -/
/- Let g(r,t) = f(w + r * exp(i*t)). Then:                                   -/
/-   (dbar f)(w + r*exp(it)) = exp(it)/2 * [dg/dr + (i/r)*dg/dt]             -/
/-                                                                           -/
/- The integrand (dbar f)(z) / (z - w) in polar becomes:                     -/
/-   (dbar f)(w + r*exp(it)) * exp(-it)/r * r  [Jacobian = r]                -/
/-   = (dbar f)(w + r*exp(it)) * exp(-it)                                    -/
/-   = (1/2) * [dg/dr + (i/r)*dg/dt]                                         -/
/-                                                                           -/
/- After Fubini (r from 0 to R, t from 0 to 2*pi):                           -/
/-   integral = (1/2) int_0^{2pi} int_0^R dg/dr dr dt                        -/
/-            + (i/2) int_0^R (1/r) int_0^{2pi} dg/dt dt dr                  -/
/-                                                                           -/
/- Radial part: by FTC, int_0^R dg/dr dr = g(R,t) - g(0,t)                   -/
/-   = 0 - f(w) = -f(w) for large R (compact support).                       -/
/-   Hence = (1/2) * 2*pi * (-f(w)) = -pi * f(w).                            -/
/-                                                                           -/
/- Angular part: int_0^{2pi} dg/dt dt = g(r,2pi) - g(r,0) = 0                -/
/-   (periodicity of exp). So this part = 0.                                 -/
/-                                                                           -/
/- Total: -pi * f(w). QED.                                                   -/
/- Sub-lemma: translation reduces to w = 0                                   -/

#eval phrase 16
def CAUCHY_TRANSFORM_DBAR_TRANSLATION : thm := keep "CAUCHY_TRANSFORM_DBAR_TRANSLATION" fun _ => (do
  let h1 ← va (← ExceptT.mk [[(w + x) - w:complex = x]])
  prove ([[!f:complex->complex w.
        integral (:complex) (\z. wirtinger_dbar f z / (z - w)) =
        integral (:complex) (\z. wirtinger_dbar f (w + z) / z)]])
   (REPEAT GEN_TAC THEN
    MP_TAC (← HolLight.ISPEC ([[w:complex]]) TRANSLATION_UNIV) THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [(← HolLight.SYM th)])) THEN
    REWRITE_TAC [(← HolLight.GSYM INTEGRAL_TRANSLATION)] THEN
    REWRITE_TAC [h1])
  : ExceptT String IO thm).run
#eval CAUCHY_TRANSFORM_DBAR_TRANSLATION

/- Helper lemmas for the polar coordinates proof                             -/

#eval phrase 17
def CONTINUOUS_ON_TRANSLATE_UNIV : thm := keep "CONTINUOUS_ON_TRANSLATE_UNIV" fun _ => (do
  prove ([[!f:complex->complex a.
        f continuous_on (:complex)
        ==> (\z. f(a + z)) continuous_on (:complex)]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[(\z:complex. (f:complex->complex)(a + z)) =
     (f:complex->complex) o (\z:complex. a + z)]]) SUBST1_TAC THENL
     [REWRITE_TAC [o_DEF], ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
      REWRITE_TAC [CONTINUOUS_ON_CONST, CONTINUOUS_ON_ID],
      FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN REWRITE_TAC [SUBSET_UNIV]])
  : ExceptT String IO thm).run
#eval CONTINUOUS_ON_TRANSLATE_UNIV

#eval phrase 18
def BOUNDED_SUPPORT_TRANSLATE : thm := keep "BOUNDED_SUPPORT_TRANSLATE" fun _ => (do
  let h1 ← va (← ExceptT.mk [[--a + a + z:complex = z]])
  prove ([[!f:complex->complex a.
        bounded (support (+) f (:complex))
        ==> bounded (support (+) (\z. f(a + z)) (:complex))]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[support (+) (\z:complex. (f:complex->complex)(a + z)) (:complex) SUBSET
     IMAGE (\z. --a + z) (support (+) f (:complex))]]) ASSUME_TAC THENL
     [REWRITE_TAC [SUBSET, IN_SUPPORT, IN_UNIV, IN_IMAGE] THEN
      X_GEN_TAC ([[z:complex]]) THEN STRIP_TAC THEN
      EXISTS_TAC ([[a + z:complex]]) THEN
      ASM_REWRITE_TAC [h1,
                      NEUTRAL_VECTOR_ADD] THEN
      REWRITE_TAC [IN_SUPPORT, IN_UNIV] THEN
      ASM_REWRITE_TAC [NEUTRAL_VECTOR_ADD],
      ALL_TAC] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC ([[IMAGE (\z:complex. --a + z)
                (support (+) (f:complex->complex) (:complex))]]) THEN
    ASM_SIMP_TAC [BOUNDED_TRANSLATION])
  : ExceptT String IO thm).run
#eval BOUNDED_SUPPORT_TRANSLATE

#eval phrase 19
def POLAR_SIMPLIFY : thm := keep "POLAR_SIMPLIFY" fun _ => (do
  prove ([[!g:complex (r:real^1) (e:complex).
        &0 < drop r /\ ~(e = Cx(&0))
        ==> drop r % (g / (Cx(drop r) * e)) = g * inv e]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [COMPLEX_CMUL] THEN
    SUBGOAL_THEN ([[~(Cx(drop r) = Cx(&0))]]) ASSUME_TAC THENL
     [REWRITE_TAC [CX_INJ] THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [complex_div, COMPLEX_INV_MUL] THEN
    SUBGOAL_THEN ([[Cx(drop r) * (g * (inv(Cx(drop r)) * inv e)) =
                (Cx(drop r) * inv(Cx(drop r))) * (g * inv e)]]) SUBST1_TAC THENL
     [SIMPLE_COMPLEX_ARITH_TAC, ALL_TAC] THEN
    ASM_SIMP_TAC [COMPLEX_MUL_RINV, COMPLEX_MUL_LID])
  : ExceptT String IO thm).run
#eval POLAR_SIMPLIFY

#eval phrase 20
def INV_CEXP_II : thm := keep "INV_CEXP_II" fun _ => (do
  prove ([[!t. inv(cexp(ii * Cx t)) = cnj(cexp(ii * Cx t))]])
   (GEN_TAC THEN REWRITE_TAC [CNJ_CEXP] THEN
    CONV_TAC HolLight.SYM_CONV THEN REWRITE_TAC [(← HolLight.GSYM CEXP_NEG)] THEN
    AP_TERM_TAC THEN
    REWRITE_TAC [cnj, ii, CX_DEF, complex_mul, complex_neg,
                RE, IM, COMPLEX_EQ] THEN
    REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval INV_CEXP_II

#eval phrase 21
def POLAR_CEXP_SIMPLIFY : thm := keep "POLAR_CEXP_SIMPLIFY" fun _ => (do
  prove ([[!g:complex (r:real^1) t.
        &0 < drop r
        ==> drop r % (g / (Cx(drop r) * cexp(ii * Cx(drop t)))) =
            g * cnj(cexp(ii * Cx(drop t)))]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[~(cexp(ii * Cx(drop t)) = Cx(&0))]]) ASSUME_TAC THENL
     [REWRITE_TAC [CEXP_NZ], ALL_TAC] THEN
    ASM_SIMP_TAC [POLAR_SIMPLIFY] THEN
    REWRITE_TAC [INV_CEXP_II])
  : ExceptT String IO thm).run
#eval POLAR_CEXP_SIMPLIFY

#eval phrase 22
def WIRTINGER_DBAR_FRECHET_POLAR : thm := keep "WIRTINGER_DBAR_FRECHET_POLAR" fun _ => (do
  prove ([[!f:complex->complex z e.
        f differentiable at z
        ==> frechet_derivative f (at z) e +
            ii * frechet_derivative f (at z) (ii * e) =
            Cx(&2) * wirtinger_dbar f z * cnj e]])
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.REWRITE_RULE [differentiable]) THEN
    DISCH_THEN (X_CHOOSE_TAC ([[f':complex->complex]])) THEN
    MP_TAC (← HolLight.ISPECL [([[f:complex->complex]]), ([[f':complex->complex]]), ([[z:complex]])] FRECHET_WIRTINGER) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[f' = frechet_derivative (f:complex->complex) (at z)]]) SUBST_ALL_TAC THENL
     [MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [CNJ_MUL, CNJ_II] THEN
    CONV_TAC cr)
  : ExceptT String IO thm).run
#eval WIRTINGER_DBAR_FRECHET_POLAR

#eval phrase 23
def CEXP_2PII : thm := keep "CEXP_2PII" fun _ => (do
  prove ([[cexp(ii * Cx(&2 * pi)) = Cx(&1)]])
   (MP_TAC (← HolLight.SPEC ([[&1]]) CEXP_INTEGER_2PI) THEN
    REWRITE_TAC [INTEGER_CLOSED, REAL_MUL_LID, COMPLEX_MUL_SYM])
  : ExceptT String IO thm).run
#eval CEXP_2PII

#eval phrase 24
def CEXP_0II : thm := keep "CEXP_0II" fun _ => (do
  prove ([[cexp(ii * Cx(&0)) = Cx(&1)]])
   (REWRITE_TAC [COMPLEX_MUL_RZERO, CEXP_0])
  : ExceptT String IO thm).run
#eval CEXP_0II

/- ========================================================================= -/
/- Absolutely integrable cpow.                                               -/
/- Uses polar Fubini to show (z - w) cpow p is integrable on bounded sets    -/
/- for Re p > -2.                                                            -/
/- ========================================================================= -/

#eval phrase 25
def NORM_CPOW_COMPLEX : thm := keep "NORM_CPOW_COMPLEX" fun _ => (do
  prove ([[!w z. real z
         ==> norm(w cpow z) =
             if w = Cx(&0) /\ z = Cx(&0) then &0 else norm(w) rpow (Re z)]])
   (X_GEN_TAC ([[w:complex]]) THEN
    REWRITE_TAC [FORALL_REAL, RE_CX, CX_INJ] THEN X_GEN_TAC ([[r:real]]) THEN
    REWRITE_TAC [cpow] THEN ASM_CASES_TAC ([[w = Cx(&0)]]) THEN
    ASM_SIMP_TAC [COMPLEX_NORM_0, RPOW_ZERO, COND_ID] THEN
    ASM_SIMP_TAC [NORM_CEXP, RE_MUL_CX, RE_CLOG] THEN
    ASM_REWRITE_TAC [rpow, NORM_POS_LT, NORM_EQ_0, COMPLEX_VEC_0])
  : ExceptT String IO thm).run
#eval NORM_CPOW_COMPLEX

#eval phrase 26
def ABSOLUTELY_INTEGRABLE_CPOW : thm := keep "ABSOLUTELY_INTEGRABLE_CPOW" fun _ => (do
  let h6 ← rr (← ExceptT.mk [[(p + &2) - &1:real = p + &1]])
  let h5 ← rr (← ExceptT.mk [[&0 <= x /\ abs x <= a <=> &0 <= x /\ x <= a]])
  let h4 ← sr (← ExceptT.mk [[(\x. P x) INTER {x | Q x} = {x | Q x /\ P x}]])
  let h3 ← sr (← ExceptT.mk [[{x | x IN s /\ ~(x = a)} = s DELETE a]])
  let h2 ← cr (← ExceptT.mk [[(w + y) - (w + Cx(&0)) = y]])
  let h1 ← cr (← ExceptT.mk [[w = w + Cx(&0)]])
  prove ([[!s p w.
        bounded s /\ measurable s /\ real p /\ --(&2) < Re p
        ==> (\z. (z - w) cpow p) absolutely_integrable_on s]])
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_REAL] THEN
    GEN_TAC THEN REPEAT DISCH_TAC THEN X_GEN_TAC ([[p:real]]) THEN
    REWRITE_TAC [RE_CX] THEN DISCH_TAC THEN X_GEN_TAC ([[w:complex]]) THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[w:complex]]) o HolLight.MATCH_MP BOUNDED_SUBSET_CBALL) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[r:real]]) STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC ([[cball(w:complex,r)]]) THEN
    ASM_SIMP_TAC [MEASURABLE_IMP_LEBESGUE_MEASURABLE] THEN
    REPEAT (FIRST_X_ASSUM (fun (th : thm) => HolLight.tactic_of do
        let q ← ExceptT.mk [[s:complex->bool]]
        pure (if HolCore.Basics.free_in q (concl th) then ALL_TAC else FAIL_TAC "check"))) THEN
    SUBST1_TAC h1 THEN
    REWRITE_TAC [(← HolLight.GSYM ABSOLUTELY_INTEGRABLE_TRANSLATION), CBALL_TRANSLATION] THEN
    REWRITE_TAC [h2] THEN
    ONCE_REWRITE_TAC [ABSOLUTELY_INTEGRABLE_MEASURABLE] THEN
    ASM_SIMP_TAC [MEASURABLE_ON_CPOW, LEBESGUE_MEASURABLE_CBALL] THEN
    SIMP_TAC [NORM_CPOW_COMPLEX, REAL_CX, CX_INJ, RE_CX] THEN
    ASM_CASES_TAC ([[p:real = &0]]) THEN ASM_REWRITE_TAC [] THENL
     [REWRITE_TAC [RPOW_0, COND_RAND, LIFT_NUM] THEN
      MATCH_MP_TAC INTEGRABLE_CASES THEN REWRITE_TAC [INTEGRABLE_ON_CONST] THEN
      REWRITE_TAC [h3] THEN
      REWRITE_TAC [MEASURABLE_DELETE, MEASURABLE_CBALL],
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    GEN_REWRITE_TAC HolCore.Lib.I [(← HolLight.GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV)] THEN
    HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
        let x1 ← ExceptT.mk (HolLight.PART_MATCH (HolCore.Equal.lhand o HolCore.Kernel.rand) FUBINI_TONELLI_POLAR w)
        pure (MP_TAC x1)) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC MEASURABLE_ON_CASES THEN
      REWRITE_TAC [IN_GSPEC, MEASURABLE_ON_CONST] THEN
      REWRITE_TAC [LEBESGUE_MEASURABLE_CBALL] THEN MATCH_MP_TAC CONTINUOUS_AE_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC ([[{Cx(&0)}]]) THEN
      REWRITE_TAC [LEBESGUE_MEASURABLE_UNIV, NEGLIGIBLE_SING] THEN
      SUBGOAL_THEN ([[(\x:complex. lift(norm x rpow p)) =
      (lift o (\x. x rpow p) o drop) o lift o norm]]) SUBST1_TAC THENL [REWRITE_TAC [o_DEF, LIFT_DROP], ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      REWRITE_TAC [CONTINUOUS_ON_LIFT_NORM] THEN
      MP_TAC (← HolLight.SPECL [([[(:real) DELETE (&0)]]), ([[p:real]])] REAL_CONTINUOUS_ON_RPOW) THEN
      REWRITE_TAC [IN_DELETE, REAL_CONTINUOUS_ON] THEN
      MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_CONJ_ALT] CONTINUOUS_ON_SUBSET) THEN
      REWRITE_TAC [IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_DIFF, IN_SING, IN_UNIV,
                  IN_DELETE, COMPLEX_NORM_ZERO],
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC [COND_RAND, COND_RATOR] THEN
    REWRITE_TAC [IN_CBALL_0, (← HolLight.GSYM COMPLEX_VEC_0)] THEN
    REWRITE_TAC [COMPLEX_NORM_MUL, NORM_CEXP_II, REAL_MUL_RID] THEN
    REWRITE_TAC [NORM_0, LIFT_NUM, VECTOR_MUL_RZERO] THEN
    REWRITE_TAC [NORM_LIFT, REAL_ABS_NORM, (← HolLight.GSYM LIFT_CMUL)] THEN
    REWRITE_TAC [COMPLEX_NORM_CX, REAL_ABS_RPOW, REAL_ABS_ABS] THEN
    REWRITE_TAC [ABSOLUTELY_INTEGRABLE_CONST, INTEGRAL_CONST] THEN
    REWRITE_TAC [EMPTY_GSPEC, NEGLIGIBLE_EMPTY, COND_RAND] THEN
    REWRITE_TAC [VECTOR_MUL_RZERO] THEN
    REWRITE_TAC [(← HolLight.REWRITE_RULE [IN] INTEGRABLE_RESTRICT_INTER)] THEN
    MATCH_MP_TAC INTEGRABLE_CMUL THEN
    REWRITE_TAC [h4] THEN
    REWRITE_TAC [h5] THEN
    SUBGOAL_THEN ([[{x | &0 <= drop x /\ drop x <= r} = interval[vec 0,lift r] ]]) SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_INTERVAL_1] THEN
      REWRITE_TAC [LIFT_DROP, DROP_VEC],
      ALL_TAC] THEN
    ASM_CASES_TAC ([[interval[vec 0,lift r] = {}]]) THEN
    ASM_REWRITE_TAC [INTEGRABLE_ON_EMPTY] THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [INTERVAL_NE_EMPTY_1, DROP_VEC, LIFT_DROP]) THEN
    MP_TAC (← HolLight.SPECL [([[\x. inv(p + &2) * x rpow (p + &2)]]), ([[\x. x rpow (p + &1)]]),
      ([[&0:real]]), ([[r:real]])] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_RPOW THEN ASM_REAL_ARITH_TAC,
        REWRITE_TAC [IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
        REAL_DIFF_TAC THEN
        ASM_REWRITE_TAC [h6] THEN
        UNDISCH_TAC ([[--(&2):real < p]]) THEN CONV_TAC rf],
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP HAS_REAL_INTEGRAL_INTEGRABLE)] THEN
    REWRITE_TAC [REAL_INTEGRABLE_ON, IMAGE_LIFT_REAL_INTERVAL, LIFT_NUM] THEN
    MATCH_MP_TAC INTEGRABLE_SPIKE THEN EXISTS_TAC ([[{vec 0:real^1}]]) THEN
    REWRITE_TAC [NEGLIGIBLE_SING, IN_SING, IN_DIFF, (← HolLight.GSYM DROP_EQ)] THEN
    REWRITE_TAC [IN_INTERVAL_1, DROP_VEC, LIFT_DROP, o_THM] THEN
    ASM_SIMP_TAC [real_abs, RPOW_ADD_ALT, RPOW_POW, REAL_POW_1] THEN
    REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval ABSOLUTELY_INTEGRABLE_CPOW

/- ------------------------------------------------------------------------- -/
/- inv(z - w) is absolutely integrable on bounded measurable sets.           -/
/- ------------------------------------------------------------------------- -/

#eval phrase 27
def INV_ABSOLUTELY_INTEGRABLE_BOUNDED : thm := keep "INV_ABSOLUTELY_INTEGRABLE_BOUNDED" fun _ => (do
  prove ([[!s w:complex.
        bounded s /\ measurable s
        ==> (\z. inv(z - w)) absolutely_integrable_on s]])
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_IMP] ABSOLUTELY_INTEGRABLE_SPIKE) THEN
    EXISTS_TAC ([[(\z:complex. (z - w) cpow (--Cx(&1)))]]) THEN
    EXISTS_TAC ([[{w:complex}]]) THEN
    REWRITE_TAC [NEGLIGIBLE_SING] THEN CONJ_TAC THENL
     [X_GEN_TAC ([[z:complex]]) THEN REWRITE_TAC [IN_DIFF, IN_SING] THEN
      STRIP_TAC THEN REWRITE_TAC [CPOW_NEG, CPOW_N, COMPLEX_POW_1] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [],
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CPOW THEN
      ASM_SIMP_TAC [REAL_NEG, REAL_CX, RE_NEG, RE_CX] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV])
  : ExceptT String IO thm).run
#eval INV_ABSOLUTELY_INTEGRABLE_BOUNDED

/- ========================================================================= -/
/- Lp-based infrastructure.                                                  -/
/- Uses Holder's inequality and Lp-space theory to prove integrability of    -/
/- Cauchy-type kernels f(z)/(z-w).                                           -/
/- ========================================================================= -/

#eval phrase 28
def LSPACE_COMPLEX_INV : thm := keep "LSPACE_COMPLEX_INV" fun _ => (do
  prove ([[!s p w:complex.
      bounded s /\ measurable s /\ p < &2 ==> (\z. inv(z - w)) IN lspace s p]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [LSPACE_ALT, IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [MP_TAC (← HolLight.SPECL [([[s:complex->bool]]), ([[--Cx(&1)]]), ([[w:complex]])] ABSOLUTELY_INTEGRABLE_CPOW) THEN
      ASM_SIMP_TAC [CPOW_NEG, CPOW_N, REAL_NEG, REAL_CX, RE_NEG, RE_CX] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC [COMPLEX_POW_1, COMPLEX_SUB_0] THEN
      REWRITE_TAC [ABSOLUTELY_INTEGRABLE_MEASURABLE] THEN
      DISCH_THEN (MP_TAC o HolLight.CONJUNCT1) THEN MATCH_MP_TAC EQ_IMP THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [COMPLEX_SUB_REFL, COMPLEX_INV_0],
      MP_TAC (← HolLight.SPECL [([[s:complex->bool]]), ([[--Cx p]]), ([[w:complex]])] ABSOLUTELY_INTEGRABLE_CPOW) THEN
      ASM_SIMP_TAC [CPOW_NEG, CPOW_N, REAL_NEG, REAL_CX, RE_NEG, RE_CX] THEN
      ASM_REWRITE_TAC [REAL_LT_NEG2] THEN DISCH_THEN (MP_TAC o
        HolLight.MATCH_MP ABSOLUTELY_INTEGRABLE_NORM) THEN
      REWRITE_TAC [] THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SPIKE THEN
      EXISTS_TAC ([[{w:complex}]]) THEN REWRITE_TAC [NEGLIGIBLE_SING] THEN
      X_GEN_TAC ([[z:complex]]) THEN REWRITE_TAC [IN_DIFF, IN_SING] THEN
      STRIP_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC [COMPLEX_NORM_INV, RPOW_INV] THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC [NORM_CPOW_COMPLEX, REAL_CX, COMPLEX_SUB_0, RE_CX]])
  : ExceptT String IO thm).run
#eval LSPACE_COMPLEX_INV

/- ------------------------------------------------------------------------- -/
/- u(z) / (z - w) is absolutely integrable for compactly supported u.        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 29
def CAUCHY_KERNEL_ABSOLUTELY_INTEGRABLE : thm := keep "CAUCHY_KERNEL_ABSOLUTELY_INTEGRABLE" fun _ => (do
  prove ([[!u:complex->complex w.
        u continuous_on (:complex) /\
        bounded (support (+) u (:complex))
        ==> (\z. u(z) / (z - w)) absolutely_integrable_on (:complex)]])
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [complex_div] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[Cx(&0)]]) o HolLight.MATCH_MP BOUNDED_SUBSET_CBALL) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[R:real]]) STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_IMP] ABSOLUTELY_INTEGRABLE_SPIKE) THEN
    EXISTS_TAC ([[(\z:complex. if z IN cball(Cx(&0),R) then
                     u z * inv(z - w) else vec 0)]]) THEN
    EXISTS_TAC ([[{}:complex->bool]]) THEN
    REWRITE_TAC [NEGLIGIBLE_EMPTY, IN_DIFF, NOT_IN_EMPTY, IN_UNIV] THEN
    CONJ_TAC THENL
     [X_GEN_TAC ([[z:complex]]) THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN ([[~((z:real^2) IN support (+) (u:real^2->real^2) (:real^2))]]) MP_TAC THENL [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN
      REWRITE_TAC [support, IN_ELIM_THM, IN_UNIV, NEUTRAL_VECTOR_ADD] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC [COMPLEX_MUL_LZERO, COMPLEX_VEC_0],
      REWRITE_TAC [ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
      SUBGOAL_THEN ([[(\z:real^2. (u:real^2->real^2) z * inv(z - w)) =
       (\z. u z * (\z. inv(z - w)) z)]]) SUBST1_TAC THENL
       [REWRITE_TAC [], ALL_TAC] THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
      REWRITE_TAC [BILINEAR_COMPLEX_MUL] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
        EXISTS_TAC ([[(:complex)]]) THEN
        REWRITE_TAC [SUBSET_UNIV] THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN ASM_REWRITE_TAC [],
          MATCH_MP_TAC MEASURABLE_IMP_LEBESGUE_MEASURABLE THEN
          REWRITE_TAC [MEASURABLE_CBALL]],
        MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
        MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC ([[(:complex)]]) THEN
          ASM_REWRITE_TAC [SUBSET_UNIV],
          REWRITE_TAC [COMPACT_CBALL]],
        MATCH_MP_TAC INV_ABSOLUTELY_INTEGRABLE_BOUNDED THEN
        REWRITE_TAC [BOUNDED_CBALL, MEASURABLE_CBALL]]])
  : ExceptT String IO thm).run
#eval CAUCHY_KERNEL_ABSOLUTELY_INTEGRABLE

/- ------------------------------------------------------------------------- -/
/- Helper: if-then-else with constant predicate under integral.              -/
/- ------------------------------------------------------------------------- -/

#eval phrase 30
def INTEGRAL_IF_CONST : thm := keep "INTEGRAL_IF_CONST" fun _ => (do
  prove ([[!s P (f:real^M->real^N).
    integral s (\y. if P then f y else vec 0) =
    if P then integral s f else vec 0]])
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [ETA_AX, INTEGRAL_0])
  : ExceptT String IO thm).run
#eval INTEGRAL_IF_CONST

/- ------------------------------------------------------------------------- -/
/- Negligibility of a graph in the product space real^1 x complex.           -/
/- The graph {(x,y) | y = h(x)} is a 1-dim curve in 3-dim space.             -/
/- Uses FUBINI_TONELLI_NEGLIGIBLE: each x-slice is a singleton (negligible). -/
/- ------------------------------------------------------------------------- -/

#eval phrase 31
def NEGLIGIBLE_GRAPH_PRODUCT : thm := keep "NEGLIGIBLE_GRAPH_PRODUCT" fun _ => (do
  let h1 ← sr (← ExceptT.mk [[{y:complex | y = a} = {a}]])
  prove ([[!h:real^1->complex. h measurable_on (:real^1) ==>
    negligible {p:real^(1,2)finite_sum | sndcart p = h(fstcart p)}]])
   (GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[(\p:real^(1,2)finite_sum. sndcart p - (h:real^1->complex)(fstcart p)) measurable_on
    (:real^(1,2)finite_sum)]]) ASSUME_TAC THENL
    [MATCH_MP_TAC MEASURABLE_ON_SUB THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
      MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC [LINEAR_SNDCART],
      MATCH_MP_TAC (← HolLight.INST_TYPE [((← ExceptT.mk (HolCore.Parser.parse_type "2")), (← ExceptT.mk (HolCore.Parser.parse_type "N")))] MEASURABLE_ON_COMPOSE_FSTCART) THEN
      ASM_REWRITE_TAC []], ALL_TAC] THEN
    SUBGOAL_THEN ([[lebesgue_measurable
    {p:real^(1,2)finite_sum | sndcart p = (h:real^1->complex)(fstcart p)}]]) ASSUME_TAC THENL
    [SUBGOAL_THEN ([[{p:real^(1,2)finite_sum | sndcart p = h(fstcart p)} =
    {p | (\p:real^(1,2)finite_sum. sndcart p - h(fstcart p)) p IN
         {vec 0:complex}}]]) SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_SING] THEN
      GEN_TAC THEN CONV_TAC va, ALL_TAC] THEN
     MATCH_MP_TAC LEBESGUE_MEASURABLE_PREIMAGE_CLOSED THEN
     ASM_REWRITE_TAC [CLOSED_SING], ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP (← HolLight.INST_TYPE [((← ExceptT.mk (HolCore.Parser.parse_type "1")), (← ExceptT.mk (HolCore.Parser.parse_type "M"))), ((← ExceptT.mk (HolCore.Parser.parse_type "2")), (← ExceptT.mk (HolCore.Parser.parse_type "N")))] FUBINI_TONELLI_NEGLIGIBLE)) THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [IN_ELIM_THM, FSTCART_PASTECART, SNDCART_PASTECART] THEN
    SUBGOAL_THEN ([[{x:real^1 | ~negligible {y:complex | y = (h:real^1->complex) x}} = {}]]) SUBST1_TAC THENL
    [REWRITE_TAC [EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY] THEN
     GEN_TAC THEN REWRITE_TAC [h1] THEN
     REWRITE_TAC [NEGLIGIBLE_SING], ALL_TAC] THEN
    REWRITE_TAC [NEGLIGIBLE_EMPTY])
  : ExceptT String IO thm).run
#eval NEGLIGIBLE_GRAPH_PRODUCT

/- ------------------------------------------------------------------------- -/
/- Measurability of the Fubini integrand on the product space.               -/
/- Key idea: extend g from [0,1] to all of R via Tietze, then factor the     -/
/- function as u(y) * inv(y - G(x)) * (if x IN [0,1] then g'(x) else 0).     -/
/- Each factor is measurable using standard library lemmas.                  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 32
def MEASURABLE_ON_FUBINI_INTEGRAND : thm := keep "MEASURABLE_ON_FUBINI_INTEGRAND" fun _ => (do
  prove ([[!u:complex->complex g:real^1->complex.
    u continuous_on (:complex) /\
    g absolutely_continuous_on interval[vec 0,vec 1]
    ==> (\p:real^(1,2)finite_sum.
            if fstcart p IN interval[vec 0,vec 1]
            then u(sndcart p) / (sndcart p - g(fstcart p)) *
                 vector_derivative g (at (fstcart p))
            else vec 0)
        measurable_on (:real^(1,2)finite_sum)]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[?G:real^1->complex. G continuous_on (:real^1) /\
     (!x. x IN interval[vec 0,vec 1] ==> G x = (g:real^1->complex) x)]]) STRIP_ASSUME_TAC THENL
    [MP_TAC (← HolLight.ISPECL [([[g:real^1->complex]]), ([[(:real^1)]]),
                     ([[interval[vec 0:real^1,vec 1] ]])] TIETZE_UNBOUNDED) THEN
     ANTS_TAC THENL
     [CONJ_TAC THENL
      [MATCH_MP_TAC CLOSED_SUBSET THEN
       REWRITE_TAC [CLOSED_INTERVAL, SUBSET_UNIV],
       ASM_MESON_TAC [ABSOLUTELY_CONTINUOUS_IMP_PATH, path]],
      MESON_TAC []], ALL_TAC] THEN
    MATCH_MP_TAC MEASURABLE_ON_EQ THEN
    EXISTS_TAC ([[(\p:real^(1,2)finite_sum.
    u(sndcart p:complex) * inv(sndcart p - (G:real^1->complex)(fstcart p)) *
    (if fstcart p IN interval[vec 0,vec 1]
     then vector_derivative (g:real^1->complex) (at (fstcart p))
     else vec 0))]]) THEN
    CONJ_TAC THENL
    [X_GEN_TAC ([[p:real^(1,2)finite_sum]]) THEN REWRITE_TAC [IN_UNIV] THEN
     COND_CASES_TAC THENL
     [ASM_SIMP_TAC [] THEN REWRITE_TAC [complex_div, COMPLEX_MUL_ASSOC],
      REWRITE_TAC [COMPLEX_VEC_0, COMPLEX_MUL_RZERO]],
     ALL_TAC] THEN
    MATCH_MP_TAC MEASURABLE_ON_COMPLEX_MUL THEN CONJ_TAC THENL
    [MATCH_MP_TAC (← HolLight.INST_TYPE [((← ExceptT.mk (HolCore.Parser.parse_type "1")), (← ExceptT.mk (HolCore.Parser.parse_type "M")))] MEASURABLE_ON_COMPOSE_SNDCART) THEN
     MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN ASM_REWRITE_TAC [],
     MATCH_MP_TAC MEASURABLE_ON_COMPLEX_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_ON_COMPLEX_INV THEN CONJ_TAC THENL
      [MATCH_MP_TAC MEASURABLE_ON_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
        MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC [LINEAR_SNDCART],
        MATCH_MP_TAC (← HolLight.INST_TYPE [((← ExceptT.mk (HolCore.Parser.parse_type "2")), (← ExceptT.mk (HolCore.Parser.parse_type "N")))] MEASURABLE_ON_COMPOSE_FSTCART) THEN
        MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN ASM_REWRITE_TAC []],
       SUBGOAL_THEN ([[{p:real^(1,2)finite_sum |
          sndcart p - (G:real^1->complex)(fstcart p) = Cx(&0)} =
        {p | sndcart p = G(fstcart p)}]]) SUBST1_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_ELIM_THM, (← HolLight.GSYM COMPLEX_VEC_0)] THEN
        GEN_TAC THEN CONV_TAC va,
        MATCH_MP_TAC NEGLIGIBLE_GRAPH_PRODUCT THEN
        MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN ASM_REWRITE_TAC []]],
      SUBGOAL_THEN ([[(\t:real^1. if t IN interval[vec 0,vec 1]
        then vector_derivative (g:real^1->complex) (at t)
        else vec 0) measurable_on (:real^1)]]) MP_TAC THENL
      [REWRITE_TAC [MEASURABLE_ON_UNIV] THEN
       MATCH_MP_TAC INTEGRABLE_IMP_MEASURABLE THEN
       MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
       MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_VECTOR_DERIVATIVE_ABSOLUTELY_CONTINUOUS THEN
       ASM_REWRITE_TAC [],
       ALL_TAC] THEN
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← HolLight.INST_TYPE [((← ExceptT.mk (HolCore.Parser.parse_type "2")), (← ExceptT.mk (HolCore.Parser.parse_type "N")))] MEASURABLE_ON_COMPOSE_FSTCART)) THEN
      MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_CONJ] MEASURABLE_ON_EQ) THEN
      X_GEN_TAC ([[p:real^(1,2)finite_sum]]) THEN
      REWRITE_TAC [IN_UNIV]]])
  : ExceptT String IO thm).run
#eval MEASURABLE_ON_FUBINI_INTEGRAND

/- ------------------------------------------------------------------------- -/
/- Uniform bound on Cauchy kernel L^1 norm over compact sets of poles.       -/
/- For w in compact K, integral |u(y)/(y-w)| dy <= C uniformly.              -/
/- Key tool: cball(0,R) subset cball(w,R+S) + translation of integral.       -/
/- ------------------------------------------------------------------------- -/

#eval phrase 33
def CAUCHY_KERNEL_NORM_UNIFORM_BOUND : thm := keep "CAUCHY_KERNEL_NORM_UNIFORM_BOUND" fun _ => (do
  prove ([[!u:complex->complex K.
        u continuous_on (:complex) /\
        bounded (support (+) u (:complex)) /\
        compact K
        ==> ?C. &0 <= C /\
                !w. w IN K ==>
                  drop(integral (:complex)
                       (\y. lift(norm(u y / (y - w))))) <= C]])
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[Cx(&0)]]) o HolLight.MATCH_MP BOUNDED_SUBSET_CBALL) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[R:real]]) STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP COMPACT_IMP_BOUNDED) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[Cx(&0)]]) o HolLight.MATCH_MP BOUNDED_SUBSET_CBALL) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[S:real]]) STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN ([[?M. &0 <= M /\ !y:complex. norm((u:complex->complex) y) <= M]]) STRIP_ASSUME_TAC THENL
    [MP_TAC (← HolLight.ISPECL [([[u:complex->complex]]), ([[(:complex)]])] CONTINUOUS_ON_CLOSURE) THEN
     ASM_REWRITE_TAC [CLOSURE_UNIV, IN_UNIV] THEN
     DISCH_TAC THEN
     MP_TAC (← HolLight.ISPECL [([[u:complex->complex]]),
                     ([[cball(Cx(&0),R)]])] COMPACT_CONTINUOUS_IMAGE) THEN
     ANTS_TAC THENL
      [CONJ_TAC THENL
        [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
         EXISTS_TAC ([[(:complex)]]) THEN ASM_REWRITE_TAC [SUBSET_UNIV],
         REWRITE_TAC [COMPACT_CBALL]], ALL_TAC] THEN
     DISCH_THEN (MP_TAC o HolLight.MATCH_MP COMPACT_IMP_BOUNDED) THEN
     REWRITE_TAC [BOUNDED_POS, FORALL_IN_IMAGE] THEN
     DISCH_THEN (X_CHOOSE_THEN ([[M:real]]) STRIP_ASSUME_TAC) THEN
     EXISTS_TAC ([[M:real]]) THEN CONJ_TAC THENL
      [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
     X_GEN_TAC ([[y:complex]]) THEN
     ASM_CASES_TAC ([[(y:complex) IN cball(Cx(&0),R)]]) THENL
      [ASM_SIMP_TAC [], ALL_TAC] THEN
     SUBGOAL_THEN ([[~(y IN support (+) (u:complex->complex) (:complex))]]) MP_TAC THENL [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN
     REWRITE_TAC [support, IN_ELIM_THM, IN_UNIV, NEUTRAL_VECTOR_ADD] THEN
     DISCH_TAC THEN ASM_REWRITE_TAC [NORM_0] THEN ASM_REAL_ARITH_TAC,
     ALL_TAC] THEN
    SUBGOAL_THEN ([[!w:complex. (\z. inv(z - w))
       absolutely_integrable_on cball(Cx(&0),R + S)]]) ASSUME_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC INV_ABSOLUTELY_INTEGRABLE_BOUNDED THEN
     REWRITE_TAC [BOUNDED_CBALL, MEASURABLE_CBALL], ALL_TAC] THEN
    ABBREV_TAC ([[C = M * drop(integral (cball(Cx(&0),R + S))
                           (\z:complex. lift(norm(inv z))))]]) THEN
    EXISTS_TAC ([[C:real]]) THEN CONJ_TAC THENL
    [EXPAND_TAC "C" THEN MATCH_MP_TAC REAL_LE_MUL THEN
     ASM_REWRITE_TAC [] THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN CONJ_TAC THENL
      [FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[Cx(&0)]])) THEN
       REWRITE_TAC [COMPLEX_SUB_RZERO] THEN
       DISCH_THEN (fun th => HolLight.tactic_of do
        pure (ACCEPT_TAC (← HolLight.MATCH_MP ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE (← HolLight.CONV_RULE (HolLight.ONCE_DEPTH_CONV HolLight.BETA_CONV) (← HolLight.MATCH_MP ABSOLUTELY_INTEGRABLE_NORM th))))),
       REWRITE_TAC [LIFT_DROP, NORM_POS_LE]], ALL_TAC] THEN
    X_GEN_TAC ([[w:complex]]) THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[integral (:complex) (\y. lift(norm((u:complex->complex) y / (y - w)))) =
     integral (cball(Cx(&0),R)) (\y:complex. lift(norm(u y / (y - w))))]]) SUBST1_TAC THENL
    [CONV_TAC HolLight.SYM_CONV THEN GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM INTEGRAL_RESTRICT_UNIV)] THEN
     MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC ([[y:complex]]) THEN
     REWRITE_TAC [IN_UNIV] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
     SUBGOAL_THEN ([[(u:complex->complex) y = vec 0]]) SUBST1_TAC THENL
      [SUBGOAL_THEN ([[~(y IN support (+) (u:complex->complex) (:complex))]]) MP_TAC THENL
        [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN
       REWRITE_TAC [support, IN_ELIM_THM, IN_UNIV, NEUTRAL_VECTOR_ADD] THEN
       SIMP_TAC [],
       REWRITE_TAC [COMPLEX_VEC_0, complex_div, COMPLEX_MUL_LZERO,
                   COMPLEX_NORM_CX, REAL_ABS_NUM, NORM_0, LIFT_NUM]], ALL_TAC] THEN
    SUBGOAL_THEN ([[drop(integral (cball(Cx(&0),R))
       (\y:complex. lift(norm((u:complex->complex) y / (y - w))))) <=
     M * drop(integral (cball(Cx(&0),R))
       (\y:complex. lift(norm(inv(y - w)))))]]) (fun th => MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC ([[M * drop(integral (cball(Cx(&0),R))
         (\y:complex. lift(norm(inv(y - w:complex)))))]]) THEN
        CONJ_TAC THENL [ACCEPT_TAC th, ALL_TAC]) THENL
    [MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC ([[drop(integral (cball(Cx(&0),R))
     (\y:complex. lift(M * norm(inv(y - w:complex)))))]]) THEN
     CONJ_TAC THENL
      [MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
        [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
         MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
         MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
         EXISTS_TAC ([[(:complex)]]) THEN
         ASM_REWRITE_TAC [SUBSET_UNIV] THEN CONJ_TAC THENL
          [MATCH_MP_TAC CAUCHY_KERNEL_ABSOLUTELY_INTEGRABLE THEN
           ASM_REWRITE_TAC [] THEN
           MATCH_MP_TAC BOUNDED_SUBSET THEN
           EXISTS_TAC ([[cball(Cx(&0),R)]]) THEN
           ASM_REWRITE_TAC [BOUNDED_CBALL],
           MATCH_MP_TAC MEASURABLE_IMP_LEBESGUE_MEASURABLE THEN
           REWRITE_TAC [MEASURABLE_CBALL]],
         REWRITE_TAC [LIFT_CMUL] THEN
         MATCH_MP_TAC INTEGRABLE_CMUL THEN
         MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
         MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
         MATCH_MP_TAC INV_ABSOLUTELY_INTEGRABLE_BOUNDED THEN
         REWRITE_TAC [BOUNDED_CBALL, MEASURABLE_CBALL],
         X_GEN_TAC ([[y:complex]]) THEN DISCH_TAC THEN
         REWRITE_TAC [LIFT_DROP] THEN
         REWRITE_TAC [complex_div, COMPLEX_NORM_MUL] THEN
         MATCH_MP_TAC REAL_LE_RMUL THEN
         ASM_REWRITE_TAC [NORM_POS_LE]],
       REWRITE_TAC [LIFT_CMUL] THEN
       SUBGOAL_THEN ([[(\y:complex. lift(norm(inv(y - w)))) integrable_on cball(Cx(&0),R)]]) (fun th => HolLight.tactic_of do
        pure (SIMP_TAC [(← HolLight.CONV_RULE (HolLight.ONCE_DEPTH_CONV HolLight.BETA_CONV) (← HolLight.MATCH_MP INTEGRAL_CMUL th)), DROP_CMUL,
                             REAL_LE_REFL])) THEN
       MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
       MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
       MATCH_MP_TAC INV_ABSOLUTELY_INTEGRABLE_BOUNDED THEN
       REWRITE_TAC [BOUNDED_CBALL, MEASURABLE_CBALL]], ALL_TAC] THEN
    SUBGOAL_THEN ([[cball(Cx(&0),R) SUBSET cball(w:complex,R + S)]]) ASSUME_TAC THENL
    [REWRITE_TAC [SUBSET] THEN X_GEN_TAC ([[y:complex]]) THEN
     DISCH_TAC THEN
     SUBGOAL_THEN ([[w:complex IN cball(Cx(&0),S)]]) MP_TAC THENL
      [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN
     REWRITE_TAC [IN_CBALL, SessionMultiLib.Vectors.dist, COMPLEX_SUB_LZERO, NORM_NEG] THEN
     UNDISCH_TAC ([[y:complex IN cball(Cx(&0),R)]]) THEN
     REWRITE_TAC [IN_CBALL, SessionMultiLib.Vectors.dist, COMPLEX_SUB_LZERO, NORM_NEG] THEN
     REPEAT STRIP_TAC THEN
     MP_TAC (← HolLight.ISPECL [([[w:complex]]), ([[Cx(&0)]]), ([[y:complex]])] SessionMultiLib.Vectors.DIST_TRIANGLE) THEN
     REWRITE_TAC [SessionMultiLib.Vectors.dist, COMPLEX_SUB_RZERO, COMPLEX_SUB_LZERO, NORM_NEG] THEN
     ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    SUBGOAL_THEN ([[M * drop(integral (cball(Cx(&0),R))
       (\y:complex. lift(norm(inv(y - w))))) <=
     M * drop(integral (cball(w:complex,R + S))
       (\y. lift(norm(inv(y - w)))))]]) (fun th => MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC ([[M * drop(integral (cball(w:complex,R + S))
         (\y. lift(norm(inv(y - w)))))]]) THEN
        CONJ_TAC THENL [ACCEPT_TAC th, ALL_TAC]) THENL
    [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
     ASM_REWRITE_TAC [LIFT_DROP, NORM_POS_LE] THEN
     CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
     MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
     MATCH_MP_TAC INV_ABSOLUTELY_INTEGRABLE_BOUNDED THENL
      [REWRITE_TAC [BOUNDED_CBALL, MEASURABLE_CBALL],
       REWRITE_TAC [BOUNDED_CBALL, MEASURABLE_CBALL]], ALL_TAC] THEN
    SUBGOAL_THEN ([[M * drop(integral (cball(w:complex,R + S))
       (\y. lift(norm(inv(y - w))))) = C]]) (fun th => ASM_REWRITE_TAC [th, REAL_LE_REFL]) THEN
    EXPAND_TAC "C" THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN ([[cball(w:complex,R + S) = IMAGE (\z. w + z) (cball(Cx(&0),R + S))]]) SUBST1_TAC THENL
    [REWRITE_TAC [(← HolLight.GSYM CBALL_TRANSLATION), COMPLEX_ADD_RID], ALL_TAC] THEN
    REWRITE_TAC [(← HolLight.GSYM INTEGRAL_TRANSLATION)] THEN
    MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC ([[z:complex]]) THEN
    DISCH_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN SIMPLE_COMPLEX_ARITH_TAC)
  : ExceptT String IO thm).run
#eval CAUCHY_KERNEL_NORM_UNIFORM_BOUND

/- ------------------------------------------------------------------------- -/
/- Measurability of the weighted Cauchy kernel norm integral on [0,1].       -/
/- Uses dominated convergence to show continuity and convergence of          -/
/- truncated integrals, then MEASURABLE_ON_LIMIT + MEASURABLE_ON_DROP_MUL.   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 34
def SUPPORT_BOUNDED_OUTSIDE : thm := keep "SUPPORT_BOUNDED_OUTSIDE" fun _ => (do
  prove ([[!(u:real^M->real^N) R y.
    (!z. z IN support (+) u (:real^M) ==> norm z <= R) /\
    norm(y) > R ==> u y = vec 0]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_CASES_TAC ([[(u:real^M->real^N) y = vec 0]]) THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[y:real^M]])) THEN
    REWRITE_TAC [IN_SUPPORT, IN_UNIV, NEUTRAL_VECTOR_ADD] THEN
    ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC)
  : ExceptT String IO thm).run
#eval SUPPORT_BOUNDED_OUTSIDE

#eval phrase 35
def CAUCHY_KERNEL_NORM_TRUNC_INTEGRABLE : thm := keep "CAUCHY_KERNEL_NORM_TRUNC_INTEGRABLE" fun _ => (do
  prove ([[!u:complex->complex w:complex n:num.
    u continuous_on (:complex) /\ bounded(support (+) u (:complex))
    ==> (\y. lift(real_min (norm(u y / (y - w))) (&n)))
        integrable_on (:complex)]])
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC ([[(\y:complex. lift(norm(u y / (y - w))))]]) THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN ([[(\y:complex. lift(norm(u y / (y - w)))) measurable_on (:complex)]]) ASSUME_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_IMP_MEASURABLE THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_LIFT_NORM_INTEGRABLE THEN
        MATCH_MP_TAC CAUCHY_KERNEL_ABSOLUTELY_INTEGRABLE THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN ([[(\y:complex. lift(real_min (norm(u y / (y - w))) (&n))) =
      (\y. (lambda i. min (lift(norm(u y / (y - w)))$i) (lift(&n)$i)):real^1)]]) SUBST1_TAC THENL
       [REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC ([[y:complex]]) THEN
        SIMP_TAC [CART_EQ, LAMBDA_BETA, DIMINDEX_1, FORALL_1] THEN
        REWRITE_TAC [(← HolLight.GSYM drop), LIFT_DROP, real_min], ALL_TAC] THEN
      MATCH_MP_TAC MEASURABLE_ON_MIN THEN ASM_REWRITE_TAC [MEASURABLE_ON_CONST],
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_LIFT_NORM_INTEGRABLE THEN
      MATCH_MP_TAC CAUCHY_KERNEL_ABSOLUTELY_INTEGRABLE THEN ASM_REWRITE_TAC [],
      X_GEN_TAC ([[y:complex]]) THEN REWRITE_TAC [IN_UNIV, NORM_LIFT, LIFT_DROP, real_min] THEN
      COND_CASES_TAC THEN REWRITE_TAC [REAL_ABS_NORM, REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC])
  : ExceptT String IO thm).run
#eval CAUCHY_KERNEL_NORM_TRUNC_INTEGRABLE

#eval phrase 36
def CAUCHY_KERNEL_NORM_TRUNC_CONTINUOUS : thm := keep "CAUCHY_KERNEL_NORM_TRUNC_CONTINUOUS" fun _ => (do
  prove ([[!u:complex->complex n:num.
    u continuous_on (:complex) /\ bounded(support (+) u (:complex))
    ==> (\w. integral (:complex)
               (\y. lift(real_min (norm(u y / (y - w))) (&n))))
        continuous_on (:complex)]])
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [CONTINUOUS_ON_SEQUENTIALLY, IN_UNIV, o_DEF] THEN
    MAP_EVERY X_GEN_TAC [([[w:num->complex]]), ([[w0:complex]])] THEN
    DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [BOUNDED_POS]) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[R:real]]) STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN ([[!k:num. (\y:complex. lift(real_min (norm(u y / (y - (w:num->complex) k))) (&n)))
            integrable_on (:complex)]]) ASSUME_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC CAUCHY_KERNEL_NORM_TRUNC_INTEGRABLE THEN
     ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN ([[(\y:complex. if y IN cball(vec 0, R) then lift(&n) else vec 0)
    integrable_on (:complex)]]) ASSUME_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_ON_SUPERSET THEN
     EXISTS_TAC ([[cball(vec 0:complex, R)]]) THEN REPEAT CONJ_TAC THENL
      [X_GEN_TAC ([[y:complex]]) THEN
       REWRITE_TAC [] THEN DISCH_TAC THEN ASM_REWRITE_TAC [],
       REWRITE_TAC [SUBSET_UNIV],
       MATCH_MP_TAC INTEGRABLE_EQ THEN
       EXISTS_TAC ([[(\y:complex. lift(&n))]]) THEN CONJ_TAC THENL
        [X_GEN_TAC ([[y:complex]]) THEN DISCH_TAC THEN
         BETA_TAC THEN ASM_REWRITE_TAC [],
         REWRITE_TAC [INTEGRABLE_ON_CONST, MEASURABLE_CBALL]]],
     ALL_TAC] THEN
    SUBGOAL_THEN ([[!k:num y:complex. ~(y = w0)
    ==> norm(lift(real_min (norm(u y / (y - (w:num->complex) k))) (&n))) <=
        drop(if y IN cball(vec 0:complex, R) then lift(&n) else vec 0)]]) ASSUME_TAC THENL
    [REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [NORM_LIFT] THEN
     ASM_CASES_TAC ([[(y:complex) IN cball(vec 0:complex, R)]]) THENL
      [ASM_REWRITE_TAC [LIFT_DROP] THEN
       REWRITE_TAC [real_min] THEN COND_CASES_TAC THEN
       REWRITE_TAC [REAL_ABS_NORM] THEN ASM_REAL_ARITH_TAC,
       ASM_REWRITE_TAC [DROP_VEC] THEN
       SUBGOAL_THEN ([[(u:complex->complex) y = vec 0]]) SUBST1_TAC THENL
        [MP_TAC (← HolLight.ISPECL [([[u:complex->complex]]), ([[R:real]]), ([[y:complex]])] SUPPORT_BOUNDED_OUTSIDE) THEN
         ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
         POP_ASSUM MP_TAC THEN REWRITE_TAC [IN_CBALL_0] THEN ASM_REAL_ARITH_TAC,
         REWRITE_TAC [complex_div, COMPLEX_VEC_0, COMPLEX_MUL_LZERO,
                      COMPLEX_NORM_CX, REAL_ABS_NUM, real_min] THEN
         REAL_ARITH_TAC2]],
     ALL_TAC] THEN
    SUBGOAL_THEN ([[!y:complex. ~(y = w0:complex)
    ==> ((\k:num. lift(real_min (norm((u:complex->complex) y / (y - (w:num->complex) k))) (&(n:num))))
         --> lift(real_min (norm(u y / (y - w0))) (&n))) sequentially]]) ASSUME_TAC THENL
    [X_GEN_TAC ([[y:complex]]) THEN DISCH_TAC THEN
     SUBGOAL_THEN ([[!z:complex. lift(real_min (norm((u:complex->complex) (y:complex) / (y - z))) (&(n:num))) =
       (lambda i. min (lift(norm(u y / (y - z)))$i) (lift(&n)$i)):real^1]]) (fun th => REWRITE_TAC [th]) THENL
      [GEN_TAC THEN
       SIMP_TAC [CART_EQ, LAMBDA_BETA, DIMINDEX_1, FORALL_1] THEN
       REWRITE_TAC [(← HolLight.GSYM drop), LIFT_DROP, real_min], ALL_TAC] THEN
     MATCH_MP_TAC LIM_MIN THEN CONJ_TAC THENL
      [MATCH_MP_TAC LIM_NORM THEN
       REWRITE_TAC [complex_div] THEN
       MATCH_MP_TAC LIM_COMPLEX_MUL THEN
       CONJ_TAC THENL [REWRITE_TAC [LIM_CONST], ALL_TAC] THEN
       MATCH_MP_TAC LIM_COMPLEX_INV THEN CONJ_TAC THENL
        [MATCH_MP_TAC LIM_SUB THEN
         REWRITE_TAC [LIM_CONST] THEN ASM_REWRITE_TAC [],
         REWRITE_TAC [COMPLEX_SUB_0] THEN ASM_MESON_TAC []],
       REWRITE_TAC [LIM_CONST]],
     ALL_TAC] THEN
    MP_TAC (← HolLight.ISPECL [([[\k:num. \y:complex.
       lift(real_min (norm((u:complex->complex) y / (y - (w:num->complex) k))) (&(n:num)))]]),
       ([[\y:complex.
       lift(real_min (norm((u:complex->complex) y / (y - w0:complex))) (&(n:num)))]]),
       ([[\y:complex.
       if y IN cball(vec 0:complex, R:real) then lift(&(n:num)) else vec 0]]),
       ([[(:complex)]]),
       ([[{w0:complex}]])] DOMINATED_CONVERGENCE_AE) THEN
    CONV_TAC (HolLight.LAND_CONV (HolLight.DEPTH_CONV HolLight.BETA_CONV)) THEN
    REWRITE_TAC [IN_UNIV, IN_DIFF, IN_SING] THEN
    DISCH_THEN (fun th => ASM_REWRITE_TAC [] THEN
      MP_TAC th THEN ASM_REWRITE_TAC [NEGLIGIBLE_SING]) THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
        pure (ACCEPT_TAC (← HolLight.CONJUNCT2 th))))
  : ExceptT String IO thm).run
#eval CAUCHY_KERNEL_NORM_TRUNC_CONTINUOUS

#eval phrase 37
def CAUCHY_KERNEL_NORM_TRUNC_CONVERGES : thm := keep "CAUCHY_KERNEL_NORM_TRUNC_CONVERGES" fun _ => (do
  prove ([[!u:complex->complex w:complex.
    u continuous_on (:complex) /\ bounded(support (+) u (:complex))
    ==> ((\n. integral (:complex)
               (\y. lift(real_min (norm(u y / (y - w))) (&n))))
         --> integral (:complex)
               (\y. lift(norm(u y / (y - w))))) sequentially]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[\k:num. \y:complex.
       lift(real_min (norm((u:complex->complex) y / (y - w:complex))) (&k))]]),
       ([[\y:complex.
       lift(norm((u:complex->complex) y / (y - w:complex)))]]),
       ([[\y:complex.
       lift(norm((u:complex->complex) y / (y - w:complex)))]]),
       ([[(:complex)]]),
       ([[{}:complex->bool]])] DOMINATED_CONVERGENCE_AE) THEN
    CONV_TAC (HolLight.LAND_CONV (HolLight.DEPTH_CONV HolLight.BETA_CONV)) THEN
    REWRITE_TAC [IN_UNIV, IN_DIFF, NOT_IN_EMPTY, NEGLIGIBLE_EMPTY] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC CAUCHY_KERNEL_NORM_TRUNC_INTEGRABLE THEN
        ASM_REWRITE_TAC [],
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_LIFT_NORM_INTEGRABLE THEN
        MATCH_MP_TAC CAUCHY_KERNEL_ABSOLUTELY_INTEGRABLE THEN
        ASM_REWRITE_TAC [],
        REPEAT GEN_TAC THEN
        REWRITE_TAC [NORM_LIFT, LIFT_DROP, real_min] THEN
        COND_CASES_TAC THEN REWRITE_TAC [REAL_ABS_NORM, REAL_LE_REFL] THEN
        ASM_REAL_ARITH_TAC,
        X_GEN_TAC ([[y:complex]]) THEN
        MATCH_MP_TAC LIM_EVENTUALLY THEN
        REWRITE_TAC [EVENTUALLY_SEQUENTIALLY] THEN
        MP_TAC (← HolLight.SPEC ([[norm((u:complex->complex) y / (y - w:complex))]]) REAL_ARCH_SIMPLE) THEN
        DISCH_THEN (X_CHOOSE_TAC ([[N:num]])) THEN
        EXISTS_TAC ([[N:num]]) THEN
        X_GEN_TAC ([[k:num]]) THEN DISCH_TAC THEN
        AP_TERM_TAC THEN
        REWRITE_TAC [real_min] THEN
        COND_CASES_TAC THEN REWRITE_TAC [] THEN
        UNDISCH_TAC ([[~(norm((u:complex->complex) y / (y - w)) <= &k)]]) THEN
        REWRITE_TAC [REAL_NOT_LE] THEN DISCH_TAC THEN
        UNDISCH_TAC ([[N:num <= k]]) THEN
        REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_LE)] THEN
        ASM_REAL_ARITH_TAC],
      STRIP_TAC THEN ASM_REWRITE_TAC []])
  : ExceptT String IO thm).run
#eval CAUCHY_KERNEL_NORM_TRUNC_CONVERGES

#eval phrase 38
def CAUCHY_KERNEL_WEIGHTED_MEASURABLE : thm := keep "CAUCHY_KERNEL_WEIGHTED_MEASURABLE" fun _ => (do
  prove ([[!u:complex->complex g:real^1->complex.
    u continuous_on (:complex) /\ bounded(support (+) u (:complex)) /\
    g absolutely_continuous_on interval[vec 0,vec 1]
    ==> (\x. norm(vector_derivative g (at x)) %
             integral (:complex) (\y. lift(norm(u y / (y - g x)))))
        measurable_on interval[vec 0, vec 1] ]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[(\x. norm(vector_derivative (g:real^1->complex) (at x)) %
          integral (:complex) (\y. lift(norm((u:complex->complex) y / (y - g x))))) =
     (\x. drop((\x. lift(norm(vector_derivative g (at x)))) x) %
          (\x. integral (:complex) (\y. lift(norm(u y / (y - g x))))) x)]]) SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM, LIFT_DROP], ALL_TAC] THEN
    MATCH_MP_TAC MEASURABLE_ON_DROP_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_ON_NORM THEN
      MATCH_MP_TAC INTEGRABLE_IMP_MEASURABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_VECTOR_DERIVATIVE_ABSOLUTELY_CONTINUOUS THEN
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC (← HolLight.ISPECL [([[\n:num. \x:real^1. integral (:complex)
         (\y:complex. lift(real_min (norm((u:complex->complex) y / (y - (g:real^1->complex) x))) (&n)))]]),
         ([[\x:real^1. integral (:complex)
         (\y:complex. lift(norm((u:complex->complex) y / (y - (g:real^1->complex) x))))]]),
         ([[interval[vec 0:real^1, vec 1] ]]),
         ([[{}:real^1->bool]])] MEASURABLE_ON_LIMIT) THEN
      CONV_TAC (HolLight.LAND_CONV (HolLight.DEPTH_CONV HolLight.BETA_CONV)) THEN
      REWRITE_TAC [NEGLIGIBLE_EMPTY, IN_DIFF, NOT_IN_EMPTY, IN_UNIV] THEN
      CONJ_TAC THENL
       [X_GEN_TAC ([[nn:num]]) THEN
        MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_CLOSED_SUBSET THEN
        REWRITE_TAC [CLOSED_INTERVAL] THEN
        SUBGOAL_THEN ([[(\x:real^1. integral (:complex)
           (\y:complex. lift(real_min (norm((u:complex->complex) y / (y - (g:real^1->complex) x))) (&nn)))) =
         (\w. integral (:complex)
           (\y. lift(real_min (norm(u y / (y - w))) (&nn)))) o g]]) SUBST1_TAC THENL
         [REWRITE_TAC [o_DEF], ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [ASM_MESON_TAC [ABSOLUTELY_CONTINUOUS_IMP_PATH, path],
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
          EXISTS_TAC ([[(:complex)]]) THEN REWRITE_TAC [SUBSET_UNIV] THEN
          MATCH_MP_TAC CAUCHY_KERNEL_NORM_TRUNC_CONTINUOUS THEN
          ASM_REWRITE_TAC []],
        X_GEN_TAC ([[x:real^1]]) THEN DISCH_TAC THEN
        MP_TAC (← HolLight.ISPECL [([[u:complex->complex]]), ([[(g:real^1->complex) x]])] CAUCHY_KERNEL_NORM_TRUNC_CONVERGES) THEN
        ASM_REWRITE_TAC []]])
  : ExceptT String IO thm).run
#eval CAUCHY_KERNEL_WEIGHTED_MEASURABLE

/- ------------------------------------------------------------------------- -/
/- Fubini exchange: swap path integral and area integral.                    -/
/- Uses FUBINI_INTEGRAL_SWAP on the product space real^1 x complex.          -/
/- LMUL integrability handled via INTEGRAL_SPIKE + NEGLIGIBLE_AC_PATH.       -/
/- ------------------------------------------------------------------------- -/
/- AC path image is negligible (measure zero in R^2)                         -/

#eval phrase 39
def NEGLIGIBLE_ABSOLUTELY_CONTINUOUS_PATH_IMAGE : thm := keep "NEGLIGIBLE_ABSOLUTELY_CONTINUOUS_PATH_IMAGE" fun _ => (do
  prove ([[!g:real^1->complex.
    g absolutely_continuous_on interval[vec 0,vec 1]
    ==> negligible(path_image g)]])
   (GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [path_image] THEN
    MATCH_MP_TAC NEGLIGIBLE_ABSOLUTELY_CONTINUOUS_IMAGE_LOWDIM THEN
    ASM_REWRITE_TAC [IS_INTERVAL_INTERVAL] THEN
    REWRITE_TAC [DIMINDEX_2] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval NEGLIGIBLE_ABSOLUTELY_CONTINUOUS_PATH_IMAGE

#eval phrase 40
def PATH_INTEGRABLE_CONTINUOUS_ABSOLUTELY_CONTINUOUS : thm := keep "PATH_INTEGRABLE_CONTINUOUS_ABSOLUTELY_CONTINUOUS" fun _ => (do
  prove ([[!f:complex->complex g:real^1->complex.
    f continuous_on path_image g /\
    g absolutely_continuous_on interval[vec 0,vec 1]
    ==> f path_integrable_on g]])
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [path_integrable_on, HAS_PATH_INTEGRAL, (← HolLight.GSYM integrable_on)] THEN
    SUBGOAL_THEN ([[g:real^1->complex has_bounded_variation_on interval[vec 0,vec 1] ]]) ASSUME_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_CONTINUOUS_ON_IMP_HAS_BOUNDED_VARIATION_ON THEN
      ASM_REWRITE_TAC [BOUNDED_INTERVAL], ALL_TAC] THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP ABSOLUTELY_INTEGRABLE_BOUNDED_VARIATION_DERIVATIVE) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [([[gd:real^1->complex]]), ([[s:real^1->bool]])] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN ([[path(g:real^1->complex)]]) ASSUME_TAC THENL
     [REWRITE_TAC [path] THEN
      ASM_MESON_TAC [ABSOLUTELY_CONTINUOUS_ON_IMP_CONTINUOUS,
                     IS_INTERVAL_INTERVAL], ALL_TAC] THEN
    SUBGOAL_THEN ([[(\t. (f:complex->complex)((g:real^1->complex) t))
     continuous_on interval[vec 0,vec 1] ]]) ASSUME_TAC THENL
     [REWRITE_TAC [(← HolLight.GSYM o_DEF)] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      CONJ_TAC THENL [ASM_MESON_TAC [path], ALL_TAC] THEN
      ASM_MESON_TAC [CONTINUOUS_ON_SUBSET, path_image, IMAGE_o, SUBSET_REFL],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[(\t. (f:complex->complex)((g:real^1->complex) t) * (gd:real^1->complex) t)
     integrable_on interval[vec 0,vec 1] ]]) ASSUME_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC (← HolLight.ISPEC ([[( * ):complex->complex->complex]]) ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT) THEN
      ASM_REWRITE_TAC [BILINEAR_COMPLEX_MUL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_CLOSED_SUBSET THEN
        ASM_REWRITE_TAC [CLOSED_INTERVAL],
        MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
        MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
        ASM_REWRITE_TAC [COMPACT_INTERVAL]], ALL_TAC] THEN
    MP_TAC (← HolLight.ISPECL [([[\t. (f:complex->complex)((g:real^1->complex) t) *
          (gd:real^1->complex) t]]),
       ([[\t. (f:complex->complex)((g:real^1->complex) t) *
          vector_derivative g (at t)]]),
       ([[s:real^1->bool]]),
       ([[interval[vec 0:real^1,vec 1] ]])] INTEGRABLE_SPIKE) THEN
    CONV_TAC (HolLight.LAND_CONV (HolLight.DEPTH_CONV HolLight.BETA_CONV)) THEN
    REWRITE_TAC [IMP_IMP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    X_GEN_TAC ([[t:real^1]]) THEN REWRITE_TAC [IN_DIFF] THEN STRIP_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [IN_DIFF])
  : ExceptT String IO thm).run
#eval PATH_INTEGRABLE_CONTINUOUS_ABSOLUTELY_CONTINUOUS

#eval phrase 41
def FUBINI_PATH_AREA : thm := keep "FUBINI_PATH_AREA" fun _ => (do
  let h2 ← rr (← ExceptT.mk [[&0 <= x /\ x <= C ==> abs(x) <= C]])
  let h1 ← tt (← ExceptT.mk [[~(~p) <=> p]])
  prove ([[!u:complex->complex g.
        u continuous_on (:complex) /\
        bounded (support (+) u (:complex)) /\
        g absolutely_continuous_on interval[vec 0,vec 1] /\
        pathfinish g = pathstart g
        ==> path_integral g (\w. integral (:complex)
               (\z. u(z) / (z - w))) =
            integral (:complex)
               (\z. u(z) * path_integral g (\w. Cx(&1) / (z - w)))]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [PATH_INTEGRAL_INTEGRAL] THEN
    SUBGOAL_THEN ([[!w:complex. (\z. u(z:complex) / (z - w))
                 absolutely_integrable_on (:complex)]]) ASSUME_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC CAUCHY_KERNEL_ABSOLUTELY_INTEGRABLE THEN
     ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN ([[!w:complex. (\z. u(z:complex) / (z - w)) integrable_on (:complex)]]) ASSUME_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
     ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN ([[(\p:real^(1,2)finite_sum.
        if fstcart p IN interval[vec 0,vec 1]
        then u(sndcart p:complex) / (sndcart p - g(fstcart p)) *
             vector_derivative g (at (fstcart p))
        else vec 0)
     absolutely_integrable_on (:real^(1,2)finite_sum)]]) ASSUME_TAC THENL
     [SUBGOAL_THEN ([[(\p:real^(1,2)finite_sum.
          if fstcart p IN interval[vec 0,vec 1]
          then u(sndcart p:complex) / (sndcart p - g(fstcart p)) *
               vector_derivative g (at (fstcart p))
          else vec 0)
       measurable_on (:real^(1,2)finite_sum)]]) MP_TAC THENL
      [MATCH_MP_TAC MEASURABLE_ON_FUBINI_INTEGRAND THEN
       ASM_REWRITE_TAC [], ALL_TAC] THEN
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP FUBINI_TONELLI) THEN
      DISCH_THEN (fun th => REWRITE_TAC [th]) THEN
      REWRITE_TAC [FSTCART_PASTECART, SNDCART_PASTECART] THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN ([[{x:real^1 | ~((\y:complex.
            if x IN interval[vec 0,vec 1]
            then u y / (y - g x) * vector_derivative g (at x)
            else vec 0)
            absolutely_integrable_on (:complex))} = {}]]) SUBST1_TAC THENL
         [REWRITE_TAC [EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY] THEN
          X_GEN_TAC ([[t:real^1]]) THEN
          REWRITE_TAC [h1] THEN
          ASM_CASES_TAC ([[t:real^1 IN interval[vec 0,vec 1] ]]) THENL
           [ASM_REWRITE_TAC [] THEN
            MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_COMPLEX_RMUL THEN
            MATCH_MP_TAC CAUCHY_KERNEL_ABSOLUTELY_INTEGRABLE THEN
            ASM_REWRITE_TAC [],
            ASM_REWRITE_TAC [absolutely_integrable_on,
                            NORM_0, LIFT_NUM, INTEGRABLE_0]],
          REWRITE_TAC [NEGLIGIBLE_EMPTY]],
        SUBGOAL_THEN ([[(\x:real^1. integral (:complex)
           (\y. lift(norm(if x IN interval[vec 0,vec 1]
                  then u y / (y - g x) * vector_derivative g (at x)
                  else vec 0)))) =
         (\x. if x IN interval[vec 0,vec 1]
              then norm(vector_derivative g (at x)) %
                   integral (:complex)
                     (\y. lift(norm(u y / (y - (g:real^1->complex) x))))
              else vec 0)]]) SUBST1_TAC THENL
        [REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC ([[x:real^1]]) THEN
         COND_CASES_TAC THENL
          [ASM_REWRITE_TAC [] THEN
           SUBGOAL_THEN ([[(\y:complex. lift(norm(u y / (y - g(x:real^1)) *
              vector_derivative g (at x)))) =
            (\y. norm(vector_derivative g (at x)) %
                 lift(norm(u y / (y - g x))))]]) SUBST1_TAC THENL
            [REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
             REWRITE_TAC [COMPLEX_NORM_MUL] THEN
             ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
             REWRITE_TAC [LIFT_CMUL], ALL_TAC] THEN
           MATCH_MP_TAC INTEGRAL_CMUL THEN
           MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
           MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
           MATCH_MP_TAC CAUCHY_KERNEL_ABSOLUTELY_INTEGRABLE THEN
           ASM_REWRITE_TAC [],
           ASM_REWRITE_TAC [NORM_0, LIFT_NUM, INTEGRAL_0]], ALL_TAC] THEN
        REWRITE_TAC [INTEGRABLE_RESTRICT_UNIV] THEN
        MP_TAC (← HolLight.ISPECL [([[u:complex->complex]]),
          ([[path_image(g:real^1->complex)]])] CAUCHY_KERNEL_NORM_UNIFORM_BOUND) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC COMPACT_PATH_IMAGE THEN
          ASM_MESON_TAC [ABSOLUTELY_CONTINUOUS_IMP_PATH], ALL_TAC] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[C:real]]) STRIP_ASSUME_TAC) THEN
        MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
        EXISTS_TAC ([[(\x:real^1. C % lift(norm(
        vector_derivative (g:real^1->complex) (at x))))]]) THEN
        REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC CAUCHY_KERNEL_WEIGHTED_MEASURABLE THEN
          ASM_REWRITE_TAC [],
          MATCH_MP_TAC INTEGRABLE_CMUL THEN
          MP_TAC (← HolLight.ISPEC ([[g:real^1->complex]]) ABSOLUTELY_INTEGRABLE_VECTOR_DERIVATIVE_ABSOLUTELY_CONTINUOUS) THEN
          ASM_REWRITE_TAC [] THEN
          REWRITE_TAC [absolutely_integrable_on] THEN
          STRIP_TAC THEN ASM_REWRITE_TAC [],
          BETA_TAC THEN
          X_GEN_TAC ([[x:real^1]]) THEN
          REWRITE_TAC [IN_INTERVAL_1, DROP_VEC] THEN DISCH_TAC THEN
          REWRITE_TAC [NORM_MUL, real_abs, NORM_POS_LE] THEN
          REWRITE_TAC [DROP_CMUL, LIFT_DROP] THEN
          GEN_REWRITE_TAC HolLight.RAND_CONV [REAL_MUL_SYM] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN
          CONJ_TAC THENL
           [REWRITE_TAC [NORM_POS_LE],
            REWRITE_TAC [NORM_REAL, (← HolLight.GSYM drop)] THEN
            MATCH_MP_TAC h2 THEN
            CONJ_TAC THENL
             [MATCH_MP_TAC INTEGRAL_DROP_POS THEN CONJ_TAC THENL
               [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
                MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
                MATCH_MP_TAC CAUCHY_KERNEL_ABSOLUTELY_INTEGRABLE THEN
                ASM_REWRITE_TAC [],
                REWRITE_TAC [LIFT_DROP, NORM_POS_LE]],
              FIRST_X_ASSUM MATCH_MP_TAC THEN
              REWRITE_TAC [path_image, IN_IMAGE] THEN
              EXISTS_TAC ([[x:real^1]]) THEN
              ASM_REWRITE_TAC [IN_INTERVAL_1, DROP_VEC]]]]],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP FUBINI_INTEGRAL_SWAP) THEN
    REWRITE_TAC [FSTCART_PASTECART, SNDCART_PASTECART] THEN
    REWRITE_TAC [INTEGRAL_IF_CONST, INTEGRAL_RESTRICT_UNIV] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN ([[!x:real^1.
       integral (:complex) (\z:complex. u z / (z - g x)) *
       vector_derivative g (at x) =
       integral (:complex)
       (\z. u z / (z - g x) * vector_derivative g (at x))]]) (fun th => REWRITE_TAC [th]) THENL
    [GEN_TAC THEN CONV_TAC HolLight.SYM_CONV THEN
     MATCH_MP_TAC INTEGRAL_COMPLEX_RMUL THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    FIRST_X_ASSUM (fun th => GEN_REWRITE_TAC HolLight.LAND_CONV [th]) THEN
    MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC ([[path_image (g:real^1->complex)]]) THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC NEGLIGIBLE_ABSOLUTELY_CONTINUOUS_PATH_IMAGE THEN ASM_REWRITE_TAC [],
     ALL_TAC] THEN
    X_GEN_TAC ([[z:complex]]) THEN REWRITE_TAC [IN_DIFF, IN_UNIV] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN ([[!x:real^1. u(z:complex) / (z - (g:real^1->complex) x) *
                vector_derivative g (at x) =
                u z * (Cx(&1) / (z - g x) * vector_derivative g (at x))]]) (fun th => REWRITE_TAC [th]) THENL
    [GEN_TAC THEN REWRITE_TAC [complex_div, COMPLEX_MUL_LID, COMPLEX_MUL_ASSOC],
     ALL_TAC] THEN
    CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC INTEGRAL_COMPLEX_LMUL THEN
    SUBGOAL_THEN ([[(\t:real^1. Cx(&1) / ((g:real^1->complex) t - z) *
                 vector_derivative g (at t))
     integrable_on interval[vec 0,vec 1] ]]) ASSUME_TAC THENL
    [REWRITE_TAC [(← HolLight.GSYM PATH_INTEGRABLE_ON)] THEN
     MATCH_MP_TAC PATH_INTEGRABLE_CONTINUOUS_ABSOLUTELY_CONTINUOUS THEN
     ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_DIV THEN
     REWRITE_TAC [CONTINUOUS_ON_CONST] THEN CONJ_TAC THENL
      [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
       REWRITE_TAC [CONTINUOUS_ON_CONST, CONTINUOUS_ON_ID],
       REWRITE_TAC [COMPLEX_SUB_0] THEN
       X_GEN_TAC ([[w:complex]]) THEN DISCH_TAC THEN DISCH_TAC THEN
       UNDISCH_TAC ([[~(z IN path_image(g:real^1->complex))]]) THEN
       REWRITE_TAC [] THEN ASM_MESON_TAC []],
     ALL_TAC] THEN
    SUBGOAL_THEN ([[(\t:real^1. Cx(&1) / (z - (g:real^1->complex) t) *
                 vector_derivative g (at t)) =
     (\t. --(Cx(&1) / (g t - z) * vector_derivative g (at t)))]]) SUBST1_TAC THENL
    [REWRITE_TAC [FUN_EQ_THM, complex_div] THEN X_GEN_TAC ([[t:real^1]]) THEN
     GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [(← HolLight.GSYM COMPLEX_NEG_SUB)] THEN
     REWRITE_TAC [COMPLEX_INV_NEG, COMPLEX_MUL_RNEG, COMPLEX_MUL_LNEG],
     ALL_TAC] THEN
    MATCH_MP_TAC INTEGRABLE_NEG THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval FUBINI_PATH_AREA

/- ------------------------------------------------------------------------- -/
/- Absolute integrability of the translated dbar kernel.                     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 42
def ABSOLUTELY_INTEGRABLE_DBAR_KERNEL : thm := keep "ABSOLUTELY_INTEGRABLE_DBAR_KERNEL" fun _ => (do
  prove ([[!f:complex->complex w.
        (\z. wirtinger_dbar f z) continuous_on (:complex) /\
        bounded (support (+) (wirtinger_dbar f) (:complex))
        ==> (\z. wirtinger_dbar f (w + z) / z) absolutely_integrable_on
            (:complex)]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[(\z:complex. wirtinger_dbar (f:complex->complex) (w + z) / z) =
     (\z. wirtinger_dbar f (w + z) / (z - Cx(&0)))]]) SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM, COMPLEX_SUB_RZERO], ALL_TAC] THEN
    MATCH_MP_TAC CAUCHY_KERNEL_ABSOLUTELY_INTEGRABLE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_TRANSLATE_UNIV THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [ETA_AX]) THEN ASM_REWRITE_TAC [],
      MATCH_MP_TAC BOUNDED_SUPPORT_TRANSLATE THEN ASM_REWRITE_TAC []])
  : ExceptT String IO thm).run
#eval ABSOLUTELY_INTEGRABLE_DBAR_KERNEL

/- ------------------------------------------------------------------------- -/
/- Angular / polar path lemmas for polar coordinates proof.                  -/
/- ------------------------------------------------------------------------- -/
/- Derivative chain: t -> Cx(drop t)                                         -/

#eval phrase 43
def HAS_DERIVATIVE_CX_DROP : thm := keep "HAS_DERIVATIVE_CX_DROP" fun _ => (do
  prove ([[!t:real^1. ((\t. Cx(drop t)) has_derivative (\h. Cx(drop h))) (at t)]])
   (GEN_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    REWRITE_TAC [linear, DROP_ADD, DROP_CMUL, CX_ADD, CX_MUL, COMPLEX_CMUL])
  : ExceptT String IO thm).run
#eval HAS_DERIVATIVE_CX_DROP

/- Derivative chain: t -> ii * Cx(drop t)                                    -/

#eval phrase 44
def HAS_DERIVATIVE_II_CX_DROP : thm := keep "HAS_DERIVATIVE_II_CX_DROP" fun _ => (do
  prove ([[!t:real^1. ((\t. ii * Cx(drop t)) has_derivative (\h. ii * Cx(drop h)))
              (at t)]])
   (GEN_TAC THEN
    SUBGOAL_THEN ([[(\t:real^1. ii * Cx(drop t)) =
     ((\z:complex. ii * z) o (\t:real^1. Cx(drop t)))]]) SUBST1_TAC THENL
     [REWRITE_TAC [o_DEF], ALL_TAC] THEN
    SUBGOAL_THEN ([[(\h:real^1. ii * Cx(drop h)) =
     ((\z:complex. ii * z) o (\h:real^1. Cx(drop h)))]]) SUBST1_TAC THENL
     [REWRITE_TAC [o_DEF], ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MESON_TAC [HAS_DERIVATIVE_CX_DROP],
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      MATCH_ACCEPT_TAC LINEAR_COMPLEX_MUL])
  : ExceptT String IO thm).run
#eval HAS_DERIVATIVE_II_CX_DROP

/- Derivative chain: t -> cexp(ii * Cx(drop t))                              -/

#eval phrase 45
def HAS_DERIVATIVE_CEXP_POLAR : thm := keep "HAS_DERIVATIVE_CEXP_POLAR" fun _ => (do
  prove ([[!t:real^1. ((\t. cexp(ii * Cx(drop t))) has_derivative
      (\h. cexp(ii * Cx(drop t)) * (ii * Cx(drop h)))) (at t)]])
   (GEN_TAC THEN
    SUBGOAL_THEN ([[(\t:real^1. cexp(ii * Cx(drop t))) =
     (cexp o (\t:real^1. ii * Cx(drop t)))]]) SUBST1_TAC THENL
     [REWRITE_TAC [o_DEF], ALL_TAC] THEN
    SUBGOAL_THEN ([[(\h:real^1. cexp(ii * Cx(drop t)) * (ii * Cx(drop h))) =
     ((\x:complex. cexp(ii * Cx(drop t)) * x) o (\h:real^1. ii * Cx(drop h)))]]) SUBST1_TAC THENL
     [REWRITE_TAC [o_DEF], ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MESON_TAC [HAS_DERIVATIVE_II_CX_DROP],
      MP_TAC (← HolLight.SPEC ([[ii * Cx(drop(t:real^1))]]) HAS_COMPLEX_DERIVATIVE_CEXP) THEN
      REWRITE_TAC [has_complex_derivative]])
  : ExceptT String IO thm).run
#eval HAS_DERIVATIVE_CEXP_POLAR

/- Affine map z -> w + c*z has derivative h -> c*h                           -/

#eval phrase 46
def HAS_DERIVATIVE_AFFINE_MUL : thm := keep "HAS_DERIVATIVE_AFFINE_MUL" fun _ => (do
  prove ([[!c:complex w:complex a:complex.
     ((\z. w + c * z) has_derivative (\h. c * h)) (at a)]])
   (REPEAT GEN_TAC THEN
    SUBGOAL_THEN ([[((\z:complex. w) has_derivative (\h:complex. vec 0:complex)) (at a) /\
     ((\z:complex. c * z) has_derivative (\h:complex. c * h)) (at a)]]) MP_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC [HAS_DERIVATIVE_CONST],
        MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
        MATCH_ACCEPT_TAC LINEAR_COMPLEX_MUL],
      DISCH_THEN (ACCEPT_TAC o HolLight.REWRITE_RULE [VECTOR_ADD_LID] o
        HolLight.MATCH_MP HAS_DERIVATIVE_ADD)])
  : ExceptT String IO thm).run
#eval HAS_DERIVATIVE_AFFINE_MUL

/- Derivative of full polar path t -> w + Cx(r) * cexp(ii * Cx(drop t))      -/

#eval phrase 47
def HAS_DERIVATIVE_POLAR_PATH : thm := keep "HAS_DERIVATIVE_POLAR_PATH" fun _ => (do
  prove ([[!w:complex r t:real^1.
     ((\t. w + Cx r * cexp(ii * Cx(drop t))) has_derivative
      (\h. Cx r * (cexp(ii * Cx(drop t)) * (ii * Cx(drop h))))) (at t)]])
   (REPEAT GEN_TAC THEN
    SUBGOAL_THEN ([[(\t:real^1. w + Cx r * cexp(ii * Cx(drop t))) =
     ((\z:complex. w + Cx r * z) o (\t:real^1. cexp(ii * Cx(drop t))))]]) SUBST1_TAC THENL [REWRITE_TAC [o_DEF], ALL_TAC] THEN
    SUBGOAL_THEN ([[(\h:real^1. Cx r * (cexp(ii * Cx(drop(t:real^1))) * (ii * Cx(drop h)))) =
     ((\h:complex. Cx r * h) o
      (\h:real^1. cexp(ii * Cx(drop t)) * (ii * Cx(drop h))))]]) SUBST1_TAC THENL [REWRITE_TAC [o_DEF], ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MESON_TAC [HAS_DERIVATIVE_CEXP_POLAR],
      REWRITE_TAC [HAS_DERIVATIVE_AFFINE_MUL]])
  : ExceptT String IO thm).run
#eval HAS_DERIVATIVE_POLAR_PATH

/- Continuity helper: (\z. c * z) continuous on (:complex)                   -/

#eval phrase 48
def CONTINUOUS_ON_COMPLEX_LMUL_FN : thm := keep "CONTINUOUS_ON_COMPLEX_LMUL_FN" fun _ => (do
  prove ([[!c:complex. (\z:complex. c * z) continuous_on (:complex)]])
   (GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
    MATCH_ACCEPT_TAC LINEAR_COMPLEX_MUL)
  : ExceptT String IO thm).run
#eval CONTINUOUS_ON_COMPLEX_LMUL_FN

/- Continuity: t -> ii * Cx(drop t) on (:real^1)                             -/

#eval phrase 49
def CONT_II_CX_DROP : thm := keep "CONT_II_CX_DROP" fun _ => (do
  prove ([[(\t:real^1. ii * Cx(drop t)) continuous_on (:real^1)]])
   (SUBGOAL_THEN ([[((\z:complex. ii * z) o (\t:real^1. Cx(drop t))) continuous_on (:real^1)]]) (fun th => HolLight.tactic_of do
        pure (ACCEPT_TAC (← HolLight.REWRITE_RULE [o_DEF] th))) THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_CX_DROP THEN REWRITE_TAC [CONTINUOUS_ON_ID],
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC ([[(:complex)]]) THEN
      REWRITE_TAC [SUBSET_UNIV, CONTINUOUS_ON_COMPLEX_LMUL_FN]])
  : ExceptT String IO thm).run
#eval CONT_II_CX_DROP

/- Continuity: t -> cexp(ii * Cx(drop t)) on (:real^1)                       -/

#eval phrase 50
def CONT_CEXP_POLAR : thm := keep "CONT_CEXP_POLAR" fun _ => (do
  prove ([[(\t:real^1. cexp(ii * Cx(drop t))) continuous_on (:real^1)]])
   (SUBGOAL_THEN ([[(cexp o (\t:real^1. ii * Cx(drop t))) continuous_on (:real^1)]]) (fun th => HolLight.tactic_of do
        pure (ACCEPT_TAC (← HolLight.REWRITE_RULE [o_DEF] th))) THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [REWRITE_TAC [CONT_II_CX_DROP],
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC ([[(:complex)]]) THEN
      REWRITE_TAC [SUBSET_UNIV, CONTINUOUS_ON_CEXP]])
  : ExceptT String IO thm).run
#eval CONT_CEXP_POLAR

/- Continuity: full polar path on (:real^1)                                  -/

#eval phrase 51
def CONTINUOUS_ON_POLAR_PATH : thm := keep "CONTINUOUS_ON_POLAR_PATH" fun _ => (do
  prove ([[!w:complex r.
     (\t. w + Cx r * cexp(ii * Cx(drop t))) continuous_on (:real^1)]])
   (REPEAT GEN_TAC THEN
    SUBGOAL_THEN ([[((\z:complex. w + Cx r * z) o (\t:real^1. cexp(ii * Cx(drop t))))
     continuous_on (:real^1)]]) (fun th => HolLight.tactic_of do
        pure (ACCEPT_TAC (← HolLight.REWRITE_RULE [o_DEF] th))) THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [REWRITE_TAC [CONT_CEXP_POLAR],
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC ([[(:complex)]]) THEN REWRITE_TAC [SUBSET_UNIV] THEN
      SUBGOAL_THEN ([[((\z:complex. w + z) o (\z:complex. Cx r * z)) continuous_on (:complex)]]) (fun th => HolLight.tactic_of do
        pure (ACCEPT_TAC (← HolLight.REWRITE_RULE [o_DEF] th))) THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [REWRITE_TAC [CONTINUOUS_ON_COMPLEX_LMUL_FN],
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC ([[(:complex)]]) THEN REWRITE_TAC [SUBSET_UNIV] THEN
        MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
        REWRITE_TAC [CONTINUOUS_ON_CONST, CONTINUOUS_ON_ID]]])
  : ExceptT String IO thm).run
#eval CONTINUOUS_ON_POLAR_PATH

/- Continuity on the interval [0, 2*pi]                                      -/

#eval phrase 52
def CONTINUOUS_ON_POLAR_PATH_INTERVAL : thm := keep "CONTINUOUS_ON_POLAR_PATH_INTERVAL" fun _ => (do
  prove ([[!w:complex r.
     (\t. w + Cx r * cexp(ii * Cx(drop t))) continuous_on
     interval[vec 0:real^1, lift(&2 * pi)] ]])
   (REPEAT GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC ([[(:real^1)]]) THEN
    REWRITE_TAC [SUBSET_UNIV, CONTINUOUS_ON_POLAR_PATH])
  : ExceptT String IO thm).run
#eval CONTINUOUS_ON_POLAR_PATH_INTERVAL

/- f composed with polar path continuous                                     -/

#eval phrase 53
def CONTINUOUS_ON_F_POLAR : thm := keep "CONTINUOUS_ON_F_POLAR" fun _ => (do
  prove ([[!f:complex->complex w r.
     f continuous_on (:complex)
     ==> (\t. f(w + Cx r * cexp(ii * Cx(drop t)))) continuous_on
         interval[vec 0:real^1, lift(&2 * pi)] ]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[((f:complex->complex) o
     (\t:real^1. w + Cx r * cexp(ii * Cx(drop t)))) continuous_on
     interval[vec 0:real^1, lift(&2 * pi)] ]]) (fun th => HolLight.tactic_of do
        pure (ACCEPT_TAC (← HolLight.REWRITE_RULE [o_DEF] th))) THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [REWRITE_TAC [CONTINUOUS_ON_POLAR_PATH_INTERVAL],
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC ([[(:complex)]]) THEN ASM_REWRITE_TAC [SUBSET_UNIV]])
  : ExceptT String IO thm).run
#eval CONTINUOUS_ON_F_POLAR

/- Vector derivative of f composed with polar path                           -/

#eval phrase 54
def HAS_VECTOR_DERIVATIVE_F_POLAR : thm := keep "HAS_VECTOR_DERIVATIVE_F_POLAR" fun _ => (do
  prove ([[!f:complex->complex w r t.
     f differentiable at (w + Cx r * cexp(ii * Cx(drop t)))
     ==> ((\t. f(w + Cx r * cexp(ii * Cx(drop t))))
          has_vector_derivative
          (frechet_derivative f (at (w + Cx r * cexp(ii * Cx(drop t))))
            (Cx r * cexp(ii * Cx(drop t)) * ii)))
         (at t)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [has_vector_derivative] THEN
    SUBGOAL_THEN ([[((\t:real^1. (f:complex->complex)(w + Cx r * cexp(ii * Cx(drop t))))
      has_derivative
      (\h. frechet_derivative f
             (at (w + Cx r * cexp(ii * Cx(drop(t:real^1)))))
             (Cx r * (cexp(ii * Cx(drop t)) * (ii * Cx(drop h))))))
     (at t)]]) MP_TAC THENL
     [SUBGOAL_THEN ([[(\t:real^1. (f:complex->complex)(w + Cx r * cexp(ii * Cx(drop t)))) =
       (f o (\t:real^1. w + Cx r * cexp(ii * Cx(drop t))))]]) SUBST1_TAC THENL [REWRITE_TAC [o_DEF], ALL_TAC] THEN
      SUBGOAL_THEN ([[(\h:real^1. frechet_derivative (f:complex->complex)
                    (at (w + Cx r * cexp(ii * Cx(drop(t:real^1)))))
                    (Cx r * (cexp(ii * Cx(drop t)) * (ii * Cx(drop h))))) =
       (frechet_derivative f (at (w + Cx r * cexp(ii * Cx(drop t)))) o
        (\h:real^1. Cx r * (cexp(ii * Cx(drop t)) * (ii * Cx(drop h)))))]]) SUBST1_TAC THENL [REWRITE_TAC [o_DEF], ALL_TAC] THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
       [REWRITE_TAC [HAS_DERIVATIVE_POLAR_PATH],
        FIRST_X_ASSUM (MP_TAC o
          HolLight.GEN_REWRITE_RULE HolCore.Lib.I [FRECHET_DERIVATIVE_WORKS]) THEN
        REWRITE_TAC []],
      DISCH_TAC THEN
      SUBGOAL_THEN ([[(\h:real^1. drop h % frechet_derivative (f:complex->complex)
                    (at (w + Cx r * cexp(ii * Cx(drop(t:real^1)))))
                    (Cx r * cexp(ii * Cx(drop t)) * ii)) =
       (\h:real^1. frechet_derivative f
                    (at (w + Cx r * cexp(ii * Cx(drop t))))
                    (Cx r * (cexp(ii * Cx(drop t)) * (ii * Cx(drop h)))))]]) SUBST1_TAC THENL
       [REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC ([[h:real^1]]) THEN
        SUBGOAL_THEN ([[Cx r * (cexp(ii * Cx(drop t)) * (ii * Cx(drop(h:real^1)))) =
         drop h % (Cx r * cexp(ii * Cx(drop t)) * ii)]]) SUBST1_TAC THENL
         [REWRITE_TAC [COMPLEX_CMUL, CX_DEF, complex_mul, RE, IM,
                      REAL_MUL_RZERO, REAL_SUB_RZERO, REAL_ADD_LID] THEN
          REWRITE_TAC [COMPLEX_EQ, RE, IM] THEN REAL_ARITH_TAC2,
          SUBGOAL_THEN ([[linear (frechet_derivative (f:complex->complex)
                  (at (w + Cx r * cexp(ii * Cx(drop(t:real^1))))))]]) (fun th => HolLight.tactic_of do
        pure (REWRITE_TAC [(← HolLight.MATCH_MP LINEAR_CMUL th)])) THEN
          MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC []],
        ASM_REWRITE_TAC []]])
  : ExceptT String IO thm).run
#eval HAS_VECTOR_DERIVATIVE_F_POLAR

/- Angular FTC: integral of derivative along polar path                      -/

#eval phrase 55
def ANGULAR_FTC : thm := keep "ANGULAR_FTC" fun _ => (do
  prove ([[!f:complex->complex w r.
     f continuous_on (:complex) /\
     f differentiable_on (:complex)
     ==> ((\t. frechet_derivative f (at (w + Cx r * cexp(ii * Cx(drop t))))
                (Cx r * cexp(ii * Cx(drop t)) * ii))
          has_integral
          (f(w + Cx r * cexp(ii * Cx(drop(lift(&2 * pi))))) -
           f(w + Cx r * cexp(ii * Cx(drop(vec 0))))))
         (interval[vec 0, lift(&2 * pi)])]])
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR THEN
    REWRITE_TAC [DROP_VEC, LIFT_DROP] THEN
    CONJ_TAC THENL
     [MP_TAC PI_POS THEN REAL_ARITH_TAC2, ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_F_POLAR THEN ASM_REWRITE_TAC [],
      X_GEN_TAC ([[t:real^1]]) THEN
      REWRITE_TAC [IN_INTERVAL_1, DROP_VEC, LIFT_DROP] THEN
      STRIP_TAC THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_F_POLAR THEN
      ASM_MESON_TAC [DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT,
                    OPEN_UNIV, IN_UNIV]])
  : ExceptT String IO thm).run
#eval ANGULAR_FTC

/- The angular integral is zero by 2*pi-periodicity of exp                   -/

#eval phrase 56
def ANGULAR_INTEGRAL_ZERO : thm := keep "ANGULAR_INTEGRAL_ZERO" fun _ => (do
  prove ([[!f:complex->complex w r.
     f continuous_on (:complex) /\
     f differentiable_on (:complex)
     ==> integral (interval[vec 0, lift(&2 * pi)])
           (\t. frechet_derivative f (at (w + Cx r * cexp(ii * Cx(drop t))))
                  (Cx r * cexp(ii * Cx(drop t)) * ii)) = vec 0]])
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC INTEGRAL_UNIQUE THEN
    MP_TAC (← HolLight.SPECL [([[f:complex->complex]]), ([[w:complex]]), ([[r:real]])] ANGULAR_FTC) THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [LIFT_DROP, DROP_VEC] THEN
    REWRITE_TAC [CEXP_2PII, CEXP_0II] THEN
    REWRITE_TAC [COMPLEX_MUL_RID, VECTOR_SUB_REFL])
  : ExceptT String IO thm).run
#eval ANGULAR_INTEGRAL_ZERO

/- ========================================================================= -/
/- Frechet derivative commutes with real scalar multiplication               -/
/- ========================================================================= -/

#eval phrase 57
def FRECHET_DERIVATIVE_CX_LMUL : thm := keep "FRECHET_DERIVATIVE_CX_LMUL" fun _ => (do
  prove ([[!f:complex->complex z c x.
     f differentiable at z
     ==> frechet_derivative f (at z) (Cx c * x) =
         Cx c * frechet_derivative f (at z) x]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[linear(frechet_derivative (f:complex->complex) (at z))]]) MP_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN ([[Cx c * (x:complex) = c % x]]) SUBST1_TAC THENL
     [REWRITE_TAC [COMPLEX_CMUL], ALL_TAC] THEN
    SUBGOAL_THEN ([[Cx c * frechet_derivative (f:complex->complex) (at z) x =
                c % frechet_derivative f (at z) x]]) SUBST1_TAC THENL
     [REWRITE_TAC [COMPLEX_CMUL], ALL_TAC] THEN
    ASM_MESON_TAC [LINEAR_CMUL])
  : ExceptT String IO thm).run
#eval FRECHET_DERIVATIVE_CX_LMUL

/- For r != 0, the angular integral of f'(z)(ii * exp(it)) is zero           -/

#eval phrase 58
def ANGULAR_INTEGRAL_II_ZERO : thm := keep "ANGULAR_INTEGRAL_II_ZERO" fun _ => (do
  prove ([[!f:complex->complex w r.
     f continuous_on (:complex) /\
     f differentiable_on (:complex) /\
     ~(r = &0)
     ==> integral (interval[vec 0, lift(&2 * pi)])
           (\t. frechet_derivative f
                  (at (w + Cx r * cexp(ii * Cx(drop t))))
                  (ii * cexp(ii * Cx(drop t)))) = vec 0]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [([[f:complex->complex]]), ([[w:complex]]), ([[r:real]])] ANGULAR_INTEGRAL_ZERO) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[!t:real^1. frechet_derivative (f:complex->complex)
                  (at (w + Cx r * cexp(ii * Cx(drop t))))
                  (Cx r * cexp(ii * Cx(drop t)) * ii) =
                Cx r * frechet_derivative f
                  (at (w + Cx r * cexp(ii * Cx(drop t))))
                  (ii * cexp(ii * Cx(drop t)))]]) (fun th => RULE_ASSUM_TAC (HolLight.REWRITE_RULE [th])) THENL
     [X_GEN_TAC ([[t:real^1]]) THEN
      SUBGOAL_THEN ([[Cx r * cexp(ii * Cx(drop t)) * ii =
       Cx r * (ii * cexp(ii * Cx(drop(t:real^1))))]]) SUBST1_TAC THENL
       [SIMPLE_COMPLEX_ARITH_TAC, ALL_TAC] THEN
      MATCH_MP_TAC FRECHET_DERIVATIVE_CX_LMUL THEN
      ASM_MESON_TAC [DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT, OPEN_UNIV, IN_UNIV],
      SUBGOAL_THEN ([[((\t. frechet_derivative (f:complex->complex)
               (at (w + Cx r * cexp(ii * Cx(drop t))))
               (ii * cexp(ii * Cx(drop t))))
       integrable_on (interval[vec 0, lift(&2 * pi)]))]]) ASSUME_TAC THENL
       [MP_TAC (← HolLight.SPECL [([[f:complex->complex]]), ([[w:complex]]), ([[r:real]])] ANGULAR_FTC) THEN
        ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
        SUBGOAL_THEN ([[!t:real^1.
        frechet_derivative (f:complex->complex)
          (at (w + Cx r * cexp(ii * Cx(drop t))))
          (Cx r * cexp(ii * Cx(drop t)) * ii) =
        Cx r * frechet_derivative f
          (at (w + Cx r * cexp(ii * Cx(drop t))))
          (ii * cexp(ii * Cx(drop t)))]]) (fun th => RULE_ASSUM_TAC (HolLight.REWRITE_RULE [th])) THENL
         [X_GEN_TAC ([[t:real^1]]) THEN
          SUBGOAL_THEN ([[Cx r * cexp(ii * Cx(drop t)) * ii =
                      Cx r * (ii * cexp(ii * Cx(drop(t:real^1))))]]) SUBST1_TAC THENL
           [SIMPLE_COMPLEX_ARITH_TAC, ALL_TAC] THEN
          MATCH_MP_TAC FRECHET_DERIVATIVE_CX_LMUL THEN
          ASM_MESON_TAC [DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT,
                         OPEN_UNIV, IN_UNIV],
          ALL_TAC] THEN
        FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP HAS_INTEGRAL_INTEGRABLE) THEN
        REWRITE_TAC [(← HolLight.GSYM COMPLEX_CMUL), INTEGRABLE_CMUL_EQ] THEN
        ASM_MESON_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[Cx r * integral (interval[vec 0, lift(&2 * pi)])
        (\t. frechet_derivative (f:complex->complex)
               (at (w + Cx r * cexp(ii * Cx(drop t))))
               (ii * cexp(ii * Cx(drop t)))) = vec 0]]) MP_TAC THENL
       [ASM_SIMP_TAC [(← HolLight.GSYM INTEGRAL_COMPLEX_LMUL)] THEN ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      REWRITE_TAC [COMPLEX_VEC_0, COMPLEX_ENTIRE, CX_INJ] THEN
      DISCH_THEN DISJ_CASES_TAC THENL
       [UNDISCH_TAC ([[~(r = &0)]]) THEN ASM_REWRITE_TAC [],
        ASM_REWRITE_TAC [(← HolLight.GSYM COMPLEX_VEC_0)]]])
  : ExceptT String IO thm).run
#eval ANGULAR_INTEGRAL_II_ZERO

/- ========================================================================= -/
/- Radial path lemmas for polar coordinates proof                            -/
/- ========================================================================= -/
/- Radial path: r -> w + Cx(drop r) * cexp(ii * Cx t0)  for fixed t0         -/

#eval phrase 59
def HAS_DERIVATIVE_RADIAL_PATH : thm := keep "HAS_DERIVATIVE_RADIAL_PATH" fun _ => (do
  prove ([[!w:complex t0:real r:real^1.
     ((\r. w + Cx(drop r) * cexp(ii * Cx t0)) has_derivative
      (\h. Cx(drop h) * cexp(ii * Cx t0))) (at r)]])
   (REPEAT GEN_TAC THEN
    SUBGOAL_THEN ([[((\r:real^1. w) has_derivative (\h:real^1. vec 0:complex)) (at r) /\
     ((\r:real^1. Cx(drop r) * cexp(ii * Cx t0)) has_derivative
      (\h:real^1. Cx(drop h) * cexp(ii * Cx t0))) (at r)]]) MP_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC [HAS_DERIVATIVE_CONST],
        SUBGOAL_THEN ([[(\r:real^1. Cx(drop r) * cexp(ii * Cx t0)) =
         ((\z:complex. cexp(ii * Cx t0) * z) o (\r:real^1. Cx(drop r)))]]) SUBST1_TAC THENL
         [REWRITE_TAC [o_DEF, COMPLEX_MUL_SYM], ALL_TAC] THEN
        SUBGOAL_THEN ([[(\h:real^1. Cx(drop h) * cexp(ii * Cx t0)) =
         ((\z:complex. cexp(ii * Cx t0) * z) o (\h:real^1. Cx(drop h)))]]) SUBST1_TAC THENL
         [REWRITE_TAC [o_DEF, COMPLEX_MUL_SYM], ALL_TAC] THEN
        MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
         [MESON_TAC [HAS_DERIVATIVE_CX_DROP],
          MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
          MATCH_ACCEPT_TAC LINEAR_COMPLEX_MUL]],
      DISCH_THEN (ACCEPT_TAC o HolLight.REWRITE_RULE [VECTOR_ADD_LID] o
        HolLight.MATCH_MP HAS_DERIVATIVE_ADD)])
  : ExceptT String IO thm).run
#eval HAS_DERIVATIVE_RADIAL_PATH

#eval phrase 60
def HAS_VECTOR_DERIVATIVE_F_RADIAL : thm := keep "HAS_VECTOR_DERIVATIVE_F_RADIAL" fun _ => (do
  prove ([[!f:complex->complex w t0 r.
     f differentiable at (w + Cx(drop r) * cexp(ii * Cx t0))
     ==> ((\r. f(w + Cx(drop r) * cexp(ii * Cx t0)))
          has_vector_derivative
          (frechet_derivative f (at (w + Cx(drop r) * cexp(ii * Cx t0)))
            (cexp(ii * Cx t0))))
         (at r)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [has_vector_derivative] THEN
    SUBGOAL_THEN ([[((\r:real^1. (f:complex->complex)(w + Cx(drop r) * cexp(ii * Cx t0)))
      has_derivative
      (\h. frechet_derivative f
             (at (w + Cx(drop(r:real^1)) * cexp(ii * Cx t0)))
             (Cx(drop h) * cexp(ii * Cx t0))))
     (at r)]]) MP_TAC THENL
     [SUBGOAL_THEN ([[(\r:real^1. (f:complex->complex)(w + Cx(drop r) * cexp(ii * Cx t0))) =
       (f o (\r:real^1. w + Cx(drop r) * cexp(ii * Cx t0)))]]) SUBST1_TAC THENL [REWRITE_TAC [o_DEF], ALL_TAC] THEN
      SUBGOAL_THEN ([[(\h:real^1. frechet_derivative (f:complex->complex)
                    (at (w + Cx(drop(r:real^1)) * cexp(ii * Cx t0)))
                    (Cx(drop h) * cexp(ii * Cx t0))) =
       (frechet_derivative f (at (w + Cx(drop r) * cexp(ii * Cx t0))) o
        (\h:real^1. Cx(drop h) * cexp(ii * Cx t0)))]]) SUBST1_TAC THENL [REWRITE_TAC [o_DEF], ALL_TAC] THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
       [REWRITE_TAC [HAS_DERIVATIVE_RADIAL_PATH],
        FIRST_X_ASSUM (MP_TAC o
          HolLight.GEN_REWRITE_RULE HolCore.Lib.I [FRECHET_DERIVATIVE_WORKS]) THEN
        REWRITE_TAC []],
      DISCH_TAC THEN
      SUBGOAL_THEN ([[(\h:real^1. drop h % frechet_derivative (f:complex->complex)
                    (at (w + Cx(drop(r:real^1)) * cexp(ii * Cx t0)))
                    (cexp(ii * Cx t0))) =
       (\h:real^1. frechet_derivative f
                    (at (w + Cx(drop r) * cexp(ii * Cx t0)))
                    (Cx(drop h) * cexp(ii * Cx t0)))]]) SUBST1_TAC THENL
       [REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC ([[h:real^1]]) THEN
        SUBGOAL_THEN ([[linear (frechet_derivative (f:complex->complex)
                (at (w + Cx(drop(r:real^1)) * cexp(ii * Cx t0))))]]) (fun th => HolLight.tactic_of do
        pure (REWRITE_TAC [(← HolLight.GSYM (← HolLight.MATCH_MP LINEAR_CMUL th))] THEN
            REWRITE_TAC [COMPLEX_CMUL])) THEN
        MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC [],
        ASM_REWRITE_TAC []]])
  : ExceptT String IO thm).run
#eval HAS_VECTOR_DERIVATIVE_F_RADIAL

/- The radial path is continuous                                             -/

#eval phrase 61
def CONTINUOUS_ON_RADIAL_PATH : thm := keep "CONTINUOUS_ON_RADIAL_PATH" fun _ => (do
  prove ([[!w:complex t0. (\r:real^1. w + Cx(drop r) * cexp(ii * Cx t0))
                  continuous_on (:real^1)]])
   (REPEAT GEN_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    REWRITE_TAC [CONTINUOUS_ON_CONST] THEN
    SUBGOAL_THEN ([[((\z:complex. z * cexp(ii * Cx t0)) o (\r:real^1. Cx(drop r)))
     continuous_on (:real^1)]]) (fun th => HolLight.tactic_of do
        pure (ACCEPT_TAC (← HolLight.REWRITE_RULE [o_DEF] th))) THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_CX_DROP THEN REWRITE_TAC [CONTINUOUS_ON_ID],
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC ([[(:complex)]]) THEN
      REWRITE_TAC [SUBSET_UNIV] THEN
      SUBGOAL_THEN ([[(\z:complex. z * cexp(ii * Cx t0)) =
                  (\z. cexp(ii * Cx t0) * z)]]) (fun th => REWRITE_TAC [th, CONTINUOUS_ON_COMPLEX_LMUL_FN]) THEN
      REWRITE_TAC [FUN_EQ_THM, COMPLEX_MUL_SYM]])
  : ExceptT String IO thm).run
#eval CONTINUOUS_ON_RADIAL_PATH

/- Continuity of f composed with radial path                                 -/

#eval phrase 62
def CONTINUOUS_ON_F_RADIAL : thm := keep "CONTINUOUS_ON_F_RADIAL" fun _ => (do
  prove ([[!f:complex->complex w t0.
     f continuous_on (:complex)
     ==> (\r. f(w + Cx(drop r) * cexp(ii * Cx t0))) continuous_on
         {r:real^1 | &0 <= drop r}]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[((f:complex->complex) o
     (\r:real^1. w + Cx(drop r) * cexp(ii * Cx t0))) continuous_on
     {r:real^1 | &0 <= drop r}]]) (fun th => HolLight.tactic_of do
        pure (ACCEPT_TAC (← HolLight.REWRITE_RULE [o_DEF] th))) THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC ([[(:real^1)]]) THEN
      REWRITE_TAC [SUBSET_UNIV, CONTINUOUS_ON_RADIAL_PATH],
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC ([[(:complex)]]) THEN
      ASM_REWRITE_TAC [SUBSET_UNIV]])
  : ExceptT String IO thm).run
#eval CONTINUOUS_ON_F_RADIAL

/- Radial FTC for f on [0, R]                                                -/

#eval phrase 63
def RADIAL_FTC : thm := keep "RADIAL_FTC" fun _ => (do
  prove ([[!f:complex->complex w t0 R.
     f continuous_on (:complex) /\
     f differentiable_on (:complex) /\
     &0 < R
     ==> ((\r. frechet_derivative f
                (at (w + Cx(drop r) * cexp(ii * Cx t0)))
                (cexp(ii * Cx t0)))
          has_integral
          (f(w + Cx R * cexp(ii * Cx t0)) - f(w)))
         (interval[vec 0, lift R])]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[((\r:real^1. frechet_derivative (f:complex->complex)
                   (at (w + Cx(drop r) * cexp(ii * Cx t0)))
                   (cexp(ii * Cx t0)))
      has_integral
      (f(w + Cx(drop(lift R)) * cexp(ii * Cx t0)) -
       f(w + Cx(drop(vec 0:real^1)) * cexp(ii * Cx t0))))
     (interval[vec 0, lift R])]]) MP_TAC THENL
     [MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR THEN
      REWRITE_TAC [DROP_VEC, LIFT_DROP] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC ([[{r:real^1 | &0 <= drop r}]]) THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_F_RADIAL THEN ASM_REWRITE_TAC [],
          REWRITE_TAC [SUBSET, IN_INTERVAL_1, IN_ELIM_THM, DROP_VEC, LIFT_DROP] THEN
          REAL_ARITH_TAC2],
        X_GEN_TAC ([[r:real^1]]) THEN
        REWRITE_TAC [IN_INTERVAL_1, DROP_VEC, LIFT_DROP] THEN
        STRIP_TAC THEN
        MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_F_RADIAL THEN
        ASM_MESON_TAC [DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT,
                      OPEN_UNIV, IN_UNIV]],
      REWRITE_TAC [DROP_VEC, LIFT_DROP, COMPLEX_MUL_LZERO, COMPLEX_ADD_RID]])
  : ExceptT String IO thm).run
#eval RADIAL_FTC

/- For r > 0, the inner polar integral simplifies:                           -/
/- drop r % (dbar f z / (Cx(drop r) * cexp)) =                               -/
/-   inv(Cx 2) * integral [0,2pi] f'(z)(cexp)                                -/
/- Uses: POLAR_CEXP_SIMPLIFY + WIRTINGER_DBAR_FRECHET_POLAR +                -/
/-       ANGULAR_INTEGRAL_II_ZERO                                            -/

#eval phrase 64
def INNER_INTEGRAL_SIMPLIFY : thm := keep "INNER_INTEGRAL_SIMPLIFY" fun _ => (do
  let h1 ← cf (← ExceptT.mk [[~(Cx(&2) = Cx(&0)) /\ f1 + ii * f2 = Cx(&2) * d * c
       ==> d * c = inv(Cx(&2)) * (f1 + ii * f2)]])
  prove ([[!f:complex->complex w r.
     f continuous_on (:complex) /\
     f differentiable_on (:complex) /\
     (!h. (\z. frechet_derivative f (at z) h) continuous_on (:complex)) /\
     &0 < drop r
     ==> integral (interval[vec 0, lift(&2 * pi)])
           (\t. drop r %
                (wirtinger_dbar f (w + Cx(drop r) * cexp(ii * Cx(drop t))) /
                 (Cx(drop r) * cexp(ii * Cx(drop t))))) =
         inv(Cx(&2)) *
         integral (interval[vec 0, lift(&2 * pi)])
           (\t. frechet_derivative f
                  (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
                  (cexp(ii * Cx(drop t))))]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[!t:real^1.
       drop r %
       (wirtinger_dbar (f:complex->complex)
          (w + Cx(drop r) * cexp(ii * Cx(drop t))) /
        (Cx(drop r) * cexp(ii * Cx(drop t)))) =
       inv(Cx(&2)) *
       (frechet_derivative f
          (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
          (cexp(ii * Cx(drop t))) +
        ii * frechet_derivative f
          (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
          (ii * cexp(ii * Cx(drop t))))]]) ASSUME_TAC THENL
     [X_GEN_TAC ([[t:real^1]]) THEN
      ASM_SIMP_TAC [POLAR_CEXP_SIMPLIFY] THEN
      MATCH_MP_TAC h1 THEN
      CONJ_TAC THENL
       [REWRITE_TAC [CX_INJ] THEN REAL_ARITH_TAC2,
        MATCH_MP_TAC WIRTINGER_DBAR_FRECHET_POLAR THEN
        ASM_MESON_TAC [DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT, OPEN_UNIV, IN_UNIV]],
      ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN ([[((\t:real^1. frechet_derivative (f:complex->complex)
          (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
          (cexp(ii * Cx(drop t))) +
        ii * frechet_derivative f
          (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
          (ii * cexp(ii * Cx(drop t))))
       integrable_on (interval[vec 0, lift(&2 * pi)]))]]) ASSUME_TAC THENL
       [SUBGOAL_THEN ([[(\t:real^1. frechet_derivative (f:complex->complex)
           (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
           (cexp(ii * Cx(drop t))) +
         ii * frechet_derivative f
           (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
           (ii * cexp(ii * Cx(drop t)))) =
         (\t. Cx(&2) * wirtinger_dbar f
                (w + Cx(drop r) * cexp(ii * Cx(drop t))) *
              cnj(cexp(ii * Cx(drop t))))]]) SUBST1_TAC THENL
         [REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC ([[t:real^1]]) THEN
          MATCH_MP_TAC WIRTINGER_DBAR_FRECHET_POLAR THEN
          ASM_MESON_TAC [DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT,
                         OPEN_UNIV, IN_UNIV],
          ALL_TAC] THEN
        MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
         [REWRITE_TAC [CONTINUOUS_ON_CONST],
          MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
           [SUBGOAL_THEN ([[(\t:real^1. wirtinger_dbar (f:complex->complex)
               (w + Cx(drop r) * cexp(ii * Cx(drop t)))) =
             ((\z. wirtinger_dbar f z) o
              (\t. w + Cx(drop r) * cexp(ii * Cx(drop t))))]]) SUBST1_TAC THENL
             [REWRITE_TAC [o_DEF], ALL_TAC] THEN
            MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
             [REWRITE_TAC [CONTINUOUS_ON_POLAR_PATH_INTERVAL], ALL_TAC] THEN
            MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
            EXISTS_TAC ([[(:complex)]]) THEN
            REWRITE_TAC [SUBSET_UNIV] THEN
            MATCH_MP_TAC WIRTINGER_DBAR_CONTINUOUS THEN
            ASM_REWRITE_TAC [],
            SUBGOAL_THEN ([[(\t:real^1. cnj(cexp(ii * Cx(drop t)))) =
             (cnj o (\t. cexp(ii * Cx(drop t))))]]) SUBST1_TAC THENL
             [REWRITE_TAC [o_DEF], ALL_TAC] THEN
            MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
             [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
              EXISTS_TAC ([[(:real^1)]]) THEN
              REWRITE_TAC [SUBSET_UNIV, CONT_CEXP_POLAR],
              REWRITE_TAC [CONTINUOUS_ON_CNJ]]]],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[integral (interval[vec 0, lift(&2 * pi)])
        (\t:real^1. inv(Cx(&2)) *
          (frechet_derivative (f:complex->complex)
            (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
            (cexp(ii * Cx(drop t))) +
           ii * frechet_derivative f
            (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
            (ii * cexp(ii * Cx(drop t))))) =
       inv(Cx(&2)) *
       integral (interval[vec 0, lift(&2 * pi)])
        (\t:real^1. frechet_derivative (f:complex->complex)
            (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
            (cexp(ii * Cx(drop t))) +
           ii * frechet_derivative f
            (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
            (ii * cexp(ii * Cx(drop t))))]]) SUBST1_TAC THENL
       [MATCH_MP_TAC INTEGRAL_COMPLEX_LMUL THEN ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      AP_TERM_TAC THEN
      SUBGOAL_THEN ([[((\t:real^1. frechet_derivative (f:complex->complex)
          (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
          (cexp(ii * Cx(drop t))))
       integrable_on (interval[vec 0, lift(&2 * pi)])) /\
       ((\t:real^1. ii * frechet_derivative (f:complex->complex)
          (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
          (ii * cexp(ii * Cx(drop t))))
       integrable_on (interval[vec 0, lift(&2 * pi)]))]]) STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN ([[((\t:real^1. frechet_derivative (f:complex->complex)
            (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
            (ii * cexp(ii * Cx(drop t))))
         integrable_on (interval[vec 0, lift(&2 * pi)]))]]) ASSUME_TAC THENL
         [SUBGOAL_THEN ([[~(drop(r:real^1) = &0)]]) ASSUME_TAC THENL
           [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
          MP_TAC (← HolLight.SPECL [([[f:complex->complex]]), ([[w:complex]]), ([[drop(r:real^1)]])] ANGULAR_FTC) THEN
          ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
          SUBGOAL_THEN ([[!t:real^1.
          frechet_derivative (f:complex->complex)
            (at (w + Cx(drop(r:real^1)) * cexp(ii * Cx(drop t))))
            (Cx(drop r) * cexp(ii * Cx(drop t)) * ii) =
          Cx(drop r) * frechet_derivative f
            (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
            (ii * cexp(ii * Cx(drop t)))]]) (fun th => RULE_ASSUM_TAC (HolLight.REWRITE_RULE [th])) THENL
           [X_GEN_TAC ([[t':real^1]]) THEN
            SUBGOAL_THEN ([[Cx(drop(r:real^1)) * cexp(ii * Cx(drop t')) * ii =
             Cx(drop r) * (ii * cexp(ii * Cx(drop(t':real^1))))]]) SUBST1_TAC THENL
             [SIMPLE_COMPLEX_ARITH_TAC, ALL_TAC] THEN
            MATCH_MP_TAC FRECHET_DERIVATIVE_CX_LMUL THEN
            ASM_MESON_TAC [DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT,
                           OPEN_UNIV, IN_UNIV],
            ALL_TAC] THEN
          FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP HAS_INTEGRAL_INTEGRABLE) THEN
          REWRITE_TAC [(← HolLight.GSYM COMPLEX_CMUL), INTEGRABLE_CMUL_EQ] THEN
          ASM_MESON_TAC [],
          ALL_TAC] THEN
        SUBGOAL_THEN ([[((\t:real^1. ii * frechet_derivative (f:complex->complex)
            (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
            (ii * cexp(ii * Cx(drop t))))
         integrable_on (interval[vec 0, lift(&2 * pi)]))]]) ASSUME_TAC THENL
         [SUBGOAL_THEN ([[(\t:real^1. ii * frechet_derivative (f:complex->complex)
              (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
              (ii * cexp(ii * Cx(drop t)))) =
           ((\x:complex. ii * x) o
            (\t. frechet_derivative f
              (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
              (ii * cexp(ii * Cx(drop t)))))]]) SUBST1_TAC THENL
           [REWRITE_TAC [o_DEF], ALL_TAC] THEN
          MATCH_MP_TAC INTEGRABLE_LINEAR THEN
          ASM_REWRITE_TAC [LINEAR_COMPLEX_MUL],
          ALL_TAC] THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN ([[(\t:real^1. frechet_derivative (f:complex->complex)
              (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
              (cexp(ii * Cx(drop t)))) =
           (\t. (frechet_derivative (f:complex->complex)
              (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
              (cexp(ii * Cx(drop t))) +
            ii * frechet_derivative f
              (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
              (ii * cexp(ii * Cx(drop t)))) -
            ii * frechet_derivative f
              (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
              (ii * cexp(ii * Cx(drop t))))]]) SUBST1_TAC THENL
           [REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC ([[t':real^1]]) THEN
            CONV_TAC cr,
            ALL_TAC] THEN
          MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC [],
          ASM_REWRITE_TAC []],
        ALL_TAC] THEN
      ASM_SIMP_TAC [INTEGRAL_ADD] THEN
      SUBGOAL_THEN ([[~(drop(r:real^1) = &0)]]) ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      MP_TAC (← HolLight.SPECL [([[f:complex->complex]]), ([[w:complex]]), ([[drop(r:real^1)]])] ANGULAR_INTEGRAL_II_ZERO) THEN
      ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
      SUBGOAL_THEN ([[((\t:real^1. frechet_derivative (f:complex->complex)
          (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
          (ii * cexp(ii * Cx(drop t))))
       integrable_on (interval[vec 0, lift(&2 * pi)]))]]) ASSUME_TAC THENL
       [MP_TAC (← HolLight.SPECL [([[f:complex->complex]]), ([[w:complex]]), ([[drop(r:real^1)]])] ANGULAR_FTC) THEN
        ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
        SUBGOAL_THEN ([[!t:real^1.
        frechet_derivative (f:complex->complex)
          (at (w + Cx(drop(r:real^1)) * cexp(ii * Cx(drop t))))
          (Cx(drop r) * cexp(ii * Cx(drop t)) * ii) =
        Cx(drop r) * frechet_derivative f
          (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
          (ii * cexp(ii * Cx(drop t)))]]) (fun th => RULE_ASSUM_TAC (HolLight.REWRITE_RULE [th])) THENL
         [X_GEN_TAC ([[t':real^1]]) THEN
          SUBGOAL_THEN ([[Cx(drop(r:real^1)) * cexp(ii * Cx(drop t')) * ii =
                      Cx(drop r) * (ii * cexp(ii * Cx(drop(t':real^1))))]]) SUBST1_TAC THENL
           [SIMPLE_COMPLEX_ARITH_TAC, ALL_TAC] THEN
          MATCH_MP_TAC FRECHET_DERIVATIVE_CX_LMUL THEN
          ASM_MESON_TAC [DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT,
                         OPEN_UNIV, IN_UNIV],
          ALL_TAC] THEN
        FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP HAS_INTEGRAL_INTEGRABLE) THEN
        REWRITE_TAC [(← HolLight.GSYM COMPLEX_CMUL), INTEGRABLE_CMUL_EQ] THEN
        ASM_MESON_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[integral (interval[vec 0, lift(&2 * pi)])
        (\t:real^1. ii * frechet_derivative (f:complex->complex)
          (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
          (ii * cexp(ii * Cx(drop t)))) = vec 0]]) (fun th => REWRITE_TAC [th, VECTOR_ADD_RID]) THEN
      SUBGOAL_THEN ([[integral (interval[vec 0, lift(&2 * pi)])
        (\t:real^1. ii * frechet_derivative (f:complex->complex)
          (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
          (ii * cexp(ii * Cx(drop t)))) =
       ii * integral (interval[vec 0, lift(&2 * pi)])
        (\t. frechet_derivative (f:complex->complex)
          (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
          (ii * cexp(ii * Cx(drop t))))]]) SUBST1_TAC THENL
       [MATCH_MP_TAC INTEGRAL_COMPLEX_LMUL THEN ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      ASM_REWRITE_TAC [COMPLEX_VEC_0, COMPLEX_MUL_RZERO]])
  : ExceptT String IO thm).run
#eval INNER_INTEGRAL_SIMPLIFY

/- For each fixed angle t, the radial integral from 0 to infinity            -/
/- of the radial derivative equals -f(w) (by FTC + compact support).         -/

#eval phrase 65
def RADIAL_INTEGRAL_NEG_FW : thm := keep "RADIAL_INTEGRAL_NEG_FW" fun _ => (do
  let h2 ← cr (← ExceptT.mk [[x - (w + x):complex = --w]])
  let h1 ← tt (← ExceptT.mk [[(~p ==> F) ==> p]])
  prove ([[!f:complex->complex w t0.
     f continuous_on (:complex) /\
     f differentiable_on (:complex) /\
     bounded (support (+) f (:complex))
     ==> integral {r:real^1 | &0 <= drop r}
           (\r. frechet_derivative f
                  (at (w + Cx(drop r) * cexp(ii * Cx t0)))
                  (cexp(ii * Cx t0))) = --(f w)]])
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [BOUNDED_POS]) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[R:real]]) STRIP_ASSUME_TAC) THEN
    ABBREV_TAC ([[B = R + norm(w:complex) + &1]]) THEN
    SUBGOAL_THEN ([[((\r:real^1. frechet_derivative (f:complex->complex)
                    (at (w + Cx(drop r) * cexp(ii * Cx t0)))
                    (cexp(ii * Cx t0)))
     has_integral --(f w)) {r:real^1 | &0 <= drop r}]]) (fun th => HolLight.tactic_of do
        pure (REWRITE_TAC [(← HolLight.MATCH_MP INTEGRAL_UNIQUE th)])) THEN
    REWRITE_TAC [HAS_INTEGRAL_LIM_AT_POSINFINITY] THEN
    CONJ_TAC THENL
     [X_GEN_TAC ([[a:real^1]]) THEN
      ASM_CASES_TAC ([[drop(a:real^1) <= &0]]) THENL
       [MATCH_MP_TAC INTEGRABLE_ON_NULL THEN
        REWRITE_TAC [CONTENT_EQ_0_1, DROP_VEC] THEN ASM_REAL_ARITH_TAC,
        MATCH_MP_TAC HAS_INTEGRAL_INTEGRABLE THEN
        EXISTS_TAC ([[(f:complex->complex)(w + Cx(drop(a:real^1)) * cexp(ii * Cx t0)) - f w]]) THEN
        MP_TAC (← HolLight.SPECL [([[f:complex->complex]]), ([[w:complex]]), ([[t0:real]]),
                       ([[drop(a:real^1)]])] RADIAL_FTC) THEN
        ASM_REWRITE_TAC [] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
        REWRITE_TAC [LIFT_DROP]],
      ALL_TAC] THEN
    REWRITE_TAC [LIM_AT_POSINFINITY] THEN
    X_GEN_TAC ([[e:real]]) THEN DISCH_TAC THEN
    EXISTS_TAC ([[B:real]]) THEN
    X_GEN_TAC ([[a:real]]) THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[&0 < a]]) ASSUME_TAC THENL
     [MP_TAC (← HolLight.ISPEC ([[w:complex]]) NORM_POS_LE) THEN ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[integral (interval[vec 0:real^1, lift a])
      (\r. frechet_derivative (f:complex->complex)
             (at (w + Cx(drop r) * cexp(ii * Cx t0)))
             (cexp(ii * Cx t0))) =
     f(w + Cx a * cexp(ii * Cx t0)) - f w]]) SUBST1_TAC THENL
     [MATCH_MP_TAC INTEGRAL_UNIQUE THEN
      MATCH_MP_TAC RADIAL_FTC THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[(f:complex->complex)(w + Cx a * cexp(ii * Cx t0)) = vec 0]]) SUBST1_TAC THENL
     [MATCH_MP_TAC h1 THEN DISCH_TAC THEN
      SUBGOAL_THEN ([[norm(w + Cx a * cexp(ii * Cx t0):complex) <= R]]) MP_TAC THENL
       [SUBGOAL_THEN ([[w + Cx a * cexp(ii * Cx t0) IN
         support (+) (f:complex->complex) (:complex)]]) MP_TAC THENL
         [REWRITE_TAC [IN_SUPPORT, IN_UNIV, NEUTRAL_VECTOR_ADD] THEN
          ASM_REWRITE_TAC [],
          ASM_MESON_TAC []],
        ALL_TAC] THEN
      MP_TAC (← HolLight.ISPECL [([[Cx a * cexp(ii * Cx t0)]]),
                      ([[w + Cx a * cexp(ii * Cx t0):complex]])] NORM_TRIANGLE_SUB) THEN
      REWRITE_TAC [h2, NORM_NEG] THEN
      REWRITE_TAC [COMPLEX_NORM_MUL, NORM_CEXP_II, COMPLEX_NORM_CX,
                  REAL_MUL_RID] THEN
      MP_TAC (← HolLight.ISPEC ([[w:complex]]) NORM_POS_LE) THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [VECTOR_SUB_LZERO, SessionMultiLib.Vectors.DIST_REFL] THEN
    ASM_REAL_ARITH_TAC)
  : ExceptT String IO thm).run
#eval RADIAL_INTEGRAL_NEG_FW

/- Helper: in real^1, nonneg and nonzero means positive                      -/

#eval phrase 66
def DROP_POS_OF_NONNEG_NZ : thm := keep "DROP_POS_OF_NONNEG_NZ" fun _ => (do
  prove ([[!r:real^1. &0 <= drop r /\ ~(r = vec 0) ==> &0 < drop r]])
   (GEN_TAC THEN REWRITE_TAC [CART_EQ, DIMINDEX_1, FORALL_1,
      VEC_COMPONENT, drop] THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval DROP_POS_OF_NONNEG_NZ

/- ------------------------------------------------------------------------- -/
/- Helpers for Fubini swap of polar integrals.                               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 67
def WIRTINGER_DZ_FRECHET : thm := keep "WIRTINGER_DZ_FRECHET" fun _ => (do
  prove ([[!f:complex->complex z.
        wirtinger_dz f z =
        (frechet_derivative f (at z) (Cx(&1)) -
         ii * frechet_derivative f (at z) ii) / Cx(&2)]])
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [wirtinger_dz, jacobian, COMPLEX_EQ] THEN
    REWRITE_TAC [complex_add, complex_sub, complex_mul, complex_neg,
                RE, IM, RE_DIV_CX, IM_DIV_CX, ii, CX_DEF, complex] THEN
    REWRITE_TAC [RE_DEF, IM_DEF] THEN
    SIMP_TAC [MATRIX_COMPONENT, DIMINDEX_2, ARITH] THEN
    SIMP_TAC [LAMBDA_BETA, DIMINDEX_2, ARITH, VECTOR_2] THEN
    REWRITE_TAC [COMPLEX_BASIS] THEN
    REWRITE_TAC [(← HolLight.GSYM RE_DEF), (← HolLight.GSYM IM_DEF), ii, CX_DEF, complex] THEN
    REWRITE_TAC [RE_DEF, IM_DEF] THEN
    SIMP_TAC [VECTOR_2, LAMBDA_BETA, DIMINDEX_2, ARITH] THEN
    REWRITE_TAC [(← HolLight.GSYM RE_DEF), (← HolLight.GSYM IM_DEF)] THEN
    REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval WIRTINGER_DZ_FRECHET

#eval phrase 68
def WIRTINGER_DZ_CONTINUOUS : thm := keep "WIRTINGER_DZ_CONTINUOUS" fun _ => (do
  prove ([[!f:complex->complex s.
        (!h. (\z. frechet_derivative f (at z) h) continuous_on s)
        ==> (\z. wirtinger_dz f z) continuous_on s]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [WIRTINGER_DZ_FRECHET] THEN
    REWRITE_TAC [complex_div] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_RMUL THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[Cx(&1)]])) THEN REWRITE_TAC [],
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[ii]])) THEN REWRITE_TAC []])
  : ExceptT String IO thm).run
#eval WIRTINGER_DZ_CONTINUOUS

#eval phrase 69
def FRECHET_CONTINUOUS_ON_JOINT : thm := keep "FRECHET_CONTINUOUS_ON_JOINT" fun _ => (do
  prove ([[!f:complex->complex (g:real^P->complex) (h:real^P->complex) s.
        f differentiable_on (:complex) /\
        (!e. (\z. frechet_derivative f (at z) e) continuous_on (:complex)) /\
        g continuous_on s /\
        h continuous_on s
        ==> (\x. frechet_derivative f (at (g x)) (h x)) continuous_on s]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[!z:complex. (f:complex->complex) differentiable (at z)]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT, OPEN_UNIV, IN_UNIV],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[(\x:real^P. frechet_derivative (f:complex->complex)
          (at ((g:real^P->complex) x)) ((h:real^P->complex) x)) =
     (\x. wirtinger_dz f (g x) * h x + wirtinger_dbar f (g x) * cnj(h x))]]) SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC ([[x:real^P]]) THEN
      MP_TAC (← HolLight.ISPECL [([[f:complex->complex]]),
                     ([[frechet_derivative (f:complex->complex)
                      (at ((g:real^P->complex) x))]]),
                     ([[(g:real^P->complex) x]])] FRECHET_WIRTINGER) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [(← HolLight.GSYM FRECHET_DERIVATIVE_WORKS)],
        DISCH_THEN (fun th => REWRITE_TAC [th])],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[wirtinger_dz (f:complex->complex) continuous_on (:complex)]]) ASSUME_TAC THENL
     [MATCH_MP_TAC (← HolLight.REWRITE_RULE [ETA_AX] WIRTINGER_DZ_CONTINUOUS) THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[wirtinger_dbar (f:complex->complex) continuous_on (:complex)]]) ASSUME_TAC THENL
     [MATCH_MP_TAC (← HolLight.REWRITE_RULE [ETA_AX] WIRTINGER_DBAR_CONTINUOUS) THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM o_DEF)] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC ([[(:complex)]]) THEN ASM_REWRITE_TAC [SUBSET_UNIV],
        ASM_REWRITE_TAC [ETA_AX]],
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM o_DEF)] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC ([[(:complex)]]) THEN ASM_REWRITE_TAC [SUBSET_UNIV],
        GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM o_DEF)] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        ASM_REWRITE_TAC [ETA_AX, CONTINUOUS_ON_CNJ]]])
  : ExceptT String IO thm).run
#eval FRECHET_CONTINUOUS_ON_JOINT

#eval phrase 70
def CONTINUOUS_ON_CEXP_SNDCART : thm := keep "CONTINUOUS_ON_CEXP_SNDCART" fun _ => (do
  prove ([[!s. (\z:real^(1,1)finite_sum.
          cexp(ii * Cx(drop(sndcart z)))) continuous_on s]])
   (GEN_TAC THEN GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM o_DEF)] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    REWRITE_TAC [CONTINUOUS_ON_CEXP] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
    MATCH_MP_TAC CONTINUOUS_ON_CX_DROP THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC [LINEAR_SNDCART])
  : ExceptT String IO thm).run
#eval CONTINUOUS_ON_CEXP_SNDCART

#eval phrase 71
def CONTINUOUS_ON_POLAR_PASTECART : thm := keep "CONTINUOUS_ON_POLAR_PASTECART" fun _ => (do
  prove ([[!w:complex s.
     (\z:real^(1,1)finite_sum.
        w + Cx(drop(fstcart z)) * cexp(ii * Cx(drop(sndcart z))))
     continuous_on s]])
   (REPEAT GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THENL
     [REWRITE_TAC [CONTINUOUS_ON_CONST],
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_CX_DROP THEN
        MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC [LINEAR_FSTCART],
        REWRITE_TAC [CONTINUOUS_ON_CEXP_SNDCART]]])
  : ExceptT String IO thm).run
#eval CONTINUOUS_ON_POLAR_PASTECART

#eval phrase 72
def FRECHET_DERIVATIVE_ZERO_OUTSIDE : thm := keep "FRECHET_DERIVATIVE_ZERO_OUTSIDE" fun _ => (do
  prove ([[!f:real^M->real^N z h R.
    f differentiable_on (:real^M) /\
    (!y. R < norm y ==> f y = vec 0) /\
    R < norm z
    ==> frechet_derivative f (at z) h = vec 0]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[(f has_derivative (\h:real^M. vec 0:real^N)) (at (z:real^M))]]) ASSUME_TAC THENL
     [MP_TAC (← HolLight.ISPECL [([[\y:real^M. vec 0:real^N]]), ([[\h:real^M. vec 0:real^N]]),
                      ([[f:real^M->real^N]]), ([[z:real^M]]),
                      ([[(norm(z:real^M) - R) / &2]])] HAS_DERIVATIVE_TRANSFORM_AT) THEN
      REWRITE_TAC [HAS_DERIVATIVE_CONST] THEN ANTS_TAC THENL
       [CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
        X_GEN_TAC ([[y:real^M]]) THEN REWRITE_TAC [SessionMultiLib.Vectors.dist] THEN DISCH_TAC THEN
        CONV_TAC HolLight.SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        MP_TAC (← HolLight.ISPECL [([[z:real^M]]), ([[y:real^M]])] NORM_TRIANGLE_SUB) THEN
        REWRITE_TAC [NORM_SUB] THEN ASM_REAL_ARITH_TAC,
        REWRITE_TAC []],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
        pure (REWRITE_TAC [(← HolLight.GSYM th)])))
  : ExceptT String IO thm).run
#eval FRECHET_DERIVATIVE_ZERO_OUTSIDE

#eval phrase 73
def ZERO_OUTSIDE_SUPPORT_BALL : thm := keep "ZERO_OUTSIDE_SUPPORT_BALL" fun _ => (do
  let h1 ← tt (← ExceptT.mk [[(~p ==> F) ==> p]])
  prove ([[!f:real^M->real^N R.
    (!x. x IN support (+) f (:real^M) ==> norm x <= R)
    ==> (!y. R < norm y ==> f y = vec 0)]])
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC h1 THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[y IN support (+) (f:real^M->real^N) (:real^M)]]) MP_TAC THENL
     [REWRITE_TAC [IN_SUPPORT, IN_UNIV, NEUTRAL_VECTOR_ADD] THEN
      ASM_REWRITE_TAC [],
      DISCH_THEN (fun th => FIRST_ASSUM (MP_TAC o HolCore.Lib.C HolLight.MATCH_MP th)) THEN
      ASM_REAL_ARITH_TAC])
  : ExceptT String IO thm).run
#eval ZERO_OUTSIDE_SUPPORT_BALL

#eval phrase 74
def POLAR_POINT_NORM_BOUND : thm := keep "POLAR_POINT_NORM_BOUND" fun _ => (do
  let h1 ← cr (← ExceptT.mk [[x - (w + x):complex = --w]])
  prove ([[!w:complex r:real^1 t:real^1 R.
    R + norm w + &1 <= drop r
    ==> R < norm(w + Cx(drop r) * cexp(ii * Cx(drop t)))]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[Cx(drop(r:real^1)) * cexp(ii * Cx(drop(t:real^1)))]]),
                    ([[w + Cx(drop(r:real^1)) * cexp(ii * Cx(drop(t:real^1)))]])] NORM_TRIANGLE_SUB) THEN
    REWRITE_TAC [h1, NORM_NEG] THEN
    REWRITE_TAC [COMPLEX_NORM_MUL, NORM_CEXP_II, COMPLEX_NORM_CX,
                REAL_MUL_RID] THEN
    MP_TAC (← HolLight.ISPEC ([[w:complex]]) NORM_POS_LE) THEN ASM_REAL_ARITH_TAC)
  : ExceptT String IO thm).run
#eval POLAR_POINT_NORM_BOUND

#eval phrase 75
def POLAR_FUBINI_SWAP : thm := keep "POLAR_FUBINI_SWAP" fun _ => (do
  prove ([[!f:complex->complex w.
     f continuous_on (:complex) /\
     f differentiable_on (:complex) /\
     (!h. (\z. frechet_derivative f (at z) h) continuous_on (:complex)) /\
     bounded (support (+) f (:complex))
     ==>
     integral {r:real^1 | &0 <= drop r}
       (\r. integral (interval[vec 0, lift(&2 * pi)])
              (\t. frechet_derivative f
                     (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
                     (cexp(ii * Cx(drop t))))) =
     integral (interval[vec 0, lift(&2 * pi)])
       (\t. integral {r:real^1 | &0 <= drop r}
              (\r. frechet_derivative f
                     (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
                     (cexp(ii * Cx(drop t)))))]])
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [BOUNDED_POS]) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[R:real]]) STRIP_ASSUME_TAC) THEN
    ABBREV_TAC ([[B = R + norm(w:complex) + &1]]) THEN
    SUBGOAL_THEN ([[&0 < B]]) ASSUME_TAC THENL
     [EXPAND_TAC "B" THEN MP_TAC (← HolLight.ISPEC ([[w:complex]]) NORM_POS_LE) THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    MP_TAC (← HolLight.ISPECL [([[f:complex->complex]]), ([[R:real]])] ZERO_OUTSIDE_SUPPORT_BALL) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[!r:real^1 t:real^1. B < drop r ==>
       frechet_derivative (f:complex->complex)
         (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
         (cexp(ii * Cx(drop t))) = vec 0]]) ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC FRECHET_DERIVATIVE_ZERO_OUTSIDE THEN
      EXISTS_TAC ([[R:real]]) THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC POLAR_POINT_NORM_BOUND THEN
      EXPAND_TAC "B" THEN ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[integral {r:real^1 | &0 <= drop r}
       (\r. integral (interval[vec 0, lift(&2 * pi)])
              (\t. frechet_derivative (f:complex->complex)
                     (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
                     (cexp(ii * Cx(drop t))))) =
     integral (interval[vec 0:real^1, lift B])
       (\r. integral (interval[vec 0, lift(&2 * pi)])
              (\t. frechet_derivative f
                     (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
                     (cexp(ii * Cx(drop t)))))]]) SUBST1_TAC THENL
     [ONCE_REWRITE_TAC [(← HolLight.GSYM INTEGRAL_RESTRICT_UNIV)] THEN
      AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN
      X_GEN_TAC ([[r:real^1]]) THEN
      REWRITE_TAC [IN_ELIM_THM, IN_INTERVAL_1, DROP_VEC, LIFT_DROP] THEN
      ASM_CASES_TAC ([[&0 <= drop(r:real^1)]]) THEN ASM_REWRITE_TAC [] THEN
      ASM_CASES_TAC ([[drop(r:real^1) <= B]]) THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN ([[!t:real^1.
      frechet_derivative (f:complex->complex)
        (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
        (cexp(ii * Cx(drop t))) = vec 0]]) (fun th => REWRITE_TAC [th, INTEGRAL_0]) THEN
      GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[integral (interval[vec 0, lift(&2 * pi)])
       (\t. integral {r:real^1 | &0 <= drop r}
              (\r. frechet_derivative (f:complex->complex)
                     (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
                     (cexp(ii * Cx(drop t))))) =
     integral (interval[vec 0, lift(&2 * pi)])
       (\t. integral (interval[vec 0:real^1, lift B])
              (\r. frechet_derivative f
                     (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
                     (cexp(ii * Cx(drop t)))))]]) SUBST1_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN
      X_GEN_TAC ([[t:real^1]]) THEN
      ONCE_REWRITE_TAC [(← HolLight.GSYM INTEGRAL_RESTRICT_UNIV)] THEN
      AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN
      X_GEN_TAC ([[r:real^1]]) THEN
      REWRITE_TAC [IN_ELIM_THM, IN_INTERVAL_1, DROP_VEC, LIFT_DROP] THEN
      ASM_CASES_TAC ([[&0 <= drop(r:real^1)]]) THEN ASM_REWRITE_TAC [] THEN
      ASM_CASES_TAC ([[drop(r:real^1) <= B]]) THEN ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    MP_TAC (← HolLight.ISPECL [([[\r:real^1 t:real^1. frechet_derivative (f:complex->complex)
       (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
       (cexp(ii * Cx(drop t)))]]),
      ([[vec 0:real^1]]), ([[lift B:real^1]]),
      ([[vec 0:real^1]]), ([[lift(&2 * pi):real^1]])] INTEGRAL_SWAP_CONTINUOUS) THEN
    REWRITE_TAC [] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC FRECHET_CONTINUOUS_ON_JOINT THEN
    ASM_REWRITE_TAC [CONTINUOUS_ON_POLAR_PASTECART,
                     CONTINUOUS_ON_CEXP_SNDCART])
  : ExceptT String IO thm).run
#eval POLAR_FUBINI_SWAP

/- Full polar decomposition: converts 2D dbar integral to constant           -/
/- angular integral. Combines FUBINI_POLAR + INNER_INTEGRAL_SIMPLIFY +       -/
/- Fubini swap + RADIAL_INTEGRAL_NEG_FW.                                     -/

#eval phrase 76
def POLAR_INTEGRAL_DECOMPOSITION : thm := keep "POLAR_INTEGRAL_DECOMPOSITION" fun _ => (do
  prove ([[!f:complex->complex w.
     f differentiable_on (:complex) /\
     (!h. (\z. frechet_derivative f (at z) h) continuous_on (:complex)) /\
     bounded (support (+) f (:complex))
     ==> integral (:complex) (\z. wirtinger_dbar f (w + z) / z) =
         inv(Cx(&2)) *
         integral (interval[vec 0:real^1, lift(&2 * pi)]) (\t:real^1. --(f w))]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[(f:complex->complex) continuous_on (:complex)]]) ASSUME_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[(\z. wirtinger_dbar (f:complex->complex) (w + z) / z)
     absolutely_integrable_on (:complex)]]) ASSUME_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_DBAR_KERNEL THEN CONJ_TAC THENL
       [MATCH_MP_TAC WIRTINGER_DBAR_CONTINUOUS THEN ASM_REWRITE_TAC [],
        MATCH_MP_TAC WIRTINGER_DBAR_BOUNDED_SUPPORT THEN ASM_REWRITE_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[integral (:complex) (\z. wirtinger_dbar (f:complex->complex) (w + z) / z) =
     integral {r:real^1 | &0 <= drop r}
       (\r. integral (interval[vec 0, lift(&2 * pi)])
              (\t. drop r %
                   (wirtinger_dbar f (w + Cx(drop r) * cexp(ii * Cx(drop t))) /
                    (Cx(drop r) * cexp(ii * Cx(drop t))))))]]) SUBST1_TAC THENL
     [MP_TAC (← HolLight.BETA_RULE (← HolLight.ISPEC ([[\z. wirtinger_dbar (f:complex->complex) (w + z) / z]]) FUBINI_POLAR)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
      DISCH_THEN (ACCEPT_TAC o HolLight.SYM o HolLight.CONJUNCT2 o HolLight.CONJUNCT2),
      ALL_TAC] THEN
    SUBGOAL_THEN ([[integral {r:real^1 | &0 <= drop r}
       (\r. integral (interval[vec 0, lift(&2 * pi)])
              (\t. drop r %
                   (wirtinger_dbar (f:complex->complex)
                      (w + Cx(drop r) * cexp(ii * Cx(drop t))) /
                    (Cx(drop r) * cexp(ii * Cx(drop t)))))) =
     inv(Cx(&2)) *
     integral {r:real^1 | &0 <= drop r}
       (\r. integral (interval[vec 0, lift(&2 * pi)])
              (\t. frechet_derivative f
                     (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
                     (cexp(ii * Cx(drop t)))))]]) SUBST1_TAC THENL
     [SUBGOAL_THEN ([[(\r:real^1. integral (interval[vec 0, lift(&2 * pi)])
         (\t. drop r %
              (wirtinger_dbar (f:complex->complex)
                 (w + Cx(drop r) * cexp(ii * Cx(drop t))) /
               (Cx(drop r) * cexp(ii * Cx(drop t))))))
       absolutely_integrable_on {r | &0 <= drop r}]]) ASSUME_TAC THENL
       [MP_TAC (← HolLight.BETA_RULE (← HolLight.ISPEC ([[\z. wirtinger_dbar (f:complex->complex) (w + z) / z]]) FUBINI_POLAR)) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
        DISCH_THEN (fun th => HolLight.tactic_of do
        pure (ACCEPT_TAC (← HolLight.CONJUNCT1 (← HolLight.CONJUNCT2 th)))),
        ALL_TAC] THEN
      SUBGOAL_THEN ([[integral {r:real^1 | &0 <= drop r}
         (\r. integral (interval[vec 0, lift(&2 * pi)])
                (\t. drop r %
                     (wirtinger_dbar (f:complex->complex)
                        (w + Cx(drop r) * cexp(ii * Cx(drop t))) /
                      (Cx(drop r) * cexp(ii * Cx(drop t)))))) =
       integral {r:real^1 | &0 <= drop r}
         (\r. inv(Cx(&2)) *
              integral (interval[vec 0, lift(&2 * pi)])
                (\t. frechet_derivative (f:complex->complex)
                       (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
                       (cexp(ii * Cx(drop t)))))]]) SUBST1_TAC THENL
       [MATCH_MP_TAC INTEGRAL_SPIKE THEN
        EXISTS_TAC ([[{vec 0:real^1}]]) THEN
        REWRITE_TAC [NEGLIGIBLE_SING, IN_DIFF, IN_ELIM_THM, IN_SING] THEN
        GEN_TAC THEN STRIP_TAC THEN
        MP_TAC (← HolLight.SPECL [([[f:complex->complex]]), ([[w:complex]]), ([[x:real^1]])] INNER_INTEGRAL_SIMPLIFY) THEN
        ASM_REWRITE_TAC [] THEN
        ANTS_TAC THENL
         [ASM_MESON_TAC [DROP_POS_OF_NONNEG_NZ], SIMP_TAC []],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[(\r:real^1. integral (interval[vec 0, lift(&2 * pi)])
         (\t. frechet_derivative (f:complex->complex)
                (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
                (cexp(ii * Cx(drop t)))))
       integrable_on {r | &0 <= drop r}]]) ASSUME_TAC THENL
       [SUBGOAL_THEN ([[(\r:real^1. inv(Cx(&2)) *
              integral (interval[vec 0, lift(&2 * pi)])
                (\t. frechet_derivative (f:complex->complex)
                       (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
                       (cexp(ii * Cx(drop t)))))
         integrable_on {r | &0 <= drop r}]]) MP_TAC THENL
         [MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_IMP] INTEGRABLE_SPIKE) THEN
          EXISTS_TAC ([[(\r:real^1. integral (interval[vec 0, lift(&2 * pi)])
             (\t. drop r %
                  (wirtinger_dbar (f:complex->complex)
                     (w + Cx(drop r) * cexp(ii * Cx(drop t))) /
                   (Cx(drop r) * cexp(ii * Cx(drop t))))))]]) THEN
          EXISTS_TAC ([[{vec 0:real^1}]]) THEN
          REWRITE_TAC [NEGLIGIBLE_SING, IN_DIFF, IN_ELIM_THM, IN_SING] THEN
          CONJ_TAC THENL
           [GEN_TAC THEN STRIP_TAC THEN
            CONV_TAC HolLight.SYM_CONV THEN
            MP_TAC (← HolLight.SPECL [([[f:complex->complex]]), ([[w:complex]]), ([[x:real^1]])] INNER_INTEGRAL_SIMPLIFY) THEN
            ASM_REWRITE_TAC [] THEN
            ANTS_TAC THENL
             [ASM_MESON_TAC [DROP_POS_OF_NONNEG_NZ], SIMP_TAC []],
            MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
            ASM_REWRITE_TAC []],
          ALL_TAC] THEN
        REWRITE_TAC [INTEGRABLE_COMPLEX_LMUL_EQ] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
        UNDISCH_TAC ([[inv(Cx(&2)) = Cx(&0)]]) THEN
        REWRITE_TAC [COMPLEX_INV_EQ_0, CX_INJ] THEN REAL_ARITH_TAC2,
        ALL_TAC] THEN
      ASM_SIMP_TAC [(← HolLight.GSYM INTEGRAL_COMPLEX_LMUL)],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[integral {r:real^1 | &0 <= drop r}
       (\r. integral (interval[vec 0, lift(&2 * pi)])
              (\t. frechet_derivative (f:complex->complex)
                     (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
                     (cexp(ii * Cx(drop t))))) =
     integral (interval[vec 0, lift(&2 * pi)])
       (\t. integral {r:real^1 | &0 <= drop r}
              (\r. frechet_derivative f
                     (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
                     (cexp(ii * Cx(drop t)))))]]) SUBST1_TAC THENL
     [MATCH_MP_TAC POLAR_FUBINI_SWAP THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!t:real^1. integral {r:real^1 | &0 <= drop r}
                  (\r. frechet_derivative (f:complex->complex)
                         (at (w + Cx(drop r) * cexp(ii * Cx(drop t))))
                         (cexp(ii * Cx(drop t)))) = --(f w)]]) (fun th => REWRITE_TAC [th]) THEN
    X_GEN_TAC ([[t0:real^1]]) THEN
    MP_TAC (← HolLight.SPECL [([[f:complex->complex]]), ([[w:complex]]), ([[drop(t0:real^1)]])] RADIAL_INTEGRAL_NEG_FW) THEN
    ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval POLAR_INTEGRAL_DECOMPOSITION

/- ------------------------------------------------------------------------- -/
/- Helper lemmas for the Pompeiu formula.                                    -/
/- ------------------------------------------------------------------------- -/

#eval phrase 77
def INTEGRAL_CONST_2PI : thm := keep "INTEGRAL_CONST_2PI" fun _ => (do
  prove ([[!c:complex.
     integral (interval[vec 0:real^1, lift(&2 * pi)]) (\t. c) =
     Cx(&2 * pi) * c]])
   (GEN_TAC THEN REWRITE_TAC [INTEGRAL_CONST] THEN
    SUBGOAL_THEN ([[content(interval[vec 0:real^1, lift(&2 * pi)]) = &2 * pi]]) SUBST1_TAC THENL
     [MP_TAC (← HolLight.SPECL [([[vec 0:real^1]]), ([[lift(&2 * pi)]])] CONTENT_1) THEN
      REWRITE_TAC [DROP_VEC, LIFT_DROP] THEN
      MP_TAC PI_POS THEN REAL_ARITH_TAC2,
      REWRITE_TAC [COMPLEX_CMUL]])
  : ExceptT String IO thm).run
#eval INTEGRAL_CONST_2PI

#eval phrase 78
def INV_TWO_TIMES_TWO_PI : thm := keep "INV_TWO_TIMES_TWO_PI" fun _ => (do
  prove ([[inv(Cx(&2)) * Cx(&2 * pi) = Cx(pi)]])
   (REWRITE_TAC [CX_MUL] THEN
    SUBGOAL_THEN ([[inv(Cx(&2)) * Cx(&2) = Cx(&1)]]) (fun th => REWRITE_TAC [COMPLEX_MUL_ASSOC, th, COMPLEX_MUL_LID]) THEN
    MATCH_MP_TAC COMPLEX_MUL_LINV THEN
    REWRITE_TAC [CX_INJ] THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval INV_TWO_TIMES_TWO_PI

/- ------------------------------------------------------------------------- -/
/- The Pompeiu formula: Cauchy transform inverts dbar.                       -/
/- ------------------------------------------------------------------------- -/

#eval phrase 79
def CAUCHY_TRANSFORM_INVERTS_DBAR : thm := keep "CAUCHY_TRANSFORM_INVERTS_DBAR" fun _ => (do
  prove ([[!f:complex->complex w.
        f differentiable_on (:complex) /\
        (!h. (\z. frechet_derivative f (at z) h) continuous_on (:complex)) /\
        bounded (support (+) f (:complex))
        ==> integral (:complex)
              (\z. wirtinger_dbar f z / (z - w)) = --(Cx pi * f w)]])
   (REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [CAUCHY_TRANSFORM_DBAR_TRANSLATION] THEN
    SUBGOAL_THEN ([[integral (:complex) (\z. wirtinger_dbar (f:complex->complex) (w + z) / z) =
     inv(Cx(&2)) *
     integral (interval[vec 0:real^1, lift(&2 * pi)]) (\t:real^1. --(f w))]]) SUBST1_TAC THENL
     [MATCH_MP_TAC POLAR_INTEGRAL_DECOMPOSITION THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [INTEGRAL_CONST_2PI] THEN
      REWRITE_TAC [COMPLEX_MUL_ASSOC, INV_TWO_TIMES_TWO_PI] THEN
      REWRITE_TAC [COMPLEX_MUL_RNEG]])
  : ExceptT String IO thm).run
#eval CAUCHY_TRANSFORM_INVERTS_DBAR

/- ========================================================================= -/
/- Hermite cutoff infrastructure for smooth extension.                       -/
/- ========================================================================= -/

#eval phrase 80
def PIECEWISE_HAS_DERIVATIVE_LOCAL : thm := keep "PIECEWISE_HAS_DERIVATIVE_LOCAL" fun _ => (do
  prove ([[!(f:real^M->real^N) g ef f' z d0.
    &0 < d0 /\
    (f has_derivative f') (at z) /\
    (g has_derivative f') (at z) /\
    f z = g z /\
    (!y:real^M. norm(y - z) < d0 ==> ef y = f y \/ ef y = g y) /\
    ef z = f z
    ==> (ef has_derivative f') (at z)]])
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [HAS_DERIVATIVE_AT_ALT] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC ([[e:real]]) THEN DISCH_TAC THEN
    UNDISCH_TAC ([[!e. &0 < e
         ==> (?d. &0 < d /\
                  (!y. norm (y - z) < d
                       ==> norm ((f:real^M->real^N) y - f z - f' (y - z))
                           <= e * norm (y - z)))]]) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[e:real]])) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[d1:real]]) STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC ([[!e. &0 < e
         ==> (?d. &0 < d /\
                  (!y. norm (y - z) < d
                       ==> norm ((g:real^M->real^N) y - g z - f' (y - z))
                           <= e * norm (y - z)))]]) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[e:real]])) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[d2:real]]) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC ([[min d0 (min d1 d2)]]) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    X_GEN_TAC ([[y:real^M]]) THEN DISCH_TAC THEN
    UNDISCH_TAC ([[!y:real^M. norm(y - z) < d0
                ==> (ef:real^M->real^N) y = f y \/ ef y = g y]]) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[y:real^M]])) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [SUBGOAL_THEN ([[(ef:real^M->real^N) y - g z - f'(y - z:real^M) =
       f y - f z - f'(y - z)]]) SUBST1_TAC THENL
       [SUBGOAL_THEN ([[(g:real^M->real^N) z = f z]]) (fun th => REWRITE_TAC [th]) THENL
         [ASM_MESON_TAC [], ASM_REWRITE_TAC []],
        FIRST_X_ASSUM (fun (th : thm) => HolLight.tactic_of do
        let q ← ExceptT.mk [[d1:real]]
        pure (if HolCore.Basics.free_in q (concl th) then MATCH_MP_TAC th else FAIL_TAC "check")) THEN
        ASM_REAL_ARITH_TAC],
      SUBGOAL_THEN ([[(ef:real^M->real^N) y - g z - f'(y - z:real^M) =
       g y - g z - f'(y - z)]]) SUBST1_TAC THENL
       [ASM_REWRITE_TAC [],
        FIRST_X_ASSUM (fun (th : thm) => HolLight.tactic_of do
        let q ← ExceptT.mk [[d2:real]]
        pure (if HolCore.Basics.free_in q (concl th) then MATCH_MP_TAC th else FAIL_TAC "check")) THEN
        ASM_REAL_ARITH_TAC]])
  : ExceptT String IO thm).run
#eval PIECEWISE_HAS_DERIVATIVE_LOCAL

#eval phrase 81
def PIECEWISE_HAS_REAL_DERIVATIVE_LOCAL : thm := keep "PIECEWISE_HAS_REAL_DERIVATIVE_LOCAL" fun _ => (do
  prove ([[!f g ef f' x d0.
    &0 < d0 /\
    (f has_real_derivative f') (atreal x) /\
    (g has_real_derivative f') (atreal x) /\
    f x = g x /\
    (!y. abs(y - x) < d0 ==> ef y = f y \/ ef y = g y) /\
    ef x = f x
    ==> (ef has_real_derivative f') (atreal x)]])
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [HAS_REAL_FRECHET_DERIVATIVE_AT, o_DEF, LIFT_DROP] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC PIECEWISE_HAS_DERIVATIVE_LOCAL THEN
    MAP_EVERY EXISTS_TAC [([[(\y:real^1. lift(f(drop y)))]]),
      ([[(\y:real^1. lift(g(drop y)))]]),
      ([[d0:real]])] THEN
    CONV_TAC (HolLight.DEPTH_CONV HolLight.BETA_CONV) THEN
    ASM_REWRITE_TAC [LIFT_EQ, LIFT_DROP] THEN
    X_GEN_TAC ([[y:real^1]]) THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[drop y]])) THEN
    ANTS_TAC THENL
     [POP_ASSUM MP_TAC THEN
      REWRITE_TAC [NORM_REAL, (← HolLight.GSYM drop), DROP_SUB, LIFT_DROP],
      SIMP_TAC []])
  : ExceptT String IO thm).run
#eval PIECEWISE_HAS_REAL_DERIVATIVE_LOCAL

#eval phrase 82
def hermite_cutoff : thm := keep "hermite_cutoff" fun _ => new_definition
 [[hermite_cutoff (t:real) =
    if t <= &0 then &1
    else if &1 <= t then &0
    else &2 * t pow 3 - &3 * t pow 2 + &1]]
#eval hermite_cutoff

#eval phrase 83
def hermite_cutoff_deriv : thm := keep "hermite_cutoff_deriv" fun _ => new_definition
 [[hermite_cutoff_deriv (t:real) =
    if t <= &0 then &0
    else if &1 <= t then &0
    else &6 * t pow 2 - &6 * t]]
#eval hermite_cutoff_deriv

#eval phrase 84
def HAS_REAL_DERIVATIVE_HERMITE_INTERIOR : thm := keep "HAS_REAL_DERIVATIVE_HERMITE_INTERIOR" fun _ => (do
  prove ([[!t. &0 < t /\ t < &1
       ==> (hermite_cutoff has_real_derivative (&6 * t pow 2 - &6 * t))
           (atreal t)]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [([[\t:real. &2 * t pow 3 - &3 * t pow 2 + &1]]),
                   ([[&6 * t pow 2 - &6 * t]]), ([[hermite_cutoff]]),
                   ([[t:real]]), ([[min t (&1 - t)]])] HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      CONJ_TAC THENL
       [X_GEN_TAC ([[s:real]]) THEN DISCH_TAC THEN
        REWRITE_TAC [hermite_cutoff] THEN
        COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
        COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC, REFL_TAC],
        REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC2],
      SIMP_TAC []])
  : ExceptT String IO thm).run
#eval HAS_REAL_DERIVATIVE_HERMITE_INTERIOR

#eval phrase 85
def HAS_REAL_DERIVATIVE_HERMITE_LEFT : thm := keep "HAS_REAL_DERIVATIVE_HERMITE_LEFT" fun _ => (do
  prove ([[!t. t < &0
       ==> (hermite_cutoff has_real_derivative (&0)) (atreal t)]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [([[\t:real. &1]]), ([[&0:real]]), ([[hermite_cutoff]]),
                   ([[t:real]]), ([[-- t:real]])] HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      CONJ_TAC THENL
       [X_GEN_TAC ([[s:real]]) THEN DISCH_TAC THEN
        REWRITE_TAC [hermite_cutoff] THEN
        COND_CASES_TAC THENL [REFL_TAC, ASM_REAL_ARITH_TAC],
        REAL_DIFF_TAC THEN REFL_TAC],
      SIMP_TAC []])
  : ExceptT String IO thm).run
#eval HAS_REAL_DERIVATIVE_HERMITE_LEFT

#eval phrase 86
def HAS_REAL_DERIVATIVE_HERMITE_RIGHT : thm := keep "HAS_REAL_DERIVATIVE_HERMITE_RIGHT" fun _ => (do
  prove ([[!t. &1 < t
       ==> (hermite_cutoff has_real_derivative (&0)) (atreal t)]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [([[\t:real. &0:real]]), ([[&0:real]]), ([[hermite_cutoff]]),
                   ([[t:real]]), ([[t - &1:real]])] HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      CONJ_TAC THENL
       [X_GEN_TAC ([[s:real]]) THEN DISCH_TAC THEN
        REWRITE_TAC [hermite_cutoff] THEN
        COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
        COND_CASES_TAC THENL [REFL_TAC, ASM_REAL_ARITH_TAC],
        REAL_DIFF_TAC THEN REFL_TAC],
      SIMP_TAC []])
  : ExceptT String IO thm).run
#eval HAS_REAL_DERIVATIVE_HERMITE_RIGHT

#eval phrase 87
def HAS_REAL_DERIVATIVE_HERMITE_AT_0 : thm := keep "HAS_REAL_DERIVATIVE_HERMITE_AT_0" fun _ => (do
  prove ([[(hermite_cutoff has_real_derivative (&0)) (atreal (&0))]])
   (MATCH_MP_TAC PIECEWISE_HAS_REAL_DERIVATIVE_LOCAL THEN
    MAP_EVERY EXISTS_TAC [([[\t:real. &1]]), ([[\t:real. &2 * t pow 3 - &3 * t pow 2 + &1]]), ([[&1]])] THEN
    REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC2, REAL_DIFF_TAC THEN REFL_TAC,
      REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC2,
      REAL_ARITH_TAC2,
      X_GEN_TAC ([[t:real]]) THEN REWRITE_TAC [REAL_SUB_RZERO] THEN DISCH_TAC THEN
      REWRITE_TAC [hermite_cutoff] THEN
      COND_CASES_TAC THENL [DISJ1_TAC THEN REFL_TAC, ALL_TAC] THEN
      COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC, DISJ2_TAC THEN REFL_TAC],
      REWRITE_TAC [hermite_cutoff] THEN REAL_ARITH_TAC2])
  : ExceptT String IO thm).run
#eval HAS_REAL_DERIVATIVE_HERMITE_AT_0

#eval phrase 88
def HAS_REAL_DERIVATIVE_HERMITE_AT_1 : thm := keep "HAS_REAL_DERIVATIVE_HERMITE_AT_1" fun _ => (do
  prove ([[(hermite_cutoff has_real_derivative (&0)) (atreal (&1))]])
   (MATCH_MP_TAC PIECEWISE_HAS_REAL_DERIVATIVE_LOCAL THEN
    MAP_EVERY EXISTS_TAC [([[\t:real. &2 * t pow 3 - &3 * t pow 2 + &1]]), ([[\t:real. &0]]), ([[&1]])] THEN
    REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC2,
      REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC2,
      REAL_DIFF_TAC THEN REFL_TAC, REAL_ARITH_TAC2,
      X_GEN_TAC ([[t:real]]) THEN DISCH_TAC THEN
      REWRITE_TAC [hermite_cutoff] THEN
      COND_CASES_TAC THENL [DISJ1_TAC THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      COND_CASES_TAC THENL [DISJ2_TAC THEN REAL_ARITH_TAC2, ALL_TAC] THEN
      DISJ1_TAC THEN REFL_TAC,
      REWRITE_TAC [hermite_cutoff] THEN REAL_ARITH_TAC2])
  : ExceptT String IO thm).run
#eval HAS_REAL_DERIVATIVE_HERMITE_AT_1

#eval phrase 89
def HAS_REAL_DERIVATIVE_HERMITE_EXPLICIT : thm := keep "HAS_REAL_DERIVATIVE_HERMITE_EXPLICIT" fun _ => (do
  prove ([[!t. (hermite_cutoff has_real_derivative hermite_cutoff_deriv t) (atreal t)]])
   (GEN_TAC THEN REWRITE_TAC [hermite_cutoff_deriv] THEN
    COND_CASES_TAC THENL
     [ASM_CASES_TAC ([[t = &0]]) THENL
       [ASM_REWRITE_TAC [HAS_REAL_DERIVATIVE_HERMITE_AT_0],
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_HERMITE_LEFT THEN
        ASM_REAL_ARITH_TAC],
      COND_CASES_TAC THENL
       [ASM_CASES_TAC ([[t = &1]]) THENL
         [ASM_REWRITE_TAC [HAS_REAL_DERIVATIVE_HERMITE_AT_1],
          MATCH_MP_TAC HAS_REAL_DERIVATIVE_HERMITE_RIGHT THEN
          ASM_REAL_ARITH_TAC],
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_HERMITE_INTERIOR THEN
        ASM_REAL_ARITH_TAC]])
  : ExceptT String IO thm).run
#eval HAS_REAL_DERIVATIVE_HERMITE_EXPLICIT

#eval phrase 90
def POLY_CONTINUOUS_REAL1 : thm := keep "POLY_CONTINUOUS_REAL1" fun _ => (do
  prove ([[(\x:real^1. lift(&6 * drop x pow 2 - &6 * drop x)) continuous_on s]])
   (MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC ([[(:real^1)]]) THEN REWRITE_TAC [SUBSET_UNIV] THEN
    SUBGOAL_THEN ([[(\x:real^1. lift(&6 * drop x pow 2 - &6 * drop x)) =
     (\x. &6 % lift(x dot x) - &6 % x)]]) SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
      SIMP_TAC [CART_EQ, DIMINDEX_1, FORALL_1,
        VECTOR_SUB_COMPONENT, VECTOR_MUL_COMPONENT,
        lift, LAMBDA_BETA, LE_REFL, DOT_1, drop, REAL_POW_2] THEN
      REAL_ARITH_TAC2,
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THEN
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THENL
       [MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
        REWRITE_TAC [CONTINUOUS_ON_ID],
        REWRITE_TAC [CONTINUOUS_ON_ID]]])
  : ExceptT String IO thm).run
#eval POLY_CONTINUOUS_REAL1

#eval phrase 91
def HERMITE_CUTOFF_DERIV_CONTINUOUS : thm := keep "HERMITE_CUTOFF_DERIV_CONTINUOUS" fun _ => (do
  prove ([[(lift o hermite_cutoff_deriv o drop) continuous_on (:real^1)]])
   (SUBGOAL_THEN ([[(lift o hermite_cutoff_deriv o drop) =
     (\x:real^1. if drop x <= &0 then vec 0
                 else if drop x <= &1
                 then lift(&6 * drop x pow 2 - &6 * drop x)
                 else vec 0)]]) SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM, o_THM, hermite_cutoff_deriv] THEN
      X_GEN_TAC ([[x:real^1]]) THEN
      COND_CASES_TAC THEN REWRITE_TAC [LIFT_NUM] THEN
      ASM_CASES_TAC ([[&1 <= drop x]]) THENL
       [ASM_REWRITE_TAC [LIFT_NUM] THEN
        COND_CASES_TAC THENL
         [SUBGOAL_THEN ([[drop(x:real^1) = &1]]) SUBST1_TAC THENL
           [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
          CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [LIFT_NUM],
          REFL_TAC],
        ASM_REWRITE_TAC [] THEN
        COND_CASES_TAC THENL [REFL_TAC, ASM_REAL_ARITH_TAC]],
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES_LE THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC [CONTINUOUS_ON_CONST],
      MATCH_MP_TAC CONTINUOUS_ON_CASES_LE THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC [POLY_CONTINUOUS_REAL1],
        REWRITE_TAC [CONTINUOUS_ON_CONST],
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC ([[(:real^1)]]) THEN
        REWRITE_TAC [SUBSET_UNIV, o_DEF, LIFT_DROP, CONTINUOUS_ON_ID],
        SIMP_TAC [] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        REWRITE_TAC [LIFT_NUM]],
      REWRITE_TAC [o_DEF, LIFT_DROP, CONTINUOUS_ON_ID],
      SIMP_TAC [] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC [LIFT_NUM]])
  : ExceptT String IO thm).run
#eval HERMITE_CUTOFF_DERIV_CONTINUOUS

#eval phrase 92
def HERMITE_CUTOFF_DIFFERENTIABLE : thm := keep "HERMITE_CUTOFF_DIFFERENTIABLE" fun _ => (do
  prove ([[!x:real^1. (lift o hermite_cutoff o drop) differentiable (at x)]])
   (GEN_TAC THEN REWRITE_TAC [differentiable] THEN
    EXISTS_TAC ([[\v:real^1. hermite_cutoff_deriv(drop x) % v]]) THEN
    MP_TAC (← HolLight.SPEC ([[drop x]]) HAS_REAL_DERIVATIVE_HERMITE_EXPLICIT) THEN
    REWRITE_TAC [HAS_REAL_FRECHET_DERIVATIVE_AT, o_DEF, LIFT_DROP])
  : ExceptT String IO thm).run
#eval HERMITE_CUTOFF_DIFFERENTIABLE

#eval phrase 93
def HERMITE_CUTOFF_DIFFERENTIABLE_ON : thm := keep "HERMITE_CUTOFF_DIFFERENTIABLE_ON" fun _ => (do
  prove ([[!s. (lift o hermite_cutoff o drop) differentiable_on s]])
   (REWRITE_TAC [differentiable_on] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC DIFFERENTIABLE_AT_WITHIN THEN
    REWRITE_TAC [HERMITE_CUTOFF_DIFFERENTIABLE])
  : ExceptT String IO thm).run
#eval HERMITE_CUTOFF_DIFFERENTIABLE_ON

#eval phrase 94
def HERMITE_CUTOFF_CONTINUOUS : thm := keep "HERMITE_CUTOFF_CONTINUOUS" fun _ => (do
  prove ([[(lift o hermite_cutoff o drop) continuous_on (:real^1)]])
   (MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC [HERMITE_CUTOFF_DIFFERENTIABLE_ON])
  : ExceptT String IO thm).run
#eval HERMITE_CUTOFF_CONTINUOUS

/- Chain rule for hermite_cutoff composed with phi(z) = (norm z^2 - R^2)/c   -/

#eval phrase 95
def HERMITE_CUTOFF_CHI_HAS_DERIVATIVE : thm := keep "HERMITE_CUTOFF_CHI_HAS_DERIVATIVE" fun _ => (do
  prove ([[!R c (z:complex).
     &0 < c
     ==> ((\z'. lift(hermite_cutoff((norm z' pow 2 - R pow 2) / c)))
          has_derivative
          (\h:complex. lift(hermite_cutoff_deriv((norm z pow 2 - R pow 2) / c) *
                            (&2 * (z dot h)) / c))) (at z)]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[(\z':complex. lift(hermite_cutoff((norm z' pow 2 - R pow 2) / c))) =
     (lift o hermite_cutoff o drop) o
     (\z':complex. lift((norm z' pow 2 - R pow 2) / c))]]) SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM, o_DEF, LIFT_DROP], ALL_TAC] THEN
    SUBGOAL_THEN ([[(\h:complex. lift(hermite_cutoff_deriv((norm z pow 2 - R pow 2) / c) *
                       (&2 * (z dot h)) / c)) =
     (\h. hermite_cutoff_deriv((norm(z:complex) pow 2 - R pow 2) / c) %
          lift((&2 * (z dot h)) / c))]]) SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
      SIMP_TAC [CART_EQ, DIMINDEX_1, FORALL_1, VECTOR_MUL_COMPONENT,
        lift, LAMBDA_BETA, LE_REFL] THEN REAL_ARITH_TAC2,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[(\h:complex. hermite_cutoff_deriv((norm(z:complex) pow 2 - R pow 2) / c) %
          lift((&2 * (z dot h)) / c)) =
     (\v:real^1. hermite_cutoff_deriv((norm z pow 2 - R pow 2) / c) % v) o
     (\h:complex. lift((&2 * (z dot h)) / c))]]) SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM, o_DEF], ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [SUBGOAL_THEN ([[(\z':complex. lift((norm z' pow 2 - R pow 2) / c)) =
       (\z'. inv(c) % lift(norm z' pow 2) + lift(--(R pow 2 / c)))]]) SUBST1_TAC THENL
       [REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
        SIMP_TAC [CART_EQ, DIMINDEX_1, FORALL_1, VECTOR_MUL_COMPONENT,
          VECTOR_ADD_COMPONENT, lift, LAMBDA_BETA, LE_REFL] THEN
        UNDISCH_TAC ([[&0 < c]]) THEN CONV_TAC rf,
        ALL_TAC] THEN
      SUBGOAL_THEN ([[(\h:complex. lift((&2 * (z dot h)) / c)) =
       (\h. inv(c) % (\h. &2 % lift(z dot h)) h + (\h:complex. vec 0) h)]]) SUBST1_TAC THENL
       [REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
        SIMP_TAC [CART_EQ, DIMINDEX_1, FORALL_1, VECTOR_MUL_COMPONENT,
          VECTOR_ADD_COMPONENT, VEC_COMPONENT, lift, LAMBDA_BETA, LE_REFL,
          real_div, REAL_MUL_ASSOC] THEN
        REAL_ARITH_TAC2,
        MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
        REWRITE_TAC [HAS_DERIVATIVE_CONST] THEN
        MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
        REWRITE_TAC [HAS_DERIVATIVE_SQNORM_AT]],
      MP_TAC (← HolLight.SPEC ([[(norm(z:complex) pow 2 - R pow 2) / c]]) HAS_REAL_DERIVATIVE_HERMITE_EXPLICIT) THEN
      REWRITE_TAC [HAS_REAL_FRECHET_DERIVATIVE_AT, o_DEF, LIFT_DROP]])
  : ExceptT String IO thm).run
#eval HERMITE_CUTOFF_CHI_HAS_DERIVATIVE

/- Helper lemmas for continuity of composed functions                        -/

#eval phrase 96
def HERMITE_CUTOFF_LE_0 : thm := keep "HERMITE_CUTOFF_LE_0" fun _ => (do
  prove ([[!t. t <= &0 ==> hermite_cutoff t = &1]])
   (GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [hermite_cutoff] THEN
    ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval HERMITE_CUTOFF_LE_0

#eval phrase 97
def HERMITE_CUTOFF_GE_1 : thm := keep "HERMITE_CUTOFF_GE_1" fun _ => (do
  prove ([[!t. &1 <= t ==> hermite_cutoff t = &0]])
   (GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [hermite_cutoff] THEN
    COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC, ASM_REWRITE_TAC []])
  : ExceptT String IO thm).run
#eval HERMITE_CUTOFF_GE_1

#eval phrase 98
def HERMITE_CUTOFF_NONNEG : thm := keep "HERMITE_CUTOFF_NONNEG" fun _ => (do
  prove ([[!t. &0 <= hermite_cutoff t]])
   (GEN_TAC THEN
    ASM_CASES_TAC ([[t <= &0]]) THENL
     [ASM_SIMP_TAC [HERMITE_CUTOFF_LE_0] THEN REAL_ARITH_TAC2, ALL_TAC] THEN
    ASM_CASES_TAC ([[&1 <= t]]) THENL
     [ASM_SIMP_TAC [HERMITE_CUTOFF_GE_1] THEN REAL_ARITH_TAC2, ALL_TAC] THEN
    REWRITE_TAC [hermite_cutoff] THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN ([[&2 * t pow 3 - &3 * t pow 2 + &1 = (&1 - t) pow 2 * (&1 + &2 * t)]]) SUBST1_TAC THENL
     [CONV_TAC rg, ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC,
      ASM_REAL_ARITH_TAC])
  : ExceptT String IO thm).run
#eval HERMITE_CUTOFF_NONNEG

/- ========================================================================= -/
/- C^1 extension from open sets: weaken f differentiable_on (:complex) to    -/
/- f differentiable_on u for an open set u containing the compact set K.     -/
/- Approach: cover K by finitely many balls inside u, build C^1 ball bumps,  -/
/- sum them, compose with hermite_cutoff to get a C^1 cutoff chi = 1 on K    -/
/- with support inside u, then ef = chi * f extends to all of C.             -/
/- ========================================================================= -/
/- Shifted version: derivative of hermite_cutoff((|w-a|^2 - R^2)/c)          -/

#eval phrase 99
def HERMITE_CUTOFF_SHIFTED_HAS_DERIVATIVE : thm := keep "HERMITE_CUTOFF_SHIFTED_HAS_DERIVATIVE" fun _ => (do
  prove ([[!a:complex R c (z:complex).
     &0 < c
     ==> ((\w. lift(hermite_cutoff((norm(w - a) pow 2 - R pow 2) / c)))
          has_derivative
          (\h:complex. lift(hermite_cutoff_deriv
               ((norm(z - a) pow 2 - R pow 2) / c) *
               (&2 * ((z - a) dot h)) / c))) (at z)]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[\w:complex. w - a]]),
       ([[\w:complex. lift(hermite_cutoff((norm w pow 2 - R pow 2) / c))]]),
       ([[\h:complex. h]]),
       ([[\h:complex. lift(hermite_cutoff_deriv
          ((norm(z - a:complex) pow 2 - R pow 2) / c) *
          (&2 * ((z - a) dot h)) / c)]]),
       ([[z:complex]])] DIFF_CHAIN_AT) THEN
    REWRITE_TAC [o_DEF] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN ([[(\h:complex. h) = (\h. h - (vec 0):complex)]]) SUBST1_TAC THENL
       [REWRITE_TAC [FUN_EQ_THM, VECTOR_SUB_RZERO], ALL_TAC] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
      REWRITE_TAC [HAS_DERIVATIVE_ID, HAS_DERIVATIVE_CONST],
      MP_TAC (← HolLight.SPECL [([[R:real]]), ([[c:real]]), ([[z - a:complex]])] HERMITE_CUTOFF_CHI_HAS_DERIVATIVE) THEN
      ASM_REWRITE_TAC []])
  : ExceptT String IO thm).run
#eval HERMITE_CUTOFF_SHIFTED_HAS_DERIVATIVE

/- Continuity of shifted phi                                                 -/

#eval phrase 100
def PHI_SHIFTED_CONTINUOUS_ON : thm := keep "PHI_SHIFTED_CONTINUOUS_ON" fun _ => (do
  prove ([[!a:complex c R s. &0 < c ==>
    (\z. lift((norm(z - a) pow 2 - R pow 2) / c)) continuous_on s]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[(\z:complex. lift((norm(z - a) pow 2 - R pow 2) / c)) =
     (\z. inv(c) % lift((z - a) dot (z - a)) + lift(--(R pow 2 / c)))]]) SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM, NORM_POW_2] THEN GEN_TAC THEN
      SIMP_TAC [CART_EQ, DIMINDEX_1, FORALL_1, VECTOR_ADD_COMPONENT,
        VECTOR_MUL_COMPONENT, lift, LAMBDA_BETA, LE_REFL] THEN
      UNDISCH_TAC ([[&0 < c]]) THEN CONV_TAC rf,
      MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
        MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
        CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
        REWRITE_TAC [CONTINUOUS_ON_ID, CONTINUOUS_ON_CONST],
        REWRITE_TAC [CONTINUOUS_ON_CONST]]])
  : ExceptT String IO thm).run
#eval PHI_SHIFTED_CONTINUOUS_ON

/- Continuity of hcd(shifted phi) and hc(shifted phi)                        -/

#eval phrase 101
def HCD_SHIFTED_CONTINUOUS_ON : thm := keep "HCD_SHIFTED_CONTINUOUS_ON" fun _ => (do
  prove ([[!a:complex c R s. &0 < c ==>
    (\z. lift(hermite_cutoff_deriv((norm(z - a) pow 2 - R pow 2) / c)))
    continuous_on s]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[(\z:complex. lift(hermite_cutoff_deriv
        ((norm(z - a) pow 2 - R pow 2) / c))) =
     (lift o hermite_cutoff_deriv o drop) o
     (\z. lift((norm(z - a) pow 2 - R pow 2) / c))]]) SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM, o_THM, LIFT_DROP], ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [ASM_SIMP_TAC [PHI_SHIFTED_CONTINUOUS_ON],
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC ([[(:real^1)]]) THEN
      REWRITE_TAC [SUBSET_UNIV, HERMITE_CUTOFF_DERIV_CONTINUOUS]])
  : ExceptT String IO thm).run
#eval HCD_SHIFTED_CONTINUOUS_ON

#eval phrase 102
def HC_SHIFTED_CONTINUOUS_ON : thm := keep "HC_SHIFTED_CONTINUOUS_ON" fun _ => (do
  prove ([[!a:complex c R s. &0 < c ==>
    (\z. lift(hermite_cutoff((norm(z - a) pow 2 - R pow 2) / c)))
    continuous_on s]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[(\z:complex. lift(hermite_cutoff
        ((norm(z - a) pow 2 - R pow 2) / c))) =
     (lift o hermite_cutoff o drop) o
     (\z. lift((norm(z - a) pow 2 - R pow 2) / c))]]) SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM, o_THM, LIFT_DROP], ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [ASM_SIMP_TAC [PHI_SHIFTED_CONTINUOUS_ON],
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC ([[(:real^1)]]) THEN
      REWRITE_TAC [SUBSET_UNIV, HERMITE_CUTOFF_CONTINUOUS]])
  : ExceptT String IO thm).run
#eval HC_SHIFTED_CONTINUOUS_ON

/- ========================================================================= -/
/- C^1 extension from open sets.                                             -/
/- Given compact K in open u, extend C^1 function on u to C^1 on all of C    -/
/- with compact support inside u. Uses finite ball cover + hermite cutoff.   -/
/- ========================================================================= -/

#eval phrase 103
def SMOOTH_EXTENSION_FROM_OPEN : thm := keep "SMOOTH_EXTENSION_FROM_OPEN" fun _ => (do
  let h2 ← rr (← ExceptT.mk [[x * y <= &0 <=> &0 <= --(x * y)]])
  let h1 ← rr (← ExceptT.mk [[t < e ==> x <= t ==> x < e]])
  prove ([[!f:complex->complex u (K:complex->bool).
    compact K /\ open u /\ K SUBSET u /\
    f differentiable_on u /\
    (!h:complex. (\z. frechet_derivative f (at z) h) continuous_on u)
    ==> ?ef:complex->complex.
        ef differentiable_on (:complex) /\
        (!h:complex. (\z. frechet_derivative ef (at z) h)
          continuous_on (:complex)) /\
        bounded(support (+) ef (:complex)) /\
        (!z. z IN K ==> ef z = f z)]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPEC ([[K:complex->bool]]) HEINE_BOREL_LEMMA) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[{u:complex->bool}]])) THEN
    REWRITE_TAC [IN_SING, UNIONS_1, UNWIND_THM2] THEN
    ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[e:real]]) STRIP_ASSUME_TAC) THEN
    MP_TAC (← HolLight.ISPEC ([[K:complex->bool]]) COMPACT_IMP_TOTALLY_BOUNDED) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[e / &3]])) THEN
    ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[A:complex->bool]]) STRIP_ASSUME_TAC) THEN
    ABBREV_TAC ([[r = e / &3]]) THEN
    ABBREV_TAC ([[cc = &3 * r pow 2]]) THEN
    SUBGOAL_THEN ([[&0 < r]]) ASSUME_TAC THENL
     [EXPAND_TAC "r" THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    SUBGOAL_THEN ([[&0 < cc]]) ASSUME_TAC THENL
     [EXPAND_TAC "cc" THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC [REAL_POW_LT] THEN REAL_ARITH_TAC2, ALL_TAC] THEN
    SUBGOAL_THEN ([[r pow 2 + cc = (&2 * r) pow 2]]) ASSUME_TAC THENL
     [EXPAND_TAC "cc" THEN REWRITE_TAC [REAL_POW_MUL, REAL_POW_2] THEN
      REAL_ARITH_TAC2, ALL_TAC] THEN
    SUBGOAL_THEN ([[!a:complex. a IN A ==> cball(a, &2 * r) SUBSET u]]) ASSUME_TAC THENL
     [X_GEN_TAC ([[a:complex]]) THEN DISCH_TAC THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC ([[ball(a:complex, e)]]) THEN
      CONJ_TAC THENL
       [REWRITE_TAC [SUBSET, IN_CBALL, IN_BALL] THEN GEN_TAC THEN
        MATCH_MP_TAC h1 THEN
        EXPAND_TAC "r" THEN ASM_REAL_ARITH_TAC,
        FIRST_X_ASSUM MATCH_MP_TAC THEN HolLight.ASM SET_TAC []],
      ALL_TAC] THEN
    ABBREV_TAC ([[W = UNIONS(IMAGE (\a:complex. cball(a, &2 * r)) A)]]) THEN
    SUBGOAL_THEN ([[(W:complex->bool) SUBSET u]]) ASSUME_TAC THENL
     [EXPAND_TAC "W" THEN REWRITE_TAC [UNIONS_SUBSET, FORALL_IN_IMAGE] THEN
      ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN ([[compact(W:complex->bool)]]) ASSUME_TAC THENL
     [EXPAND_TAC "W" THEN MATCH_MP_TAC COMPACT_UNIONS THEN
      ASM_SIMP_TAC [FINITE_IMAGE, FORALL_IN_IMAGE, COMPACT_CBALL],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[open((:complex) DIFF W)]]) ASSUME_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC [OPEN_UNIV] THEN
      ASM_MESON_TAC [COMPACT_IMP_CLOSED], ALL_TAC] THEN
    SUBGOAL_THEN ([[!z:complex a:complex.
      &2 * r <= norm(z - a)
      ==> hermite_cutoff((norm(z - a) pow 2 - r pow 2) / cc) = &0]]) ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC HERMITE_CUTOFF_GE_1 THEN
      ASM_SIMP_TAC [REAL_LE_RDIV_EQ, REAL_MUL_LID] THEN
      SUBGOAL_THEN ([[(&2 * r) pow 2 <= norm(z - a:complex) pow 2]]) MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!z:complex a:complex.
      norm(z - a) <= r
      ==> hermite_cutoff((norm(z - a) pow 2 - r pow 2) / cc) = &1]]) ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC HERMITE_CUTOFF_LE_0 THEN
      SUBGOAL_THEN ([[norm(z - a:complex) pow 2 <= r pow 2]]) MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC [NORM_POS_LE],
        ALL_TAC] THEN
      REWRITE_TAC [real_div, h2,
                  (← HolLight.GSYM REAL_MUL_LNEG)] THEN
      DISCH_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC [REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!z:complex a:complex.
      &0 <= hermite_cutoff((norm(z - a) pow 2 - r pow 2) / cc)]]) ASSUME_TAC THENL
     [REWRITE_TAC [HERMITE_CUTOFF_NONNEG], ALL_TAC] THEN
    SUBGOAL_THEN ([[!z:complex. ~(z IN W)
     ==> hermite_cutoff(&1 - sum A (\a:complex.
           hermite_cutoff((norm(z - a) pow 2 - r pow 2) / cc))) %
         (f:complex->complex) z = vec 0]]) ASSUME_TAC THENL
     [X_GEN_TAC ([[z:complex]]) THEN DISCH_TAC THEN
      SUBGOAL_THEN ([[!b:complex. b IN A ==> cball(b, &2 * r) SUBSET W]]) ASSUME_TAC THENL
       [X_GEN_TAC ([[b:complex]]) THEN DISCH_TAC THEN EXPAND_TAC "W" THEN
        REWRITE_TAC [UNIONS_IMAGE, SUBSET, IN_ELIM_THM] THEN
        X_GEN_TAC ([[y:complex]]) THEN DISCH_TAC THEN
        EXISTS_TAC ([[b:complex]]) THEN ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[sum A (\a:complex. hermite_cutoff(
          (norm(z - a) pow 2 - r pow 2) / cc)) = &0]]) (fun th => REWRITE_TAC [th, REAL_SUB_RZERO]) THENL
       [MATCH_MP_TAC SUM_EQ_0 THEN
        X_GEN_TAC ([[a:complex]]) THEN DISCH_TAC THEN BETA_TAC THEN
        FIRST_X_ASSUM (fun bz => MATCH_MP_TAC bz) THEN
        SUBGOAL_THEN ([[~(z:complex IN cball(a, &2 * r))]]) MP_TAC THENL
         [SUBGOAL_THEN ([[cball(a:complex, &2 * r) SUBSET W]]) MP_TAC THENL
           [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
            ASM_MESON_TAC [SUBSET]],
          REWRITE_TAC [IN_CBALL, SessionMultiLib.Vectors.dist, NORM_SUB, REAL_NOT_LE] THEN
          REAL_ARITH_TAC2],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[hermite_cutoff(&1) = &0]]) SUBST1_TAC THENL
       [MATCH_MP_TAC HERMITE_CUTOFF_GE_1 THEN REAL_ARITH_TAC2, ALL_TAC] THEN
      REWRITE_TAC [VECTOR_MUL_LZERO],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!z:complex. z IN K
     ==> &1 <= sum A (\a. hermite_cutoff(
           (norm(z - a) pow 2 - r pow 2) / cc))]]) ASSUME_TAC THENL
     [X_GEN_TAC ([[z:complex]]) THEN DISCH_TAC THEN
      SUBGOAL_THEN ([[?a:complex. a IN A /\ norm(z - a) < r]]) MP_TAC THENL
       [EXPAND_TAC "r" THEN
        SUBGOAL_THEN ([[(z:complex) IN UNIONS(IMAGE (\x:complex. ball(x, e / &3)) A)]]) MP_TAC THENL
         [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN
        REWRITE_TAC [UNIONS_IMAGE, IN_ELIM_THM] THEN
        REWRITE_TAC [IN_BALL, SessionMultiLib.Vectors.dist] THEN
        MESON_TAC [NORM_SUB],
        ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[a0:complex]]) STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC ([[sum {a0:complex} (\a. hermite_cutoff(
                  (norm(z - a) pow 2 - r pow 2) / cc))]]) THEN
      CONJ_TAC THENL
       [REWRITE_TAC [SUM_SING] THEN BETA_TAC THEN
        SUBGOAL_THEN ([[hermite_cutoff((norm(z - a0:complex) pow 2 - r pow 2) / cc) = &1]]) (fun th => REWRITE_TAC [th, REAL_LE_REFL]) THEN
        FIRST_X_ASSUM (fun bz => MATCH_MP_TAC bz) THEN ASM_REAL_ARITH_TAC,
        ALL_TAC] THEN
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      CONV_TAC (HolLight.DEPTH_CONV HolLight.BETA_CONV) THEN
      ASM_REWRITE_TAC [IN_DIFF] THEN HolLight.ASM SET_TAC [],
      ALL_TAC] THEN
    EXISTS_TAC ([[\w:complex.
       hermite_cutoff(&1 - sum A (\a:complex.
         hermite_cutoff((norm(w - a) pow 2 - r pow 2) / cc))) %
       (f:complex->complex) w]]) THEN
    CONV_TAC (HolLight.DEPTH_CONV HolLight.BETA_CONV) THEN
    REPEAT CONJ_TAC THENL
     [SIMP_TAC [DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT,
               OPEN_UNIV, IN_UNIV] THEN
      X_GEN_TAC ([[z:complex]]) THEN
      ASM_CASES_TAC ([[(z:complex) IN u]]) THENL
       [MATCH_MP_TAC DIFFERENTIABLE_MUL_AT THEN CONJ_TAC THENL
         [SUBGOAL_THEN ([[(lift o (\w:complex. hermite_cutoff(&1 -
              sum A (\a:complex. hermite_cutoff(
                (norm(w - a) pow 2 - r pow 2) / cc))))) =
           (lift o hermite_cutoff o drop) o
           (\w:complex. lift(&1 - sum A (\a:complex. hermite_cutoff(
                (norm(w - a) pow 2 - r pow 2) / cc))))]]) SUBST1_TAC THENL
           [REWRITE_TAC [FUN_EQ_THM, o_THM, LIFT_DROP], ALL_TAC] THEN
          MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN CONJ_TAC THENL
           [SUBGOAL_THEN ([[(\w:complex. lift(&1 - sum A (\a:complex. hermite_cutoff(
                  (norm(w - a) pow 2 - r pow 2) / cc)))) =
             (\w. lift(&1) - vsum A (\a:complex. lift(hermite_cutoff(
                  (norm(w - a) pow 2 - r pow 2) / cc))))]]) SUBST1_TAC THENL
             [REWRITE_TAC [FUN_EQ_THM, LIFT_SUB, LIFT_SUM, o_DEF],
              ALL_TAC] THEN
            MATCH_MP_TAC DIFFERENTIABLE_SUB THEN CONJ_TAC THENL
             [REWRITE_TAC [DIFFERENTIABLE_CONST],
              MATCH_MP_TAC DIFFERENTIABLE_VSUM THEN ASM_REWRITE_TAC [] THEN
              X_GEN_TAC ([[a:complex]]) THEN DISCH_TAC THEN
              REWRITE_TAC [differentiable] THEN
              EXISTS_TAC ([[\h:complex. lift(
              hermite_cutoff_deriv(
                (norm(z - a) pow 2 - r pow 2) / cc) *
              (&2 * ((z - a) dot h)) / cc)]]) THEN
              MATCH_MP_TAC HERMITE_CUTOFF_SHIFTED_HAS_DERIVATIVE THEN
              ASM_REWRITE_TAC []],
            REWRITE_TAC [HERMITE_CUTOFF_DIFFERENTIABLE]],
          UNDISCH_TAC ([[(f:complex->complex) differentiable_on u]]) THEN
          ASM_SIMP_TAC [DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT] THEN
          DISCH_THEN (MP_TAC o HolLight.SPEC ([[z:complex]])) THEN
          ASM_REWRITE_TAC []],
        SUBGOAL_THEN ([[~((z:complex) IN W)]]) ASSUME_TAC THENL
         [HolLight.ASM SET_TAC [], ALL_TAC] THEN
        REWRITE_TAC [differentiable] THEN
        EXISTS_TAC ([[(\h:complex. (vec 0):complex)]]) THEN
        MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
        EXISTS_TAC ([[(\w:complex. (vec 0):complex)]]) THEN
        EXISTS_TAC ([[(:complex) DIFF W]]) THEN
        ASM_REWRITE_TAC [IN_DIFF, IN_UNIV] THEN CONJ_TAC THENL
         [X_GEN_TAC ([[y:complex]]) THEN REWRITE_TAC [IN_DIFF, IN_UNIV] THEN
          DISCH_TAC THEN CONV_TAC HolLight.SYM_CONV THEN ASM_MESON_TAC [],
          REWRITE_TAC [HAS_DERIVATIVE_CONST]]],
      GEN_TAC THEN
      SUBGOAL_THEN ([[!z':complex.
        ((\w:complex. lift(hermite_cutoff(&1 -
            sum A (\a:complex. hermite_cutoff(
              (norm(w - a) pow 2 - r pow 2) / cc)))))
         has_derivative
         (\h':complex. hermite_cutoff_deriv(&1 -
            sum A (\a:complex. hermite_cutoff(
              (norm(z' - a) pow 2 - r pow 2) / cc))) %
           ((vec 0):real^1 - vsum A (\a:complex. lift(
              hermite_cutoff_deriv(
                (norm(z' - a) pow 2 - r pow 2) / cc) *
              (&2 * ((z' - a) dot h')) / cc)))))
         (at z')]]) ASSUME_TAC THENL
       [X_GEN_TAC ([[z':complex]]) THEN
        SUBGOAL_THEN ([[(\w:complex. lift(hermite_cutoff(&1 -
            sum A (\a:complex. hermite_cutoff(
              (norm(w - a) pow 2 - r pow 2) / cc))))) =
         (lift o hermite_cutoff o drop) o
         (\w. lift(&1 - sum A (\a:complex. hermite_cutoff(
              (norm(w - a) pow 2 - r pow 2) / cc))))]]) SUBST1_TAC THENL
         [REWRITE_TAC [FUN_EQ_THM, o_THM, LIFT_DROP], ALL_TAC] THEN
        SUBGOAL_THEN ([[(\h':complex. hermite_cutoff_deriv(&1 -
            sum A (\a:complex. hermite_cutoff(
              (norm(z' - a) pow 2 - r pow 2) / cc))) %
           ((vec 0):real^1 - vsum A (\a:complex. lift(
              hermite_cutoff_deriv(
                (norm(z' - a) pow 2 - r pow 2) / cc) *
              (&2 * ((z' - a) dot h')) / cc)))) =
         (\v:real^1. hermite_cutoff_deriv(
            drop(lift(&1 - sum A (\a:complex. hermite_cutoff(
              (norm(z' - a) pow 2 - r pow 2) / cc))))) % v) o
         (\h'. (vec 0):real^1 - vsum A (\a:complex. lift(
              hermite_cutoff_deriv(
                (norm(z' - a) pow 2 - r pow 2) / cc) *
              (&2 * ((z' - a) dot h')) / cc)))]]) SUBST1_TAC THENL
         [REWRITE_TAC [FUN_EQ_THM, o_THM, LIFT_DROP], ALL_TAC] THEN
        MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
         [SUBGOAL_THEN ([[(\w:complex. lift(&1 - sum A (\a:complex. hermite_cutoff(
                (norm(w - a) pow 2 - r pow 2) / cc)))) =
           (\w. lift(&1) - vsum A (\a:complex. lift(hermite_cutoff(
                (norm(w - a) pow 2 - r pow 2) / cc))))]]) SUBST1_TAC THENL
           [REWRITE_TAC [FUN_EQ_THM, LIFT_SUB, LIFT_SUM, o_DEF],
            ALL_TAC] THEN
          MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN CONJ_TAC THENL
           [REWRITE_TAC [HAS_DERIVATIVE_CONST],
            MATCH_MP_TAC HAS_DERIVATIVE_VSUM THEN ASM_REWRITE_TAC [] THEN
            X_GEN_TAC ([[a:complex]]) THEN DISCH_TAC THEN
            MATCH_MP_TAC HERMITE_CUTOFF_SHIFTED_HAS_DERIVATIVE THEN
            ASM_REWRITE_TAC []],
          MP_TAC (← HolLight.SPEC ([[&1 - sum A (\a:complex. hermite_cutoff(
            (norm(z' - a:complex) pow 2 - r pow 2) / cc))]]) HAS_REAL_DERIVATIVE_HERMITE_EXPLICIT) THEN
          REWRITE_TAC [HAS_REAL_FRECHET_DERIVATIVE_AT, o_DEF, LIFT_DROP]],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[(\z':complex.
         hermite_cutoff_deriv(&1 -
           sum A (\a:complex. hermite_cutoff(
             (norm(z' - a) pow 2 - r pow 2) / cc))) %
         ((vec 0):real^1 - vsum A (\a:complex. lift(
           hermite_cutoff_deriv(
             (norm(z' - a) pow 2 - r pow 2) / cc) *
           (&2 * ((z' - a) dot h)) / cc))))
       continuous_on (:complex)]]) ASSUME_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
         [REWRITE_TAC [o_DEF] THEN
          SUBGOAL_THEN ([[(\z':complex. lift(hermite_cutoff_deriv(&1 -
             sum A (\a:complex. hermite_cutoff(
               (norm(z' - a) pow 2 - r pow 2) / cc))))) =
           (lift o hermite_cutoff_deriv o drop) o
           (\z'. lift(&1 - sum A (\a:complex. hermite_cutoff(
               (norm(z' - a) pow 2 - r pow 2) / cc))))]]) SUBST1_TAC THENL
           [REWRITE_TAC [FUN_EQ_THM, o_THM, LIFT_DROP], ALL_TAC] THEN
          MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
           [SUBGOAL_THEN ([[(\z':complex. lift(&1 - sum A (\a:complex. hermite_cutoff(
                  (norm(z' - a) pow 2 - r pow 2) / cc)))) =
             (\z'. lift(&1) - vsum A (\a:complex. lift(hermite_cutoff(
                  (norm(z' - a) pow 2 - r pow 2) / cc))))]]) SUBST1_TAC THENL
             [REWRITE_TAC [FUN_EQ_THM, LIFT_SUB, LIFT_SUM, o_DEF],
              ALL_TAC] THEN
            MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
             [REWRITE_TAC [CONTINUOUS_ON_CONST],
              MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN ASM_REWRITE_TAC [] THEN
              X_GEN_TAC ([[a:complex]]) THEN DISCH_TAC THEN
              ASM_SIMP_TAC [HC_SHIFTED_CONTINUOUS_ON]],
            MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
            EXISTS_TAC ([[(:real^1)]]) THEN
            REWRITE_TAC [SUBSET_UNIV, HERMITE_CUTOFF_DERIV_CONTINUOUS]],
          MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
           [REWRITE_TAC [CONTINUOUS_ON_CONST],
            MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN ASM_REWRITE_TAC [] THEN
            X_GEN_TAC ([[a:complex]]) THEN DISCH_TAC THEN
            SUBGOAL_THEN ([[(\z':complex. lift(
              hermite_cutoff_deriv(
                (norm(z' - a) pow 2 - r pow 2) / cc) *
              (&2 * ((z' - a) dot h)) / cc)) =
             (\z'. hermite_cutoff_deriv(
                (norm(z' - a) pow 2 - r pow 2) / cc) %
               lift((&2 * ((z' - a) dot h)) / cc))]]) SUBST1_TAC THENL
             [REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
              SIMP_TAC [CART_EQ, DIMINDEX_1, FORALL_1,
                VECTOR_MUL_COMPONENT, lift, LAMBDA_BETA, LE_REFL] THEN
              REAL_ARITH_TAC2,
              ALL_TAC] THEN
            MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
             [REWRITE_TAC [o_DEF] THEN
              ASM_SIMP_TAC [HCD_SHIFTED_CONTINUOUS_ON],
              SUBGOAL_THEN ([[(\z':complex. lift((&2 * ((z' - a) dot h)) / cc)) =
               (\z'. (inv cc * &2) % lift((z' - a) dot h))]]) SUBST1_TAC THENL
               [REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
                SIMP_TAC [CART_EQ, DIMINDEX_1, FORALL_1,
                  VECTOR_MUL_COMPONENT, lift, LAMBDA_BETA, LE_REFL] THEN
                UNDISCH_TAC ([[&0 < cc]]) THEN CONV_TAC rf,
                MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
                MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN CONJ_TAC THENL
                 [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
                  REWRITE_TAC [CONTINUOUS_ON_ID, CONTINUOUS_ON_CONST],
                  REWRITE_TAC [CONTINUOUS_ON_CONST]]]]]],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[(\z':complex.
        frechet_derivative
          (\w. hermite_cutoff(&1 -
            sum A (\a:complex. hermite_cutoff(
              (norm(w - a) pow 2 - r pow 2) / cc))) %
           (f:complex->complex) w) (at z') h)
       continuous_on u]]) ASSUME_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
        EXISTS_TAC ([[\z':complex.
          hermite_cutoff(&1 -
            sum A (\a:complex. hermite_cutoff(
              (norm(z' - a) pow 2 - r pow 2) / cc))) %
          frechet_derivative (f:complex->complex) (at z') h +
          drop(hermite_cutoff_deriv(&1 -
            sum A (\a:complex. hermite_cutoff(
              (norm(z' - a) pow 2 - r pow 2) / cc))) %
            ((vec 0):real^1 - vsum A (\a:complex. lift(
              hermite_cutoff_deriv(
                (norm(z' - a) pow 2 - r pow 2) / cc) *
              (&2 * ((z' - a) dot h)) / cc)))) %
          (f:complex->complex) z']]) THEN
        CONJ_TAC THENL
         [X_GEN_TAC ([[z':complex]]) THEN DISCH_TAC THEN
          CONV_TAC HolLight.SYM_CONV THEN
          MP_TAC (← HolLight.ISPECL [([[\z'':complex. hermite_cutoff(&1 -
              sum A (\a:complex. hermite_cutoff(
                (norm(z'' - a) pow 2 - r pow 2) / cc))) %
             (f:complex->complex) z'']]),
             ([[\h':complex.
              hermite_cutoff(&1 -
                sum A (\a:complex. hermite_cutoff(
                  (norm(z' - a) pow 2 - r pow 2) / cc))) %
              frechet_derivative (f:complex->complex) (at z') h' +
              drop(hermite_cutoff_deriv(&1 -
                sum A (\a:complex. hermite_cutoff(
                  (norm(z' - a) pow 2 - r pow 2) / cc))) %
                ((vec 0):real^1 - vsum A (\a:complex. lift(
                  hermite_cutoff_deriv(
                    (norm(z' - a) pow 2 - r pow 2) / cc) *
                  (&2 * ((z' - a) dot h')) / cc)))) %
              (f:complex->complex) z']]),
             ([[z':complex]])] FRECHET_DERIVATIVE_AT) THEN
          CONV_TAC (HolLight.DEPTH_CONV HolLight.BETA_CONV) THEN
          ANTS_TAC THENL
           [MP_TAC (← HolLight.ISPECL [([[\z'':complex. hermite_cutoff(&1 -
                sum A (\a:complex. hermite_cutoff(
                  (norm(z'' - a) pow 2 - r pow 2) / cc)))]]),
               ([[\h':complex.
                drop(hermite_cutoff_deriv(&1 -
                  sum A (\a:complex. hermite_cutoff(
                    (norm(z' - a) pow 2 - r pow 2) / cc))) %
                  ((vec 0):real^1 - vsum A (\a:complex. lift(
                    hermite_cutoff_deriv(
                      (norm(z' - a) pow 2 - r pow 2) / cc) *
                    (&2 * ((z' - a) dot h')) / cc))))]]),
               ([[f:complex->complex]]),
               ([[frechet_derivative (f:complex->complex) (at z')]]),
               ([[z':complex]])] HAS_DERIVATIVE_MUL_AT) THEN
            REWRITE_TAC [o_DEF] THEN
            DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
             [SUBGOAL_THEN ([[(\h':complex.
                lift(drop(hermite_cutoff_deriv(&1 -
                  sum A (\a:complex. hermite_cutoff(
                    (norm(z' - a) pow 2 - r pow 2) / cc))) %
                  ((vec 0):real^1 - vsum A (\a:complex. lift(
                    hermite_cutoff_deriv(
                      (norm(z' - a) pow 2 - r pow 2) / cc) *
                    (&2 * ((z' - a) dot h')) / cc)))))) =
               (\h':complex.
                hermite_cutoff_deriv(&1 -
                  sum A (\a:complex. hermite_cutoff(
                    (norm(z' - a) pow 2 - r pow 2) / cc))) %
                  ((vec 0):real^1 - vsum A (\a:complex. lift(
                    hermite_cutoff_deriv(
                      (norm(z' - a) pow 2 - r pow 2) / cc) *
                    (&2 * ((z' - a) dot h')) / cc))))]]) SUBST1_TAC THENL
               [REWRITE_TAC [FUN_EQ_THM, LIFT_DROP], ALL_TAC] THEN
              FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[z':complex]])) THEN
              REWRITE_TAC [],
              REWRITE_TAC [(← HolLight.GSYM FRECHET_DERIVATIVE_WORKS)] THEN
              UNDISCH_TAC ([[(f:complex->complex) differentiable_on u]]) THEN
              ASM_SIMP_TAC [DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT] THEN
              DISCH_THEN (MP_TAC o HolLight.SPEC ([[z':complex]])) THEN
              ASM_REWRITE_TAC []],
            DISCH_THEN (fun th => HolLight.tactic_of do
        pure (REWRITE_TAC [(← HolLight.GSYM th)])) THEN REFL_TAC],
          MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THENL
           [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
             [REWRITE_TAC [o_DEF] THEN
              MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
              EXISTS_TAC ([[(:complex)]]) THEN REWRITE_TAC [SUBSET_UNIV] THEN
              SUBGOAL_THEN ([[(\z':complex. lift(hermite_cutoff(&1 -
                sum A (\a:complex. hermite_cutoff(
                  (norm(z' - a) pow 2 - r pow 2) / cc))))) =
               (lift o hermite_cutoff o drop) o
               (\z'. lift(&1 - sum A (\a:complex. hermite_cutoff(
                  (norm(z' - a) pow 2 - r pow 2) / cc))))]]) SUBST1_TAC THENL
               [REWRITE_TAC [FUN_EQ_THM, o_THM, LIFT_DROP], ALL_TAC] THEN
              MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
               [SUBGOAL_THEN ([[(\z':complex. lift(&1 - sum A (\a:complex.
                   hermite_cutoff(
                     (norm(z' - a) pow 2 - r pow 2) / cc)))) =
                 (\z'. lift(&1) - vsum A (\a:complex. lift(
                   hermite_cutoff(
                     (norm(z' - a) pow 2 - r pow 2) / cc))))]]) SUBST1_TAC THENL
                 [REWRITE_TAC [FUN_EQ_THM, LIFT_SUB, LIFT_SUM, o_DEF],
                  ALL_TAC] THEN
                MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
                 [REWRITE_TAC [CONTINUOUS_ON_CONST],
                  MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN
                  ASM_REWRITE_TAC [] THEN
                  X_GEN_TAC ([[a:complex]]) THEN DISCH_TAC THEN
                  ASM_SIMP_TAC [HC_SHIFTED_CONTINUOUS_ON]],
                MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
                EXISTS_TAC ([[(:real^1)]]) THEN
                REWRITE_TAC [SUBSET_UNIV, HERMITE_CUTOFF_CONTINUOUS]],
              ASM_REWRITE_TAC []],
            MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
             [REWRITE_TAC [o_DEF] THEN
              REWRITE_TAC [LIFT_DROP] THEN
              MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
              EXISTS_TAC ([[(:complex)]]) THEN
              ASM_REWRITE_TAC [SUBSET_UNIV],
              MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
              EXISTS_TAC ([[u:complex->bool]]) THEN
              REWRITE_TAC [SUBSET_REFL] THEN
              MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
              ASM_REWRITE_TAC []]]],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[(\z':complex.
        frechet_derivative
          (\w. hermite_cutoff(&1 -
            sum A (\a:complex. hermite_cutoff(
              (norm(w - a) pow 2 - r pow 2) / cc))) %
           (f:complex->complex) w) (at z') h)
       continuous_on ((:complex) DIFF W)]]) ASSUME_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
        EXISTS_TAC ([[(\z':complex. (vec 0):complex)]]) THEN
        CONJ_TAC THENL
         [X_GEN_TAC ([[z':complex]]) THEN REWRITE_TAC [IN_DIFF, IN_UNIV] THEN
          DISCH_TAC THEN CONV_TAC HolLight.SYM_CONV THEN
          MP_TAC (← HolLight.ISPECL [([[\w:complex. hermite_cutoff(&1 -
              sum A (\a:complex. hermite_cutoff(
                (norm(w - a) pow 2 - r pow 2) / cc))) %
             (f:complex->complex) w]]),
             ([[\h':complex. (vec 0):complex]]),
             ([[z':complex]])] FRECHET_DERIVATIVE_AT) THEN
          CONV_TAC (HolLight.DEPTH_CONV HolLight.BETA_CONV) THEN
          ANTS_TAC THENL
           [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
            EXISTS_TAC ([[(\w:complex. (vec 0):complex)]]) THEN
            EXISTS_TAC ([[(:complex) DIFF W]]) THEN
            ASM_REWRITE_TAC [IN_DIFF, IN_UNIV] THEN CONJ_TAC THENL
             [X_GEN_TAC ([[y:complex]]) THEN REWRITE_TAC [IN_DIFF, IN_UNIV] THEN
              DISCH_TAC THEN CONV_TAC HolLight.SYM_CONV THEN ASM_MESON_TAC [],
              REWRITE_TAC [HAS_DERIVATIVE_CONST]],
            DISCH_THEN (fun th => HolLight.tactic_of do
        pure (REWRITE_TAC [(← HolLight.GSYM th)])) THEN REWRITE_TAC []],
          REWRITE_TAC [CONTINUOUS_ON_CONST]],
        ALL_TAC] THEN
      SIMP_TAC [CONTINUOUS_ON_EQ_CONTINUOUS_AT, OPEN_UNIV, IN_UNIV] THEN
      X_GEN_TAC ([[w:complex]]) THEN
      ASM_CASES_TAC ([[(w:complex) IN u]]) THENL
       [ASM_MESON_TAC [CONTINUOUS_ON_EQ_CONTINUOUS_AT],
        SUBGOAL_THEN ([[(w:complex) IN (:complex) DIFF W]]) ASSUME_TAC THENL
         [REWRITE_TAC [IN_DIFF, IN_UNIV] THEN HolLight.ASM SET_TAC [],
          ALL_TAC] THEN
        ASM_MESON_TAC [CONTINUOUS_ON_EQ_CONTINUOUS_AT]],
      MATCH_MP_TAC BOUNDED_SUBSET THEN
      EXISTS_TAC ([[W:complex->bool]]) THEN CONJ_TAC THENL
       [ASM_MESON_TAC [COMPACT_IMP_BOUNDED], ALL_TAC] THEN
      REWRITE_TAC [SUBSET, support, IN_ELIM_THM, NEUTRAL_VECTOR_ADD,
                  IN_UNIV] THEN
      ASM_MESON_TAC [],
      X_GEN_TAC ([[z:complex]]) THEN DISCH_TAC THEN
      SUBGOAL_THEN ([[&1 <= sum A (\a:complex. hermite_cutoff(
            (norm(z - a) pow 2 - r pow 2) / cc))]]) ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN ([[hermite_cutoff(&1 - sum A (\a:complex.
         hermite_cutoff((norm(z - a) pow 2 - r pow 2) / cc))) = &1]]) SUBST1_TAC THENL
       [MATCH_MP_TAC HERMITE_CUTOFF_LE_0 THEN ASM_REAL_ARITH_TAC,
        ALL_TAC] THEN
      REWRITE_TAC [VECTOR_MUL_LID]])
  : ExceptT String IO thm).run
#eval SMOOTH_EXTENSION_FROM_OPEN

/- ========================================================================= -/
/- Product-space absolute integrability for the Cauchy kernel integrand.     -/
/- Factored out from FUBINI_PATH_AREA to expose integrability separately.    -/
/- Does NOT need simple_path or pathfinish = pathstart.                      -/
/- ========================================================================= -/

#eval phrase 104
def ABSOLUTELY_INTEGRABLE_CAUCHY_PATH_PRODUCT : thm := keep "ABSOLUTELY_INTEGRABLE_CAUCHY_PATH_PRODUCT" fun _ => (do
  let h2 ← rr (← ExceptT.mk [[&0 <= x /\ x <= C ==> abs(x) <= C]])
  let h1 ← tt (← ExceptT.mk [[~(~p) <=> p]])
  prove ([[!u:complex->complex g:real^1->complex.
        u continuous_on (:complex) /\
        bounded (support (+) u (:complex)) /\
        g absolutely_continuous_on interval[vec 0,vec 1]
        ==> (\p:real^(1,2)finite_sum.
                if fstcart p IN interval[vec 0,vec 1]
                then u(sndcart p) / (sndcart p - g(fstcart p)) *
                     vector_derivative g (at (fstcart p))
                else vec 0)
            absolutely_integrable_on (:real^(1,2)finite_sum)]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[!w:complex. (\z. u(z:complex) / (z - w))
                 absolutely_integrable_on (:complex)]]) ASSUME_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC CAUCHY_KERNEL_ABSOLUTELY_INTEGRABLE THEN
     ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN ([[(\p:real^(1,2)finite_sum.
        if fstcart p IN interval[vec 0,vec 1]
        then u(sndcart p:complex) / (sndcart p - g(fstcart p)) *
             vector_derivative g (at (fstcart p))
        else vec 0)
     measurable_on (:real^(1,2)finite_sum)]]) MP_TAC THENL
    [MATCH_MP_TAC MEASURABLE_ON_FUBINI_INTEGRAND THEN
     ASM_REWRITE_TAC [], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP FUBINI_TONELLI) THEN
    DISCH_THEN (fun th => REWRITE_TAC [th]) THEN
    REWRITE_TAC [FSTCART_PASTECART, SNDCART_PASTECART] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN ([[{x:real^1 | ~((\y:complex.
          if x IN interval[vec 0,vec 1]
          then u y / (y - g x) * vector_derivative g (at x)
          else vec 0)
          absolutely_integrable_on (:complex))} = {}]]) SUBST1_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY] THEN
        X_GEN_TAC ([[t:real^1]]) THEN
        REWRITE_TAC [h1] THEN
        ASM_CASES_TAC ([[t:real^1 IN interval[vec 0,vec 1] ]]) THENL
         [ASM_REWRITE_TAC [] THEN
          MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_COMPLEX_RMUL THEN
          MATCH_MP_TAC CAUCHY_KERNEL_ABSOLUTELY_INTEGRABLE THEN
          ASM_REWRITE_TAC [],
          ASM_REWRITE_TAC [absolutely_integrable_on,
                          NORM_0, LIFT_NUM, INTEGRABLE_0]],
        REWRITE_TAC [NEGLIGIBLE_EMPTY]],
      SUBGOAL_THEN ([[(\x:real^1. integral (:complex)
         (\y. lift(norm(if x IN interval[vec 0,vec 1]
                then u y / (y - g x) * vector_derivative g (at x)
                else vec 0)))) =
       (\x. if x IN interval[vec 0,vec 1]
            then norm(vector_derivative g (at x)) %
                 integral (:complex)
                   (\y. lift(norm(u y / (y - (g:real^1->complex) x))))
            else vec 0)]]) SUBST1_TAC THENL
      [REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC ([[x:real^1]]) THEN
       COND_CASES_TAC THENL
        [ASM_REWRITE_TAC [] THEN
         SUBGOAL_THEN ([[(\y:complex. lift(norm(u y / (y - g(x:real^1)) *
            vector_derivative g (at x)))) =
          (\y. norm(vector_derivative g (at x)) %
               lift(norm(u y / (y - g x))))]]) SUBST1_TAC THENL
          [REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
           REWRITE_TAC [COMPLEX_NORM_MUL] THEN
           ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
           REWRITE_TAC [LIFT_CMUL], ALL_TAC] THEN
         MATCH_MP_TAC INTEGRAL_CMUL THEN
         MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
         MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
         MATCH_MP_TAC CAUCHY_KERNEL_ABSOLUTELY_INTEGRABLE THEN
         ASM_REWRITE_TAC [],
         ASM_REWRITE_TAC [NORM_0, LIFT_NUM, INTEGRAL_0]], ALL_TAC] THEN
      REWRITE_TAC [INTEGRABLE_RESTRICT_UNIV] THEN
      MP_TAC (← HolLight.ISPECL [([[u:complex->complex]]),
        ([[path_image(g:real^1->complex)]])] CAUCHY_KERNEL_NORM_UNIFORM_BOUND) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC COMPACT_PATH_IMAGE THEN
        ASM_MESON_TAC [ABSOLUTELY_CONTINUOUS_IMP_PATH], ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[C:real]]) STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
      EXISTS_TAC ([[(\x:real^1. C % lift(norm(
      vector_derivative (g:real^1->complex) (at x))))]]) THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CAUCHY_KERNEL_WEIGHTED_MEASURABLE THEN
        ASM_REWRITE_TAC [],
        MATCH_MP_TAC INTEGRABLE_CMUL THEN
        MP_TAC (← HolLight.ISPEC ([[g:real^1->complex]]) ABSOLUTELY_INTEGRABLE_VECTOR_DERIVATIVE_ABSOLUTELY_CONTINUOUS) THEN
        ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [absolutely_integrable_on] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC [],
        BETA_TAC THEN
        X_GEN_TAC ([[x:real^1]]) THEN
        REWRITE_TAC [IN_INTERVAL_1, DROP_VEC] THEN DISCH_TAC THEN
        REWRITE_TAC [NORM_MUL, real_abs, NORM_POS_LE] THEN
        REWRITE_TAC [DROP_CMUL, LIFT_DROP] THEN
        GEN_REWRITE_TAC HolLight.RAND_CONV [REAL_MUL_SYM] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL
         [REWRITE_TAC [NORM_POS_LE],
          REWRITE_TAC [NORM_REAL, (← HolLight.GSYM drop)] THEN
          MATCH_MP_TAC h2 THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC INTEGRAL_DROP_POS THEN CONJ_TAC THENL
             [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
              MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
              MATCH_MP_TAC CAUCHY_KERNEL_ABSOLUTELY_INTEGRABLE THEN
              ASM_REWRITE_TAC [],
              REWRITE_TAC [LIFT_DROP, NORM_POS_LE]],
            FIRST_X_ASSUM MATCH_MP_TAC THEN
            REWRITE_TAC [path_image, IN_IMAGE] THEN
            EXISTS_TAC ([[x:real^1]]) THEN
            ASM_REWRITE_TAC [IN_INTERVAL_1, DROP_VEC]]]]])
  : ExceptT String IO thm).run
#eval ABSOLUTELY_INTEGRABLE_CAUCHY_PATH_PRODUCT

/- ========================================================================= -/
/- Integrability of winding_number * dbar f without simple_path.             -/
/- Derived from the Fubini product-space integrability via:                  -/
/-   Fubini abs integ -> has_integral -> integrable ->                       -/
/-   INTEGRABLE_SPIKE -> INTEGRABLE_COMPLEX_LMUL_EQ                          -/
/- ========================================================================= -/

#eval phrase 105
def INTEGRABLE_WINDING_DBAR_PRODUCT : thm := keep "INTEGRABLE_WINDING_DBAR_PRODUCT" fun _ => (do
  prove ([[!f:complex->complex g:real^1->complex.
        (\z. wirtinger_dbar f z) continuous_on (:complex) /\
        bounded (support (+) (wirtinger_dbar f) (:complex)) /\
        g absolutely_continuous_on interval[vec 0,vec 1] /\
        pathfinish g = pathstart g
        ==> (\z. Cx(Re(winding_number(g,z))) *
              wirtinger_dbar f z) integrable_on (:complex)]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[\z:complex. wirtinger_dbar (f:complex->complex) z]]),
       ([[g:real^1->complex]])] ABSOLUTELY_INTEGRABLE_CAUCHY_PATH_PRODUCT) THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [ETA_AX]) THEN
    REWRITE_TAC [ETA_AX] THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP FUBINI_ABSOLUTELY_INTEGRABLE_ALT) THEN
    REWRITE_TAC [FSTCART_PASTECART, SNDCART_PASTECART] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC [INTEGRAL_IF_CONST, INTEGRAL_RESTRICT_UNIV] THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.MATCH_MP HAS_INTEGRAL_INTEGRABLE th))) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN ([[(\z:complex. --(Cx(&2) * Cx pi * ii) *
       (Cx(Re(winding_number(g:real^1->complex,z))) *
        wirtinger_dbar (f:complex->complex) z))
     integrable_on (:complex)]]) ASSUME_TAC THENL
     [MP_TAC (← HolLight.REWRITE_RULE [IMP_IMP] (← HolLight.ISPECL [([[(\z:complex. integral (interval[vec 0,vec 1])
        (\t:real^1. wirtinger_dbar (f:complex->complex) z /
                     (z - (g:real^1->complex) t) *
                     vector_derivative g (at t)))]]),
        ([[(\z:complex. --(Cx(&2) * Cx pi * ii) *
         (Cx(Re(winding_number(g:real^1->complex,z))) *
          wirtinger_dbar (f:complex->complex) z))]]),
        ([[path_image(g:real^1->complex)]]),
        ([[(:complex)]])] INTEGRABLE_SPIKE)) THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC [NEGLIGIBLE_ABSOLUTELY_CONTINUOUS_PATH_IMAGE],
        X_GEN_TAC ([[z:complex]]) THEN REWRITE_TAC [IN_DIFF, IN_UNIV] THEN
        DISCH_TAC THEN BETA_TAC THEN CONV_TAC HolLight.SYM_CONV THEN
        MP_TAC (← HolLight.ISPECL [([[g:real^1->complex]]), ([[z:complex]])] HAS_PATH_INTEGRAL_WINDING_NUMBER_AC) THEN
        ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
        FIRST_ASSUM (ASSUME_TAC o HolLight.MATCH_MP HAS_PATH_INTEGRAL_INTEGRABLE) THEN
        FIRST_ASSUM (ASSUME_TAC o HolLight.MATCH_MP PATH_INTEGRAL_UNIQUE) THEN
        SUBGOAL_THEN ([[(\t:real^1. Cx(&1) / ((g:real^1->complex) t - z) *
                     vector_derivative g (at t))
         integrable_on interval[vec 0,vec 1] ]]) ASSUME_TAC THENL
         [UNDISCH_TAC ([[(\w:complex. Cx(&1) / (w - z))
                     path_integrable_on (g:real^1->complex)]]) THEN
          REWRITE_TAC [PATH_INTEGRABLE_ON],
          ALL_TAC] THEN
        SUBGOAL_THEN ([[(\t:real^1. Cx(&1) / (z - (g:real^1->complex) t) *
                     vector_derivative g (at t)) =
         (\t. --(Cx(&1) / (g t - z) * vector_derivative g (at t)))]]) ASSUME_TAC THENL
         [REWRITE_TAC [FUN_EQ_THM, complex_div, COMPLEX_MUL_LID] THEN
          X_GEN_TAC ([[t:real^1]]) THEN
          GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [(← HolLight.GSYM COMPLEX_NEG_SUB)] THEN
          REWRITE_TAC [COMPLEX_INV_NEG, COMPLEX_MUL_LNEG],
          ALL_TAC] THEN
        SUBGOAL_THEN ([[!t:real^1. wirtinger_dbar (f:complex->complex) z /
           (z - (g:real^1->complex) t) * vector_derivative g (at t) =
         wirtinger_dbar f z *
           (Cx(&1) / (z - g t) * vector_derivative g (at t))]]) (fun th => REWRITE_TAC [th]) THENL
         [GEN_TAC THEN
          REWRITE_TAC [complex_div, COMPLEX_MUL_LID, COMPLEX_MUL_ASSOC],
          ALL_TAC] THEN
        SUBGOAL_THEN ([[integral (interval[vec 0,vec 1])
           (\t:real^1. wirtinger_dbar (f:complex->complex) z *
             (Cx(&1) / (z - (g:real^1->complex) t) *
                 vector_derivative g (at t))) =
         wirtinger_dbar f z *
           integral (interval[vec 0,vec 1])
             (\t. Cx(&1) / (z - g t) * vector_derivative g (at t))]]) SUBST1_TAC THENL
         [MATCH_MP_TAC INTEGRAL_COMPLEX_LMUL THEN
          ASM_REWRITE_TAC [] THEN MATCH_MP_TAC INTEGRABLE_NEG THEN
          ASM_REWRITE_TAC [],
          ALL_TAC] THEN
        SUBGOAL_THEN ([[integral (interval[vec 0,vec 1])
           (\t:real^1. Cx(&1) / (z - (g:real^1->complex) t) *
                       vector_derivative g (at t)) =
         --(Cx(&2) * Cx pi * ii *
            winding_number(g:real^1->complex,z))]]) SUBST1_TAC THENL
         [ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [INTEGRAL_NEG] THEN
          AP_TERM_TAC THEN
          REWRITE_TAC [(← HolLight.GSYM PATH_INTEGRAL_INTEGRAL)] THEN
          ASM_REWRITE_TAC [],
          ALL_TAC] THEN
        SUBGOAL_THEN ([[winding_number(g:real^1->complex,z) =
         Cx(Re(winding_number(g,z)))]]) SUBST1_TAC THENL
         [REWRITE_TAC [(← HolLight.GSYM REAL), real] THEN
          SUBGOAL_THEN ([[complex_integer(winding_number(g:real^1->complex,z))]]) MP_TAC THENL
           [MATCH_MP_TAC INTEGER_WINDING_NUMBER THEN
            ASM_MESON_TAC [ABSOLUTELY_CONTINUOUS_IMP_PATH], ALL_TAC] THEN
          REWRITE_TAC [complex_integer] THEN SIMP_TAC [],
          ALL_TAC] THEN
        SIMPLE_COMPLEX_ARITH_TAC,
        BETA_TAC THEN ASM_REWRITE_TAC []],
      ALL_TAC] THEN
    UNDISCH_TAC ([[(\z:complex. --(Cx(&2) * Cx pi * ii) *
       (Cx(Re(winding_number(g:real^1->complex,z))) *
        wirtinger_dbar (f:complex->complex) z))
     integrable_on (:complex)]]) THEN
    REWRITE_TAC [INTEGRABLE_COMPLEX_LMUL_EQ] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [UNDISCH_TAC ([[--(Cx(&2) * Cx pi * ii) = Cx(&0)]]) THEN
      REWRITE_TAC [COMPLEX_NEG_EQ_0] THEN
      MP_TAC CX_2PII_NZ THEN MESON_TAC [],
      FIRST_X_ASSUM ACCEPT_TAC])
  : ExceptT String IO thm).run
#eval INTEGRABLE_WINDING_DBAR_PRODUCT

/- ========================================================================= -/
/- Most general Gauss-Green formula: no simple_path, local C^1.              -/
/- Uses smooth extension + Cauchy transform + Fubini.                        -/
/- ========================================================================= -/

#eval phrase 106
def COMPLEX_GREEN_ALT : thm := keep "COMPLEX_GREEN_ALT" fun _ => (do
  let complex_green_univ ← prove ([[!f:complex->complex g.
          f differentiable_on (:complex) /\
          (!h. (\z. frechet_derivative f (at z) h) continuous_on (:complex)) /\
          bounded (support (+) f (:complex)) /\
          g absolutely_continuous_on interval[vec 0,vec 1] /\
          pathfinish g = pathstart g
          ==> (\z. Cx(Re(winding_number(g,z))) *
                   wirtinger_dbar f z) integrable_on (:complex) /\
              f path_integrable_on g /\
              Cx(inv(&2)) / ii * path_integral g f =
              integral (:complex)
                (\z. Cx(Re(winding_number(g,z))) *
                     wirtinger_dbar f z)]])
     (REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[(\z. wirtinger_dbar (f:complex->complex) z) continuous_on (:complex)]]) ASSUME_TAC THENL
     [MATCH_MP_TAC WIRTINGER_DBAR_CONTINUOUS THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[bounded (support (+) (wirtinger_dbar (f:complex->complex)) (:complex))]]) ASSUME_TAC THENL
     [MATCH_MP_TAC WIRTINGER_DBAR_BOUNDED_SUPPORT THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!w. integral (:complex)
           (\z. wirtinger_dbar (f:complex->complex) z / (z - w)) =
         --(Cx pi * f w)]]) ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC CAUCHY_TRANSFORM_INVERTS_DBAR THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[(\z. Cx(Re(winding_number(g:real^1->complex,z))) *
          wirtinger_dbar (f:complex->complex) z) integrable_on (:complex)]]) ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_WINDING_DBAR_PRODUCT THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[(f:complex->complex) path_integrable_on g]]) ASSUME_TAC THENL
     [MATCH_MP_TAC PATH_INTEGRABLE_CONTINUOUS_ABSOLUTELY_CONTINUOUS THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC ([[(:complex)]]) THEN REWRITE_TAC [SUBSET_UNIV] THEN
        MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN ASM_REWRITE_TAC [],
        ASM_REWRITE_TAC []],
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN ([[--(Cx pi) * path_integral g (f:complex->complex) =
     integral (:complex)
       (\z. wirtinger_dbar f z *
            path_integral g (\w. Cx(&1) / (z - w)))]]) ASSUME_TAC THENL
     [SUBGOAL_THEN ([[path_integral g (\w. --(Cx pi) * (f:complex->complex) w) =
       --(Cx pi) * path_integral g f]]) ASSUME_TAC THENL
       [MATCH_MP_TAC PATH_INTEGRAL_COMPLEX_LMUL THEN ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[path_integral g
         (\w. integral (:complex)
                (\z. wirtinger_dbar (f:complex->complex) z / (z - w))) =
       integral (:complex)
         (\z. wirtinger_dbar f z *
              path_integral g (\w. Cx(&1) / (z - w)))]]) ASSUME_TAC THENL
       [MATCH_MP_TAC FUBINI_PATH_AREA THEN
        RULE_ASSUM_TAC (HolLight.REWRITE_RULE [ETA_AX]) THEN
        REWRITE_TAC [ETA_AX] THEN ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[(\w. integral (:complex)
              (\z. wirtinger_dbar (f:complex->complex) z / (z - w))) =
       (\w. --(Cx pi) * f w)]]) ASSUME_TAC THENL
       [REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
        ASM_REWRITE_TAC [COMPLEX_MUL_LNEG],
        ALL_TAC] THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[--(Cx pi) * path_integral g (f:complex->complex) =
     --(Cx(&2) * Cx pi * ii) *
     integral (:complex)
       (\z. Cx(Re(winding_number(g:real^1->complex,z))) *
            wirtinger_dbar f z)]]) ASSUME_TAC THENL
     [ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN ([[integral (:complex)
         (\z. wirtinger_dbar (f:complex->complex) z *
              path_integral g (\w. Cx(&1) / (z - w))) =
       integral (:complex)
         (\z. wirtinger_dbar f z *
              (--(Cx(&2) * Cx pi * ii *
                  Cx(Re(winding_number(g:real^1->complex,z))))))]]) SUBST1_TAC THENL
       [MATCH_MP_TAC INTEGRAL_SPIKE THEN
        EXISTS_TAC ([[path_image(g:real^1->complex)]]) THEN
        CONJ_TAC THENL
         [ASM_MESON_TAC [NEGLIGIBLE_ABSOLUTELY_CONTINUOUS_PATH_IMAGE], ALL_TAC] THEN
        X_GEN_TAC ([[z:complex]]) THEN REWRITE_TAC [IN_DIFF, IN_UNIV] THEN
        DISCH_TAC THEN AP_TERM_TAC THEN
        SUBGOAL_THEN ([[path_integral g (\w. Cx(&1) / (z - w)) =
         --(Cx(&2) * Cx pi * ii * winding_number(g:real^1->complex,z))]]) SUBST1_TAC THENL
         [MP_TAC (← HolLight.ISPECL [([[g:real^1->complex]]), ([[z:complex]])] HAS_PATH_INTEGRAL_WINDING_NUMBER_AC) THEN
          ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
          FIRST_ASSUM (ASSUME_TAC o HolLight.MATCH_MP HAS_PATH_INTEGRAL_INTEGRABLE) THEN
          FIRST_ASSUM (ASSUME_TAC o HolLight.MATCH_MP PATH_INTEGRAL_UNIQUE) THEN
          SUBGOAL_THEN ([[(\w:complex. Cx(&1) / (z - w)) =
           (\w. --(Cx(&1) / (w - z)))]]) SUBST1_TAC THENL
           [REWRITE_TAC [FUN_EQ_THM, complex_div, COMPLEX_MUL_LID] THEN
            X_GEN_TAC ([[w:complex]]) THEN
            GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [(← HolLight.GSYM COMPLEX_NEG_SUB)] THEN
            REWRITE_TAC [COMPLEX_INV_NEG],
            ALL_TAC] THEN
          ASM_SIMP_TAC [PATH_INTEGRAL_NEG] THEN
          ASM_REWRITE_TAC [] THEN SIMPLE_COMPLEX_ARITH_TAC,
          ALL_TAC] THEN
        REPEAT AP_TERM_TAC THEN
        REWRITE_TAC [(← HolLight.GSYM REAL), real] THEN
        SUBGOAL_THEN ([[complex_integer(winding_number(g:real^1->complex,z))]]) MP_TAC THENL
         [MATCH_MP_TAC INTEGER_WINDING_NUMBER THEN
          ASM_MESON_TAC [ABSOLUTELY_CONTINUOUS_IMP_PATH], ALL_TAC] THEN
        REWRITE_TAC [complex_integer] THEN SIMP_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[(\z. wirtinger_dbar (f:complex->complex) z *
            (--(Cx(&2) * Cx pi * ii *
                Cx(Re(winding_number(g:real^1->complex,z)))))) =
       (\z. --(Cx(&2) * Cx pi * ii) *
            (Cx(Re(winding_number(g,z))) * wirtinger_dbar f z))]]) SUBST1_TAC THENL
       [REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN SIMPLE_COMPLEX_ARITH_TAC,
        ALL_TAC] THEN
      ASM_SIMP_TAC [INTEGRAL_COMPLEX_LMUL],
      ALL_TAC] THEN
    MP_TAC CX_2PII_NZ THEN MP_TAC CX_PI_NZ THEN
    UNDISCH_TAC ([[--(Cx pi) * path_integral g (f:complex->complex) =
     --(Cx(&2) * Cx pi * ii) *
     integral (:complex)
       (\z. Cx(Re(winding_number(g:real^1->complex,z))) *
            wirtinger_dbar f z)]]) THEN
    REWRITE_TAC [CX_INV] THEN CONV_TAC cf)
  prove ([[!f:complex->complex g u.
        g absolutely_continuous_on interval[vec 0,vec 1] /\
        pathfinish g = pathstart g /\
        open u /\
        inside(path_image g) UNION path_image g SUBSET u /\
        f differentiable_on u /\
        (!h:complex. (\z. frechet_derivative f (at z) h) continuous_on u)
        ==> (\z. Cx(Re(winding_number(g,z))) *
                 wirtinger_dbar f z) integrable_on (:complex) /\
            f path_integrable_on g /\
            Cx(inv(&2)) / ii * path_integral g f =
            integral (:complex)
              (\z. Cx(Re(winding_number(g,z))) *
                   wirtinger_dbar f z)]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[f:complex->complex]]), ([[u:complex->bool]]),
                    ([[path_image g UNION inside(path_image g):complex->bool]])] SMOOTH_EXTENSION_FROM_OPEN) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC COMPACT_WITH_INSIDE THEN
        MATCH_MP_TAC COMPACT_PATH_IMAGE THEN
        ASM_MESON_TAC [ABSOLUTELY_CONTINUOUS_IMP_PATH], ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
      CONJ_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[ef:complex->complex]]) STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN ([[open(inside(path_image(g:real^1->complex)))]]) ASSUME_TAC THENL
     [MATCH_MP_TAC OPEN_INSIDE THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MATCH_MP_TAC COMPACT_PATH_IMAGE THEN
      ASM_MESON_TAC [ABSOLUTELY_CONTINUOUS_IMP_PATH], ALL_TAC] THEN
    SUBGOAL_THEN ([[!z. z IN inside(path_image g) ==>
     frechet_derivative (ef:complex->complex) (at z) =
     frechet_derivative f (at z)]]) ASSUME_TAC THENL
     [X_GEN_TAC ([[z:complex]]) THEN DISCH_TAC THEN
      CONV_TAC HolLight.SYM_CONV THEN
      MATCH_MP_TAC HAS_FRECHET_DERIVATIVE_UNIQUE_AT THEN
      MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
      EXISTS_TAC ([[ef:complex->complex]]) THEN
      EXISTS_TAC ([[inside(path_image(g:real^1->complex))]]) THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [X_GEN_TAC ([[w:complex]]) THEN DISCH_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [IN_UNION],
        ASM_MESON_TAC [FRECHET_DERIVATIVE_WORKS,
                      differentiable_on, IN_UNIV, WITHIN_UNIV]],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[(\z. Cx(Re(winding_number(g:real^1->complex,z))) *
          wirtinger_dbar (ef:complex->complex) z)
     integrable_on (:complex) /\
     ef path_integrable_on g /\
     Cx(inv(&2)) / ii * path_integral g ef =
     integral (:complex)
       (\z. Cx(Re(winding_number(g:real^1->complex,z))) *
            wirtinger_dbar ef z)]]) STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC complex_green_univ THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!z. ~(z IN path_image(g:real^1->complex)) ==>
         Cx(Re(winding_number(g,z))) *
         wirtinger_dbar (ef:complex->complex) z =
         Cx(Re(winding_number(g,z))) * wirtinger_dbar f z]]) ASSUME_TAC THENL
     [X_GEN_TAC ([[z:complex]]) THEN DISCH_TAC THEN
      SUBGOAL_THEN ([[z IN inside(path_image(g:real^1->complex)) \/
       z IN outside(path_image g)]]) MP_TAC THENL
       [MP_TAC (← HolLight.ISPEC ([[path_image(g:real^1->complex)]]) INSIDE_UNION_OUTSIDE) THEN
        REWRITE_TAC [EXTENSION, IN_UNION, IN_DIFF, IN_UNIV] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[z:complex]])) THEN ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      DISCH_THEN DISJ_CASES_TAC THENL
       [AP_TERM_TAC THEN REWRITE_TAC [wirtinger_dbar, jacobian] THEN
        ASM_SIMP_TAC [],
        SUBGOAL_THEN ([[winding_number(g:real^1->complex,z) = Cx(&0)]]) SUBST1_TAC THENL
         [MATCH_MP_TAC WINDING_NUMBER_ZERO_IN_OUTSIDE THEN
          ASM_MESON_TAC [ABSOLUTELY_CONTINUOUS_IMP_PATH],
          REWRITE_TAC [RE_CX, COMPLEX_MUL_LZERO]]],
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC (← HolLight.CONV_RULE (HolLight.DEPTH_CONV HolLight.BETA_CONV) (← HolLight.ISPECL [([[\z:complex. Cx(Re(winding_number(g:real^1->complex,z))) *
            wirtinger_dbar (ef:complex->complex) z]]),
         ([[\z:complex. Cx(Re(winding_number(g:real^1->complex,z))) *
            wirtinger_dbar (f:complex->complex) z]]),
         ([[path_image(g:real^1->complex)]]),
         ([[(:complex)]])] INTEGRABLE_SPIKE)) THEN
      DISCH_THEN (fun th => HolLight.tactic_of do
        pure (MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_IMP] th))) THEN
      REWRITE_TAC [IN_DIFF, IN_UNIV] THEN
      ASM_MESON_TAC [NEGLIGIBLE_ABSOLUTELY_CONTINUOUS_PATH_IMAGE],
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PATH_INTEGRABLE_EQ THEN
      EXISTS_TAC ([[ef:complex->complex]]) THEN ASM_REWRITE_TAC [] THEN
      X_GEN_TAC ([[z:complex]]) THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [IN_UNION],
      ALL_TAC] THEN
    UNDISCH_TAC ([[Cx(inv(&2)) / ii * path_integral g (ef:complex->complex) =
     integral (:complex)
       (\z. Cx(Re(winding_number(g:real^1->complex,z))) *
            wirtinger_dbar ef z)]]) THEN
    SUBGOAL_THEN ([[path_integral g (ef:complex->complex) = path_integral g f]]) SUBST1_TAC THENL
     [MATCH_MP_TAC PATH_INTEGRAL_EQ THEN
      X_GEN_TAC ([[z:complex]]) THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [IN_UNION],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[integral (:complex)
              (\z. Cx(Re(winding_number(g:real^1->complex,z))) *
                   wirtinger_dbar (ef:complex->complex) z) =
     integral (:complex)
              (\z. Cx(Re(winding_number(g,z))) *
                   wirtinger_dbar f z)]]) SUBST1_TAC THENL
     [MATCH_MP_TAC INTEGRAL_SPIKE THEN
      EXISTS_TAC ([[path_image(g:real^1->complex)]]) THEN
      REWRITE_TAC [IN_DIFF, IN_UNIV] THEN
      ASM_MESON_TAC [NEGLIGIBLE_ABSOLUTELY_CONTINUOUS_PATH_IMAGE],
      ALL_TAC] THEN
    DISCH_THEN ACCEPT_TAC)
  : ExceptT String IO thm).run
#eval COMPLEX_GREEN_ALT

/- Relational form: replaces Cx(Re(winding_number)) with winding_number      -/
/- (they agree a.e. since winding_number is integer off path_image g).       -/

#eval phrase 107
def COMPLEX_GREEN : thm := keep "COMPLEX_GREEN" fun _ => (do
  let h1 ← cf (← ExceptT.mk [[inv(Cx(&2)) / ii * x = y <=> x = Cx(&2) * ii * y]])
  prove ([[!f:complex->complex g u.
        g absolutely_continuous_on interval[vec 0,vec 1] /\
        pathfinish g = pathstart g /\
        open u /\
        inside(path_image g) UNION path_image g SUBSET u /\
        f differentiable_on u /\
        (!h:complex. (\z. frechet_derivative f (at z) h) continuous_on u)
        ==> (\z. winding_number(g,z) * wirtinger_dbar f z)
            integrable_on (:complex) /\
            f path_integrable_on g /\
            path_integral g f =
            Cx(&2) * ii *
            integral (:complex)
                     (\z. winding_number(g,z) * wirtinger_dbar f z)]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP COMPLEX_GREEN_ALT) THEN
    FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
    REWRITE_TAC [CX_INV, h1] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN ([[path(g:real^1->complex)]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [ABSOLUTELY_CONTINUOUS_IMP_PATH], ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC (← HolLight.CONV_RULE (HolLight.DEPTH_CONV HolLight.BETA_CONV) (← HolLight.ISPECL [([[\z:complex. Cx(Re(winding_number(g:real^1->complex,z))) *
            wirtinger_dbar (f:complex->complex) z]]),
         ([[\z:complex. winding_number(g:real^1->complex,z) *
            wirtinger_dbar (f:complex->complex) z]]),
         ([[path_image(g:real^1->complex)]]),
         ([[(:complex)]])] INTEGRABLE_SPIKE)) THEN
      DISCH_THEN (fun th => HolLight.tactic_of do
        pure (MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_IMP] th))) THEN
      REWRITE_TAC [IN_DIFF, IN_UNIV] THEN CONJ_TAC THENL
       [CONJ_TAC THENL
         [ASM_MESON_TAC [NEGLIGIBLE_ABSOLUTELY_CONTINUOUS_PATH_IMAGE],
          REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          CONV_TAC HolLight.SYM_CONV THEN REWRITE_TAC [(← HolLight.GSYM REAL), real] THEN
          ASM_MESON_TAC [INTEGER_WINDING_NUMBER, complex_integer]],
        ASM_REWRITE_TAC []],
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    REPLICATE_TAC 2 AP_TERM_TAC THEN
    MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC ([[path_image g:complex->bool]]) THEN
    ASM_SIMP_TAC [NEGLIGIBLE_ABSOLUTELY_CONTINUOUS_PATH_IMAGE, IN_DIFF, IN_UNIV] THEN
    REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC HolLight.SYM_CONV THEN REWRITE_TAC [(← HolLight.GSYM REAL), real] THEN
    ASM_MESON_TAC [INTEGER_WINDING_NUMBER, complex_integer])
  : ExceptT String IO thm).run
#eval COMPLEX_GREEN

def COMPLEX_GREEN_INSIDE : thm := keep "COMPLEX_GREEN_INSIDE" fun _ => (do
  prove ([[!f:complex->complex g u.
        g absolutely_continuous_on interval[vec 0,vec 1] /\
        pathfinish g = pathstart g /\
        open u /\
        inside(path_image g) UNION path_image g SUBSET u /\
        f differentiable_on u /\
        (!h:complex. (\z. frechet_derivative f (at z) h) continuous_on u)
        ==> (\z. winding_number(g,z) * wirtinger_dbar f z)
            integrable_on inside(path_image g) /\
            f path_integrable_on g /\
            path_integral g f =
            Cx(&2) * ii *
            integral (inside(path_image g))
                     (\z. winding_number(g,z) * wirtinger_dbar f z)]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_ASSUM (MP_TAC o HolLight.CONJUNCT1 o HolLight.MATCH_MP COMPLEX_GREEN) THEN
      DISCH_TAC THEN
      SUBGOAL_THEN ([[(\z:complex. if z IN inside(path_image(g:real^1->complex))
                    then winding_number(g,z) *
                         wirtinger_dbar (f:complex->complex) z
                    else vec 0)
       integrable_on (:complex)]]) MP_TAC THENL
       [MP_TAC (← HolLight.CONV_RULE (HolLight.DEPTH_CONV HolLight.BETA_CONV) (← HolLight.ISPECL [([[\z:complex. winding_number(g:real^1->complex,z) *
              wirtinger_dbar (f:complex->complex) z]]),
           ([[\z:complex. if z IN inside(path_image(g:real^1->complex))
                      then winding_number(g,z) *
                           wirtinger_dbar (f:complex->complex) z
                      else vec 0]]),
           ([[path_image(g:real^1->complex)]]),
           ([[(:complex)]])] INTEGRABLE_SPIKE)) THEN
        DISCH_THEN (fun th => HolLight.tactic_of do
        pure (MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_IMP] th))) THEN
        CONJ_TAC THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC NEGLIGIBLE_ABSOLUTELY_CONTINUOUS_PATH_IMAGE THEN
            ASM_REWRITE_TAC [],
            X_GEN_TAC ([[z:complex]]) THEN REWRITE_TAC [IN_DIFF, IN_UNIV] THEN
            DISCH_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
            REWRITE_TAC [COMPLEX_VEC_0] THEN
            SUBGOAL_THEN ([[winding_number(g:real^1->complex,z) = Cx(&0)]]) SUBST1_TAC THENL
             [MATCH_MP_TAC WINDING_NUMBER_ZERO_IN_OUTSIDE THEN
              ASM_SIMP_TAC [ABSOLUTELY_CONTINUOUS_IMP_PATH] THEN
              ASM_REWRITE_TAC [OUTSIDE_INSIDE, IN_DIFF, IN_UNIV, IN_UNION],
              REWRITE_TAC [COMPLEX_MUL_LZERO]]],
          ASM_REWRITE_TAC []],
        REWRITE_TAC [INTEGRABLE_RESTRICT_UNIV]],
      ALL_TAC] THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o HolLight.MATCH_MP COMPLEX_GREEN) THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    REPLICATE_TAC 2 AP_TERM_TAC THEN
    GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.GSYM INTEGRAL_RESTRICT_UNIV)] THEN
    MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC ([[path_image g:complex->bool]]) THEN
    ASM_SIMP_TAC [NEGLIGIBLE_ABSOLUTELY_CONTINUOUS_PATH_IMAGE, IN_DIFF, IN_UNIV] THEN
    X_GEN_TAC ([[z:complex]]) THEN STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [COMPLEX_VEC_0] THEN CONV_TAC HolLight.SYM_CONV THEN
    REWRITE_TAC [COMPLEX_ENTIRE] THEN DISJ1_TAC THEN
    MATCH_MP_TAC WINDING_NUMBER_ZERO_IN_OUTSIDE THEN
    ASM_SIMP_TAC [ABSOLUTELY_CONTINUOUS_IMP_PATH] THEN
    ASM_REWRITE_TAC [OUTSIDE_INSIDE, IN_DIFF, IN_UNIV, IN_UNION])
  : ExceptT String IO thm).run
#eval COMPLEX_GREEN_INSIDE

/- Path integral of cnj for absolutely continuous closed curves.              -/
/- General form: path_integral = Cx(&2)*ii * integral_inside(wn).            -/

#eval phrase 108
def HAS_PATH_INTEGRAL_CNJ : thm := keep "HAS_PATH_INTEGRAL_CNJ" fun _ => (do
  prove ([[!g:real^1->complex.
        g absolutely_continuous_on interval[vec 0,vec 1] /\
        pathfinish g = pathstart g
        ==> cnj path_integrable_on g /\
            path_integral g cnj =
            Cx(&2) * ii *
            integral (inside(path_image g))
                     (\z. winding_number(g,z))]])
   (GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[cnj]]), ([[g:real^1->complex]]), ([[(:complex)]])] COMPLEX_GREEN_INSIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [OPEN_UNIV, SUBSET_UNIV] THEN CONJ_TAC THENL
       [MATCH_MP_TAC DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON THEN
        GEN_TAC THEN DISCH_TAC THEN
        MATCH_MP_TAC HAS_DERIVATIVE_IMP_DIFFERENTIABLE THEN
        EXISTS_TAC ([[cnj]]) THEN REWRITE_TAC [HAS_DERIVATIVE_CNJ],
        GEN_TAC THEN
        REWRITE_TAC [(← HolLight.MATCH_MP HAS_FRECHET_DERIVATIVE_UNIQUE_AT (← HolLight.SPEC_ALL HAS_DERIVATIVE_CNJ))] THEN
        REWRITE_TAC [CONTINUOUS_ON_CONST]],
      ALL_TAC] THEN
    STRIP_TAC THEN CONJ_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN REPLICATE_TAC 2 AP_TERM_TAC THEN
    MATCH_MP_TAC INTEGRAL_EQ THEN
    REWRITE_TAC [WIRTINGER_DBAR_CNJ, COMPLEX_MUL_RID])
  : ExceptT String IO thm).run
#eval HAS_PATH_INTEGRAL_CNJ

/- Gauss-Green for cnj: integral of wirtinger_dbar cnj = 1 gives area.       -/

#eval phrase 109
def COMPLEX_GREEN_CNJ : thm := keep "COMPLEX_GREEN_CNJ" fun _ => (do
  prove ([[!g. g absolutely_continuous_on interval[vec 0,vec 1] /\
       pathfinish g = pathstart g /\
       (!z. z IN inside(path_image g) ==> winding_number(g,z) = Cx(&1))
       ==> (cnj has_path_integral
            Cx(&2) * ii * Cx(measure(inside(path_image g)))) g]])
   (GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC [HAS_PATH_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
    MP_TAC (← HolLight.SPEC ([[g:real^1->complex]]) HAS_PATH_INTEGRAL_CNJ) THEN
    ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN CONJ_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN REPLICATE_TAC 2 AP_TERM_TAC THEN
    SUBGOAL_THEN ([[measurable(inside(path_image(g:real^1->complex)))]]) ASSUME_TAC THENL
     [MATCH_MP_TAC MEASURABLE_INSIDE THEN
      MATCH_MP_TAC COMPACT_PATH_IMAGE THEN
      ASM_MESON_TAC [ABSOLUTELY_CONTINUOUS_IMP_PATH], ALL_TAC] THEN
    MP_TAC (← HolLight.ISPECL [([[\z:complex. winding_number(g:real^1->complex,z)]]),
                    ([[\z:complex. Cx(&1)]]),
                    ([[inside(path_image(g:real^1->complex))]])] INTEGRAL_EQ) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC [], DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC [INTEGRAL_CONST_GEN] THEN
    REWRITE_TAC [COMPLEX_CMUL, COMPLEX_MUL_RID])
  : ExceptT String IO thm).run
#eval COMPLEX_GREEN_CNJ

/- Cauchy's theorem for identity (no wn hypothesis, closed path only).       -/

#eval phrase 110
def HAS_PATH_INTEGRAL_I_CLOSED : thm := keep "HAS_PATH_INTEGRAL_I_CLOSED" fun _ => (do
  prove ([[!g:real^1->complex.
        g absolutely_continuous_on interval[vec 0,vec 1] /\
        pathfinish g = pathstart g
        ==> (I has_path_integral Cx(&0)) g]])
   (GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[I:complex->complex]]), ([[g:real^1->complex]]), ([[(:complex)]])] COMPLEX_GREEN_INSIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [OPEN_UNIV, SUBSET_UNIV] THEN CONJ_TAC THENL
       [REWRITE_TAC [I_DEF, DIFFERENTIABLE_ON_ID],
        GEN_TAC THEN REWRITE_TAC [I_DEF] THEN
        SUBGOAL_THEN ([[!z:complex. frechet_derivative (\x:complex. x) (at z) = (\h. h)]]) (fun th => REWRITE_TAC [th]) THENL
         [GEN_TAC THEN CONV_TAC HolLight.SYM_CONV THEN
          MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
          REWRITE_TAC [HAS_DERIVATIVE_ID],
          CONV_TAC (HolLight.DEPTH_CONV HolLight.BETA_CONV) THEN
          REWRITE_TAC [CONTINUOUS_ON_CONST]]],
      DISCH_THEN (MP_TAC o HolLight.CONJUNCT2) THEN
      REWRITE_TAC [(← HolLight.GSYM HAS_PATH_INTEGRAL_INTEGRABLE_INTEGRAL)]] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [WIRTINGER_DBAR_I] THEN
    REWRITE_TAC [COMPLEX_MUL_RZERO] THEN
    SUBGOAL_THEN ([[(\z:complex. Cx(&0)) = (\z. vec 0)]]) SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM, COMPLEX_VEC_0], ALL_TAC] THEN
    REWRITE_TAC [INTEGRAL_0, COMPLEX_MUL_RZERO, COMPLEX_VEC_0])
  : ExceptT String IO thm).run
#eval HAS_PATH_INTEGRAL_I_CLOSED

/- Cauchy's theorem for the identity: wirtinger_dbar I = 0.                  -/
/- Trivial corollary of HAS_PATH_INTEGRAL_I_CLOSED (extra wn hyp unused).   -/

#eval phrase 111
def COMPLEX_GREEN_I : thm := keep "COMPLEX_GREEN_I" fun _ => (do
  prove ([[!g. g absolutely_continuous_on interval[vec 0,vec 1] /\
       pathfinish g = pathstart g /\
       (!z. z IN inside(path_image g) ==> winding_number(g,z) = Cx(&1))
       ==> (I has_path_integral Cx(&0)) g]])
   (MESON_TAC [HAS_PATH_INTEGRAL_I_CLOSED])
  : ExceptT String IO thm).run
#eval COMPLEX_GREEN_I

/- Complex area formula: measure of inside from path integral of cnj.        -/

#eval phrase 112
def COMPLEX_GREEN_AREA : thm := keep "COMPLEX_GREEN_AREA" fun _ => (do
  prove ([[!g. g absolutely_continuous_on interval[vec 0,vec 1] /\
       pathfinish g = pathstart g /\
       (!z. z IN inside(path_image g) ==> winding_number(g,z) = Cx(&1))
       ==> cnj path_integrable_on g /\
           Cx(measure(inside(path_image g))) =
           --ii / Cx(&2) * path_integral g cnj]])
   (GEN_TAC THEN DISCH_THEN (MP_TAC o HolLight.MATCH_MP COMPLEX_GREEN_CNJ) THEN
    REWRITE_TAC [HAS_PATH_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    UNDISCH_TAC ([[path_integral g cnj =
               Cx(&2) * ii * Cx(measure(inside(path_image g)))]]) THEN
    CONV_TAC cf)
  : ExceptT String IO thm).run
#eval COMPLEX_GREEN_AREA

/- Orientation-free complex area formula for simple closed curves.           -/
/- Uses COMPLEX_GREEN_INSIDE and case split on wn=+1/ -1.                     -/

#eval phrase 113
def COMPLEX_GREEN_AREA_ABS : thm := keep "COMPLEX_GREEN_AREA_ABS" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[&0 <= x ==> x = (&2 * abs x) / &2]])
  prove ([[!g:real^1->complex.
        g absolutely_continuous_on interval[vec 0,vec 1] /\
        simple_path g /\ pathfinish g = pathstart g
        ==> cnj path_integrable_on g /\
            measure(inside(path_image g)) =
            norm(path_integral g cnj) / &2]])
   (GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← HolLight.SPEC ([[g:real^1->complex]]) HAS_PATH_INTEGRAL_CNJ) THEN
    ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN CONJ_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN ([[measurable(inside(path_image g):complex->bool)]]) ASSUME_TAC THENL
     [MATCH_MP_TAC MEASURABLE_INSIDE THEN
      MATCH_MP_TAC COMPACT_PATH_IMAGE THEN
      ASM_MESON_TAC [ABSOLUTELY_CONTINUOUS_IMP_PATH], ALL_TAC] THEN
    MP_TAC (← HolLight.ISPEC ([[g:real^1->complex]]) SIMPLE_CLOSED_PATH_WINDING_NUMBER_INSIDE) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC [ABSOLUTELY_CONTINUOUS_IMP_PATH], ALL_TAC] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [SUBGOAL_THEN ([[integral (inside(path_image g))
         (\z. winding_number(g:real^1->complex,z)) =
       Cx(measure(inside(path_image g)))]]) SUBST1_TAC THENL
       [MP_TAC (← HolLight.ISPECL [([[\z:complex. winding_number(g:real^1->complex,z)]]),
                        ([[\z:complex. Cx(&1)]]),
                        ([[inside(path_image(g:real^1->complex))]])] INTEGRAL_EQ) THEN
        ANTS_TAC THENL [ASM_SIMP_TAC [], DISCH_THEN SUBST1_TAC] THEN
        ASM_SIMP_TAC [INTEGRAL_CONST_GEN] THEN
        REWRITE_TAC [COMPLEX_CMUL, COMPLEX_MUL_RID],
        ALL_TAC],
      SUBGOAL_THEN ([[integral (inside(path_image g))
         (\z. winding_number(g:real^1->complex,z)) =
       --Cx(measure(inside(path_image g)))]]) SUBST1_TAC THENL
       [MP_TAC (← HolLight.ISPECL [([[\z:complex. winding_number(g:real^1->complex,z)]]),
                        ([[\z:complex. --Cx(&1)]]),
                        ([[inside(path_image(g:real^1->complex))]])] INTEGRAL_EQ) THEN
        ANTS_TAC THENL [ASM_SIMP_TAC [], DISCH_THEN SUBST1_TAC] THEN
        ASM_SIMP_TAC [INTEGRAL_CONST_GEN] THEN
        REWRITE_TAC [COMPLEX_CMUL] THEN
        ONCE_REWRITE_TAC [COMPLEX_MUL_SYM] THEN
        REWRITE_TAC [COMPLEX_MUL_LNEG, COMPLEX_MUL_LID],
        ALL_TAC]] THEN
    REWRITE_TAC [COMPLEX_MUL_RNEG, NORM_NEG,
                COMPLEX_NORM_MUL, COMPLEX_NORM_CX, COMPLEX_NORM_II,
                REAL_ABS_NUM, REAL_MUL_LID] THEN
    REWRITE_TAC [COMPLEX_NORM_CX] THEN
    MATCH_MP_TAC h1 THEN
    MATCH_MP_TAC MEASURE_POS_LE THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval COMPLEX_GREEN_AREA_ABS

/- ------------------------------------------------------------------------- -/
/- Real Green's theorem (curl form) and real area formulas.                  -/
/- ------------------------------------------------------------------------- -/
/- Green's theorem in classical curl form:                                   -/
/-   integral(f2 dx + f1 dy) = integral(df1/dx - df2/dy) dA                  -/
/- Expands wirtinger_dbar integral into explicit partial derivatives.        -/
/- Statement uses real^2, basis 1, basis 2 to avoid complex paraphernalia.   -/
/- Helper lemmas (green_theorem_real, wirtinger_dbar_2i_im, linearity)       -/
/- are localized inside the proof.                                           -/

#eval phrase 114
def GREEN_THEOREM_CURL : thm := keep "GREEN_THEOREM_CURL" fun _ => (do
  let green_theorem_real ← prove ([[!f:complex->complex g u.
          g absolutely_continuous_on interval[vec 0,vec 1] /\
          pathfinish g = pathstart g /\
          (!z. z IN inside(path_image g) ==> winding_number(g,z) = Cx(&1)) /\
          open u /\
          inside(path_image g) UNION path_image g SUBSET u /\
          f differentiable_on u /\
          (!h:complex. (\z. frechet_derivative f (at z) h) continuous_on u)
          ==> ((\t. lift(f(g t)$2 * vector_derivative g (at t) $1 +
                         f(g t)$1 * vector_derivative g (at t) $2))
               has_integral
               lift(Im(Cx(&2) * ii *
                       integral (inside(path_image g))
                                (wirtinger_dbar f))))
              (interval[vec 0,vec 1])]])
     (REPEAT GEN_TAC THEN STRIP_TAC THEN
      MP_TAC (← HolLight.ISPECL [([[f:complex->complex]]), ([[g:real^1->complex]]), ([[u:complex->bool]])] COMPLEX_GREEN_INSIDE) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (MP_TAC o HolLight.CONJUNCT2) THEN
      REWRITE_TAC [(← HolLight.GSYM HAS_PATH_INTEGRAL_INTEGRABLE_INTEGRAL)] THEN
      SUBGOAL_THEN ([[integral (inside(path_image g))
         (\z. winding_number(g:real^1->complex,z) * wirtinger_dbar f z) =
       integral (inside(path_image g)) (wirtinger_dbar f)]]) (fun th => REWRITE_TAC [th]) THENL
       [MATCH_MP_TAC INTEGRAL_EQ THEN
        X_GEN_TAC ([[z:complex]]) THEN DISCH_TAC THEN
        ASM_SIMP_TAC [COMPLEX_MUL_LID],
        ALL_TAC] THEN
      REWRITE_TAC [(← HolLight.REWRITE_RULE [complex_mul] HAS_PATH_INTEGRAL)] THEN
      GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [HAS_INTEGRAL_COMPONENTWISE] THEN
      REWRITE_TAC [DIMINDEX_2, FORALL_2, (← HolLight.GSYM IM_DEF), (← HolLight.GSYM RE_DEF)] THEN
      DISCH_THEN (MP_TAC o HolLight.CONJUNCT2) THEN
      REWRITE_TAC [IM, (← HolLight.GSYM IM_DEF), (← HolLight.GSYM RE_DEF)] THEN
      SIMP_TAC [REAL_ADD_AC] THEN
      DISCH_THEN ACCEPT_TAC)
  let wirtinger_dbar_2i_im ← prove ([[!f:complex->complex z.
          Im(Cx(&2) * ii * wirtinger_dbar f z) =
          frechet_derivative f (at z) (Cx(&1)) $1 -
          frechet_derivative f (at z) ii $2]])
     (REPEAT GEN_TAC THEN
      REWRITE_TAC [WIRTINGER_DBAR_FRECHET, complex_div, (← HolLight.GSYM CX_INV)] THEN
      REWRITE_TAC [IM_MUL_CX] THEN
      ONCE_REWRITE_TAC [COMPLEX_MUL_ASSOC] THEN
      REWRITE_TAC [IM_MUL_CX, IM_MUL_II, RE_ADD, RE_MUL_II] THEN
      REWRITE_TAC [RE_DEF, IM_DEF] THEN
      CONV_TAC rf)
  let linear_lift_im_2i ← prove ([[linear(\z:complex. lift(Im(Cx(&2) * ii * z)))]])
     (SUBGOAL_THEN ([[(\z:complex. lift(Im(Cx(&2) * ii * z))) =
       (\x:complex. lift(x$2)) o (\z:complex. Cx(&2) * ii * z)]]) SUBST1_TAC THENL
       [REWRITE_TAC [FUN_EQ_THM, o_THM] THEN GEN_TAC THEN
        CONV_TAC (HolLight.DEPTH_CONV HolLight.BETA_CONV) THEN REWRITE_TAC [IM_DEF],
        ALL_TAC] THEN
      MATCH_MP_TAC LINEAR_COMPOSE THEN
      REWRITE_TAC [LINEAR_LIFT_COMPONENT] THEN
      MATCH_MP_TAC LINEAR_COMPLEX_LMUL THEN
      MATCH_MP_TAC LINEAR_COMPLEX_LMUL THEN
      REWRITE_TAC [LINEAR_ID])
  prove ([[!f:real^2->real^2 g u.
        g absolutely_continuous_on interval[vec 0,vec 1] /\
        pathfinish g = pathstart g /\
        (!z. z IN inside(path_image g) ==> winding_number(g,z) = Cx(&1)) /\
        open u /\
        inside(path_image g) UNION path_image g SUBSET u /\
        f differentiable_on u /\
        (!h:real^2. (\z. frechet_derivative f (at z) h) continuous_on u)
        ==> (\z. lift(frechet_derivative f (at z) (basis 1) $1 -
                      frechet_derivative f (at z) (basis 2) $2))
            integrable_on inside(path_image g) /\
            (\t. lift(f(g t)$2 * vector_derivative g (at t) $1 +
                      f(g t)$1 * vector_derivative g (at t) $2))
            integrable_on interval[vec 0,vec 1] /\
            integral (interval[vec 0,vec 1])
              (\t. lift(f(g t)$2 * vector_derivative g (at t) $1 +
                        f(g t)$1 * vector_derivative g (at t) $2)) =
            integral (inside(path_image g))
              (\z. lift(frechet_derivative f (at z) (basis 1) $1 -
                        frechet_derivative f (at z) (basis 2) $2))]])
   (REWRITE_TAC [COMPLEX_BASIS] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[wirtinger_dbar (f:complex->complex) integrable_on
     inside(path_image g)]]) ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_EQ THEN
      EXISTS_TAC ([[\z:complex. winding_number(g:real^1->complex,z) *
                   wirtinger_dbar (f:complex->complex) z]]) THEN
      CONJ_TAC THENL
       [X_GEN_TAC ([[z:complex]]) THEN DISCH_TAC THEN
        CONV_TAC (HolLight.DEPTH_CONV HolLight.BETA_CONV) THEN
        ASM_SIMP_TAC [COMPLEX_MUL_LID],
        MP_TAC (← HolLight.ISPECL [([[f:complex->complex]]), ([[g:real^1->complex]]),
                        ([[u:complex->bool]])] COMPLEX_GREEN_INSIDE) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC [], SIMP_TAC []]],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[(\z. lift(frechet_derivative (f:complex->complex) (at z) (Cx(&1)) $1 -
              frechet_derivative f (at z) ii $2))
     integrable_on inside(path_image g)]]) ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_EQ THEN
      EXISTS_TAC ([[(\z:complex. lift(Im(Cx(&2) * ii * z))) o
       wirtinger_dbar (f:complex->complex)]]) THEN
      CONJ_TAC THENL
       [X_GEN_TAC ([[z:complex]]) THEN DISCH_TAC THEN
        REWRITE_TAC [o_THM] THEN AP_TERM_TAC THEN
        REWRITE_TAC [wirtinger_dbar_2i_im],
        MATCH_MP_TAC INTEGRABLE_LINEAR THEN
        ASM_REWRITE_TAC [linear_lift_im_2i]],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    MP_TAC (← HolLight.ISPECL [([[f:complex->complex]]), ([[g:real^1->complex]]), ([[u:complex->bool]])] green_theorem_real) THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN ([[lift(Im(Cx(&2) * ii *
             integral (inside(path_image g))
                      (wirtinger_dbar (f:complex->complex)))) =
     integral (inside(path_image g))
       (\z. lift(frechet_derivative f (at z) (Cx(&1)) $1 -
                 frechet_derivative f (at z) ii $2))]]) (fun th => REWRITE_TAC [th]) THENL
     [MP_TAC (← HolLight.ISPECL [([[wirtinger_dbar (f:complex->complex)]]),
                      ([[inside(path_image(g:real^1->complex))]]),
                      ([[\z:complex. lift(Im(Cx(&2) * ii * z))]])] INTEGRAL_LINEAR) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [linear_lift_im_2i],
        REWRITE_TAC [o_DEF] THEN
        DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN
        MATCH_MP_TAC INTEGRAL_EQ THEN
        X_GEN_TAC ([[z:complex]]) THEN DISCH_TAC THEN
        BETA_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [wirtinger_dbar_2i_im]],
      ALL_TAC] THEN
    REWRITE_TAC [HAS_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval GREEN_THEOREM_CURL

/- De-complexified area formula: integral of x*dy = area (x*y' form).        -/

#eval phrase 115
def GREEN_AREA : thm := keep "GREEN_AREA" fun _ => (do
  prove ([[!g. g absolutely_continuous_on interval[vec 0,vec 1] /\
       pathfinish g = pathstart g /\
       (!z. z IN inside(path_image g) ==> winding_number(g,z) = Cx(&1))
       ==> (\t. lift(g t $1 * vector_derivative g (at t) $2))
           integrable_on interval[vec 0,vec 1] /\
           integral (interval[vec 0,vec 1])
             (\t. lift(g t $1 * vector_derivative g (at t) $2)) =
           lift(measure(inside(path_image g)))]])
   (REWRITE_TAC [(← HolLight.GSYM HAS_INTEGRAL_INTEGRABLE_INTEGRAL)] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPEC ([[g:real^1->complex]]) COMPLEX_GREEN_I) THEN
    MP_TAC (← HolLight.SPEC ([[g:real^1->complex]]) COMPLEX_GREEN_CNJ) THEN
    ASM_REWRITE_TAC [IMP_IMP] THEN
    REWRITE_TAC [(← HolLight.REWRITE_RULE [complex_mul] HAS_PATH_INTEGRAL)] THEN
    REWRITE_TAC [RE_CNJ, IM_CNJ] THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [HAS_INTEGRAL_COMPONENTWISE] THEN
    REWRITE_TAC [DIMINDEX_2, FORALL_2, (← HolLight.GSYM IM_DEF), (← HolLight.GSYM RE_DEF), I_DEF] THEN
    REWRITE_TAC [RE, IM, RE_II, IM_II, RE_CX, IM_CX, IM_MUL_CX, RE_MUL_CX] THEN
    REWRITE_TAC [REAL_MUL_LZERO, REAL_MUL_RZERO, LIFT_NUM] THEN
    REWRITE_TAC [REAL_MUL_LID, COMPLEX_VEC_0] THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
        let b ← HolLight.CONJUNCT2 (← HolLight.CONJUNCT1 th)
        pure (HolLight.tactic_of do
        let d ← HolLight.CONJUNCT2 (← HolLight.CONJUNCT2 th)
        pure (ASSUME_TAC b THEN ASSUME_TAC d))) THEN
    SUBGOAL_THEN ([[!t:real^1. lift(Re (g t) * Im (vector_derivative g (at t))) =
     inv(&2) %
       (lift (Re (g t) * Im (vector_derivative g (at t)) +
                --Im (g t) * Re (vector_derivative g (at t))) +
        lift (Re (g t) * Im (vector_derivative g (at t)) +
                Im (g t) * Re (vector_derivative g (at t))))]]) (fun th => REWRITE_TAC [th]) THENL
     [GEN_TAC THEN REWRITE_TAC [(← HolLight.GSYM LIFT_ADD), (← HolLight.GSYM LIFT_CMUL)] THEN
      AP_TERM_TAC THEN REAL_ARITH_TAC2,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[lift(measure(inside(path_image(g:real^1->complex)))) =
     inv(&2) % (lift (&2 * measure(inside(path_image g))) +
                (vec 0:real^1))]]) SUBST1_TAC THENL
     [REWRITE_TAC [VECTOR_ADD_RID, (← HolLight.GSYM LIFT_CMUL), LIFT_EQ] THEN
      REAL_ARITH_TAC2,
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_INTEGRAL_CMUL THEN
    MATCH_MP_TAC HAS_INTEGRAL_ADD THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC)
  : ExceptT String IO thm).run
#eval GREEN_AREA

/- De-complexified area formula: integral of y*dx = -area (x'*y form).       -/

#eval phrase 116
def GREEN_AREA_ALT : thm := keep "GREEN_AREA_ALT" fun _ => (do
  prove ([[!g. g absolutely_continuous_on interval[vec 0,vec 1] /\
       pathfinish g = pathstart g /\
       (!z. z IN inside(path_image g) ==> winding_number(g,z) = Cx(&1))
       ==> (\t. lift(vector_derivative g (at t) $1 * g t $2))
           integrable_on interval[vec 0,vec 1] /\
           integral (interval[vec 0,vec 1])
             (\t. lift(vector_derivative g (at t) $1 * g t $2)) =
           --lift(measure(inside(path_image g)))]])
   (REWRITE_TAC [(← HolLight.GSYM HAS_INTEGRAL_INTEGRABLE_INTEGRAL)] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPEC ([[g:real^1->complex]]) COMPLEX_GREEN_I) THEN
    MP_TAC (← HolLight.SPEC ([[g:real^1->complex]]) COMPLEX_GREEN_CNJ) THEN
    ASM_REWRITE_TAC [IMP_IMP] THEN
    REWRITE_TAC [(← HolLight.REWRITE_RULE [complex_mul] HAS_PATH_INTEGRAL)] THEN
    REWRITE_TAC [RE_CNJ, IM_CNJ] THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [HAS_INTEGRAL_COMPONENTWISE] THEN
    REWRITE_TAC [DIMINDEX_2, FORALL_2, (← HolLight.GSYM IM_DEF), (← HolLight.GSYM RE_DEF), I_DEF] THEN
    REWRITE_TAC [RE, IM, RE_II, IM_II, RE_CX, IM_CX, IM_MUL_CX, RE_MUL_CX] THEN
    REWRITE_TAC [REAL_MUL_LZERO, REAL_MUL_RZERO, LIFT_NUM] THEN
    REWRITE_TAC [REAL_MUL_LID, COMPLEX_VEC_0] THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
        let b ← HolLight.CONJUNCT2 (← HolLight.CONJUNCT1 th)
        pure (HolLight.tactic_of do
        let d ← HolLight.CONJUNCT2 (← HolLight.CONJUNCT2 th)
        pure (ASSUME_TAC b THEN ASSUME_TAC d))) THEN
    SUBGOAL_THEN ([[!t:real^1. lift(Re (vector_derivative g (at t)) * Im (g t)) =
     --inv(&2) %
       (lift (Re (g t) * Im (vector_derivative g (at t)) +
                --Im (g t) * Re (vector_derivative g (at t))) -
        lift (Re (g t) * Im (vector_derivative g (at t)) +
                Im (g t) * Re (vector_derivative g (at t))))]]) (fun th => REWRITE_TAC [th]) THENL
     [GEN_TAC THEN REWRITE_TAC [(← HolLight.GSYM LIFT_SUB), (← HolLight.GSYM LIFT_CMUL)] THEN
      AP_TERM_TAC THEN REAL_ARITH_TAC2,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[--lift(measure(inside(path_image(g:real^1->complex)))) =
     --inv(&2) % (lift (&2 * measure(inside(path_image g))) -
                  (vec 0:real^1))]]) SUBST1_TAC THENL
     [REWRITE_TAC [VECTOR_SUB_RZERO, (← HolLight.GSYM LIFT_CMUL), (← HolLight.GSYM LIFT_NEG), LIFT_EQ] THEN
      REAL_ARITH_TAC2,
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_INTEGRAL_CMUL THEN
    MATCH_MP_TAC HAS_INTEGRAL_SUB THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC)
  : ExceptT String IO thm).run
#eval GREEN_AREA_ALT

/- Orientation-free real area formula: x*dy form.                            -/
/- For wn=+1 uses GREEN_AREA; for wn=-1 derives from componentwise           -/
/- extraction of cnj and I path integrals.                                   -/

#eval phrase 117
def GREEN_AREA_ABS : thm := keep "GREEN_AREA_ABS" fun _ => (do
  let h2 ← rr (← ExceptT.mk [[&0 <= x ==> abs x = x]])
  let h1 ← rr (← ExceptT.mk [[&0 <= x ==> abs x = x]])
  prove ([[!g:real^1->complex.
        g absolutely_continuous_on interval[vec 0,vec 1] /\
        simple_path g /\ pathfinish g = pathstart g
        ==> (\t. lift(g t $1 * vector_derivative g (at t) $2))
            integrable_on interval[vec 0,vec 1] /\
            norm(integral (interval[vec 0,vec 1])
              (\t. lift(g t $1 * vector_derivative g (at t) $2))) =
            measure(inside(path_image g))]])
   (GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← HolLight.ISPEC ([[g:real^1->complex]]) SIMPLE_CLOSED_PATH_WINDING_NUMBER_INSIDE) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC [ABSOLUTELY_CONTINUOUS_IMP_PATH], ALL_TAC] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [MP_TAC (← HolLight.SPEC ([[g:real^1->complex]]) GREEN_AREA) THEN
      ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [(← HolLight.GSYM HAS_INTEGRAL_INTEGRABLE_INTEGRAL)] THEN
      DISCH_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC [HAS_INTEGRAL_INTEGRABLE], ALL_TAC] THEN
      FIRST_ASSUM (SUBST1_TAC o HolLight.MATCH_MP INTEGRAL_UNIQUE) THEN
      REWRITE_TAC [NORM_LIFT] THEN
      MATCH_MP_TAC h1 THEN
      MATCH_MP_TAC MEASURE_POS_LE THEN
      MATCH_MP_TAC MEASURABLE_INSIDE THEN
      MATCH_MP_TAC COMPACT_PATH_IMAGE THEN
      ASM_MESON_TAC [ABSOLUTELY_CONTINUOUS_IMP_PATH],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[measurable(inside(path_image g):complex->bool)]]) ASSUME_TAC THENL
     [MATCH_MP_TAC MEASURABLE_INSIDE THEN
      MATCH_MP_TAC COMPACT_PATH_IMAGE THEN
      ASM_MESON_TAC [ABSOLUTELY_CONTINUOUS_IMP_PATH], ALL_TAC] THEN
    SUBGOAL_THEN ([[(cnj has_path_integral
      (Cx(&2) * ii * --Cx(measure(inside(path_image g))))) (g:real^1->complex)]]) ASSUME_TAC THENL
     [REWRITE_TAC [HAS_PATH_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
      MP_TAC (← HolLight.SPEC ([[g:real^1->complex]]) HAS_PATH_INTEGRAL_CNJ) THEN
      ASM_REWRITE_TAC [] THEN
      STRIP_TAC THEN CONJ_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN REPLICATE_TAC 2 AP_TERM_TAC THEN
      MP_TAC (← HolLight.ISPECL [([[\z:complex. winding_number(g:real^1->complex,z)]]),
                      ([[\z:complex. --Cx(&1)]]),
                      ([[inside(path_image(g:real^1->complex))]])] INTEGRAL_EQ) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC [], DISCH_THEN SUBST1_TAC] THEN
      ASM_SIMP_TAC [INTEGRAL_CONST_GEN] THEN
      REWRITE_TAC [COMPLEX_CMUL] THEN
      ONCE_REWRITE_TAC [COMPLEX_MUL_SYM] THEN
      REWRITE_TAC [COMPLEX_MUL_LNEG, COMPLEX_MUL_LID],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[(I has_path_integral Cx(&0)) (g:real^1->complex)]]) ASSUME_TAC THENL
     [MATCH_MP_TAC HAS_PATH_INTEGRAL_I_CLOSED THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    UNDISCH_TAC ([[(cnj has_path_integral
      Cx(&2) * ii * --Cx(measure(inside(path_image g))))
     (g:real^1->complex)]]) THEN
    UNDISCH_TAC ([[(I has_path_integral Cx(&0)) (g:real^1->complex)]]) THEN
    REWRITE_TAC [IMP_IMP] THEN
    REWRITE_TAC [(← HolLight.REWRITE_RULE [complex_mul] HAS_PATH_INTEGRAL)] THEN
    REWRITE_TAC [RE_CNJ, IM_CNJ] THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [HAS_INTEGRAL_COMPONENTWISE] THEN
    REWRITE_TAC [DIMINDEX_2, FORALL_2, (← HolLight.GSYM IM_DEF), (← HolLight.GSYM RE_DEF), I_DEF] THEN
    REWRITE_TAC [RE, IM, RE_II, IM_II, RE_CX, IM_CX, IM_MUL_CX, RE_MUL_CX,
                RE_NEG, IM_NEG, COMPLEX_MUL_RNEG] THEN
    REWRITE_TAC [REAL_MUL_LZERO, REAL_MUL_RZERO, LIFT_NUM,
                REAL_NEG_0, REAL_MUL_LNEG] THEN
    REWRITE_TAC [REAL_MUL_LID, COMPLEX_VEC_0, LIFT_NEG] THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
        let c1 ← HolLight.CONJUNCT1 th
        pure (HolLight.tactic_of do
        let c2 ← HolLight.CONJUNCT2 th
        pure (HolLight.tactic_of do
        let b ← HolLight.CONJUNCT2 c1
        pure (HolLight.tactic_of do
        let d ← HolLight.CONJUNCT2 c2
        pure (ASSUME_TAC b THEN ASSUME_TAC d))))) THEN
    SUBGOAL_THEN ([[((\t:real^1. lift(Re(g t) * Im(vector_derivative g (at t))))
      has_integral --lift(measure(inside(path_image(g:real^1->complex)))))
     (interval[vec 0,vec 1])]]) ASSUME_TAC THENL
     [SUBGOAL_THEN ([[!t:real^1. lift(Re (g t) * Im (vector_derivative g (at t))) =
       inv(&2) %
         (lift (Re (g t) * Im (vector_derivative g (at t)) +
                  --(Im (g t) * Re (vector_derivative g (at t)))) +
          lift (Re (g t) * Im (vector_derivative g (at t)) +
                  Im (g t) * Re (vector_derivative g (at t))))]]) (fun th => REWRITE_TAC [th]) THENL
       [GEN_TAC THEN REWRITE_TAC [(← HolLight.GSYM LIFT_ADD), (← HolLight.GSYM LIFT_CMUL)] THEN
        AP_TERM_TAC THEN REAL_ARITH_TAC2,
        ALL_TAC] THEN
      SUBGOAL_THEN ([[--lift(measure(inside(path_image(g:real^1->complex)))) =
       inv(&2) % (lift (&2 * --measure(inside(path_image g))) +
                  (vec 0:real^1))]]) SUBST1_TAC THENL
       [REWRITE_TAC [VECTOR_ADD_RID, (← HolLight.GSYM LIFT_CMUL), (← HolLight.GSYM LIFT_NEG), LIFT_EQ] THEN
        REAL_ARITH_TAC2,
        ALL_TAC] THEN
      MATCH_MP_TAC HAS_INTEGRAL_CMUL THEN
      MATCH_MP_TAC HAS_INTEGRAL_ADD THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC,
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC [HAS_INTEGRAL_INTEGRABLE], ALL_TAC] THEN
    FIRST_ASSUM (SUBST1_TAC o HolLight.MATCH_MP INTEGRAL_UNIQUE) THEN
    REWRITE_TAC [NORM_NEG, NORM_LIFT] THEN
    MATCH_MP_TAC h2 THEN
    MATCH_MP_TAC MEASURE_POS_LE THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval GREEN_AREA_ABS

/- Orientation-free real area formula: y*dx form.                            -/

#eval phrase 118
def GREEN_AREA_ABS_ALT : thm := keep "GREEN_AREA_ABS_ALT" fun _ => (do
  let h2 ← rr (← ExceptT.mk [[&0 <= x ==> abs x = x]])
  let h1 ← rr (← ExceptT.mk [[&0 <= x ==> abs x = x]])
  prove ([[!g:real^1->complex.
        g absolutely_continuous_on interval[vec 0,vec 1] /\
        simple_path g /\ pathfinish g = pathstart g
        ==> (\t. lift(vector_derivative g (at t) $1 * g t $2))
            integrable_on interval[vec 0,vec 1] /\
            norm(integral (interval[vec 0,vec 1])
              (\t. lift(vector_derivative g (at t) $1 * g t $2))) =
            measure(inside(path_image g))]])
   (GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← HolLight.ISPEC ([[g:real^1->complex]]) SIMPLE_CLOSED_PATH_WINDING_NUMBER_INSIDE) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC [ABSOLUTELY_CONTINUOUS_IMP_PATH], ALL_TAC] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [MP_TAC (← HolLight.SPEC ([[g:real^1->complex]]) GREEN_AREA_ALT) THEN
      ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [(← HolLight.GSYM HAS_INTEGRAL_INTEGRABLE_INTEGRAL)] THEN
      DISCH_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC [HAS_INTEGRAL_INTEGRABLE], ALL_TAC] THEN
      FIRST_ASSUM (SUBST1_TAC o HolLight.MATCH_MP INTEGRAL_UNIQUE) THEN
      REWRITE_TAC [NORM_NEG, NORM_LIFT] THEN
      MATCH_MP_TAC h1 THEN
      MATCH_MP_TAC MEASURE_POS_LE THEN
      MATCH_MP_TAC MEASURABLE_INSIDE THEN
      MATCH_MP_TAC COMPACT_PATH_IMAGE THEN
      ASM_MESON_TAC [ABSOLUTELY_CONTINUOUS_IMP_PATH],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[measurable(inside(path_image g):complex->bool)]]) ASSUME_TAC THENL
     [MATCH_MP_TAC MEASURABLE_INSIDE THEN
      MATCH_MP_TAC COMPACT_PATH_IMAGE THEN
      ASM_MESON_TAC [ABSOLUTELY_CONTINUOUS_IMP_PATH], ALL_TAC] THEN
    SUBGOAL_THEN ([[(cnj has_path_integral
      (Cx(&2) * ii * --Cx(measure(inside(path_image g))))) (g:real^1->complex)]]) ASSUME_TAC THENL
     [REWRITE_TAC [HAS_PATH_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
      MP_TAC (← HolLight.SPEC ([[g:real^1->complex]]) HAS_PATH_INTEGRAL_CNJ) THEN
      ASM_REWRITE_TAC [] THEN
      STRIP_TAC THEN CONJ_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN REPLICATE_TAC 2 AP_TERM_TAC THEN
      MP_TAC (← HolLight.ISPECL [([[\z:complex. winding_number(g:real^1->complex,z)]]),
                      ([[\z:complex. --Cx(&1)]]),
                      ([[inside(path_image(g:real^1->complex))]])] INTEGRAL_EQ) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC [], DISCH_THEN SUBST1_TAC] THEN
      ASM_SIMP_TAC [INTEGRAL_CONST_GEN] THEN
      REWRITE_TAC [COMPLEX_CMUL] THEN
      ONCE_REWRITE_TAC [COMPLEX_MUL_SYM] THEN
      REWRITE_TAC [COMPLEX_MUL_LNEG, COMPLEX_MUL_LID],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[(I has_path_integral Cx(&0)) (g:real^1->complex)]]) ASSUME_TAC THENL
     [MATCH_MP_TAC HAS_PATH_INTEGRAL_I_CLOSED THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    UNDISCH_TAC ([[(cnj has_path_integral
      Cx(&2) * ii * --Cx(measure(inside(path_image g))))
     (g:real^1->complex)]]) THEN
    UNDISCH_TAC ([[(I has_path_integral Cx(&0)) (g:real^1->complex)]]) THEN
    REWRITE_TAC [IMP_IMP] THEN
    REWRITE_TAC [(← HolLight.REWRITE_RULE [complex_mul] HAS_PATH_INTEGRAL)] THEN
    REWRITE_TAC [RE_CNJ, IM_CNJ] THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [HAS_INTEGRAL_COMPONENTWISE] THEN
    REWRITE_TAC [DIMINDEX_2, FORALL_2, (← HolLight.GSYM IM_DEF), (← HolLight.GSYM RE_DEF), I_DEF] THEN
    REWRITE_TAC [RE, IM, RE_II, IM_II, RE_CX, IM_CX, IM_MUL_CX, RE_MUL_CX,
                RE_NEG, IM_NEG, COMPLEX_MUL_RNEG] THEN
    REWRITE_TAC [REAL_MUL_LZERO, REAL_MUL_RZERO, LIFT_NUM,
                REAL_NEG_0, REAL_MUL_LNEG] THEN
    REWRITE_TAC [REAL_MUL_LID, COMPLEX_VEC_0, LIFT_NEG] THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
        let c1 ← HolLight.CONJUNCT1 th
        pure (HolLight.tactic_of do
        let c2 ← HolLight.CONJUNCT2 th
        pure (HolLight.tactic_of do
        let b ← HolLight.CONJUNCT2 c1
        pure (HolLight.tactic_of do
        let d ← HolLight.CONJUNCT2 c2
        pure (ASSUME_TAC b THEN ASSUME_TAC d))))) THEN
    SUBGOAL_THEN ([[((\t:real^1. lift(Re(vector_derivative g (at t)) * Im(g t)))
      has_integral lift(measure(inside(path_image(g:real^1->complex)))))
     (interval[vec 0,vec 1])]]) ASSUME_TAC THENL
     [SUBGOAL_THEN ([[!t:real^1. lift(Re(vector_derivative g (at t)) * Im(g t)) =
       --inv(&2) %
         (lift (Re (g t) * Im (vector_derivative g (at t)) +
                  --(Im (g t) * Re (vector_derivative g (at t)))) -
          lift (Re (g t) * Im (vector_derivative g (at t)) +
                  Im (g t) * Re (vector_derivative g (at t))))]]) (fun th => REWRITE_TAC [th]) THENL
       [GEN_TAC THEN REWRITE_TAC [(← HolLight.GSYM LIFT_SUB), (← HolLight.GSYM LIFT_CMUL)] THEN
        AP_TERM_TAC THEN REAL_ARITH_TAC2,
        ALL_TAC] THEN
      SUBGOAL_THEN ([[lift(measure(inside(path_image(g:real^1->complex)))) =
       --inv(&2) % (lift (&2 * --measure(inside(path_image g))) -
                    (vec 0:real^1))]]) SUBST1_TAC THENL
       [REWRITE_TAC [VECTOR_SUB_RZERO, (← HolLight.GSYM LIFT_CMUL), (← HolLight.GSYM LIFT_NEG), LIFT_EQ] THEN
        REAL_ARITH_TAC2,
        ALL_TAC] THEN
      MATCH_MP_TAC HAS_INTEGRAL_CMUL THEN
      MATCH_MP_TAC HAS_INTEGRAL_SUB THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC,
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC [HAS_INTEGRAL_INTEGRABLE], ALL_TAC] THEN
    FIRST_ASSUM (SUBST1_TAC o HolLight.MATCH_MP INTEGRAL_UNIQUE) THEN
    REWRITE_TAC [NORM_LIFT] THEN
    MATCH_MP_TAC h2 THEN
    MATCH_MP_TAC MEASURE_POS_LE THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval GREEN_AREA_ABS_ALT

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py; keep it in step with the `#eval`s above. -/
def ensure : IO Unit := once "Hol100.Green" do
  replay (
          SessionMultiLib.Cauchy.ensureCauchy)
  replay (
          SessionMultiLib.LpSpaces.ensureLpSpaces)
  replay (
          Session.prioritize_real)
  replay (
          wirtinger_dbar)
  replay (
          wirtinger_dz)
  replay (
          WIRTINGER_DBAR_EQ_ZERO)
  replay (
          WIRTINGER_DZ_COMPLEX_DERIVATIVE)
  replay (
          FRECHET_WIRTINGER)
  replay (
          HAS_DERIVATIVE_CNJ)
  replay (
          JACOBIAN_CNJ)
  replay (
          WIRTINGER_DBAR_CNJ)
  replay (
          WIRTINGER_DBAR_I)
  replay (
          WIRTINGER_DBAR_FRECHET)
  replay (
          WIRTINGER_DBAR_CONTINUOUS)
  replay (
          WIRTINGER_DBAR_BOUNDED_SUPPORT)
  replay (
          CAUCHY_TRANSFORM_DBAR_TRANSLATION)
  replay (
          CONTINUOUS_ON_TRANSLATE_UNIV)
  replay (
          BOUNDED_SUPPORT_TRANSLATE)
  replay (
          POLAR_SIMPLIFY)
  replay (
          INV_CEXP_II)
  replay (
          POLAR_CEXP_SIMPLIFY)
  replay (
          WIRTINGER_DBAR_FRECHET_POLAR)
  replay (
          CEXP_2PII)
  replay (
          CEXP_0II)
  replay (
          NORM_CPOW_COMPLEX)
  replay (
          ABSOLUTELY_INTEGRABLE_CPOW)
  replay (
          INV_ABSOLUTELY_INTEGRABLE_BOUNDED)
  replay (
          LSPACE_COMPLEX_INV)
  replay (
          CAUCHY_KERNEL_ABSOLUTELY_INTEGRABLE)
  replay (
          INTEGRAL_IF_CONST)
  replay (
          NEGLIGIBLE_GRAPH_PRODUCT)
  replay (
          MEASURABLE_ON_FUBINI_INTEGRAND)
  replay (
          CAUCHY_KERNEL_NORM_UNIFORM_BOUND)
  replay (
          SUPPORT_BOUNDED_OUTSIDE)
  replay (
          CAUCHY_KERNEL_NORM_TRUNC_INTEGRABLE)
  replay (
          CAUCHY_KERNEL_NORM_TRUNC_CONTINUOUS)
  replay (
          CAUCHY_KERNEL_NORM_TRUNC_CONVERGES)
  replay (
          CAUCHY_KERNEL_WEIGHTED_MEASURABLE)
  replay (
          NEGLIGIBLE_ABSOLUTELY_CONTINUOUS_PATH_IMAGE)
  replay (
          PATH_INTEGRABLE_CONTINUOUS_ABSOLUTELY_CONTINUOUS)
  replay (
          FUBINI_PATH_AREA)
  replay (
          ABSOLUTELY_INTEGRABLE_DBAR_KERNEL)
  replay (
          HAS_DERIVATIVE_CX_DROP)
  replay (
          HAS_DERIVATIVE_II_CX_DROP)
  replay (
          HAS_DERIVATIVE_CEXP_POLAR)
  replay (
          HAS_DERIVATIVE_AFFINE_MUL)
  replay (
          HAS_DERIVATIVE_POLAR_PATH)
  replay (
          CONTINUOUS_ON_COMPLEX_LMUL_FN)
  replay (
          CONT_II_CX_DROP)
  replay (
          CONT_CEXP_POLAR)
  replay (
          CONTINUOUS_ON_POLAR_PATH)
  replay (
          CONTINUOUS_ON_POLAR_PATH_INTERVAL)
  replay (
          CONTINUOUS_ON_F_POLAR)
  replay (
          HAS_VECTOR_DERIVATIVE_F_POLAR)
  replay (
          ANGULAR_FTC)
  replay (
          ANGULAR_INTEGRAL_ZERO)
  replay (
          FRECHET_DERIVATIVE_CX_LMUL)
  replay (
          ANGULAR_INTEGRAL_II_ZERO)
  replay (
          HAS_DERIVATIVE_RADIAL_PATH)
  replay (
          HAS_VECTOR_DERIVATIVE_F_RADIAL)
  replay (
          CONTINUOUS_ON_RADIAL_PATH)
  replay (
          CONTINUOUS_ON_F_RADIAL)
  replay (
          RADIAL_FTC)
  replay (
          INNER_INTEGRAL_SIMPLIFY)
  replay (
          RADIAL_INTEGRAL_NEG_FW)
  replay (
          DROP_POS_OF_NONNEG_NZ)
  replay (
          WIRTINGER_DZ_FRECHET)
  replay (
          WIRTINGER_DZ_CONTINUOUS)
  replay (
          FRECHET_CONTINUOUS_ON_JOINT)
  replay (
          CONTINUOUS_ON_CEXP_SNDCART)
  replay (
          CONTINUOUS_ON_POLAR_PASTECART)
  replay (
          FRECHET_DERIVATIVE_ZERO_OUTSIDE)
  replay (
          ZERO_OUTSIDE_SUPPORT_BALL)
  replay (
          POLAR_POINT_NORM_BOUND)
  replay (
          POLAR_FUBINI_SWAP)
  replay (
          POLAR_INTEGRAL_DECOMPOSITION)
  replay (
          INTEGRAL_CONST_2PI)
  replay (
          INV_TWO_TIMES_TWO_PI)
  replay (
          CAUCHY_TRANSFORM_INVERTS_DBAR)
  replay (
          PIECEWISE_HAS_DERIVATIVE_LOCAL)
  replay (
          PIECEWISE_HAS_REAL_DERIVATIVE_LOCAL)
  replay (
          hermite_cutoff)
  replay (
          hermite_cutoff_deriv)
  replay (
          HAS_REAL_DERIVATIVE_HERMITE_INTERIOR)
  replay (
          HAS_REAL_DERIVATIVE_HERMITE_LEFT)
  replay (
          HAS_REAL_DERIVATIVE_HERMITE_RIGHT)
  replay (
          HAS_REAL_DERIVATIVE_HERMITE_AT_0)
  replay (
          HAS_REAL_DERIVATIVE_HERMITE_AT_1)
  replay (
          HAS_REAL_DERIVATIVE_HERMITE_EXPLICIT)
  replay (
          POLY_CONTINUOUS_REAL1)
  replay (
          HERMITE_CUTOFF_DERIV_CONTINUOUS)
  replay (
          HERMITE_CUTOFF_DIFFERENTIABLE)
  replay (
          HERMITE_CUTOFF_DIFFERENTIABLE_ON)
  replay (
          HERMITE_CUTOFF_CONTINUOUS)
  replay (
          HERMITE_CUTOFF_CHI_HAS_DERIVATIVE)
  replay (
          HERMITE_CUTOFF_LE_0)
  replay (
          HERMITE_CUTOFF_GE_1)
  replay (
          HERMITE_CUTOFF_NONNEG)
  replay (
          HERMITE_CUTOFF_SHIFTED_HAS_DERIVATIVE)
  replay (
          PHI_SHIFTED_CONTINUOUS_ON)
  replay (
          HCD_SHIFTED_CONTINUOUS_ON)
  replay (
          HC_SHIFTED_CONTINUOUS_ON)
  replay (
          SMOOTH_EXTENSION_FROM_OPEN)
  replay (
          ABSOLUTELY_INTEGRABLE_CAUCHY_PATH_PRODUCT)
  replay (
          INTEGRABLE_WINDING_DBAR_PRODUCT)
  replay (
          COMPLEX_GREEN_ALT)
  replay (
          COMPLEX_GREEN)
  replay (
          COMPLEX_GREEN_INSIDE)
  replay (
          HAS_PATH_INTEGRAL_CNJ)
  replay (
          COMPLEX_GREEN_CNJ)
  replay (
          HAS_PATH_INTEGRAL_I_CLOSED)
  replay (
          COMPLEX_GREEN_I)
  replay (
          COMPLEX_GREEN_AREA)
  replay (
          COMPLEX_GREEN_AREA_ABS)
  replay (
          GREEN_THEOREM_CURL)
  replay (
          GREEN_AREA)
  replay (
          GREEN_AREA_ALT)
  replay (
          GREEN_AREA_ABS)
  replay (
          GREEN_AREA_ABS_ALT)
-- @@ENSURE END

end Hol100.Green
