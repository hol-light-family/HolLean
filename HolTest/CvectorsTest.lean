/- File: HolTest/CvectorsTest.lean
Runtime test suite: Multivariate/cvectors.ml
(HolMultiLib/CVectors.lean, wired by SessionMultiLib/CVectors.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/cvectors.ml"`, then `string_of_thm`).  The whole file
is also compared with HOL Light by tools/cvecdiff: all 302 theorems
structurally and by their printed forms.

The theorem checks are spread over the file: the additions to the base
library, vector maps, the vector space laws, linearity, pasting, real and
imaginary parts, flattening, conjugation, cross and dot products, norms,
collinearity, orthogonality and infinite sums.  The procedure checks run
CVECTOR_ARITH on terms whose results HOL Light printed.

Loading cvectors.ml (`ensureCvectors`) builds every bundle in file order; a
proof that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.CVectors

open HolCore.Kernel SessionMultiLib.CVectors
open HolTest.CommonTest HolLight.Syntax

#eval ensureCvectors

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/-- Run a rule or conversion on a parsed term and check the printed theorem. -/
private unsafe def procCheck (lbl : String) (f : term → IO (Except String thm)) (s : String)
    (expected : String) : IO Unit := do
  match ← HolCore.Parser.parse_term s with
  | .error e => IO.println s!"{lbl} -> MISMATCH parse: {e}"
  | .ok tm =>
    match ← f tm with
    | .error e => IO.println s!"{lbl} -> MISMATCH failed: {e}"
    | .ok th => thmCheck lbl th expected

/- ---------------------------------------------------------------------- -/
/- Theorem statements (cvectors.ml), as HOL Light prints them.          -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "cvectors.ml COMPONENT_LE_NORM_ALT" COMPONENT_LE_NORM_ALT
  "|- forall x i. 1 <= i /\\ i <= dimindex (:N) ==> x$i <= norm x"
#eval thmCheck "cvectors.ml ABS_IM_NORM" ABS_IM_NORM "|- forall x. abs (Im x) <= norm x"
#eval thmCheck "cvectors.ml NORM2_ADD_REAL" NORM2_ADD_REAL
  "|- forall x y. real x /\\ real y ==> norm (x + ii * y) pow 2 = norm x pow 2 + norm y pow 2"
#eval thmCheck "cvectors.ml CSQRT_MUL_LCX" CSQRT_MUL_LCX
  "|- forall x y. &0 <= x ==> csqrt (Cx x * y) = Cx (sqrt x) * csqrt y"
#eval thmCheck "cvectors.ml real_of_complex" real_of_complex
  "|- forall c. real_of_complex c = (@r. c = Cx r)"
#eval thmCheck "cvectors.ml REAL_OF_COMPLEX_0" REAL_OF_COMPLEX_0
  "|- forall x. real x ==> (real_of_complex x = &0 <=> x = Cx (&0))"
#eval thmCheck "cvectors.ml vector_map2" vector_map2
  "|- forall f v1 v2. vector_map2 f v1 v2 = (lambda i. f (v1$i) (v2$i))"
#eval thmCheck "cvectors.ml VECTOR_MAP2_COMPONENT" VECTOR_MAP2_COMPONENT
  "|- forall i f v1 v2. vector_map2 f v1 v2$i = f (v1$i) (v2$i)"
#eval thmCheck "cvectors.ml VECTOR_MAP_VECTOR_MAP2" VECTOR_MAP_VECTOR_MAP2
  "|- forall f g u v. vector_map f (vector_map2 g u v) = vector_map2 (\\x y. f (g x y)) u v"
#eval thmCheck "cvectors.ml VECTOR_NEG_IS_A_MAP" VECTOR_NEG_IS_A_MAP "|- (--) = vector_map (--)"
#eval thmCheck "cvectors.ml COMPLEX_SUB_IS_A_MAP" COMPLEX_SUB_IS_A_MAP "|- (-) = vector_map2 (-)"
#eval thmCheck "cvectors.ml VECTOR_ZIP_COMPONENT" VECTOR_ZIP_COMPONENT
  "|- forall i v1 v2. vector_zip v1 v2$i = v1$i,v2$i"
#eval thmCheck "cvectors.ml cvector_zero" cvector_zero "|- cvector_zero = vector_const (Cx (&0))"
#eval thmCheck "cvectors.ml cvector_mul" cvector_mul "|- forall a. (%) a = vector_map ((*) a)"
#eval thmCheck "cvectors.ml CVECTOR_SUB_COMPONENT" CVECTOR_SUB_COMPONENT
  "|- forall X Y i. (X - Y)$i = X$i - Y$i"
#eval thmCheck "cvectors.ml CVECTOR_ADD_ASSOC" CVECTOR_ADD_ASSOC
  "|- forall x y z. x + y + z = (x + y) + z"
#eval thmCheck "cvectors.ml CVECTOR_ADD_INV" CVECTOR_ADD_INV
  "|- forall x. x + --x = cvector_zero /\\ --x + x = cvector_zero"
#eval thmCheck "cvectors.ml CVECTOR_NEG_MINUS1" CVECTOR_NEG_MINUS1
  "|- forall x. --x = --Cx (&1) % x"
#eval thmCheck "cvectors.ml CVECTOR_MUL_RCANCEL" CVECTOR_MUL_RCANCEL
  "|- forall a b x. a % x = b % x <=> a = b \\/ x = cvector_zero"
#eval thmCheck "cvectors.ml CLINEAR_NEGATION" CLINEAR_NEGATION "|- clinear (--)"
#eval thmCheck "cvectors.ml CLINEAR_NEG" CLINEAR_NEG
  "|- forall f x. clinear f ==> f (--x) = --f x"
#eval thmCheck "cvectors.ml FSTCART_SNDCART_CVECTOR_MUL" FSTCART_SNDCART_CVECTOR_MUL
  "|- forall x c. fstcart (c % x) = c % fstcart x /\\ sndcart (c % x) = c % sndcart x"
#eval thmCheck "cvectors.ml VECTOR_TO_CVECTOR_MUL" VECTOR_TO_CVECTOR_MUL
  "|- forall a x. vector_to_cvector (a % x) = Cx a % vector_to_cvector x"
#eval thmCheck "cvectors.ml VECTOR_TO_CVECTOR_CVECTOR_RE_IM" VECTOR_TO_CVECTOR_CVECTOR_RE_IM
  "|- forall x. vector_to_cvector (cvector_re x) + ii % vector_to_cvector (cvector_im x) = x"
#eval thmCheck "cvectors.ml CVECTOR_IM_VECTOR_MAP2" CVECTOR_IM_VECTOR_MAP2
  "|- forall f v1 v2. cvector_im (vector_map2 f v1 v2) = vector_map2 (\\x y. Im (f x y)) v1 v2"
#eval thmCheck "cvectors.ml cvector_unflatten" cvector_unflatten
  "|- forall v. cvector_unflatten v = complex_vector (fstcart v,sndcart v)"
#eval thmCheck "cvectors.ml FLATTEN_NEG" FLATTEN_NEG
  "|- forall x. cvector_flatten (--x) = --cvector_flatten x"
#eval thmCheck "cvectors.ml FLATTEN_SUB" FLATTEN_SUB
  "|- forall x y. cvector_flatten (x - y) = cvector_flatten x - cvector_flatten y"
#eval thmCheck "cvectors.ml CVECTOR_CNJ_CNJ" CVECTOR_CNJ_CNJ
  "|- forall x. cvector_cnj (cvector_cnj x) = x"
#eval thmCheck "cvectors.ml CCROSS_JACOBI" CCROSS_JACOBI
  "|- forall x y z. x ccross y ccross z + y ccross z ccross x + z ccross x ccross y = cvector_zero"
#eval thmCheck "cvectors.ml cdot" cdot
  "|- forall x y. x cdot y = vsum (1..dimindex (:N)) (\\i. x$i * cnj (y$i))"
#eval thmCheck "cvectors.ml CDOT_SYM" CDOT_SYM "|- forall x y. x cdot y = cnj (y cdot x)"
#eval thmCheck "cvectors.ml CNJ_ZERO" CNJ_ZERO "|- cnj (Cx (&0)) = Cx (&0)"
#eval thmCheck "cvectors.ml CDOT3" CDOT3
  "|- forall x y. x cdot y = x$1 * cnj (y$1) + x$2 * cnj (y$2) + x$3 * cnj (y$3)"
#eval thmCheck "cvectors.ml cnorm2" cnorm2 "|- forall v. cnorm2 v = real_of_complex (v cdot v)"
#eval thmCheck "cvectors.ml CNORM2_MUL" CNORM2_MUL
  "|- forall a x. cnorm2 (a % x) = norm a pow 2 * cnorm2 x"
#eval thmCheck "cvectors.ml cnorm" cnorm "|- norm = sqrt o cnorm2"
#eval thmCheck "cvectors.ml CNORM_MUL" CNORM_MUL "|- forall a x. norm (a % x) = norm a * norm x"
#eval thmCheck "cvectors.ml cunit" cunit "|- forall X. cunit X = inv (Cx (norm X)) % X"
#eval thmCheck "cvectors.ml collinear_cvectors" collinear_cvectors
  "|- forall x y. collinear_cvectors x y <=> (exists a. y = a % x \\/ x = a % y)"
#eval thmCheck "cvectors.ml CCROSS_COLLINEAR_CVECTORS" CCROSS_COLLINEAR_CVECTORS
  "|- forall x y. x ccross y = cvector_zero <=> collinear_cvectors x y"
#eval thmCheck "cvectors.ml corthogonal" corthogonal
  "|- forall x y. corthogonal x y <=> x cdot y = Cx (&0)"
#eval thmCheck "cvectors.ml CORTHOGONAL_PROJECTION" CORTHOGONAL_PROJECTION
  "|- forall x y. corthogonal (x - (x cdot cunit y) % cunit y) y"
#eval thmCheck "cvectors.ml CDOT_PYTHAGOREAN" CDOT_PYTHAGOREAN
  "|- forall x y. corthogonal x y ==> cnorm2 (x + y) = cnorm2 x + cnorm2 y"
#eval thmCheck "cvectors.ml CDOT_CAUCHY_SCHWARZ_EQUAL" CDOT_CAUCHY_SCHWARZ_EQUAL
  "|- forall x y. norm (x cdot y) = norm x * norm y <=> collinear_cvectors x y"
#eval thmCheck "cvectors.ml CNORM_TRIANGLE" CNORM_TRIANGLE
  "|- forall x y. norm (x + y) <= norm x + norm y"
#eval thmCheck "cvectors.ml REAL_ABS_SUB_CNORM" REAL_ABS_SUB_CNORM
  "|- forall x y. abs (norm x - norm y) <= norm (x - y)"
#eval thmCheck "cvectors.ml csummable" csummable
  "|- forall s f. csummable s f <=> summable s (cvector_re o f) /\\ summable s (cvector_im o f)"
#eval thmCheck "cvectors.ml CINFSUM_LINEAR" CINFSUM_LINEAR
  "|- forall f h s. csummable s f /\\ clinear h ==> cinfsum s (h o f) = h (cinfsum s f)"

/- ---------------------------------------------------------------------- -/
/- The procedure, on terms HOL Light ran it on.                           -/
/- ---------------------------------------------------------------------- -/
#eval procCheck "cvectors.ml CVECTOR_ARITH 1" CVECTOR_ARITH
  "!x y:complex^N. (x + y) - y = x"
  "|- forall x y. (x + y) - y = x"
#eval procCheck "cvectors.ml CVECTOR_ARITH 2" CVECTOR_ARITH
  "!a x y:complex^N. a % (x - y) = a % x - a % y"
  "|- forall a x y. a % (x - y) = a % x - a % y"
