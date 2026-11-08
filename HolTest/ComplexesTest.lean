/- File: HolTest/ComplexesTest.lean
Runtime test suite: Multivariate/complexes.ml
(HolMultiLib/Complexes.lean, wired by SessionMultiLib/Complexes.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/complexes.ml"`, then `string_of_thm`).  The whole file
is also compared with HOL Light by tools/cpxdiff: all 319 theorems
structurally and by their printed forms.

The theorem checks are spread over the file: the definitions, the algebraic
laws, Cx, Re and Im, inverses, norms, conjugation, square roots, linear maps,
the real complex numbers, geometric progressions, polynomial functions and
complex products.  The procedure checks run COMPLEX_RING, COMPLEX_FIELD,
COMPLEX_POLY_CONV, COMPLEX_RAT_POW_CONV, COMPLEX_RAT_ADD_CONV and
SIMPLE_COMPLEX_ARITH on terms whose results HOL Light printed.

Loading complexes.ml (`ensureComplexes`) builds every bundle in file order; a
proof that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.Complexes

open HolCore.Kernel SessionMultiLib.ComplexAlgebra SessionMultiLib.Complexes
open HolTest.CommonTest HolLight.Syntax

#eval ensureComplexes

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
/- Theorem statements (complexes.ml), as HOL Light prints them.           -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "complexes.ml IM_DEF" IM_DEF "|- forall z. Im z = z$2"
#eval thmCheck "complexes.ml ii" ii "|- ii = complex (&0,&1)"
#eval thmCheck "complexes.ml complex_mul" complex_mul
  "|- forall w z. w * z = complex (Re w * Re z - Im w * Im z,Re w * Im z + Im w * Re z)"
#eval thmCheck "complexes.ml complex_pow" complex_pow
  "|- x pow 0 = Cx (&1) /\\ (forall n. x pow SUC n = x * x pow n)"
#eval thmCheck "complexes.ml RE" RE "|- Re (complex (x,y)) = x"
#eval thmCheck "complexes.ml complex_add" complex_add
  "|- w + z = complex (Re w + Re z,Im w + Im z)"
#eval thmCheck "complexes.ml COMPLEX_MUL_SYM" COMPLEX_MUL_SYM "|- forall x y. x * y = y * x"
#eval thmCheck "complexes.ml COMPLEX_MUL_LNEG" COMPLEX_MUL_LNEG
  "|- forall x y. --x * y = --(x * y)"
#eval thmCheck "complexes.ml COMPLEX_SUB_RNEG" COMPLEX_SUB_RNEG
  "|- forall x y. x - --y = x + y"
#eval thmCheck "complexes.ml COMPLEX_DIV_REFL" COMPLEX_DIV_REFL
  "|- forall x. ~(x = Cx (&0)) ==> x / x = Cx (&1)"
#eval thmCheck "complexes.ml COMPLEX_POW_II_2" COMPLEX_POW_II_2 "|- ii pow 2 = --Cx (&1)"
#eval thmCheck "complexes.ml CX_INJ" CX_INJ "|- forall x y. Cx x = Cx y <=> x = y"
#eval thmCheck "complexes.ml CX_SUB" CX_SUB "|- forall x y. Cx (x - y) = Cx x - Cx y"
#eval thmCheck "complexes.ml COMPLEX_EXPAND" COMPLEX_EXPAND
  "|- forall z. z = Cx (Re z) + ii * Cx (Im z)"
#eval thmCheck "complexes.ml IM_CMUL" IM_CMUL "|- forall a z. Im (a % z) = a * Im z"
#eval thmCheck "complexes.ml COMPLEX_INV_MUL" COMPLEX_INV_MUL
  "|- forall w z. inv (w * z) = inv w * inv z"
#eval thmCheck "complexes.ml COMPLEX_EQ_MUL_LCANCEL" COMPLEX_EQ_MUL_LCANCEL
  "|- forall x y z. x * y = x * z <=> x = Cx (&0) \\/ y = z"
#eval thmCheck "complexes.ml COMPLEX_DIV_1" COMPLEX_DIV_1 "|- forall z. z / Cx (&1) = z"
#eval thmCheck "complexes.ml COMPLEX_NEG_INV" COMPLEX_NEG_INV
  "|- forall x. --inv x = inv (--x)"
#eval thmCheck "complexes.ml COMPLEX_NORM_MUL" COMPLEX_NORM_MUL
  "|- forall w z. norm (w * z) = norm w * norm z"
#eval thmCheck "complexes.ml COMPLEX_POW_EQ_1" COMPLEX_POW_EQ_1
  "|- forall z n. z pow n = Cx (&1) ==> norm z = &1 \\/ n = 0"
#eval thmCheck "complexes.ml CNJ_ADD" CNJ_ADD "|- forall w z. cnj (w + z) = cnj w + cnj z"
#eval thmCheck "complexes.ml COMPLEX_MUL_CNJ" COMPLEX_MUL_CNJ
  "|- forall z. cnj z * z = Cx (norm z) pow 2 /\\ z * cnj z = Cx (norm z) pow 2"
#eval thmCheck "complexes.ml IM_COMPLEX_DIV_GE_0" IM_COMPLEX_DIV_GE_0
  "|- forall a b. &0 <= Im (a / b) <=> &0 <= Im (a * cnj b)"
#eval thmCheck "complexes.ml IM_COMPLEX_INV_LT_0" IM_COMPLEX_INV_LT_0
  "|- forall z. Im (inv z) < &0 <=> &0 < Im z"
#eval thmCheck "complexes.ml CSQRT" CSQRT "|- forall z. csqrt z pow 2 = z"
#eval thmCheck "complexes.ml CX_SQRT" CX_SQRT
  "|- forall x. &0 <= x ==> Cx (sqrt x) = csqrt (Cx x)"
#eval thmCheck "complexes.ml CSQRT_UNIQUE" CSQRT_UNIQUE
  "|- forall s z. s pow 2 = z /\\ (&0 < Re s \\/ Re s = &0 /\\ &0 <= Im s) ==> csqrt z = s"
#eval thmCheck "complexes.ml LINEAR_COMPLEX_RMUL" LINEAR_COMPLEX_RMUL
  "|- forall f c. linear f ==> linear (\\x. f x * c)"
#eval thmCheck "complexes.ml COMPLEX_ORTHOGONAL_TRANSFORMATION"
  COMPLEX_ORTHOGONAL_TRANSFORMATION
  "|- forall f. orthogonal_transformation f <=>
      (exists c. norm c = &1 /\\ (f = (\\z. c * z) \\/ f = (\\z. c * cnj z)))"
#eval thmCheck "complexes.ml COMPLEX_SUB_POW" COMPLEX_SUB_POW
  "|- forall x y n. 1 <= n ==> x pow n - y pow n =
      (x - y) * vsum (0..n - 1) (\\i. x pow i * y pow (n - 1 - i))"
#eval thmCheck "complexes.ml real" real "|- forall z. real z <=> Im z = &0"
#eval thmCheck "complexes.ml REAL_SEGMENT" REAL_SEGMENT
  "|- forall a b x. x IN segment [a,b] /\\ real a /\\ real b ==> real x"
#eval thmCheck "complexes.ml INTERIOR_REAL" INTERIOR_REAL "|- interior real = {}"
#eval thmCheck "complexes.ml VSUM_GP" VSUM_GP
  "|- forall x m n. vsum (m..n) (\\i. x pow i) =
      (if n < m then Cx (&0) else if x = Cx (&1) then Cx (&((n + 1) - m))
       else (x pow m - x pow SUC n) / (Cx (&1) - x))"
#eval thmCheck "complexes.ml COMPLEX_POLYFUN_ROOTBOUND" COMPLEX_POLYFUN_ROOTBOUND
  "|- forall n c. ~(forall i. i IN 0..n ==> c i = Cx (&0))
      ==> FINITE {z | vsum (0..n) (\\i. c i * z pow i) = Cx (&0)} /\\
          CARD {z | vsum (0..n) (\\i. c i * z pow i) = Cx (&0)} <= n"
#eval thmCheck "complexes.ml COMPLEX_POLYFUN_EQ_CONST" COMPLEX_POLYFUN_EQ_CONST
  "|- forall n c k. (forall z. vsum (0..n) (\\i. c i * z pow i) = k) <=>
      c 0 = k /\\ (forall i. i IN 1..n ==> c i = Cx (&0))"
#eval thmCheck "complexes.ml CPRODUCT_PAIR" CPRODUCT_PAIR
  "|- forall f m n. cproduct (2 * m..2 * n + 1) f = cproduct (m..n) (\\i. f (2 * i) * f (2 * i + 1))"

/- ---------------------------------------------------------------------- -/
/- The procedures, on terms HOL Light ran them on.                        -/
/- ---------------------------------------------------------------------- -/
#eval procCheck "complexes.ml COMPLEX_RING 1" COMPLEX_RING
  "(x + ii * y) * (x - ii * y) = x pow 2 + y pow 2"
  "|- (x + ii * y) * (x - ii * y) = x pow 2 + y pow 2"
#eval procCheck "complexes.ml COMPLEX_RING 2" COMPLEX_RING
  "(a + b) pow 3 = a pow 3 + Cx(&3) * a pow 2 * b + Cx(&3) * a * b pow 2 + b pow 3"
  "|- (a + b) pow 3 = a pow 3 + Cx (&3) * a pow 2 * b + Cx (&3) * a * b pow 2 + b pow 3"
#eval procCheck "complexes.ml COMPLEX_FIELD 1" COMPLEX_FIELD
  "~(z = Cx(&0)) ==> z / z = Cx(&1)"
  "|- ~(z = Cx (&0)) ==> z / z = Cx (&1)"
#eval procCheck "complexes.ml COMPLEX_FIELD 2" COMPLEX_FIELD
  "~(x = Cx(&0)) ==> inv(x) * x pow 2 = x"
  "|- ~(x = Cx (&0)) ==> inv x * x pow 2 = x"
#eval procCheck "complexes.ml COMPLEX_POLY_CONV 1" COMPLEX_POLY_CONV
  "(x + Cx(&1)) pow 2 - x * x"
  "|- (x + Cx (&1)) pow 2 - x * x = Cx (&2) * x + Cx (&1)"
#eval procCheck "complexes.ml COMPLEX_POLY_CONV 2" COMPLEX_POLY_CONV
  "(x / Cx(&2) + y) * Cx(&4)"
  "|- (x / Cx (&2) + y) * Cx (&4) = Cx (&2) * x + Cx (&4) * y"
#eval procCheck "complexes.ml COMPLEX_RAT_POW_CONV" COMPLEX_RAT_POW_CONV
  "Cx(&2) pow 3" "|- Cx (&2) pow 3 = Cx (&8)"
#eval procCheck "complexes.ml COMPLEX_RAT_ADD_CONV" COMPLEX_RAT_ADD_CONV
  "Cx(&1 / &2) + Cx(&1 / &3)" "|- Cx (&1 / &2) + Cx (&1 / &3) = Cx (&5 / &6)"
#eval procCheck "complexes.ml SIMPLE_COMPLEX_ARITH" SIMPLE_COMPLEX_ARITH
  "w * (z + Cx(&1)) = w * z + w" "|- w * (z + Cx (&1)) = w * z + w"
