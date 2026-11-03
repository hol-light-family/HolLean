/- File: HolTest/TranscendentalsTest.lean
Runtime test suite: Multivariate/transcendentals.ml
(HolMultiLib/Transcendentals.lean, wired by SessionMultiLib/Transcendentals.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/transcendentals.ml"`, then `string_of_thm`).  The whole file is also
compared with HOL Light by tools/transcendentalsdiff: all exported theorems structurally
and by their printed forms.  The 20 theorems here are spread evenly over the
file; theorems that print with `?nnn` invented type variables are left out.

Loading transcendentals.ml (`ensureTranscendentals`) builds every bundle in file order; a proof
that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.Transcendentals

open HolCore.Kernel Session SessionMultiLib.Transcendentals
open HolTest.CommonTest HolLight.Syntax

#eval ensureTranscendentals

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

#eval thmCheck "transcendentals.ml CEXP_0" CEXP_0
  "|- cexp (Cx (&0)) = Cx (&1)"
#eval thmCheck "transcendentals.ml COMPLEX_MUL_CSIN_CSIN" COMPLEX_MUL_CSIN_CSIN
  "|- forall w z. csin w * csin z = (ccos (w - z) - ccos (w + z)) / Cx (&2)"
#eval thmCheck "transcendentals.ml CNJ_CCOS" CNJ_CCOS
  "|- forall z. cnj (ccos z) = ccos (cnj z)"
#eval thmCheck "transcendentals.ml COS_SUB" COS_SUB
  "|- forall w z. cos (w - z) = cos w * cos z + sin w * sin z"
#eval thmCheck "transcendentals.ml LOG_LE_STRONG" LOG_LE_STRONG
  "|- forall x. &0 < &1 + x ==> log (&1 + x) <= x"
#eval thmCheck "transcendentals.ml COS_POS_PI" COS_POS_PI
  "|- forall x. --(pi / &2) < x /\\ x < pi / &2 ==> &0 < cos x"
#eval thmCheck "transcendentals.ml CEXP_EQ_1" CEXP_EQ_1
  "|- forall z.        cexp z = Cx (&1) <=>        Re z = &0 /\\ (exists n. integer n /\\ Im z = &2 * n * pi)"
#eval thmCheck "transcendentals.ml TAYLOR_CCOS" TAYLOR_CCOS
  "|- forall n z.        norm        (ccos z -         vsum (0..n)         (\\k. --Cx (&1) pow k * z pow (2 * k) / Cx (&(FACT (2 * k))))) <=        exp (abs (Im z)) * norm z pow (2 * n + 2) / &(FACT (2 * n + 1))"
#eval thmCheck "transcendentals.ml MATRIX_ROTATE2D" MATRIX_ROTATE2D
  "|- forall t.        matrix (rotate2d t) =        vector [vector [cos t; --sin t]; vector [sin t; cos t]]"
#eval thmCheck "transcendentals.ml CTAN_NEG" CTAN_NEG
  "|- forall z. ctan (--z) = --ctan z"
#eval thmCheck "transcendentals.ml SIN_TAN" SIN_TAN
  "|- forall x. abs x < pi / &2 ==> sin x = tan x / sqrt (&1 + tan x pow 2)"
#eval thmCheck "transcendentals.ml CONTINUOUS_ON_CLOG" CONTINUOUS_ON_CLOG
  "|- forall s.        (forall z. z IN s /\\ Im z = &0 ==> &0 < Re z) ==> clog continuous_on s"
#eval thmCheck "transcendentals.ml CPOW_EQ_0" CPOW_EQ_0
  "|- forall w z. w cpow z = Cx (&0) <=> w = Cx (&0)"
#eval thmCheck "transcendentals.ml ATN_0" ATN_0
  "|- atn (&0) = &0"
#eval thmCheck "transcendentals.ml CASN_UNIQUE" CASN_UNIQUE
  "|- forall w z.        csin z = w /\\        (abs (Re z) < pi / &2 \\/ abs (Re z) = pi / &2 /\\ Im z = &0)        ==> casn w = z"
#eval thmCheck "transcendentals.ml CSIN_CACS_NZ" CSIN_CACS_NZ
  "|- forall z. ~(z pow 2 = Cx (&1)) ==> ~(csin (cacs z) = Cx (&0))"
#eval thmCheck "transcendentals.ml ACS_MONO_LT_EQ" ACS_MONO_LT_EQ
  "|- forall x y. abs x <= &1 /\\ abs y <= &1 ==> (acs x < acs y <=> y < x)"
#eval thmCheck "transcendentals.ml LIM_INV_X_POW_OFFSET" LIM_INV_X_POW_OFFSET
  "|- forall z n.        1 <= n ==> ((\\x. inv (Cx x + z) pow n) --> Cx (&0)) at_posinfinity"
#eval thmCheck "transcendentals.ml REAL_POW_ROOT" REAL_POW_ROOT
  "|- forall n x. ODD n \\/ ~(n = 0) /\\ &0 <= x ==> root n x pow n = x"
#eval thmCheck "transcendentals.ml REAL_INV_RPOW" REAL_INV_RPOW
  "|- forall x y. inv (x rpow y) = inv x rpow y"
