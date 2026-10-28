/- File: SessionMath/Normalizer.lean
normalizer.ml: the canonical polynomial normalizer for the naturals
(`NmzP`), built by `initialize` when this module is imported.
-/
import SessionMath.CalcNum
import HolMath.Normalizer

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Simp HolCore.Theorems HolCore.Classic

namespace Session

private def ioOk' {α : Type} (what : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{what}: {e}")


/- normalizer.ml : canonical polynomial normalization for the naturals.   -/
/- ---------------------------------------------------------------------- -/

/-- The natural-number `SemiringCtx` and normalizer.ml's `SEMIRING_PTHS`,
    proved once while it is built (normalizer.ml 542-565). -/
initialize NmzP : HolMath.Normalizer.SemiringCtx × thm ←
  ioOk' "setupNumNormalizeCtx" (HolMath.Normalizer.setupNumNormalizeCtx' TRUTH ADD_CLAUSES
    MULT_CLAUSES EXP LEFT_ADD_DISTRIB ADD_AC MULT_AC ASM_MESON_TAC
    INDUCT_TAC num_CONV
    NUM_ADD_CONV NUM_MULT_CONV NUM_EXP_CONV).run

def Nmz : HolMath.Normalizer.SemiringCtx := NmzP.1

/-- The natural-number `SemiringCtx` (normalizer.ml 542-565). -/
def numSemiringCtx : HolMath.Normalizer.SemiringCtx := Nmz

/-- `SEMIRING_NORMALIZERS_CONV` with the OCaml interface (normalizer.ml 9):
    `sth rth (is_semiring_constant, ADD_CONV, MUL_CONV, POW_CONV)
    variable_order`, returning the six conversions as a tuple.  The Lean
    version takes a prebuilt `SemiringCtx`; this builds it, as the OCaml
    does on each call, from the `SEMIRING_PTHS` proved once. -/
def SEMIRING_NORMALIZERS_CONV (sth rth : thm)
    (cs : (term → Bool) × ioconv × ioconv × ioconv)
    (variable_order : term → term → Bool) :
    ExceptT String IO (ioconv × ioconv × ioconv × ioconv × ioconv × ioconv) := do
  let (is_semiring_constant, add_conv, mul_conv, pow_conv) := cs
  -- `SEMIRING_PTHS` is proved once, when normalizer.ml defines
  -- SEMIRING_NORMALIZERS_CONV (here: when the natural-number normalizer is
  -- built), not on each call.
  let K ← HolMath.Normalizer.setupSemiringCtxFrom NmzP.2 TRUTH sth rth
            is_semiring_constant add_conv mul_conv pow_conv variable_order
  let P := HolMath.Normalizer.SEMIRING_NORMALIZERS_CONV K
             NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV num_CONV
  return (P.POLYNOMIAL_NEG_CONV, P.POLYNOMIAL_ADD_CONV, P.POLYNOMIAL_SUB_CONV,
          P.POLYNOMIAL_MUL_CONV, P.POLYNOMIAL_POW_CONV, P.POLYNOMIAL_CONV)

/-- The six polynomial conversions for the naturals, bundled by
    `SEMIRING_NORMALIZERS_CONV` (normalizer.ml 537-538).  The IO-valued
    exponent conversions and `num_CONV` — which are NOT stored in the
    `SemiringCtx` — are threaded in here, matching the OCaml.  `NUM_SUC_CONV`
    is the caller-supplied successor conversion the monomial layer needs. -/
def numPolynomialConvs : HolMath.Normalizer.PolynomialConvs :=
  HolMath.Normalizer.SEMIRING_NORMALIZERS_CONV Nmz
    NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV num_CONV

/-- `POLYNOMIAL_NEG_CONV` for the naturals (normalizer.ml 491-497).  In this
    instance `rth = TRUTH`, so `neg_tm` is a DUMMY and a real negation never
    matches — the conversion fails, exactly as the OCaml intends. -/
def NORM_POLYNOMIAL_NEG_CONV : ioconv := numPolynomialConvs.POLYNOMIAL_NEG_CONV

/-- `POLYNOMIAL_ADD_CONV` for the naturals (normalizer.ml 374-440). -/
def NORM_POLYNOMIAL_ADD_CONV : ioconv := numPolynomialConvs.POLYNOMIAL_ADD_CONV

/-- `POLYNOMIAL_SUB_CONV` for the naturals (normalizer.ml 502-509).  DUMMY
    `sub_tm` in this instance; never routed to for a real subtraction. -/
def NORM_POLYNOMIAL_SUB_CONV : ioconv := numPolynomialConvs.POLYNOMIAL_SUB_CONV

/-- `POLYNOMIAL_MUL_CONV` for the naturals (normalizer.ml 445-467). -/
def NORM_POLYNOMIAL_MUL_CONV : ioconv := numPolynomialConvs.POLYNOMIAL_MUL_CONV

/-- `POLYNOMIAL_POW_CONV` for the naturals (normalizer.ml 472-486). -/
def NORM_POLYNOMIAL_POW_CONV : ioconv := numPolynomialConvs.POLYNOMIAL_POW_CONV

/-- `NUM_NORMALIZE_CONV tm` (normalizer.ml 541-565): put a natural-number
    term into canonical polynomial form.  This is the SIXTH component
    (`POLYNOMIAL_CONV`) of the tuple `SEMIRING_NORMALIZERS_CONV` returns; the
    OCaml discards the other five with
    `let _,_,_,_,_,NUM_NORMALIZE_CONV = ... in NUM_NORMALIZE_CONV`. -/
def NUM_NORMALIZE_CONV : ioconv := numPolynomialConvs.POLYNOMIAL_CONV

/- ---------------------------------------------------------------------- -/

end Session
