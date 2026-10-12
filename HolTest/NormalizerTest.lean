/- File: HolTest/NormalizerTest.lean
Runtime test suite: normalizer.ml - canonical polynomial form.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- Tests: normalizer.ml - canonical polynomial form for the naturals.     -/
/- ---------------------------------------------------------------------- -/

/- ---------------------------------------------------------------------- -/
/- Forcing any `NUM_NORMALIZE_CONV`-adjacent theorem builds the whole      -/
/- natural-number `SemiringCtx`: `SEMIRING_PTHS` is proved and split into  -/
/- 38 conjuncts, and `sth`/`rth` are read back.  `#eval Session.ARITH_MULT -/
/- forces the `calc_num.ml` arithmetic layer (so `NUM_ADD/MULT/EXP_CONV`   -/
/- work) and, crucially, forces `EXP`/`MULT`/`ADD` to be CONSTANTS before  -/
/- any term mentioning `EXP` below is parsed (a not-yet-declared constant  -/
/- parses as a variable, which would silently break the conversion).       -/
/- ---------------------------------------------------------------------- -/

#eval Session.ARITH_MULT

/- ---------------------------------------------------------------------- -/
/- Self-checking helper: normalise `expr` with `NUM_NORMALIZE_CONV` and    -/
/- compare the printed RHS (spaces stripped) against `expected` (also      -/
/- space-stripped).  Prints `-> OK` or `-> MISMATCH got=...`, mirroring    -/
/- CalcNumTest's `numConvCheck`.  A bare `|-  = ` line (empty RHS) is the   -/
/- signature of a panicked bundle serving `Inhabited` defaults; every      -/
/- printed result below carries a concrete RHS, so its absence confirms    -/
/- the real context was built.                                             -/
/- ---------------------------------------------------------------------- -/

private unsafe def normCheck (lbl expr expected : String) : IO Unit := do
  match ← HolCore.Parser.parse_term expr with
  | .error e => IO.println s!"{lbl} parse ERR: {e}"
  | .ok tm =>
    match ← Session.NUM_NORMALIZE_CONV tm with
    | .error e => IO.println s!"{lbl} ERR: {e}"
    | .ok th =>
      match HolCore.Equal.rhs (concl th) with
      | .error e => IO.println s!"{lbl} rhs ERR: {e}"
      | .ok r =>
        let got := ((← HolCore.Printer.string_of_term r).replace "\n" "").replace " " ""
        let exp := expected.replace " " ""
        if got == exp then IO.println s!"{lbl} -> OK"
        else IO.println s!"{lbl} -> MISMATCH got={got}"

/- ---------------------------------------------------------------------- -/
/- Constant folding: the semiring-constant conversions fire on pure        -/
/- numerals (NUM_ADD_CONV / NUM_MULT_CONV / NUM_EXP_CONV).                 -/
/- ---------------------------------------------------------------------- -/
#eval normCheck "const 2+3" "2 + 3" "5"       -- 2 + 3 = 5
#eval normCheck "const 2*3" "2 * 3" "6"       -- 2 * 3 = 6
#eval normCheck "const 2EXP3" "2 EXP 3" "8"   -- 2 EXP 3 = 8

/- ---------------------------------------------------------------------- -/
/- A single variable: collect a repeated sum into a coefficient, a repeated -/
/- product into a power, and add exponents on like powers.                 -/
/- ---------------------------------------------------------------------- -/
#eval normCheck "var x+x" "x + x" "2 * x"                 -- x + x = 2 * x
#eval normCheck "var x*x" "x * x" "x EXP 2"               -- x * x = x^2
#eval normCheck "var xEXP2*xEXP3" "x EXP 2 * x EXP 3" "x EXP 5"  -- x^2 * x^3 = x^5

/- ---------------------------------------------------------------------- -/
/- Collecting like terms.                                                 -/
/- ---------------------------------------------------------------------- -/
#eval normCheck "like x+y+x" "x + y + x" "2 * x + y"     -- x + y + x = 2x + y
#eval normCheck "like 2x+3x" "2 * x + 3 * x" "5 * x"     -- 2x + 3x = 5x

/- ---------------------------------------------------------------------- -/
/- Reordering by the variable order (structural `<`: "x" < "y" < "z").    -/
/- ---------------------------------------------------------------------- -/
#eval normCheck "order y+x" "y + x" "x + y"              -- y + x = x + y
#eval normCheck "order y*x" "y * x" "x * y"              -- y * x = x * y
#eval normCheck "order z*y*x" "z * y * x" "x * y * z"    -- z*y*x = x*y*z

/- ---------------------------------------------------------------------- -/
/- Distribution.                                                          -/
/- ---------------------------------------------------------------------- -/
#eval normCheck "dist x*(y+z)" "x * (y + z)" "x * y + x * z"   -- x(y+z) = xy + xz
#eval normCheck "dist (x+y)*(x+y)" "(x + y) * (x + y)"
  "x EXP 2 + 2 * x * y + y EXP 2"                              -- (x+y)^2 expanded

/- ---------------------------------------------------------------------- -/
/- Nested powers.                                                         -/
/- ---------------------------------------------------------------------- -/
#eval normCheck "pow (xEXP2)EXP3" "(x EXP 2) EXP 3" "x EXP 6"        -- (x^2)^3 = x^6
#eval normCheck "pow (x*y)EXP2" "(x * y) EXP 2" "x EXP 2 * y EXP 2"  -- (xy)^2 = x^2 y^2

/- ---------------------------------------------------------------------- -/
/- Binomial expansion.                                                    -/
/- ---------------------------------------------------------------------- -/
#eval normCheck "binom (x+y)EXP2" "(x + y) EXP 2"
  "x EXP 2 + 2 * x * y + y EXP 2"                              -- (x+y)^2
#eval normCheck "binom (x+y)EXP3" "(x + y) EXP 3"
  "x EXP 3 + 3 * x EXP 2 * y + 3 * x * y EXP 2 + y EXP 3"      -- (x+y)^3

/- ---------------------------------------------------------------------- -/
/- Many variables and a deep sum.                                         -/
/- ---------------------------------------------------------------------- -/
#eval normCheck "multi (x+y+z)EXP2" "(x + y + z) EXP 2"
  "x EXP 2 + 2 * x * y + 2 * x * z + y EXP 2 + 2 * y * z + z EXP 2"  -- (x+y+z)^2
#eval normCheck "multi x*y*z+z*y*x" "x * y * z + z * y * x" "2 * x * y * z"  -- collapses

/- ---------------------------------------------------------------------- -/
/- Zero / one absorption and power edge cases.                            -/
/- ---------------------------------------------------------------------- -/
#eval normCheck "abs 0+x" "0 + x" "x"          -- 0 + x = x
#eval normCheck "abs 1*x" "1 * x" "x"          -- 1 * x = x
#eval normCheck "abs 0*x" "0 * x" "0"          -- 0 * x = 0 (collapses to 0)
#eval normCheck "abs xEXP0" "x EXP 0" "1"      -- x^0 = 1 (collapses to a numeral)
#eval normCheck "abs xEXP1" "x EXP 1" "x"      -- x^1 = x

/- ---------------------------------------------------------------------- -/
/- A deeper single-variable sum, collapsing to one monomial.              -/
/- ---------------------------------------------------------------------- -/
#eval normCheck "collapse 5x" "x + x + x + x + x" "5 * x"  -- five copies -> 5x
