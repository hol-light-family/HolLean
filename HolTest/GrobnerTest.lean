/- File: HolTest/GrobnerTest.lean
Runtime test suite: grobner.ml - Grobner basis ring/ideal decision procedure.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- Tests: grobner.ml - two layers.  (1) The PURE Grobner algorithm         -/
/- (polynomial arithmetic, `monic`, `grobner_refute`/`resolve_proof`,      -/
/- `grobner_ideal`), callable with no Session state.  (2) `NUM_RING` END   -/
/- TO END on real `num` ring identities - the decisive soundness test that -/
/- the Groebner certificates become genuine theorems.                      -/
/- ---------------------------------------------------------------------- -/

/- ---------------------------------------------------------------------- -/
/- Forcing `Session.ARITH_MULT` forces the whole `calc_num.ml` arithmetic  -/
/- layer (so `NUM_ADD/MULT/EXP_CONV` work) and, crucially, forces          -/
/- `EXP`/`MULT`/`ADD` to be CONSTANTS before any term mentioning `EXP`     -/
/- below is parsed (a not-yet-declared constant parses as a variable,      -/
/- which would silently break `NUM_RING`).  `#eval Session.DIVISION`       -/
/- likewise forces DIV/MOD to be constants.  A bare `|-  = ` line (empty   -/
/- RHS) would be the signature of a panicked bundle serving `Inhabited`    -/
/- defaults; every printed result below carries a concrete conclusion, so  -/
/- its absence confirms the real context was built.                        -/
/- ---------------------------------------------------------------------- -/

#eval Session.ARITH_MULT
#eval Session.DIVISION

/- ====================================================================== -/
/- LAYER 1: the PURE Grobner algorithm (no Session needed).                -/
/-                                                                         -/
/- Encoding: monomial `[a,b]` = x^a * y^b; polynomials are lists of        -/
/- monomials in DESCENDING order.  So `x = [(1,[1,0])]`, `y = [(1,[0,1])]`. -/
/- ====================================================================== -/

open HolMath.Grobner

/- ---------------------------------------------------------------------- -/
/- Self-checking helper for the pure `Except`-valued algorithm: compare    -/
/- the `repr` of the actual result (spaces stripped) against `expected`    -/
/- (also space-stripped).  Prints `-> OK` or `-> MISMATCH got=...`.        -/
/- ---------------------------------------------------------------------- -/

private def pureCheck {α : Type} [Repr α] (lbl : String) (got : α)
    (expected : String) : IO Unit := do
  let g := ((reprStr got).replace " " "").replace "\n" ""
  let e := expected.replace " " ""
  if g == e then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={g}"

-- Two variables (x,y): monomial [a,b] = x^a * y^b.
private def px : poly := [(1, [1, 0])]              -- x
private def py : poly := [(1, [0, 1])]              -- y

/- ---------------------------------------------------------------------- -/
/- Polynomial arithmetic: add, sub, mul, neg on the two-variable monomials. -/
/- Canonical (descending-monomial) order places the lower-degree-first     -/
/- monomial as printed below; the values are the algorithm's actual output. -/
/- ---------------------------------------------------------------------- -/
#eval pureCheck "arith x+y" (grob_add px py)
  "Except.ok [(1, [0, 1]), (1, [1, 0])]"                 -- x + y
#eval pureCheck "arith x-y" (grob_sub px py)
  "Except.ok [(-1, [0, 1]), (1, [1, 0])]"                -- x - y
#eval pureCheck "arith x*y" (grob_mul px py)
  "Except.ok [(1, [1, 1])]"                              -- x*y
#eval pureCheck "arith (x+y)^2" (do grob_mul (← grob_add px py) (← grob_add px py))
  "Except.ok [(1, [0, 2]), (2, [1, 1]), (1, [2, 0])]"    -- x^2 + 2xy + y^2
#eval pureCheck "arith neg x" (grob_neg px)
  "[(-1, [1, 0])]"                                       -- -x
#eval pureCheck "arith x-x" (grob_sub px px)
  "Except.ok []"                                         -- cancels to 0

/- ---------------------------------------------------------------------- -/
/- `monic`: the history multiplier is the RECIPROCAL of the leading        -/
/- coefficient with ZEROED exponents.  Leading monomial here is `(2,[1,0])` -/
/- so the multiplier is `Mmul (1/2, [0,0]) hist` and the polynomial is      -/
/- scaled by 1/2.                                                          -/
/- ---------------------------------------------------------------------- -/
#eval pureCheck "monic 2x+y" (monic ([(2, [1, 0]), (1, [0, 1])], history.Start 0))
  "Except.ok ([(1, [1, 0]), ((1 : Rat)/2, [0, 1])], HolMath.Grobner.history.Mmul ((1 : Rat)/2, [0, 0]) (HolMath.Grobner.history.Start 0))"

/- ---------------------------------------------------------------------- -/
/- `grobner_refute` on an INCONSISTENT system, one variable x.  Equations  -/
/- `x = 0` and `x = 1` grobify to the polynomials `x` and `x - 1`; their    -/
/- ideal contains 1, so the system is inconsistent.  `resolve_proof`        -/
/- produces the certificate `[(0, [(1,[0])]), (1, [(-1,[0])])]`: multiplier -/
/- `1` on generator 0 (x) and `-1` on generator 1 (x-1).  Verified by hand: -/
/-   1*(x) + (-1)*(x - 1) = x - x + 1 = 1,                                  -/
/- the constant 1 - exactly the Nullstellensatz witness of contradiction.  -/
/- `resolve_proof` takes `vars : List term` (only its LENGTH matters); pass -/
/- one real term for the single variable x.                                -/
/- ---------------------------------------------------------------------- -/
private def one_var : List term := [(.Var "x" (.Tyvar "A") : term)]
private def gx : poly := [(1, [1])]                     -- x
private def gxm1 : poly := [(1, [1]), (-1, [0])]        -- x - 1

#eval (do
  let h ← grobner_refute [gx, gxm1]
  match resolve_proof one_var h with
  | .ok cert => pureCheck "refute cert" cert "[(0, [(1, [0])]), (1, [(-1, [0])])]"
  | .error e => IO.println s!"refute cert -> MISMATCH got=err {e}").run

/- ---------------------------------------------------------------------- -/
/- `grobner_ideal` POSITIVE: x IS in the ideal <x>.  Cofactor certificate  -/
/- `[(0, [(1,[0])])]` = multiplier 1 on generator 0: 1*x = x.              -/
/- ---------------------------------------------------------------------- -/
#eval (do
  match ← Session.grobner_ideal one_var [gx] gx with
  | .ok cert => pureCheck "ideal in" cert "[(0, [(1, [0])])]"
  | .error e => IO.println s!"ideal in -> MISMATCH got=err {e}")

/- ---------------------------------------------------------------------- -/
/- `grobner_ideal` NEGATIVE: 1 is NOT in the ideal <x>.  Must return the    -/
/- exact error `"grobner_ideal: not in the ideal"`.                        -/
/- ---------------------------------------------------------------------- -/
#eval (do
  match ← Session.grobner_ideal one_var [gx] [(1, [0])] with
  | .ok _ => IO.println "ideal out -> MISMATCH got=proved (SOUNDNESS BUG)"
  | .error e =>
    if e == "grobner_ideal: not in the ideal" then IO.println "ideal out -> OK"
    else IO.println s!"ideal out -> MISMATCH got=err {e}")

/- ====================================================================== -/
/- LAYER 2: `NUM_RING` END TO END on real ring identities over `num`.      -/
/- THE DECISIVE TEST - validates that Groebner certificates get turned      -/
/- into SOUND theorems.  `grobner_basis` prints "N basis elements and M     -/
/- critical pairs"; `execute_proof`/`REFUTE` print "Generating HOL version  -/
/- of proof" / "Translating certificate to HOL inferences".  That noise is  -/
/- filtered by the grep in the verification command.                       -/
/- ====================================================================== -/

/- ---------------------------------------------------------------------- -/
/- Self-checking helper: prove `expr` with `NUM_RING`; compare the printed  -/
/- conclusion (spaces stripped) against `expected` (also space-stripped).   -/
/- Prints `-> OK` or `-> MISMATCH got=...`.  A bare `|-  = ` (empty side)    -/
/- would signal a panicked bundle - every expected below carries a concrete -/
/- statement, so its absence confirms the wiring is real.                   -/
/- ---------------------------------------------------------------------- -/

private unsafe def ringCheck (lbl expr expected : String) : IO Unit := do
  match ← HolCore.Parser.parse_term expr with
  | .error e => IO.println s!"{lbl} parse ERR: {e}"
  | .ok tm =>
    match ← Session.NUM_RING tm with
    | .error e => IO.println s!"{lbl} FAIL: {e}"
    | .ok th =>
      let got := ((← HolCore.Printer.string_of_thm th).replace "\n" "").replace " " ""
      let exp := ("|-" ++ expected).replace " " ""
      if got == exp then IO.println s!"{lbl} -> OK"
      else IO.println s!"{lbl} -> MISMATCH got={got}"

/- ---------------------------------------------------------------------- -/
/- Self-checking helper for a NON-identity: `NUM_RING` MUST fail (return an -/
/- error) rather than "prove" it.  A success here is a SOUNDNESS BUG and is -/
/- reported loudly.                                                        -/
/- ---------------------------------------------------------------------- -/

private unsafe def ringMustFail (lbl expr : String) : IO Unit := do
  match ← HolCore.Parser.parse_term expr with
  | .error e => IO.println s!"{lbl} parse ERR: {e}"
  | .ok tm =>
    match ← Session.NUM_RING tm with
    | .error _ => IO.println s!"{lbl} -> OK (correctly failed)"
    | .ok th =>
      IO.println s!"{lbl} -> SOUNDNESS BUG: proved {← HolCore.Printer.string_of_thm th}"

/- ---------------------------------------------------------------------- -/
/- Binomial square, two ways: via EXP and via explicit product.            -/
/- ---------------------------------------------------------------------- -/
#eval ringCheck "sq (x+y)^2" "(x + y) EXP 2 = x EXP 2 + 2 * x * y + y EXP 2"
  "(x + y) EXP 2 = x EXP 2 + 2 * x * y + y EXP 2"
#eval ringCheck "prod (x+y)(x+y)" "(x + y) * (x + y) = x EXP 2 + 2 * x * y + y EXP 2"
  "(x + y) * (x + y) = x EXP 2 + 2 * x * y + y EXP 2"

/- ---------------------------------------------------------------------- -/
/- Trinomial square (three variables).                                    -/
/- ---------------------------------------------------------------------- -/
#eval ringCheck "sq3 (x+y+z)^2"
  "(x + y + z) EXP 2 = x EXP 2 + y EXP 2 + z EXP 2 + 2 * x * y + 2 * x * z + 2 * y * z"
  "(x + y + z) EXP 2 = x EXP 2 + y EXP 2 + z EXP 2 + 2 * x * y + 2 * x * z + 2 * y * z"

/- ---------------------------------------------------------------------- -/
/- A cancellation identity (uses the integral-domain cancellation law).    -/
/- ---------------------------------------------------------------------- -/
#eval ringCheck "cancel x+z=y+z" "(x + z = y + z) <=> (x = y)"
  "x + z = y + z <=> x = y"

/- ---------------------------------------------------------------------- -/
/- Factoring identity.                                                    -/
/- ---------------------------------------------------------------------- -/
#eval ringCheck "factor (x+1)(x+2)" "(x + 1) * (x + 2) = x EXP 2 + 3 * x + 2"
  "(x + 1) * (x + 2) = x EXP 2 + 3 * x + 2"

/- ---------------------------------------------------------------------- -/
/- NOT a ring identity: `x + y = x * y` is false in general.  `NUM_RING`   -/
/- MUST fail rather than "prove" it.                                       -/
/- ---------------------------------------------------------------------- -/
#eval ringMustFail "nonid x+y=x*y" "x + y = x * y"
