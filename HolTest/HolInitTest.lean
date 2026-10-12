/- File: HolTest/HolInitTest.lean
Importing HolInit runs the whole HOL Light load sequence, as hol_lib.ml does.
This module imports it, so a layer that fails during that sequence is reported
by the build (`make verify` gates on `PANIC`), and checks a few results.
Lean4 translation by Chris Walton 2026 -/

-- CommonTest first: its quiet-output initializer then runs before HolInit's
-- load sequence (imports initialise in order).
import HolTest.CommonTest
import HolInit

open HolCore.Kernel Session HolTest.CommonTest

-- One theorem from each end of the load sequence, and the arithmetic
-- decision procedures in their final (int.ml / calc_rat.ml) versions.  ONE
-- `#eval`: output printed while HolInit loads (e.g. grobner.ml's unconditional
-- "N basis elements and M critical pairs") is shown again with every `#eval`
-- of the module, so a single one shows it once.
#eval (do
  stmtOK "HolInit: WF (wf.ml)" WF
    "!(<<). WF(<<) <=> !P:A->bool. (?x. P(x)) ==> (?x. P(x) /\\ !y. y << x ==> ~P(y))"
  -- HolInit ends with int.ml's `prioritize_num`, so annotate `:real`.
  stmtOK "HolInit: REAL_INTEGRAL (calc_rat.ml 491)" REAL_INTEGRAL
    ("(!x:real. &0 * x = &0) /\\ (!x y z:real. (x + y = x + z) <=> (y = z)) /\\ " ++
     "(!w x y z:real. (w * y + x * z = w * z + x * y) <=> (w = x) \\/ (y = z))")
  ruleOK "HolInit: ARITH_RULE" (ARITH_RULE ([[ !m n. m + n = n + m ]])) "!m n. m + n = n + m"
  ruleOK "HolInit: REAL_ARITH" (REAL_ARITH3 ([[ !x y:real. abs(x + y) <= abs x + abs y ]]))
    "!x y:real. abs(x + y) <= abs x + abs y"
  : IO Unit)

-- After the whole load, untyped terms are typed as in HOL Light: overloaded
-- operators default to `num` (iterate.ml 3112), and `&`/`abs`/`max` give
-- `real` (iterate.ml 1982's prioritize_real puts real ahead of int).  HolInit
-- used to stop at sets.ml, leaving int.ml's priorities, so these were `int`.
-- The reduction nets of calc_num.ml, calc_int.ml and calc_rat.ml are built
-- from untyped patterns when those files load; built later (on first use)
-- they keyed on the wrong types and never fired.  Expected results are from
-- real HOL Light.
#eval (do
  for (s, want) in [("x + &0", "real"), ("abs (x + y)", "real"), ("max x y", "real"),
                    ("x + y", "num"), ("&2 + &3", "real")] do
    match ← HolCore.Parser.parse_term s with
    | .ok t =>
      let got ← HolCore.Printer.string_of_type (type_of t)
      IO.println (if got == want then s!"HolInit: `{s}` : {want} (as HOL Light) -> OK"
                  else s!"HolInit: `{s}` -> MISMATCH type {got}, want {want}")
    | .error e => IO.println s!"HolInit: `{s}` -> MISMATCH {e}"
  for (lbl, conv, s, want) in
      [("REAL_INT_REDUCE_CONV", REAL_INT_REDUCE_CONV, "(&2 + &3) * &4", "|- (&2 + &3) * &4 = &20"),
       ("REAL_RAT_REDUCE_CONV", REAL_RAT_REDUCE_CONV, "&1 / &2 + &1 / &3", "|- &1 / &2 + &1 / &3 = &5 / &6"),
       ("NUM_REDUCE_CONV", NUM_REDUCE_CONV, "2 + 2 * 3", "|- 2 + 2 * 3 = 8")] do
    match ← HolCore.Parser.parse_term s with
    | .error e => IO.println s!"HolInit: {lbl} -> MISMATCH {e}"
    | .ok t =>
      match ← conv t with
      | .ok th =>
        let got ← HolCore.Printer.string_of_thm th
        IO.println (if got == want then s!"HolInit: {lbl} `{s}` -> OK" else s!"HolInit: {lbl} -> MISMATCH {got}")
      | .error e => IO.println s!"HolInit: {lbl} -> MISMATCH {e}"
  : IO Unit)
