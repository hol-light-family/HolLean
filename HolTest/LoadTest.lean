/- File: HolTest/LoadTest.lean
Importing Session runs the whole HOL Light load sequence, as hol_lib.ml does.
This module imports it, so a layer that fails during that sequence is
reported by the build, and checks a few results.
Lean4 translation by Chris Walton 2026 -/

import HolTest.CommonTest
import Session

open HolCore.Kernel Session HolTest.CommonTest

-- One theorem from each end of the load sequence, and the arithmetic
-- decision procedures in their final (int.ml / calc_rat.ml) versions.  ONE
-- `#eval`: output printed while Session loads (e.g. grobner.ml's unconditional
-- "N basis elements and M critical pairs") is shown again with every `#eval`
-- of the module, so a single one shows it once.
#eval (do
  stmtOK "Load: WF (wf.ml)" WF
    "!(<<). WF(<<) <=> !P:A->bool. (?x. P(x)) ==> (?x. P(x) /\\ !y. y << x ==> ~P(y))"
  -- The load ends with iterate.ml's `prioritize_num`, so annotate `:real`.
  stmtOK "Load: REAL_INTEGRAL (calc_rat.ml 491)" REAL_INTEGRAL
    ("(!x:real. &0 * x = &0) /\\ (!x y z:real. (x + y = x + z) <=> (y = z)) /\\ " ++
     "(!w x y z:real. (w * y + x * z = w * z + x * y) <=> (w = x) \\/ (y = z))")
  ruleOK "Load: ARITH_RULE" (ARITH_RULE ([[ !m n. m + n = n + m ]])) "!m n. m + n = n + m"
  ruleOK "Load: REAL_ARITH" (REAL_ARITH3 ([[ !x y:real. abs(x + y) <= abs x + abs y ]]))
    "!x y:real. abs(x + y) <= abs x + abs y"
  : IO Unit)

-- After the whole load, untyped terms are typed as in HOL Light: overloaded
-- operators default to `num` (iterate.ml 3112), and `&`/`abs`/`max` give
-- `real` (iterate.ml 1982's prioritize_real puts real ahead of int).  The
-- reduction nets of calc_num.ml, calc_int.ml and calc_rat.ml are built from
-- untyped patterns when those files load, so they key on the types HOL
-- Light's do.  Expected results are from real HOL Light.
#eval (do
  for (s, want) in [("x + &0", "real"), ("abs (x + y)", "real"), ("max x y", "real"),
                    ("x + y", "num"), ("&2 + &3", "real")] do
    match ← HolCore.Parser.parse_term s with
    | .ok t =>
      let got ← HolCore.Printer.string_of_type (type_of t)
      IO.println (if got == want then s!"Load: `{s}` : {want} (as HOL Light) -> OK"
                  else s!"Load: `{s}` -> MISMATCH type {got}, want {want}")
    | .error e => IO.println s!"Load: `{s}` -> MISMATCH {e}"
  for (lbl, conv, s, want) in
      [("REAL_INT_REDUCE_CONV", REAL_INT_REDUCE_CONV, "(&2 + &3) * &4", "|- (&2 + &3) * &4 = &20"),
       ("REAL_RAT_REDUCE_CONV", REAL_RAT_REDUCE_CONV, "&1 / &2 + &1 / &3", "|- &1 / &2 + &1 / &3 = &5 / &6"),
       ("NUM_REDUCE_CONV", NUM_REDUCE_CONV, "2 + 2 * 3", "|- 2 + 2 * 3 = 8")] do
    match ← HolCore.Parser.parse_term s with
    | .error e => IO.println s!"Load: {lbl} -> MISMATCH {e}"
    | .ok t =>
      match ← conv t with
      | .ok th =>
        let got ← HolCore.Printer.string_of_thm th
        IO.println (if got == want then s!"Load: {lbl} `{s}` -> OK" else s!"Load: {lbl} -> MISMATCH {got}")
      | .error e => IO.println s!"Load: {lbl} -> MISMATCH {e}"
  : IO Unit)
