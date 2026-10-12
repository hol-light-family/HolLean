/- File: Prove.lean
A scratchpad for users of HolLean: put your own `#eval`s here.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

`import HolInit` starts the system the way `hol.ml` does: HOL Light's
`loads "hol_lib.ml"` runs every source file in dependency order, so by the time
you get a prompt all the types, constants, parser fixities and theorems exist.
HolInit reproduces that with an `initialize` block, Lean's analogue of `loads`.

So write what you would write in HOL Light.  Terms go in `[[ ... ]]`, which is
this translation's stand-in for HOL Light's backquotes, and results print
themselves:

    HOL Light   REAL_ARITH `!x y. abs(x + y) <= abs x + abs y`;;
    here        #eval REAL_ARITH2 [[!x y. abs (x + y) <= abs x + abs y]]

Nothing needs forcing and no `do`/`match` wrapper is needed - the coercions in
Session.lean unwrap a quotation into a `term` and a rule result into a `thm`,
and failures panic with HOL Light's own error text.

To keep a result, as HOL Light's `let th = NUM_REDUCE_CONV `2 + 2 * 3`;;`,
define it; later commands can then use the name:

    unsafe def th : thm := NUM_REDUCE_CONV [[2 + 2 * 3]]
    #eval th

ONE SYNTAX WRINKLE: parenthesise a quotation when it is NOT the last argument.
`prove ([[...]]) tac` works; `prove [[...]] tac` does not parse.

Interactive proofs use HOL Light's subgoal package; each command's result
prints as the goalstack, as in HOL Light:

    #eval g ([[x + 1 = 1 + x /\ 1 + 1 = 2]])
    #eval e CONJ_TAC
    #eval er ALL_TAC               -- also b, r n, p, flush_goalstack, top_thm

HOL Light's online help is available as `#eval help("NAME")` (help.ml),
e.g. `#eval help("REAL_ARITH")`; an unknown name lists the closest entries.

HolInit brings in HolCore, HolMath and Session, but NOT the test suite, so you
do not re-run the project's test assertions.  This file belongs to no Lake
target and nothing imports it, so whatever you write here cannot break
`make build`, `make proofs` or `make check`.  Run it with

    make prove                      -- or: lake env lean Prove.lean
-/

import HolInit
import Help

open Session HolCore.Kernel

/- ---------------------------------------------------------------------- -/
/- Worked examples.  Delete these and write your own.                     -/
/- ---------------------------------------------------------------------- -/

-- HOL Light's documentation for a function or theorem.
#eval help("REAL_ARITH")

-- Parse a term.
#eval [[!x y. abs (x + y) <= abs x + abs y]]

-- Look at a theorem.
#eval REAL_ADD_SYM
#eval REAL_ADD_AC

-- Prove a goal with the linear real decision procedure (realarith.ml).
-- `REAL_ARITH2` is the version that file leaves in place: it handles abs, max
-- and min, and INTEGER constants.  Rational constants such as `/ &2` are
-- handled by calc_rat.ml's `REAL_ARITH3`.
#eval REAL_ARITH2 [[!x y. abs (x + y) <= abs x + abs y]]
-- Without `:real` the variables would be natural numbers (the default after
-- loading, as in HOL Light), and REAL_ARITH would fail.
#eval REAL_ARITH2 [[!x y z:real. x <= y /\ y <= z ==> x <= z]]
#eval REAL_ARITH2 [[!x y. max x y >= x]]

-- Evaluate arithmetic.
#eval NUM_REDUCE_CONV [[2 + 2 * 3]]
#eval REAL_INT_REDUCE_CONV [[(&2 + &3) * &4]]

-- Prove a goal with a tactic script of your own.
#eval prove ([[!x. x + &0 = x]]) (REWRITE_TAC [REAL_ADD_RID])

-- Keep a result under a name, as HOL Light's `let th = ...;;`.
unsafe def th : thm := NUM_REDUCE_CONV [[2 + 2 * 3]]
#eval th
#eval concl th

/- ---------------------------------------------------------------------- -/
/- Your work below.                                                       -/
/- ---------------------------------------------------------------------- -/
