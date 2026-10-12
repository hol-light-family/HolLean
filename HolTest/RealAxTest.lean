/- File: HolTest/RealAxTest.lean
Runtime test suite: realax.ml - the construction of the real numbers.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set.

WHAT THIS FILE IS FOR.  realax.ml builds `:real` in three layered stages, each
introducing a type:
  1. `nadd`  - a BASIC type definition: the "nearly additive" functions
               `num->num` satisfying `is_nadd`.
  2. `hreal` - `nadd` quotiented by `===`, the non-negative reals.
  3. `real`  - `hreal#hreal` quotiented by `treal_eq`, the reals.
The checks below confirm all three types exist, that the ordered-field axioms
and the SUPREMUM property hold at the `real` level, and - separately - that
loading this layer has not disturbed the parser for everything built before it.

THE PARSER-STATE CHECKS ARE THE POINT OF THE SECOND HALF OF THIS FILE.
realax.ml mutates global parser state in three ways, and each is measured here
rather than assumed:
  * its head makes `+ - * / < <= > >= -- pow inv abs max min &` OVERLOADABLE
    and then calls `prioritize_num()`, so `num` must remain the DEFAULT for a
    bare `1 + 2` even though `:real` now also claims `+`;
  * its tail runs fifteen `overload_interface` calls for the real operations,
    so `&2 + &3` must come out at type `:real`;
  * its tail also runs `reduce_interface`/`remove_interface`, RETIRING the
    working notations `** ++ <<= === fn afn`.  After that, `remove_interface`
    has dropped their interface MAPPINGS - so they no longer denote
    `nadd_mul`/`nadd_add`/... - while `parse_as_infix` still makes `===` etc.
    parse syntactically.  The faithful outcome is therefore that they parse as
    FREE VARIABLES, which is what the checks assert. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- FORCING THE REALAX LAYER FIRST IS MANDATORY.                           -/
/-                                                                        -/
/- The realax bootstrap is LAZY: importing `Session` does NOT run it, so   -/
/- the `real` type and the overload declarations do not exist until        -/
/- something reads a realax accessor.  Measured in a bare `import Session` -/
/- process, BEFORE any force:                                             -/
/-   `1 + 2`  -> PARSE FAILED: mk_type: type num has not been defined      -/
/- Reading `REAL_COMPLETE` drives the whole ten-stage chain in realax.ml's -/
/- own order, so this `#eval` must come first in the file.                 -/
/- ---------------------------------------------------------------------- -/

#eval Session.REAL_COMPLETE

/- ---------------------------------------------------------------------- -/
/- WHY SOME EXPECTATIONS BELOW USE FULL CONSTANT NAMES - DO NOT "TIDY".    -/
/-                                                                        -/
/- realax.ml's closing cleanup (1968-1973) runs                            -/
/-   reduce_interface  for "+" "*" "<=" "inv"  at :hreal, and              -/
/-   remove_interface  for "**" "++" "<<=" "===" "fn" "afn",               -/
/- so those symbols STOP denoting the nadd/hreal constants.  Every theorem -/
/- in this file is printed AFTER that cleanup has run, so any theorem that -/
/- MENTIONS one of those constants prints it under its full name.  Hence   -/
/- the expectations read `dest_nadd x n` not `fn x n`, `nadd_le x M` not   -/
/- `x <<= M`, and `hreal_mul x (hreal_add y z)` not `x * (y + z)`.         -/
/- That is HOL Light's own behaviour, not a translation artefact: the same -/
/- printing would be seen in OCaml after loading realax.ml.                -/
/-                                                                        -/
/- `&` is the exception and DOES still print, for both `hreal_of_num` and  -/
/- `real_of_num`: realax.ml `reduce_interface`s "+", "*", "<=" and "inv"   -/
/- but never "&", and the two `&` mappings are distinguished by type.      -/
/-                                                                        -/
/- My first draft of this file expected `fn`/`<<=`/`*` throughout and got  -/
/- 13 mismatches.  Each one was this effect, which I had already predicted -/
/- when translating the cleanup - so the expectations were corrected, not  -/
/- the code.  If a future change makes these print as `fn`/`<<=` again,    -/
/- that means the cleanup has stopped running and IS a real defect.        -/
/- ---------------------------------------------------------------------- -/

/-- Squash whitespace so a printed theorem can be compared against a
    single-line expected string. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

/-- Compare a theorem against an expected printed form. -/
private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/-- Parse a term and compare BOTH its printed form and its type.  Used for the
    parser-state checks, where the TYPE is the whole point. -/
private unsafe def parseCheck (lbl expr expTm expTy : String) : IO Unit := do
  match ← HolCore.Parser.parse_term expr with
  | .error e => IO.println s!"{lbl} -> PARSE FAILED: {e}"
  | .ok tm =>
    let gotTm := squash (← HolCore.Printer.string_of_term tm)
    let gotTy := squash (← HolCore.Printer.string_of_type (type_of tm))
    if gotTm == squash expTm && gotTy == squash expTy then
      IO.println s!"{lbl} -> OK"
    else IO.println s!"{lbl} -> MISMATCH got={gotTm} : {gotTy}"

/-- Confirm a type name exists by building it. -/
private unsafe def tyCheck (lbl name : String) : IO Unit := do
  match ← (mk_type name [] : IO (Except String hol_type)) with
  | .error e => IO.println s!"{lbl} -> MISSING: {e}"
  | .ok ty =>
    let s ← HolCore.Printer.string_of_type ty
    if s == name then IO.println s!"{lbl} -> OK" else
      IO.println s!"{lbl} -> MISMATCH got={s}"

/-- Assert that a term parses but its head is a free VARIABLE rather than a
    constant.  This is the shape realax.ml's closing `remove_interface` leaves
    the retired working notations in. -/
private unsafe def freeVarCheck (lbl expr : String) : IO Unit := do
  match ← HolCore.Parser.parse_term expr with
  | .error _ => IO.println s!"{lbl} -> OK (no longer parses)"
  | .ok tm =>
    if (frees tm).isEmpty then
      IO.println s!"{lbl} -> MISMATCH still a constant"
    else IO.println s!"{lbl} -> OK (free variable, interface retired)"

/- ---------------------------------------------------------------------- -/
/- The three type constructions (realax.ml 260, 1257, 1712).              -/
/- ---------------------------------------------------------------------- -/

#eval tyCheck "type nadd" "nadd"
#eval tyCheck "type hreal" "hreal"
#eval tyCheck "type real" "real"

/- ---------------------------------------------------------------------- -/
/- Stage 1: `nadd`, the nearly additive functions (realax.ml 253-1179).   -/
/- Statements checked against realax.ml itself.                           -/
/- ---------------------------------------------------------------------- -/

#eval thmCheck "dist" distThms.dist "|- forall n m. dist (m,n) = m - n + n - m"
#eval thmCheck "DIST_TRIANGLE" distThms.DIST_TRIANGLE
  "|- forall m n p. dist (m,p) <= dist (m,n) + dist (n,p)"
#eval thmCheck "is_nadd" naddThms.is_nadd
  "|- forall x. is_nadd x <=> (exists B. forall m n. dist (m * x n,n * x m) <= B * (m + n))"
#eval thmCheck "nadd_abs" naddThms.nadd_abs "|- mk_nadd (dest_nadd a) = a"
#eval thmCheck "nadd_rep" naddThms.nadd_rep "|- is_nadd r <=> dest_nadd (mk_nadd r) = r"
#eval thmCheck "NADD_CAUCHY" naddThms.NADD_CAUCHY
  "|- forall x. exists B. forall m n. dist (m * dest_nadd x n,n * dest_nadd x m) <= B * (m + n)"

/- `NADD_COMPLETE` (realax.ml 823) - completeness of the `nadd` ordering, and
    the ~105-line proof this whole layer exists to support. -/
#eval thmCheck "NADD_COMPLETE" naddCompleteThms.NADD_COMPLETE
  "|- forall P. (exists x. P x) /\\ (exists M. forall x. P x ==> nadd_le x M) ==> (exists M. (forall x. P x ==> nadd_le x M) /\\ (forall M'. (forall x. P x ==> nadd_le x M') ==> nadd_le M M'))"

/- `nadd_rinv` (realax.ml 976): the auxiliary for the multiplicative inverse. -/
#eval thmCheck "nadd_rinv" naddInvAuxThms.nadd_rinv
  "|- forall x. nadd_rinv x = (\\n. (n * n) DIV dest_nadd x n)"

/- ---------------------------------------------------------------------- -/
/- Stage 2: `hreal`, the non-negative reals (realax.ml 1257-1381).         -/
/-                                                                        -/
/- The LIFTED statements are the evidence the quotient really worked: on   -/
/- `hreal` the equivalence `===` has become genuine EQUALITY and the       -/
/- operations carry the ordinary overloaded symbols, where the `nadd`      -/
/- level had `=== <<= ++ **`.                                             -/
/-                                                                        -/
/- NOTE `hreal_le` prints under its CONSTANT NAME rather than as `<=`.     -/
/- That is faithful: realax.ml's closing `reduce_interface "<=" hreal_le`  -/
/- retires that mapping, and these theorems are printed after it has run.  -/
/- ---------------------------------------------------------------------- -/

#eval thmCheck "HREAL_OF_NUM_EQ" hrealThms.HREAL_OF_NUM_EQ "|- forall m n. &m = &n <=> m = n"
#eval thmCheck "HREAL_ADD_LDISTRIB" hrealThms.HREAL_ADD_LDISTRIB
  "|- forall x y z. hreal_mul x (hreal_add y z) = hreal_add (hreal_mul x y) (hreal_mul x z)"
#eval thmCheck "HREAL_MUL_LINV" hrealThms.HREAL_MUL_LINV
  "|- forall x. ~(x = &0) ==> hreal_mul (hreal_inv x) x = &1"
#eval thmCheck "HREAL_INV_0" hrealThms.HREAL_INV_0 "|- hreal_inv (&0) = &0"
#eval thmCheck "HREAL_LE_TOTAL" hrealThms.HREAL_LE_TOTAL
  "|- forall x y. hreal_le x y \\/ hreal_le y x"
#eval thmCheck "HREAL_COMPLETE" hrealThms.HREAL_COMPLETE
  "|- forall P. (exists x. P x) /\\ (exists M. forall x. P x ==> hreal_le x M) ==> (exists M. (forall x. P x ==> hreal_le x M) /\\ (forall M'. (forall x. P x ==> hreal_le x M') ==> hreal_le M M'))"

/- ---------------------------------------------------------------------- -/
/- Stage 3a: the signed-real representatives (realax.ml 1385-1708).        -/
/-                                                                        -/
/- All six operations plus `treal_eq` have PAIRED left-hand sides, so all  -/
/- seven are made with `new_definition_pair`.  `TREAL_ADD_LINV` is the     -/
/- mathematical point of this layer: signed reals have ADDITIVE INVERSES,  -/
/- which is exactly what `hreal` lacked.                                  -/
/- ---------------------------------------------------------------------- -/

#eval thmCheck "treal_add" trealThms.treal_add
  "|- forall x1 x2 y1 y2. (x1,y1) treal_add (x2,y2) = hreal_add x1 x2,hreal_add y1 y2"
#eval thmCheck "treal_eq" trealThms.treal_eq
  "|- forall x1 y2 x2 y1. x1,y1 treal_eq x2,y2 <=> hreal_add x1 y2 = hreal_add x2 y1"
#eval thmCheck "TREAL_ADD_LINV" trealThms.TREAL_ADD_LINV
  "|- forall x. treal_neg x treal_add x treal_eq treal_of_num 0"
#eval thmCheck "TREAL_MUL_LINV" trealThms.TREAL_MUL_LINV
  "|- forall x. ~(x treal_eq treal_of_num 0) ==> treal_inv x treal_mul x treal_eq treal_of_num 1"
#eval thmCheck "TREAL_INV_WELLDEF" trealThms.TREAL_INV_WELLDEF
  "|- forall x y. x treal_eq y ==> treal_inv x treal_eq treal_inv y"

/- ---------------------------------------------------------------------- -/
/- Stage 3b: `real` - THE ORDERED FIELD AXIOMS (realax.ml 1738).           -/
/-                                                                        -/
/- These twenty are lifted positionally from their `treal` counterparts.   -/
/- Everything here is in ORDINARY real notation, which is the evidence     -/
/- that no representative-level detail leaked through the quotient.        -/
/- ---------------------------------------------------------------------- -/

#eval thmCheck "REAL_ADD_SYM" realThms.REAL_ADD_SYM "|- forall x y. x + y = y + x"
#eval thmCheck "REAL_ADD_ASSOC" realThms.REAL_ADD_ASSOC
  "|- forall x y z. x + y + z = (x + y) + z"
#eval thmCheck "REAL_ADD_LID" realThms.REAL_ADD_LID "|- forall x. &0 + x = x"
#eval thmCheck "REAL_ADD_LINV" realThms.REAL_ADD_LINV "|- forall x. --x + x = &0"
#eval thmCheck "REAL_MUL_SYM" realThms.REAL_MUL_SYM "|- forall x y. x * y = y * x"
#eval thmCheck "REAL_MUL_ASSOC" realThms.REAL_MUL_ASSOC
  "|- forall x y z. x * y * z = (x * y) * z"
#eval thmCheck "REAL_MUL_LID" realThms.REAL_MUL_LID "|- forall x. &1 * x = x"
#eval thmCheck "REAL_ADD_LDISTRIB" realThms.REAL_ADD_LDISTRIB
  "|- forall x y z. x * (y + z) = x * y + x * z"
#eval thmCheck "REAL_LE_REFL" realThms.REAL_LE_REFL "|- forall x. x <= x"
#eval thmCheck "REAL_LE_ANTISYM" realThms.REAL_LE_ANTISYM
  "|- forall x y. x <= y /\\ y <= x <=> x = y"
#eval thmCheck "REAL_LE_TRANS" realThms.REAL_LE_TRANS
  "|- forall x y z. x <= y /\\ y <= z ==> x <= z"
#eval thmCheck "REAL_LE_TOTAL" realThms.REAL_LE_TOTAL "|- forall x y. x <= y \\/ y <= x"
#eval thmCheck "REAL_LE_LADD_IMP" realThms.REAL_LE_LADD_IMP
  "|- forall x y z. y <= z ==> x + y <= x + z"
#eval thmCheck "REAL_LE_MUL" realThms.REAL_LE_MUL
  "|- forall x y. &0 <= x /\\ &0 <= y ==> &0 <= x * y"
#eval thmCheck "REAL_INV_0" realThms.REAL_INV_0 "|- inv (&0) = &0"
#eval thmCheck "REAL_MUL_LINV" realThms.REAL_MUL_LINV
  "|- forall x. ~(x = &0) ==> inv x * x = &1"

/- The injection of the naturals is a homomorphism for `= <= + *`. -/
#eval thmCheck "REAL_OF_NUM_EQ" realThms.REAL_OF_NUM_EQ "|- forall m n. &m = &n <=> m = n"
#eval thmCheck "REAL_OF_NUM_LE" realThms.REAL_OF_NUM_LE "|- forall m n. &m <= &n <=> m <= n"
#eval thmCheck "REAL_OF_NUM_ADD" realThms.REAL_OF_NUM_ADD "|- forall m n. &m + &n = &(m + n)"
#eval thmCheck "REAL_OF_NUM_MUL" realThms.REAL_OF_NUM_MUL "|- forall m n. &m * &n = &(m * n)"

/- ---------------------------------------------------------------------- -/
/- The additional definitions (realax.ml 1786-1807).                       -/
/- `real_pow` is the ONLY recursive definition in the whole file.          -/
/- ---------------------------------------------------------------------- -/

#eval thmCheck "real_sub" realThms.real_sub "|- forall x y. x - y = x + --y"
#eval thmCheck "real_lt" realThms.real_lt "|- forall y x. x < y <=> ~(y <= x)"
#eval thmCheck "real_ge" realThms.real_ge "|- forall y x. x >= y <=> y <= x"
#eval thmCheck "real_gt" realThms.real_gt "|- forall y x. x > y <=> y < x"
#eval thmCheck "real_abs" realThms.real_abs
  "|- forall x. abs x = (if &0 <= x then x else --x)"
#eval thmCheck "real_pow" realThms.real_pow
  "|- x pow 0 = &1 /\\ (forall n. x pow SUC n = x * x pow n)"
#eval thmCheck "real_div" realThms.real_div "|- forall x y. x / y = x * inv y"
#eval thmCheck "real_max" realThms.real_max
  "|- forall n m. max m n = (if m <= n then n else m)"
#eval thmCheck "real_min" realThms.real_min
  "|- forall m n. min m n = (if m <= n then m else n)"

/- ---------------------------------------------------------------------- -/
/- THE SUPREMUM PROPERTY (realax.ml 1907) - the goal of the whole file.    -/
/- ---------------------------------------------------------------------- -/

#eval thmCheck "REAL_COMPLETE" realThms.REAL_COMPLETE
  "|- forall P. (exists x. P x) /\\ (exists M. forall x. P x ==> x <= M) ==> (exists M. (forall x. P x ==> x <= M) /\\ (forall M'. (forall x. P x ==> x <= M') ==> M <= M'))"

#eval thmCheck "REAL_COMPLETE_SOMEPOS" realThms.REAL_COMPLETE_SOMEPOS
  "|- forall P. (exists x. P x /\\ &0 <= x) /\\ (exists M. forall x. P x ==> x <= M) ==> (exists M. (forall x. P x ==> x <= M) /\\ (forall M'. (forall x. P x ==> x <= M') ==> M <= M'))"

/- ---------------------------------------------------------------------- -/
/- PARSER STATE.  realax.ml's overloading must NOT have disturbed anything -/
/- built before it: `prioritize_num()` at realax.ml 48 keeps `num` the     -/
/- default, and realax.ml DEFINES but never CALLS `prioritize_real`, so    -/
/- `num` is still the default when the file finishes.  Measured, not       -/
/- assumed - these all run AFTER the layer has been forced above.          -/
/- ---------------------------------------------------------------------- -/

#eval parseCheck "parse 1 + 2 (still num)" "1 + 2" "1 + 2" "num"
#eval parseCheck "parse 2 * 3 <= 7 (still num)" "2 * 3 <= 7" "2 * 3 <= 7" "bool"
#eval parseCheck "parse x < y (still num)" "x < y" "x < y" "bool"
#eval parseCheck "parse SUC 0 (still num)" "SUC 0" "SUC 0" "num"

/- The real operations are reachable via `&`, at type `:real`. -/
#eval parseCheck "parse &2 + &3 (real)" "&2 + &3" "&2 + &3" "real"
#eval parseCheck "parse &1 / &2 (real)" "&1 / &2" "&1 / &2" "real"
#eval parseCheck "parse --(&3) (real)" "--(&3)" "--&3" "real"
#eval parseCheck "parse abs(&2) (real)" "abs(&2)" "abs (&2)" "real"
#eval parseCheck "parse &2 pow 3 (real)" "&2 pow 3" "&2 pow 3" "real"

/- ---------------------------------------------------------------------- -/
/- The retired working notations (realax.ml 1968-1973).  `remove_interface` -/
/- drops their interface MAPPINGS, so they no longer denote the nadd       -/
/- constants; `parse_as_infix` still lets `===` etc. parse, so the         -/
/- faithful outcome is a FREE VARIABLE rather than a parse error.          -/
/- ---------------------------------------------------------------------- -/

#eval freeVarCheck "=== retired" "x === y"
#eval freeVarCheck "<<= retired" "x <<= y"
#eval freeVarCheck "++ retired" "x ++ y"
#eval freeVarCheck "** retired" "x ** y"
#eval freeVarCheck "fn retired" "fn x n"
#eval freeVarCheck "afn retired" "afn x"
