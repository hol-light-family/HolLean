/- File: Session.lean
A HOL Light-style session.  Importing this module loads the whole core
system, as hol.ml's `loads "hol_lib.ml"` does: every file of hol_lib.ml runs
when its module is imported, in hol_lib.ml's order, so that afterwards the
types, constants, parser fixities and theorems all exist.

The session state is in two libraries that mirror the pure ones: SessionCore
(one module per HolCore file with load-time state, bool.ml to impconv.ml)
and SessionMath (one per HolMath file, pair.ml to define.ml).  Each layer is
an `initialize` constant, and the rules, tactics and theorems over them are
ordinary (safe) definitions in namespace `Session`, so a file that imports
Session needs no `unsafe` code.

SessionCore/Base.lean also provides the `[[ ... ]]` term quotations, the
coercions that let rule results and quotations compose without `do`, and
`Repr` instances so `#eval` prints values as the OCaml toplevel does.

Lean4 translation by Chris Walton 2026
-/
import SessionCore
import SessionMath
