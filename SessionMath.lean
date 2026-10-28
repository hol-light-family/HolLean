/- File: SessionMath.lean
The session state of HOL Light's mathematical theories, pair.ml to define.ml:
one module per HolMath file with load-time state, in hol_lib.ml order, after
SessionCore.  Each module builds its file's layers by `initialize` when it is
imported; the chain is linear, so importing the last module loads them all.
Lean4 translation by Chris Walton 2026
-/
import SessionMath.Define
