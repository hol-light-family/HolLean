/- File: SessionCore.lean
The session state of HOL Light's core, bool.ml to impconv.ml: one module per
HolCore file with load-time state, in hol_lib.ml order (SessionCore/Base.lean
first).  Each module builds its file's layers by `initialize` when it is
imported; the chain is linear, so importing the last module loads them all.
Lean4 translation by Chris Walton 2026
-/
import SessionCore.ImpConv
