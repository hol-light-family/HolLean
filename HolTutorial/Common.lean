/- File: HolTutorial/Common.lean
The prelude shared by the translations of HOL Light's Tutorial/ files.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Each tutorial file is a HOL Light toplevel session.  Its translation is
written as a user would write it in Prove.lean (`#eval`, `[[...]]`), one
toplevel phrase after another, in the same order.  Each phrase is preceded
by `#eval phrase k`, which prints the `@@P k` marker that
tools/tutorialdiff uses to compare its output with HOL Light's.

OCaml's `let x = e;;` evaluates `e` once, there and then.  A Lean
`def x := e` is evaluated again at every use (so a `new_definition`
would run twice), so a toplevel `let` is written

    def x : thm := keep "x" fun _ => e
    #eval x

`keep` evaluates `e` at its first use and caches the value under its name;
the `#eval x` straight after it makes that first use the `let` itself, and
prints the value as HOL Light's toplevel does (`val x : thm = ...`).
-/

import Session
import Help
import HolToplevel

open HolCore.Kernel

namespace HolTutorial

/- The toplevel helpers (HolToplevel.lean), under this namespace. -/
export HolToplevel (keepPut keepGet runIO runBaseIO)

/-- `keep name f`: the value of `f ()`, computed at the first use with this
    `name` and cached (OCaml's `let name = ...;;`, evaluated once).  Written
    `keep "x" fun _ => e`. -/
scoped syntax "keep " term:max ppSpace term : term
scoped macro_rules
  | `(keep $n fun _ => $e) =>
    `(HolToplevel.keepBoxed (HolToplevel.keyOf decl_name% $n) (fun _ => ⟨$e, ()⟩))
  | `(keep $n $f) =>
    `(HolToplevel.keepBoxed (HolToplevel.keyOf decl_name% $n) (fun u => ⟨$f u, ()⟩))

/-- Print a failure as HOL Light's toplevel reports an uncaught `Failure`:
    `Exception: Failure "msg".` -/
def failure (msg : String) : IO Unit := IO.println s!"Exception: Failure \"{msg}\"."

/-- Run `x`; print its value with `show`, or its failure as HOL Light does. -/
def try_ {α : Type} (x : IO (Except String α)) (pr : α → IO String) : IO Unit := do
  match ← x with
  | .ok v => IO.println (← pr v)
  | .error m => failure m

/-- The marker for toplevel phrase `k` (see tools/tutorialdiff). -/
def phrase (k : Nat) : IO Unit := IO.println s!"\n@@P {k}"

end HolTutorial
