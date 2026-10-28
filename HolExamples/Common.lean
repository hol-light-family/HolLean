/- File: HolExamples/Common.lean
The prelude shared by the translations of HOL Light's Examples/ files.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Each Examples file is a HOL Light toplevel session.  Its translation is
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
import Std.Data.HashSet

open HolCore.Kernel

namespace HolExamples

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

/- Loading a file again.  A file loaded by `needs` from a later one (Logic/ loads reduct.ml and
   multiwf.ml) supplies its definitions, types, parser settings and theorems,
   so each module ends with `ensure`, which replays all its phrases, in
   order and once per process (as HOL Light's `loadt` runs a file), after
   the `ensure` of what it loads first.  `ensure` is maintained by hand:
   when a module's `#eval`s change, update its `ensure` to match. -/

initialize onceCell : IO.Ref (Std.HashSet String) ← IO.mkRef {}

/-- Run `act` the first time `once name` is called in this process. -/
def once (name : String) (act : IO Unit) : IO Unit := do
  if (← onceCell.get).contains name then return
  onceCell.modify (·.insert name)
  act

/-- How a replayed phrase is run: an IO action is run and its value
    discarded; any other value is evaluated (a `keep` value is computed and
    cached). -/
class Replay (α : Type) where
  replay : α → IO Unit

instance {α : Type} : Replay (IO α) := ⟨fun act => do let _ ← act⟩

@[noinline] def forceValue {α : Type} (x : α) : IO Unit := do
  let _ ← IO.mkRef x

instance {ε α : Type} : Replay (ExceptT ε IO α) := ⟨fun act => do let _ ← act.run⟩

instance (priority := low) {α : Type} : Replay α := ⟨forceValue⟩

export Replay (replay)

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

end HolExamples
