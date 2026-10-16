/- File: HolTutorial/Common.lean
The prelude shared by the translations of HOL Light's Tutorial/ files.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Each tutorial file is a HOL Light toplevel session.  Its translation is
written as a user would write it in Prove.lean (`#eval`, `[[...]]`), one
toplevel phrase after another, in the same order.  Each phrase is preceded
by `#eval phrase k`, which prints the `@@P k` marker that
tools/tutorialdiff uses to compare its output with HOL Light's.

OCaml's `let x = e;;` evaluates `e` once, there and then.  A Lean
`unsafe def x := e` is evaluated again at every use (so a `new_definition`
would run twice), so a toplevel `let` is written

    unsafe def x : thm := keep "x" fun _ => e
    #eval x

`keep` evaluates `e` at its first use and caches the value under its name;
the `#eval x` straight after it makes that first use the `let` itself, and
prints the value as HOL Light's toplevel does (`val x : thm = ...`).
-/

import HolInit
import Help
import SessionLibrary
import Std.Data.HashMap

open HolCore.Kernel

namespace HolTutorial

/-- The core bundles, for the infix tactic syntax (`THEN`, `THENL`, ...). -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

initialize keepCell : IO.Ref (Std.HashMap String NonScalar) ← IO.mkRef {}

/-- `keep name f`: the value of `f ()`, computed at the first call with this
    `name` and cached (OCaml's `let name = ...;;`, evaluated once). -/
@[noinline] unsafe def keep {α : Type} (name : String) (f : Unit → α) : α :=
  match unsafeIO (do
    match (← keepCell.get).get? name with
    | some v => pure (unsafeCast v : α)
    | none =>
      let v := f ()
      keepCell.modify (·.insert name (unsafeCast v))
      pure v) with
  | .ok v => v
  | .error _ => f ()

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
