/- File: HolToplevel.lean
Helpers for writing a HOL Light toplevel session as a Lean file, as the
translations of HOL Light's tutorial, Examples/ and Logic/ files do
(HolTutorial, HolExamples, HolLogicArith; their Common.lean files build on
this module).  Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Each helper is a safe declaration whose compiled implementation is given by
`implemented_by`, as SessionCore/Base.lean's `runThm` is, so a file using them
needs no `unsafe` of its own:

  * `keepBoxed` (through each Common's `keep` syntax): OCaml's
    `let x = e;;`, which evaluates `e` once.  The value is computed at its
    first use and cached under a name, so a `new_definition` in `e` runs once
    however often `x` is used.
  * `keepPut` / `keepGet`: a value stored under a name, kept between the
    separate elaborations of a file's `#eval`s.
  * `runIO`, `runBaseIO`: run an IO action where OCaml calls a function with
    side effects from pure code.

It is a module of its own, not part of Session: these helpers let pure code
run side effects and read stored values, so a file that wants them imports
this module explicitly.  It is support for writing OCaml sessions as Lean
files, not part of HOL Light's load.
-/

import Session
import Std.Data.HashMap

namespace HolToplevel

/-- The values of `keep`, `keepPut`, by name. -/
initialize keepCell : IO.Ref (Std.HashMap String NonScalar) ← IO.mkRef {}

/-- A cached value, boxed.  The box is what makes `keep` evaluate once
    for a FUNCTION-valued `let` (a conversion, rule or tactic): Lean's
    compiler merges `fun _ => e` with the function `e` returns into one
    lambda of higher arity, so `e` itself (with any proof it does) would
    run again at every application.  A lambda returning a structure is not
    merged. -/
structure Kept (α : Type) where
  val : α
  tag : Unit

@[noinline] private unsafe def keepBoxedImpl {α : Type} (name : String)
    (f : Unit → Kept α) : α :=
  match unsafeIO (do
    match (← keepCell.get).get? name with
    | some v => pure (unsafeCast v : Kept α).val
    | none =>
      let b := f ()
      keepCell.modify (·.insert name (unsafeCast b))
      pure b.val) with
  | .ok v => v
  | .error _ => (f ()).val

/-- `keepBoxed name f`: the value of `f ()`, computed at the first call with
    this `name` and cached.  Used through each Common's `keep`. -/
@[implemented_by keepBoxedImpl]
def keepBoxed {α : Type} (_name : String) (f : Unit → Kept α) : α := (f ()).val

/-- The cache key of `keep name` in declaration `d`: the same name in two
    modules (or two declarations) is two different values. -/
def keyOf (d : Lean.Name) (name : String) : String := s!"{d}/{name}"

private unsafe def keepPutImpl {α : Type} (name : String) (v : α) : IO Unit :=
  keepCell.modify (·.insert name (unsafeCast v))

/-- Store `v` under `name` (read back with `keepGet`). -/
@[implemented_by keepPutImpl]
opaque keepPut {α : Type} (name : String) (v : α) : IO Unit

@[noinline] private unsafe def keepGetImpl {α : Type} [Inhabited α] (name : String) : α :=
  match unsafeIO (do return (← keepCell.get).get? name) with
  | .ok (some v) => unsafeCast v
  | _ => panic! s!"{name} not set"

/-- The value stored under `name` by `keepPut` (panics if there is none). -/
@[implemented_by keepGetImpl]
opaque keepGet {α : Type} [Inhabited α] (name : String) : α

@[noinline] private unsafe def runIOImpl {α : Type} (x : IO α) : Except IO.Error α :=
  unsafeIO x

/-- Run `x` and return its result (or the error it raised). -/
@[implemented_by runIOImpl]
opaque runIO {α : Type} (x : IO α) : Except IO.Error α

@[noinline] private unsafe def runBaseIOImpl {α : Type} [Nonempty α] (x : BaseIO α) : α :=
  unsafeBaseIO x

/-- Run `x` (which cannot fail) and return its result. -/
@[implemented_by runBaseIOImpl]
opaque runBaseIO {α : Type} [Nonempty α] (x : BaseIO α) : α

end HolToplevel
