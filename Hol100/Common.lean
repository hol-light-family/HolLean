/- File: Hol100/Common.lean
The prelude shared by the translations of HOL Light's 100/ files.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

The 100/ files are toplevel sessions like those of Examples/, and are
translated in the same style, with the same helpers: `phrase`, `keep`,
`once`, `replay`, `failure` and `try_` of HolExamples/Common.lean (see
there).  A module opens `HolExamples` to use them.  Sharing them (rather
than copying them) also means one `once` registry, so a 100/ file that
`needs` an Examples file (mangoldt.ml, machin.ml) and an Examples file that
`needs` a 100/ file (apery.ml, lucas_lehmer.ml) replay each file at most
once per process.

This file adds what several 100/ proofs need beyond that (open `Hol100`):
`check` (lib.ml) for `ttac o check p o concl`, an `o` for a plain
function after a syntax function that can fail (`is_var o rand o concl`),
and `map` / `funpow` for rules that can fail (`mapR`, `funpowR`).
-/

import HolExamples.Common

open HolCore.Kernel

namespace Hol100

/-- A predicate as `check` takes it: plain, or built from syntax functions
    that can fail (a failure counts as false: OCaml's `check` then fails). -/
class CheckPred (π : Type) (α : outParam Type) where
  holds : π → α → Bool

instance {α : Type} : CheckPred (α → Bool) α := ⟨fun p x => p x⟩
instance {α : Type} : CheckPred (α → Except String Bool) α :=
  ⟨fun p x => match p x with | .ok b => b | .error _ => false⟩

/-- lib.ml's `check p x`: `x` if `p x`, otherwise a failure
    (`MP_TAC o check (is_neg o concl)`, `UNDISCH_TAC o check is_eq o concl`). -/
def check {π α : Type} [CheckPred π α] (p : π) (x : α) : ExceptT String IO α :=
  if CheckPred.holds p x then pure x else throw "check"

/-- `f o g` where `g` can fail and `f` cannot (`is_var o rand`). -/
instance (priority := 200) oPureExcept {α β γ : Type} :
    HolLight.OComp (β → γ) (α → Except String β) (α → Except String γ) where
  comp f g := fun a => (g a).map f

/-- A rule (`ExceptT String IO`) after a syntax function that can fail. -/
instance (priority := 200) oRuleExcept {α β γ : Type} :
    HolLight.OComp (β → ExceptT String IO γ) (α → Except String β) (α → ExceptT String IO γ) where
  comp f g := fun a => do f (← ExceptT.mk (pure (g a)))

/-- `map r` for a rule `r` that can fail (`REWRITE_TAC o map GSYM`). -/
def mapR {α β : Type} (r : α → ExceptT String IO β) (l : List α) : ExceptT String IO (List β) :=
  l.mapM r

/-- `funpow n r x` for a rule `r` that can fail. -/
def funpowR {α : Type} : Nat → (α → ExceptT String IO α) → α → ExceptT String IO α
  | 0, _, x => pure x
  | n + 1, r, x => do funpowR n r (← r x)

/-- `f o g` where `g` is a rule that can fail and `f` cannot
    (`fst o EQ_IMP_RULE`). -/
instance (priority := 200) oPureRule {α β γ : Type} :
    HolLight.OComp (β → γ) (α → ExceptT String IO β) (α → ExceptT String IO γ) where
  comp f g := fun a => do pure (f (← g a))

/-- An `Except` value in `ExceptT String IO` (a syntax function's result). -/
def ec {α : Type} (x : Except String α) : ExceptT String IO α := ExceptT.mk (pure x)

end Hol100

namespace Hol100

/-- A conversion that cannot do IO (`term → Except String thm`, such as
    `SELECT_CONV` or `GEN_ALPHA_CONV v`) as the `ioconv` that `CONV_TAC`
    and the conversionals take. -/
def pureC (c : term → Except String thm) : HolCore.Equal.ioconv := fun t => pure (c t)

end Hol100

namespace Hol100

/-- Print a theorem list as OCaml's toplevel does (`val x : thm list =
    [|- ...; |- ...]`, the prefix being dropped by tools/tutorialdiff): the
    toplevel stops after 299 elements and prints `...` (its printer step
    limit). -/
def printThms (l : List thm) : IO Unit := do
  let shown := l.take 299
  let strs ← shown.mapM HolCore.Printer.string_of_thm
  let more := if l.length > 299 then "; ..." else ""
  IO.println ("[" ++ String.intercalate ";\n " strs ++ more ++ "]")

end Hol100

namespace Hol100

/-- Run an `ExceptT String IO` list computation for a `keep`ed value,
    panicking with HOL Light's message on failure (as the toplevel throws). -/
def runList {α : Type} (m : ExceptT String IO (List α)) : List α :=
  match HolToplevel.runIO m.run with
  | .ok (.ok l) => l
  | .ok (.error e) => panic! e
  | .error e => panic! (toString e)

end Hol100
