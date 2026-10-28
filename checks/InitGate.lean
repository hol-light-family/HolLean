/- File: checks/InitGate.lean
The `make check` gate against function-typed `initialize` constants.

Lean 4.35 compiles an `initialize` constant whose type is (or unfolds to) a
function type as a function of one or more arguments, and then never runs
its initialiser in compiled code; every call from another module reaches
`unreachable` (interpreted) or an undefined symbol (native).  See
holtranslation.md, "Function-typed initialize".  Box the function in a
structure instead.

Usage: `lake env lean --run checks/InitGate.lean MOD...`
Loads the listed modules (and their imports) and checks every constant with
an `[init]` attribute that was declared in a HolLean module.  Prints each
offending constant and exits 1 if there are any.
-/
import Lean
open Lean Meta

/-- Does `ty` reduce (unfolding definitions and abbreviations) to a pi type? -/
def isFunctionType (ty : Expr) : MetaM Bool := do
  let ty ← whnf ty
  return ty.isForall

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: InitGate MOD..."
    return 2
  initSearchPath (← findSysroot)
  let mods := args.toArray.map fun s => ({ module := s.toName } : Import)
  let env ← importModules mods {} (loadExts := false)
  let mut bad : Array (Name × String) := #[]
  let mut checked := 0
  for (n, ci) in env.constants.toList do
    -- an `initialize`/`builtin_initialize` constant has an init function
    let isInit := (getInitFnNameFor? env n).isSome || (getBuiltinInitFnNameFor? env n).isSome
    if !isInit then continue
    -- only constants declared in this project's modules
    let some modIdx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[modIdx.toNat]!
    let root := modName.getRoot.toString
    if !(["Session", "SessionCore", "SessionMath", "SessionLibrary", "SessionMultiLib", "HolCore", "HolMath", "HolLibrary", "HolMultiLib",
          "HolTest", "HolTutorial", "HolExamples", "HolLogicArith", "Help",
          "Database", "Hol", "HolTrace", "HolToplevel"].contains root) then continue
    checked := checked + 1
    let ctx : Core.Context := { fileName := "<initgate>", fileMap := default }
    let st : Core.State := { env }
    let r ← ((MetaM.run' (isFunctionType ci.type)).run ctx st).toBaseIO
    match r with
    | .ok (true, _) => bad := bad.push (n, s!"{modName}")
    | .ok (false, _) => pure ()
    | .error e => IO.eprintln s!"initgate: could not check {n}: {← e.toMessageData.toString}"
  for (n, m) in bad do
    IO.println s!"    FUNCTION-TYPED initialize: {n} (in {m})"
  IO.println s!"initgate: {checked} initialize constants checked, {bad.size} function-typed"
  return (if bad.isEmpty then 0 else 1)
