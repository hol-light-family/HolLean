/- File: HolInit.lean
Eager initialisation of the whole system, the way HOL Light starts up.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

WHY THIS EXISTS.  HOL Light has no notion of "forcing": `hol.ml` calls
`loads "hol_lib.ml"`, and `hol_lib.ml` in turn `loads` each source file in
dependency order (system.ml, lib.ml, fusion.ml, ... realarith.ml, real.ml,
calc_rat.ml, int.ml).  Every `loads` executes that file's top-level statements
IMMEDIATELY, so by the time the user reaches a prompt the types, constants,
parser fixities and theorems all exist.

This translation is lazy instead: each `HolMath` layer is a pure parameterized
library and `Session.lean` holds the state behind memoised caches that populate
on first read.  Nothing runs until an accessor is read, so a bare
`parse_term "&2 + &2"` in a fresh process fails with

    mk_type: type num has not been defined

Importing THIS module removes that difference.  Its `initialize` block runs when
the module is loaded - Lean's nearest analogue to `loads` - and drives the whole
chain, exactly as `hol_lib.ml` does.  After `import HolInit` everything is
declared and no forcing is needed.

  This initialisation has a real cost, paid once per process.  That is the same
  bargain HOL Light makes (its startup is not instant either), but note the
  difference in model: HOL Light pays it ONCE for a long-lived session, whereas
  Lean elaborates each module in a SEPARATE process.  So this module is
  deliberately NOT imported by the library or the test suite - if `Session`
  initialised eagerly, all the test modules would each pay that cost and the
  build would take far longer.  Import it from a scratchpad (see Prove.lean),
  not from library code.

IMPLEMENTATION NOTE.  An `initialize` block may not mention an `unsafe`
declaration, and the Session accessors are all `unsafe`.  The way round it is
the same `@[implemented_by]` device `Hol.lean` already uses for `main`: do the
work in an `unsafe` function, then expose it through a safe `opaque` constant.
-/

import HolCore
import HolMath
import Session

open HolCore.Kernel

namespace HolInit

/- Forcing the TOP of each dependency branch transitively forces everything
   beneath it, so this list is short by design.

   *** THE ORDER HERE IS LOAD-BEARING AND MUST FOLLOW hol_lib.ml. ***
   Forcing `Wf` AFTER the real-number layers panics with `setupWf failed:
   tryfind`.  The reason is the same one that governs HOL Light's own
   load order: realax.ml's fifteen `overload_interface` calls make `:real` the
   default type for SCHEMATIC terms, so a later-parsed wf.ml proforma reads as
   real rather than natural and its proof collapses.  hol_lib.ml loads wf.ml at
   line 87 and lists.ml at 92, both BEFORE realax.ml at 93 - so we force in that
   same sequence.  Do not reorder these lines. -/
private unsafe def bootstrapImpl : IO Unit := do
  -- ensureDefine forces every layer hol_lib.ml loads, in its order: the
  -- prefix through int.ml (Session.ensureHolPrefixThroughInt), then sets.ml,
  -- iterate.ml, cart.ml and define.ml.  Session owns the order: every layer
  -- whose proofs depend on the schematic default type (`:real` before int.ml,
  -- `:num` after its final `prioritize_num`) is forced at its true position.
  -- iterate.ml's `prioritize_real()` (1982) and closing `prioritize_num()`
  -- (3112) decide how untyped terms such as `x + &0` are typed afterwards.
  --
  -- The load prints MESON's progress and type-invention warnings (about 5,000
  -- lines), as HOL Light's does.  This runs while a module is being IMPORTED,
  -- where nothing captures the output: in the editor's language server it
  -- goes to the worker's stdout, which is the server's protocol channel, and
  -- the worker deadlocks.  So the output of the load is captured and dropped,
  -- unless HOLLEAN_SHOW_LOAD is set (`make prove` sets 1; in a terminal the
  -- output is safe to show):
  --   0 (or unset)  drop it;
  --   1             HOL Light's default messages, as HOL Light shows them;
  --   2             also the tracing switches `copverb`, `metisverb` and
  --                 `Metis_unify.verb`, for the load only.
  -- The flags keep their HOL Light defaults for the user's own commands.
  let level := ((← IO.getEnv "HOLLEAN_SHOW_LOAD").bind String.toNat?).getD 0
  if level ≥ 2 then
    let flags := [HolCore.FirstOrder.copverb, HolCore.Metis.metisverb,
                  HolCore.Metis.metis_unify_verb]
    for f in flags do f.set true
    try Session.ensureDefine
    finally for f in flags do f.set false
    HolCore.FirstOrder.stdFlush
  else if level == 1 then
    Session.ensureDefine
  else
    let sink ← IO.mkRef ({} : IO.FS.Stream.Buffer)
    let out := IO.FS.Stream.ofBuffer sink
    let _ ← IO.withStdout out (IO.withStderr out Session.ensureDefine)

/-- Run the whole HOL Light load sequence, as `hol_lib.ml` does at startup.
    Safe wrapper over `bootstrapImpl` so that `initialize` can call it. -/
@[implemented_by bootstrapImpl]
opaque bootstrap : IO Unit

end HolInit

/- Lean's analogue of `loads`: this runs when the module is imported. -/
initialize HolInit.bootstrap
