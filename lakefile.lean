import Lake
open Lake DSL

/- Optimisation level of the C code Lake compiles (native HolCore, HolMath,
   HolLibrary, and the `hollean` executable).

   By default HolCore, HolMath and the executable are compiled at -O3 (Lake's
   own level: their code is where proof search spends its time) and
   HolLibrary at -O0.  HolLibrary's C is mostly one-off theorem set-up in
   very large functions (HolLibrary.RingTheory's C is 117 MB), on which
   clang's optimiser is very slow: RingTheory takes about 1 hour at -O1 and
   about 2.5 minutes at -O0.

   `-Kopt=N` (e.g. `lake build -Kopt=1`, or `make ... OPT=1` and `make
   build-O3`) compiles EVERYTHING at -ON instead, into `.lake/build-ON`, so
   switching levels never recompiles the default build's objects.

   Lake passes the build type's `-O3 -DNDEBUG` first and `moreLeancArgs`
   after them, and clang uses the last `-O`.  Where the level is -O3 nothing
   is added, so those objects are identical to a plain Lake build. -/
def optLevel? : Option String := get_config? opt

def optArgs (level : String) : Array String :=
  if level == "3" then #[] else #["-O" ++ level]

package HolLean where
  version := v!"0.1.0"
  moreLeancArgs := optArgs (optLevel?.getD "3")
  buildDir := match optLevel? with
    | none => defaultBuildDir
    | some level => defaultBuildDir.toString ++ "-O" ++ level

/- Separate targets mirroring the project's strict layering, so each can be
   built on its own:

     HolCore         the HOL Light kernel and core proof infrastructure
                     (self-contained)
     HolMath         the mathematical theories       (depends on HolCore)
     Session         the `unsafe` session state      (depends on HolCore + HolMath)
     HolLibrary      HOL Light's Library/ files      (depends on HolMath)
     SessionLibrary  their session wiring            (depends on Session + HolLibrary)
     HolTest         the runtime test suite          (depends on Session + SessionLibrary)

   A library's `roots` say which modules BELONG to it; the default `globs`
   build only each root module plus, recursively, its local imports.  So each
   root .lean file's import list is that library's build set.

     lake build @/HolCore     just the kernel and core           (fast)
     lake build @/HolMath     the mathematics, no tests run
     lake build @/HolTest     everything, running every test
     lake build               the default `hollean` executable, incl. native
                              code; no tests (Hol.lean does not import them) -/

/- Compiled to native code for `#eval`.  Safe here: these libraries have no
   `unsafe` code, so evaluating their top-level constants at load (as native
   code does) cannot depend on session state.  NOT Session: its layers must be
   built on first use, in hol_lib.ml order (see Session.lean). -/
lean_lib HolCore where
  roots := #[`HolCore]
  precompileModules := true

/- Native, for the same reason as HolCore. -/
lean_lib HolMath where
  roots := #[`HolMath]
  precompileModules := true

lean_lib Session where
  roots := #[`Session]

lean_lib HolTest where
  roots := #[`HolTest]

/- Eager initialisation for interactive/scratchpad use (see HolInit.lean).  It
   is deliberately NOT a default target: importing it runs the whole HOL Light
   load sequence, about 20-30 s per process with native HolCore/HolMath, which
   is right for a scratchpad but would be paid by every module if the library
   depended on it. -/
lean_lib HolInit where
  roots := #[`HolInit]

/- The help system (help.ml) and theorem database (database.ml), as in hol.ml
   88-92.  `Help` depends only on HolCore; `Database` names every library
   theorem and so depends on Session. -/
lean_lib Help where
  roots := #[`Help]

lean_lib Database where
  roots := #[`Database]

@[default_target]
lean_exe hollean where
  root := `Hol

/- HOL Light's Library/ files, loaded on demand (`needs`).  `HolLibrary` is
   PURE, like HolMath (and native, for the same reason); `SessionLibrary` is
   its `unsafe` wiring to Session, like Session.lean is for HolMath. -/
lean_lib HolLibrary where
  roots := #[`HolLibrary]
  precompileModules := true
  -- -O0 by default (see the top of this file); with `-Kopt=N` the
  -- package's level applies.  These come after the package's arguments.
  moreLeancArgs := if optLevel?.isNone then #["-O0"] else #[]

lean_lib SessionLibrary where
  roots := #[`SessionLibrary]

/- The HOLTrace proof reconstructor (HolTrace.lean): reads a trace in the
   format at https://holtrace.cr.yp.to/format.html and replays every inference
   in it through the kernel.

   It depends on HolCore ALONE, and that is load-bearing rather than tidiness.
   Replay starts from a bare kernel - the trace itself creates every constant,
   type and axiom it uses - so importing `Session` would break it: Session's
   `initialize` runs `setupBool` on load, which declares `T`, `/\` and the
   rest, and the trace's own definitions of those names would then collide. -/
/- Translations of HOL Light's Tutorial/ files (HolTutorial.lean imports
   them all).  Each is a toplevel session in Prove.lean style; building it
   runs it.  Built by `make tutorial` and `make check`. -/
lean_lib HolTutorial where
  roots := #[`HolTutorial]

lean_lib HolTrace where
  roots := #[`HolTrace]

lean_exe holtrace where
  root := `HolTrace
