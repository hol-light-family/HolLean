import Lake
open Lake DSL

/- Optimisation level of the C code Lake compiles (native HolCore, HolMath,
   HolLibrary, the session libraries SessionCore, SessionMath, Session and
   HolToplevel, and the `hollean` executable).

   By default HolCore, HolMath and the executable are compiled at -O3 (Lake's
   own level: their code is where proof search spends its time), and
   HolLibrary and the session libraries at -O0.  Their C is mostly one-off
   theorem set-up in very large functions (HolLibrary.RingTheory's C is
   117 MB), on which clang's optimiser is very slow: RingTheory takes about 1
   hour at -O1 and about 2.5 minutes at -O0.

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
  -- One recursion limit for every module (instead of a `set_option` in
  -- each file): elaboration of the large proof scripts nests deeply.
  leanOptions := #[⟨`maxRecDepth, (8000 : Nat)⟩]
  buildDir := match optLevel? with
    | none => defaultBuildDir
    | some level => defaultBuildDir.toString ++ "-O" ++ level

/- Separate targets mirroring the project's strict layering, so each can be
   built on its own:

     HolCore         the HOL Light kernel and core proof infrastructure
                     (self-contained)
     HolMath         the mathematical theories       (depends on HolCore)
     SessionCore     the core's session state, one module per HolCore file
                     with load-time state            (depends on HolCore)
     SessionMath     the theories' session state, one module per HolMath file
                                                     (depends on SessionCore + HolMath)
     Session         Session.lean, which imports both
     HolToplevel     helpers for the translated toplevel sessions
     HolLibrary      HOL Light's Library/ files      (depends on HolMath)
     SessionLibrary  their session wiring            (depends on Session + HolLibrary)
     HolMultiLib     HOL Light's Multivariate/ files (depends on HolMath)
     SessionMultiLib their session wiring            (depends on SessionLibrary + HolMultiLib)
     Help, Database  help.ml and database.ml          (depend on Session)
     HolTest         the test suite                  (depends on Session + SessionLibrary)
     HolTutorial, HolExamples, HolLogicArith
                     the translations of HOL Light's Tutorial/, Examples/,
                     Logic/ and Arithmetic/ files    (depend on HolToplevel)

   A library with `roots` builds each root module plus, recursively, its local
   imports, so the root file's import list is that library's build set
   (HolCore, HolMath, HolLibrary).  A library with `globs := .submodules`
   (SessionLibrary, HolTest and the translations) builds every module under
   its directory, each on its own: none of them has a module that imports all
   the others, because a session cannot load every library file at once.

     lake build @/HolCore     just the kernel and core           (fast)
     lake build @/HolMath     the mathematics, no tests run
     lake build @/HolTest     the tests (and what they need), running each
     lake build               the default `hollean` executable, incl. native
                              code; no tests (Hol.lean does not import them) -/

/- Compiled to native code for `#eval`.  Safe here: these libraries have no
   `unsafe` code, so evaluating their top-level constants at load (as native
   code does) cannot depend on session state. -/
lean_lib HolCore where
  roots := #[`HolCore]
  precompileModules := true

/- Native, for the same reason as HolCore. -/
lean_lib HolMath where
  roots := #[`HolMath]
  precompileModules := true

/- The session state, native like HolCore: each module of SessionCore (one
   per HolCore file with load-time state) and SessionMath (one per HolMath
   file) builds its file's layers by `initialize`, so evaluating its
   constants at load is how it is meant to run, in import (= hol_lib.ml)
   order.  -O0, as HolLibrary: its C is mostly one-off set-up code. -/
lean_lib SessionCore where
  roots := #[`SessionCore]
  globs := #[.one `SessionCore, .andSubmodules `SessionCore]
  precompileModules := true
  moreLeancArgs := if optLevel?.isNone then #["-O0"] else #[]

lean_lib SessionMath where
  roots := #[`SessionMath]
  globs := #[.one `SessionMath, .andSubmodules `SessionMath]
  precompileModules := true
  moreLeancArgs := if optLevel?.isNone then #["-O0"] else #[]

/- `Session.lean` imports the last modules of SessionCore and SessionMath,
   so `import Session` loads the whole library. -/
lean_lib Session where
  roots := #[`Session]
  precompileModules := true
  moreLeancArgs := if optLevel?.isNone then #["-O0"] else #[]

/- Helpers for writing a HOL Light toplevel session as a Lean file
   (HolToplevel.lean), for the translations' Common.lean files.  Not part of
   Session: a file that wants them imports this module. -/
lean_lib HolToplevel where
  roots := #[`HolToplevel]
  precompileModules := true
  moreLeancArgs := if optLevel?.isNone then #["-O0"] else #[]

/- The test suite: every module under HolTest/, each built on its own (a
   module's `#eval`s are its checks, so building it runs them).  There is
   no aggregate root: one module importing all the tests would load every
   library file into one session, which HOL Light does not accept for every
   combination (see SessionLibrary below). -/
lean_lib HolTest where
  globs := #[.submodules `HolTest]

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

/- HOL Light's Library/ files.  `HolLibrary` is PURE, like HolMath (and
   native, for the same reason); `SessionLibrary` is its wiring to Session,
   like Session is for HolMath, and importing one of its modules is that
   file's `needs`. -/
lean_lib HolLibrary where
  roots := #[`HolLibrary]
  precompileModules := true
  -- -O0 by default (see the top of this file); with `-Kopt=N` the
  -- package's level applies.  These come after the package's arguments.
  moreLeancArgs := if optLevel?.isNone then #["-O0"] else #[]

/- Each module is built on its own, with no aggregate root: importing a
   module runs its library file's load (`needs`), and HOL Light does not
   accept every combination of library files in one session (for example
   analysis.ml, then rstc.ml, then transc.ml fails with EQT_ELIM there too:
   rstc.ml's `prioritize_num` changes how transc.ml's terms parse).  So a
   file imports the libraries it `needs`, as a HOL Light session would. -/
lean_lib SessionLibrary where
  globs := #[.submodules `SessionLibrary]

/- HOL Light's Multivariate/ files, in the same two layers as Library/:
   `HolMultiLib` is pure (native, -O0, like HolLibrary), and
   `SessionMultiLib` is its wiring to Session and SessionLibrary; importing
   one of its modules is that file's `needs`. -/
lean_lib HolMultiLib where
  roots := #[`HolMultiLib]
  precompileModules := true
  moreLeancArgs := if optLevel?.isNone then #["-O0"] else #[]

lean_lib SessionMultiLib where
  globs := #[.submodules `SessionMultiLib]

/- HOL Light's EC/ files (elliptic curves over arbitrary fields), in the same
   two layers: `HolEC` is pure (native, -O0), and `SessionEC` is its wiring
   to Session and SessionLibrary; importing one of its modules is that
   file's `needs`. -/
lean_lib HolEC where
  roots := #[`HolEC]
  precompileModules := true
  moreLeancArgs := if optLevel?.isNone then #["-O0"] else #[]

lean_lib SessionEC where
  globs := #[.submodules `SessionEC]

/- Translations of HOL Light's Tutorial/ files, each built on its own (each
   imports the library files its HOL Light session `needs`).  Each is a
   toplevel session in Prove.lean style; building it runs it.  Built by
   `make tutorial` and `make check`. -/
lean_lib HolTutorial where
  globs := #[.submodules `HolTutorial]

/- Translations of files of HOL Light's Examples/, in the same style as
   HolTutorial, each built on its own.  Built by `make examples` and
   `make check`. -/
lean_lib HolExamples where
  globs := #[.submodules `HolExamples]

/- Translations of the files of HOL Light's 100/ (proofs of theorems from
   the "top 100 theorems" list), in the same style as HolExamples, each
   built on its own.  Built by `make hundred` and `make check`. -/
lean_lib Hol100 where
  globs := #[.submodules `Hol100]

/- Translations of HOL Light's Logic/ and Arithmetic/, in the same style as
   HolTutorial, each built on its own; each module imports the ones
   Logic/make.ml (Arithmetic/make.ml) loads before it.  Built by
   `make logic` and `make check`. -/
lean_lib HolLogicArith where
  globs := #[.submodules `HolLogicArith]

/- The HOLTrace proof reconstructor (HolTrace.lean): reads a trace in the
   format at https://holtrace.cr.yp.to/format.html and replays every inference
   in it through the kernel.

   It depends on HolCore ALONE, and that is load-bearing rather than tidiness.
   Replay starts from a bare kernel - the trace itself creates every constant,
   type and axiom it uses - so importing `Session` would break it: Session's
   first `initialize`s run `setupBool` on load (SessionCore/Bool.lean), which
   declares `T`, `/\` and the rest, and the trace's own definitions of those
   names would then collide. -/
lean_lib HolTrace where
  roots := #[`HolTrace]

lean_exe holtrace where
  root := `HolTrace
