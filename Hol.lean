/- File: Hol.lean
Top-level loader for the Lean 4 translation of HOL Light (`hol.ml` + `hol_lib.ml`).
Original       John Harrison, University of Cambridge Computer Laboratory
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2024
Original (c) Copyright, Juneyoung Lee 2024
Lean4 translation by Chris Walton 2026

`hol.ml`/`hol_lib.ml` are HOL Light's top-level scripts: `hol_lib.ml` `loads` each
source file in dependency order and `hol.ml` sets the version, installs printers,
and loads the help/database.  In Lean the load order is expressed by `import`s
(transitively resolved), so this module simply imports the translated layers in
`hol_lib.ml` order and reproduces the two pieces of genuine logic from those
scripts: the `hol_version` string and `check_axioms`.
-/

-- hol_lib.ml load order (each `loads "X.ml"` becomes `import HolCore.X`)
-- Importing `Session` transitively pulls in every layer below in the
-- correct dependency order;

/- ---------------------------------------------------------------------- -/
/- System and general library functions.                                  -/
/- ---------------------------------------------------------------------- -/

import HolCore.System        -- system.ml : parsing setup / bignums
import HolCore.Lib           -- lib.ml    : general library functions

/- ---------------------------------------------------------------------- -/
/- The logical core.                                                      -/
/- ---------------------------------------------------------------------- -/

import HolCore.Fusion        -- fusion.ml : the logical core

/- ---------------------------------------------------------------------- -/
/- Some extra support stuff needed outside the core.                      -/
/- ---------------------------------------------------------------------- -/

import HolCore.Basics        -- basics.ml : syntax operations and utilities
import HolCore.Nets          -- nets.ml   : term nets

/- ---------------------------------------------------------------------- -/
/- The interface.                                                         -/
/- ---------------------------------------------------------------------- -/

import HolCore.Printer       -- printer.ml
import HolCore.Preterm       -- preterm.ml
import HolCore.Parser        -- parser.ml

/- ---------------------------------------------------------------------- -/
/- Higher level deductive system.                                         -/
/- ---------------------------------------------------------------------- -/

import HolCore.Equal         -- equal.ml  : equality reasoning / conversionals
import HolCore.Bool          -- bool.ml   : boolean theory + derived rules
import HolCore.Drule         -- drule.ml  : additional derived rules
import HolCore.Tactics       -- tactics.ml
import HolCore.Itab          -- itab.ml   : intuitionistic prover
import HolCore.Simp          -- simp.ml   : rewriting and simplification
import HolCore.Theorems      -- theorems.ml
import HolCore.IndDefs       -- ind_defs.ml : inductive definitions
import HolCore.Classic       -- class.ml  : classical reasoning
import HolCore.Trivia        -- trivia.ml : basic theories (e.g. `:1`)
import HolCore.Canon         -- canon.ml  : canonical forms
import HolCore.Meson         -- meson.ml  : MESON
import HolCore.FirstOrder    -- firstorder.ml : first-order shadow-term utils
import HolCore.Metis         -- metis.ml  : Metis
import HolCore.TheCops       -- thecops.ml : leanCoP and nanoCoP
import HolCore.Quot          -- quot.ml   : quotient types
import HolCore.ImpConv       -- impconv.ml : implicational rewriting

/- ---------------------------------------------------------------------- -/
/- Mathematical theories and additional proof tools.                      -/
/- ---------------------------------------------------------------------- -/

import HolMath.Pair          -- pair.ml   : pairing theory + syntax sugar
import HolMath.Compute       -- compute.ml : call-by-value reduction (computeLib)
import HolMath.Nums          -- nums.ml   : axiom of infinity; the natural numbers
import HolMath.Recursion     -- recursion.ml : definition by primitive recursion
import HolMath.Arith         -- arith.ml   : natural number arithmetic
import HolMath.Wf            -- wf.ml      : theory of wellfounded relations
import HolMath.CalcNum       -- calc_num.ml : calculation with natural numbers
import HolMath.Normalizer    -- normalizer.ml : canonical polynomial form
import HolMath.Grobner       -- grobner.ml  : Grobner basis ring/ideal procedure
import HolMath.IndTypes      -- ind_types.ml: tools for defining inductive types
import HolMath.Lists         -- lists.ml    : theory of lists, chars and strings
import HolMath.RealAx        -- realax.ml   : construction of the real numbers
import HolMath.CalcInt       -- calc_int.ml : calculation with integer-valued reals
import HolMath.RealArith     -- realarith.ml: universal real decision procedure
import HolMath.Real          -- real.ml     : derived properties of the reals
import HolMath.CalcRat       -- calc_rat.ml : calculation with rational-valued reals
import HolMath.Int           -- int.ml      : the integers, embedded in the reals
import HolMath.Sets          -- sets.ml     : basic set theory (predicates as sets)
import HolMath.Iterate       -- iterate.ml  : iterated operations, sums over N and R
import HolMath.Cart          -- cart.ml     : finite Cartesian product types
import HolMath.Define        -- define.ml   : general recursive definitions
import Session               -- the established (`unsafe`) session state

/- ---------------------------------------------------------------------- -/
/- The theorem database (database.ml).  The test suite is NOT imported   -/
/- here: it is the HolTest library (HolTest.lean), built by `make test`. -/
/- ---------------------------------------------------------------------- -/

import Database

open HolCore.Kernel Session

namespace HolCore

/-- `hol_version` (mirrors `hol.ml`'s `let hol_version = ...`).
    Tracks the HOL Light release this translation follows. -/
def hol_version : String := "3.1.0"

/- `check_axioms` (hol_lib.ml 105-114) lives in `Session`, NOT here.  It was
   defined in both, identically.  Session is the right home: it is where the rest
   of HOL Light's top-level names live, and it can be reached BY the tests, so `HolTest/DefineTest.lean` can
   assert it over the fully bootstrapped library and `HolTest/AxiomsTest.lean` can
   assert that it REJECTS a leaked axiom.  `hentry` below calls it. -/

end HolCore

open HolCore

/-- Executable entry point: report the version and run `check_axioms`. -/
unsafe def hentry : IO Unit := do
  IO.println s!"HOL Light (Lean 4 translation) — hol_version {hol_version}"
  match ← Session.check_axioms with
  | .ok () => IO.println "check_axioms: OK (only basic axioms present)"
  | .error e => IO.eprintln e

@[implemented_by hentry]
opaque mainImpl : IO Unit

def main : IO Unit := mainImpl
