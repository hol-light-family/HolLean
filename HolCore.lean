/- File: HolCore.lean
Library root: the HOL Light kernel and core proof infrastructure.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

This module is the ROOT of the `HolCore` Lean library (see `lakefile.toml`).
Lake's `roots` determine which modules BELONG to a library, while the default
`globs` build only the root module itself and, recursively, its local imports.
So this import list IS the library's build set - a module absent from it is not
built by `lake build @/HolCore`.  Kept in `hol_lib.ml` order to match Hol.lean. -/

import HolCore.System        -- system.ml : parsing setup / bignums
import HolCore.Lib           -- lib.ml    : general library functions
import HolCore.Fusion        -- fusion.ml : the logical core
import HolCore.OcamlHash     -- OCaml Hashtbl.hash, switchable (HOLLEAN_OCAML_HASH) for comparison
import HolCore.Basics        -- basics.ml : syntax operations and utilities
import HolCore.Nets          -- nets.ml   : term nets
import HolCore.Printer       -- printer.ml
import HolCore.Preterm       -- preterm.ml
import HolCore.Parser        -- parser.ml
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
