/- File: HolMath.lean
Library root: the mathematical theories and additional proof tools.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

This module is the ROOT of the `HolMath` Lean library (see `lakefile.toml`).
Lake's `roots` determine which modules BELONG to a library, while the default
`globs` build only the root module itself and, recursively, its local imports.
So this import list IS the library's build set - a module absent from it is not
built by `lake build @/HolMath`.  Kept in `hol_lib.ml` order to match Hol.lean. -/

import HolMath.Base          -- the HOL Light surface for the pure translations
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
