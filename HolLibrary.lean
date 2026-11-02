/- File: HolLibrary.lean
Library root: the files of HOL Light's Library/ directory.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Each module translates one Library/*.ml file (prime.ml is HolLibrary.Prime,
ring_det.ml is HolLibrary.RingDet, ...): every file except
tactician_light.ml, which runs tactics given as OCaml source and so has no
Lean counterpart.  Like HolMath these are pure libraries, with no `unsafe`
code: each file's theorems are built by setup functions that take what the
file needs from the session as parameters.  SessionLibrary/<Name>.lean runs
them with Session's values, and importing it is the file's `needs`.

This module is the ROOT of the `HolLibrary` Lean library (see
`lakefile.lean`).  Lake's `roots` determine which modules BELONG to a library,
while the default `globs` build only the root module itself and, recursively,
its local imports.  So this import list IS the library's build set - a module
absent from it is not built by `lake build @/HolLibrary`.  Importing this
module loads no library file: nothing runs until a SessionLibrary module is
imported. -/

import HolLibrary.Prime
import HolLibrary.Floor
import HolLibrary.Components
import HolLibrary.Records
import HolLibrary.BDD
import HolLibrary.Words
import HolLibrary.Analysis
import HolLibrary.RSTC
import HolLibrary.Transc
import HolLibrary.Wo
import HolLibrary.Card
import HolLibrary.BitMatch
import HolLibrary.Products
import HolLibrary.Agm
import HolLibrary.Iter
import HolLibrary.Bitsize
import HolLibrary.Binary
import HolLibrary.Isum
import HolLibrary.Frag
import HolLibrary.Binomial
import HolLibrary.Pocklington
import HolLibrary.RingTheory
import HolLibrary.Integer
import HolLibrary.Multiplicative
import HolLibrary.Primitive
import HolLibrary.Pratt
import HolLibrary.Poly
import HolLibrary.Matroids
import HolLibrary.Permutations
import HolLibrary.Jacobi
import HolLibrary.CalcReal
import HolLibrary.WordAutomata
import HolLibrary.Q
import HolLibrary.FieldTheory
import HolLibrary.RingDet
import HolLibrary.GroupTheory
import HolLibrary.RingGroups
import HolLibrary.ModmulGroup
import HolLibrary.SymmetricGroup
import HolLibrary.Galois
import HolLibrary.FiniteFields
import HolLibrary.Cyclotomic
