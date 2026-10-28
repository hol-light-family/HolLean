/- File: HolMultiLib.lean
Library root: the files of HOL Light's Multivariate/ directory translated so
far (misc.ml, vectors.ml, msum.ml, determinants.ml, clifford.ml, metric.ml,
topology.ml, homology.ml, specialtopologies.ml, convex.ml, complexes.ml,
cross.ml, tarski.ml, wlog.ml, wlog_examples.ml, cvectors.ml and paths.ml).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Each module translates one Multivariate/*.ml file, in the style of
HolLibrary: pure, with no `unsafe` code; each file's theorems are built by
setup functions that take what the file needs as parameters.
SessionMultiLib/<Name>.lean runs them with Session's (and SessionLibrary's)
values, and importing it is the file's `needs`.

This module is the ROOT of the `HolMultiLib` Lean library (see
`lakefile.lean`): its import list is the library's build set.  Importing it
loads no file; nothing runs until a SessionMultiLib module is imported. -/

import HolMultiLib.Misc
import HolMultiLib.Vectors
import HolMultiLib.MSum
import HolMultiLib.Determinants
import HolMultiLib.Clifford
import HolMultiLib.Metric
import HolMultiLib.Topology
import HolMultiLib.Homology
import HolMultiLib.SpecialTopologies
import HolMultiLib.Convex
import HolMultiLib.Complexes
import HolMultiLib.Cross
import HolMultiLib.Tarski
import HolMultiLib.Wlog
import HolMultiLib.WlogExamples
import HolMultiLib.CVectors
import HolMultiLib.Paths
import HolMultiLib.Paracompact
