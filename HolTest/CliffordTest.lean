/- File: HolTest/CliffordTest.lean
Runtime test suite: Multivariate/clifford.ml (HolMultiLib/Clifford.lean,
wired by SessionMultiLib/Clifford.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/clifford.ml"`, then `string_of_thm`).  The whole file is
also compared with HOL Light by tools/clifdiff: all 112 theorems and
definitions structurally.

The theorems and terms chosen here print without invented type variables,
so their printed forms do not depend on type-variable numbering.

Loading clifford.ml (`ensureClifford`) builds every bundle in file order; a
proof that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.Clifford

open HolCore.Kernel Session SessionMultiLib.Clifford HolTest.CommonTest HolLight.Syntax

#eval ensureClifford

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/-- Apply a conversion to a parsed term; compare the theorem, or `FAIL msg`. -/
private unsafe def convCheck (lbl : String) (c : HolCore.Equal.ioconv) (s expected : String) :
    IO Unit := do
  let got ← match ← HolCore.Parser.parse_term s with
    | Except.error e => pure s!"FAIL parse: {e}"
    | Except.ok tm => do
      match ← c tm with
      | Except.ok th => pure (squash (← HolCore.Printer.string_of_thm th))
      | Except.error e => pure s!"FAIL {e}"
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/- ---------------------------------------------------------------------- -/
/- Theorem statements (clifford.ml), as HOL Light prints them.  They also  -/
/- check the $$, outer, multivector and grade infixes, the lambdas binder  -/
/- and the * overload.                                                     -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "clifford.ml DIMINDEX_MULTIVECTOR" DIMINDEX_MULTIVECTOR
  "|- dimindex (:(N)multivector) = 2 EXP dimindex (:N)"
#eval thmCheck "clifford.ml GEOM_ASSOC" GEOM_ASSOC
  "|- forall x y z. x * y * z = (x * y) * z"
#eval thmCheck "clifford.ml OUTER_ASSOC" OUTER_ASSOC
  "|- forall x y z. x outer y outer z = (x outer y) outer z"
#eval thmCheck "clifford.ml GEOM_MBASIS_SING" GEOM_MBASIS_SING
  "|- forall i j. mbasis {i} * mbasis {j} = (if i IN 1..dimindex (:N) /\\ j IN 1..dimindex (:N) then if i = j then mbasis {} else if i < j then mbasis {i, j} else --mbasis {i, j} else vec 0)"
#eval thmCheck "clifford.ml reversion" reversion
  "|- forall x. reversion x = (lambdas s. -- &1 pow ((CARD s * (CARD s - 1)) DIV 2) * x $$ s)"

/- ---------------------------------------------------------------------- -/
/- The conversions (clifford.ml 756-865).                                   -/
/- ---------------------------------------------------------------------- -/
#eval convCheck "clifford.ml SETENUM_NORM_CONV" SETENUM_NORM_CONV "{3,1,2,1}"
  "|- {3, 1, 2, 1} = {1, 2, 3}"
#eval convCheck "clifford.ml SETENUM_NORM_CONV sorted" SETENUM_NORM_CONV "{1,2}"
  "|- {1, 2} = {1, 2}"
#eval convCheck "clifford.ml MBASIS_SPLIT_CONV" MBASIS_SPLIT_CONV
  "mbasis{1,3,2}:real^(3)multivector"
  "|- mbasis {1, 3, 2} = mbasis {1} outer mbasis {2} outer mbasis {3}"
#eval convCheck "clifford.ml MBASIS_MERGE_CONV" MBASIS_MERGE_CONV
  "mbasis{1} outer mbasis{2,3}:real^(3)multivector"
  "|- mbasis {1} outer mbasis {2, 3} = mbasis {1, 2, 3}"
#eval convCheck "clifford.ml MBASIS_GROUP_CONV" MBASIS_GROUP_CONV
  "&2 % mbasis{1} + &3 % mbasis{2} + &4 % mbasis{1}:real^(3)multivector"
  "|- &2 % mbasis {1} + &3 % mbasis {2} + &4 % mbasis {1} = &3 % mbasis {2} + &6 % mbasis {1}"
#eval convCheck "clifford.ml OUTER_CANON_CONV" OUTER_CANON_CONV
  "(mbasis{1} + &2 % mbasis{2}) outer (mbasis{2} - mbasis{1}) :real^(3)multivector"
  "|- (mbasis {1} + &2 % mbasis {2}) outer (mbasis {2} - mbasis {1}) = &3 % mbasis {1, 2}"
#eval convCheck "clifford.ml OUTER_CANON_CONV reorder" OUTER_CANON_CONV
  "mbasis{2,1} outer mbasis{3} :real^(3)multivector"
  "|- mbasis {2, 1} outer mbasis {3} = &1 % mbasis {1, 2, 3}"
