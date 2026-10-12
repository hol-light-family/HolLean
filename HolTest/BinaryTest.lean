/- File: HolTest/BinaryTest.lean
Runtime test suite: Library/binary.ml (HolLibrary/Binary.lean, wired by
SessionLibrary/Binary.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/binary.ml"`, `set_margin 1000`, then `string_of_thm`).
tools/binarydiff/check.sh compares far more structurally: all theorems, the
constants and definitions. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.Binary.ensureBinary

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thm' (lbl : String) (th : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm th)
  if got == squash expected || got == expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

namespace Bin
open Session SessionLibrary.Binary HolLight.Syntax

#eval thm' "bitset" bitset
  "|- forall n. bitset n = {i | ODD (n DIV 2 EXP i)}"
#eval thm' "binarysum" binarysum
  "|- forall s. binarysum s = nsum s (\\i. 2 EXP i)"
#eval thm' "BITSET_0" BITSET_0
  "|- bitset 0 = {}"
#eval thm' "BITSET_STEP" BITSET_STEP
  "|- (forall n. bitset (2 * n) = IMAGE SUC (bitset n)) /\\ (forall n. bitset (2 * n + 1) = 0 INSERT IMAGE SUC (bitset n))"
#eval thm' "BINARYSUM_BITSET" BINARYSUM_BITSET
  "|- forall n. binarysum (bitset n) = n"
#eval thm' "BITSET_EQ" BITSET_EQ
  "|- forall m n. bitset m = bitset n <=> m = n"
#eval thm' "BITSET_EQ_EMPTY" BITSET_EQ_EMPTY
  "|- forall n. bitset n = {} <=> n = 0"
#eval thm' "FINITE_BITSET" FINITE_BITSET
  "|- forall n. FINITE (bitset n)"
#eval thm' "BITSET_BOUND_LEMMA" BITSET_BOUND_LEMMA
  "|- forall n i. i IN bitset n ==> 2 EXP i <= n"
#eval thm' "BINARYSUM_BOUND" BINARYSUM_BOUND
  "|- forall k s. (forall i. i IN s ==> i < k) ==> binarysum s < 2 EXP k"
#eval thm' "BITSET_BOUND" BITSET_BOUND
  "|- forall n i k. n < 2 EXP k /\\ i IN bitset n ==> i < k"
#eval thm' "BITSET_BINARYSUM" BITSET_BINARYSUM
  "|- forall s. FINITE s ==> bitset (binarysum s) = s"
#eval thm' "BINARYSUM_DIV" BINARYSUM_DIV
  "|- forall k s. FINITE s ==> nsum s (\\j. 2 EXP j) DIV 2 EXP k = nsum s (\\j. if j < k then 0 else 2 EXP (j - k))"
#eval thm' "BITSET_BOUND_EQ" BITSET_BOUND_EQ
  "|- forall n k. n < 2 EXP k <=> (forall i. i IN bitset n ==> i < k)"
#eval thm' "BINARYSUM_BOUND_EQ" BINARYSUM_BOUND_EQ
  "|- forall s k. FINITE s ==> (binarysum s < 2 EXP k <=> (forall i. i IN s ==> i < k))"

end Bin
