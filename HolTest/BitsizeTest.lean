/- File: HolTest/BitsizeTest.lean
Runtime test suite: Library/bitsize.ml (HolLibrary/Bitsize.lean, wired by
SessionLibrary/Bitsize.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/bitsize.ml"`, `set_margin 1000`, then `string_of_thm`).
tools/bitsizediff/check.sh compares far more structurally: all theorems, the
constants and definitions, and the BITSIZE_CONV conversion tests from
tools/bitsizediff/convs.txt. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.Bitsize.ensureBitsize

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def check (lbl : String) (r : IO (Except String thm)) (expected : String) :
    IO Unit := do
  let got ← match ← r with
    | .ok th => pure (squash (← HolCore.Printer.string_of_thm th))
    | .error e => pure s!"FAIL {e}"
  if got == squash expected || got == expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

private unsafe def thm' (lbl : String) (th : thm) (expected : String) : IO Unit :=
  check lbl (pure (.ok th)) expected

/-- A conversion must fail on this input. -/
private unsafe def mustFail (lbl : String) (r : IO (Except String thm)) : IO Unit := do
  match ← r with
  | .ok th => IO.println s!"{lbl} -> MISMATCH got={← HolCore.Printer.string_of_thm th}"
  | .error _ => IO.println s!"{lbl} -> OK"

namespace B
open Session SessionLibrary.Bitsize HolLight.Syntax

#eval thm' "bitsize" bitsize
  "|- forall n. bitsize n = (minimal i. n < 2 EXP i)"
#eval thm' "BITSIZE_0" BITSIZE_0
  "|- bitsize 0 = 0"
#eval thm' "BITSIZE_POW2" BITSIZE_POW2
  "|- forall k. bitsize (2 EXP k) = k + 1"
#eval thm' "BITSIZE_1" BITSIZE_1
  "|- bitsize 1 = 1"
#eval thm' "BITSIZE_2" BITSIZE_2
  "|- bitsize 2 = 2"
#eval thm' "BITSIZE_LE" BITSIZE_LE
  "|- forall n k. bitsize n <= k <=> n < 2 EXP k"
#eval thm' "BITSIZE" BITSIZE
  "|- forall n. n < 2 EXP bitsize n"
#eval thm' "BITSIZE_EQ_0" BITSIZE_EQ_0
  "|- forall n. bitsize n = 0 <=> n = 0"
#eval thm' "BITSIZE_MONO" BITSIZE_MONO
  "|- forall m n. m <= n ==> bitsize m <= bitsize n"
#eval thm' "BITSIZE_MAX" BITSIZE_MAX
  "|- forall m n. bitsize (MAX m n) = MAX (bitsize m) (bitsize n)"
#eval thm' "BITSIZE_MULT_LE" BITSIZE_MULT_LE
  "|- forall m n. bitsize (m * n) <= bitsize m + bitsize n"
#eval thm' "BITSIZE_UNIQUE_EQ" BITSIZE_UNIQUE_EQ
  "|- forall n k. bitsize n = k <=> n < 2 EXP k /\\ (~(k = 0) ==> 2 EXP k <= 2 * n)"
#eval thm' "BITSIZE_MULT" BITSIZE_MULT
  "|- (forall k n. bitsize (2 EXP k * n) = (if n = 0 then 0 else k + bitsize n)) /\\ (forall k n. bitsize (n * 2 EXP k) = (if n = 0 then 0 else bitsize n + k))"
#eval thm' "BITSIZE_DIV" BITSIZE_DIV
  "|- forall n k. bitsize (n DIV 2 EXP k) = bitsize n - k"
#eval thm' "LE_BITSIZE" LE_BITSIZE
  "|- forall n k. k <= bitsize n <=> ~(k = 0) ==> 2 EXP (k - 1) <= n"

-- BITSIZE_CONV on numerals (expected values printed by real HOL Light).
#eval check "BITSIZE_CONV 0"
  (do match ← HolCore.Parser.parse_term r"bitsize 0" with
      | .ok t => BITSIZE_CONV t | .error e => pure (.error e))
  "|- bitsize 0 = 0"
#eval check "BITSIZE_CONV 1"
  (do match ← HolCore.Parser.parse_term r"bitsize 1" with
      | .ok t => BITSIZE_CONV t | .error e => pure (.error e))
  "|- bitsize 1 = 1"
#eval check "BITSIZE_CONV 11"
  (do match ← HolCore.Parser.parse_term r"bitsize 11" with
      | .ok t => BITSIZE_CONV t | .error e => pure (.error e))
  "|- bitsize 11 = 4"
#eval check "BITSIZE_CONV 255"
  (do match ← HolCore.Parser.parse_term r"bitsize 255" with
      | .ok t => BITSIZE_CONV t | .error e => pure (.error e))
  "|- bitsize 255 = 8"
#eval check "BITSIZE_CONV 256"
  (do match ← HolCore.Parser.parse_term r"bitsize 256" with
      | .ok t => BITSIZE_CONV t | .error e => pure (.error e))
  "|- bitsize 256 = 9"

-- BITSIZE_CONV fails on a non-numeral argument.
#eval mustFail "BITSIZE_CONV fail"
  (do match ← HolCore.Parser.parse_term r"bitsize n" with
      | .ok t => BITSIZE_CONV t | .error e => pure (.error e))

end B
