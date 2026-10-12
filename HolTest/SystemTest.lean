/- File: HolTest/SystemTest.lean
Runtime test suite: system.ml - miscellaneous system setup, and the formatter
(`HolCore.System`, a translation of OCaml's Format) used by the printers.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set.

HOL Light's system.ml is almost entirely platform glue with no testable
analogue here.  The formatter is tested against OCaml 5's Format: every expected
string below is what OCaml prints for the same calls.  (It was also checked on
17,000 random box/break programs, byte for byte.) -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

open HolCore.System

/-- Compare a rendered formatter run against an expected string. -/
private def fmtCheck (lbl : String) (got expected : String) : IO Unit := do
  if got == expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={repr got} expected={repr expected}"

/- ---------------------------------------------------------------------- -/
/- printString / printAs: buffer append and column accounting.  `printAs`  -/
/- appends its full string but counts it as width `n` (n = 0 for a         -/
/- zero-width escape), so the visible buffer still contains all the text.  -/
/- ---------------------------------------------------------------------- -/

#eval fmtCheck "printString plain" (Fmt.run 120 (Fmt.printString "hello")) "hello"

#eval fmtCheck "printAs zero-width then text"
  (Fmt.run 120 (do Fmt.printAs 0 "XYZ"; Fmt.printString "!")) "XYZ!"

/- ---------------------------------------------------------------------- -/
/- Expected values below are OCaml 5's Format on the same calls (a buffer   -/
/- formatter with max_boxes 100 and the given margin, as print_to_string). -/
/- A break in a box fits on the line; a break directly in the system box   -/
/- (never closed, so its size is never known) always splits.              -/
/- ---------------------------------------------------------------------- -/

#eval fmtCheck "printSpace within margin, in a box"
  (Fmt.run 120 (do Fmt.openBox 0; Fmt.printString "a"; Fmt.printSpace; Fmt.printString "b"
                   Fmt.closeBox)) "a b"
#eval fmtCheck "printSpace directly in the system box splits"
  (Fmt.run 120 (do Fmt.printString "a"; Fmt.printSpace; Fmt.printString "b")) "a\nb"

/- ---------------------------------------------------------------------- -/
/- printBreak PAST the margin breaks to a new line indented to the current  -/
/- box level plus the break's own indent.  With no open box the box level   -/
/- is 0, so the continuation starts at column 0.  (margin = 3, and "abcd"   -/
/- already puts the column at 4 > 3.)                                       -/
/- ---------------------------------------------------------------------- -/

#eval fmtCheck "printBreak past margin, no box"
  (Fmt.run 3 (do Fmt.printString "abcd"; Fmt.printBreak 1 0; Fmt.printString "z"))
  "abcd\nz"

/- ---------------------------------------------------------------------- -/
/- An unclosed box's size is unknown until the flush, so its break is      -/
/- decided then; OCaml keeps "abcd z" on one line here.                    -/
/- ---------------------------------------------------------------------- -/

#eval fmtCheck "printBreak in an unclosed box (OCaml keeps one line)"
  (Fmt.run 3 (do Fmt.openBox 2; Fmt.printString "abcd"; Fmt.printBreak 1 0
                 Fmt.printString "z"))
  "abcd z"

/- ---------------------------------------------------------------------- -/
/- forceNewline always breaks, indenting to the current box level          -/
/- regardless of the margin.  `openBox 3` at column 0 gives box level 3.    -/
/- ---------------------------------------------------------------------- -/

#eval fmtCheck "forceNewline indents to box level"
  (Fmt.run 120 (do Fmt.openBox 3; Fmt.printString "x"; Fmt.forceNewline
                   Fmt.printString "y"))
  "x\n   y"

/- ---------------------------------------------------------------------- -/
/- pp_print_num renders a numeral.  `string_of_num` prints the -/
/- integer value (Lib.string_of_num = toString n.num), so 42 renders "42". -/
/- ---------------------------------------------------------------------- -/

#eval fmtCheck "pp_print_num 42" (Fmt.run 78 (pp_print_num (42 : Rat))) "42"

#eval fmtCheck "pp_print_num 0" (Fmt.run 78 (pp_print_num (0 : Rat))) "0"

/- ---------------------------------------------------------------------- -/
/- pp_print_fpf is the trivial `<func>` printer for finite partial          -/
/- functions (matching HOL Light's `<fun>`-style opaque printing).          -/
/- ---------------------------------------------------------------------- -/

#eval fmtCheck "pp_print_fpf prints <func>"
  (Fmt.run 78 (pp_print_fpf (HolCore.Lib.undefined : Func Nat Nat))) "<func>"
