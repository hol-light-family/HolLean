/- File: HolTest/FragTest.lean
Runtime test suite: Library/frag.ml (HolLibrary/Frag.lean, wired by
SessionLibrary/Frag.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/frag.ml"`, `set_margin 1000`, then `string_of_thm`).
tools/fragdiff/check.sh compares far more structurally.  The theorems whose
printed form contains `?NNN` invented type variables (FRAG_SUPPORT_0,
MONOIDAL_FRAG_ADD) are omitted here; the FRAG_MODULE rule is tested on terms
given a concrete `:(num)frag` type so its output prints cleanly. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.Frag.ensureFrag

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

namespace F
open Session SessionLibrary.Frag HolLight.Syntax

#eval thm' "frag_tybij" frag_tybij
  "|- (forall a. mk_frag (dest_frag a) = a) /\\ (forall r. FINITE {x | ~(r x = &0)} <=> dest_frag (mk_frag r) = r)"
#eval thm' "FRAG_EQ" FRAG_EQ
  "|- forall c1 c2. c1 = c2 <=> dest_frag c1 = dest_frag c2"
#eval thm' "DEST_FRAG_OF" DEST_FRAG_OF
  "|- forall c. dest_frag (frag_of c) = (\\a. if a = c then &1 else &0)"
#eval thm' "DEST_FRAG_ADD" DEST_FRAG_ADD
  "|- forall x y. dest_frag (frag_add x y) = (\\a. dest_frag x a + dest_frag y a)"
#eval thm' "FRAG_OF_NONZERO" FRAG_OF_NONZERO
  "|- forall a. ~(frag_of a = frag_0)"
#eval thm' "FRAG_SUPPORT_OF" FRAG_SUPPORT_OF
  "|- forall a. frag_support (frag_of a) = {a}"
#eval thm' "NEUTRAL_FRAG_ADD" NEUTRAL_FRAG_ADD
  "|- neutral frag_add = frag_0"
#eval thm' "FRAG_EXTEND_OF" FRAG_EXTEND_OF
  "|- forall f a. frag_extend f (frag_of a) = f a"
#eval thm' "FRAG_EXTEND_ADD" FRAG_EXTEND_ADD
  "|- forall f x y. frag_extend f (frag_add x y) = frag_add (frag_extend f x) (frag_extend f y)"
#eval thm' "FRAG_EXPANSION" FRAG_EXPANSION
  "|- forall x. x = frag_extend frag_of x"
#eval thm' "FRAG_INDUCTION" FRAG_INDUCTION
  "|- forall P s. P frag_0 /\\ (forall a. a IN s ==> P (frag_of a)) /\\ (forall c1 c2. P c1 /\\ P c2 ==> P (frag_sub c1 c2)) ==> (forall c. frag_support c SUBSET s ==> P c)"
#eval thm' "FRAG_EXTEND_COMPOSE" FRAG_EXTEND_COMPOSE
  "|- forall f g c. frag_extend f (frag_extend (frag_of o g) c) = frag_extend (f o g) c"

-- The FRAG_MODULE rule, on terms given a concrete `:(num)frag` type so the
-- printed form has no invented type variables.
#eval check "FRAG_MODULE comm"
  (do match ← HolCore.Parser.parse_term r"frag_add (x:(num)frag) y = frag_add y x" with
      | .ok t => FRAG_MODULE t
      | .error e => pure (.error e))
  "|- frag_add x y = frag_add y x"
#eval check "FRAG_MODULE sub"
  (do match ← HolCore.Parser.parse_term r"frag_sub (x:(num)frag) x = frag_0" with
      | .ok t => FRAG_MODULE t
      | .error e => pure (.error e))
  "|- frag_sub x x = frag_0"
#eval check "FRAG_MODULE cmul0"
  (do match ← HolCore.Parser.parse_term r"frag_cmul (&0) (x:(num)frag) = frag_0" with
      | .ok t => FRAG_MODULE t
      | .error e => pure (.error e))
  "|- frag_cmul (&0) x = frag_0"

end F
