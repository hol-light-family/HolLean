/- File: HolTest/WordAutomataTest.lean
Runtime test suite: Library/word_automata.ml (HolLibrary/WordAutomata.lean, wired by
SessionLibrary/WordAutomata.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/word_automata.ml"`, then `string_of_thm`, newlines joined).
tools/word_automatadiff/check.sh compares every theorem structurally and as
printed, and the constants and definitions after loading.  Theorems that
print with `?NNN` invented type variables are omitted here. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.WordAutomata.ensureWordAutomata

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

namespace T
open Session SessionLibrary.WordAutomata HolLight.Syntax

#eval thm' "OVERAPPROXIMATE_REACHABLE" OVERAPPROXIMATE_REACHABLE
  "|- forall init step final invariant.        (forall s. init s ==> invariant s) /\\        (forall s s'. invariant s /\\ step s s' ==> invariant s') /\\        (forall s. invariant s ==> final s)        ==> (forall s s'. init s /\\ RTC step s s' ==> final s')"
#eval thm' "WORD_SHLADD" WORD_SHLADD
  "|- forall x b. word_shladd x b = word_add (word_shl x 1) (word (bitval b))"
#eval thm' "WORD_SHLADD_0" WORD_SHLADD_0
  "|- forall x. word_shladd x false = word_shl x 1"
#eval thm' "WORD_USHR_SHLADD" WORD_USHR_SHLADD
  "|- forall x y.        word_ushr x 1 = y <=>        word_and word_INT_MIN y = word 0 /\\ word_shladd y (bit 0 x) = x"
#eval thm' "DEFINE_WORD_INT_MIN" DEFINE_WORD_INT_MIN
  "|- ~(word_INT_MIN = word 0) /\\ word_shladd word_INT_MIN false = word 0"
#eval thm' "IVAL_LT_ELIM_THM" IVAL_LT_ELIM_THM
  "|- forall x y.        ival x < ival y <=>        ~(word_and word_INT_MIN          (word_or (word_and x (word_not y))          (word_and (word_not (word_xor x y)) (word_sub x y))) =          word 0)"
#eval thm' "CONJ_WORD_EQ_0" CONJ_WORD_EQ_0
  "|- forall x y. x = word 0 /\\ y = word 0 <=> word_or x y = word 0"
#eval thm' "LSB_CARRYING" LSB_CARRYING
  "|- (forall x z. word_neg x = z ==> (bit 0 z <=> bit 0 x)) /\\    (forall x y z. word_add x y = z ==> (bit 0 z <=> ~(bit 0 x <=> bit 0 y))) /\\    (forall x y z. word_sub x y = z ==> (bit 0 z <=> ~(bit 0 x <=> bit 0 y))) /\\    (forall x z b. word_shladd x b = z ==> (bit 0 z <=> b)) /\\    (forall a b. a = b ==> (bit 0 a <=> bit 0 b))"
#eval thm' "WORD_MUL_SHLADD" WORD_MUL_SHLADD
  "|- forall x y.        word_mul (word_shladd x true) y =        word_add (word_shladd (word_mul x y) false) y /\\        word_mul y (word_shladd x true) =        word_add (word_shladd (word_mul y x) false) y /\\        word_mul (word_shladd x false) y = word_shladd (word_mul x y) false /\\        word_mul y (word_shladd x false) = word_shladd (word_mul y x) false"

-- The conversions on sample inputs (expected values printed by HOL Light;
-- a failure is expected as `FAIL <message>`).
#eval check "WORD_AUTO_RULE !(x:(N)word) (y:(N)word). word_add (word_add x (word 1)) (word_not y) = word_sub x y" (do
    match ← HolCore.Parser.parse_term "!(x:(N)word) (y:(N)word). word_add (word_add x (word 1)) (word_not y) = word_sub x y" with
    | .ok tm => WORD_AUTO_RULE tm
    | .error e => pure (.error e))
  "|- forall x y. word_add (word_add x (word 1)) (word_not y) = word_sub x y"
#eval check "WORD_AUTO_RULE !x:N word. word_and (word_not x) (word_sub x (word 1)) = word_not (word_or x (word_neg x))" (do
    match ← HolCore.Parser.parse_term "!x:N word. word_and (word_not x) (word_sub x (word 1)) = word_not (word_or x (word_neg x))" with
    | .ok tm => WORD_AUTO_RULE tm
    | .error e => pure (.error e))
  "|- forall x.        word_and (word_not x) (word_sub x (word 1)) =        word_not (word_or x (word_neg x))"
#eval check "WORD_AUTO_RULE !x:N word. word_and x (word_not(word 1)) = word 0 <=> x = word 0 \\/ x = word 1" (do
    match ← HolCore.Parser.parse_term "!x:N word. word_and x (word_not(word 1)) = word 0 <=> x = word 0 \\/ x = word 1" with
    | .ok tm => WORD_AUTO_RULE tm
    | .error e => pure (.error e))
  "|- forall x.        word_and x (word_not (word 1)) = word 0 <=> x = word 0 \\/ x = word 1"
#eval check "WORD_AUTO_RULE word_xor x y:S word  = word_sub (word_or x y) (word_and x y)" (do
    match ← HolCore.Parser.parse_term "word_xor x y:S word  = word_sub (word_or x y) (word_and x y)" with
    | .ok tm => WORD_AUTO_RULE tm
    | .error e => pure (.error e))
  "|- word_xor x y = word_sub (word_or x y) (word_and x y)"
#eval check "WORD_AUTO_RULE word_add x y:M word = word_sub (word_shl (word_or x y) 1) (word_xor x y)" (do
    match ← HolCore.Parser.parse_term "word_add x y:M word = word_sub (word_shl (word_or x y) 1) (word_xor x y)" with
    | .ok tm => WORD_AUTO_RULE tm
    | .error e => pure (.error e))
  "|- word_add x y = word_sub (word_shl (word_or x y) 1) (word_xor x y)"
#eval check "WORD_AUTO_RULE word_and (x:int32) x = x" (do
    match ← HolCore.Parser.parse_term "word_and (x:int32) x = x" with
    | .ok tm => WORD_AUTO_RULE tm
    | .error e => pure (.error e))
  "|- word_and x x = x"
#eval check "WORD_AUTO_RULE !(x:N word) (y:M word). word_and x x = x /\\ word_or y y = y" (do
    match ← HolCore.Parser.parse_term "!(x:N word) (y:M word). word_and x x = x /\\ word_or y y = y" with
    | .ok tm => WORD_AUTO_RULE tm
    | .error e => pure (.error e))
  "FAIL WORD_AUTO_TAC: Multiple generic types not supported"
#eval check "PURE_WORD_AUTO_RULE !x:N word. word_xor x x = word 0" (do
    match ← HolCore.Parser.parse_term "!x:N word. word_xor x x = word 0" with
    | .ok tm => PURE_WORD_AUTO_RULE tm
    | .error e => pure (.error e))
  "|- forall x. word_xor x x = word 0"
#eval check "WORD_AUTO_RULE !x:N word. word_add x x = x" (do
    match ← HolCore.Parser.parse_term "!x:N word. word_add x x = x" with
    | .ok tm => WORD_AUTO_RULE tm
    | .error e => pure (.error e))
  "FAIL WORD_AUTO_TAC: Sanity check for size 4 failed!"

end T
