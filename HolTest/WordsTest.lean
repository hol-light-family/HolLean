/- File: HolTest/WordsTest.lean
Runtime test suite: Library/words.ml (HolLibrary/Words.lean, wired by
SessionLibrary/Words.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/words.ml"`, then `string_of_thm`, or the failure message).
tools/wordsdiff/check.sh compares far more structurally: all 840 theorems,
388 constants, 346 definitions, 200 conversion results and all 1,111 load
messages. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel Session SessionLibrary.Words HolTest.CommonTest

#eval ensureWords

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def check (lbl : String) (r : IO (Except String thm)) (expected : String) :
    IO Unit := do
  let got ← match ← r with
    | .ok th => pure (squash (← HolCore.Printer.string_of_thm th))
    | .error e => pure s!"FAIL {e}"
  if got == squash expected || got == expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

private unsafe def tm (s : String) : IO term := do
  match ← HolCore.Parser.parse_term s with
  | .ok t => pure t | .error e => throw (IO.userError e)

private unsafe def thm' (lbl : String) (th : thm) (expected : String) : IO Unit :=
  check lbl (pure (.ok th)) expected

private unsafe def conv (lbl : String) (c : term → IO (Except String thm)) (s expected : String) :
    IO Unit := do
  check s!"{lbl} {s}" (do c (← tm s)) expected

-- Theorems.
#eval thm' "WORD_ADD_0" WORD_ADD_0
  "|- (forall x. word_add x (word 0) = x) /\\ (forall x. word_add (word 0) x = x)"
#eval thm' "VAL_BOUND" VAL_BOUND "|- forall w. val w < 2 EXP dimindex (:N)"
#eval thm' "WORD_CTZ_EMULATION" WORD_CTZ_EMULATION
  "|- forall x. word_ctz x = dimindex (:N) - word_clz (word_and (word_not x) (word_sub x (word 1)))"
#eval thm' "BIT_WORD_SX" BIT_WORD_SX
  "|- forall x i. bit i (word_sx x) <=> i < dimindex (:N) /\\ bit (MIN i (dimindex (:M) - 1)) x"
#eval thm' "SIMD2" SIMD2
  "|- forall f xhi xlo yhi ylo. simd2 f (word_join xhi xlo) (word_join yhi ylo) = word_join (f xhi yhi) (f xlo ylo)"

-- Explicit calculation.
#eval conv "WORD_REDUCE_CONV" WORD_REDUCE_CONV
  "word_add (word_mul (word 3:byte) (word 100)) (word_xor (word 5) (word 12))"
  "|- word_add (word_mul (word 3) (word 100)) (word_xor (word 5) (word 12)) = word 53"
#eval conv "WORD_REDUCE_CONV" WORD_REDUCE_CONV "val(word_not(word 3:int16)) + 1 = 65533"
  "|- val (word_not (word 3)) + 1 = 65533 <=> 65532 + 1 = 65533"
#eval conv "WORD_REDUCE_CONV" WORD_REDUCE_CONV "word_clz(word 40:int32)"
  "|- word_clz (word 40) = 26"
#eval conv "WORD_REDUCE_CONV" WORD_REDUCE_CONV "word_popcount(word 255:int64)"
  "|- word_popcount (word 255) = 8"
#eval conv "WORD_REDUCE_CONV" WORD_REDUCE_CONV "word_bytereverse(word 4660:int16)"
  "|- word_bytereverse (word 4660) = word 13330"
#eval conv "WORD_COMPUTE_CONV" WORD_COMPUTE_CONV
  "if word_ult (word 3:byte) (word 4) then word_popcount (word 13:int16) else 0"
  "|- (if word_ult (word 3) (word 4) then word_popcount (word 13) else 0) = 3"
#eval conv "WORD_IREDUCE_CONV" WORD_IREDUCE_CONV "word_sub (word 3:byte) (word 5)"
  "|- word_sub (word 3) (word 5) = iword (-- &2)"
#eval conv "NUMBIT_CONV" NUMBIT_CONV "numbit 3 13" "|- numbit 3 13 <=> true"

-- Bits of word operations.
#eval conv "BIT_WORD_CONV" BIT_WORD_CONV "bit 7 (word_sub x y:int16)"
  "|- bit 7 (word_sub x y) <=> (bit 7 x <=> bit 7 y) <=> ~bit 6 x /\\ bit 6 y \\/ (~bit 6 x \\/ bit 6 y) /\\ bit 6 (word_sub x y)"
#eval conv "BIT_WORD_CONV" BIT_WORD_CONV "bit 3 (x:byte)" "FAIL BIT_WORD_CONV: no change"
#eval conv "VAL_EXPAND_CONV" VAL_EXPAND_CONV "val(x:(3)word)"
  "|- val x = 2 EXP 0 * bitval (bit 0 x) + 2 EXP 1 * bitval (bit 1 x) + 2 EXP 2 * bitval (bit 2 x)"
#eval conv "WORD_SIMPLE_SUBWORD_CONV" WORD_SIMPLE_SUBWORD_CONV
  "word_subword (word_join (x:int32) (y:int32):int64) (32,32):int32"
  "|- word_subword (word_join x y) (32,32) = word_subword x (0,32)"

-- Decision procedures.
#eval conv "WORD_RULE" WORD_RULE "word_add x (word_sub y x):N word = y"
  "|- word_add x (word_sub y x) = y"
#eval conv "WORD_BITWISE_RULE" WORD_BITWISE_RULE "word_and x (word_or x y):N word = x"
  "|- word_and x (word_or x y) = x"
#eval conv "WORD_ARITH" WORD_ARITH "val(x:int32) < 2 EXP 32" "|- val x < 2 EXP 32"
#eval conv "WORD_BLAST" WORD_BLAST
  "!x:int16. word_ushr (word_shl x 8) 8 = word_and x (word 255)"
  "|- forall x. word_ushr (word_shl x 8) 8 = word_and x (word 255)"
#eval conv "WORD_BLAST" WORD_BLAST "!x:byte. word_add x x = x"
  "FAIL WORD_BLAST `forall x. word_add x x = x`: TAC_PROOF: Unsolved goals"
#eval conv "BITBLAST_RULE" BITBLAST_RULE "!x y:byte. word_and x y = word_and y x"
  "|- forall x y. word_and x y = word_and y x"
#eval conv "BITBLAST_RULE" BITBLAST_RULE
  "!x y:(4)word. val(word_add x y) = (val x + val y) MOD 16" "FAIL EQT_ELIM"

-- Word forms of arithmetic.
#eval conv "WORDIFY_CONV" WORDIFY_CONV "val(x:byte) * 3 + bitval b"
  "|- val x * 3 + bitval b = val (word_add (word_zx (word_mul (word_zx x) (word_zx (word 3)))) (word_zx (word (bitval b))))"
#eval conv "IWORDIFY_ATOM_CONV" IWORDIFY_ATOM_CONV "ival(x:byte) < ival(y:int16) + -- &5"
  "|- ival x < ival y + -- &5 <=> bit 16 (word_sx x) /\\ ~bit 16 (word_add (word_sx y) (word_sx (word 11))) \\/ (bit 16 (word_sx x) \\/ ~bit 16 (word_add (word_sx y) (word_sx (word 11)))) /\\ bit 16 (word_sub (word_sx x) (word_add (word_sx y) (word_sx (word 11))))"
