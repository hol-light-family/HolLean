/- File: HolTest/BitMatchTest.lean
Runtime test suite: Library/bitmatch.ml (HolLibrary/BitMatch.lean, wired by
SessionLibrary/BitMatch.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/bitmatch.ml"`, `set_margin 1000`, then `string_of_thm`, the
string printers, or the failure message).  tools/bitmatchdiff/check.sh
compares far more structurally: all 30 theorems, 11 conversion results, the
constants and definitions and all load messages. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.BitMatch.ensureBitMatch

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

/-- An error as HOL Light's test printed it: `INVALID m` for
    `Invalid_argument m`, `FAIL m` for `Failure m`. -/
private def errStr (e : String) : String :=
  if HolLibrary.BitMatch.isInvalidArg e then
    "INVALID " ++ (e.drop HolLibrary.BitMatch.invalidArgPrefix.length).toString
  else s!"FAIL {e}"

private def report (lbl got expected : String) : IO Unit :=
  if got == squash expected || got == expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

private unsafe def check (lbl : String) (r : IO (Except String thm)) (expected : String) :
    IO Unit := do
  let got ← match ← r with
    | .ok th => pure (squash (← HolCore.Printer.string_of_thm th))
    | .error e => pure (errStr e)
  report lbl got expected

private unsafe def thm' (lbl : String) (th : thm) (expected : String) : IO Unit :=
  check lbl (pure (.ok th)) expected

/-- `REFL` of a parsed quotation: a parse and print round trip. -/
private unsafe def parsed (s : String) : IO (Except String thm) := do
  match ← HolCore.Parser.parse_term s with
  | .ok t => pure (.ok (REFL t))
  | .error e => pure (.error e)

/-- A conversion on a parsed quotation. -/
private unsafe def onTerm (c : term → IO (Except String thm)) (s : String) :
    IO (Except String thm) := do
  match ← HolCore.Parser.parse_term s with
  | .ok t => c t
  | .error e => pure (.error e)

/-- A string printer on a parsed quotation. -/
private unsafe def str (lbl : String) (f : term → ExceptT String IO String) (s : String)
    (expected : String) : IO Unit := do
  let got ← match ← HolCore.Parser.parse_term s with
    | .ok t => do
      match ← (f t).run with
      | .ok r => pure r
      | .error e => pure (errStr e)
    | .error e => pure (errStr e)
  if got == expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

namespace B
open Session SessionLibrary.BitMatch HolLight.Syntax

#eval thm' "NILPAT_pat_set" NILPAT_pat_set
  "|- forall s. pat_set (BITPAT []) s <=> s = 0"
#eval thm' "CONSPAT_pat_set" CONSPAT_pat_set
  "|- forall s. pat_set (CONSPAT p a) s <=> (exists t. pat_set p t /\\ s = val a + 2 EXP dimindex (:N) * t)"
#eval thm' "BIT0_WORD1" BIT0_WORD1
  "|- bit 0 (word1 b) <=> b"
#eval thm' "WORD1_ODD" WORD1_ODD
  "|- word1 (ODD n) = word n"
#eval thm' "BITMATCH_SEQPATTERN" BITMATCH_SEQPATTERN
  "|- _BITMATCH e (_SEQPATTERN c cs) = (if exists y. c (val e) y then _BITMATCH e c else _BITMATCH e cs)"
#eval thm' "CONSPAT_word1_inverts" CONSPAT_word1_inverts
  "|- bitpat_inverts (CONSPAT p (word1 b)) (bit 0 o word) b"
#eval thm' "bitpat_inverts_comp" bitpat_inverts_comp
  "|- bitpat_inverts p f x ==> bitpat_inverts p (g o f) (g x)"

-- The quotation parsers and the printers.
#eval check "parse bitmatch"
  (parsed "bitmatch (x:(4)word) with | [a:2; 0b01:2] -> val a + 1 | [0b00:2; b:2] -> val b | _ -> 7")
  "|- (bitmatch x with [a:2; 1:2] -> val a + 1 | [0:2; b:2] -> val b | _ -> 7) = (bitmatch x with [a:2; 1:2] -> val a + 1 | [0:2; b:2] -> val b | _ -> 7)"
#eval check "parse BITPAT"
  (parsed "pat_set (BITPAT [T; x:2; 0b1:1]) n")
  "|- pat_set (BITPAT [true; x:2; 1:1]) n <=> pat_set (BITPAT [true; x:2; 1:1]) n"
#eval str "string_of_bitpat" string_of_bitpat "BITPAT [T; x:2; 0b1:1]"
  "(BITPAT [true; x:2; 1:1])"
#eval str "string_of_bitmatch" string_of_bitmatch "bitmatch (x:(2)word) with | [T; y] -> y | _ -> F"
  "(bitmatch x with [true; y] -> y | _ -> false)"

-- The conversions.
#eval check "BITMATCH_CONV"
  (onTerm BITMATCH_CONV "bitmatch (word 13:(4)word) with | [a:2; 0b01:2] -> val a + 1 | [0b00:2; b:2] -> val b | _ -> 7")
  "|- (bitmatch word 13 with [a:2; 1:2] -> val a + 1 | [0:2; b:2] -> val b | _ -> 7) = val (word 3) + 1"
#eval check "BITMATCH_CONV fail"
  (onTerm BITMATCH_CONV "bitmatch (word 6:(4)word) with | [a:2; 0b01:2] -> val a + 1 | [0b00:2; b:2] -> val b | _ -> 7")
  "FAIL inst_bitpat_numeral: number does not match pattern"
#eval check "BITMATCH_SEQ_CONV"
  (onTerm BITMATCH_SEQ_CONV "bitmatch (word 2:(2)word) with | [T; x] -> x | [y; F] -> y | _ -> T")
  "|- (bitmatch word 2 with [true; x] -> x | [y; false] -> y | _ -> true) <=> false"
#eval check "BM_IF_CONV"
  (onTerm BM_IF_CONV "bitmatch (e:(3)word) with | [x; T; y] -> x /\\ y | [F; F; F] -> F | _ -> T")
  "|- (bitmatch e with [x; true; y] -> x /\\ y | [false; false; false] -> false | _ -> true) <=> (if bit 1 e then (bitmatch e with [x; true; y] -> x /\\ y | _ -> true) else (bitmatch e with [false; false; false] -> false | _ -> true))"
#eval check "bitpat_irrefutable_thm"
  (onTerm bitpat_irrefutable_thm "?a b. pat_set (BITPAT [a:2; b]) (val (e:(3)word))")
  "|- exists a b. pat_set (BITPAT [a:2; b]) (val e)"
#eval check "bm_check_disjointness"
  (onTerm (fun t => do
      match ← (bm_check_disjointness t).run with
      | .ok () => pure (.ok Session.TRUTH)
      | .error e => pure (.error e))
    "bitmatch (x:(2)word) with | [T; x] -> T | [y; T] -> T")
  "INVALID Pattern number 1 and pattern number 0 overlap"

-- The case tactics.
#eval check "BITMATCH_ASM_CASES_TAC"
  (HolLight.prove r"!e:(2)word. (bitmatch e with | [T; x] -> x | [F; y] -> T) \/ T"
     (GEN_TAC THEN BITMATCH_ASM_CASES_TAC THEN REWRITE_TAC [])).run
  "|- forall e. (bitmatch e with [true; x] -> x | [false; y] -> true) \\/ true"
#eval check "BITMATCH_CASES_TAC"
  (HolLight.prove r"!e:(2)word. (bitmatch e with | [T; x] -> T | [F; y] -> T) = T"
     (GEN_TAC THEN BITMATCH_CASES_TAC THEN REWRITE_TAC [])).run
  "FAIL TAC_PROOF: Unsolved goals"

-- bitpat_matches: `none` if the pattern matches, else the first bit that differs.
#eval do
  let p ← HolCore.Parser.parse_term "BITPAT [T; x:2; 0b1:1]"
  match p with
  | .error e => IO.println s!"bitpat_matches -> MISMATCH {e}"
  | .ok p =>
    let r9 := (bitpat_matches p 9).toOption
    let r10 := (bitpat_matches p 10).toOption
    if r9 == some none && r10 == some (some 0) then IO.println "bitpat_matches -> OK"
    else IO.println "bitpat_matches -> MISMATCH"

end B
