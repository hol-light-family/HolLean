/- File: HolTest/CardTest.lean
Runtime test suite: Library/card.ml (HolLibrary/Card.lean, wired by
SessionLibrary/Card.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/card.ml"`, then `string_of_thm`, or the failure message).
tools/carddiff/check.sh compares far more structurally: all 289 theorems,
the constants and definitions and all 1,285 load messages. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.Card.ensureCard

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

namespace C
open Session SessionLibrary.Card HolLight.Syntax

#eval thm' "sum_DISTINCT" sum_DISTINCT
  "|- forall a a'. ~(INL a = INR a')"
#eval thm' "sum_CASES" sum_CASES
  "|- forall x. (exists a. x = INL a) \\/ (exists a. x = INR a)"
#eval thm' "TARSKI_SET" TARSKI_SET
  "|- forall f. (forall s t. s SUBSET t ==> f s SUBSET f t) ==> (exists s. f s = s)"
#eval thm' "CARD_LE_ANTISYM" CARD_LE_ANTISYM
  "|- forall s t. s <=_c t /\\ t <=_c s <=> s =_c t"
#eval thm' "CARD_LE_TOTAL" CARD_LE_TOTAL
  "|- forall s t. s <=_c t \\/ t <=_c s"
#eval thm' "WF_CARD_LT" WF_CARD_LT
  "|- WF (<_c)"
#eval thm' "UNION_LE_ADD_C" UNION_LE_ADD_C
  "|- forall s t. s UNION t <=_c s +_c t"
#eval thm' "CARD_SQUARE_INFINITE" CARD_SQUARE_INFINITE
  "|- forall k. INFINITE k ==> k *_c k =_c k"
#eval thm' "CARD_ADD_ABSORB_LEFT" CARD_ADD_ABSORB_LEFT
  "|- forall s t. INFINITE t /\\ s <=_c t ==> s +_c t =_c t"
#eval thm' "CANTOR_THM" CANTOR_THM
  "|- forall s. s <_c {t | t SUBSET s}"
#eval thm' "COUNTABLE_UNIONS" COUNTABLE_UNIONS
  "|- forall A. COUNTABLE A /\\ (forall s. s IN A ==> COUNTABLE s) ==> COUNTABLE (UNIONS A)"
#eval thm' "COUNTABLE_AS_INJECTIVE_IMAGE_SUBSET" COUNTABLE_AS_INJECTIVE_IMAGE_SUBSET
  "|- forall s. COUNTABLE s <=> (exists f k. s = IMAGE f k /\\ (forall m n. m IN k /\\ n IN k /\\ f m = f n ==> m = n))"
#eval thm' "CARD_EQ_INT_NUM" CARD_EQ_INT_NUM
  "|- (:int) =_c (:num)"
#eval thm' "COUNTABLE_CART" COUNTABLE_CART
  "|- forall P. (forall i. 1 <= i /\\ i <= dimindex (:N) ==> COUNTABLE {x | P i x}) ==> COUNTABLE {v | forall i. 1 <= i /\\ i <= dimindex (:N) ==> P i (v$i)}"
#eval thm' "COUNTABLE_UNION_OF_ASCENDING" COUNTABLE_UNION_OF_ASCENDING
  "|- forall P s. P {} /\\ (forall t u. P t /\\ P u ==> P (t UNION u)) ==> ((COUNTABLE UNION_OF P) s <=> (exists t. (forall n. P (t n)) /\\ (forall n. t n SUBSET t (SUC n)) /\\ UNIONS {t n | n IN (:num)} = s))"
#eval thm' "CARD_EQ_LIST" CARD_EQ_LIST
  "|- INFINITE (:A) ==> (:(A)list) =_c (:A)"
#eval thm' "CARD_EQ_REAL" CARD_EQ_REAL
  "|- (:real) =_c (:num->bool)"
#eval thm' "UNCOUNTABLE_REAL" UNCOUNTABLE_REAL
  "|- ~COUNTABLE (:real)"
#eval thm' "exp_c" exp_c
  "|- forall s t. s ^_c t = {f | (forall x. x IN t ==> f x IN s) /\\ (forall x. ~(x IN t) ==> f x = (@y. false))}"
#eval thm' "CARD_EXP_C" CARD_EXP_C
  "|- forall s t. FINITE s /\\ FINITE t ==> CARD (s ^_c t) = CARD s EXP CARD t"
#eval thm' "CARD_EQ_LIMITED_POWERSET" CARD_EQ_LIMITED_POWERSET
  "|- forall s t. INFINITE s ==> (if t <=_c s then {k | k SUBSET s /\\ k <=_c t} =_c s ^_c t else {k | k SUBSET s /\\ k <=_c t} =_c (:bool) ^_c s)"
#eval thm' "CARD_EQ_REAL_SEQUENCES" CARD_EQ_REAL_SEQUENCES
  "|- (:num->real) =_c (:real)"
#eval thm' "FINITE_CARTESIAN_PRODUCT" FINITE_CARTESIAN_PRODUCT
  "|- forall s k. FINITE (cartesian_product k s) <=> cartesian_product k s = {} \\/ FINITE {i | i IN k /\\ ~(exists a. s i SUBSET {a})} /\\ (forall i. i IN k ==> FINITE (s i))"

-- TRANS_CHAIN_TAC in a proof, and a chain that leaves a goal; the
-- cardinal-arithmetic infixes parse with HOL Light's precedences.
#eval check "TRANS_CHAIN_TAC"
  (HolLight.prove r"!s:A->bool t:B->bool u:C->bool v:D->bool. s =_c t /\ t =_c u /\ u =_c v ==> s =_c v"
     (REPEAT STRIP_TAC THEN TRANS_CHAIN_TAC CARD_EQ_TRANS [([[t:B->bool]]), ([[u:C->bool]])])).run
  "|- forall s t u v. s =_c t /\\ t =_c u /\\ u =_c v ==> s =_c v"
#eval check "TRANS_CHAIN_TAC fail"
  (HolLight.prove r"!s:A->bool t:B->bool. s =_c t ==> t =_c s"
     (REPEAT STRIP_TAC THEN TRANS_CHAIN_TAC CARD_EQ_TRANS [([[s:A->bool]])])).run
  "FAIL TAC_PROOF: Unsolved goals"
#eval check "parse ^_c" (do
    match ← HolCore.Parser.parse_term "(s:A->bool) ^_c (t:B->bool) +_c (u:C->bool) *_c (v:D->bool)" with
    | .ok t => pure (.ok (HolCore.Kernel.REFL t)) | .error e => pure (.error e))
  "|- s ^_c t +_c u *_c v = s ^_c t +_c u *_c v"

end C
