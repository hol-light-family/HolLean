/- File: HolTest/LlistTest.lean
Runtime test suite: Library/llist.ml (HolLibrary/Llist.lean, wired by
SessionLibrary/Llist.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/llist.ml"`, then `string_of_thm`, newlines joined).
tools/llistdiff/check.sh compares every theorem structurally and as
printed, and the constants and definitions after loading.  Theorems that
print with `?NNN` invented type variables are omitted here. -/

import HolTest.CommonTest
import SessionLibrary.Llist

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.Llist.ensureLlist

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
open Session SessionLibrary.Llist HolLight.Syntax

#eval thm' "THE" THE
  "|- THE (SOME x) = x"
#eval thm' "OPTION_MAP_ID" OPTION_MAP_ID
  "|- forall x. OPTION_MAP (\\a. a) x = x"
#eval thm' "LLIST_OF_LIST_NEQ_SEQ" LLIST_OF_LIST_NEQ_SEQ
  "|- forall l f. ~(llist_of_list l = llist_of_seq f)"
#eval thm' "LLIST_OF_LIST" LLIST_OF_LIST
  "|- llist_of_list [] = LNIL /\\    (forall h t. llist_of_list (CONS h t) = LCONS h (llist_of_list t))"
#eval thm' "NOT_LCONS_LNIL" NOT_LCONS_LNIL
  "|- forall h t. ~(LCONS h t = LNIL)"
#eval thm' "LTL" LTL
  "|- LTL LNIL = LNIL /\\ (forall h t. LTL (LCONS h t) = t)"
#eval thm' "LCOREC" LCOREC
  "|- forall p e h t x.        LCOREC p e h t x =        (if p x then e x else LCONS (h x) (LCOREC p e h t (t x)))"
#eval thm' "LLIST_COINDUCT" LLIST_COINDUCT
  "|- forall R.        (forall l1 l2.             R l1 l2             ==> l1 = LNIL /\\ l2 = LNIL \\/                 (exists h t1 t2.                      l1 = LCONS h t1 /\\ l2 = LCONS h t2 /\\ R t1 t2))        ==> (forall l1 l2. R l1 l2 ==> l1 = l2)"
#eval thm' "list_of_llist" list_of_llist
  "|- forall l. list_of_llist (llist_of_list l) = l"
#eval thm' "LFINITE_LTL" LFINITE_LTL
  "|- forall l. LFINITE (LTL l) <=> LFINITE l"
#eval thm' "NOT_LFINITE_COINDUCT" NOT_LFINITE_COINDUCT
  "|- forall P.        (forall l. P l ==> (exists h t. l = LCONS h t /\\ P t))        ==> (forall l. P l ==> ~LFINITE l)"
#eval thm' "LMAP" LMAP
  "|- (forall f. LMAP f LNIL = LNIL) /\\    (forall f h t. LMAP f (LCONS h t) = LCONS (f h) (LMAP f t))"
#eval thm' "LMAP_EQ_LNIL" LMAP_EQ_LNIL
  "|- forall f l. LMAP f l = LNIL <=> l = LNIL"
#eval thm' "LAPPEND_ASSOC" LAPPEND_ASSOC
  "|- forall l1 l2 l3. LAPPEND l1 (LAPPEND l2 l3) = LAPPEND (LAPPEND l1 l2) l3"
#eval thm' "LAPPEND_EQ_LNIL" LAPPEND_EQ_LNIL
  "|- forall l1 l2. LAPPEND l1 l2 = LNIL <=> l1 = LNIL /\\ l2 = LNIL"
#eval thm' "LTAKE_LDROP" LTAKE_LDROP
  "|- forall n l. LAPPEND (llist_of_list (LTAKE n l)) (LDROP n l) = l"
#eval thm' "LDROP_LLIST_OF_SEQ" LDROP_LLIST_OF_SEQ
  "|- forall n f. LDROP n (llist_of_seq f) = llist_of_seq (\\i. f (i + n))"
#eval thm' "SET_OF_LLIST_LLIST_OF_LIST" SET_OF_LLIST_LLIST_OF_LIST
  "|- forall l. set_of_llist (llist_of_list l) = set_of_list l"
#eval thm' "LALL_SET_OF_LLIST" LALL_SET_OF_LLIST
  "|- forall P l. LALL P l <=> (forall x. x IN set_of_llist l ==> P x)"
#eval thm' "LALL_LMAP" LALL_LMAP
  "|- forall P f l. LALL P (LMAP f l) <=> LALL (P o f) l"
#eval thm' "LFIRST_RULES" LFIRST_RULES
  "|- forall P.        (forall h t. P h ==> LFIRST P (LCONS h t) (LCONS h t)) /\\        (forall h t l. ~P h /\\ LFIRST P t l ==> LFIRST P (LCONS h t) l)"
#eval thm' "LFIRST_LCONS" LFIRST_LCONS
  "|- forall P l l'. LFIRST P l l' ==> (exists h t. l' = LCONS h t /\\ P h)"
#eval thm' "LFIRST_LCONS_P" LFIRST_LCONS_P
  "|- forall P h t. P h ==> lfirst P (LCONS h t) = LCONS h t"
#eval thm' "LFILTER_LAPPEND" LFILTER_LAPPEND
  "|- forall P l1 l2.        LFINITE l1        ==> LFILTER P (LAPPEND l1 l2) = LAPPEND (LFILTER P l1) (LFILTER P l2)"
#eval thm' "LFLATTEN_DEF" LFLATTEN_DEF
  "|- LFLATTEN =    LUNFOLD (\\ls. ~LEXISTS (\\l. ~(l = LNIL)) ls)    (\\ls. LHD (LHD (lfirst (\\l. ~(l = LNIL)) ls)))    (\\ls.         LCONS (LTL (LHD (lfirst (\\l. ~(l = LNIL)) ls)))         (LTL (lfirst (\\l. ~(l = LNIL)) ls)))"
#eval thm' "LMAP_LFLATTEN" LMAP_LFLATTEN
  "|- forall f ls. LMAP f (LFLATTEN ls) = LFLATTEN (LMAP (LMAP f) ls)"
#eval thm' "LALL2_DEF" LALL2_DEF
  "|- (LALL2 R (llist_of_list l1) (llist_of_list l2) <=> ALL2 R l1 l2) /\\    (LALL2 R (llist_of_list l1) (llist_of_seq g) <=> false) /\\    (LALL2 R (llist_of_seq f) (llist_of_list l2) <=> false) /\\    (LALL2 R (llist_of_seq f) (llist_of_seq g) <=> (forall n. R (f n) (g n)))"
#eval thm' "MONO_LALL2" MONO_LALL2
  "|- (forall x y. P x y ==> Q x y) ==> LALL2 P l l' ==> LALL2 Q l l'"
#eval thm' "LPREFIX_TRANS" LPREFIX_TRANS
  "|- forall l1 l2 l3. LPREFIX l1 l2 /\\ LPREFIX l2 l3 ==> LPREFIX l1 l3"
#eval thm' "LPREFIX_CHAIN_LUB" LPREFIX_CHAIN_LUB
  "|- forall s.        (forall l1 l2. l1 IN s /\\ l2 IN s ==> LPREFIX l1 l2 \\/ LPREFIX l2 l1)        ==> (exists u.                 (forall l. l IN s ==> LPREFIX l u) /\\                 (forall u'.                      (forall l. l IN s ==> LPREFIX l u') ==> LPREFIX u u'))"

end T
