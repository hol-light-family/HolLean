/- File: HolTest/PermutationsTest.lean
Runtime test suite: Library/permutations.ml (HolLibrary/Permutations.lean, wired by
SessionLibrary/Permutations.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/permutations.ml"`, then `string_of_thm`, newlines joined).
tools/permutationsdiff/check.sh compares every theorem structurally and as
printed, and the constants and definitions after loading.  Theorems that
print with `?NNN` invented type variables are omitted here. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.Permutations.ensurePermutations

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
open Session SessionLibrary.Permutations HolLight.Syntax

#eval thm' "PERMUTES_INVERSE_FUNCTION" PERMUTES_INVERSE_FUNCTION
  "|- forall s p.        p permutes s <=>        (exists q.             (forall x. ~(x IN s) ==> p x = x) /\\             (forall x. x IN s ==> p x IN s) /\\             (forall x. x IN s ==> p (q x) = x /\\ q (p x) = x))"
#eval thm' "RESTRICT_SWAP" RESTRICT_SWAP
  "|- forall s a b.        a IN s /\\ b IN s        ==> (\\x. if x IN s then swap (a,b) x else x) = swap (a,b)"
#eval thm' "THREE_CYCLE_INVERSE" THREE_CYCLE_INVERSE
  "|- forall a b c.        ~(a = b) /\\ ~(b = c) /\\ ~(a = c)        ==> inverse (three_cycle a b c) = three_cycle a c b"
#eval thm' "PERMUTATION_COMPOSE_EQ" PERMUTATION_COMPOSE_EQ
  "|- (forall p q. permutation p ==> (permutation (p o q) <=> permutation q)) /\\    (forall p q. permutation q ==> (permutation (p o q) <=> permutation p))"
#eval thm' "PERMUTES_IN_NUMSEG" PERMUTES_IN_NUMSEG
  "|- forall p n i. p permutes 1..n /\\ i IN 1..n ==> 1 <= p i /\\ p i <= n"
#eval thm' "EVENPERM_CYCLIC_N" EVENPERM_CYCLIC_N
  "|- forall n k.        evenperm (\\i. if i < n then (i + k) MOD n else i) <=>        n = 0 \\/ ODD n \\/ EVEN k"
#eval thm' "SUM_OVER_PERMUTATIONS_NUMSEG" SUM_OVER_PERMUTATIONS_NUMSEG
  "|- forall f m n.        m <= n        ==> sum {p | p permutes m..n} f =            sum (m..n)            (\\i. sum {p | p permutes m + 1..n} (\\q. f (swap (m,i) o q)))"

-- The conversions on sample inputs (expected values printed by HOL Light;
-- a failure is expected as `FAIL <message>`).
#eval check "PERMSET_CONV {p | p permutes ({}:num->bool)}" (do
    match ← HolCore.Parser.parse_term "{p | p permutes ({}:num->bool)}" with
    | .ok tm => PERMSET_CONV tm
    | .error e => pure (.error e))
  "|- {p | p permutes {}} = {I}"
#eval check "PERMSET_CONV {p | p permutes {1}}" (do
    match ← HolCore.Parser.parse_term "{p | p permutes {1}}" with
    | .ok tm => PERMSET_CONV tm
    | .error e => pure (.error e))
  "|- {p | p permutes {1}} = {I}"
#eval check "PERMSET_CONV {p | p permutes {1,2}}" (do
    match ← HolCore.Parser.parse_term "{p | p permutes {1,2}}" with
    | .ok tm => PERMSET_CONV tm
    | .error e => pure (.error e))
  "|- {p | p permutes {1, 2}} = {I, swap (1,2)}"
#eval check "PERMSET_CONV {p | p permutes {1,2,3}}" (do
    match ← HolCore.Parser.parse_term "{p | p permutes {1,2,3}}" with
    | .ok tm => PERMSET_CONV tm
    | .error e => pure (.error e))
  "|- {p | p permutes {1, 2, 3}} =    {I, swap (2,3), swap (1,2), swap (1,2) o swap (2,3), swap (1,3),     swap (1,3) o swap (2,3)}"

end T
