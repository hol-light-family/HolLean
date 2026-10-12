/- File: HolTest/LibTest.lean
Runtime test suite: lib.ml - the convenient library functions.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set.

FAITHFULNESS BASIS.  `lib.ml` is the very bottom of the tower, so an error here
propagates everywhere.  Expectations are taken from HOL Light's reference
documentation where a worked example exists (each such assertion cites its
`Help/*.hlp` file and uses the `MISMATCH` build gate), and otherwise DERIVED
from `lib.ml` itself (those use the softer `DIFFERS` token).

The defect classes this project has actually hit shape the emphasis:
  * FOLD DIRECTION - every fold is exercised with a NON-COMMUTATIVE operation
    so a reversed traversal is observable, not hidden by symmetry;
  * FAILURE STRINGS - `assoc`/`rev_assoc` both fail with "find" (not "assoc"),
    `chop_list` normalises to "chop_list", `tryfind`/`find`/`remove`/`end_itlist`
    each have their own literal message;
  * `tryfind` must catch ONLY a failure and return the FIRST success;
  * the composition-operator family must run its RIGHT operand FIRST and a
    left-associative chain must equal its explicitly right-grouped form;
  * the Patricia-tree `Func` operations, pinned against the Help examples. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

namespace HolTest.LibTest

/- ---------------------------------------------------------------------- -/
/- Reporting helpers.  A pass prints `-> OK`.  `MISMATCH` is a hard build  -/
/- gate, reserved for expectations quoted VERBATIM from a Help example;    -/
/- `DIFFERS` is the soft token for expectations DERIVED from lib.ml.       -/
/- ---------------------------------------------------------------------- -/

/-- A pure value quoted from a Help example must equal `exp` (hard gate). -/
private def okHelp {α : Type} [BEq α] [Repr α] (lbl : String) (got exp : α) :
    IO Unit :=
  if got == exp then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={reprStr got} expected={reprStr exp}"

/-- A pure value DERIVED from lib.ml must equal `exp` (soft token). -/
private def okDer {α : Type} [BEq α] [Repr α] (lbl : String) (got exp : α) :
    IO Unit :=
  if got == exp then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> DIFFERS got={reprStr got} expected={reprStr exp}"

/-- An `Except String α` from a Help example must be `.ok exp` (hard gate). -/
private def okHelpE {α : Type} [BEq α] [Repr α] (lbl : String)
    (got : Except String α) (exp : α) : IO Unit :=
  match got with
  | .ok v   => if v == exp then IO.println s!"{lbl} -> OK"
               else IO.println s!"{lbl} -> MISMATCH got={reprStr v}"
  | .error e => IO.println s!"{lbl} -> MISMATCH unexpected error: {e}"

/-- An `Except String α` DERIVED from lib.ml must be `.ok exp` (soft token). -/
private def okDerE {α : Type} [BEq α] [Repr α] (lbl : String)
    (got : Except String α) (exp : α) : IO Unit :=
  match got with
  | .ok v   => if v == exp then IO.println s!"{lbl} -> OK"
               else IO.println s!"{lbl} -> DIFFERS got={reprStr v}"
  | .error e => IO.println s!"{lbl} -> DIFFERS unexpected error: {e}"

/-- An `Except String α` MUST be `.error` with EXACTLY `expMsg` (hard gate:
    a wrong or short failure string is a real defect class here). -/
private def failMsg {α : Type} (lbl : String) (got : Except String α)
    (expMsg : String) : IO Unit :=
  match got with
  | .error e => if e == expMsg then IO.println s!"{lbl} -> OK (correctly rejected)"
                else IO.println s!"{lbl} -> MISMATCH msg=\"{e}\" expected=\"{expMsg}\""
  | .ok _    => IO.println s!"{lbl} -> MISMATCH unexpectedly succeeded"

/- ---------------------------------------------------------------------- -/
/- Fold DIRECTION.  Every fold below uses a NON-COMMUTATIVE combiner so a  -/
/- reversed traversal changes the answer.                                  -/
/- ---------------------------------------------------------------------- -/

-- itlist Help example (Help/itlist.hlp): itlist (+) [1;2;3;4;5] 0 = 15,
-- and with base 6 = 21.  `+` is commutative, so these pin the RESULT but not
-- the direction; the derived cases below pin the direction.
#eval okHelp "itlist (+) [1,2,3,4,5] 0 (Help/itlist.hlp)"
  (itlist (· + ·) ([1,2,3,4,5] : List Nat) 0) 15
#eval okHelp "itlist (+) [1,2,3,4,5] 6 (Help/itlist.hlp)"
  (itlist (· + ·) ([1,2,3,4,5] : List Nat) 6) 21

-- itlist DIRECTION (derived): itlist f [x1..xn] b = f x1 (f x2 .. (f xn b)),
-- so with cons the list is rebuilt in ORIGINAL order and appended to the base.
-- itlist (::) [1,2,3] [9] = 1::2::3::[9] = [1,2,3,9].  A reversed fold would
-- give [3,2,1,9].
#eval okDer "itlist (::) [1,2,3] [9] direction"
  (itlist (fun (x : Nat) acc => x :: acc) [1,2,3] [9]) [1,2,3,9]

-- itlist DIRECTION via a non-associative arithmetic combiner (subtraction on
-- Int).  itlist (-) [1,2,3] 0 = 1-(2-(3-0)) = 1-(2-3) = 1-(-1) = 2.
#eval okDer "itlist (-) [1,2,3] 0 direction"
  (itlist (fun (x : Int) acc => x - acc) [1,2,3] 0) 2

-- rev_itlist Help example (Help/rev_itlist.hlp): rev_itlist ( * ) [1;2;3;4] 1
-- = 24.  Product is commutative; the derived case pins the direction.
#eval okHelp "rev_itlist (*) [1,2,3,4] 1 (Help/rev_itlist.hlp)"
  (rev_itlist (fun (x : Nat) y => x * y) [1,2,3,4] 1) 24

-- rev_itlist DIRECTION (derived): rev_itlist f [x1..xn] b = f xn (.. (f x1 b)),
-- so with cons the list is REVERSED onto the base.
-- rev_itlist (::) [1,2,3] [9] = 3::2::1::[9] = [3,2,1,9].
#eval okDer "rev_itlist (::) [1,2,3] [9] direction"
  (rev_itlist (fun (x : Nat) acc => x :: acc) [1,2,3] [9]) [3,2,1,9]

-- itlist vs rev_itlist on the SAME non-commutative combiner must DIFFER.
-- This DISCRIMINATING PAIR fails any implementation that confuses the two.
#eval (do
  let l := itlist (fun (x : Nat) acc => x :: acc) [1,2,3] ([] : List Nat)
  let r := rev_itlist (fun (x : Nat) acc => x :: acc) [1,2,3] ([] : List Nat)
  if l == [1,2,3] && r == [3,2,1] && l != r then
    IO.println "itlist/rev_itlist opposite directions -> OK"
  else IO.println s!"itlist/rev_itlist -> DIFFERS l={l} r={r}")

-- end_itlist Help example (Help/end_itlist.hlp): end_itlist (+) [1;2;3;4] = 10.
#eval okHelpE "end_itlist (+) [1,2,3,4] (Help/end_itlist.hlp)"
  (end_itlist (· + ·) ([1,2,3,4] : List Nat)) 10
-- end_itlist DIRECTION (derived): end_itlist f [x1..xn] = f x1 (.. (f x_{n-1} xn)),
-- right-nested with NO base.  On Int subtraction:
-- end_itlist (-) [10,1,2] = 10-(1-2) = 10-(-1) = 11.
#eval okDerE "end_itlist (-) [10,1,2] direction"
  (end_itlist (fun (x y : Int) => x - y) [10,1,2]) 11
-- end_itlist one-element list returns that element.
#eval okDerE "end_itlist (-) [7] singleton" (end_itlist (fun (x y : Int) => x - y) [7]) 7
-- end_itlist FAILURE: empty list, literal "end_itlist".
#eval failMsg "end_itlist [] fails" (end_itlist (fun (x y : Int) => x - y) []) "end_itlist"

-- itlist2 DIRECTION (derived): itlist2 f [a1..] [b1..] b applies to the LAST
-- pair first, right-nested.  Encode direction by consing the pair (ai,bi):
-- itlist2 (fun a b acc => (a,b)::acc) [1,2] [10,20] [] = [(1,10),(2,20)].
#eval okDerE "itlist2 pair-order direction"
  (itlist2 (fun (a b : Nat) acc => (a, b) :: acc) [1,2] [10,20] [])
  [(1,10),(2,20)]
-- itlist2 arithmetic non-commutative direction:
-- itlist2 (fun a b acc => a - b - acc) is right-nested; with Int and a
-- subtraction combiner the value depends on nesting order.
-- itlist2 (fun a b acc => (a-b) - acc) [1,2] [0,0] 0
--   = (1-0) - ((2-0) - 0) = 1 - 2 = -1.
#eval okDerE "itlist2 (-) direction value"
  (itlist2 (fun (a b : Int) acc => (a - b) - acc) [1,2] [0,0] 0) (-1)
-- itlist2 FAILURE: length mismatch, literal "itlist2".
#eval failMsg "itlist2 length mismatch"
  (itlist2 (fun (a b : Nat) acc => a + b + acc) [1,2] [1] 0) "itlist2"

/- ---------------------------------------------------------------------- -/
/- tryfind: catch ONLY a failure, return the FIRST success.                -/
/- Help/tryfind.hlp: returns (f xi) for the first xi where f succeeds;     -/
/- fails with "tryfind" if it fails for all.                               -/
/- ---------------------------------------------------------------------- -/

-- FIRST success: `f` succeeds only on even numbers, returning n/2.  Over
-- [1,3,4,6] the first success is at 4 -> 2 (NOT 3, the later even 6).
#eval okDerE "tryfind returns FIRST success"
  (tryfind (fun (n : Nat) => if n % 2 == 0 then .ok (n / 2) else failwith "odd")
           [1,3,4,6]) 2
-- ALL fail: literal "tryfind".
#eval failMsg "tryfind all-fail message"
  (tryfind (fun (_ : Nat) => (failwith "nope" : Except String Nat)) [1,2,3])
  "tryfind"
-- Empty list: also "tryfind".
#eval failMsg "tryfind [] message"
  (tryfind (fun (n : Nat) => (.ok n : Except String Nat)) []) "tryfind"

/- ---------------------------------------------------------------------- -/
/- assoc / rev_assoc / find / remove / partition.                          -/
/- CRITICAL: assoc AND rev_assoc both fail with "find" (lib.ml 297/302),   -/
/- NOT "assoc"/"rev_assoc".                                                 -/
/- ---------------------------------------------------------------------- -/

#eval okDerE "assoc found" (assoc 2 [(1,"a"),(2,"b"),(3,"c")]) "b"
-- FIRST match wins even with a duplicate key.
#eval okDerE "assoc first-match wins" (assoc 1 [(1,"x"),(1,"y")]) "x"
#eval failMsg "assoc absent fails with find" (assoc 9 [(1,"a"),(2,"b")]) "find"
#eval okDerE "rev_assoc found (looks up by value)"
  (rev_assoc "b" [(1,"a"),(2,"b"),(3,"c")]) 2
#eval failMsg "rev_assoc absent fails with find"
  (rev_assoc "z" [(1,"a"),(2,"b")]) "find"

-- find (lib.ml): first satisfying element, else "find".
#eval okDerE "find first even" (find (fun (n : Nat) => n % 2 == 0) [1,3,5,4,6]) 4
#eval failMsg "find none fails" (find (fun (n : Nat) => n > 100) [1,2,3]) "find"

-- remove (lib.ml): removes FIRST satisfying element, keeping order of the
-- rest, returns (removed, rest).  Else "remove".
#eval okDerE "remove first even"
  (remove (fun (n : Nat) => n % 2 == 0) [1,3,4,5,6]) (4, [1,3,5,6])
#eval failMsg "remove none fails" (remove (fun (n : Nat) => n > 100) [1,2,3]) "remove"

-- partition (lib.ml): (elements satisfying p, elements not), ORDER PRESERVED
-- within each part.
#eval okDer "partition preserves order in both parts"
  (partition (fun (n : Nat) => n % 2 == 0) [1,2,3,4,5,6])
  ([2,4,6], [1,3,5])

/- ---------------------------------------------------------------------- -/
/- setify / uniq / set operations.                                         -/
/- ---------------------------------------------------------------------- -/

-- setify Help example (Help/setify.hlp): setify [1;2;3;1;4;3] = [1;2;3;4].
-- (Our setify sorts by the derived Ord, and these are already sorted.)
#eval okHelp "setify [1,2,3,1,4,3] (Help/setify.hlp)"
  (setify ([1,2,3,1,4,3] : List Nat)) [1,2,3,4]
-- setify sorts (derived): setify of a scrambled list is the sorted set.
#eval okDer "setify sorts and dedups"
  (setify ([3,1,2,3,1] : List Nat)) [1,2,3]

-- uniq removes ADJACENT duplicates ONLY (lib.ml comment "NB!").  A
-- DISCRIMINATING PAIR: adjacent dups collapse, non-adjacent survive.
#eval okDer "uniq collapses adjacent" (uniq ([1,1,2,2,3] : List Nat)) [1,2,3]
#eval okDer "uniq keeps NON-adjacent dups" (uniq ([1,2,1] : List Nat)) [1,2,1]

-- union (lib.ml): itlist insert l1 l2; keeps l2, prepends the l1 elements not
-- already present, in itlist order.  union [1,2,3] [2,4] :
--   insert 1 (insert 2 (insert 3 [2,4])) = insert 1 (insert 2 [3,2,4])
--   = insert 1 [3,2,4] = [1,3,2,4].
#eval okDer "union prepends new elements" (union ([1,2,3] : List Nat) [2,4]) [1,3,2,4]
-- subtract (lib.ml): elements of l1 not in l2, order of l1 preserved.
#eval okDer "subtract keeps l1 order" (subtract ([1,2,3,4] : List Nat) [2,4]) [1,3]
-- intersect (lib.ml): elements of l1 that are in l2, order of l1 preserved.
#eval okDer "intersect keeps l1 order" (intersect ([1,2,3,4] : List Nat) [4,2]) [2,4]

/- ---------------------------------------------------------------------- -/
/- chop_list / shareout.  (RegressionTest already pins chop_list's success -/
/- and the overrun MESSAGE; here we extend to the boundary and to shareout,-/
/- which matches on that exact "chop_list" message.)                       -/
/- ---------------------------------------------------------------------- -/

-- chop_list boundary: n = length gives (whole, []).
#eval okDerE "chop_list at exact length"
  (chop_list 3 ([1,2,3] : List Nat)) ([1,2,3], [])
-- chop_list 0 gives ([], whole).
#eval okDerE "chop_list 0" (chop_list 0 ([1,2,3] : List Nat)) ([], [1,2,3])

-- shareout Help example (Help/shareout.hlp): shareout [ [1;2;3];[4;5];[6];[7;8;9] ]
-- (explode "abcdefghijklmnopq") = [ ["a";"b";"c"];["d";"e"];["f"];["g";"h";"i"] ].
-- The pattern lists' VALUES are irrelevant - only their LENGTHS matter (3,2,1,3).
#eval okHelpE "shareout groups by pattern lengths (Help/shareout.hlp)"
  (shareout [ [1,2,3],[4,5],[6],[7,8,9] ] (explode "abcdefghijklmnopq"))
  [ ["a","b","c"],["d","e"],["f"],["g","h","i"] ]
-- shareout FAILURE: too few elements -> the underlying "chop_list" message.
#eval failMsg "shareout too few elements"
  (shareout [ [1,2],[3,4] ] (explode "abc")) "chop_list"

/- ---------------------------------------------------------------------- -/
/- mergesort.  Help/mergesort.hlp: mergesort (<) [6;2;5;9;2;5;3]            -/
/-   = [2;2;3;5;5;6;9]  (KEEPS duplicates - it is a sort, not a setify).    -/
/- ---------------------------------------------------------------------- -/

#eval okHelp "mergesort (<) [6,2,5,9,2,5,3] (Help/mergesort.hlp)"
  (mergesort (fun (a b : Nat) => a < b) [6,2,5,9,2,5,3]) [2,2,3,5,5,6,9]
-- Non-symmetric check: a DESCENDING order comparator reverses the sort, so the
-- direction of `ord` is observable.
#eval okDer "mergesort with (>) sorts descending"
  (mergesort (fun (a b : Nat) => a > b) [6,2,5,9,2,5,3]) [9,6,5,5,3,2,2]

/- ---------------------------------------------------------------------- -/
/- Composition operators: RIGHT operand runs FIRST, and a mixed            -/
/- LEFT-ASSOCIATIVE chain equals its explicitly right-grouped form.        -/
/- All combiners are NON-COMMUTATIVE so a swapped order is visible.        -/
/- ---------------------------------------------------------------------- -/

-- `o` (total): (f o g) x = f (g x), g FIRST.  f = (+1), g = (*2).
-- (f o g) 3 = (3*2)+1 = 7 ;  (g o f) 3 = (3+1)*2 = 8.  These MUST differ.
#eval (do
  let fg := (fun (n : Nat) => n + 1) o (fun (n : Nat) => n * 2)
  let gf := (fun (n : Nat) => n * 2) o (fun (n : Nat) => n + 1)
  if fg 3 == 7 && gf 3 == 8 then IO.println "o runs RIGHT operand first -> OK"
  else IO.println s!"o direction -> DIFFERS fg3={fg 3} gf3={gf 3}")

-- `o` LEFT-ASSOCIATIVITY equals explicit RIGHT grouping (same function).
-- h o g o f  parses as  (h o g) o f;  must equal  h o (g o f).
#eval (do
  let h := fun (n : Nat) => n + 100
  let g := fun (n : Nat) => n * 3
  let f := fun (n : Nat) => n + 1
  let chain := h o g o f            -- left-assoc: (h o g) o f
  let right := h o (g o f)
  -- value: f then g then h: ((3+1)*3)+100 = 112
  if chain 3 == right 3 && chain 3 == 112 then
    IO.println "o chain (h o g o f) = right-grouped -> OK"
  else IO.println s!"o assoc -> DIFFERS chain={chain 3} right={right 3}")

-- `oM` (Kleisli in Except): (f oM g) x = g x >>= f, g FIRST and short-circuits.
#eval (do
  let g := fun (n : Nat) => if n == 0 then failwith "zero" else (.ok (n * 2) : Except String Nat)
  let f := fun (n : Nat) => (.ok (n + 1) : Except String Nat)
  okDerE "oM runs g first" ((f oM g) 3) 7
  -- short-circuit: g fails -> f never runs, error propagates.
  failMsg "oM short-circuits on g failure" ((f oM g) 0) "zero")

-- `oEm` (total outer, Except inner): (f oEm g) x = f <$> g x.
#eval (do
  let g := fun (n : Nat) => if n == 0 then failwith "zero" else (.ok (n * 2) : Except String Nat)
  let f := fun (n : Nat) => n + 1     -- total
  okDerE "oEm maps total f over Except result" ((f oEm g) 3) 7
  failMsg "oEm short-circuits on g failure" ((f oEm g) 0) "zero")

-- `oIO` (both IO (Except ·)): (f oIO g) x runs g FIRST, short-circuits.
#eval (do
  let g : Nat → IO (Except String Nat) :=
    fun n => return (if n == 0 then failwith "zero" else .ok (n * 2))
  let f : Nat → IO (Except String Nat) := fun n => return .ok (n + 1)
  match ← (f oIO g) 3 with
  | .ok v => if v == 7 then IO.println "oIO runs g first -> OK"
             else IO.println s!"oIO -> DIFFERS got {v}"
  | .error e => IO.println s!"oIO -> DIFFERS unexpected error {e}"
  match ← (f oIO g) 0 with
  | .error e => if e == "zero" then IO.println "oIO short-circuits on g failure -> OK"
                else IO.println s!"oIO -> DIFFERS msg={e}"
  | .ok _ => IO.println "oIO short-circuit -> DIFFERS unexpectedly succeeded")

-- `oIOm` (total outer, IO (Except ·) inner): (f oIOm g) x maps total f.
#eval (do
  let g : Nat → IO (Except String Nat) :=
    fun n => return (if n == 0 then failwith "zero" else .ok (n * 2))
  let f : Nat → Nat := fun n => n + 1
  match ← (f oIOm g) 3 with
  | .ok v => if v == 7 then IO.println "oIOm maps total f -> OK"
             else IO.println s!"oIOm -> DIFFERS got {v}"
  | .error e => IO.println s!"oIOm -> DIFFERS unexpected error {e}"
  match ← (f oIOm g) 0 with
  | .error e => if e == "zero" then IO.println "oIOm short-circuits on g failure -> OK"
                else IO.println s!"oIOm -> DIFFERS msg={e}"
  | .ok _ => IO.println "oIOm short-circuit -> DIFFERS unexpectedly succeeded")

/- ---------------------------------------------------------------------- -/
/- Patricia-tree finite partial functions (`Func`).  Keys are `Nat`/`Int`, -/
/- which have `Ord`/`Hashable`, so `dom`/`ran`/`graph`/`apply` typecheck.   -/
/- Expectations are the Help examples for apply/undefined/dom/ran/combine/  -/
/- undefine.                                                                -/
/- ---------------------------------------------------------------------- -/

-- apply Help example (Help/apply.hlp): apply undefined 1 fails with "apply";
-- apply (1 |=> 2) 1 = 2.
#eval failMsg "apply undefined fails with apply (Help/apply.hlp)"
  (apply (undefined : Func Nat Nat) 1) "apply"
#eval okHelpE "apply (1 |=> 2) 1 = 2 (Help/apply.hlp)"
  (apply (pointFun 1 2 : Func Nat Nat) 1) 2
-- apply on an undefined point of a NON-empty function still fails with "apply".
#eval failMsg "apply on undefined point fails with apply"
  (apply (pointFun 1 2 : Func Nat Nat) 9) "apply"

-- is_undefined / undefined.
#eval okDer "is_undefined undefined = true" (is_undefined (undefined : Func Nat Nat)) true
#eval okDer "is_undefined (1|=>2) = false" (is_undefined (pointFun 1 2 : Func Nat Nat)) false

-- dom Help example (Help/dom.hlp): dom (1 |=> "1") = [1];
-- dom(itlist I [2|->4; 3|->6] undefined) = [2;3].
#eval okHelp "dom (1 |=> \"1\") (Help/dom.hlp)"
  (dom (pointFun 1 "1" : Func Nat String)) [1]
#eval okHelp "dom {2|->4,3|->6} (Help/dom.hlp)"
  (dom (update 2 4 (update 3 6 (undefined : Func Nat Nat)))) [2,3]

-- ran Help example (Help/ran.hlp): ran (1 |=> "1") = ["1"];
-- ran(itlist I [2|->4; 3|->6] undefined) = [4;6].
#eval okHelp "ran (1 |=> \"1\") (Help/ran.hlp)"
  (ran (pointFun 1 "1" : Func Nat String)) ["1"]
#eval okHelp "ran {2|->4,3|->6} (Help/ran.hlp)"
  (ran (update 2 4 (update 3 6 (undefined : Func Nat Nat)))) [4,6]

-- update overwrites an existing key (redefinition).
#eval okDerE "update overwrites existing key"
  (apply (update 1 99 (pointFun 1 2 : Func Nat Nat)) 1) 99

-- undefine Help example (Help/undefine.hlp): dom{1,2,3} then dom(undefine 2 f)
-- = [1;3].  undefine of an ABSENT key leaves the function unchanged.
#eval okHelp "dom(undefine 2 {1,2,3}) (Help/undefine.hlp)"
  (dom (undefine 2 (update 1 1 (update 2 2 (update 3 3 (undefined : Func Nat Nat)))))) [1,3]
#eval okDer "undefine of absent key is a no-op"
  (dom (undefine 9 (update 1 1 (update 2 2 (undefined : Func Nat Nat))))) [1,2]

-- combine Help example (Help/combine.hlp):
--   f = {1|->2; 2|->3; 3|->6}, g = {1|->5; 2|->-3}
--   graph(combine (+) (fun x -> x = 0) f g) = [(1,7); (3,6)]
-- Point 2 gives 3+(-3)=0, which the zero-predicate DROPS; point 1 gives 7;
-- point 3 is only in f, giving 6.  Values are Int to allow the negative.
-- (Asserted via `dom` + `apply` rather than `graph`, to avoid relying on an
-- `Ord (Nat × Int)` product instance; the point 2 DROP is checked directly.)
#eval (do
  let f : Func Nat Int := update 1 2 (update 2 3 (update 3 6 undefined))
  let g : Func Nat Int := update 1 5 (update 2 (-3) undefined)
  let c := combine (· + ·) (fun x => x == 0) f g
  okHelp "combine (+) zero f g: domain drops point 2 (Help/combine.hlp)"
    (dom c) [1,3]
  okHelp "combine (+) zero f g: value at 1 = 7 (Help/combine.hlp)" ((apply c 1).toOption) (some 7)
  okHelp "combine (+) zero f g: value at 3 = 6 (Help/combine.hlp)" ((apply c 3).toOption) (some 6)
  okDer "combine (+) zero f g: point 2 undefined" (defined c 2) false)
-- combine where NOTHING cancels: a plain pointwise sum over shared keys, union
-- over the rest.  {1|->2,2|->3} (+) {2|->10,3|->1} = {1|->2,2|->13,3|->1}.
#eval (do
  let f : Func Nat Int := update 1 2 (update 2 3 undefined)
  let g : Func Nat Int := update 2 10 (update 3 1 undefined)
  let c := combine (· + ·) (fun _ => false) f g
  okDer "combine (+) no-cancel domain" (dom c) [1,2,3]
  okDerE "combine (+) no-cancel value at 2 = 13" (apply c 2) 13)

end HolTest.LibTest
