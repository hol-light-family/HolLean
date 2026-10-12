/- File: HolTest/BasicsTest.lean
Runtime test suite: basics.ml - more syntax constructors and prelogical
utilities like matching.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set.

FAITHFULNESS BASIS.  `basics.ml` sits just above the kernel, so an error here
propagates everywhere.  Expectations are taken from HOL Light's reference
documentation where a worked example exists (each such assertion cites its
`Help/*.hlp` file and uses the hard `MISMATCH` build gate); the remainder are
DERIVED from `basics.ml` itself and use the softer `DIFFERS` token.

TERMS/TYPES ARE HAND-BUILT FROM THE KERNEL CONSTRUCTORS wherever possible, to
keep these tests independent of the parser/printer theory bootstrap (the same
discipline `FusionTest` uses).  A few functions genuinely require declared
constants (`mk_mconst`, `dest_numeral`, `mk_let`/`dest_let`, `mk_gabs`); those
lean on the `Session` bootstrap that `CommonTest` loads and are flagged in the
report as the higher-risk cases. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

namespace HolTest.BasicsTest

/- ---------------------------------------------------------------------- -/
/- Fixed atoms/types, hand-built so their shapes are known exactly.        -/
/- ---------------------------------------------------------------------- -/

private def bTy : hol_type := .Tyvar "B"
private def numTy : hol_type := .Tyapp "num" []
private def funTy (a b : hol_type) : hol_type := .Tyapp "fun" [a, b]

private def xA : term := .Var "x" aty
private def yA : term := .Var "y" aty

/- ---------------------------------------------------------------------- -/
/- Reporting helpers.  A pass prints `-> OK`.  `MISMATCH` is a hard gate    -/
/- reserved for Help-example expectations; `DIFFERS` is the soft token for  -/
/- expectations DERIVED from basics.ml.                                     -/
/- ---------------------------------------------------------------------- -/

private def okHelp {α : Type} [BEq α] [Repr α] (lbl : String) (got exp : α) :
    IO Unit :=
  if got == exp then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={reprStr got} expected={reprStr exp}"

private def okDer {α : Type} [BEq α] [Repr α] (lbl : String) (got exp : α) :
    IO Unit :=
  if got == exp then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> DIFFERS got={reprStr got} expected={reprStr exp}"

private def okHelpE {α : Type} [BEq α] [Repr α] (lbl : String)
    (got : Except String α) (exp : α) : IO Unit :=
  match got with
  | .ok v   => if v == exp then IO.println s!"{lbl} -> OK"
               else IO.println s!"{lbl} -> MISMATCH got={reprStr v}"
  | .error e => IO.println s!"{lbl} -> MISMATCH unexpected error: {e}"

private def okDerE {α : Type} [BEq α] [Repr α] (lbl : String)
    (got : Except String α) (exp : α) : IO Unit :=
  match got with
  | .ok v   => if v == exp then IO.println s!"{lbl} -> OK"
               else IO.println s!"{lbl} -> DIFFERS got={reprStr v}"
  | .error e => IO.println s!"{lbl} -> DIFFERS unexpected error: {e}"

private def failMsg {α : Type} (lbl : String) (got : Except String α)
    (expMsg : String) : IO Unit :=
  match got with
  | .error e => if e == expMsg then IO.println s!"{lbl} -> OK (correctly rejected)"
                else IO.println s!"{lbl} -> MISMATCH msg=\"{e}\" expected=\"{expMsg}\""
  | .ok _    => IO.println s!"{lbl} -> MISMATCH unexpectedly succeeded"

/- ---------------------------------------------------------------------- -/
/- genvar: freshness (Help/genvar.hlp: "a variable ... whose name has not  -/
/- previously been produced by genvar").                                   -/
/- ---------------------------------------------------------------------- -/

-- Two successive genvar calls of the same type must be DISTINCT variables
-- (the backing counter advances).  Names themselves are unstable across runs,
-- so this is asserted STRUCTURALLY via `!=`.
#eval (do
  let v1 ← genvar bool_ty
  let v2 ← genvar bool_ty
  if v1 != v2 && is_var v1 && is_var v2 && type_of v1 == bool_ty then
    IO.println "genvar produces fresh distinct variables -> OK"
  else IO.println s!"genvar freshness -> DIFFERS v1={reprStr v1} v2={reprStr v2}")

/- ---------------------------------------------------------------------- -/
/- dest_fun_ty (Help/dest_fun_ty.hlp).                                     -/
/- ---------------------------------------------------------------------- -/

-- dest_fun_ty `:A->B` = (`:A`,`:B`).
#eval okHelpE "dest_fun_ty :A->B (Help/dest_fun_ty.hlp)"
  (dest_fun_ty (funTy aty bTy)) (aty, bTy)
-- dest_fun_ty `:num->num->bool` = (`:num`, `:num->bool`).
#eval okHelpE "dest_fun_ty :num->num->bool (Help/dest_fun_ty.hlp)"
  (dest_fun_ty (funTy numTy (funTy numTy bool_ty))) (numTy, funTy numTy bool_ty)
-- dest_fun_ty on a non-function type fails with "dest_fun_ty".
#eval failMsg "dest_fun_ty on tyvar (Help/dest_fun_ty.hlp)"
  (dest_fun_ty aty) "dest_fun_ty"

/- ---------------------------------------------------------------------- -/
/- type_match (Help/type_match.hlp), including the FAILURE cases.          -/
/- ---------------------------------------------------------------------- -/

-- type_match `:A->B->bool` `:num->num->bool` [] = [(`:num`,`:A`); (`:num`,`:B`)].
#eval okHelpE "type_match A->B->bool / num->num->bool (Help/type_match.hlp)"
  (type_match (funTy aty (funTy bTy bool_ty))
              (funTy numTy (funTy numTy bool_ty)) [])
  [(numTy, aty), (numTy, bTy)]
-- FAILURE: incompatible constructors (bool vs num) -> "type_match".
#eval failMsg "type_match bool / num fails" (type_match bool_ty numTy []) "type_match"
-- FAILURE: a type variable already bound to a DIFFERENT type in `sofar`.
-- Match `:A` against `:num` given A already bound to `:bool` -> "type_match".
#eval failMsg "type_match conflicting prior binding"
  (type_match aty numTy [(bool_ty, aty)]) "type_match"
-- FAILURE: arity/shape mismatch on the SAME head (fun vs fun with a var side
-- that conflicts): match `:A->A` against `:num->bool` forces A := num then
-- A := bool, a conflict -> "type_match".
#eval failMsg "type_match A->A / num->bool conflict"
  (type_match (funTy aty aty) (funTy numTy bool_ty) []) "type_match"

/- ---------------------------------------------------------------------- -/
/- mk_mconst (Help/mk_mconst.hlp).  IO-valued; needs the `T` constant, so   -/
/- relies on the Session bootstrap (Bool layer).                            -/
/- ---------------------------------------------------------------------- -/

-- mk_mconst ("T", `:bool`) = `T` : the boolean truth constant.
#eval (do
  match ← mk_mconst "T" bool_ty with
  | .error e => IO.println s!"mk_mconst T:bool -> MISMATCH error {e}"
  | .ok c =>
    match dest_const c with
    | .ok ("T", ty) => if ty == bool_ty then IO.println "mk_mconst T:bool (Help/mk_mconst.hlp) -> OK"
                       else IO.println s!"mk_mconst T:bool -> MISMATCH ty={reprStr ty}"
    | _ => IO.println s!"mk_mconst T:bool -> MISMATCH not const T: {reprStr c}")
-- mk_mconst ("T", `:num`) fails: "mk_const: generic type cannot be instantiated".
#eval (do failMsg "mk_mconst T:num rejected (Help/mk_mconst.hlp)" (← mk_mconst "T" numTy)
            "mk_const: generic type cannot be instantiated")

/- ---------------------------------------------------------------------- -/
/- mk_icomb: the FAILURE branch is testable without the parser.            -/
/- ---------------------------------------------------------------------- -/

-- mk_icomb with a non-function rator fails: "mk_icomb: not a function type".
-- The rator must have a non-function type CONSTRUCTOR (so `dest_type` succeeds
-- but is not "fun"); a variable of type `:num` does this.  (A type-VARIABLE
-- rator would instead surface the underlying "dest_type: ..." message.)
#eval failMsg "mk_icomb non-function rator"
  (mk_icomb (.Var "z" (.Tyapp "num" [])) yA) "mk_icomb: not a function type"

/- ---------------------------------------------------------------------- -/
/- subst (general substitution).  IO-nested: `subst ilist` yields a         -/
/- substitution FUNCTION which itself is IO (Except ·)-valued.              -/
/- ---------------------------------------------------------------------- -/

-- Substituting `y` for `x` in the term `x` (both `:A`) yields `y`.
#eval (do
  match ← subst [(yA, xA)] with
  | .error e => IO.println s!"subst build -> DIFFERS error {e}"
  | .ok f =>
    match ← f xA with
    | .ok t => if t == yA then IO.println "subst [y/x] applied to x = y -> OK"
               else IO.println s!"subst -> DIFFERS got {reprStr t}"
    | .error e => IO.println s!"subst apply -> DIFFERS error {e}")
-- Substituting into a term that does NOT contain the pattern leaves it
-- unchanged: subst [y/x] applied to `f` (a different variable) = `f`.
#eval (do
  let fA : term := .Var "f" aty
  match ← subst [(yA, xA)] with
  | .error e => IO.println s!"subst2 build -> DIFFERS error {e}"
  | .ok f =>
    match ← f fA with
    | .ok t => if t == fA then IO.println "subst [y/x] leaves unrelated term fixed -> OK"
               else IO.println s!"subst2 -> DIFFERS got {reprStr t}"
    | .error e => IO.println s!"subst2 apply -> DIFFERS error {e}")

/- ---------------------------------------------------------------------- -/
/- is_binary / dest_binary.  Hand-built `+`-application term.              -/
/- ---------------------------------------------------------------------- -/

private def plusConst : term := .Const "+" (funTy numTy (funTy numTy numTy))
private def n_x : term := .Var "x" numTy
private def n_y : term := .Var "y" numTy
-- `x + y` as a raw two-fold combination.
private def xPlusY : term := .Comb (.Comb plusConst n_x) n_y

#eval okDer "is_binary + on (x+y) = true" (is_binary "+" xPlusY) true
#eval okDer "is_binary * on (x+y) = false" (is_binary "*" xPlusY) false
#eval okDer "is_binary + on a variable = false" (is_binary "+" n_x) false
#eval okDerE "dest_binary + (x+y) = (x,y)" (dest_binary "+" xPlusY) (n_x, n_y)
-- dest_binary with the WRONG operator name fails with "dest_binary".
#eval failMsg "dest_binary wrong name fails" (dest_binary "*" xPlusY) "dest_binary"
-- dest_binary on a non-binary term fails with "dest_binary".
#eval failMsg "dest_binary on variable fails" (dest_binary "+" n_x) "dest_binary"

/- ---------------------------------------------------------------------- -/
/- striplist / splitlist / rev_splitlist.  These are POLYMORPHIC in the     -/
/- destructor, so they are exercised with a `Nat`/`Int` destructor - no     -/
/- term bootstrap needed - and a NON-SYMMETRIC shape so the traversal        -/
/- DIRECTION is observable.                                                  -/
/- ---------------------------------------------------------------------- -/

-- splitlist repeatedly peels the LEFT component off the destructor's result,
-- recursing on the RIGHT remainder.  With dest n = (n, n-1) while n > 0:
--   splitlist dest 3 = ([3,2,1], 0)  (collect lefts left-to-right, stop at 0).
private def peelPair (n : Nat) : Except String (Nat × Nat) :=
  if n == 0 then failwith "done" else .ok (n, n - 1)
#eval (do
  let (ls, rem) := splitlist peelPair 3
  okDer "splitlist collects lefts, keeps remainder" (ls, rem) ([3,2,1], 0))

-- rev_splitlist recurses on the LEFT component, so the collected list comes
-- out REVERSED and it returns (remainder, list).  With dest n = (n-1, n):
--   rev_splitlist dest 3 = (0, [1,2,3]).
private def peelPairL (n : Nat) : Except String (Nat × Nat) :=
  if n == 0 then failwith "done" else .ok (n - 1, n)
#eval (do
  let (rem, ls) := rev_splitlist peelPairL 3
  okDer "rev_splitlist recurses left, reverses" (rem, ls) (0, [1,2,3]))

-- striplist strips a BINARY tree via `dest`, returning the fringe of leaves
-- left-to-right.  Use a destructor whose RIGHT child is always a LEAF (0) and
-- whose LEFT child decreases, so recursion terminates:
--   dest n = if n > 1 then (n-1, 0) else fail.
-- Trace: strip 3 [] = strip 2 (strip 0 []); strip 0 [] = [0] (leaf);
--   strip 2 [0] = strip 1 (strip 0 [0]); strip 0 [0] = [0,0];
--   strip 1 [0,0] = [1,0,0] (leaf 1); so striplist dest 3 = [1,0,0].
-- The leftmost leaf (1) comes first and the interior right-leaves (0) follow,
-- so a reversed traversal would give a different fringe.
private def peelTree (n : Nat) : Except String (Nat × Nat) :=
  if n > 1 then .ok (n - 1, 0) else failwith "leaf"
#eval (do
  okDer "striplist returns left-to-right fringe" (striplist peelTree 3) [1,0,0])

/- ---------------------------------------------------------------------- -/
/- dest_numeral (Help/dest_numeral.hlp).  Built with Session.mk_numeral    -/
/- (a numeral term needs the NUMERAL/BIT0/BIT1/_0 constants from the num    -/
/- bootstrap), then destructed with basics.ml's dest_numeral.               -/
/- ---------------------------------------------------------------------- -/

-- dest_numeral `0` = 0.
#eval (do
  match Session.mk_numeral (0 : Rat) with
  | .error e => IO.println s!"dest_numeral 0 setup ERR: {e}"
  | .ok z => okHelpE "dest_numeral 0 (Help/dest_numeral.hlp)"
               (HolCore.Basics.dest_numeral z) 0)
-- Round trip on a larger value: dest_numeral (mk_numeral n) = n.
#eval (do
  match Session.mk_numeral (42 : Rat) with
  | .error e => IO.println s!"dest_numeral 42 setup ERR: {e}"
  | .ok t => okDerE "dest_numeral round-trips 42"
               (HolCore.Basics.dest_numeral t) 42)
-- dest_numeral on a NON-numeral term fails with "dest_numeral".
#eval failMsg "dest_numeral on a variable fails"
  (HolCore.Basics.dest_numeral n_x) "dest_numeral"

/- ---------------------------------------------------------------------- -/
/- mk_gabs / dest_gabs (Help/mk_gabs.hlp, Help/dest_gabs.hlp).             -/
/-                                                                        -/
/- KEY dest_gabs property (Help/dest_gabs.hlp): "it also works on basic   -/
/- abstractions".  A PLAIN abstraction is hand-built, so this needs no     -/
/- bootstrap and pins that branch directly.                                -/
/- ---------------------------------------------------------------------- -/

-- dest_gabs on a PLAIN abstraction `\x. x` returns (`x`, `x`), exactly as
-- dest_abs would (Help/dest_gabs.hlp final example).
#eval okDerE "dest_gabs on plain abstraction \\x.x (Help/dest_gabs.hlp)"
  (dest_gabs (.Abs xA xA)) (xA, xA)
-- is_gabs on a plain abstraction is true.
#eval okDer "is_gabs on plain abstraction = true" (is_gabs (.Abs xA xA)) true
-- dest_gabs on a NON-abstraction non-GABS term fails with the literal message.
#eval failMsg "dest_gabs on a variable fails"
  (dest_gabs xA) "dest_gabs: Not a generalized abstraction"

-- mk_gabs on a VARIABLE varstruct yields an ORDINARY abstraction (Help/
-- mk_gabs.hlp: "In the case where s is a variable, the result is an ordinary
-- abstraction").  mk_gabs(`x:A`, `y:A`) = `\x. y`; check by round-trip through
-- dest_gabs.
#eval (do
  match ← mk_gabs xA yA with
  | .error e => IO.println s!"mk_gabs var -> DIFFERS error {e}"
  | .ok g =>
    if g == term.Abs xA yA then IO.println "mk_gabs on variable = plain abstraction (Help/mk_gabs.hlp) -> OK"
    else IO.println s!"mk_gabs var -> DIFFERS got {reprStr g}")

/- ---------------------------------------------------------------------- -/
/- dest_let / mk_let (Help/dest_let.hlp).  Needs LET/LET_END/GABS/GEQ from  -/
/- the bootstrap; exercised as a mk_let -> dest_let ROUND TRIP over a        -/
/- single binding, so the exact printed numerals are not depended on.       -/
/- FLAG: highest-risk case in this file (many constants involved).          -/
/- ---------------------------------------------------------------------- -/

-- Round trip: build `let x = 5 in x` (x, 5 : num), destruct it back to the
-- binding list [(x,5)] and body x.
#eval (do
  -- FORCE the pair layer: `LET`/`LET_END` are introduced by the pair.ml
  -- bootstrap, so `mk_let` cannot build a let-term before it has run - it fails
  -- with "mk_const: not a constant name".  Reading a pair theorem forces it.
  let _ ← (IO.mkRef (concl Session.LET_DEF) : IO (IO.Ref term))
  match Session.mk_numeral (5 : Rat) with
  | .error e => IO.println s!"mk_let setup (numeral) ERR: {e}"
  | .ok five =>
    match ← mk_let [(n_x, five)] n_x with
    | .error e => IO.println s!"mk_let -> DIFFERS build error {e}"
    | .ok letTm =>
      match dest_let letTm with
      | .error e => IO.println s!"dest_let -> DIFFERS error {e}"
      | .ok (binds, body) =>
        if binds == [(n_x, five)] && body == n_x then
          IO.println "mk_let/dest_let round trip (let x=5 in x) (Help/dest_let.hlp) -> OK"
        else
          IO.println s!"dest_let -> DIFFERS binds={reprStr binds} body={reprStr body}")
-- dest_let on a non-let term fails with "dest_let: not a let-term".
#eval failMsg "dest_let on a variable fails" (dest_let n_x) "dest_let: not a let-term"

/- ---------------------------------------------------------------------- -/
/- follow_path / find_path (Help/follow_path.hlp, Help/find_path.hlp).      -/
/- Hand-built term so no bootstrap is needed; the director-string semantics -/
/- (l = rator, r = rand, b = body) are pinned directly.                     -/
/- ---------------------------------------------------------------------- -/

-- Build `f x` where f : A->A, x : A.  follow_path "l" = f ; "r" = x.
private def fAA : term := .Var "f" (funTy aty aty)
private def appFX : term := .Comb fAA xA
#eval okDerE "follow_path \"l\" (f x) = f" (follow_path "l" appFX) fAA
#eval okDerE "follow_path \"r\" (f x) = x" (follow_path "r" appFX) xA
#eval okDerE "follow_path \"\" (f x) = whole term" (follow_path "" appFX) appFX
-- follow_path "b" into a non-abstraction fails (a "b" step needs `body`).
#eval failMsg "follow_path b on non-abstraction fails" (follow_path "b" appFX) "body: Not an abstraction"
-- follow_path "b" into a genuine abstraction `\x. y` yields the body `y`.
#eval okDerE "follow_path \"b\" (\\x. y) = y" (follow_path "b" (.Abs xA yA)) yA

-- find_path: the FIRST subterm satisfying `p`, top-down.  In `f x`, find the
-- first VARIABLE named "x": path is "r" (the rand).  find_path returns the
-- director string.
#eval okDerE "find_path to x in (f x) = \"r\""
  (find_path (fun t => t == xA) appFX) "r"
-- find_path where the WHOLE term matches returns the empty path.
#eval okDerE "find_path matching whole term = \"\""
  (find_path (fun t => t == appFX) appFX) ""

/- ---------------------------------------------------------------------- -/
/- follow_path / find_path are INVERSE on a found path: following the path  -/
/- found by find_path lands on a subterm satisfying the predicate.          -/
/- ---------------------------------------------------------------------- -/

#eval (do
  match find_path (fun t => t == xA) appFX with
  | .error e => IO.println s!"find/follow inverse -> DIFFERS find error {e}"
  | .ok pth =>
    match follow_path pth appFX with
    | .ok sub => if sub == xA then IO.println "find_path/follow_path are inverse -> OK"
                 else IO.println s!"find/follow inverse -> DIFFERS landed {reprStr sub}"
    | .error e => IO.println s!"find/follow inverse -> DIFFERS follow error {e}")

end HolTest.BasicsTest
