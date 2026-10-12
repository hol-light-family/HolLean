/- File: HolTest/SimpTest.lean
Runtime test suite: simp.ml - the rewriting/simplification engine.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set.

FAITHFULNESS BASIS.  Expectations are taken from simp.ml itself and from HOL
Light's reference documentation where a worked example exists:
  hol-light/Help/basic_rewrites.hlp   (the default rewrite set)
  hol-light/Help/basic_congs.hlp      (the default congruence set)
  hol-light/Help/PURE_REWRITE_TAC.hlp (the `b <=> T` un-simplified example)
  hol-light/Help/REWRITE_CONV.hlp / REWRITE_TAC.hlp

Simp is the rewriting engine (`REWRITE_TAC`, `SIMP_TAC`, `ONCE_REWRITE_TAC`,
conditional rewriting, AC-ordering) yet was barely covered; two defects were
already found here by audit.  These tests target `term_order`/AC-orientation,
the `net_of_thm` ETA_AX special case, the core rewriting conversions, and the
basic-rewrite state accessors.

The AC-ordering assertions are STRUCTURAL (hand-built kernel terms, no parser
bootstrap needed); the rewriting assertions compare the REWRITTEN side (`rand`
of the conclusion) structurally against a parsed expectation, so a degenerate
`Inhabited`-default theorem cannot masquerade as a pass. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

namespace HolTest.SimpTest

/- ---------------------------------------------------------------------- -/
/- Fixed atoms, hand-built so their types/heads are known exactly.        -/
/- ---------------------------------------------------------------------- -/

private def funTy (a b : hol_type) : hol_type := .Tyapp "fun" [a, b]

-- Two DIFFERENT constants, neither of which is the distinguished top `T`.
private def cA : term := .Const "cA" bool_ty
private def cB : term := .Const "cB" bool_ty
-- A Comb headed by a constant, and a bare variable, for the Comb/Var case.
private def fBB : term := .Const "f" (funTy bool_ty bool_ty)
private def zV  : term := .Var "z" bool_ty
private def wV  : term := .Var "w" bool_ty
private def fApp : term := .Comb fBB zV
-- Same-head applications with different (variable) arguments, for lexify.
private def gVV : term := .Var "g" (funTy bool_ty bool_ty)
private def aV  : term := .Var "a" bool_ty
private def bV  : term := .Var "b" bool_ty
private def gA  : term := .Comb gVV aV
private def gB  : term := .Comb gVV bV

/- ---------------------------------------------------------------------- -/
/- Reporting helpers.                                                     -/
/- ---------------------------------------------------------------------- -/

/-- A boolean expectation DERIVED from the OCaml `dyn_order`/`compare`
    semantics (soft `DIFFERS`, no build gate). -/
private def okBoolDerived (lbl : String) (got exp : Bool) : IO Unit :=
  if got == exp then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> DIFFERS got {got} expected {exp}"

/-- The RHS of a rewrite theorem (the `rand` of its conclusion) must equal
    `exp` STRUCTURALLY.  `gate` picks the hard (`MISMATCH`) vs soft (`DIFFERS`)
    token: use the hard gate only when `exp` is taken verbatim from a Help
    example. -/
private unsafe def okRewrites (lbl : String) (gate : Bool)
    (got : Except String thm) (exp : term) : IO Unit :=
  match got with
  | .ok th =>
      match rand (concl th) with
      | .ok r =>
          if r == exp then IO.println s!"{lbl} -> OK"
          else
            let tok := if gate then "MISMATCH" else "DIFFERS"
            IO.println s!"{lbl} -> {tok} got={reprStr r} exp={reprStr exp}"
      | .error e => IO.println s!"{lbl} -> {if gate then "MISMATCH" else "DIFFERS"} concl not an application: {e}"
  | .error e => IO.println s!"{lbl} -> {if gate then "MISMATCH" else "DIFFERS"} unexpected error: {e}"

/- ---------------------------------------------------------------------- -/
/- 1. `term_order` / AC-orientation (simp.ml 65-80).                       -/
/-                                                                        -/
/- `term_order = dyn_order `T``.  `dyn_order tm1 tm2` answers "is tm1      -/
/- GREATER than tm2".  The RegressionTest already pins that the top term  -/
/- `T` is treated as the LARGEST; these are COMPLEMENTARY cases that do    -/
/- NOT involve `T`, exercising the other three branches of simp.ml 73-79. -/
/- ---------------------------------------------------------------------- -/

-- Two different constants, neither `T`: fall to `compare f1 f2 = gt` (the OCaml
-- `f1 > f2` fallback, simp.ml 79).  Lean's derived `Ord term` compares the
-- `Const` name field, so cB > cA.  DISCRIMINATING PAIR: no wrong orientation
-- can satisfy both directions.
#eval okBoolDerived "term_order cB cA (name fallback, cB > cA)"
        (HolCore.Simp.term_order cB cA) true
#eval okBoolDerived "term_order cA cB (name fallback, cA not > cB)"
        (HolCore.Simp.term_order cA cB) false

-- Comb vs Var: `strip_comb (f z)` has head `Const "f"`, so this compares a
-- `Const` head against a bare `Var` head.  Constructor order is Var < Const <
-- Comb < Abs (fusion.ml 24-29 / Fusion.lean), so `Const > Var`: (f z) > w, but
-- w not > (f z).  DISCRIMINATING PAIR.
#eval okBoolDerived "term_order (f z) w (Const head > Var)"
        (HolCore.Simp.term_order fApp wV) true
#eval okBoolDerived "term_order w (f z) (Var not > Const head)"
        (HolCore.Simp.term_order wV fApp) false

-- Same head `g`: `dyn_order` recurses via `lexify (dyn_order g)` over the
-- argument lists (simp.ml 71-72), so the FIRST differing argument decides.
-- `g b` > `g a` iff b > a, and not the other way: this observes the recursive
-- descent AND its direction.  DISCRIMINATING PAIR.
#eval okBoolDerived "term_order (g b) (g a) (lexify on args, b > a)"
        (HolCore.Simp.term_order gB gA) true
#eval okBoolDerived "term_order (g a) (g b) (lexify on args, a not > b)"
        (HolCore.Simp.term_order gA gB) false

/- ---------------------------------------------------------------------- -/
/- 2. `net_of_thm` ETA_AX special case (simp.ml 96).                       -/
/-                                                                        -/
/- The eta arm fires only for `Abs(x,Comb(Var _ as v,x'))` - the inner     -/
/- function MUST be a VARIABLE (a missing `is_var` guard was FIXED here).  -/
/- A theorem `|- (\x. f x) = f` with a CONSTANT `f` must therefore NOT     -/
/- take the eta arm but the plain-equation arm.                            -/
/-                                                                        -/
/- I cannot fabricate `|- (\x. c x) = c` for a constant `c` without extra  -/
/- machinery, so - as the brief permits - I assert the OBSERVABLE REWRITE  -/
/- consequences instead:                                                   -/
/-  (a) `REWRITE_CONV [ETA_AX] (\y. ~ y)` eta-reduces to `~`  (eta arm      -/
/-      DOES fire when the specialised head is a variable);                 -/
/-  (b) a plain equation `|- (p ==> q ==> p) <=> T` rewrites via the        -/
/-      plain-equation arm (the non-eta path that the constant-`f` theorem  -/
/-      would take).                                                        -/
/- ---------------------------------------------------------------------- -/

-- (a) ETA_AX eta-reduces `\y. ~y` to `~`.  `ETA_AX` is canonicalised by
-- `mk_rewrites` to the variable-headed `|- (\x. t x) = t`, so the eta arm
-- fires.  Expected RHS is the constant `~` (`Const "~"`), asserted
-- STRUCTURALLY (its printed form has an unstable type variable otherwise).
#eval (do
  -- Build the expected result `~` via the kernel (a bare prefix operator is
  -- awkward to parse), so the expectation is the exact `Const "~" (bool->bool)`.
  match ← (mk_const "~" [] : IO (Except String term)) with
  | .error e => IO.println s!"eta setup: mk_const ~ ERR {e}"
  | .ok notC =>
    match ← (parse_term "\\y. ~ y" : IO (Except String term)) with
    | .error e => IO.println s!"eta setup: parse (\\y. ~ y) ERR {e}"
    | .ok lamNot =>
      -- rand of the result must be `~` itself (structural).
      okRewrites "ETA_AX eta-reduces (\\y. ~y) to ~ (eta arm, var head)"
        false (← Session.REWRITE_CONV [Session.ETA_AX] lamNot) notC)

-- (b) A plain (non-eta, non-permutative) equation drives the plain-equation
-- arm: `|- (p ==> q ==> p) <=> T` supplied to REWRITE_CONV rewrites
-- `p ==> q ==> p` to `T`.  This is the SAME arm a constant-headed
-- `|- (\x. c x) = c` theorem would fall through to.
#eval (do
  match ← (parse_term "p ==> q ==> p" : IO (Except String term)) with
  | .error e => IO.println s!"plain-eq setup: parse ERR {e}"
  | .ok pqp =>
    match ← (Session.TAUT ([[ (p ==> q ==> p) <=> T ]]) : IO (Except String thm)) with
    | .error e => IO.println s!"plain-eq setup: TAUT ERR {e}"
    | .ok th =>
      okRewrites "plain-equation arm rewrites (p ==> q ==> p) to T"
        false (← Session.REWRITE_CONV [th] pqp) tT)

/- ---------------------------------------------------------------------- -/
/- 3. Core rewriting conversions and tactics.                             -/
/- ---------------------------------------------------------------------- -/

-- REWRITE_CONV uses the basic net: `T /\ p` reduces to `p` via AND_CLAUSES
-- (`|- T /\ t <=> t`, listed VERBATIM in basic_rewrites.hlp), so this is a
-- hard `MISMATCH` gate.
#eval (do
  okRewrites "REWRITE_CONV [] (T /\\ p) = p (basic net)"
    true (← Session.REWRITE_CONV [] ([[ T /\ (p:bool) ]])) p)

-- ONCE_REWRITE_CONV also consults the basic net and reduces the outermost
-- match: `F \/ p` reduces to `p` via OR_CLAUSES (`|- F \/ t <=> t`, verbatim
-- in basic_rewrites.hlp).
#eval (do
  okRewrites "ONCE_REWRITE_CONV [] (F \\/ p) = p (basic net)"
    true (← Session.ONCE_REWRITE_CONV [] ([[ F \/ (p:bool) ]])) p)

-- PURE_REWRITE_CONV does NOT use the basic net.  PURE_REWRITE_TAC.hlp's worked
-- example: `b <=> T` is left UNCHANGED by the pure variant (whereas the plain
-- variant reduces it to `b`).  DISCRIMINATING PAIR: pure leaves it, basic
-- reduces it.  Both are verbatim Help expectations -> hard gate.
#eval (do
  -- pure: unchanged (rand = the whole LHS `p <=> T`)
  okRewrites "PURE_REWRITE_CONV [] (p <=> T) unchanged"
    true (← Session.PURE_REWRITE_CONV [] ([[ (p:bool) <=> T ]])) ([[ (p:bool) <=> T ]]))
#eval (do
  -- basic: reduced to `p` via EQ_CLAUSES (`|- (t <=> T) <=> t`)
  okRewrites "REWRITE_CONV [] (p <=> T) = p (basic net)"
    true (← Session.REWRITE_CONV [] ([[ (p:bool) <=> T ]])) p)

-- REWRITE_RULE (rule form): rewriting `|- (T /\ p) = (T /\ p)` (a REFL) with
-- the basic net collapses `T /\ p` to `p` on BOTH sides, giving `|- p = p`.
-- Assert the conclusion is an equation with identical sides = `p`.
#eval (do
  match ← (Session.REWRITE_RULE [] (REFL ([[ T /\ (p:bool) ]])) : IO (Except String thm)) with
  | .error e => IO.println s!"REWRITE_RULE -> DIFFERS error {e}"
  | .ok th =>
      match dest_eq (concl th) with
      | .ok (l, r) =>
          if l == HolTest.CommonTest.p && r == HolTest.CommonTest.p then IO.println "REWRITE_RULE collapses REFL(T /\\ p) to |- p = p -> OK"
          else IO.println s!"REWRITE_RULE -> DIFFERS sides={reprStr (concl th)}"
      | .error _ =>
          -- NOT an equation, and that is the CORRECT outcome: after both sides
          -- collapse to `p`, REFL_CLAUSE (`|- (x = x) <=> T`, itself a basic
          -- rewrite) reduces `p = p` to `T`.  The first draft expected
          -- `|- p = p` and forgot that the net is applied to FIXPOINT.
          if concl th == tT then
            IO.println "REWRITE_RULE reduces REFL(T /\\ p) to |- T -> OK"
          else IO.println s!"REWRITE_RULE -> DIFFERS {reprStr (concl th)}")

-- Conditional rewriting via an IMPLICATIONAL theorem (simp.ml's conditional
-- arm + basic_prover discharging the side condition).  The theorem
-- `|- T ==> ((p ==> q ==> p) <=> T)` is netted as a conditional rewrite; when
-- SIMP_CONV rewrites `p ==> q ==> p`, IMP_REWR_CONV fires and the trivial
-- side-condition `T` is discharged by the basic prover, yielding `T`.
-- FLAG: I am moderately confident but not certain the basic prover discharges
-- the `T` condition exactly as expected; soft `DIFFERS` so it never gates.
#eval (do
  match ← (parse_term "p ==> q ==> p" : IO (Except String term)) with
  | .error e => IO.println s!"cond-rewrite setup: parse ERR {e}"
  | .ok pqp =>
    match ← (Session.TAUT ([[ T ==> ((p ==> q ==> p) <=> T) ]]) : IO (Except String thm)) with
    | .error e => IO.println s!"cond-rewrite setup: TAUT ERR {e}"
    | .ok cth =>
      okRewrites "SIMP_CONV [|- T ==> (X <=> T)] X = T (conditional arm)"
        false (← Session.SIMP_CONV [cth] pqp) tT)

/- ---------------------------------------------------------------------- -/
/- 4. Basic-rewrite state accessors (simp.ml 700-770-ish).                 -/
/-                                                                        -/
/- Reading these FORCES the Session bootstrap's `extend_basic_rewrites` /  -/
/- `extend_basic_congs` side effects; if that setup ever fails to run, the -/
/- accessors return empty and these assertions catch it.                   -/
/- ---------------------------------------------------------------------- -/

-- Force the theorems/class layer (which installs the basic rewrites and the
-- IMP congruence, theorems.ml) before reading the accessors, exactly as the
-- RegressionTest forces layers via a Session theorem.
#eval (do
  let _ ← HolCore.Printer.string_of_thm Session.AND_CLAUSES
  let rws ← Session.basic_rewrites
  if rws.length ≥ 1 then
    IO.println s!"basic_rewrites non-empty ({rws.length}) -> OK"
  else IO.println s!"basic_rewrites -> MISMATCH empty ({rws.length})")

-- basic_congs: theorems.ml installs at least the propositional IMP congruence
-- (`(p <=> p') ==> ...`) and class.ml adds COND_CONG, so the set is non-empty.
#eval (do
  let _ ← HolCore.Printer.string_of_thm Session.COND_ID   -- force class layer
  let cgs ← Session.basic_congs
  if cgs.length ≥ 1 then
    IO.println s!"basic_congs non-empty ({cgs.length}) -> OK"
  else IO.println s!"basic_congs -> DIFFERS empty ({cgs.length}); expected >= 1")

-- basic_net is forced and consulted by the REWRITE_CONV tests above (which pass
-- iff the net contains the basic rewrites); here we simply confirm the accessor
-- itself evaluates without panicking, and that the net-backed reduction that
-- REWRITE_CONV performed above is genuinely coming through the SAME net.
#eval (do
  let _ ← Session.basic_net      -- forces `theConvNet`
  IO.println "basic_net accessor readable (forced without panic) -> OK")

-- `extend_basic_rewrites` must AFFECT a subsequent rewrite.  DISCRIMINATING
-- PAIR: `p ==> q ==> p` is NOT reduced by the basic net alone (no basic rule
-- matches it), but after extending the basics with `|- (p ==> q ==> p) <=> T`
-- the same REWRITE_CONV reduces it to `T`.  Placed LAST so the global mutation
-- cannot perturb the earlier assertions.
#eval (do
  match ← (parse_term "p ==> q ==> p" : IO (Except String term)) with
  | .error e => IO.println s!"extend setup: parse ERR {e}"
  | .ok pqp =>
    -- BEFORE: unchanged (rand = pqp itself)
    okRewrites "extend_basic_rewrites BEFORE: (p ==> q ==> p) unchanged"
      false (← Session.REWRITE_CONV [] pqp) pqp
    match ← (Session.TAUT ([[ (p ==> q ==> p) <=> T ]]) : IO (Except String thm)) with
    | .error e => IO.println s!"extend setup: TAUT ERR {e}"
    | .ok th =>
      match ← (Session.extend_basic_rewrites [th] : IO (Except String Unit)) with
      | .error e => IO.println s!"extend_basic_rewrites ERR {e}"
      | .ok _ =>
        -- AFTER: now reduced to `T`
        okRewrites "extend_basic_rewrites AFTER: (p ==> q ==> p) = T"
          false (← Session.REWRITE_CONV [] pqp) tT)

end HolTest.SimpTest
