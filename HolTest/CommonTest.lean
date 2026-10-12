/- File: HolTest/CommonTest.lean
Shared helpers for the runtime test suite.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Every test module imports this one.  Tests are compile-time `#eval`s, so
building a module runs its tests; to disable a group, exclude its file from the
build (there are no flags to set).

HOL Light-style tests: bare `#eval <expr>`, auto-printed in HOL syntax.  Terms
are entered with the `[[ ... ]]` quotation (parenthesize `([[ ]])` when it is
not the final/sole argument).  The coercions from `Session` auto-unwrap
`Except String thm` rule results and `[[ ]]` quotations, so `ASSUME _` and
nested rule applications compose without `force`/`do`. -/

import Session

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib

namespace HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- Quiet output for the test suite.                                       -/
/- ---------------------------------------------------------------------- -/

/- HOL Light's defaults print MESON's search trace (`verbose`, lib.ml: the
   "Searching with limit N" / "0..1..solved at 4" lines) and a warning for
   every term with invented type variables (`type_invention_warning`,
   preterm.ml), and grobner.ml prints its progress unconditionally
   (`grobner_messages`).  Over the whole suite that is over half a million lines, which
   buries the test results in build.log, so every module importing this one
   turns them off.  It also turns off `report_timing` (lib.ml), so the `time`
   calls some files make while loading (sets.ml 1780, pocklington.ml
   2606-2614, words.ml) print no `CPU time (user): ...` lines.  Prove.lean and HolInit keep HOL Light's defaults.  Other
   warnings (`warn`: benign redefinitions, free variables in a goal) still
   appear. -/
initialize do
  HolCore.Lib.verbose.set false
  HolCore.Preterm.type_invention_warning.set false
  HolMath.Grobner.grobner_messages.set false
  HolCore.Lib.report_timing.set false

/- ---------------------------------------------------------------------- -/
/- Result-reporting helpers.                                             -/
/- ---------------------------------------------------------------------- -/

/-- Run `act` and print its result like a bare `#eval`. -/
unsafe def evalThm (act : IO (Except String thm)) : IO Unit := do
  IO.println (reprStr (← act))

/-- The prover-specific aliases kept from the original suite, so the existing
    test lines read unchanged.  They no longer gate on anything. -/
unsafe def evalMeson   (act : IO (Except String thm)) : IO Unit := evalThm act
unsafe def evalMetis   (act : IO (Except String thm)) : IO Unit := evalThm act
unsafe def evalLeancop (act : IO (Except String thm)) : IO Unit := evalThm act
unsafe def evalNanocop (act : IO (Except String thm)) : IO Unit := evalThm act

/-- A goal that MUST be rejected: prints `non-thm correctly failed`, or
    `UNSOUND!!` if it was somehow proved. -/
unsafe def evalNonThm (act : IO (Except String thm)) : IO Unit := do
  match ← act with
  | .ok th   => IO.println s!"UNSOUND!! -> {reprStr (Except.ok th : Except String thm)}"
  | .error e => IO.println s!"non-thm correctly failed: {e}"

/-- Prove the same goal twice; report whether the theorems are identical. -/
unsafe def evalDeterministic (act : IO (Except String thm)) : IO Unit := do
  match ← act, ← act with
  | .ok th1, .ok th2 =>
    let s1 ← HolCore.Printer.string_of_thm th1
    let s2 ← HolCore.Printer.string_of_thm th2
    IO.println s!"determinism: {if s1 == s2 then "IDENTICAL" else "DIFFERS!"} ({s1})"
  | _, _ => IO.println "determinism ERR"

/-- Prove each `lemmaGoals` entry, then prove `goal` with them supplied. -/
unsafe def evalWithLemmas
    (prover : List thm → term → IO (Except String thm))
    (lemmaGoals : List term) (goal : term) : IO Unit := do
  let rec go (gs : List term) (acc : List thm) : IO Unit := do
    match gs with
    | []       => IO.println (reprStr (← prover acc.reverse goal))
    | g :: rest =>
      match ← prover [] g with
      | .error e => IO.println s!"ERR: {e}"
      | .ok lem  => go rest (lem :: acc)
  go lemmaGoals []

/- ---------------------------------------------------------------------- -/
/- Session "variables": common atomic terms.                             -/
/- ---------------------------------------------------------------------- -/

unsafe def p : term := [[ p:bool ]]
unsafe def q : term := [[ q:bool ]]
unsafe def x : term := [[ x:bool ]]
unsafe def tT : term := [[ T ]]
unsafe def fF : term := [[ F ]]

/- ---------------------------------------------------------------------- -/
/- Self-checking helpers that do NOT depend on printing.                   -/
/- ---------------------------------------------------------------------- -/

/-- Statement equality for tests: alpha-equivalence, after instantiating the
    expected term's INVENTED type variables (`?N`, from re-parsing a string
    with no type annotations) to match the actual term.  Only invented
    variables may be instantiated, so a genuinely wrong type still fails. -/
partial def stmtEq (got want : term) : Bool :=
  let invented (v : hol_type) : Bool :=
    match v with | .Tyvar n => n.startsWith "?" | _ => false
  -- Walk both terms in lockstep, collecting a type instantiation for the
  -- expected side; any structural disagreement just falls back to aconv.
  let rec walk (g w : term) (acc : List (hol_type × hol_type)) :
      Option (List (hol_type × hol_type)) :=
    match g, w with
    | .Var _ tg, .Var _ tw | .Const _ tg, .Const _ tw =>
        -- `type_match` binds each variable of the EXPECTED type at most once,
        -- consistently across the whole term, so an invented `?N` shared
        -- between subterms must resolve to one actual type everywhere.
        (type_match tw tg acc).toOption
    | .Comb f x, .Comb f' x' => do walk x x' (← walk f f' acc)
    | .Abs v b, .Abs v' b' => do walk b b' (← walk v v' acc)
    | _, _ => none
  match walk got want [] with
  | some ins =>
    -- An invented `?N` may bind to any type; an ordinary type variable of the
    -- expected statement may only bind to ITSELF (so a wrong type still fails).
    if ins.all (fun (t, v) => invented v || t == v) then aconv got (inst ins want)
    else aconv got want
  | none => aconv got want

/-- `th` states exactly `expected` (the OCaml `prove` statement, parsed),
    with no hypotheses, up to alpha-conversion.  Parsing the expected string
    AFTER the theorem's layer has been forced gives it the same types. -/
unsafe def stmtOK (lbl : String) (th : thm) (expected : String) : IO Unit := do
  match ← HolCore.Parser.parse_term expected with
  | .error e => IO.println s!"{lbl} -> MISMATCH expected-statement parse ERR {e}"
  | .ok want =>
    if !(hyp th).isEmpty then
      IO.println s!"{lbl} -> MISMATCH has hypotheses: {← HolCore.Printer.string_of_thm th}"
    else if stmtEq (concl th) want then IO.println s!"{lbl} -> OK"
    else IO.println s!"{lbl} -> MISMATCH got {← HolCore.Printer.string_of_thm th}"

/-- An `Except`-returning rule/conversion application succeeds with a
    hypothesis-free theorem whose conclusion is alpha-equivalent to `expected`. -/
unsafe def ruleOK (lbl : String) (act : IO (Except String thm)) (expected : String) :
    IO Unit := do
  match ← act with
  | .error e => IO.println s!"{lbl} -> MISMATCH failed: {e}"
  | .ok th => stmtOK lbl th expected

/-- `act` must FAIL; if `needle` is non-empty the message must contain it. -/
unsafe def failsOK (lbl : String) (act : IO (Except String thm)) (needle : String := "") :
    IO Unit := do
  match ← act with
  | .ok th => IO.println s!"{lbl} -> MISMATCH wrongly succeeded: {← HolCore.Printer.string_of_thm th}"
  | .error e =>
    if needle == "" || (e.splitOn needle).length ≥ 2 then
      IO.println s!"{lbl} -> OK (correctly rejected)"
    else IO.println s!"{lbl} -> MISMATCH wrong message: {e}"

end HolTest.CommonTest
