/- File: HolTest/PretermTest.lean
Runtime test suite: preterm.ml - preterms/pretypes, typechecking, and the
translation to types and terms.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set.

FAITHFULNESS BASIS.  The preterm->term elaboration pipeline is reached through
the term quotation parser: `parse_term` lexes, parses a preterm, then runs
`retypecheck [] ptm` and `term_of_preterm` (HolCore/Parser.lean:1096-1105 - the
faithful port of preterm.ml's `parse_term`).  So `parse_term` is the authentic
entry point and most tests drive the pipeline through it.  Expectations for the
flag behaviour come VERBATIM from HOL Light's reference docs:
  hol-light/Help/type_invention_error.hlp   (the `x = x` error example)
  hol-light/Help/the_implicit_types.hlp     (restricting a variable's type)
  hol-light/Help/make_overloadable.hlp      (clash on differing skeleton)
The pretype<->type and preterm round-trips are checked against the identity
laws stated in preterm.ml.

NOTE ON NUMERALS.  The `the_implicit_types` doc example uses `mul 1 x`, but the
numeral `1` requires the type `num` (nums.ml), which is NOT loaded at this core
layer.  The implicit-types test below therefore uses a bool-typed variable
instead - same code path (`get_var_type` + `unify` in `typify`) with no
`num` dependency.

GLOBAL-FLAG HYGIENE.  `type_invention_error`, `type_invention_warning`,
`the_implicit_types` and the overload skeleton table are process-global IO.Refs.
Every test that mutates one RESTORES it in the same `#eval`, so later `#eval`s
(here and in sibling test files compiled in the same module) are unaffected. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- Self-checking helpers.                                                 -/
/- ---------------------------------------------------------------------- -/

private def ptSquash (s : String) : String :=
  (s.replace "\n" "").replace " " ""

/-- Parse `s`, assert the elaborated term re-prints as `expected`.  This drives
    the whole preterm->term pipeline (typify + resolve_interface + solve_preterm
    + term_of_preterm) and pins the RESULT, not merely that it succeeds. -/
private unsafe def parsePrints (lbl s expected : String) : IO Unit := do
  match ← HolCore.Parser.parse_term s with
  | .error e => IO.println s!"{lbl} -> FAILED parse ERR: {e}"
  | .ok tm =>
    let got := ptSquash (← HolCore.Printer.string_of_term tm)
    if got == ptSquash expected then IO.println s!"{lbl} -> OK"
    else IO.println s!"{lbl} -> FAILED got={got} want={ptSquash expected}"

/-- Parse `s`, assert the whole term's `type_of` prints as `expected`. -/
private unsafe def parseTypeIs (lbl s expected : String) : IO Unit := do
  match ← HolCore.Parser.parse_term s with
  | .error e => IO.println s!"{lbl} -> FAILED parse ERR: {e}"
  | .ok tm =>
    let got := ptSquash (← HolCore.Printer.string_of_type (type_of tm))
    if got == ptSquash expected then IO.println s!"{lbl} -> OK"
    else IO.println s!"{lbl} -> FAILED got={got} want={ptSquash expected}"

/-- Substring test: is `needle` contained in `hay`? -/
private def containsStr (hay needle : String) : Bool :=
  (hay.splitOn needle).length >= 2

/-- Parse `s`, expect FAILURE, and assert the error message CONTAINS `needle`.
    Prints `-> OK (correctly rejected)` on the expected failure. -/
private unsafe def parseFailsWith (lbl s needle : String) : IO Unit := do
  match ← HolCore.Parser.parse_term s with
  | .ok tm =>
    IO.println s!"{lbl} -> FAILED wrongly accepted: {
      ptSquash (← HolCore.Printer.string_of_term tm)}"
  | .error e =>
    if containsStr e needle
    then IO.println s!"{lbl} -> OK (correctly rejected): {e}"
    else IO.println s!"{lbl} -> FAILED msg={e} (expected to contain {needle})"

/- ---------------------------------------------------------------------- -/
/- 1. Basic elaboration through the full pipeline (parse_term).           -/
/- ---------------------------------------------------------------------- -/

-- A fully-determined propositional term round-trips unchanged.
#eval parsePrints "elaborate p ==> p" "p ==> p" "p ==> p"
#eval parsePrints "elaborate p /\\ q \\/ r" "p /\\ q \\/ r" "p /\\ q \\/ r"
-- The whole term is boolean: type inference propagates bool through /\, ==>.
#eval parseTypeIs "type of (p ==> q) is bool" "p ==> q" "bool"

/- ---------------------------------------------------------------------- -/
/- 2. Invented type variables.  With nothing to fix `x`'s type, typify     -/
/- leaves a system type variable that `type_of_pretype_base` turns into a  -/
/- real (invented) type variable, printed with a leading `?`.  CoreTest    -/
/- documents `\x. x` as `\(x:?0). x`; the exact index is a global counter, -/
/- so we assert only that an invented `?`-variable appears, via the type.  -/
/- ---------------------------------------------------------------------- -/

-- `\x. x` has type `?n -> ?n` for some invented `?n`; both ends are the SAME
-- invented variable.  We check the identity function's domain = codomain by
-- comparing the two halves of the printed function type.
#eval (do
  match ← HolCore.Parser.parse_term "\\x. x" with
  | .error e => IO.println s!"invented tyvar \\x.x -> FAILED parse ERR: {e}"
  | .ok tm =>
    let sty ← HolCore.Printer.string_of_type (type_of tm)
    -- printed as `?n->?n`; split on the arrow and require both sides equal and
    -- both begin with `?` (an invented variable).
    let s := (sty.replace " " "")
    match (s.splitOn "->") with
    | [dom, cod] =>
        if dom == cod && dom.startsWith "?" then
          IO.println s!"invented tyvar \\x.x -> OK ({s})"
        else IO.println s!"invented tyvar \\x.x -> FAILED ({s})"
    | _ => IO.println s!"invented tyvar \\x.x -> FAILED (not a 1-arrow fn: {s})")

/- ---------------------------------------------------------------------- -/
/- 3. type_invention_error (Help/type_invention_error.hlp).               -/
/- With the flag set, `x = x` (whose most general type needs an invented   -/
/- variable) must FAIL with a message beginning                            -/
/-   "typechecking error (cannot infer type of variables)".                -/
/- The OCaml lists the offending names (`=, x`); we assert only the fixed  -/
/- prefix, since the Lean accumulation order of the name list is an        -/
/- implementation detail.  Flag is restored to its default (false).        -/
/- ---------------------------------------------------------------------- -/

#eval (do
  let saved ← HolCore.Preterm.type_invention_error.get
  HolCore.Preterm.type_invention_error.set true
  let res ← HolCore.Parser.parse_term "x = x"
  HolCore.Preterm.type_invention_error.set saved   -- restore no matter what
  match res with
  | .ok tm =>
    IO.println s!"type_invention_error -> FAILED wrongly accepted: {
      ptSquash (← HolCore.Printer.string_of_term tm)}"
  | .error e =>
    if (e.splitOn "typechecking error (cannot infer type of variables)").length >= 2
    then IO.println s!"type_invention_error -> OK (correctly rejected): {e}"
    else IO.println s!"type_invention_error -> FAILED msg={e}")

-- With the flag at its default (false), the SAME term parses fine (a warning,
-- not an error) - `x = x` is `|- x = x` shaped, both `x` invented but equal.
#eval (do
  match ← HolCore.Parser.parse_term "x = x" with
  | .error e => IO.println s!"x = x (flag off) -> FAILED parse ERR: {e}"
  | .ok tm =>
    let got := ptSquash (← HolCore.Printer.string_of_term tm)
    -- HOL Light ANNOTATES a subterm whose type has an invented typevar, under
    -- its DEFAULT `print_types_of_subterms = 1` (printer.ml 154, 577-578), so
    -- the expected shape is `(x:?N)=(x:?N)`, not a bare `x=x`.  The number N
    -- comes from a GLOBAL counter and is unstable, so assert structurally.
    let annotated := containsStr got "(x:?"
    let bothSides := (got.splitOn "(x:?").length == 3
    if annotated && bothSides then IO.println s!"x = x (flag off) -> OK ({got})"
    else IO.println s!"x = x (flag off) -> FAILED got={got}")

/- ---------------------------------------------------------------------- -/
/- 4. the_implicit_types (Help/the_implicit_types.hlp).                   -/
/- Associating a variable name with a type in the_implicit_types restricts -/
/- its inferred type.  We restrict `myv` to `:bool` and check the parsed   -/
/- variable is typed `:bool` even though nothing else forces it.  (The doc  -/
/- uses a numeral, which needs `num`; a bool constraint uses the identical  -/
/- code path - `get_var_type` + `unify` in typify - without that            -/
/- dependency.)  The_implicit_types is restored afterwards.                 -/
/- ---------------------------------------------------------------------- -/

#eval (do
  let saved ← HolCore.Preterm.the_implicit_types.get
  HolCore.Preterm.the_implicit_types.set [("myv", bool_ty)]
  let res ← HolCore.Parser.parse_term "myv"
  HolCore.Preterm.the_implicit_types.set saved     -- restore
  match res with
  | .error e => IO.println s!"the_implicit_types myv:bool -> FAILED parse ERR: {e}"
  | .ok tm =>
    let sty := ptSquash (← HolCore.Printer.string_of_type (type_of tm))
    -- `string_of_type` is `pp_print_type` (printer.ml 748), so NO leading
    -- colon; the `:` of `:bool` belongs to the quotation printer.
    if sty == "bool" then IO.println s!"the_implicit_types myv:bool -> OK"
    else IO.println s!"the_implicit_types myv:bool -> FAILED type={sty}")

/- ---------------------------------------------------------------------- -/
/- 5. pretype <-> type and preterm round-trips (preterm.ml identity laws). -/
/- ---------------------------------------------------------------------- -/

-- pretype_of_type then type_of_pretype is the identity on a concrete type.
#eval (do
  let pty := HolCore.Preterm.pretype_of_type bool_ty
  match ← (HolCore.Preterm.type_of_pretype pty).run with
  | .error e => IO.println s!"pretype round-trip bool -> FAILED: {e}"
  | .ok ty =>
    if ty == bool_ty then IO.println s!"pretype round-trip bool -> OK"
    else IO.println s!"pretype round-trip bool -> FAILED: {
      ptSquash (← HolCore.Printer.string_of_type ty)}")

-- A function type `:bool->bool` also round-trips through pretype.
#eval (do
  match ← HolCore.Parser.parse_type "bool->bool" with
  | .error e => IO.println s!"pretype round-trip fn -> FAILED parse: {e}"
  | .ok fty =>
    let pty := HolCore.Preterm.pretype_of_type fty
    match ← (HolCore.Preterm.type_of_pretype pty).run with
    | .error e => IO.println s!"pretype round-trip fn -> FAILED: {e}"
    | .ok ty =>
      if ty == fty then IO.println s!"pretype round-trip fn -> OK"
      else IO.println s!"pretype round-trip fn -> FAILED")

-- preterm_of_term then term_of_preterm recovers the SAME term - WITHOUT
-- retypecheck.  `retypecheck` must NOT be inserted here: `preterm_of_term`
-- emits `Constp` for constants (preterm.ml 140-145), and `typify` has cases
-- ONLY for `Varp`/`Combp`/`Typing`/`Absp`, falling through to
-- `failwith "typify: unexpected constant at this stage"` (preterm.ml 357).
-- So OCaml fails on that pipeline too - retypecheck is for PARSER output, where
-- a constant is still `Varp` and typify itself rebinds it to `Constp`.
#eval (do
  match ← HolCore.Parser.parse_term "p /\\ q ==> p" with
  | .error e => IO.println s!"preterm round-trip -> FAILED parse: {e}"
  | .ok tm0 =>
    let ptm := HolCore.Preterm.preterm_of_term tm0
    match ← (HolCore.Preterm.term_of_preterm ptm).run with
    | .error e => IO.println s!"preterm round-trip -> FAILED: {e}"
    | .ok tm1 =>
      if tm1 == tm0 then IO.println "preterm_of_term/term_of_preterm round-trip -> OK"
      else IO.println s!"preterm round-trip -> FAILED terms differ")

-- And the NEGATIVE half, pinning the reason above: retypecheck on a preterm
-- containing `Constp` must be REJECTED, with OCaml's exact message.
#eval (do
  match ← HolCore.Parser.parse_term "p /\\ q ==> p" with
  | .error e => IO.println s!"retypecheck rejects Constp -> FAILED parse: {e}"
  | .ok tm0 =>
    let ptm := HolCore.Preterm.preterm_of_term tm0
    match ← (HolCore.Preterm.retypecheck [] ptm).run with
    | .ok _ => IO.println "retypecheck rejects Constp -> FAILED wrongly accepted"
    | .error e =>
      if containsStr e "typify: unexpected constant at this stage" then
        IO.println "retypecheck rejects Constp (preterm.ml 357) -> OK (correctly rejected)"
      else IO.println s!"retypecheck rejects Constp -> MISMATCH msg={e}")

/- ---------------------------------------------------------------------- -/
/- 6. Ill-typed input: the failure path.  A boolean connective applied to  -/
/- a non-boolean argument cannot be unified.  `parse_term` wraps the        -/
/- typify failure as "typechecking error (initial type assignment):...".    -/
/- We assert the message CONTAINS "typechecking error", i.e. the failure    -/
/- is reported by the elaborator (not a lexer/grammar error).               -/
/- ---------------------------------------------------------------------- -/

-- `~` expects a bool; feeding it a variable already constrained to a function
-- type of two bools makes the constraint unsatisfiable.
#eval parseFailsWith "ill-typed ~(p q)" "~((p:bool) q)" "typechecking error"

/- ---------------------------------------------------------------------- -/
/- 7. make_overloadable clash message (Help/make_overloadable.hlp).        -/
/- Registering the SAME symbol with the SAME skeleton twice is idempotent;  -/
/- registering it with a DIFFERENT skeleton fails with                      -/
/-   "make_overloadable: differs from existing skeleton".                   -/
/- A throwaway symbol name is used so global overload state is not polluted -/
/- for real symbols (preterm.ml keeps skeletons process-global; there is no -/
/- public de-register, so the name is deliberately unique and inert).       -/
/- ---------------------------------------------------------------------- -/

#eval (do
  let sym := "__preterm_test_ovl__"
  match ← HolCore.Preterm.make_overloadable sym aty with
  | .error e => IO.println s!"make_overloadable first -> FAILED: {e}"
  | .ok _ =>
    -- idempotent: same skeleton again succeeds
    match ← HolCore.Preterm.make_overloadable sym aty with
    | .error e => IO.println s!"make_overloadable idempotent -> FAILED: {e}"
    | .ok _ =>
      -- clash: a different skeleton must be rejected with the exact message
      match ← HolCore.Preterm.make_overloadable sym bool_ty with
      | .ok _ => IO.println s!"make_overloadable clash -> FAILED wrongly accepted"
      | .error e =>
        if e == "make_overloadable: differs from existing skeleton"
        then IO.println s!"make_overloadable clash -> OK"
        else IO.println s!"make_overloadable clash -> FAILED msg={e}")
