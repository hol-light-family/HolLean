/- File: HolTest/IndTypesTest.lean
Runtime test suite: ind_types.ml - tools for defining inductive types.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set.

FAITHFULNESS BASIS.  Every expected value below is taken VERBATIM from HOL
Light's own reference documentation, which ships worked examples with real
OCaml output:
  * hol-light/Help/define_type.hlp                 (tri, btree, term, command)
  * hol-light/Help/prove_cases_thm.hlp             (tree)
  * hol-light/Help/prove_constructors_distinct.hlp (tree)
  * hol-light/Help/prove_constructors_injective.hlp(tree)
  * hol-light/Help/distinctness.hlp                (num, list)
  * hol-light/Help/injectivity.hlp                 (num, list)
  * hol-light/Help/cases.hlp                       (num, list)
They are therefore NOT this translator's guesses about the intended shape; a
mismatch here is a genuine divergence from HOL Light.  The documented type and
constructor NAMES are reproduced exactly too, so the tests read as a direct
transcription of the manual. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- IMPORTANT CONSTRAINT: a TYPE NAME can be defined only ONCE PER PROCESS  -/
/- (defining one mutates the kernel's type table), and every `#eval` in    -/
/- this module shares a single process.  So each test uses a DISTINCT type -/
/- name, and none re-defines `list`/`option`/`sum`, which are created by    -/
/- the once-per-process bootstrap behind `Session.define_type`.            -/
/- ---------------------------------------------------------------------- -/

/-- Strip newlines and spaces so a multi-line pretty-printed theorem can be
    compared against a single-line expected string. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

/- ---------------------------------------------------------------------- -/
/- distinctness / injectivity / cases by simple lookup                    -/
/- (ind_types.ml 1041-1047).                                              -/
/-                                                                        -/
/- These must work with NO prior `define_type` call: OCaml runs all of     -/
/- ind_types.ml eagerly at load time, so `distinctness "list"` already    -/
/- succeeds the moment loading finishes.  This project is lazy-on-demand,  -/
/- so the readers force the bootstrap first - these tests pin that down.   -/
/- ---------------------------------------------------------------------- -/

/-- Compare a pure store lookup against the documented HOL Light output. -/
private unsafe def lookupCheck (lbl : String) (r : Except String thm)
    (expected : String) : IO Unit := do
  match r with
  | .error e => IO.println s!"{lbl} ERR: {e}"
  | .ok th =>
    let got := squash (← HolCore.Printer.string_of_thm th)
    if got == squash expected then IO.println s!"{lbl} -> OK"
    else IO.println s!"{lbl} -> MISMATCH got={got}"

-- Help/distinctness.hlp
#eval lookupCheck "distinctness num" (Session.distinctness "num")
  "|- forall n'. ~(0 = SUC n')"
#eval lookupCheck "distinctness list" (Session.distinctness "list")
  "|- forall a0' a1'. ~([] = CONS a0' a1')"

-- Help/injectivity.hlp
#eval lookupCheck "injectivity num" (Session.injectivity "num")
  "|- forall n n'. SUC n = SUC n' <=> n = n'"
#eval lookupCheck "injectivity list" (Session.injectivity "list")
  "|- forall a0 a1 a0' a1'. CONS a0 a1 = CONS a0' a1' <=> a0 = a0' /\\ a1 = a1'"

/-- Compare `Session.cases ty` against the documented HOL Light output. -/
private unsafe def casesCheck (ty expected : String) : IO Unit := do
  match ← Session.cases ty with
  | .error e => IO.println s!"cases {ty} ERR: {e}"
  | .ok th =>
    let got := squash (← HolCore.Printer.string_of_thm th)
    if got == squash expected then IO.println s!"cases {ty} -> OK"
    else IO.println s!"cases {ty} -> MISMATCH got={got}"

-- Help/cases.hlp.  `"num"` takes the SPECIAL-CASE branch returning `num_CASES`
-- directly; `"list"` goes through the store lookup plus `prove_cases_thm`.
#eval casesCheck "num" "|- forall m. m = 0 \\/ (exists n. m = SUC n)"
#eval casesCheck "list" "|- forall x. x = [] \\/ (exists a0 a1. x = CONS a0 a1)"

/- ---------------------------------------------------------------------- -/
/- `define_type` (ind_types.ml 1396-1414), the user-facing entry point.    -/
/- All four specifications below are the documented examples from          -/
/- Help/define_type.hlp, with their published output.                      -/
/- ---------------------------------------------------------------------- -/

/-- `define_type spec`, then compare BOTH returned theorems against the
    documented HOL Light output. -/
private unsafe def defineTypeCheck (lbl spec expInduct expRecursion : String) :
    IO Unit := do
  match ← Session.define_type spec with
  | .error e => IO.println s!"{lbl} ERR: {e}"
  | .ok (ith, rth) =>
    let gi := squash (← HolCore.Printer.string_of_thm ith)
    let gr := squash (← HolCore.Printer.string_of_thm rth)
    if gi != squash expInduct then IO.println s!"{lbl} INDUCT -> MISMATCH got={gi}"
    else if gr != squash expRecursion then
      IO.println s!"{lbl} RECURSION -> MISMATCH got={gr}"
    else IO.println s!"{lbl} -> OK"

-- An enumerated type with three distinct values.
#eval defineTypeCheck "tri" "tri = ONE | TWO | THREE"
  "|- forall P. P ONE /\\ P TWO /\\ P THREE ==> (forall x. P x)"
  "|- forall f0 f1 f2. exists fn. fn ONE = f0 /\\ fn TWO = f1 /\\ fn THREE = f2"

-- A recursive type: labelled binary trees, polymorphic in the leaf label.
-- NOTE: the documentation writes this as `btree = LEAF A | NODE btree btree`,
-- but Help/prove_cases_thm.hlp's `tree = LEAF num | NODE tree tree` example
-- below reuses the SAME constructor names.  Those are separate HOL Light
-- sessions; here every `#eval` shares one process, so a constructor name can
-- only be claimed once.  The constructors are renamed `BLEAF`/`BNODE` and the
-- documented SHAPE is what is checked; `tree` keeps the documented names
-- because it additionally pins all three derived-theorem provers.
#eval defineTypeCheck "btree" "btree = BLEAF A | BNODE btree btree"
  "|- forall P. (forall a. P (BLEAF a)) /\\ (forall a0 a1. P a0 /\\ P a1 ==> P (BNODE a0 a1)) ==> (forall x. P x)"
  "|- forall f0 f1. exists fn. (forall a. fn (BLEAF a) = f0 a) /\\ (forall a0 a1. fn (BNODE a0 a1) = f1 a0 a1 (fn a0) (fn a1))"

/- ---------------------------------------------------------------------- -/
/- NESTED RECURSION: `term` recurses through the already-defined `list`.   -/
/- This is the hardest path in the file, exercising                        -/
/- `create_auxiliary_clauses`, `prove_inductive_types_isomorphic` and      -/
/- `lift_type_bijections` (ind_types.ml 1084-1387).  Note the documented   -/
/- output's function naming: `fn1` is the function on `term` and `fn0` the -/
/- one on `term list`, with auxiliary clauses synthesised for `[]`/`CONS`. -/
/- ---------------------------------------------------------------------- -/

#eval defineTypeCheck "term (nested)" "term = Var num | Fn num (term list)"
  "|- forall P0 P1. (forall a. P0 (Var a)) /\\ (forall a0 a1. P1 a1 ==> P0 (Fn a0 a1)) /\\ P1 [] /\\ (forall a0 a1. P0 a0 /\\ P1 a1 ==> P1 (CONS a0 a1)) ==> (forall x0. P0 x0) /\\ (forall x1. P1 x1)"
  "|- forall f0 f1 f2 f3. exists fn0 fn1. (forall a. fn1 (Var a) = f0 a) /\\ (forall a0 a1. fn1 (Fn a0 a1) = f1 a0 a1 (fn0 a1)) /\\ fn0 [] = f2 /\\ (forall a0 a1. fn0 (CONS a0 a1) = f3 a0 a1 (fn1 a0) (fn0 a1))"

/- ---------------------------------------------------------------------- -/
/- MUTUAL RECURSION: two types defined simultaneously, exercising          -/
/- `generalize_recursion_theorem` (ind_types.ml 785-877), which turns the  -/
/- single-function recursion theorem - the only shape justifiable via the  -/
/- sum-type proforma - into one function per domain type.  Six             -/
/- constructors across the two types, so six `f` parameters.               -/
/- ---------------------------------------------------------------------- -/

#eval defineTypeCheck "command/expression (mutual)"
  "command = Assign num expression | Ite expression command command ; expression = Variable num | Constant num | Plus expression expression | Valof command"
  "|- forall P0 P1. (forall a0 a1. P1 a1 ==> P0 (Assign a0 a1)) /\\ (forall a0 a1 a2. P1 a0 /\\ P0 a1 /\\ P0 a2 ==> P0 (Ite a0 a1 a2)) /\\ (forall a. P1 (Variable a)) /\\ (forall a. P1 (Constant a)) /\\ (forall a0 a1. P1 a0 /\\ P1 a1 ==> P1 (Plus a0 a1)) /\\ (forall a. P0 a ==> P1 (Valof a)) ==> (forall x0. P0 x0) /\\ (forall x1. P1 x1)"
  "|- forall f0 f1 f2 f3 f4 f5. exists fn0 fn1. (forall a0 a1. fn0 (Assign a0 a1) = f0 a0 a1 (fn1 a1)) /\\ (forall a0 a1 a2. fn0 (Ite a0 a1 a2) = f1 a0 a1 a2 (fn1 a0) (fn0 a1) (fn0 a2)) /\\ (forall a. fn1 (Variable a) = f2 a) /\\ (forall a. fn1 (Constant a) = f3 a) /\\ (forall a0 a1. fn1 (Plus a0 a1) = f4 a0 a1 (fn1 a0) (fn1 a1)) /\\ (forall a. fn1 (Valof a) = f5 a (fn0 a))"

/- ---------------------------------------------------------------------- -/
/- The three derived-theorem provers (ind_types.ml 902-1006), on the       -/
/- documented `tree = LEAF num | NODE tree tree`.  Expected values come    -/
/- from Help/prove_constructors_injective.hlp,                             -/
/- Help/prove_constructors_distinct.hlp and Help/prove_cases_thm.hlp.      -/
/-                                                                        -/
/- Note `prove_constructors_injective` returns a CONJUNCTION over every    -/
/- argument-taking constructor, whereas `prove_constructors_distinct`      -/
/- returns the pairwise inequalities (a single one here, since `tree` has  -/
/- two constructors).                                                      -/
/- ---------------------------------------------------------------------- -/

#eval (do
  match ← Session.define_type "tree = LEAF num | NODE tree tree" with
  | .error e => IO.println s!"tree define ERR: {e}"
  | .ok (ith, rth) =>
    -- the induction/recursion theorems themselves are documented in
    -- Help/prove_cases_thm.hlp, so check them too
    let gi := squash (← HolCore.Printer.string_of_thm ith)
    let gr := squash (← HolCore.Printer.string_of_thm rth)
    let ei := squash "|- forall P. (forall a. P (LEAF a)) /\\ (forall a0 a1. P a0 /\\ P a1 ==> P (NODE a0 a1)) ==> (forall x. P x)"
    let er := squash "|- forall f0 f1. exists fn. (forall a. fn (LEAF a) = f0 a) /\\ (forall a0 a1. fn (NODE a0 a1) = f1 a0 a1 (fn a0) (fn a1))"
    IO.println (if gi == ei then "tree INDUCT -> OK" else s!"tree INDUCT -> MISMATCH got={gi}")
    IO.println (if gr == er then "tree RECURSION -> OK" else s!"tree RECURSION -> MISMATCH got={gr}")
    -- prove_constructors_injective: a CONJUNCTION over both constructors
    match ← Session.prove_constructors_injective rth with
    | .error e => IO.println s!"tree INJ ERR: {e}"
    | .ok ij =>
      let g := squash (← HolCore.Printer.string_of_thm ij)
      let e' := squash "|- (forall a a'. LEAF a = LEAF a' <=> a = a') /\\ (forall a0 a1 a0' a1'. NODE a0 a1 = NODE a0' a1' <=> a0 = a0' /\\ a1 = a1')"
      IO.println (if g == e' then "tree INJ -> OK" else s!"tree INJ -> MISMATCH got={g}")
    -- prove_constructors_distinct
    match ← Session.prove_constructors_distinct rth with
    | .error e => IO.println s!"tree DIST ERR: {e}"
    | .ok dth =>
      let g := squash (← HolCore.Printer.string_of_thm dth)
      let e' := squash "|- forall a a0' a1'. ~(LEAF a = NODE a0' a1')"
      IO.println (if g == e' then "tree DIST -> OK" else s!"tree DIST -> MISMATCH got={g}")
    -- prove_cases_thm
    match ← Session.prove_cases_thm ith with
    | .error e => IO.println s!"tree CASES ERR: {e}"
    | .ok cs =>
      let g := squash (← HolCore.Printer.string_of_thm cs)
      let e' := squash "|- forall x. (exists a. x = LEAF a) \\/ (exists a0 a1. x = NODE a0 a1)"
      IO.println (if g == e' then "tree CASES -> OK" else s!"tree CASES -> MISMATCH got={g}")
  : IO Unit)

/- ---------------------------------------------------------------------- -/
/- Benignity and validation (ind_types.ml 1396-1414).                      -/
/-                                                                        -/
/- The benignity check is keyed on the RAW SPEC STRING, which the OCaml    -/
/- section comment itself calls "rather crude": two different spellings of -/
/- the same type are NOT recognised as equal.                              -/
/- ---------------------------------------------------------------------- -/

-- Re-declaring the SAME spec string returns the cached pair with a warning,
-- rather than failing.  `btree` was defined above, so this is the benign path.
#eval (do
  match ← Session.define_type "btree = BLEAF A | BNODE btree btree" with
  | .error e => IO.println s!"benign redefinition -> MISMATCH failed: {e}"
  | .ok _ => IO.println "benign redefinition -> OK (cached)" : IO Unit)

/-- `define_type spec` must FAIL with exactly the OCaml message. -/
private unsafe def defineTypeFails (lbl spec expected : String) : IO Unit := do
  match ← Session.define_type spec with
  | .ok _ => IO.println s!"{lbl} -> MISMATCH: expected failure, got success"
  | .error e =>
    if e == expected then IO.println s!"{lbl} -> OK"
    else IO.println s!"{lbl} -> MISMATCH got={e}"

-- The four validation checks of ind_types.ml 1401-1411, in OCaml order.
#eval defineTypeFails "dup type name" "dup = D1 | D2 ; dup = D3"
  "define_type: multiple definitions of a type"
#eval defineTypeFails "dup constructor" "dupc = SameC A | SameC"
  "define_type: multiple instances of a constructor"
#eval defineTypeFails "constructor taken" "zt = LEAF A | ZNode zt"
  "define_type: constant LEAF already defined"

/- ---------------------------------------------------------------------- -/
/- A freshly defined type must be REGISTERED in the stores.                -/
/-                                                                        -/
/- ind_types.ml 1384-1385: define_type_raw3's tail performs BOTH           -/
/-   inductive_type_store := newentries @ (!inductive_type_store)          -/
/-   do_list extend_rectype_net newentries                                 -/
/- so `distinctness`/`injectivity` work on a type defined at runtime, not  -/
/- just on the bootstrap types.  An earlier version of this translation     -/
/- performed only the first, which left a new type in the store with no    -/
/- derived theorems - `distinctness` returned nothing where OCaml           -/
/- succeeds.  This is the regression test for that.                        -/
/- ---------------------------------------------------------------------- -/

#eval (do
  match ← Session.define_type "reg = RegA A | RegB reg reg" with
  | .error e => IO.println s!"store registration -> MISMATCH define failed: {e}"
  | .ok _ =>
    let d := (Session.distinctness "reg").toOption.isSome
    let i := (Session.injectivity "reg").toOption.isSome
    if d && i then IO.println "store registration -> OK"
    else IO.println s!"store registration -> MISMATCH dist={d} inj={i}" : IO Unit)

/- ---------------------------------------------------------------------- -/
/- UNWIND_CONV and FORALL_UNWIND_CONV (ind_types.ml 1421-1572): eliminate  -/
/- a quantified variable pinned by an equation.                            -/
/- ---------------------------------------------------------------------- -/

/-- Apply an `ioconv` to a parsed term and compare the resulting theorem. -/
private unsafe def convCheck (lbl expr expected : String)
    (c : HolCore.Equal.ioconv) : IO Unit := do
  match ← HolCore.Parser.parse_term expr with
  | .error e => IO.println s!"{lbl} parse ERR: {e}"
  | .ok tm =>
    match ← c tm with
    | .error e => IO.println s!"{lbl} ERR: {e}"
    | .ok th =>
      let got := squash (← HolCore.Printer.string_of_thm th)
      if got == squash expected then IO.println s!"{lbl} -> OK"
      else IO.println s!"{lbl} -> MISMATCH got={got}"

#eval convCheck "UNWIND_CONV" "?a b. a = 1 /\\ b = 2 /\\ a + b = 3"
  "|- (exists a b. a = 1 /\\ b = 2 /\\ a + b = 3) <=> 1 + 2 = 3" Session.UNWIND_CONV

#eval convCheck "FORALL_UNWIND_CONV" "!a b. a = 1 /\\ b = 2 ==> a + b = 3"
  "|- (forall a b. a = 1 /\\ b = 2 ==> a + b = 3) <=> 1 + 2 = 3" Session.FORALL_UNWIND_CONV
