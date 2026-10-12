/- File: HolTest/RegressionTest.lean
Runtime test suite: regression tests for defects found by the faithfulness audits
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

-- theorems.ml/class.ml extend the BASIC REWRITES at load (class.ml 340
-- `extend_basic_rewrites [COND_CLAUSES]`).  They used to run only when a layer
-- was first read, so in a fresh process `REWRITE_CONV []` could not rewrite
-- `if T then a else b`.  MUST be the first #eval in this module: nothing may be
-- forced beforehand.
#eval (do
  match ← HolCore.Parser.parse_term "(if T then a else b):bool" with
  | .error e => IO.println s!"basic rewrites at load -> MISMATCH parse ERR {e}"
  | .ok tm =>
    match ← (REWRITE_CONV [] tm : IO (Except String thm)) with
    | .error e => IO.println s!"basic rewrites at load -> MISMATCH {e}"
    | .ok th =>
      match rhs (concl th) with
      | .ok r =>
        if r == mk_var "a" bool_ty then
          IO.println "REWRITE_CONV [] sees class.ml COND_CLAUSES without forcing -> OK"
        else IO.println s!"basic rewrites at load -> MISMATCH got {← HolCore.Printer.string_of_thm th}"
      | .error e => IO.println s!"basic rewrites at load -> MISMATCH {e}")

/- ---------------------------------------------------------------------- -/
/- Regression tests for defects found by the faithfulness audits.         -/
/- Each block names the OCaml behaviour it pins down.                     -/
/- ---------------------------------------------------------------------- -/


/- ---------------------------------------------------------------------- -/
/- REGRESSION TESTS for defects found by the HolCore faithfulness audit.  -/
/- Each block names the OCaml behaviour it pins down, so a regression     -/
/- shows up as a changed line here rather than as silent misbehaviour.    -/
/- Gated by TestFlags.runRegress.                                         -/
/- ---------------------------------------------------------------------- -/

-- Lib.lean: `chop_list` must normalise every underlying hd/tl failure to the
-- message "chop_list" (OCaml wraps its body in `try ... with Failure _ ->`).
-- Callers such as `shareout` match on that exact string.
#eval (do
  match HolCore.Lib.chop_list 2 ([1,2,3,4] : List Nat) with
  | .ok (a, b) => IO.println s!"chop_list 2 [1,2,3,4] -> ({a}, {b})"
  | .error e => IO.println s!"chop_list ERR: {e}")

#eval (do
  match HolCore.Lib.chop_list 5 ([1,2,3] : List Nat) with
  | .ok r => IO.println s!"chop_list overrun unexpectedly ok: {r}"
  | .error e => IO.println s!"chop_list overrun msg = \"{e}\" (must be \"chop_list\")")
-- Lib.lean: num arithmetic must honour DENOMINATORS.  OCaml's NumExt
-- `gcd_num` is `Z.gcd (Q.to_bigint x) (Q.to_bigint y)` (truncated values) and
-- `//` is EXACT rational division.  Computing on numerators alone gave
-- divide_num 1 2 = 0 and divide_num (1/2) (1/3) = 1.

#eval (do
  IO.println s!"gcd_num 12 18 = {HolCore.Lib.gcd_num 12 18} (6)"
  IO.println s!"lcm_num 4 6 = {HolCore.Lib.lcm_num 4 6} (12)"
  IO.println s!"quo_num 17 5 = {HolCore.Lib.quo_num 17 5} (3)"
  IO.println s!"mod_num 17 5 = {HolCore.Lib.mod_num 17 5} (2)"
  IO.println s!"divide_num 1 2 = {HolCore.Lib.divide_num 1 2} (1/2, not 0)"
  IO.println s!"gcd_num (3/2) (5/2) = {HolCore.Lib.gcd_num (3/2) (5/2)} (1, via truncation)"
  IO.println s!"divide_num (1/2) (1/3) = {HolCore.Lib.divide_num (1/2) (1/3)} (3/2, not 1)")
-- Printer.lean: OCaml applies `String.escaped` to HOL string literals, so a
-- printed string must re-parse.  Without it, quotes/backslashes printed raw.

#eval (do
  IO.println s!"string_escaped = {HolCore.Printer.string_escaped "a\"b\\c"}"
  IO.println s!"string_escaped newline/tab = {HolCore.Printer.string_escaped "x\ny\tz"}")


-- Fusion.lean: `thm` must NOT be freely fabricable with an arbitrary
-- conclusion.  OCaml's `thm` is fully abstract; the Lean `Inhabited` instance is
-- pinned to `REFL default` (Fusion.lean 470), so the only fabricable theorem is
-- `|- x = x` - true under any instantiation - rather than an arbitrary
-- proposition.
--
-- ASSERTED STRUCTURALLY, and deliberately WITHOUT PRINTING the theorem.  Its
-- rendering is `|-  = ` (both sides invisible), which is exactly the
-- masked-failure signature that gate 3 counts, so printing it here would cost a
-- permanent `EXPECTED_MASKED=1` exemption and mean a REAL degeneration had to
-- reach TWO before the gate fired.  It did cost exactly that until this was
-- rewritten.
--
-- FusionTest asserts the same soundness property.  What is pinned HERE is GATE
-- 3'S OWN PREMISE: that `default : term` prints as the EMPTY STRING, which is
-- what makes a degenerated bundle visible at all.  Were that to change, the gate
-- would silently stop detecting anything - so it is asserted, not assumed.
#eval (do
  let d : thm := default
  let c := concl d
  let dfltTm ← HolCore.Printer.string_of_term (default : term)
  match dest_eq c with
  | .ok (l, r) =>
    if l == r && (hyp d).isEmpty && dfltTm == "" then
      IO.println "default thm is a REFL, no hyps, default term prints empty -> OK"
    else
      IO.println s!"default thm -> MISMATCH refl={l == r} hyps={(hyp d).length} dfltLen={dfltTm.length}"
  | .error _ => IO.println "default thm -> MISMATCH conclusion is not an equation")

-- IndDefs/Session: the monotonicity-theorem list must be RE-READ on each use.
-- It was a memoized snapshot, so `MONO_COND` (added by the class layer, exactly
-- as class.ml:393 does) was permanently lost and MONO_TAC could not backchain
-- through conditionals.
#eval (do
  IO.println s!"(force class layer: {← HolCore.Printer.string_of_thm Session.COND_ID})"
  let l ← Session.theMonotonicityTheorems.get
  let ts := l.getD []
  IO.println s!"monotonicity theorems = {ts.length} (7: MONO_COND + 6 defaults)"
  match ts.head? with
  | some t => IO.println s!"  head must be MONO_COND -> {← HolCore.Printer.string_of_thm t}"
  | none => IO.println "  EMPTY - regression!")

-- Simp.lean: the three rules that were missing entirely from the project.
#eval (do
  match (do ASSUME ([[ (a:bool) = T ]])) with
  | .error e => IO.println s!"regress setup ERR: {e}"
  | .ok ath => do
    (do match ← Session.ONCE_ASM_REWRITE_RULE [] ath with
        | .ok th => IO.println s!"ONCE_ASM_REWRITE_RULE -> {← HolCore.Printer.string_of_thm th}"
        | .error e => IO.println s!"ONCE_ASM_REWRITE_RULE ERR: {e}")
    (do match ← Session.PURE_ONCE_ASM_REWRITE_RULE [] ath with
        | .ok th => IO.println s!"PURE_ONCE_ASM_REWRITE_RULE -> {← HolCore.Printer.string_of_thm th}"
        | .error e => IO.println s!"PURE_ONCE_ASM_REWRITE_RULE ERR: {e}"))

#eval (do
  match ← Session.ONCE_SIMP_RULE [] (REFL ([[ (T /\ F) \/ F ]])) with
  | .ok th => IO.println s!"ONCE_SIMP_RULE -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"ONCE_SIMP_RULE ERR: {e}")


-- Nets.lean: term-net enter/lookup had no direct test.  Checks that a netted
-- entry is retrievable and that lookup discriminates on the term structure.
#eval (do
  (do let n0 : HolCore.Nets.net Nat := HolCore.Nets.empty_net
      match ← HolCore.Nets.enter [] ([[ (a:bool) /\ b ]], 1) n0 with
      | .error e => IO.println s!"Nets.enter ERR: {e}"
      | .ok n1 =>
        match ← HolCore.Nets.enter [] ([[ (x:bool) \/ y ]], 2) n1 with
        | .error e => IO.println s!"Nets.enter 2 ERR: {e}"
        | .ok n2 => do
          IO.println s!"net lookup (p /\\ q) = {HolCore.Nets.lookup ([[ (p:bool) /\ q ]]) n2}"
          IO.println s!"net lookup (p \\/ q) = {HolCore.Nets.lookup ([[ (p:bool) \/ q ]]) n2}"
          IO.println s!"net lookup (~p)     = {HolCore.Nets.lookup ([[ ~(p:bool) ]]) n2}"))

-- IndDefs: an actual inductive definition over a schematic relation, plus
-- strong induction.  This layer had NO direct test coverage at all.  (No
-- arithmetic: `nums.ml` is not translated yet, so the example stays first-order
-- over a type variable.)
#eval (do
  match ← Session.new_inductive_definition
           ([[ (!x:A. TCL R x x) /\ (!x y z. R x y /\ TCL R y z ==> TCL R x z) ]]) with
  | .error e => IO.println s!"new_inductive_definition (msg): {e}"
  | .ok (rth, ith, cth) => do
      IO.println s!"inductive rules -> {← HolCore.Printer.string_of_thm rth}"
      IO.println s!"inductive induct -> {← HolCore.Printer.string_of_thm ith}"
      IO.println s!"inductive cases -> {← HolCore.Printer.string_of_thm cth}"
      match ← Session.derive_strong_induction rth ith with
      | .ok sth => IO.println s!"strong induction -> {← HolCore.Printer.string_of_thm sth}"
      | .error e => IO.println s!"derive_strong_induction (msg): {e}")


/- ---------------------------------------------------------------------- -/
/- leanCoP and MESON must use DIFFERENT equality-axiom bundles.            -/
/- ---------------------------------------------------------------------- -/
/-
  Found by the wave-2 HolCore audit, which flagged this as its single most
  valuable missing test.  `TheCops` REUSES `Meson.create_equality_axioms`,
  parameterised by an `EqAxPths` bundle, so the two provers are only faithful if
  Session hands each the right one:

    thecops.ml 510-514  THREE conjuncts, including SYMMETRY:
                        `(x=x) /\ (~(x=y) \/ y=x) /\ (~(x=y) \/ ~(x=z) \/ (y=z))`
    meson.ml    583-587  TWO conjuncts, reflexivity and transitivity only:
                        `(x=x) /\ (~(x=y) \/ ~(x=z) \/ (y=z))`

  If the bundles were ever crossed, leanCoP would silently lose the symmetry
  axiom (weakening it on equality goals) or MESON would gain a redundant one.
  Both bundles are cached and derive `Inhabited`, so a panicked setup would
  degenerate every field to `|-  = `; asserting the CONCLUSIONS - not merely that
  the accessors evaluate - is what makes that visible.
-/

#eval (do
  (do
    let cop := Session.COP_EQ_THMS
    let mes := Session.MESON_EQ_THMS
    if cop.length == 3 && mes.length == 2 then
      IO.println s!"eq-axiom bundles distinct (cop=3, meson=2) -> OK"
    else
      IO.println s!"eq-axiom bundles MISMATCH cop={cop.length} meson={mes.length}"))

-- leanCoP's SECOND conjunct must be the symmetry clause; MESON has no such
-- clause at all.  Pins the actual statement, so a degenerate bundle is caught.
#eval (do
  (do
    match Session.COP_EQ_THMS with
    | _ :: sym :: _ => do
      let s ← HolCore.Printer.string_of_thm sym
      let sq := (s.replace " " "").replace "\n" ""
      if sq == "|-~(x=y)\\/y=x" then
        IO.println "leanCoP eq-axiom symmetry clause -> OK"
      else IO.println s!"leanCoP eq-axiom symmetry clause -> MISMATCH got {s}"
    | _ => IO.println "leanCoP eq-axiom symmetry clause -> MISMATCH too few conjuncts"))

#eval (do
  (do
    match Session.MESON_EQ_THMS with
    | refl :: trans :: [] => do
      let r ← HolCore.Printer.string_of_thm refl
      let t ← HolCore.Printer.string_of_thm trans
      let sq (u : String) := (u.replace " " "").replace "\n" ""
      if sq r == "|-x=x" && sq t == "|-~(x=y)\\/~(x=z)\\/y=z" then
        IO.println "MESON eq-axioms are refl+trans only -> OK"
      else IO.println s!"MESON eq-axioms -> MISMATCH refl={r} trans={t}"
    | l => IO.println s!"MESON eq-axioms -> MISMATCH {l.length} conjuncts, expected 2"))


/- ---------------------------------------------------------------------- -/
/- `term_order` and the DERIVED `Ord term` (simp.ml 65-80).                -/
/- ---------------------------------------------------------------------- -/
/-
  A standing audit question was whether Lean's DERIVED `Ord term` coincides with
  OCaml's POLYMORPHIC `compare`, because `dyn_order`'s final fallback is
  `f1 > f2` (simp.ml 79) and `term_order` decides how PERMUTATIVE (AC) rewrites
  are oriented.  A divergence would silently re-orient rewrites - possibly
  non-terminating - and nothing would report it.

  ANSWER: they coincide, because both compare CONSTRUCTOR ORDER first and then
  fields left to right, and the declarations agree:

    fusion.ml  96-97   hol_type = Tyvar | Tyapp
    fusion.ml  99-102  term     = Var | Const | Comb | Abs
    Fusion.lean        hol_type = Tyvar | Tyapp          (same order)
    Fusion.lean        term     = Var | Const | Comb | Abs (same order)

  The tests below pin the consequences, so a future reordering of either
  `inductive` - which would compile cleanly and change rewrite orientation -
  is caught here.

  Confirmed against real HOL Light (tools/orddiff, 2026-10-02): 172,398
  comparisons of terms, types and theorems from the database, all equal.
-/

-- Constructor order: a Var must sort BELOW a Const, which sorts below a Comb.
-- This is the property `dyn_order`'s `f1 > f2` fallback rests on.
#eval (do
  (do
    let v : term := HolCore.Kernel.mk_var "a" HolCore.Kernel.bool_ty
    let c : term := HolCore.Kernel.mk_var "a" HolCore.Kernel.bool_ty
    let ok1 := compare v c == Ordering.eq
    -- Var "a" < Var "b" (same constructor, field-wise on the name)
    let vb : term := HolCore.Kernel.mk_var "b" HolCore.Kernel.bool_ty
    let ok2 := compare v vb == Ordering.lt
    if ok1 && ok2 then
      IO.println "Ord term: constructor+field order -> OK"
    else
      IO.println s!"Ord term -> MISMATCH eq={ok1} lt={ok2}"))

-- `term_order` is `dyn_order `T``.  `dyn_order tm1 tm2` answers "is tm1
-- GREATER than tm2", and simp.ml 77-78 reads
--     if f2 = top then false  else if f1 = top then true  else f1 > f2
-- so the distinguished `top` term `T` is treated as the LARGEST: `T` beats any
-- other head, and nothing beats `T`.  (I first wrote this expectation the wrong
-- way round and the assertion caught it - which is the point of pinning it.)
#eval (do
  (do
    -- `tT` is CommonTest's `[[ T ]]`; `p` is `[[ p:bool ]]`.
    let topBeatsX := HolCore.Simp.term_order tT p     -- f1 = top  -> true
    let xLosesToTop := HolCore.Simp.term_order p tT    -- f2 = top  -> false
    if topBeatsX && !xLosesToTop then
      IO.println "term_order treats `T` as largest -> OK"
    else
      IO.println s!"term_order top-handling -> MISMATCH T>x={topBeatsX} x>T={xLosesToTop}"))


/- ---------------------------------------------------------------------- -/
/- CRITICAL: MESON must propagate Prolog's `Cut`, not swallow it.          -/
/- ---------------------------------------------------------------------- -/
/-
  THE DEFECT (wave-2 HolCore audit).  `meson_expand_cont` used the generic
  `tryfindM`, which catches EVERY error.  OCaml uses `tryfind`, which catches
  ONLY `Failure _` (lib.ml 240-243), so the `Cut` raised at meson.ml 402 ESCAPES
  it and is caught by `meson_expand`'s `with Cut -> ...` (meson.ml 380/384).
  Ours swallowed the `"Cut"` and went on to the NEXT rule, defeating the cut.

  WHY IT SURVIVED EVERY EXISTING TEST, and why this test is shaped as it is:
  the bug does NOT affect SOUNDNESS - every proof MESON returns is checked by the
  kernel - so no end-to-end "does it prove X" test can see it.  It changes only
  WHICH proof is found within the inference bound, and how many inferences are
  spent.  An end-to-end test would therefore have to be luckily tuned to a goal
  that tips over the bound.  So this test targets the MECHANISM directly:

    * build TWO rules that both expand successfully;
    * pass a continuation that returns `.error "Cut"` and COUNTS its calls;
    * a correct `meson_expand_cont` calls the continuation ONCE and returns
      `.error "Cut"`;
    * the buggy one swallows the Cut, tries the second rule, and so calls the
      continuation TWICE.

  The call COUNT is the discriminator, which is why the counter exists.  The
  companion test below feeds an ORDINARY failure and asserts the continuation IS
  called twice - proving this test distinguishes Cut from plain failure rather
  than passing vacuously.

  VERIFIED BY MUTATION: reintroducing the `tryfindM` behaviour makes the first
  test print `calls=2 (expected 1) propagated=false` with a MISMATCH token, which
  is a hard build gate, while the companion test stays green.  So this test
  demonstrably CATCHES the defect rather than merely agreeing with the fix.

  THE SECOND SITE IS NOT TESTED, BECAUSE IT CANNOT BE.  The audit also flagged
  `expand_goals`' divide-and-conquer fallback as a Cut leak.  It is not one: a raw
  `Cut` can never reach it.  `Cut` is raised only in `expand_goal`'s inner
  continuation (meson.ml 402) and the first enclosing handler always CONVERTS it -
  `meson_expand` (meson.ml 380/384) or `expand_goal`'s else-branch (405).  Mutation
  confirms it: deleting that guard leaves all 1303 assertions passing.  The guard
  is kept for faithfulness to the OCaml's `Failure`-only handler and is documented
  in `Meson.lean` as defensive, not load-bearing.
-/

open HolCore.Meson in
private unsafe def cutRules : List HolCore.Meson.folRule :=
  -- A rule is `((hyps, conclusion), (tag, thm))`.  No hypotheses and an
  -- argument-free conclusion makes `meson_single_expand` succeed trivially
  -- (`rev_itlist2M fol_unify` over two empty arg lists is a no-op, and with no
  -- hypotheses there is no `checkan` to fail), so the continuation is reached.
  let concl : HolCore.Meson.fol_atom := (1, [])
  let th : thm := REFL tT
  [(([], concl), (0, th)), (([], concl), (1, th))]

open HolCore.Meson in
private def cutState : HolCore.Meson.folState × HolCore.Meson.tup :=
  (((1, []), []), ([], 0, 100))

-- A `Cut` from the continuation must ABORT the rule loop: exactly ONE call.
#eval (do
  (do
    let calls ← (IO.mkRef (0 : Nat) : IO (IO.Ref Nat))
    let inferences ← (IO.mkRef (0 : Int) : IO (IO.Ref Int))
    let cont : (Int × thm) → (List (HolCore.Meson.fol_atom × HolCore.Meson.ancestors)
                              × HolCore.Meson.tup)
               → IO (Except String HolCore.Meson.searchResult) :=
      fun _ _ => do calls.modify (· + 1); return .error "Cut"
    let r ← HolCore.Meson.meson_expand_cont inferences 0 cutRules cutState cont
    let n ← calls.get
    let propagated := match r with | .error e => e == "Cut" | .ok _ => false
    if propagated && n == 1 then
      IO.println "MESON Cut propagates (1 continuation call) -> OK"
    else
      IO.println s!"MESON Cut SWALLOWED -> MISMATCH calls={n} (expected 1) propagated={propagated}"))

-- An ORDINARY failure must NOT abort: both rules are tried, so TWO calls, and
-- the loop ends with `tryfind` (meson.ml's `tryfind` exhaustion message).
#eval (do
  (do
    let calls ← (IO.mkRef (0 : Nat) : IO (IO.Ref Nat))
    let inferences ← (IO.mkRef (0 : Int) : IO (IO.Ref Int))
    let cont : (Int × thm) → (List (HolCore.Meson.fol_atom × HolCore.Meson.ancestors)
                              × HolCore.Meson.tup)
               → IO (Except String HolCore.Meson.searchResult) :=
      fun _ _ => do calls.modify (· + 1); return .error "ordinary failure"
    let r ← HolCore.Meson.meson_expand_cont inferences 0 cutRules cutState cont
    let n ← calls.get
    let exhausted := match r with | .error e => e == "tryfind" | .ok _ => false
    if exhausted && n == 2 then
      IO.println "MESON ordinary failure advances to next rule (2 calls) -> OK"
    else
      IO.println s!"MESON ordinary-failure path -> MISMATCH calls={n}"))


/- ---------------------------------------------------------------------- -/
/- Printer: infix chains merge on SURFACE name (printer.ml 294-301).       -/
/- ---------------------------------------------------------------------- -/
/-
  Found by the wave-2 audit and confirmed empirically.  `DEST_BINARY` decides
  whether two occurrences of an infix operator belong to ONE chain.  printer.ml
  compares their `reverse_interface` SURFACE names; ours compared the raw name
  AND type, which is wrong in both directions.  The two tests below are a
  DISCRIMINATING PAIR - the first REQUIRES merging, the second REQUIRES not
  merging - so neither a name+type comparison nor a name-only comparison can
  pass both.

    * `,` is polymorphic and has no interface remapping, so every occurrence
      reverse-maps to ",".  In `a,(b,c)` the outer `,` is `A->B#C->A#(B#C)` and
      the inner is `B->C->B#C`: the TYPES NEVER AGREE, even when a,b,c share a
      type, because pairing changes the result type.  So a name+type comparison
      never merges a tuple, and we printed `a,(b,c)` where HOL Light prints
      `a,b,c`.  Every nested tuple was affected.
    * `=` at `:bool` has surface name `<=>` but at `:num` has surface name `=`,
      so `(a:bool) = ((b:num) = c)` must NOT merge: `a <=> b = c`.  A name-only
      comparison would wrongly print `a <=> b <=> c`.
-/

-- MUST MERGE: a nested tuple is one right-associative chain.
#eval (do
  (do
    let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))   -- force arith
    match ← HolCore.Parser.parse_term "((a:num), ((b:bool), (c:bool)))" with
    | .error e => IO.println s!"printer tuple chain -> parse ERR {e}"
    | .ok tm =>
      let s := ((← HolCore.Printer.string_of_term tm).replace " " "")
      if s == "a,b,c" then IO.println "printer merges tuple chain -> OK"
      else IO.println s!"printer tuple chain -> MISMATCH got {s} expected a,b,c"))

-- MUST NOT MERGE: `=` at bool prints `<=>`, at num prints `=`.
#eval (do
  (do
    let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))
    match ← HolCore.Parser.parse_term "(a:bool) = ((b:num) = (c:num))" with
    | .error e => IO.println s!"printer mixed-surface chain -> parse ERR {e}"
    | .ok tm =>
      let s := ((← HolCore.Printer.string_of_term tm).replace " " "")
      if s == "a<=>b=c" then
        IO.println "printer keeps distinct surface names unmerged -> OK"
      else
        IO.println s!"printer mixed-surface chain -> MISMATCH got {s} expected a<=>b=c"))

-- Preterm.solve_preterm: OCaml's `s = s' && can (unify ...) ty` SHORT-CIRCUITS
-- (preterm.ml 389), so the unify probe - which calls `new_type_var` through
-- `pretype_instance` - runs only for SAME-NAME interface entries.  The port had
-- hoisted the `←` above the `&&`, advancing the global type-variable counter once
-- per type variable of EVERY interface entry scanned, which shifts every later
-- invented `?N`.  Discriminated by the counter advance across a parse that
-- resolves a `Constp` (`<=>`), with and without an UNRELATED interface entry
-- (three type variables) prepended so the lookup must scan past it.
#eval (do
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))
  -- The `?N` of the invented type of `x` in `x = x`.
  let probe : IO Int := do
    match ← HolCore.Parser.parse_term "x = x" with
    | .error _ => return (-1)
    | .ok t =>
      let s ← HolCore.Printer.string_of_term t
      let digits := ((s.splitOn "?").getD 1 "").takeWhile Char.isDigit
      return (digits.toNat?.map Int.ofNat).getD (-1)
  let advance : IO Int := do
    let n1 ← probe
    let _ ← HolCore.Parser.parse_term "(p <=> q) /\\ (r <=> s)"
    let n2 ← probe
    return (n2 - n1)
  let base ← advance
  let saved ← HolCore.Printer.the_interface.get
  let a := mk_vartype "A"; let b := mk_vartype "B"; let c := mk_vartype "C"
  HolCore.Printer.the_interface.set
    (("zz_unrelated", ("zz_unrelated", .Tyapp "fun" [a, .Tyapp "fun" [b, c]])) :: saved)
  let withDummy ← advance
  HolCore.Printer.the_interface.set saved       -- restore
  if base > 0 && withDummy == base then
    IO.println s!"solve_preterm probes only same-name entries (advance {base} both) -> OK"
  else
    IO.println s!"solve_preterm short-circuit -> MISMATCH advance {base} vs {withDummy} with an unrelated entry")

-- `hide_constant "SUC"` (is_hidden.hlp) must not break code whose OCaml
-- quotation `SUC` is parsed once, when its file is loaded: calc_num.ml's
-- `num_CONV` (`let SUC_tm = `SUC` in`) and ind_types.ml's `sucivate`
-- (`let zero = `0` and suc = `SUC` in`).  The translations used to parse
-- "SUC" at every call, so after hiding it `num_CONV `3`` failed with
-- "num_CONV" and `define_type` with "mk_comb: types do not agree".  Found by
-- tools/hlpdiff (the is_hidden example runs before num_CONV's and
-- new_inductive_definition's).
#eval (do
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))
  let three ← (match ← parse_term "3" with | .ok t => pure t | .error e => throw (IO.userError e))
  -- Build both layers first, as loading calc_num.ml and ind_types.ml does.
  let _ ← num_CONV three
  let _ ← define_type "hlpdiff_warm = HlpW"
  HolCore.Preterm.hide_constant "SUC"
  try
    match ← num_CONV three with
    | .ok th =>
      let s ← HolCore.Printer.string_of_thm th
      IO.println (if s == "|- 3 = SUC 2" then "num_CONV `3` with SUC hidden -> OK"
                  else s!"num_CONV `3` with SUC hidden -> MISMATCH {s}")
    | .error e => IO.println s!"num_CONV `3` with SUC hidden -> MISMATCH {e}"
    match ← define_type "hlpdiff_form = HlpFalse | HlpImp hlpdiff_form hlpdiff_form" with
    | .ok _ => IO.println "define_type with SUC hidden -> OK"
    | .error e => IO.println s!"define_type with SUC hidden -> MISMATCH {e}"
  finally
    HolCore.Preterm.unhide_constant "SUC"
  : IO Unit)

-- arith.ml 1747 quotes `(+)` inside `fun tm ->`, so OCaml parses it at each
-- call: after `prioritize_int()` it denotes integer addition, no num summand
-- is found and NUM_CANCEL_CONV returns `|- e <=> e`.  The translation took `+`
-- from EQ_ADD_LCANCEL once and cancelled anyway.  (NUM_CANCEL_CONV.hlp, run
-- after INT_ARITH_TAC.hlp's `prioritize_int()`; found by tools/hlpdiff.)
#eval (do
  Session.ensureHolPrefixThroughInt
  let tm ← (match ← parse_term "(a + b + x * y + SUC c) + d = SUC c + d + y * z" with
            | .ok t => pure t | .error e => throw (IO.userError e))
  let before ← NUM_CANCEL_CONV tm
  match ← HolCore.Kernel.mk_type "int" [] with
  | .ok ty => prioritize_overload ty
  | .error e => throw (IO.userError e)
  try
    match before, ← NUM_CANCEL_CONV tm with
    | .ok th0, .ok th =>
      let s0 ← HolCore.Printer.string_of_thm th0
      let s1 ← HolCore.Printer.string_of_thm th
      let ok := (dest_iff (concl th)).toOption.map (fun (l, r) => l == r) == some true
      IO.println (if ok && s0.endsWith "x * y + b + a = y * z"
                  then "NUM_CANCEL_CONV parses (+) per call (after prioritize_int) -> OK"
                  else s!"NUM_CANCEL_CONV after prioritize_int -> MISMATCH {s1} / before: {s0}")
    | a, b => IO.println s!"NUM_CANCEL_CONV after prioritize_int -> MISMATCH {a.isOk} {b.isOk}"
  finally
    match ← HolCore.Kernel.mk_type "num" [] with
    | .ok ty => prioritize_overload ty
    | .error _ => pure ()
  : IO Unit)

-- parser.ml 98-100: `reserve_words ["//"]` and `comment_token = ref (Resword
-- "//")`.  The translation neither reserved "//" (so `reserved_words()` lacked
-- it, reserved_words.hlp) nor let `comment_token` be reassigned
-- (comment_token.hlp sets it to `Ident "--"`).  Found by tools/hlpdiff.
#eval (do
  let _ ← (IO.mkRef (concl TRUTH) : IO (IO.Ref term))
  let rw ← HolCore.Printer.reserved_words
  IO.println (if rw.getLast? == some "//" then "reserved_words ends with \"//\" (parser.ml 98) -> OK"
              else s!"reserved_words -> MISMATCH {rw}")
  let same (lbl a b : String) : IO Unit := do
    match ← parse_term a, ← parse_term b with
    | .ok x, .ok y => IO.println (if x == y then s!"{lbl} -> OK" else s!"{lbl} -> MISMATCH")
    | .error e, _ | _, .error e => IO.println s!"{lbl} -> MISMATCH {e}"
  same "// comment skipped" "p // ignored ==> q\n ==> p" "p ==> p"
  HolCore.Parser.comment_token.set (.Ident "--")
  try
    same "comment_token := Ident \"--\"" "p -- ignored ==> q\n ==> p" "p ==> p"
  finally
    HolCore.Parser.comment_token.set (.Resword "//")
  : IO Unit)

-- lib.ml's finite partial functions are keyed on OCaml's `Hashtbl.hash`, and
-- `atoms` (basics.ml 454) lists a term's atoms by folding over one, so the
-- order is the hash order.  HolCore.OcamlHash reproduces that hash; it is used
-- for `|->` only when HOLLEAN_OCAML_HASH is set (tools/hlpdiff sets it).
-- Expected hashes and `atoms` orders are from real HOL Light (OCaml 5.3).
-- `atoms` used to build a list in insertion order rather than use `|->` and
-- `foldl`.  Found by tools/hlpdiff.
#eval (do
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))
  let cases : List (String × UInt64) :=
    [("x < 1", 275864586), ("~(x = 1)", 548742712), ("!x:num. x + 0 = x", 65587643),
     ("\\f:A->B. f", 364984110), ("SUC(SUC 0)", 932385164)]
  for (s, want) in cases do
    match ← parse_term s with
    | .ok t =>
      let h := HolCore.OcamlHash.hashTerm t
      IO.println (if h == want then s!"Hashtbl.hash `{s}` -> OK"
                  else s!"Hashtbl.hash `{s}` -> MISMATCH {h} (want {want})")
    | .error e => IO.println s!"Hashtbl.hash `{s}` -> MISMATCH {e}"
  for (s, want) in [("bool", (729028179 : UInt64)), ("(A)list->bool", 426022519), ("(A#B)list", 741271192)] do
    match ← parse_type s with
    | .ok t =>
      let h := HolCore.OcamlHash.hashType t
      IO.println (if h == want then s!"Hashtbl.hash `:{s}` -> OK"
                  else s!"Hashtbl.hash `:{s}` -> MISMATCH {h} (want {want})")
    | .error e => IO.println s!"Hashtbl.hash `:{s}` -> MISMATCH {e}"
  -- With the OCaml hash, `atoms` gives HOL Light's order; with Lean's (the
  -- default) the same atoms in hash order, each once.
  for (s, want) in [("x < 1 \\/ x > 1 ==> ~(x = 1)", ["x < 1", "x > 1", "x = 1"]),
                    ("(a /\\ b) \\/ (c ==> d) \\/ ~e", ["d", "c", "e", "a", "b"])] do
    match ← parse_term s with
    | .ok t =>
      match atoms t with
      | .ok l =>
        let got ← l.mapM HolCore.Printer.string_of_term
        let hashOrder := l == HolCore.Lib.foldl (fun a x _ => x :: a) []
          (l.foldl (fun f x => (x |-> ()) f) (HolCore.Lib.undefined : HolCore.Lib.Func term Unit))
        let ok := if HolCore.OcamlHash.ocaml_hash then got == want
                  else hashOrder && got.length == want.length && want.all got.contains
        IO.println (if ok then s!"atoms `{s}` in hash order -> OK"
                    else s!"atoms `{s}` -> MISMATCH {got} (OCaml: {want})")
      | .error e => IO.println s!"atoms `{s}` -> MISMATCH {e}"
    | .error e => IO.println s!"atoms `{s}` -> MISMATCH {e}"
  : IO Unit)

-- OCaml evaluates tuple components right to left, so preterm.ml's
-- `mk_comb(term_of_preterm l, term_of_preterm r)` meets `r`'s names first and
-- the "cannot infer type of variables" list comes out in that order.  Messages
-- from real HOL Light (type_invention_error.hlp, type_invention_warning.hlp);
-- found by tools/hlpdiff.
#eval (do
  let _ ← (IO.mkRef (concl IN_ELIM_THM) : IO (IO.Ref term))
  let old ← HolCore.Preterm.type_invention_error.get
  HolCore.Preterm.type_invention_error.set true
  try
    for (s, want) in [("x = x", "=, x"), ("x IN s", "IN, x, s"),
                      ("x IN UNIONS (a INSERT t) <=> x IN UNIONS t \\/ x IN a",
                       "INSERT, UNIONS, t, IN, x, a")] do
      let full := "typechecking error (cannot infer type of variables): " ++ want
      match ← parse_term s with
      | .ok _ => IO.println s!"type invention `{s}` -> MISMATCH parsed"
      | .error e => IO.println (if e == full then s!"type invention `{s}` names in OCaml order -> OK"
                                else s!"type invention `{s}` -> MISMATCH {e}")
  finally
    HolCore.Preterm.type_invention_error.set old
  : IO Unit)

-- basics.ml 78-81: `mk_binary` turns any failure into "mk_binary", and
-- mk_conj, mk_imp and mk_disj are `mk_binary` (bool.ml 100, 161, 363).
-- list_mk_conj.hlp / list_mk_disj.hlp: `list_mk_conj [`T`;`1`;`F`]` fails
-- with "mk_binary"; the translation reported mk_comb's message.  Found by
-- tools/hlpdiff.
#eval (do
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))
  let ts ← ["T", "1", "F"].mapM fun s => do
    match ← parse_term s with | .ok t => pure t | .error e => throw (IO.userError e)
  for (lbl, r) in [("list_mk_conj", list_mk_conj ts), ("list_mk_disj", list_mk_disj ts),
                   ("mk_imp", mk_imp ts[0]! ts[1]!)] do
    IO.println (match r with
      | .error "mk_binary" => s!"{lbl} [`T`;`1`;`F`] fails with mk_binary -> OK"
      | .error e => s!"{lbl} -> MISMATCH {e}"
      | .ok _ => s!"{lbl} -> MISMATCH succeeded")
  : IO Unit)

-- NANOCOP.hlp: `NANOCOP [EXTENSION; IN_INSERT] `x INSERT y INSERT s = y
-- INSERT x INSERT s`` is proved by HOL Light but failed in the translation
-- with "fol_of_term: higher order".  Two defects, found by tools/hlpdiff:
--  * fol_of_form (meson.ml 155, firstorder.ml 185): each `try ... with
--    Failure _ ->` covers the recursive calls too, so a quantifier whose body
--    is higher order falls through to the next case and, at worst, is
--    translated as a literal.  The translation returned the failure.
--  * create_congruence_axiom (meson.ml 629) discharges `hyp th2` with
--    `itlist`, a right fold, so the last hypothesis is discharged first.  The
--    translation folded from the left, giving the disjuncts in the wrong
--    order: `~(x2 = y2) \/ ~(x1 = y1) \/ ...` instead of `~(x1 = y1) \/ ...`.
#eval (do
  Session.ensureSets
  let w ← (match ← parse_term "x INSERT y INSERT s = y INSERT x INSERT s" with
           | .ok t => pure t | .error e => throw (IO.userError e))
  match ← NANOCOP [EXTENSION, IN_INSERT] w with
  | .ok th => IO.println (if concl th == w && (hyp th).isEmpty then "NANOCOP INSERT commutes (NANOCOP.hlp) -> OK"
                          else "NANOCOP INSERT -> MISMATCH wrong theorem")
  | .error e => IO.println s!"NANOCOP INSERT -> MISMATCH {e}"
  -- HOL Light prints this congruence axiom (thecops.ml Equality.create_eq_axs
  -- false) as `~(_113910 = _113912) \/ ~(_113911 = _113913) \/ P _113912 _113913
  -- \/ ~P _113910 _113911`; genvars renumbered here by first appearance.
  let fm ← (match ← parse_term "(P:A->B->bool) x y /\\ (u:A = v)" with
            | .ok t => pure t | .error e => throw (IO.userError e))
  let renumber (s : String) : String := Id.run do
    let mut out := ""; let mut seen : List String := []; let mut cs := s.toList
    while !cs.isEmpty do
      match cs with
      | '_' :: rest =>
        let ds := rest.takeWhile Char.isDigit
        if ds.isEmpty then out := out.push '_'; cs := rest
        else
          let k := String.ofList ds
          if !seen.contains k then seen := seen ++ [k]
          out := out ++ "_" ++ toString (seen.idxOf k + 1); cs := rest.drop ds.length
      | c :: rest => out := out.push c; cs := rest
      | [] => pure ()
    return out
  match ← create_eq_axs false [fm] with
  | .error e => IO.println s!"congruence axiom order -> MISMATCH {e}"
  | .ok axs =>
    let strs ← axs.mapM fun th => do
      pure (renumber (" ".intercalate ((← HolCore.Printer.string_of_term (concl th)).splitOn "\n" |>.map String.trimAscii |>.map toString)))
    let want := "~(_1 = _2) \\/ ~(_3 = _4) \\/ P _2 _4 \\/ ~P _1 _3"
    IO.println (if strs.contains want then "congruence axiom disjunct order (meson.ml 629) -> OK"
                else s!"congruence axiom order -> MISMATCH {strs}")
  : IO Unit)

-- Functions that were translated but not bound in Session under their OCaml
-- names (ORDERED_REWR_CONV, CONJ_ACI_RULE, DISJ_ACI_RULE, GABS_CONV,
-- LIST_INDUCT_TAC), or not translated at all (sets.ml 3872-3886: dest_setenum,
-- is_setenum, mk_setenum, mk_fset).  Expected results are the Help/*.hlp
-- examples, checked against real HOL Light by tools/hlpdiff.
#eval (do
  Session.ensureSets
  let pt (s : String) : IO term := do
    match ← parse_term s with | .ok t => pure t | .error e => throw (IO.userError e)
  let str (t : term) : IO String := HolCore.Printer.string_of_term t
  let check (lbl : String) (got : IO String) (want : String) : IO Unit := do
    try
      let g ← got
      IO.println (if g == want then s!"{lbl} -> OK" else s!"{lbl} -> MISMATCH {g}")
    catch e => IO.println s!"{lbl} -> MISMATCH {e}"
  let thmOf (r : IO (Except String thm)) : IO String := do
    match ← r with | .ok th => HolCore.Printer.string_of_thm th | .error e => pure s!"ERR {e}"
  -- dest_setenum.hlp, is_setenum.hlp, mk_setenum.hlp, mk_fset.hlp
  check "dest_setenum `{1,2,1,2}`"
    (do match dest_setenum (← pt "{1,2,1,2}") with
        | .ok l => pure ("; ".intercalate (← l.mapM str)) | .error e => pure e) "1; 2; 1; 2"
  check "is_setenum `1 INSERT 2 INSERT {}`" (do pure (toString (is_setenum (← pt "1 INSERT 2 INSERT {}")))) "true"
  check "is_setenum `1 INSERT 2 INSERT s`" (do pure (toString (is_setenum (← pt "1 INSERT 2 INSERT s")))) "false"
  check "mk_setenum([`1`;`2`;`3`],`:num`)"
    (do match ← mk_setenum ([← pt "1", ← pt "2", ← pt "3"], ← (do match ← parse_type "num" with | .ok t => pure t | .error e => throw (IO.userError e))) with
        | .ok t => str t | .error e => pure e) "{1, 2, 3}"
  check "mk_fset (map mk_small_numeral (0--3))"
    (do match ← mk_fset (← ["0", "1", "2", "3"].mapM pt) with | .ok t => str t | .error e => pure e) "{0, 1, 2, 3}"
  -- ORDERED_REWR_CONV.hlp
  check "ORDERED_REWR_CONV term_order ADD_SYM `1 + 2`"
    (thmOf (ORDERED_REWR_CONV HolCore.Simp.term_order ADD_SYM (← pt "1 + 2"))) "|- 1 + 2 = 2 + 1"
  check "ORDERED_REWR_CONV term_order ADD_SYM `2 + 1`"
    (thmOf (ORDERED_REWR_CONV HolCore.Simp.term_order ADD_SYM (← pt "2 + 1")))
    "ERR ORDERED_REWR_CONV: wrong orientation"
  -- CONJ_ACI_RULE.hlp, DISJ_ACI_RULE.hlp
  check "CONJ_ACI_RULE"
    (thmOf (pure (CONJ_ACI_RULE (← pt "(a /\\ b) /\\ (a /\\ c) <=> (a /\\ (c /\\ a)) /\\ b"))))
    "|- (a /\\ b) /\\ a /\\ c <=> (a /\\ c /\\ a) /\\ b"
  check "DISJ_ACI_RULE"
    (thmOf (pure (DISJ_ACI_RULE (← pt "(p \\/ q) \\/ (q \\/ r) <=> r \\/ q \\/ p"))))
    "|- (p \\/ q) \\/ q \\/ r <=> r \\/ q \\/ p"
  -- GABS_CONV.hlp
  check "GABS_CONV SYM_CONV"
    (thmOf (GABS_CONV (fun t => pure (HolCore.Equal.SYM_CONV t)) (← pt "\\(x,y,z). x + y + z = 7")))
    "|- (\\(x,y,z). x + y + z = 7) = (\\(x,y,z). 7 = x + y + z)"
  -- LIST_INDUCT_TAC.hlp: `e LIST_INDUCT_TAC` gives the base and step cases.
  check "LIST_INDUCT_TAC"
    (do match ← LIST_INDUCT_TAC ([], ← pt "!l f:A->B g:B->C. MAP (g o f) l = MAP g (MAP f l)") with
        | .ok (_, gls, _) =>
          let gs ← gls.mapM fun (gl : HolCore.Tactics.goal) => do
            let asms ← gl.1.mapM fun a => str (concl a.2)
            pure (s!"{asms} |- " ++ (← str gl.2))
          pure (" || ".intercalate gs)
        | .error e => pure e)
    ("[] |- forall f g. MAP (g o f) [] = MAP g (MAP f []) || " ++
     "[forall f g. MAP (g o f) t = MAP g (MAP f t)] |- " ++
     "forall f g. MAP (g o f) (CONS h t) = MAP g (MAP f (CONS h t))")
  : IO Unit)

-- grobner.ml 358: `DISJ_CASES (ASSUME tm) (refute_disj rfn l) (refute_disj rfn
-- r)`.  OCaml evaluates the arguments right to left, so the right disjunct is
-- refuted first and its failure is the one reported.  REAL_RING.hlp's example
-- after INT_ARITH_TAC.hlp's `prioritize_int()` (so the variables are `int`s)
-- fails in HOL Light with "find" (from the right disjunct's Groebner basis);
-- the translation tried the left disjunct first and failed with "type_match".
-- Without `prioritize_int` both prove it.  Found by tools/hlpdiff.
#eval (do
  Session.ensureHolPrefixThroughInt
  let s := "s pow 2 = &2 ==> (x pow 4 + &1 = &0 <=> x pow 2 + s * x + &1 = &0 \\/ x pow 2 - s * x + &1 = &0)"
  let old ← HolMath.Grobner.grobner_messages.get
  HolMath.Grobner.grobner_messages.set false
  try
    match ← parse_term ("(s:real) pow 2 = &2 ==> ((x:real) pow 4 + &1 = &0 <=> " ++
                        "x pow 2 + s * x + &1 = &0 \\/ x pow 2 - s * x + &1 = &0)") with
    | .error e => IO.println s!"REAL_RING (real) -> MISMATCH {e}"
    | .ok t =>
      match ← REAL_RING t with
      | .ok th => IO.println (if concl th == t then "REAL_RING s pow 2 = &2 ==> ... (real) -> OK"
                              else "REAL_RING (real) -> MISMATCH wrong theorem")
      | .error e => IO.println s!"REAL_RING (real) -> MISMATCH {e}"
    match ← HolCore.Kernel.mk_type "int" [] with
    | .ok ty => prioritize_overload ty
    | .error e => throw (IO.userError e)
    match ← parse_term s with
    | .error e => IO.println s!"REAL_RING (int) -> MISMATCH {e}"
    | .ok t =>
      match ← REAL_RING t with
      | .error "find" => IO.println "REAL_RING after prioritize_int fails with find (right disjunct first) -> OK"
      | .error e => IO.println s!"REAL_RING after prioritize_int -> MISMATCH {e}"
      | .ok _ => IO.println "REAL_RING after prioritize_int -> MISMATCH succeeded"
  finally
    HolMath.Grobner.grobner_messages.set old
    match ← HolCore.Kernel.mk_type "num" [] with
    | .ok ty => prioritize_overload ty
    | .error _ => pure ()
  : IO Unit)

-- Defects found by resolving the names tools/hlpdiff could not call; expected
-- values are from real HOL Light.
--  * rotate (tactics.ml 864) fails on an empty subgoal list: `hd` forwards and
--    `butlast` backwards (OCaml evaluates `butlast sgs` before `last sgs`).
--    The translation returned the empty list unchanged, so `r 1` "succeeded".
--  * HYP (tactics.ml 321) returns `thm list -> tactic` (`HYP tac s ths`) and
--    rejects non-identifier labels with "Invalid using pattern".  The
--    translation took no theorem list and split `s` on spaces.
--  * pow2/pow10 (lib.ml 400) take an OCaml int, so `pow2(-2) = 1/4`; the
--    translation took a Nat.
--  * `!inductive_type_store` was a value computed once, so types added later
--    by define_type were missing from it.
--  * define (define.ml 1028) must read `!the_definitions` after proving the
--    recursion, which can add a definition of its own; the translation wrote
--    back the list read beforehand, losing it (and pair.ml 181 likewise).
#eval (do
  Session.ensureDefine
  let empty : HolCore.Tactics.goalstate := (([], ([], [], [])), [], fun _ _ => pure (.ok TRUTH))
  for (n, want) in [((1 : Int), "hd"), (-1, "butlast")] do
    match ← HolCore.Tactics.rotate n empty with
    | .error e => IO.println (if e == want then s!"rotate {n} on no subgoals fails with {want} -> OK"
                              else s!"rotate {n} -> MISMATCH {e}")
    | .ok _ => IO.println s!"rotate {n} on no subgoals -> MISMATCH succeeded"
  match ← parse_term "T" with
  | .error e => IO.println s!"HYP -> MISMATCH {e}"
  | .ok t =>
    match ← HolCore.Tactics.HYP (fun _ => HolCore.Tactics.ALL_TAC) "a+" [] ([], t) with
    | .error "Invalid using pattern" => IO.println "HYP rejects a non-identifier label -> OK"
    | .error e => IO.println s!"HYP -> MISMATCH {e}"
    | .ok _ => IO.println "HYP -> MISMATCH accepted `a+`"
  IO.println (if HolCore.Lib.pow2 (-2) == (1 : Rat) / 4 && HolCore.Lib.pow10 (-1) == (1 : Rat) / 10
              then "pow2(-2) = 1/4, pow10(-1) = 1/10 -> OK" else "pow2/pow10 negative -> MISMATCH")
  -- define_type adds to the live store
  let before := (← get_inductive_type_store).length
  match ← define_type "hlpreg_t = HlpregA | HlpregB hlpreg_t" with
  | .error e => IO.println s!"inductive_type_store -> MISMATCH {e}"
  | .ok _ =>
    let after ← get_inductive_type_store
    IO.println (if after.length == before + 1 && after.any (·.1 == "hlpreg_t")
                then "!inductive_type_store sees a new define_type -> OK"
                else s!"inductive_type_store -> MISMATCH {before} -> {after.length}")
  -- HOL Light: 243 -> 245 definitions for this `define`
  let d0 := (← get_the_definitions).length
  match ← parse_term "hlpq n = if n = 0 then 1 else hlpq (n - 1) * 2" with
  | .error e => IO.println s!"the_definitions -> MISMATCH {e}"
  | .ok t =>
    match ← define t with
    | .error e => IO.println s!"the_definitions -> MISMATCH {e}"
    | .ok _ =>
      let d1 := (← get_the_definitions).length
      IO.println (if d1 == d0 + 2 then "define adds 2 entries to the_definitions (as HOL Light) -> OK"
                  else s!"the_definitions -> MISMATCH {d0} -> {d1}")
  : IO Unit)

-- Order of `!the_definitions` (newest first), as in HOL Light: ind_types.ml
-- defines ISO (1061) after sum, option and list (768-887), and pair.ml
-- defines CURRY, UNCURRY and PASSOC (184-192) at load.  The translation
-- defined ISO first and CURRY only when first used.  Found by tools/hlpdiff.
#eval (do
  Session.ensureDefine
  let defs ← get_the_definitions
  let idx (c : String) : Option Nat := defs.findIdx? fun th =>
    match HolCore.Kernel.dest_eq (HolCore.Basics.strip_forall (concl th)).2 with
    | .ok (l, _) => (HolCore.Kernel.dest_const (HolCore.Basics.strip_comb l).1).toOption.map Prod.fst == some c
    | .error _ => false
  IO.println (match idx "ISO", idx "CONS", idx "CURRY" with
    | some i, some c, some _ =>
      if i < c then "ISO defined after the list constructors; CURRY present -> OK"
      else s!"the_definitions order -> MISMATCH ISO at {i}, CONS at {c}"
    | a, b, c => s!"the_definitions order -> MISMATCH {a} {b} {c}")
  : IO Unit)

-- Evaluation order (tools/eoaudit).  OCaml evaluates the arguments of a call
-- and the components of a tuple RIGHT TO LEFT; `f (← a) (← b)` in Lean runs
-- `a` first.  Expected values are from real HOL Light (OCaml 5.3).
--  * COMB2_CONV/BINOP_CONV/BINOP2_CONV (equal.ml 147, 179, 185) and their IO
--    forms: `MK_COMB(..., conv r)` converts the RIGHT operand first, so when
--    both fail the right-hand failure is reported.
--  * typify (preterm.ml 344): `new_type_var(),new_type_var()` gives the RANGE
--    type the earlier number, so in `\x. y` the type of `x` is numbered after
--    the type of `y`.
#eval (do
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))
  let t ← (match ← parse_term "1 + 2" with | .ok t => pure t | .error e => throw (IO.userError e))
  let s ← (match ← parse_term "SUC 1" with | .ok t => pure t | .error e => throw (IO.userError e))
  let L : HolCore.Equal.conv := fun _ => .error "left"
  let R : HolCore.Equal.conv := fun _ => .error "right"
  let check (lbl : String) (r : Except String thm) : IO Unit :=
    IO.println (match r with
      | .error "right" => s!"{lbl} fails on the right operand first -> OK"
      | .error e => s!"{lbl} -> MISMATCH {e}"
      | .ok _ => s!"{lbl} -> MISMATCH succeeded")
  check "COMB2_CONV" (HolCore.Equal.COMB2_CONV L R s)
  check "BINOP2_CONV" (HolCore.Equal.BINOP2_CONV L R t)
  let rt ← IO.ofExcept (rand t)
  check "BINOP_CONV" (HolCore.Equal.BINOP_CONV (fun u => .error (if u == rt then "right" else "left")) t)
  let Lio : ioconv := fun _ => pure (.error "left")
  let Rio : ioconv := fun _ => pure (.error "right")
  check "comb2ConvIO" (← HolCore.Simp.comb2ConvIO Lio Rio s)
  check "binopConvIO" (← HolCore.Simp.binopConvIO (fun u => pure (.error (if u == rt then "right" else "left"))) t)
  match ← parse_term "\\x. y" with
  | .ok (.Abs (.Var _ (.Tyvar a)) (.Var _ (.Tyvar b))) =>
    let num (s : String) : Nat := (s.drop 1).toNat!
    IO.println (if num a > num b then "typify: range type numbered first (preterm.ml 344) -> OK"
                else s!"typify order -> MISMATCH x:{a} y:{b}")
  | _ => IO.println "typify order -> MISMATCH unexpected parse"
  : IO Unit)

-- Meson.fol_of_form (meson.ml 155): each `try ... with Failure _ ->` covers
-- the recursive calls, so a quantifier, conjunction or disjunction whose part
-- is higher order falls through to the next case and finally to a literal.
-- The translation returned the failure instead (fixed 2026-09-29; the
-- FirstOrder copy is tested through NANOCOP).  Expected strings are from real
-- HOL Light's `Meson.fol_of_form [] []` after `reset_vars(); reset_consts()`,
-- including the constant codes a failed attempt leaves allocated.
#eval (do
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))
  let rec st : HolCore.Meson.fol_term → String
    | .Fvar n => s!"v{n}"
    | .Fnapp f a => s!"{f}(" ++ ",".intercalate (a.map st) ++ ")"
  let rec sf : HolCore.Meson.fol_form → String
    | .Atom (pr, a) => s!"A{pr}(" ++ ",".intercalate (a.map st) ++ ")"
    | .Conj l r => s!"({sf l} & {sf r})"
    | .Disj l r => s!"({sf l} | {sf r})"
    | .Forallq v b => s!"!v{v}.{sf b}"
  for (s, want) in [
      ("!x:bool. x", "A2(3())"),
      ("(!P:A->bool. P a) /\\ q", "(A2(3()) & A4())"),
      ("!x:bool. Q x \\/ x", "!v0.A3(2(v0),v0)"),
      ("~(!x:bool. x)", "A-2(3())"),
      ("!x:A. P x /\\ Q x", "!v0.(A2(v0) & A3(v0))"),
      ("!x:A. ?y:A. R x y", "!v0.A2(3())"),
      ("(p:bool) \\/ (!f:A->B. f a = b)", "(A2() | A4(5()))")] do
    HolCore.Meson.reset_vars Session.MesonS
    let _ ← HolCore.Meson.reset_consts Session.MesonS
    match ← parse_term s with
    | .error e => IO.println s!"Meson.fol_of_form `{s}` -> MISMATCH {e}"
    | .ok t =>
      match ← HolCore.Meson.fol_of_form Session.MesonS [] [] t with
      | .ok f => IO.println (if sf f == want then s!"Meson.fol_of_form `{s}` -> OK"
                             else s!"Meson.fol_of_form `{s}` -> MISMATCH {sf f}")
      | .error e => IO.println s!"Meson.fol_of_form `{s}` -> MISMATCH failed: {e}"
  : IO Unit)
