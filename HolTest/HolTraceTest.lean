/- File: HolTest/HolTraceTest.lean
Runtime test suite: the HOLTrace proof reconstructor (HolTrace.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Checks the argument encoding against the worked examples published with the
format, then replays whole traces: one that is copied verbatim from the
specification, one built to exercise every inference tag, and a set of
malformed or unsound traces that must each be rejected for the stated reason.

THIS MODULE DOES NOT IMPORT `Session`, and must not.  `Session`'s `initialize`
runs `setupBool` when the module loads, which declares `T`, `/\` and the rest
of HOL Light's constants; replay starts from a BARE kernel, and the traces
below define constants of their own, so those definitions would collide.  That
is also why this file has local reporting helpers instead of importing
`HolTest.CommonTest`.

The kernel's type and constant tables are process-global, so the traces here
share one kernel: between them they define `T`, `ht_k`, `ht_ty`, `hv_ty` and
`hx_ty` exactly once each, and no trace below may be replayed twice.  (That is
a property of replaying into a kernel at all, not of this file: nothing can
retract a constant once the kernel has declared it.)

The fixtures are given a line at a time with the meaning of each line, because
a trace is unreadable otherwise: `e1 V!` is a term line whose three arguments
are encoded relative to three different counters. -/

import HolTrace

open HolCore.Kernel HolTrace

namespace HolTest.HolTraceTest

/- ---------------------------------------------------------------------- -/
/- Reporting.                                                             -/
/- ---------------------------------------------------------------------- -/

/-- Does `s` contain `sub`? -/
private def hasSubstr (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- Report one check in the suite's `-> OK` / `-> MISMATCH` form. -/
private def report (lbl : String) (ok : Bool) (detail : String) : IO Unit :=
  if ok then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH {detail}"

/- ---------------------------------------------------------------------- -/
/- The argument encoding.                                                 -/
/- ---------------------------------------------------------------------- -/

/-- Decode a single argument relative to `n`, as a line would carry it.
    `none` if nothing was consumed, i.e. there was no argument there. -/
private def decode (s : String) (n : Int) : Option Int :=
  let b := s.toUTF8
  let (v, c) := Cursor.scanArg { buf := b, pos := 0, stop := b.size } n
  if c.pos == 0 then none else some v

/-- Decode two arguments in a row, which is where the space rule shows up. -/
private def decode2 (s : String) (n : Int) : Option (Int × Int) :=
  let b := s.toUTF8
  let (v, c) := Cursor.scanArg { buf := b, pos := 0, stop := b.size } n
  let (w, c') := Cursor.scanArg c n
  if c.pos == 0 || c'.pos == c.pos then none else some (v, w)

/-- The specification's worked table of encodings relative to n = 10000
    (https://holtrace.cr.yp.to/format.html).  It covers all three forms - the
    `!@#$%^&*()` shorthands, absolute base 32, and `-`-relative - including the
    boundary where a writer switches between the last two. -/
private def encodingTable : List (String × Int) :=
  [ ("0", 0), ("9", 9), ("A", 10), ("V", 31), ("10", 32), ("VV", 1023),
    ("100", 1024), ("8OG", 8976), ("-VV", 8977), ("-10", 9968), ("-V", 9969),
    ("-B", 9989), (")", 9990), ("!", 9999), ("9OG", 10000), ("9OH", 10001) ]

#eval show IO Unit from do
  let bad := encodingTable.filter (fun (s, v) => decode s 10000 != some v)
  report "encoding: the specification's table at n = 10000" bad.isEmpty
    s!"wrong for {bad.map Prod.fst}"

#eval show IO Unit from do
  -- The spec's example of the inserted space: `e` with two arguments written
  -- `17` and `14` becomes `e17 14`, because without the space the reader would
  -- take `1714` for one base-32 numeral.
  report "encoding: a space separates two base-32 arguments"
    (decode2 "17 14" 10000 == some (39, 36) &&
     decode "1714" 10000 == some 39972 && decode2 "1714" 10000 == none)
    s!"{decode2 "17 14" 10000} / {decode "1714" 10000}"

#eval show IO Unit from do
  -- Lowercase is not a synonym for uppercase: `a` is not 10, so nothing is
  -- consumed and the argument is missing.
  report "encoding: lowercase base 32 is not accepted" (decode "a" 10000 == none)
    s!"{decode "a" 10000}"

/- ---------------------------------------------------------------------- -/
/- Replaying a trace.                                                     -/
/- ---------------------------------------------------------------------- -/

/-- Replay a trace given a line at a time. -/
private def replayLines (lines : List String) (cfg : Config := {}) :
    IO (Except String State) :=
  (replay cfg (String.intercalate "\n" lines ++ "\n").toUTF8).run

/-- A trace that must verify, reporting the objects it must define. -/
private def mustVerify (lbl : String) (lines : List String)
    (types terms infs thms typedefs : Nat) : IO Unit := do
  match ← replayLines lines with
  | .error e => report lbl false s!"rejected: {e}"
  | .ok st =>
      report lbl
        (st.types.size == types && st.terms.size == terms && st.infs == infs &&
         st.thms.size == thms && st.typedefs.size == typedefs)
        s!"{st.summary}"

/-- A trace that must be rejected, and the reason it must be rejected for.

    The reason is checked, not just the rejection: nearly any mistake in a
    reader shows up as "some trace was rejected", so a test that only asked
    whether the trace failed would pass even if every fixture failed on line 2. -/
private def mustReject (lbl : String) (lines : List String) (why : String) : IO Unit := do
  match ← replayLines lines with
  | .ok _     => report lbl false "wrongly accepted"
  | .error e  => report lbl (hasSubstr e why) s!"wrong reason: {e}"

/-- A named theorem the trace must end up proving. -/
private def mustProve (lbl : String) (st : State) (name want : String) : IO Unit := do
  match st.find? name with
  | none    => report lbl false s!"the trace named no theorem '{name}'"
  | some th =>
      let got ← HolCore.Printer.string_of_thm th
      report lbl (got == want) s!"got {got}"

/- ---------------------------------------------------------------------- -/
/- The specification's worked example.                                    -/
/- ---------------------------------------------------------------------- -/

/-- The first lines with lowercase tags in a trace of hol.ml, copied from the
    annotated table at https://holtrace.cr.yp.to/format.html, with the `C!T`
    definition line and the `/!T_DEF` name that go with them.  It builds
    HOL Light's very first definition, `T = ((\p. p) = (\p. p))`.

    Taking this verbatim from the published specification is the point: it is
    the one fixture whose bytes were not produced by anything in this repository. -/
def tDefTrace : List String :=
  [ "HOLTrace 1",  -- the version 1 header
    "b0bool",      -- type 0: bool
    "b2!!fun",     -- type 1: bool->bool
    "b2@!fun",     -- type 2: bool->bool->bool
    "c!=",         -- term 0: constant = of type bool->bool->bool
    "d#T",         -- term 1: variable T of type bool
    "e@@!",        -- term 2: =(T) of type bool->bool
    "b2@#fun",     -- type 3: (bool->bool)->bool
    "b2#!fun",     -- type 4: (bool->bool)->(bool->bool)->bool
    "c!=",         -- term 3: constant = of type (bool->bool)->(bool->bool)->bool
    "d%p",         -- term 4: variable p of type bool
    "f$!!",        -- term 5: function p -> p of type bool->bool
    "e@#!",        -- term 6: =(p->p) of type (bool->bool)->bool
    "e%!@",        -- term 7: =(p->p)(p->p) of type bool
    "e%^!",        -- term 8: =(T)(=(p->p)(p->p)) of type bool, with T a VARIABLE
    "C!T",         -- inference 0: new_basic_definition of that, naming T
    "c%T",         -- term 9: constant T of type bool
    "e$)!",        -- term 10: =(T) of type bool->bool, now the constant
    "e%!$",        -- term 11: =(T)(=(p->p)(p->p)) of type bool
    "t!",          -- theorem 0: |- T = ((\p. p) = (\p. p))
    "/!T_DEF" ]    -- theorem 0 is named T_DEF

#eval show IO Unit from do
  match ← replayLines tDefTrace with
  | .error e => report "hol.ml's T_DEF, from the specification's own table" false
                  s!"rejected: {e}"
  | .ok st =>
      report "hol.ml's T_DEF, from the specification's own table"
        (st.types.size == 5 && st.terms.size == 12 && st.thms.size == 1 &&
         st.infs == 1 && st.typedefs.size == 0) st.summary
      -- The printer is working from HOL Light's INITIAL fixities - replay loads
      -- no library - so `=` prints in prefix form rather than infix.
      mustProve "T_DEF is the theorem the trace claims" st "T_DEF"
        "|- = T (= (\\p. p) (\\p. p))"

/- ---------------------------------------------------------------------- -/
/- Every inference tag.                                                   -/
/- ---------------------------------------------------------------------- -/

/-- A trace using all twenty inference tags - the ten primitive rules, plus
    `X` (new_axiom), `C` (new_basic_definition), `A` and `D`
    (new_basic_type_definition), and the `,` and `;` ProofTrace bookkeeping.

    It proves nothing interesting; the point is that each tag is reached.  The
    chain is: REFL x, ASSUME p, BETA, ABS, MK_COMB, TRANS, DEDUCT_ANTISYM_RULE
    (which discharges both hypotheses of `p |- p` against each other),
    EQ_MP, INST, INST_TYPE, an axiom, the definition `ht_k = (\x. x)`, and then
    a type definition witnessed by `|- ht_k = ht_k` - which is `P ht_k` for the
    closed predicate `P = ((=) ht_k)`, as `A` requires.

    Names are prefixed `ht_` so that nothing here can collide with another
    trace replayed in the same process. -/
def allRulesTrace : List String :=
  [ "HOLTrace 1",                   -- the version 1 header
    "aQ",                           -- type 0: type variable Q
    "d!x",                          -- term 0: variable x : Q
    "R!",                           -- inference 0: REFL x
    "b0bool",                       -- type 1: bool
    "b2@!fun",                      -- type 2: (Q->bool)
    "b2#!fun",                      -- type 3: (Q->(Q->bool))
    "c!=",                          -- term 1: constant = : (Q->(Q->bool))
    "e@!@",                         -- term 2: =(x)
    "e#!#",                         -- term 3: =(x)(x)
    "t!",                           -- theorem 0: |- x = x, by REFL
    "d#p",                          -- term 4: variable p : bool
    "U!",                           -- inference 1: ASSUME p
    "t!!",                          -- theorem 1: p |- p, by ASSUME
    "b2$$fun",                      -- type 4: (Q->Q)
    "f!%%",                         -- term 5: \x. x
    "e%!^",                         -- term 6: (\x. x)(x)
    "B!",                           -- inference 2: BETA (\x. x) x
    "e#^!",                         -- term 7: =((\x. x)(x))
    "e$!*",                         -- term 8: =((\x. x)(x))(x)
    "t!",                           -- theorem 2: |- (\x. x) x = x, by BETA
    "F(#",                          -- inference 3: ABS x, over theorem 0
    "b2!$fun",                      -- type 5: ((Q->Q)->bool)
    "b2@!fun",                      -- type 6: ((Q->Q)->((Q->Q)->bool))
    "c!=",                          -- term 9: constant = : ((Q->Q)->((Q->Q)->bool))
    "e@!%",                         -- term 10: =(\x. x)
    "e^!^",                         -- term 11: =(\x. x)(\x. x)
    "t!",                           -- theorem 3: |- (\x. x) = (\x. x), by ABS
    "d#f",                          -- term 12: variable f : (Q->Q)
    "R!",                           -- inference 4: REFL f
    "e@$!",                         -- term 13: =(f)
    "e^!@",                         -- term 14: =(f)(f)
    "t!",                           -- theorem 4: |- f = f, by REFL
    "E!%",                          -- inference 5: MK_COMB of theorems 4 and 0
    "e&#0",                         -- term 15: f(x)
    "e%1!",                         -- term 16: =(f(x))
    "e^!@",                         -- term 17: =(f(x))(f(x))
    "t!",                           -- theorem 5: |- f x = f x, by MK_COMB
    "V^^",                          -- inference 6: TRANS of theorems 0 and 0
    "t3",                           -- theorem 6: |- x = x, by TRANS
    "Z^^",                          -- inference 7: DEDUCT_ANTISYM_RULE of theorem 1 with itself
    "b2^^fun",                      -- type 7: (bool->bool)
    "b2&!fun",                      -- type 8: (bool->(bool->bool))
    "c!=",                          -- term 18: constant = : (bool->(bool->bool))
    "e@!4",                         -- term 19: =(p)
    "e*!4",                         -- term 20: =(p)(p)
    "t!",                           -- theorem 7: |- p = p, by DEDUCT_ANTISYM_RULE
    "P!&",                          -- inference 8: EQ_MP of theorems 7 and 1
    "t4 4",                         -- theorem 8: p |- p, by EQ_MP
    "d(y",                          -- term 21: variable y : Q
    "S(0!",                         -- inference 9: INST x := y in theorem 0
    "e&1!",                         -- term 22: =(y)
    "e*!@",                         -- term 23: =(y)(y)
    "t!",                           -- theorem 9: |- y = y, by INST
    "T)(*",                         -- inference 10: INST_TYPE Q := bool in theorem 0
    "d*x",                          -- term 24: variable x : bool
    "e@&!",                         -- term 25: =(x)
    "e*!@",                         -- term 26: =(x)(x)
    "t!",                           -- theorem 10: |- x = x at type bool, by INST_TYPE
    "X3",                           -- inference 11: new_axiom x = x
    "t3",                           -- theorem 11: |- x = x, as an axiom
    "d%ht_k",                       -- term 27: variable ht_k : (Q->Q)
    "e$9!",                         -- term 28: =(ht_k)
    "e*!5",                         -- term 29: =(ht_k)(\x. x)
    "C!ht_k",                       -- inference 12: new_basic_definition ht_k = (\x. x)
    "c%ht_k",                       -- term 30: constant ht_k : (Q->Q)
    "e$9!",                         -- term 31: =(ht_k), now the constant
    "e*!5",                         -- term 32: =(ht_k)(\x. x)
    "t!",                           -- theorem 12: |- ht_k = (\x. x), the definition
    "R#",                           -- inference 13: REFL ht_k
    "e*@#",                         -- term 33: =(ht_k)(ht_k)
    "t!",                           -- theorem 13: |- ht_k = ht_k, the witness for the type
    "A%#!]ht_ty]ht_abs]ht_rep]Q]",  -- inference 14: new_basic_type_definition ht_ty, ht_abs, ht_rep
    "b1(ht_ty",                     -- type 9: ht_ty(Q)
    "b2!(fun",                      -- type 10: (ht_ty(Q)->bool)
    "b2@!fun",                      -- type 11: (ht_ty(Q)->(ht_ty(Q)->bool))
    "c!=",                          -- term 34: constant = : (ht_ty(Q)->(ht_ty(Q)->bool))
    "b2*#fun",                      -- type 12: ((Q->Q)->ht_ty(Q))
    "c!ht_abs",                     -- term 35: constant ht_abs : ((Q->Q)->ht_ty(Q))
    "b2$(fun",                      -- type 13: (ht_ty(Q)->(Q->Q))
    "c!ht_rep",                     -- term 36: constant ht_rep : (ht_ty(Q)->(Q->Q))
    "d%a",                          -- term 37: variable a : ht_ty(Q)
    "e)@!",                         -- term 38: ht_rep(a)
    "e%$!",                         -- term 39: ht_abs(ht_rep(a))
    "e$^!",                         -- term 40: =(ht_abs(ht_rep(a)))
    "e1!$",                         -- term 41: =(ht_abs(ht_rep(a)))(a)
    "t!",                           -- theorem 14: |- ht_abs (ht_rep a) = a, from the type definition
    "D!",                           -- inference 15: the second theorem of typedef 0
    "d)r",                          -- term 42: variable r : (Q->Q)
    "e1 V!",                        -- term 43: =(ht_k)(r)
    "e&I!",                         -- term 44: =(=(ht_k)(r))
    "e%)#",                         -- term 45: ht_abs(r)
    "e))!",                         -- term 46: ht_rep(ht_abs(r))
    "e(9!",                         -- term 47: =(ht_rep(ht_abs(r)))
    "e1!^",                         -- term 48: =(ht_rep(ht_abs(r)))(r)
    "e1%!",                         -- term 49: =(=(ht_k)(r))(=(ht_rep(ht_abs(r)))(r))
    "t!",                           -- theorem 15: |- (ht_k = r) = (ht_rep (ht_abs r) = r)
    "/$ht_k_DEF",                   -- theorem 12 is named ht_k_DEF
    "/!ht_ty_BIJ",                  -- theorem 15 is named ht_ty_BIJ
    ";",                            -- ProofTrace ID 0 is skipped
    ",!!!" ]                        -- ProofTrace ID 1: theorem 15 by inference 15

#eval show IO Unit from do
  match ← replayLines allRulesTrace with
  | .error e => report "a trace using every inference tag" false s!"rejected: {e}"
  | .ok st =>
      report "a trace using every inference tag"
        (st.types.size == 14 && st.terms.size == 50 && st.infs == 16 &&
         st.thms.size == 16 && st.typedefs.size == 1 && st.ptid == 2) st.summary
      mustProve "the C line's definition" st "ht_k_DEF" "|- = ht_k (\\x. x)"
      mustProve "the D line's bijection" st "ht_ty_BIJ"
        "|- = (= ht_k r) (= (ht_rep (ht_abs r)) r)"

/- ---------------------------------------------------------------------- -/
/- Traces that must be rejected.                                          -/
/- ---------------------------------------------------------------------- -/

/- A trace is a recipe, not an assertion, so the interesting tests are the ones
   that must FAIL.  The fixtures below are grouped by what rejects them: the
   line format, the reader's own consistency checks, and the kernel.  None of
   them is allowed to be accepted, and each must be rejected for its own
   reason - see `mustReject`. -/

/-- Enough of a prelude to have `=`, a boolean variable `p`, and the term
    `p = p`: types 0-2, terms 0-3. -/
private def eqPrelude : List String :=
  [ "HOLTrace 1", "b0bool", "b2!!fun", "b2@!fun", "c!=", "d#p", "e@@!", "e#!@" ]

#eval show IO Unit from do
  -- The line format.  An empty file has no lines at all, which `replayLines`
  -- cannot express (it terminates the last line), so `replay` is called direct.
  match ← (replay {} ByteArray.empty).run with
  | .ok _    => report "an empty file" false "wrongly accepted"
  | .error e => report "an empty file" (hasSubstr e "empty file") s!"wrong reason: {e}"
  mustReject "a version other than 1" ["HOLTrace 2", "b0bool"]
    "does not start with 'HOLTrace 1'"
  mustReject "a blank line" ["HOLTrace 1", ""] "blank line is prohibited"
  mustReject "a byte outside 32-126" ["HOLTrace 1", "a\tx"] "byte 9 is prohibited"
  mustReject "an unknown tag" ["HOLTrace 1", "u0"] "unrecognized tag 'u'"
  mustReject "a missing numeric argument" ["HOLTrace 1", "b0bool", "c"]
    "missing numeric argument"
  mustReject "a missing text argument" ["HOLTrace 1", "a"] "missing text argument"
  mustReject "an argument too many" ["HOLTrace 1", "b0bool", "d!x", "R!0"]
    "extra argument"
  -- Forward references are prohibited: a file must be in topological order, so
  -- type 1 cannot be named while only type 0 exists.
  mustReject "a forward reference" ["HOLTrace 1", "b0bool", "b2 1 1fun"]
    "out of range"

#eval show IO Unit from do
  -- The reader's own checks, none of which the kernel makes.
  mustReject "an e line declaring the wrong type" (eqPrelude.dropLast ++ ["e#@!"])
    "e: the declared type is not the type of the application"
  mustReject "an f line declaring the wrong type"
    ["HOLTrace 1", "b0bool", "b2!!fun", "d@p", "f@!!"]
    "f: the declared type is not the type of the abstraction"
  mustReject "a theorem with no inference before it"
    ["HOLTrace 1", "b0bool", "d!x", "t!"] "no inference precedes this theorem"
  -- `R#` proves `|- p = p`; the `t` line claims it also has `p = p` as a
  -- hypothesis, which is a different sequent.
  mustReject "a theorem the inference does not prove" (eqPrelude ++ ["R#", "t!!"])
    "but the line states"
  mustReject "one name for two theorems" (eqPrelude ++ ["R#", "t!", "/!N", "/!N"])
    "already used"
  mustReject "a name that is not an identifier"
    (eqPrelude ++ ["R#", "t!", "/!bad name"]) "refusing unusual characters"

#eval show IO Unit from do
  -- Rejections by the kernel, which must reach the caller rather than being
  -- swallowed: these are the cases where a trace is well formed but unsound.
  mustReject "a constant that was never declared"
    ["HOLTrace 1", "b0bool", "c!nosuchconstant"] "mk_const"
  mustReject "a type constructor at the wrong arity"
    ["HOLTrace 1", "b0bool", "b1!bool"] "wrong number of arguments"
  mustReject "ASSUME of a term that is not boolean"
    ["HOLTrace 1", "aQ", "b2!!fun", "d!f", "U!"] "not a proposition"
  mustReject "BETA of a term that is not a redex"
    ["HOLTrace 1", "b0bool", "d!p", "B!"] "not a trivial beta-redex"
  mustReject "MK_COMB of theorems that are not equations"
    ["HOLTrace 1", "b0bool", "d!p", "U!", "t!!", "E!!"] "not both equations"
  -- ABS may not abstract over a variable that is free in a hypothesis: from
  -- `p = p |- p = p` it would conclude `p = p |- (\p. p) = (\p. p)`.
  mustReject "ABS over a variable free in a hypothesis"
    (eqPrelude ++ ["U!", "t!!", "F#!"]) "ABS"

/-- A type definition witnessed by `REFL (\w. w)`, i.e. `|- (\w. w) = (\w. w)`,
    which is `P` applied to `(\w. w)` for the closed predicate
    `P = ((=) (\w. w))`.  `word` is the `]abstype]abs]rep]tyvars]` field and
    `repterm` selects which term the `A` line names as the predicate, so the
    fixture can be bent in one place at a time. -/
private def typedefTrace (word : String) (repterm : String := "@") : List String :=
  [ "HOLTrace 1",   -- the version 1 header
    "aQ",           -- type 0: type variable Q
    "b2!!fun",      -- type 1: (Q->Q)
    "d@w",          -- term 0: variable w : Q
    "f!!!",         -- term 1: \w. w
    "R!",           -- inference 0: REFL (\w. w)
    "b0bool",       -- type 2: bool
    "b2@!fun",      -- type 3: ((Q->Q)->bool)
    "b2#!fun",      -- type 4: ((Q->Q)->((Q->Q)->bool))
    "c!=",          -- term 2: constant = : ((Q->Q)->((Q->Q)->bool))
    "e@!@",         -- term 3: =(\w. w), the predicate P
    "e#!#",         -- term 4: =(\w. w)(\w. w)
    "t!",           -- theorem 0: |- (\w. w) = (\w. w), the witness
    -- reptype is (Q->Q), repterm is term 3 by default and term 1 - the
    -- identity itself, which is NOT the predicate - when `repterm` says `$`
    "A$" ++ repterm ++ "!" ++ word ]

#eval show IO Unit from do
  -- A positive control, so that the three rejections below differ from an
  -- accepted trace in exactly the thing each is testing.
  mustVerify "a type definition witnessed by REFL" (typedefTrace "]hx_ty]hx_abs]hx_rep]Q]")
    5 5 2 1 1
  -- `reptype`, `repterm` and the type variables are all redundant - the
  -- witnessing theorem determines them - so all three must be checked, or a
  -- reader would be taking on trust what it could verify.
  mustReject "a type definition naming the wrong predicate"
    (typedefTrace "]hu_ty]hu_abs]hu_rep]Q]" (repterm := "$"))
    "repterm is not the predicate"
  mustReject "a type definition declaring type variables the kernel did not use"
    (typedefTrace "]hv_ty]hv_abs]hv_rep]Q]R]") "type variables are not the ones"
  mustReject "a type definition whose name field is malformed"
    (typedefTrace "hw_ty]hw_abs]hw_rep]Q]") "the name field must"
  -- All constant names must be distinct, counting every A line's absname and
  -- repname.  The kernel checks each of the two against the constants that
  -- already exist but not against each other, so this one is HolTrace's.
  mustReject "a type definition using one name for both abs and rep"
    (typedefTrace "]hy_ty]SAME]SAME]Q]") "absname and repname are both 'SAME'"

#eval show IO Unit from do
  -- INST_TYPE may only replace type variables.  `T!@!` substitutes for `bool`,
  -- which the kernel would silently ignore rather than get wrong - so this is
  -- HolTrace's check too.  The fixture is upstream's own.
  mustReject "INST_TYPE replacing something that is not a type variable"
    ["HOLTrace 1", "b0bool", "d0p", "U!", "t!!", "aA", "T!@!"]
    "not a type variable"

/- ---------------------------------------------------------------------- -/
/- Configuration.                                                         -/
/- ---------------------------------------------------------------------- -/

#eval show IO Unit from do
  -- `checkThms := false` is upstream's `holtrace_restore_skipthmchecks`: every
  -- inference still runs through the kernel, but the results are not compared
  -- with the statements the file records.  So the fixture that states a
  -- hypothesis its inference does not prove is accepted, while a fixture whose
  -- INFERENCE is bad is rejected either way.
  match ← replayLines (eqPrelude ++ ["R#", "t!!"]) { checkThms := false } with
  | .ok _    => report "--no-thm-check skips the statement check" true ""
  | .error e => report "--no-thm-check skips the statement check" false e
  mustReject "--no-thm-check still runs the inferences"
    ["HOLTrace 1", "b0bool", "d!p", "B!"] "not a trivial beta-redex"
  match ← replayLines (eqPrelude ++ ["R#", "t!", "/!bad name"])
                      { strictNames := false } with
  | .ok _    => report "--lax-names allows an unusual theorem name" true ""
  | .error e => report "--lax-names allows an unusual theorem name" false e

/- ---------------------------------------------------------------------- -/
/- The command line.                                                      -/
/- ---------------------------------------------------------------------- -/

#eval show IO Unit from do
  report "the command line reads --print's argument"
    (match Cli.parseArgs ["--print", "FOO", "t.50"] with
     | .ok opts => opts.print == #["FOO"] && opts.files == #["t.50"]
     | .error _ => false) "parse failed"
  report "the command line rejects --print with nothing after it"
    (match Cli.parseArgs ["--print"] with | .error _ => true | .ok _ => false) ""
  report "the command line rejects an unknown option"
    (match Cli.parseArgs ["--nonesuch"] with | .error _ => true | .ok _ => false) ""
  -- `--names` prints the theorems too, `--names-only` just the names, so the
  -- two are separate flags rather than one with a modifier.
  report "the command line separates --names from --names-only"
    (match Cli.parseArgs ["--names", "t.50"], Cli.parseArgs ["--names-only", "t.50"] with
     | .ok a, .ok b =>
         a.listNames && !a.listNamesOnly && b.listNamesOnly && !b.listNames
     | _, _ => false) ""
  report "the command line treats - as a file (standard input)"
    (match Cli.parseArgs ["-"] with
     | .ok opts => opts.files == #["-"]
     | .error _ => false) ""

end HolTest.HolTraceTest
