/- File: HolTest/PrinterTest.lean
Runtime test suite: printer.ml - the HOL Light prettyprinter.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set.

FAITHFULNESS BASIS.  Almost every other test in this project asserts on a
PRINTED string, so a printer defect gets ENCODED INTO EXPECTATIONS rather than
caught.  These tests target the printer directly.  Expectations are taken from
HOL Light's reference docs where a worked example exists
(hol-light/Help/string_of_term.hlp, parse_term.hlp) and otherwise DERIVED from
printer.ml's precedence/associativity rules and the infix precedences set in
bool.ml (`==>`=4, `\/`=6, `/\`=8, `<=>`=2, `=`=12).

The SURFACE-NAME merge defect (`a,(b,c)` -> `a,b,c`) is already pinned in
HolTest/RegressionTest.lean; this file builds COMPLEMENTARY coverage:
precedence parenthesisation, binder collapsing, `string_escaped`, and a
parse -> print ROUND TRIP (the single most valuable printer test, since it is
self-checking without hardcoding an expected string).

VERIFIED SIGNATURES (read from source):
  HolCore.Parser.parse_term   : String -> IO (Except String term)   (Parser.lean)
  HolCore.Printer.string_of_term : term -> IO String                (Printer.lean)
  HolCore.Printer.string_escaped : String -> String                 (Printer.lean)
  HolCore.Kernel.aconv        : term -> term -> Bool                 (Fusion.lean 676)
  HolCore.Kernel.concl        : thm -> term                          (Fusion.lean)
  Session.ADD_SYM             : thm                                  (Session.lean 2141)
Parser layer is forced with `(IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))`
before any parse (gotcha #2), exactly as RegressionTest does. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

namespace HolTest.PrinterTest

/- ---------------------------------------------------------------------- -/
/- Reporting helpers.                                                     -/
/-                                                                        -/
/- `okPrintVerbatim` gates on `MISMATCH` (reserved for expectations taken -/
/- VERBATIM from a Help EXAMPLE).  `okPrintDerived` prints `DIFFERS`       -/
/- (soft, no gate) for expectations DERIVED from the precedence rules.    -/
/- Both compare with spaces stripped where noted, since the `Fmt` shim's  -/
/- breaking behaviour is orthogonal to the bracket/name questions tested. -/
/- ---------------------------------------------------------------------- -/

/-- Parse `src`, print it, compare the space-stripped result to `exp`;
    gate on `MISMATCH` (VERBATIM Help expectation). -/
private unsafe def okPrintVerbatim (lbl src exp : String) : IO Unit := do
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))   -- force parser layer
  match ← HolCore.Parser.parse_term src with
  | .error e => IO.println s!"{lbl} -> MISMATCH parse error: {e}"
  | .ok tm =>
    let s := (← HolCore.Printer.string_of_term tm).replace " " ""
    let e := exp.replace " " ""
    if s == e then IO.println s!"{lbl} -> OK"
    else IO.println s!"{lbl} -> MISMATCH got \"{s}\" expected \"{e}\""

/-- Parse `src`, print it, compare the space-stripped result to `exp`;
    print `DIFFERS` (soft) for a DERIVED expectation. -/
private unsafe def okPrintDerived (lbl src exp : String) : IO Unit := do
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))   -- force parser layer
  match ← HolCore.Parser.parse_term src with
  | .error e => IO.println s!"{lbl} -> DIFFERS parse error: {e}"
  | .ok tm =>
    let s := (← HolCore.Printer.string_of_term tm).replace " " ""
    let e := exp.replace " " ""
    if s == e then IO.println s!"{lbl} -> OK"
    else IO.println s!"{lbl} -> DIFFERS got \"{s}\" expected \"{e}\""

/- ---------------------------------------------------------------------- -/
/- string_escaped (printer.ml).  OCaml's String.escaped: a quote, a       -/
/- backslash and a newline must all be escaped.  A char literal printed    -/
/- without this would fail to re-parse (this is the defect the existing    -/
/- RegressionTest note describes).  DERIVED from the OCaml semantics of     -/
/- String.escaped, so `DIFFERS` on divergence.                             -/
/- ---------------------------------------------------------------------- -/

-- A literal double-quote must become \" (two chars: backslash, quote).
#eval (do
  let got := HolCore.Printer.string_escaped "\""
  if got == "\\\"" then IO.println "string_escaped quote -> OK"
  else IO.println s!"string_escaped quote -> DIFFERS got \"{got}\"")

-- A literal backslash must become \\ (two backslashes).
#eval (do
  let got := HolCore.Printer.string_escaped "\\"
  if got == "\\\\" then IO.println "string_escaped backslash -> OK"
  else IO.println s!"string_escaped backslash -> DIFFERS got \"{got}\"")

-- A newline must become the two chars backslash-n.
#eval (do
  let got := HolCore.Printer.string_escaped "\n"
  if got == "\\n" then IO.println "string_escaped newline -> OK"
  else IO.println s!"string_escaped newline -> DIFFERS got \"{got}\"")

-- All three together in one string, plus an ordinary char, in order.
#eval (do
  let got := HolCore.Printer.string_escaped "a\"b\\c\nd"
  if got == "a\\\"b\\\\c\\nd" then IO.println "string_escaped combined -> OK"
  else IO.println s!"string_escaped combined -> DIFFERS got \"{got}\"")

/- ---------------------------------------------------------------------- -/
/- ROUND TRIP: parse (string_of_term t) must give back an alpha-equivalent -/
/- term.  Self-checking with NO hardcoded string, so it survives any       -/
/- reasonable change to spacing/breaking while still catching a printer     -/
/- that drops brackets or mis-associates (which would re-parse differently).-/
/- ---------------------------------------------------------------------- -/

/-- Parse `src`, print the result, RE-parse the printed string, and assert
    the two terms are alpha-equivalent (`aconv`). -/
private unsafe def roundTrip (lbl src : String) : IO Unit := do
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))   -- force parser layer
  match ← HolCore.Parser.parse_term src with
  | .error e => IO.println s!"{lbl} -> DIFFERS first parse error: {e}"
  | .ok tm =>
    let printed ← HolCore.Printer.string_of_term tm
    match ← HolCore.Parser.parse_term printed with
    | .error e => IO.println s!"{lbl} -> DIFFERS reparse error: {e} (printed \"{printed}\")"
    | .ok tm2 =>
      if aconv tm tm2 then IO.println s!"{lbl} -> OK"
      else IO.println s!"{lbl} -> DIFFERS reparse not alpha-equal (printed \"{printed}\")"

#eval roundTrip "round trip: mixed infixes" "p /\\ q ==> r"
#eval roundTrip "round trip: nested conditional" "if p then (if q then p else q) else r"
#eval roundTrip "round trip: lambda body infix" "\\x. x /\\ p"
#eval roundTrip "round trip: collapsed binders" "!x y z. x /\\ y /\\ z"
-- A mixed-surface chain is deliberately NOT round-tripped here.  Printing is
-- LOSSY unless `print_types_of_subterms` is on: the `:num` annotations that
-- fixed b and c do not appear in `a <=> b = c`, so the reparse invents fresh
-- type variables and the result is not alpha-equal.  That is a property of
-- HOL printing, NOT a printer defect - the PRINTED FORM is pinned in
-- HolTest/RegressionTest.lean instead.
#eval roundTrip "round trip: negation and disjunction" "~p \\/ q"
#eval roundTrip "round trip: existential over conjunction" "?x. p /\\ x"

/- ---------------------------------------------------------------------- -/
/- VERBATIM Help expectations (gate on MISMATCH).                          -/
/- ---------------------------------------------------------------------- -/

-- Help/parse_term.hlp EXAMPLE: `parse_term "p /\\ q ==> r"` prints
-- `p /\ q ==> r`.  Also a precedence pin: `/\` (8) binds tighter than
-- `==>` (4), so the `/\` needs NO brackets under `==>`.
#eval okPrintVerbatim "Help/parse_term.hlp p /\\ q ==> r"
  "p /\\ q ==> r" "p /\\ q ==> r"

/- ---------------------------------------------------------------------- -/
/- DERIVED precedence parenthesisation (print `DIFFERS`).                  -/
/-                                                                        -/
/- bool.ml infix precedences: `<=>`=2, `==>`=4, `\/`=6, `/\`=8, `=`=12.     -/
/- printer.ml brackets a sub-infix only when its precedence `<=` the        -/
/- surrounding precedence (`print_infix_app`: newprec <= prec).            -/
/- ---------------------------------------------------------------------- -/

-- Lower-precedence operator NESTED under higher: the `==>` (4) inside `/\`
-- (8) MUST be bracketed.  Complements the verbatim test (which has no
-- brackets because the nesting is the other way round).
#eval okPrintDerived "precedence: (p ==> q) /\\ r brackets ==>"
  "(p ==> q) /\\ r" "(p ==> q) /\\ r"

-- Same-precedence, right-associative `==>` chain: right nesting needs NO
-- brackets, left nesting DOES.  Discriminating pair on associativity.
#eval okPrintDerived "assoc: p ==> q ==> r (right, no brackets)"
  "p ==> q ==> r" "p ==> q ==> r"
#eval okPrintDerived "assoc: (p ==> q) ==> r (left, brackets)"
  "(p ==> q) ==> r" "(p ==> q) ==> r"

-- A negation applied to a disjunction: `~` (prefix) binds tighter than `\/`,
-- so `~p \/ q` must NOT bracket, but `~(p \/ q)` MUST.  Discriminating pair.
#eval okPrintDerived "prefix: ~p \\/ q (no brackets)" "~p \\/ q" "~p \\/ q"
#eval okPrintDerived "prefix: ~(p \\/ q) (brackets)" "~(p \\/ q)" "~(p \\/ q)"

/- ---------------------------------------------------------------------- -/
/- BINDER COLLAPSING (printer.ml `collectvs`).  Consecutive same-binder     -/
/- quantifiers over abstractions print as `!x y z.`, NOT `!x. !y. !z.`.     -/
/- DERIVED, so `DIFFERS`.  The round-trip test above proves semantic         -/
/- equivalence; this pins the SURFACE collapse.                             -/
/- ---------------------------------------------------------------------- -/

#eval okPrintDerived "binder collapse: !x y z. ..." "!x y z. x /\\ y /\\ z"
  "forall x y z. x /\\ y /\\ z"

-- A change of binder must BREAK the collapse: `!x. ?y. ...` keeps both
-- binders and dots.  Complements the collapse test.
#eval okPrintDerived "binder no-collapse across ! and ?" "!x. ?y. x /\\ y"
  "forall x. exists y. x /\\ y"

end HolTest.PrinterTest

/- ---------------------------------------------------------------------- -/
/- set_verbose_symbols (bool.ml 491-504), which bool.ml runs AT LOAD.      -/
/- Cases taken verbatim from HOL Light's own UnitTests:                    -/
/-   basic_tests.ml 13-17   - both syntaxes parse to the SAME term;        -/
/-   printer_tests.ml       - the verbose form is what PRINTS by default.  -/
/- ---------------------------------------------------------------------- -/

#eval (do
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))
  -- basic_tests.ml 13-17
  for (a, b) in [("T", "true"), ("F", "false"), ("!(x:A). P x", "forall (x:A). P x"),
                 ("?(x:A). P x", "exists (x:A). P x"), ("?!(x:A). P x", "existsunique (x:A). P x")] do
    match ← HolCore.Parser.parse_term a, ← HolCore.Parser.parse_term b with
    | .ok ta, .ok tb =>
      if ta == tb then IO.println s!"verbose syntax `{a}` = `{b}` (basic_tests.ml) -> OK"
      else IO.println s!"verbose syntax `{a}` vs `{b}` -> MISMATCH different terms"
    | _, _ => IO.println s!"verbose syntax `{a}` / `{b}` -> MISMATCH parse failed"
  -- printer_tests.ml, verbatim
  for (inp, want) in [("~T", "~true"), ("~ (~T)", "~ ~true"), ("T /\\ F", "true /\\ false"),
                      ("(T <=> F)", "true <=> false"), ("?x. x = (3:num)", "exists x. x = 3"),
                      ("!x. x + 0 = x", "forall x. x + 0 = x"),
                      ("?!x. x = (5:num)", "existsunique x. x = 5"),
                      ("!x y z. x + y + z = (z:num) + y + x", "forall x y z. x + y + z = z + y + x")] do
    match ← HolCore.Parser.parse_term inp with
    | .error e => IO.println s!"printer_tests `{inp}` -> MISMATCH parse ERR {e}"
    | .ok t =>
      let got ← HolCore.Printer.string_of_term t
      if got == want then IO.println s!"printer_tests `{inp}` prints `{want}` -> OK"
      else IO.println s!"printer_tests `{inp}` -> MISMATCH got `{got}` want `{want}`")

-- unset_verbose_symbols restores the terse output; set_verbose_symbols brings the
-- default back.  (Restores the default before exiting, so later modules are
-- unaffected.)
#eval (do
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "!x. x + 0 = x /\\ T" with
  | .error e => IO.println s!"unset_verbose_symbols -> MISMATCH parse ERR {e}"
  | .ok t =>
    HolCore.Bool.unset_verbose_symbols
    let terse ← HolCore.Printer.string_of_term t
    let _ ← HolCore.Bool.set_verbose_symbols
    let verb ← HolCore.Printer.string_of_term t
    if terse == "!x. x + 0 = x /\\ T" && verb == "forall x. x + 0 = x /\\ true" then
      IO.println "unset/set_verbose_symbols toggle the printed form -> OK"
    else IO.println s!"verbose toggle -> MISMATCH terse `{terse}` verbose `{verb}`")
