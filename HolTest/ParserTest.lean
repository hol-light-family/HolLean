/- File: HolTest/ParserTest.lean
Runtime test suite: parser.ml - lexer and preterm/term parser.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set.

FAITHFULNESS BASIS.  The precedence/associativity SHAPES are DERIVED from the
infix table set in bool.ml (`<=>`=2 right, `==>`=4 right, `\/`=6 right, `/\`=8
right, `=`=12 right) together with the prefix `~` and the binders `! ? \`.  The
lexer escape codes are taken VERBATIM from parser.ml's `escapecode` (parser.ml
120-134): `\n`,`\t`,`\r`,`\b`,`\\`,`\"`,`\'`, `\xHH` (hex) and `\DDD` (decimal).
The identifier rule is parser.ml's `simple_ident`: an identifier is the longest
run of alphanumerics OR of symbolics, so an alnum run and a following symbolic
run lex as TWO tokens.

Structural assertions (via `dest_imp`/`dest_conj`/`dest_forall`) avoid pinning a
printed string, so a printer defect cannot mask a parser defect here.

VERIFIED SIGNATURES (read from source):
  HolCore.Parser.parse_term : String -> IO (Except String term)     (Parser.lean)
  HolCore.Parser.lex        : Ctx -> List String -> Except PErr (List lexcode)
                                                                     (Parser.lean)
  HolCore.Parser.mkCtx      : IO Ctx                                  (Parser.lean)
  HolCore.Parser.lexcode    : | Ident (s) | Resword (s)  (BEq, Repr)  (Parser.lean)
  HolCore.Lib.explode       : String -> List String                  (Lib.lean 634)
  HolCore.Basics.dest_imp   : term -> Except String (term × term)    (Basics.lean 418)
  HolCore.Basics.dest_forall: term -> Except String (term × term)    (Basics.lean 421)
  HolCore.Basics.is_conj    : term -> Bool                           (Basics.lean 413)
  HolCore.Basics.dest_conj  : term -> Except String (term × term)    (Basics.lean 414)
  Session.ADD_SYM           : thm                                     (Session.lean 2141)

FLAGGED AS INFEASIBLE (see bottom): the `//` comment skip.  `reserve_words` is
never called anywhere in the loaded theory, so `//` is not a reserved word and
the lexer emits `Ident "//"` rather than the `Resword "//"` the skip checks for.
Testing it would require mutating shared reserved-word state, which is unsafe in
the shared build. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

namespace HolTest.ParserTest

/- ---------------------------------------------------------------------- -/
/- PRECEDENCE SHAPES (DERIVED -> `DIFFERS`).  Parse a mixed-precedence term -/
/- and assert its TOP operator and nesting by structure, not by print.     -/
/- ---------------------------------------------------------------------- -/

-- `p /\ q ==> r`: `==>` (4) is lower than `/\` (8), so the parse tree's TOP
-- must be `==>`, with the `/\` on its LEFT.  (Help/parse_term.hlp uses this
-- very string.)  This is the parse-side companion to PrinterTest's print pin.
#eval (do
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "p /\\ q ==> r" with
  | .error e => IO.println s!"prec: /\\ binds tighter than ==> -> DIFFERS parse {e}"
  | .ok tm =>
    match HolCore.Basics.dest_imp tm with
    | .error _ => IO.println "prec: /\\ binds tighter than ==> -> DIFFERS top not ==>"
    | .ok (l, _) =>
      if is_conj l then IO.println "prec: /\\ binds tighter than ==> -> OK"
      else IO.println "prec: /\\ binds tighter than ==> -> DIFFERS left not /\\")

-- `p \/ q /\ r`: `/\` (8) binds tighter than `\/` (6), so TOP is `\/` and its
-- RIGHT operand is the `/\`.
#eval (do
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "p \\/ q /\\ r" with
  | .error e => IO.println s!"prec: /\\ binds tighter than \\/ -> DIFFERS parse {e}"
  | .ok tm =>
    match HolCore.Basics.dest_disj tm with
    | .error _ => IO.println "prec: /\\ binds tighter than \\/ -> DIFFERS top not \\/"
    | .ok (_, r) =>
      if is_conj r then IO.println "prec: /\\ binds tighter than \\/ -> OK"
      else IO.println "prec: /\\ binds tighter than \\/ -> DIFFERS right not /\\")

/- ---------------------------------------------------------------------- -/
/- ASSOCIATIVITY SHAPES (DERIVED -> `DIFFERS`).  All the bool infixes are    -/
/- RIGHT-associative, so `p ==> q ==> r` parses as `p ==> (q ==> r)`: the   -/
/- top `==>`'s RIGHT operand is itself an `==>`, and its LEFT operand is a   -/
/- plain variable (NOT an `==>`).  A left-assoc bug fails both halves.      -/
/- ---------------------------------------------------------------------- -/

#eval (do
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "p ==> q ==> r" with
  | .error e => IO.println s!"assoc: ==> right-associative -> DIFFERS parse {e}"
  | .ok tm =>
    match HolCore.Basics.dest_imp tm with
    | .error _ => IO.println "assoc: ==> right-associative -> DIFFERS top not ==>"
    | .ok (l, r) =>
      let rightNested := (HolCore.Basics.dest_imp r).toOption.isSome
      let leftFlat := !(HolCore.Basics.dest_imp l).toOption.isSome
      if rightNested && leftFlat then
        IO.println "assoc: ==> right-associative -> OK"
      else
        IO.println s!"assoc: ==> right-associative -> DIFFERS rightNested={rightNested} leftFlat={leftFlat}")

/- ---------------------------------------------------------------------- -/
/- BINDER PARSE SHAPE (DERIVED -> `DIFFERS`).  `!x y. p` parses as two       -/
/- nested universals, so `dest_forall` twice peels `x` then `y`.            -/
/- ---------------------------------------------------------------------- -/

#eval (do
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "!x y. x /\\ y" with
  | .error e => IO.println s!"binder: !x y. parses two nested ! -> DIFFERS parse {e}"
  | .ok tm =>
    match (do let (_, b1) ← dest_forall tm; dest_forall b1) with
    | .ok (_, body2) =>
      if is_conj body2 then IO.println "binder: !x y. parses two nested ! -> OK"
      else IO.println "binder: !x y. parses two nested ! -> DIFFERS body not /\\"
    | .error _ => IO.println "binder: !x y. parses two nested ! -> DIFFERS not two foralls")

/- ---------------------------------------------------------------------- -/
/- LEXER ESCAPE CODES (VERBATIM from parser.ml `escapecode` -> `MISMATCH`).  -/
/-                                                                        -/
/- Drive the PUBLIC pure `lex` over a `Ctx` snapshot.  A quoted string      -/
/- literal lexes to a SINGLE `Ident` token whose content is the decoded     -/
/- string wrapped in quotes.  We compare the decoded char against the       -/
/- expected code, so a broken escape decoder is caught without depending on -/
/- the char-term/list theory being loaded.                                  -/
/- ---------------------------------------------------------------------- -/

/-- Lex `src`, expect exactly one `Ident` token, and return its content
    (without surrounding quotes if it is a string literal). -/
private def lexOneIdent (c : Ctx) (src : String) : Except String String :=
  match HolCore.Parser.lex c (explode src) with
  | .error _ => .error "lex failed"
  | .ok toks =>
    match toks with
    | [.Ident s] => .ok s
    | _ => .error s!"expected one Ident, got {reprStr toks}"

-- `\n` decodes to a newline: the string literal "\n" (in HOL source) lexes to
-- Ident containing quote, newline, quote — length 3, middle char code 10.
#eval (do
  let c ← mkCtx
  match lexOneIdent c "\"\\n\"" with
  | .error e => IO.println s!"lex escape \\n -> MISMATCH {e}"
  | .ok s =>
    let cs := s.toList
    if cs.length == 3 && cs[1]?.map Char.toNat == some 10 then
      IO.println "lex escape \\n (newline) -> OK"
    else IO.println s!"lex escape \\n -> MISMATCH decoded={reprStr cs}")

-- `\t` decodes to a tab (code 9).
#eval (do
  let c ← mkCtx
  match lexOneIdent c "\"\\t\"" with
  | .error e => IO.println s!"lex escape \\t -> MISMATCH {e}"
  | .ok s =>
    let cs := s.toList
    if cs.length == 3 && cs[1]?.map Char.toNat == some 9 then
      IO.println "lex escape \\t (tab) -> OK"
    else IO.println s!"lex escape \\t -> MISMATCH decoded={reprStr cs}")

-- `\065` (decimal) decodes to 'A' (code 65).
#eval (do
  let c ← mkCtx
  match lexOneIdent c "\"\\065\"" with
  | .error e => IO.println s!"lex escape \\DDD -> MISMATCH {e}"
  | .ok s =>
    let cs := s.toList
    if cs.length == 3 && cs[1]? == some 'A' then
      IO.println "lex escape \\065 (decimal 'A') -> OK"
    else IO.println s!"lex escape \\065 -> MISMATCH decoded={reprStr cs}")

-- `\x41` (hex) decodes to 'A' (code 0x41 = 65).
#eval (do
  let c ← mkCtx
  match lexOneIdent c "\"\\x41\"" with
  | .error e => IO.println s!"lex escape \\xHH -> MISMATCH {e}"
  | .ok s =>
    let cs := s.toList
    if cs.length == 3 && cs[1]? == some 'A' then
      IO.println "lex escape \\x41 (hex 'A') -> OK"
    else IO.println s!"lex escape \\x41 -> MISMATCH decoded={reprStr cs}")

-- `\\` decodes to a single backslash (code 92).
#eval (do
  let c ← mkCtx
  match lexOneIdent c "\"\\\\\"" with
  | .error e => IO.println s!"lex escape \\\\ -> MISMATCH {e}"
  | .ok s =>
    let cs := s.toList
    if cs.length == 3 && cs[1]?.map Char.toNat == some 92 then
      IO.println "lex escape \\\\ (backslash) -> OK"
    else IO.println s!"lex escape \\\\ -> MISMATCH decoded={reprStr cs}")

/- ---------------------------------------------------------------------- -/
/- LEXER IDENTIFIER RUNS (DERIVED -> `DIFFERS`).  `simple_ident` is the      -/
/- longest run of alphanumerics OR of symbolics.  So an alnum run followed  -/
/- by a symbolic run lexes as TWO tokens, and a pure symbolic run as ONE.   -/
/- ---------------------------------------------------------------------- -/

-- "ab+" : "ab" (alnum) then "+" (symbolic) -> two tokens.
#eval (do
  let c ← mkCtx
  match HolCore.Parser.lex c (explode "ab+") with
  | .error _ => IO.println "lex: alnum then symbolic split -> DIFFERS lex failed"
  | .ok toks =>
    if toks == [lexcode.Ident "ab", lexcode.Ident "+"] then
      IO.println "lex: alnum then symbolic split (ab+) -> OK"
    else IO.println s!"lex: alnum then symbolic split -> DIFFERS got {reprStr toks}")

-- "<=>" is a single symbolic run -> one token (a maximal munch, NOT `<`,`=`,`>`).
#eval (do
  let c ← mkCtx
  match HolCore.Parser.lex c (explode "<=>") with
  | .error _ => IO.println "lex: symbolic maximal munch -> DIFFERS lex failed"
  | .ok toks =>
    match toks with
    | [_] => IO.println "lex: symbolic maximal munch (<=>) -> OK"
    | _ => IO.println s!"lex: symbolic maximal munch -> DIFFERS got {reprStr toks}")

/- ---------------------------------------------------------------------- -/
/- PARSER FAILURE CASE (DERIVED -> the correctly-rejected form).            -/
/- Trailing tokens after a complete term must be rejected with the exact    -/
/- message "Unparsed input following term" (parse_term, Parser.lean).       -/
/- ---------------------------------------------------------------------- -/

#eval (do
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "p q )" with
  | .ok _ => IO.println "parser: unparsed input -> DIFFERS unexpectedly parsed"
  | .error e =>
    if e == "Unparsed input following term" then
      IO.println "parser: unparsed input rejected -> OK (correctly rejected)"
    else IO.println s!"parser: unparsed input -> DIFFERS msg=\"{e}\"")

/- INFEASIBLE: the `//` comment skip.  `reserve_words` is never called in the
   loaded theory, so `//` is lexed as `Ident "//"` and never equals the
   `Resword "//"` the skip compares against.  A faithful test would need to
   mutate the shared reserved-word ref, which is unsafe under the shared build,
   so this coverage is omitted and flagged for the coordinator. -/
/- The `[[ ]]` quotation keeps text that looks like a Lean comment: real
   negation at its start (`[[--a < x ...]]`) once lost the rest of the
   line, because the scan began after the comment Lean had skipped. -/
#eval show IO Unit from do
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))
  let q : IO (Except String term) := [[--a < x /\ x < a /\
    --a < y]]
  match ← q, ← HolCore.Parser.parse_term "--a < x /\\ x < a /\\ --a < y" with
  | .ok t, .ok u =>
    -- (invented type variables differ between the two parses)
    let names (tm : term) := (HolCore.Kernel.frees tm).filterMap fun v =>
      match HolCore.Kernel.dest_var v with | .ok (n, _) => some n | .error _ => none
    if (HolCore.Basics.conjuncts t).length == 3 && names t == names u then
      IO.println "quotation: leading -- kept -> OK"
    else IO.println s!"quotation: leading -- -> MISMATCH got {← HolCore.Printer.string_of_term t}"
  | .error e, _ | _, .error e => IO.println s!"quotation: leading -- -> MISMATCH error {e}"

end HolTest.ParserTest
