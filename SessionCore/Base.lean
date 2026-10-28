/- File: SessionCore/Base.lean
The start of the session: the `[[ ... ]]` term quotations, the coercions that
let rule results and quotations compose without `do`, the `Repr`/`ToString`
instances that make `#eval` print values as the OCaml toplevel does, and the
quiet load (`beginQuietLoad`, the first `initialize` of the session).

Every later module of SessionCore and SessionMath builds one HOL Light file's
load-time state with `initialize`, in hol_lib.ml order; `Session.lean` imports
the last of them, so `import Session` loads the whole library.

The only `unsafe` code here is the printing for `#eval`/`Repr` and the
quotation coercion (`[[ ]]` to `term`), which must turn an `IO` action into a
value; each is a safe `opaque` with an `implemented_by` implementation.
-/
import Lean
import HolCore.Theorems
import HolCore.Classic
import HolCore.Trivia
import HolCore.Canon
import HolCore.Meson
import HolCore.Metis
import HolMath.Grobner

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Itab HolCore.Simp HolCore.Theorems HolCore.Classic
open HolCore.Trivia HolCore.Printer

/- ---------------------------------------------------------------------- -/
/- Term/type quotation syntax `[[ ... ]]` (HOL Light's `pa_j` expander).  -/
/- Raw text between `[[` and `]]` is scanned verbatim and dispatched:     -/
/-   `[[ :T ]]` → parse_type "T"; `[[ s: ]]` → raw string; else           -/
/-   parse_term.                                                          -/
/- ---------------------------------------------------------------------- -/
namespace HolCore.Quotation

open Lean Lean.Parser Lean.Elab.Term

/-- Node kind for the quotation. -/
def holQuotKind : SyntaxNodeKind := `HolCore.Quotation.holQuot

/-- Raw scanner: read verbatim up to `]]`, push the contents, skip past `]]`. -/
private partial def scanTo (startPos : String.Pos.Raw) : ParserFn := fun c s =>
  let i := s.pos
  if h : c.atEnd i then
    s.mkError "unterminated [[ ... ]] quotation"
  else
    let curr := c.get' i h
    if curr == ']' then
      let j := c.next' i h
      if hj : c.atEnd j then
        s.mkError "unterminated [[ ... ]] quotation"
      else if c.get' j hj == ']' then
        let contents := c.extract startPos i
        let s := s.pushSyntax (Syntax.mkStrLit contents)
        let s := s.setPos (c.next' j hj)
        whitespace c s
      else
        scanTo startPos c (s.next' c i h)
    else
      scanTo startPos c (s.next' c i h)

/-- Raw-scan combinator (from just after `[[`).  It restarts at the END of
    the `[[` token, not at the current position: the token parser has
    already skipped the whitespace and comments after `[[`, and HOL text
    can look like a Lean comment (`[[--x < a ...]]`, real negation), which
    would otherwise lose the rest of its line. -/
def holQuotRaw : Parser := {
  fn := fun c s =>
    let start := match s.stxStack.back with
      | .atom (.original _ _ _ endPos) _ => endPos
      | _ => s.pos
    scanTo start c (s.setPos start),
  info := {} }

@[combinator_formatter holQuotRaw]
def holQuotRaw.formatter : Lean.PrettyPrinter.Formatter := pure ()

@[combinator_parenthesizer holQuotRaw]
def holQuotRaw.parenthesizer : Lean.PrettyPrinter.Parenthesizer := pure ()

/-- The quotation parser: token `[[` then the raw scan to `]]`. -/
@[term_parser]
def holQuotParser : Parser :=
  leadingNode holQuotKind maxPrec (symbol "[[" >> holQuotRaw)

/-- Dispatch on the captured raw string, mirroring `quotexpander`. -/
@[term_elab holQuot]
def elabHolQuot : TermElab := fun stx expectedType? => do
  let some raw := stx[1].isStrLit? | throwError "malformed [[ ]] quotation"
  let s := raw.trimAscii.toString
  if s.isEmpty then throwError "Empty quotation"
  else if s.front == ':' then
    let body := String.ofList (s.toList.drop 1)
    elabTerm (← `(HolCore.Parser.parse_type $(Syntax.mkStrLit body))) expectedType?
  else if s.back == ':' then
    let body := String.ofList s.toList.dropLast
    elabTerm (Syntax.mkStrLit body) expectedType?
  else
    elabTerm (← `(HolCore.Parser.parse_term $(Syntax.mkStrLit s))) expectedType?

end HolCore.Quotation

namespace Session

/- ---------------------------------------------------------------------- -/
/- The only effectful-to-pure bridges, each a safe opaque with an unsafe  -/
/- `implemented_by` implementation (Session.lean 141-240).                -/
/- ---------------------------------------------------------------------- -/

private unsafe def runStringImpl (act : IO String) (fallback : String) : String :=
  match unsafeIO act with | .ok s => s | .error _ => fallback
/-- Run an `IO String` printer purely for display; fall back on failure. -/
@[implemented_by runStringImpl] opaque runString (act : IO String) (fallback : String) : String

private unsafe def runTermImpl (a : IO (Except String term)) : term :=
  match unsafeIO a with
  | .ok (.ok t) => t
  | .ok (.error e) => panic! s!"term quotation parse error: {e}"
  | .error e => panic! s!"term quotation IO error: {e}"
/-- A `[[ ]]` quotation used as a `term` (parse failure panics, as HOL Light's
    `parse_term` raises). -/
@[implemented_by runTermImpl] opaque runTerm (a : IO (Except String term)) : term

private unsafe def runThmImpl (a : IO (Except String thm)) : thm :=
  match unsafeIO a with
  | .ok (.ok t) => t
  | .ok (.error e) => panic! s!"thm coercion error: {e}"
  | .error e => panic! s!"thm coercion IO error: {e}"
/-- The result of an `IO`-valued rule or conversion used as a `thm` (a
    failure panics with its message, as HOL Light raises). -/
@[implemented_by runThmImpl] opaque runThm (a : IO (Except String thm)) : thm

/-- Coercion so a rule result `Except String thm` is auto-unwrapped where a
    `thm` is expected — lets rule applications nest without `do` (errors
    become panics, as HOL Light throws). Interactive/test use only. -/
instance : CoeHead (Except String thm) thm :=
  ⟨fun r => match r with | .ok t => t | .error e => panic! s!"thm coercion error: {e}"⟩

/-- Coercion so a `[[ ... ]]` term quotation (`IO (Except String term)`) can be
    used directly where a `term` is expected. -/
instance : CoeHead (IO (Except String term)) term := ⟨runTerm⟩

/-- Coercion so the result of an `IO`-valued rule or conversion (such as
    `NUM_REDUCE_CONV`, `REAL_ARITH`, `prove`) can be used where a `thm` is
    expected, as HOL Light's `let th = NUM_REDUCE_CONV `2 + 2 * 3`;;`. -/
instance : CoeHead (IO (Except String thm)) thm := ⟨runThm⟩

/-- How the OCaml toplevel shows a theorem (`val it : thm = ...`): the value
    inside an enclosing box, so a short theorem with hypotheses stays on one
    line (`p /\ q |- p`).  `string_of_thm` itself has no enclosing box, as in
    printer.ml, so there the break before `|-` is taken. -/
private def string_of_thm_toplevel (th : thm) : IO String :=
  print_to_string_io (fun th => do
    let f ← pp_print_thm th
    return (do HolCore.System.Fmt.openBox 0; f; HolCore.System.Fmt.closeBox)) th

instance : ToString hol_type := ⟨fun ty => runString (string_of_type ty) "<type>"⟩
instance : ToString term := ⟨fun tm => runString (string_of_term tm) "<term>"⟩
instance : ToString thm := ⟨fun th => runString (string_of_thm_toplevel th) "<thm>"⟩

instance : Repr hol_type := ⟨fun ty _ => runString (string_of_type ty) "<type>"⟩
instance : Repr term := ⟨fun tm _ => runString (string_of_term tm) "<term>"⟩
instance : Repr thm := ⟨fun th _ => runString (string_of_thm_toplevel th) "<thm>"⟩

/-- `Repr` for rule results: theorem/term/type on `.ok`, message on `.error`. -/
instance : Repr (Except String thm) := ⟨fun r _ => match r with
  | .ok th => runString (string_of_thm_toplevel th) "<thm>"
  | .error e => "ERR: " ++ e⟩
instance : Repr (Except String term) := ⟨fun r _ => match r with
  | .ok tm => runString (string_of_term tm) "<term>"
  | .error e => "ERR: " ++ e⟩
instance : Repr (Except String hol_type) := ⟨fun r _ => match r with
  | .ok ty => runString (string_of_type ty) "<type>"
  | .error e => "ERR: " ++ e⟩

/-- hol.ml's `#install_printer pp_print_goalstack`: a goalstack (the result of
    `g`, `e`, `b`, `r`, `p`, ...) displays as HOL Light shows it.  (hol.ml
    installs the COLORED printers; these are the plain ones, since `#eval`
    output is not a terminal.) -/
instance : Repr goalstack := ⟨fun l _ =>
  runString (HolCore.Printer.print_to_string_io Tactics.pp_print_goalstack l) "<goalstack>"⟩


/- ---------------------------------------------------------------------- -/
/- The load runs quietly.  Session's whole load sequence runs while the   -/
/- module is being IMPORTED.  HOL Light prints its proofs' progress (MESON -/
/- counters, Grobner basis sizes, type-invention warnings: about 25,000    -/
/- lines for hol_lib.ml), but output printed during import has no reader:  -/
/- Lean attaches it to every later `#eval` of the importing file, and in   -/
/- the editor's language server it goes to the worker's protocol channel   -/
/- and the worker hangs.  So the printing switches are turned off here,    -/
/- before the first layer, and restored after the last (`endQuietLoad` in  -/
/- SessionMath/Define.lean), so the user's own commands print as HOL      -/
/- Light's do.                                                             -/
/- HOLLEAN_SHOW_LOAD=1 keeps them on, to see the load as HOL Light shows   -/
/- it (in a terminal only).  HOLLEAN_SHOW_LOAD=2 also turns on the tracing -/
/- switches `copverb`, `metisverb` and `Metis_unify.verb` for the load.    -/
/- ---------------------------------------------------------------------- -/

/-- The printing switches as they were before the load (restored after it). -/
structure LoadFlags where
  verbose : Bool
  typeInventionWarning : Bool
  grobnerMessages : Bool
  reportTiming : Bool
  /-- HOLLEAN_SHOW_LOAD=2 turned the METIS/CoP tracing on for the load. -/
  tracing : Bool
  deriving Inhabited

private def beginQuietLoad : IO LoadFlags := do
  let level := ((← IO.getEnv "HOLLEAN_SHOW_LOAD").bind String.toNat?).getD 0
  let saved : LoadFlags :=
    { verbose := ← HolCore.Lib.verbose.get
      typeInventionWarning := ← HolCore.Preterm.type_invention_warning.get
      grobnerMessages := ← HolMath.Grobner.grobner_messages.get
      reportTiming := ← HolCore.Lib.report_timing.get
      tracing := level ≥ 2 }
  if level == 0 then
    HolCore.Lib.verbose.set false
    HolCore.Preterm.type_invention_warning.set false
    HolMath.Grobner.grobner_messages.set false
    HolCore.Lib.report_timing.set false
  if level ≥ 2 then
    for f in [HolCore.FirstOrder.copverb, HolCore.Metis.metisverb,
              HolCore.Metis.metis_unify_verb] do f.set true
  return saved

/-- The switches saved by the quiet load (see above). -/
initialize loadFlags : LoadFlags ← beginQuietLoad

end Session
