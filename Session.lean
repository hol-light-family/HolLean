/- File: Session.lean
A HOL Light-style session: runs `setupBool` once at load and exposes the rule
record `B`, so an importing file can issue bare `#eval <expr>` lines
(auto-printed via the `Display` instances), the way the OCaml toplevel echoes
results. Also provides coercions that auto-unwrap `Except String thm` results
and `[[ ]]` term quotations, so rules/quotations compose without `do`.

Because `setupBool` is not idempotent, it runs once via `initialize` into a
cache ref; `B` is an `unsafe def` reading that cache.

Lean4 translation by Chris Walton 2026
-/
import Lean
import HolCore.Theorems
import HolCore.IndDefs
import HolCore.Classic
import HolCore.Trivia
import HolCore.Canon
import HolCore.Meson
import HolCore.FirstOrder
import HolCore.Metis
import HolCore.TheCops
import HolCore.Quot
import HolCore.ImpConv
import HolMath.Pair
import HolMath.Compute
import HolMath.Nums
import HolMath.Recursion
import HolMath.Arith
import HolMath.Wf
import HolMath.CalcNum
import HolMath.Normalizer
import HolMath.Grobner
import HolMath.IndTypes
import HolMath.Lists
import HolMath.RealAx
import HolMath.CalcInt
import HolMath.RealArith
import HolMath.Real
import HolMath.CalcRat
import HolMath.Int
import HolMath.Sets
import HolMath.Iterate
import HolMath.Cart
import HolMath.Define
import HolCore.Parser
import HolCore.Bool
import HolCore.Equal
import HolCore.Printer
import HolCore.Drule
import HolCore.Tactics
import HolCore.Itab
import HolCore.Simp

open HolCore
open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule HolCore.Tactics HolCore.Itab HolCore.Simp HolCore.Theorems HolCore.IndDefs HolCore.Classic HolCore.Trivia HolCore.Canon
open HolMath.Pair

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

/- ---------------------------------------------------------------------- -/
/- Session: display instances, run `setupBool` once, expose rules +       -/
/- coercions. Display bridges the `IO` printers to pure `ToString`/`Repr` -/
/- via `unsafeIO` (the `#install_printer` analogue; display use only).    -/
/- ---------------------------------------------------------------------- -/
namespace Session

open HolCore.Kernel HolCore.Printer

/-- Run an `IO String` printer purely for display; fall back on failure. -/
private unsafe def runPrinter (act : IO String) (fallback : String) : String :=
  match unsafeIO act with
  | .ok s    => s
  | .error _ => fallback

/-- How the OCaml toplevel shows a theorem (`val it : thm = ...`): the value
    inside an enclosing box, so a short theorem with hypotheses stays on one
    line (`p /\ q |- p`).  `string_of_thm` itself has no enclosing box, as in
    printer.ml, so there the break before `|-` is taken. -/
private def string_of_thm_toplevel (th : thm) : IO String :=
  print_to_string_io (fun th => do
    let f ← pp_print_thm th
    return (do HolCore.System.Fmt.openBox 0; f; HolCore.System.Fmt.closeBox)) th

unsafe instance : ToString hol_type where
  toString ty := runPrinter (string_of_type ty) "<type>"
unsafe instance : ToString term where
  toString tm := runPrinter (string_of_term tm) "<term>"
unsafe instance : ToString thm where
  toString th := runPrinter (string_of_thm_toplevel th) "<thm>"

unsafe instance : Repr hol_type where
  reprPrec ty _ := runPrinter (string_of_type ty) "<type>"
unsafe instance : Repr term where
  reprPrec tm _ := runPrinter (string_of_term tm) "<term>"
unsafe instance : Repr thm where
  reprPrec th _ := runPrinter (string_of_thm_toplevel th) "<thm>"

/-- `Repr` for rule results: theorem/term/type on `.ok`, message on `.error`. -/
unsafe instance : Repr (Except String thm) where
  reprPrec r _ := match r with
    | .ok th => runPrinter (string_of_thm_toplevel th) "<thm>"
    | .error e => "ERR: " ++ e
unsafe instance : Repr (Except String term) where
  reprPrec r _ := match r with
    | .ok tm => runPrinter (string_of_term tm) "<term>"
    | .error e => "ERR: " ++ e
unsafe instance : Repr (Except String hol_type) where
  reprPrec r _ := match r with
    | .ok ty => runPrinter (string_of_type ty) "<type>"
    | .error e => "ERR: " ++ e

deriving instance Inhabited for HolCore.Bool.BoolThms

/-- Cache for the established boolean theory (populated once at load). -/
initialize theBool : IO.Ref (Option BoolThms) ← IO.mkRef none

/-- Run `setupBool` once at load and cache it. -/
initialize (do
  match ← setupBool.run with
  | .ok b => theBool.set (some b)
  | .error e => throw (IO.userError s!"setupBool failed: {e}"))

/-- `set_verbose_symbols();;` - the LAST line of bool.ml (504), run at load.
    Installs `forall`/`exists`/`existsunique` as binders and interface names
    `true`/`false`/`forall`/`exists`/`existsunique` for `T`/`F`/`!`/`?`/`?!`,
    so terms PRINT as `forall x. ...` and `true /\ false` (HOL Light's own
    UnitTests/printer_tests.ml expects exactly that), while the symbolic forms
    still parse.  `unset_verbose_symbols` restores the terse printing. -/
initialize (do
  match ← HolCore.Bool.set_verbose_symbols with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"set_verbose_symbols failed: {e}"))

/-- The established boolean theory (rules + theorems); private cache reader. -/
private unsafe def B : BoolThms :=
  match unsafeIO theBool.get with
  | .ok (some b) => b
  | _ => panic! "Session.B: setupBool not initialised"

/-- Coercion so a rule result `Except String thm` is auto-unwrapped where a
    `thm` is expected — lets rule applications nest without `do` (errors
    become panics, as HOL Light throws). Interactive/test use only. -/
unsafe instance : CoeHead (Except String thm) thm :=
  ⟨fun r => match r with | .ok t => t | .error e => panic! s!"thm coercion error: {e}"⟩

/-- Coercion so a `[[ ... ]]` term quotation (`IO (Except String term)`) can be
    used directly where a `term` is expected. Runs the parse via `unsafeIO`.
    Parse/typecheck failures panic with the underlying message (mirroring
    HOL Light's `parse_term`, which `failwith`s and propagates the reason). -/
unsafe instance : CoeHead (IO (Except String term)) term :=
  ⟨fun a => match unsafeIO a with
            | .ok (.ok t) => t
            | .ok (.error e) => panic! s!"term quotation parse error: {e}"
            | .error e => panic! s!"term quotation IO error: {e}"⟩

/-- Coercion so the result of an `IO`-valued rule or conversion (such as
    `NUM_REDUCE_CONV`, `REAL_ARITH`, `prove`) can be used where a `thm` is
    expected, e.g. `unsafe def th : thm := NUM_REDUCE_CONV [[2 + 2 * 3]]`, as
    HOL Light's `let th = NUM_REDUCE_CONV `2 + 2 * 3`;;`.  Runs the action via
    `unsafeIO`; a failure panics with its message.  Interactive use only. -/
unsafe instance : CoeHead (IO (Except String thm)) thm :=
  ⟨fun a => match unsafeIO a with
            | .ok (.ok t) => t
            | .ok (.error e) => panic! s!"thm coercion error: {e}"
            | .error e => panic! s!"thm coercion IO error: {e}"⟩

/-- Cache for the `_FALSITY_` definitional theorem (`|- _FALSITY_ = F`),
    populated once at load via `Drule.new_definition`. -/
initialize theFalsity : IO.Ref (Option thm) ← IO.mkRef none

/-- Parse quotations that a HolCore file parses when it loads but whose Lean
    translation builds the same term directly (a pure definition cannot parse).
    Parsing them here, in file order, keeps the type-variable counter in step
    with HOL Light. -/
private def parseLoadQuotes (qs : List String) : IO Unit := do
  for s in qs do
    match ← HolCore.Parser.parse_term s with
    | .ok _ => pure ()
    | .error e => throw (IO.userError s!"load quotation {s}: {e}")

initialize (do
  match ← theBool.get with
  | none => throw (IO.userError "theFalsity: setupBool not initialised")
  | some b =>
    -- drule.ml 33, 37: MK_CONJ's `(/\)`, MK_DISJ's `(\/)`.
    parseLoadQuotes ["(/\\)", "(\\/)"]
    match ← Drule.new_definition b ((← HolCore.Parser.parse_term "_FALSITY_ = F").toOption.get!) with
    | .ok th =>
      theFalsity.set (some th)
      -- tactics.ml 105 (mk_fthm's `_FALSITY_`), 117 (VALID's), 350 (CONV_TAC's
      -- `T`), 432 (DISCH_TAC's `F`), 754-755 (ANTS_TAC's terms, the `and`
      -- pair left to right); simp.ml 80 (term_order's `T`).
      parseLoadQuotes ["_FALSITY_", "_FALSITY_", "T", "F", "p /\\ (q ==> r)", "p ==> q", "T"]
    | .error e => throw (IO.userError s!"_FALSITY_ definition failed: {e}"))

/-- The `_FALSITY_` definitional theorem; private cache reader. -/
private unsafe def falsityDef : thm :=
  match unsafeIO theFalsity.get with
  | .ok (some th) => th
  | _ => panic! "Session.falsityDef: not initialised"

/-- `_FALSITY_` (tactics.ml 101): `|- _FALSITY_ <=> F`. -/
unsafe def FALSITY_DEF : thm := falsityDef

/-- Cache for the `theorems.ml` layer (proved once by `setupTheorems`). -/
initialize theTheorems : IO.Ref (Option TheoremThms) ← IO.mkRef none

/-- The established `theorems.ml` layer; computes and caches on first access
    (runs `setupTheorems B` once, which also populates the basic rewrites). -/
private unsafe def T : TheoremThms :=
  match unsafeIO (do
    match ← theTheorems.get with
    | some t => pure t
    | none =>
      match ← (setupTheorems B).run with
      | .ok t => do theTheorems.set (some t); pure t
      | .error e => panic! s!"setupTheorems failed: {e}") with
  | .ok t => t
  | _ => panic! "Session.T: setupTheorems not run"

/- Expose the `BoolThms` rules/theorems as top-level names, so tests can write
   `CONJ`, `SPEC`, `DISCH`, … (HOL Light style) instead of `B.CONJ`. -/
unsafe def T_DEF := B.T_DEF
unsafe def TRUTH := B.TRUTH
unsafe def EQT_ELIM := B.EQT_ELIM
unsafe def EQT_INTRO := B.EQT_INTRO
unsafe def AND_DEF := B.AND_DEF
unsafe def CONJ := B.CONJ
unsafe def CONJUNCT1 := B.CONJUNCT1
unsafe def CONJUNCT2 := B.CONJUNCT2
unsafe def CONJ_PAIR := B.CONJ_PAIR
unsafe def CONJUNCTS := B.CONJUNCTS
unsafe def IMP_DEF := B.IMP_DEF
unsafe def MP := B.MP
unsafe def DISCH := B.DISCH
unsafe def DISCH_ALL := B.DISCH_ALL
unsafe def UNDISCH := B.UNDISCH
unsafe def UNDISCH_ALL := B.UNDISCH_ALL
unsafe def IMP_ANTISYM_RULE := B.IMP_ANTISYM_RULE
unsafe def ADD_ASSUM := B.ADD_ASSUM
unsafe def EQ_IMP_RULE := B.EQ_IMP_RULE
unsafe def IMP_TRANS := B.IMP_TRANS
unsafe def FORALL_DEF := B.FORALL_DEF
unsafe def SPEC := B.SPEC
unsafe def SPECL := B.SPECL
unsafe def SPEC_VAR := B.SPEC_VAR
unsafe def SPEC_ALL := B.SPEC_ALL
unsafe def GEN := B.GEN
unsafe def GENL := B.GENL
unsafe def GEN_ALL := B.GEN_ALL
unsafe def ISPEC := B.ISPEC
unsafe def ISPECL := B.ISPECL
unsafe def EXISTS_DEF := B.EXISTS_DEF
unsafe def EXISTS := B.EXISTS
unsafe def SIMPLE_EXISTS := B.SIMPLE_EXISTS
unsafe def CHOOSE := B.CHOOSE
unsafe def SIMPLE_CHOOSE := B.SIMPLE_CHOOSE
unsafe def OR_DEF := B.OR_DEF
unsafe def DISJ1 := B.DISJ1
unsafe def DISJ2 := B.DISJ2
unsafe def DISJ_CASES := B.DISJ_CASES
unsafe def SIMPLE_DISJ_CASES := B.SIMPLE_DISJ_CASES
unsafe def F_DEF := B.F_DEF
unsafe def NOT_DEF := B.NOT_DEF
unsafe def NOT_ELIM := B.NOT_ELIM
unsafe def NOT_INTRO := B.NOT_INTRO
unsafe def EQF_INTRO := B.EQF_INTRO
unsafe def EQF_ELIM := B.EQF_ELIM
unsafe def CONTR := B.CONTR
unsafe def EXISTS_UNIQUE_DEF := B.EXISTS_UNIQUE_DEF
unsafe def EXISTENCE := B.EXISTENCE

/- Drule rules. The `B`-parameterized ones are closed over `B`; the standalone
   ones are re-exported. -/
unsafe def mk_thm := Drule.mk_thm B
unsafe def MP_CONV := Drule.MP_CONV B
unsafe def INSTANTIATE_ALL := Drule.INSTANTIATE_ALL B
unsafe def PART_MATCH := Drule.PART_MATCH B
unsafe def GEN_PART_MATCH := Drule.GEN_PART_MATCH B
unsafe def MATCH_MP := Drule.MATCH_MP B
unsafe def HIGHER_REWRITE_CONV := Drule.HIGHER_REWRITE_CONV B
-- standalone (no B):
export Drule (MK_CONJ MK_DISJ MK_FORALL MK_EXISTS BETAS_CONV instantiate
  INSTANTIATE type_unify term_unify term_type_unify deep_alpha term_match)

/- Tactics. The core machinery and B-parameterized tactics are closed over `B`
   (and `falsityDef` where needed); pure combinators are re-exported. -/
unsafe def mk_fthm (asl : List term) (c : term) := Tactics.mk_fthm B falsityDef asl c
unsafe def VALID := Tactics.VALID B falsityDef
unsafe def inst_goal := Tactics.inst_goal B
unsafe def THEN := Tactics.THEN B
unsafe def THENL := Tactics.THENL B
/-- `then1_` (tactics.ml 164): `THEN` that fails unless the first tactic
    leaves exactly one subgoal.  What pa_j turns `THEN` into after
    `unset_then_multiple_subgoals`. -/
unsafe def then1_ := Tactics.then1_ B
unsafe def TRY := Tactics.TRY B
unsafe def REPEAT := Tactics.REPEAT B
unsafe def EVERY := Tactics.EVERY B
unsafe def FIRST := Tactics.FIRST B
unsafe def MAP_EVERY {α} := @Tactics.MAP_EVERY α B
unsafe def MAP_FIRST {α} := @Tactics.MAP_FIRST α B
unsafe def CHANGED_TAC := Tactics.CHANGED_TAC B
unsafe def REPLICATE_TAC := Tactics.REPLICATE_TAC B
unsafe def LABEL_TAC := Tactics.LABEL_TAC B
unsafe def ASSUME_TAC := Tactics.ASSUME_TAC B
unsafe def EVERY_ASSUM := Tactics.EVERY_ASSUM B
unsafe def RULE_ASSUM_TAC := Tactics.RULE_ASSUM_TAC B
unsafe def ACCEPT_TAC := Tactics.ACCEPT_TAC B
unsafe def CONV_TAC := Tactics.CONV_TAC B
unsafe def REFL_TAC := Tactics.REFL_TAC B
unsafe def ABS_TAC := Tactics.ABS_TAC B
unsafe def MK_COMB_TAC := Tactics.MK_COMB_TAC B
unsafe def AP_TERM_TAC := Tactics.AP_TERM_TAC B
unsafe def AP_THM_TAC := Tactics.AP_THM_TAC B
unsafe def BINOP_TAC := Tactics.BINOP_TAC B
unsafe def SUBST1_TAC := Tactics.SUBST1_TAC B
unsafe def SUBST_ALL_TAC := Tactics.SUBST_ALL_TAC B
unsafe def BETA_TAC := Tactics.BETA_TAC B
unsafe def SUBST_VAR_TAC := Tactics.SUBST_VAR_TAC B
unsafe def DISCH_TAC := Tactics.DISCH_TAC B
unsafe def MP_TAC := Tactics.MP_TAC B
unsafe def EQ_TAC := Tactics.EQ_TAC B
unsafe def UNDISCH_TAC := Tactics.UNDISCH_TAC B
unsafe def SPEC_TAC := Tactics.SPEC_TAC B
unsafe def X_GEN_TAC := Tactics.X_GEN_TAC B
unsafe def X_CHOOSE_TAC := Tactics.X_CHOOSE_TAC B
unsafe def EXISTS_TAC := Tactics.EXISTS_TAC B
unsafe def GEN_TAC := Tactics.GEN_TAC B
unsafe def CHOOSE_TAC := Tactics.CHOOSE_TAC B
unsafe def CONJ_TAC := Tactics.CONJ_TAC B
unsafe def DISJ1_TAC := Tactics.DISJ1_TAC B
unsafe def DISJ2_TAC := Tactics.DISJ2_TAC B
unsafe def DISJ_CASES_TAC := Tactics.DISJ_CASES_TAC B
unsafe def CONTR_TAC := Tactics.CONTR_TAC B
unsafe def MATCH_ACCEPT_TAC := Tactics.MATCH_ACCEPT_TAC B
unsafe def MATCH_MP_TAC := Tactics.MATCH_MP_TAC B
unsafe def TRANS_TAC := Tactics.TRANS_TAC B
unsafe def CONJUNCTS_THEN2 := Tactics.CONJUNCTS_THEN2 B
unsafe def CONJUNCTS_THEN := Tactics.CONJUNCTS_THEN B
unsafe def DISJ_CASES_THEN2 := Tactics.DISJ_CASES_THEN2 B
unsafe def DISJ_CASES_THEN := Tactics.DISJ_CASES_THEN B
unsafe def DISCH_THEN := Tactics.DISCH_THEN B
unsafe def X_CHOOSE_THEN := Tactics.X_CHOOSE_THEN B
unsafe def CHOOSE_THEN := Tactics.CHOOSE_THEN B
unsafe def STRIP_THM_THEN := Tactics.STRIP_THM_THEN B
unsafe def ANTE_RES_THEN := Tactics.ANTE_RES_THEN B
unsafe def IMP_RES_THEN := Tactics.IMP_RES_THEN B
unsafe def STRIP_ASSUME_TAC := Tactics.STRIP_ASSUME_TAC B
unsafe def STRUCT_CASES_THEN := Tactics.STRUCT_CASES_THEN B
unsafe def STRUCT_CASES_TAC := Tactics.STRUCT_CASES_TAC B
unsafe def STRIP_GOAL_THEN := Tactics.STRIP_GOAL_THEN B
unsafe def STRIP_TAC := Tactics.STRIP_TAC B
unsafe def UNDISCH_THEN := Tactics.UNDISCH_THEN B
unsafe def FIRST_X_ASSUM := Tactics.FIRST_X_ASSUM B
unsafe def SUBGOAL_THEN := Tactics.SUBGOAL_THEN B
unsafe def SUBGOAL_TAC := Tactics.SUBGOAL_TAC B
unsafe def FREEZE_THEN := Tactics.FREEZE_THEN B
unsafe def X_META_EXISTS_TAC := Tactics.X_META_EXISTS_TAC B
unsafe def META_EXISTS_TAC := Tactics.META_EXISTS_TAC B
unsafe def META_SPEC_TAC := Tactics.META_SPEC_TAC B
unsafe def CHEAT_TAC := Tactics.CHEAT_TAC B
unsafe def ANTS_TAC := Tactics.ANTS_TAC B
unsafe def by_ := Tactics.by_ B
unsafe def mk_goalstate := Tactics.mk_goalstate B
unsafe def TAC_PROOF := Tactics.TAC_PROOF B
unsafe def prove := Tactics.prove B
-- no-B combinators / printing:
export Tactics (null_inst null_meta equals_goal compose_insts
  ORELSE FAIL_TAC NO_TAC ALL_TAC THEN_TCL ORELSE_TCL REPEAT_TCL REPEAT_GTCL
  ALL_THEN NO_THEN EVERY_TCL FIRST_TCL FIND_ASSUM POP_ASSUM ASSUM_LIST
  POP_ASSUM_LIST FIRST_ASSUM USE_THEN REMOVE_THEN NAME_ASSUMS_TAC ASM HYP
  rotate pp_print_goal print_goal pp_print_goalstack print_goalstack
  pp_print_colored_goal pp_print_colored_goalstack print_goal_hyp_max_boxes
  PRINT_GOAL_TAC PRINT_COLORED_GOAL_TAC REMARK_TAC)

/-- hol.ml's `#install_printer pp_print_goalstack`: a goalstack (the result of
    `g`, `e`, `b`, `r`, `p`, ...) displays as HOL Light shows it.  (hol.ml
    installs the COLORED printers; these are the plain ones, since `#eval`
    output is not a terminal.) -/
unsafe instance : Repr goalstack where
  reprPrec l _ := runPrinter (HolCore.Printer.print_to_string_io Tactics.pp_print_goalstack l)
    "<goalstack>"

/-- hol.ml's `#install_printer pp_print_goal`. -/
unsafe instance : Repr goal where
  reprPrec g _ := runPrinter (HolCore.Printer.print_to_string_io Tactics.pp_print_goal g) "<goal>"

/- ---------------------------------------------------------------------- -/
/- Interactive "subgoal package": mutable current goalstack + commands.   -/
/- ---------------------------------------------------------------------- -/

/-- The mutable interactive goalstack. -/
initialize currentGoalstack : IO.Ref goalstack ← IO.mkRef []

/-- Apply a refinement to the current goalstack, pushing the new state. -/
unsafe def refine (r : refinement) : IO goalstack := do
  let l ← currentGoalstack.get
  match l with
  | [] => throw (IO.userError "No current goal")
  | h :: _ =>
    match ← r h with
    | .error e => throw (IO.userError e)
    | .ok res => currentGoalstack.set (res :: l); currentGoalstack.get

/-- Apply a tactic to the head subgoal (`e tac = refine (by (VALID tac))`). -/
unsafe def e (tac : tactic) : IO goalstack := refine (Tactics.by_ B (VALID tac))

/-- Rotate the goalstack by `n`. -/
unsafe def r (n : Int) : IO goalstack := refine (Tactics.rotate n)

/-- `flush_goalstack()`: keep only the newest goalstate. -/
def flush_goalstack : IO Unit := do
  match ← currentGoalstack.get with
  | h :: _ => currentGoalstack.set [h]
  | [] => throw (IO.userError "hd")

/-- `er tac`: a sequence of `e tac; r n` where n is the number of subgoals
    after `e tac`.  This command is useful when you want to interactively try
    a list of tactics after THENL, e.g., `TAC THENL [ TAC_A; TAC_B; .. ]`:
    `e TAC;; er TAC_A;;` will execute TAC, execute TAC_A, then switch to the
    second subgoal of `e TAC`, which will be the input goalstate of TAC_B. -/
unsafe def er (tac : tactic) : IO goalstack := do
  let e_result ← e tac
  let (n_subgoals_to_rotate, n_subgoals) ←
    match ← currentGoalstack.get with
    | (_, gl, _) :: (_, glprev, _) :: _ =>
      let n_subgoals := gl.length
      if n_subgoals == 0 then pure ((0 : Int), 0)
      else pure (((n_subgoals : Int) - glprev.length + 1), n_subgoals)
    | _ => throw (IO.userError "current_goalstack must have at least 2 items after 'e'")
  if n_subgoals_to_rotate == 0 || n_subgoals == 1 then
    HolCore.Lib.remark "(Rotating zero subgoal)\n\n"
    return e_result
  else
    if ← HolCore.Lib.verbose.get then print_goalstack (← currentGoalstack.get)
    HolCore.Lib.remark s!"\n(Rotating {n_subgoals_to_rotate} subgoal{if n_subgoals_to_rotate == 1 then "" else "s"}...)\n\n"
    let new_g ← r n_subgoals_to_rotate
    -- pop the latest subgoal so that one b() can fully roll back the state
    let cur_gs ← currentGoalstack.get
    currentGoalstack.set (cur_gs.head! :: cur_gs.tail.tail)
    return new_g

/-- Set the current goal from assumptions and a conclusion. -/
unsafe def set_goal (asl : List term) (w : term) : IO goalstack := do
  let asl' ← asl.mapM (fun t => match ASSUME t with
    | .ok th => pure ("", th)
    | .error e => throw (IO.userError e))
  match mk_goalstate (asl', w) with
  | .error err => throw (IO.userError err)
  | .ok gs => currentGoalstack.set [gs]; currentGoalstack.get

/-- Start a new goal (no assumptions), warning about its free variables. -/
unsafe def g (t : term) : IO goalstack := do
  let fvs := HolCore.Lib.sort (fun a b => a < b) ((frees t).map (fun v => (dest_var v).toOption.map Prod.fst |>.getD ""))
  if fvs != [] then
    HolCore.Lib.warn true ("Free variables in goal: " ++ ", ".intercalate fvs)
  set_goal [] t

/-- Back up one step in the goalstack. -/
def b : IO goalstack := do
  let l ← currentGoalstack.get
  if l.length == 1 then throw (IO.userError "Can't back up any more")
  else currentGoalstack.set l.tail; currentGoalstack.get

/-- The current goalstack. -/
def p : IO goalstack := currentGoalstack.get

/-- The current top subgoal (assumptions as theorems, conclusion). -/
def top_realgoal : IO goal := do
  match ← currentGoalstack.get with
  | (_, (gl :: _), _) :: _ => pure gl
  | _ => throw (IO.userError "top_realgoal: no goal")

/-- The current top goal (assumption conclusions, conclusion). -/
unsafe def top_goal : IO (List term × term) := do
  let (asl, w) ← top_realgoal
  pure (asl.map (fun p => concl p.2), w)

/-- Extract the proved theorem once all subgoals are closed. -/
unsafe def top_thm : IO thm := do
  match ← currentGoalstack.get with
  | (_, [], f) :: _ =>
    match ← f null_inst [] with
    | .ok th => pure th
    | .error e => throw (IO.userError e)
  | _ => throw (IO.userError "top_thm: unsolved goals")

/- Itab: intuitionistic tableau prover. -/
unsafe def UNIFY_REFL_TAC := Itab.UNIFY_REFL_TAC B
unsafe def ITAUT_TAC := Itab.ITAUT_TAC_MAIN B
unsafe def ITAUT := Itab.ITAUT B
export Itab (UNIFY_ACCEPT_TAC)

/- Simp: rewriting and simplification. B-closed aliases. -/
unsafe def REWR_CONV := Simp.REWR_CONV B
unsafe def IMP_REWR_CONV := Simp.IMP_REWR_CONV B
unsafe def net_of_thm := Simp.net_of_thm B
unsafe def net_of_cong := Simp.net_of_cong B
unsafe def mk_rewrites := Simp.mk_rewrites B
unsafe def GEN_REWRITE_CONV := Simp.GEN_REWRITE_CONV' B
unsafe def PURE_REWRITE_CONV := Simp.PURE_REWRITE_CONV' B
unsafe def REWRITE_CONV := Simp.REWRITE_CONV' B
/-- `ORDERED_REWR_CONV ord th` (simp.ml 31): `REWR_CONV th`, failing unless
    the result `l = r` has `ord l r`. -/
unsafe def ORDERED_REWR_CONV := Simp.ORDERED_REWR_CONV B
unsafe def PURE_ONCE_REWRITE_CONV := Simp.PURE_ONCE_REWRITE_CONV' B
unsafe def ONCE_REWRITE_CONV := Simp.ONCE_REWRITE_CONV' B
unsafe def REWRITE_RULE := Simp.REWRITE_RULE B
unsafe def PURE_REWRITE_RULE := Simp.PURE_REWRITE_RULE B
unsafe def GEN_REWRITE_RULE := Simp.GEN_REWRITE_RULE B
unsafe def ONCE_REWRITE_RULE := Simp.ONCE_REWRITE_RULE B
unsafe def PURE_ONCE_REWRITE_RULE := Simp.PURE_ONCE_REWRITE_RULE B
unsafe def ASM_REWRITE_RULE := Simp.ASM_REWRITE_RULE B
unsafe def PURE_ASM_REWRITE_RULE := Simp.PURE_ASM_REWRITE_RULE B
unsafe def PURE_ONCE_ASM_REWRITE_RULE := Simp.PURE_ONCE_ASM_REWRITE_RULE B
unsafe def ONCE_ASM_REWRITE_RULE := Simp.ONCE_ASM_REWRITE_RULE B
unsafe def REWRITE_TAC := Simp.REWRITE_TAC B
unsafe def PURE_REWRITE_TAC := Simp.PURE_REWRITE_TAC B
unsafe def ONCE_REWRITE_TAC := Simp.ONCE_REWRITE_TAC B
unsafe def GEN_REWRITE_TAC := Simp.GEN_REWRITE_TAC B
unsafe def PURE_ONCE_REWRITE_TAC := Simp.PURE_ONCE_REWRITE_TAC B
unsafe def ASM_REWRITE_TAC := Simp.ASM_REWRITE_TAC B
unsafe def PURE_ASM_REWRITE_TAC := Simp.PURE_ASM_REWRITE_TAC B
unsafe def ONCE_ASM_REWRITE_TAC := Simp.ONCE_ASM_REWRITE_TAC B
unsafe def SIMP_CONV := Simp.SIMP_CONV' B
unsafe def PURE_SIMP_CONV := Simp.PURE_SIMP_CONV' B
unsafe def ONCE_SIMP_CONV := Simp.ONCE_SIMP_CONV' B
unsafe def SIMP_RULE := Simp.SIMP_RULE B
unsafe def PURE_SIMP_RULE := Simp.PURE_SIMP_RULE B
unsafe def ONCE_SIMP_RULE := Simp.ONCE_SIMP_RULE B
unsafe def SIMP_TAC := Simp.SIMP_TAC B
unsafe def PURE_SIMP_TAC := Simp.PURE_SIMP_TAC B
unsafe def ONCE_SIMP_TAC := Simp.ONCE_SIMP_TAC B
unsafe def ASM_SIMP_TAC := Simp.ASM_SIMP_TAC B
unsafe def PURE_ASM_SIMP_TAC := Simp.PURE_ASM_SIMP_TAC B
unsafe def ONCE_ASM_SIMP_TAC := Simp.ONCE_ASM_SIMP_TAC B
unsafe def empty_ss := Simp.empty_ss B
/-- `ss_of_thms thms ss` (simp.ml 240): add rewrites to a simpset. -/
unsafe def ss_of_thms := Simp.ss_of_thms B
/-- `ss_of_conv keytm conv ss` (simp.ml 245): add a conversion to a simpset. -/
def ss_of_conv := Simp.ss_of_conv
unsafe def basic_ss := Simp.basic_ss B
unsafe def set_basic_rewrites := Simp.set_basic_rewrites B
unsafe def extend_basic_rewrites := Simp.extend_basic_rewrites B
def basic_rewrites := Simp.basic_rewrites
unsafe def set_basic_convs := Simp.set_basic_convs B
unsafe def extend_basic_convs := Simp.extend_basic_convs B
def basic_convs := Simp.basic_convs
def basic_net := Simp.basic_net
def set_basic_congs := Simp.set_basic_congs
def extend_basic_congs := Simp.extend_basic_congs
def basic_congs := Simp.basic_congs
unsafe def AUGMENT_SIMPSET := Simp.AUGMENT_SIMPSET B
unsafe def ABBREV_TAC := Simp.ABBREV_TAC B
unsafe def EXPAND_TAC := Simp.EXPAND_TAC B
export Simp (gconv term_order REWRITES_CONV net_of_conv ss_of_thms ss_of_conv
  ss_of_congs ss_of_prover ss_of_provers ss_of_maker mk_prover augment apply_prover
  ONCE_DEPTH_SQCONV DEPTH_SQCONV REDEPTH_SQCONV TOP_DEPTH_SQCONV TOP_SWEEP_SQCONV)

/- theorems.ml: the standard logical theorems (proved once via `setupTheorems`,
   read from the `T` cache). -/
unsafe def EQ_REFL := T.EQ_REFL
unsafe def REFL_CLAUSE := T.REFL_CLAUSE
/-- `AC acsuite` (theorems.ml): prove an equation between terms equal up to
    the associativity and commutativity given by `acsuite`. -/
unsafe def AC (acsuite : thm) (tm : term) : IO (Except String thm) :=
  Theorems.AC B T.REFL_CLAUSE acsuite tm
unsafe def EQ_SYM := T.EQ_SYM
unsafe def EQ_SYM_EQ := T.EQ_SYM_EQ
unsafe def EQ_TRANS := T.EQ_TRANS
unsafe def BETA_THM := T.BETA_THM
unsafe def ABS_SIMP := T.ABS_SIMP
unsafe def CONJ_ASSOC := T.CONJ_ASSOC
unsafe def CONJ_SYM := T.CONJ_SYM
unsafe def CONJ_ACI := T.CONJ_ACI
unsafe def DISJ_ASSOC := T.DISJ_ASSOC
unsafe def DISJ_SYM := T.DISJ_SYM
unsafe def DISJ_ACI := T.DISJ_ACI
unsafe def IMP_CONJ := T.IMP_CONJ
unsafe def IMP_IMP := T.IMP_IMP
unsafe def IMP_CONJ_ALT := T.IMP_CONJ_ALT
unsafe def LEFT_OR_DISTRIB := T.LEFT_OR_DISTRIB
unsafe def RIGHT_OR_DISTRIB := T.RIGHT_OR_DISTRIB
unsafe def FORALL_SIMP := T.FORALL_SIMP
unsafe def EXISTS_SIMP := T.EXISTS_SIMP
unsafe def EQ_IMP := T.EQ_IMP
unsafe def EQ_CLAUSES := T.EQ_CLAUSES
unsafe def NOT_CLAUSES_WEAK := T.NOT_CLAUSES_WEAK
unsafe def AND_CLAUSES := T.AND_CLAUSES
unsafe def OR_CLAUSES := T.OR_CLAUSES
unsafe def IMP_CLAUSES := T.IMP_CLAUSES
unsafe def EXISTS_UNIQUE_THM := T.EXISTS_UNIQUE_THM
unsafe def EXISTS_REFL := T.EXISTS_REFL
unsafe def EXISTS_UNIQUE_REFL := T.EXISTS_UNIQUE_REFL
unsafe def UNWIND_THM1 := T.UNWIND_THM1
unsafe def UNWIND_THM2 := T.UNWIND_THM2
unsafe def FORALL_UNWIND_THM2 := T.FORALL_UNWIND_THM2
unsafe def FORALL_UNWIND_THM1 := T.FORALL_UNWIND_THM1
unsafe def SWAP_FORALL_THM := T.SWAP_FORALL_THM
unsafe def SWAP_EXISTS_THM := T.SWAP_EXISTS_THM
unsafe def FORALL_AND_THM := T.FORALL_AND_THM
unsafe def AND_FORALL_THM := T.AND_FORALL_THM
unsafe def LEFT_AND_FORALL_THM := T.LEFT_AND_FORALL_THM
unsafe def RIGHT_AND_FORALL_THM := T.RIGHT_AND_FORALL_THM
unsafe def EXISTS_OR_THM := T.EXISTS_OR_THM
unsafe def OR_EXISTS_THM := T.OR_EXISTS_THM
unsafe def LEFT_OR_EXISTS_THM := T.LEFT_OR_EXISTS_THM
unsafe def RIGHT_OR_EXISTS_THM := T.RIGHT_OR_EXISTS_THM
unsafe def LEFT_EXISTS_AND_THM := T.LEFT_EXISTS_AND_THM
unsafe def RIGHT_EXISTS_AND_THM := T.RIGHT_EXISTS_AND_THM
unsafe def TRIV_EXISTS_AND_THM := T.TRIV_EXISTS_AND_THM
unsafe def LEFT_AND_EXISTS_THM := T.LEFT_AND_EXISTS_THM
unsafe def RIGHT_AND_EXISTS_THM := T.RIGHT_AND_EXISTS_THM
unsafe def TRIV_AND_EXISTS_THM := T.TRIV_AND_EXISTS_THM
unsafe def TRIV_FORALL_OR_THM := T.TRIV_FORALL_OR_THM
unsafe def TRIV_OR_FORALL_THM := T.TRIV_OR_FORALL_THM
unsafe def RIGHT_IMP_FORALL_THM := T.RIGHT_IMP_FORALL_THM
unsafe def RIGHT_FORALL_IMP_THM := T.RIGHT_FORALL_IMP_THM
unsafe def LEFT_IMP_EXISTS_THM := T.LEFT_IMP_EXISTS_THM
unsafe def LEFT_FORALL_IMP_THM := T.LEFT_FORALL_IMP_THM
unsafe def TRIV_FORALL_IMP_THM := T.TRIV_FORALL_IMP_THM
unsafe def TRIV_EXISTS_IMP_THM := T.TRIV_EXISTS_IMP_THM
unsafe def MONO_AND := T.MONO_AND
unsafe def MONO_OR := T.MONO_OR
unsafe def MONO_IMP := T.MONO_IMP
unsafe def MONO_NOT := T.MONO_NOT
unsafe def MONO_FORALL := T.MONO_FORALL
unsafe def MONO_EXISTS := T.MONO_EXISTS
unsafe def WLOG_RELATION := T.WLOG_RELATION
unsafe def EXISTS_UNIQUE_ALT := T.EXISTS_UNIQUE_ALT
unsafe def EXISTS_UNIQUE := T.EXISTS_UNIQUE

/- The theorems.ml Part B tactic DSL: DESTRUCT_TAC / FIX_TAC / INTRO_TAC /
   HYP_TAC / CLAIM_TAC, closed over B and the three quantifier-commuting
   theorems `fix_tac` needs. -/
private unsafe def DSL : DSLThms :=
  setupTacticDSL B T.SWAP_FORALL_THM T.AND_FORALL_THM T.RIGHT_IMP_FORALL_THM

unsafe def DESTRUCT_TAC := DSL.DESTRUCT_TAC
unsafe def FIX_TAC      := DSL.FIX_TAC
unsafe def INTRO_TAC    := DSL.INTRO_TAC
unsafe def HYP_TAC      := DSL.HYP_TAC
unsafe def CLAIM_TAC    := DSL.CLAIM_TAC

/- ---------------------------------------------------------------------- -/
/- ind_defs.ml: inductive-definitions package                             -/
/- ---------------------------------------------------------------------- -/

/-- Registry of inductive definitions (rule, induct, cases). -/
initialize theInductiveDefinitions : IO.Ref (List (thm × thm × thm)) ← IO.mkRef []

/-- The default monotonicity theorems (mutable, as in HOL Light). -/
initialize theMonotonicityTheorems : IO.Ref (Option (List thm)) ← IO.mkRef none

/-- Cache for `ind_defs` auxiliaries computed once: the `EXISTS_EQUATION` `pth`,
    `IMP_REFL = ITAUT !p. p ==> p`, and the term `T`. -/
initialize theIndAux : IO.Ref (Option (thm × thm × term)) ← IO.mkRef none

private unsafe def indAux : thm × thm × term :=
  match unsafeIO (do
    match ← theIndAux.get with
    | some x => pure x
    | none =>
      let pth ← (match ← (EXISTS_EQUATION_pth B).run with
                 | .ok t => pure t | .error e => panic! s!"EXISTS_EQUATION_pth: {e}")
      let impRefl ← (match ← Itab.ITAUT B (← (match ← Parser.parse_term "!p. p ==> p" with
                        | .ok t => pure t | .error e => panic! s!"IMP_REFL parse: {e}")) with
                     | .ok t => pure t | .error e => panic! s!"IMP_REFL: {e}")
      let tTm ← (match ← Parser.parse_term "T" with
                 | .ok t => pure t | .error e => panic! s!"t_tm parse: {e}")
      let x := (pth, impRefl, tTm)
      theIndAux.set (some x); pure x) with
  | .ok x => x
  | _ => panic! "Session.indAux: not initialised"

/-- The current monotonicity theorems, RE-READ on every use.  OCaml dereferences
    `!monotonicity_theorems` inside `MONO_TAC`'s `fun gl -> ...`, and `class.ml`
    later does `monotonicity_theorems := MONO_COND::(!monotonicity_theorems)`
    (as `lists.ml` does for `MONO_ALL`/`MONO_ALL2`), so the list must NOT be
    captured once: a frozen snapshot would permanently lose those additions. -/
private unsafe def monoThmsIO : IO (List thm) := do
  match ← theMonotonicityTheorems.get with
  | some l => pure l
  | none =>
    let l := [T.MONO_AND, T.MONO_OR, T.MONO_IMP, T.MONO_NOT, T.MONO_EXISTS, T.MONO_FORALL]
    theMonotonicityTheorems.set (some l); pure l

/-- `!monotonicity_theorems` (ind_defs.ml 248). -/
unsafe def get_monotonicity_theorems : IO (List thm) := monoThmsIO
/-- `monotonicity_theorems := l`. -/
def set_monotonicity_theorems (l : List thm) : IO Unit := theMonotonicityTheorems.set (some l)

/-- `EXISTS_EQUATION tm th`. -/
unsafe def EXISTS_EQUATION (tm : term) (th : thm) : Except String thm :=
  IndDefs.EXISTS_EQUATION B indAux.1 tm th

/-- `derive_nonschematic_inductive_relations tm`. -/
unsafe def derive_nonschematic_inductive_relations (tm : term) : IO (Except String thm) :=
  IndDefs.derive_nonschematic_inductive_relations B T.REFL_CLAUSE T.CONJ_ACI indAux.2.2 tm

/-- Monotonicity tactic, using the current `theMonotonicityTheorems` (re-read on
    every invocation, as OCaml's `fun gl -> ... !monotonicity_theorems ...`). -/
unsafe def MONO_TAC : tactic := fun g => do
  IndDefs.MONO_TAC B (← monoThmsIO) indAux.2.1 g

/-- Prove/discharge the monotonicity hypotheses of `th`. -/
unsafe def prove_monotonicity_hyps (th : thm) : IO (Except String thm) := do
  IndDefs.prove_monotonicity_hyps B (← monoThmsIO) indAux.2.1 th

/-- Prove that relations satisfying the inductive clauses exist. -/
unsafe def prove_inductive_relations_exist (tm : term) : IO (Except String thm) :=
  do IndDefs.prove_inductive_relations_exist B indAux.1 T.REFL_CLAUSE T.CONJ_ACI indAux.2.2
       (← monoThmsIO) indAux.2.1 tm

/-- Derive strong induction from a rule/induction pair. -/
unsafe def derive_strong_induction (rth ith : thm) : IO (Except String thm) := do
  IndDefs.derive_strong_induction B T.MONO_AND (← monoThmsIO) indAux.2.1 rth ith

/-- `new_inductive_definition tm`: define a new inductive predicate, returning
    the (rule, induction, cases) triple; registers it in
    `theInductiveDefinitions` (benign redefinitions reuse the stored triple). -/
unsafe def new_inductive_definition (tm : term) : IO (Except String (thm × thm × thm)) := do
  let existing ← theInductiveDefinitions.get
  match ← (IndDefs.new_inductive_definition_core B indAux.1 T.REFL_CLAUSE T.CONJ_ACI indAux.2.2
            (← monoThmsIO) indAux.2.1 existing tm : IO (Except String ((thm × thm × thm) × Option (thm × thm × thm)))) with
  | .error e => return .error e
  | .ok (trip, newEntry) =>
    match newEntry with
    | some entry => do theInductiveDefinitions.set (entry :: existing); return .ok trip
    | none => return .ok trip   -- benign redefinition: the core already warned

/- ---------------------------------------------------------------------- -/
/- class.ml: axioms and constants (kernel-state bootstrap)                -/
/- ---------------------------------------------------------------------- -/

/-- `ETA_AX : |- !t:A->B. (\x. t x) = t`. -/
initialize theEtaAx : IO.Ref (Option thm) ← IO.mkRef none
/-- `SELECT_AX : |- !P (x:A). P x ==> P ((@) P)`. -/
initialize theSelectAx : IO.Ref (Option thm) ← IO.mkRef none
/-- `COND_DEF : |- COND = \t t1 t2. @x. ...`. -/
initialize theCondDef : IO.Ref (Option thm) ← IO.mkRef none

initialize (do
  match ← theBool.get with
  | none => throw (IO.userError "class.ml bootstrap: setupBool not initialised")
  | some b =>
    -- ETA_AX
    match ← HolCore.Parser.parse_term "!t:A->B. (\\x. t x) = t" with
    | .error e => throw (IO.userError s!"ETA_AX parse: {e}")
    | .ok etaTm =>
      match ← Kernel.new_axiom etaTm with
      | .error e => throw (IO.userError s!"ETA_AX: {e}")
      | .ok th => theEtaAx.set (some th)
    -- @ (select) constant + binder
    match ← HolCore.Parser.parse_type "(A->bool)->A" with
    | .error e => throw (IO.userError s!"@ type parse: {e}")
    | .ok selTy =>
      match ← Kernel.new_constant "@" selTy with
      | .error e => throw (IO.userError s!"new_constant @: {e}")
      | .ok _ => HolCore.Printer.parse_as_binder "@"
    -- SELECT_AX (needs @ declared + parsed as binder)
    match ← HolCore.Parser.parse_term "!P (x:A). P x ==> P ((@) P)" with
    | .error e => throw (IO.userError s!"SELECT_AX parse: {e}")
    | .ok selTm =>
      match ← Kernel.new_axiom selTm with
      | .error e => throw (IO.userError s!"SELECT_AX: {e}")
      | .ok th => theSelectAx.set (some th)
    -- COND_DEF
    match ← HolCore.Parser.parse_term
        "COND = \\t t1 t2. @x:A. ((t <=> T) ==> (x = t1)) /\\ ((t <=> F) ==> (x = t2))" with
    | .error e => throw (IO.userError s!"COND_DEF parse: {e}")
    | .ok condTm =>
      match ← Drule.new_definition b condTm with
      | .error e => throw (IO.userError s!"COND_DEF: {e}")
      | .ok th => theCondDef.set (some th))

unsafe def ETA_AX : thm :=
  match unsafeIO theEtaAx.get with | .ok (some t) => t | _ => panic! "Session.ETA_AX: not initialised"
unsafe def SELECT_AX : thm :=
  match unsafeIO theSelectAx.get with | .ok (some t) => t | _ => panic! "Session.SELECT_AX: not initialised"
unsafe def COND_DEF : thm :=
  match unsafeIO theCondDef.get with | .ok (some t) => t | _ => panic! "Session.COND_DEF: not initialised"

/- ---------------------------------------------------------------------- -/
/- trivia.ml: combinator definitions (o, I)                               -/
/- ---------------------------------------------------------------------- -/

initialize theODef : IO.Ref (Option thm) ← IO.mkRef none
initialize theIDef : IO.Ref (Option thm) ← IO.mkRef none

initialize (do
  match ← theBool.get with
  | none => throw (IO.userError "trivia.ml bootstrap: setupBool not initialised")
  | some b =>
    HolCore.Printer.parse_as_infix ("o", (26, "right"))
    match ← HolCore.Parser.parse_term "(o) (f:B->C) g = \\x:A. f(g(x))" with
    | .error e => throw (IO.userError s!"o_DEF parse: {e}")
    | .ok oTm =>
      match ← Drule.new_definition b oTm with
      | .error e => throw (IO.userError s!"o_DEF: {e}")
      | .ok th => theODef.set (some th)
    match ← HolCore.Parser.parse_term "I = \\x:A. x" with
    | .error e => throw (IO.userError s!"I_DEF parse: {e}")
    | .ok iTm =>
      match ← Drule.new_definition b iTm with
      | .error e => throw (IO.userError s!"I_DEF: {e}")
      | .ok th => theIDef.set (some th))

unsafe def o_DEF : thm :=
  match unsafeIO theODef.get with | .ok (some t) => t | _ => panic! "Session.o_DEF: not initialised"
unsafe def I_DEF : thm :=
  match unsafeIO theIDef.get with | .ok (some t) => t | _ => panic! "Session.I_DEF: not initialised"

/-- Cache for the `class.ml` theorem layer (proved once by `setupClass`). -/
initialize theClass : IO.Ref (Option ClassThms) ← IO.mkRef none

/-- theorems.ml and class.ml run EAGERLY at load, as hol_lib.ml `loads` them.

    Both files mutate the global rewrite state at load: theorems.ml 159/174
    `extend_basic_rewrites`/`extend_basic_congs`, class.ml 113/195/340/468/473
    (`SELECT_REFL`, `~T <=> F`, `COND_CLAUSES`, `COND_CONG`, `COND_EQ_CLAUSE`).
    Left lazy, those only happened when a test first READ a theorem from the
    layer, so `REWRITE_CONV []` on `if T then a else b` returned the term
    UNCHANGED in a fresh process - HOL Light gives `|- ... <=> a`.  Forcing
    these two layers costs under a second, unlike the ~90 s math library (still
    lazy by design, see HolInit.lean).  The caches are filled here directly, so
    the lazy readers `T`/`C` simply find them; the monotonicity registration
    (class.ml 393) is done here too, as `C` would. -/
initialize (do
  -- Run quietly.  Lean attaches output printed while a module's imports
  -- initialise to the message of EVERY later `#eval` in that module, so the
  -- ~190-line ITAUT/MESON trace these proofs print under HOL Light's defaults
  -- would be repeated for each `#eval`.  The flags are restored afterwards.
  let verb ← HolCore.Lib.verbose.get
  let tiw ← HolCore.Preterm.type_invention_warning.get
  HolCore.Lib.verbose.set false
  HolCore.Preterm.type_invention_warning.set false
  match ← theBool.get, ← theEtaAx.get, ← theSelectAx.get, ← theCondDef.get with
  | some b, some eta, some sel, some cond =>
    let t ← match ← (setupTheorems b).run with
      | .ok t => pure t
      | .error e => throw (IO.userError s!"setupTheorems failed: {e}")
    theTheorems.set (some t)
    match ← (setupClass b t eta sel cond).run with
    | .ok c =>
      theClass.set (some c)
      let base := [t.MONO_AND, t.MONO_OR, t.MONO_IMP, t.MONO_NOT, t.MONO_EXISTS, t.MONO_FORALL]
      theMonotonicityTheorems.set (some (c.MONO_COND :: ((← theMonotonicityTheorems.get).getD base)))
    | .error e => throw (IO.userError s!"setupClass failed: {e}")
  | _, _, _, _ => throw (IO.userError "theorems/class bootstrap: kernel axioms not initialised")
  HolCore.Lib.verbose.set verb
  HolCore.Preterm.type_invention_warning.set tiw)

/-- The established `class.ml` layer; computes and caches on first access. -/
private unsafe def C : ClassThms :=
  match unsafeIO (do
    match ← theClass.get with
    | some c => pure c
    | none =>
      match ← (setupClass B T ETA_AX SELECT_AX COND_DEF).run with
      | .ok c => do
          theClass.set (some c)
          -- monotonicity_theorems := MONO_COND :: (!monotonicity_theorems)
          let cur ← theMonotonicityTheorems.get
          let base := cur.getD [T.MONO_AND, T.MONO_OR, T.MONO_IMP, T.MONO_NOT, T.MONO_EXISTS, T.MONO_FORALL]
          theMonotonicityTheorems.set (some (c.MONO_COND :: base))
          pure c
      | .error e => panic! s!"setupClass failed: {e}") with
  | .ok c => c
  | _ => panic! "Session.C: setupClass not run"

/-- The Bool, Class and Theorem bundles (`B`, `C`, `T`, private above), for
    the `SessionLibrary` wiring, which passes them to the pure `HolLibrary`
    files as HolMath's setup functions receive them here. -/
unsafe def sessionB : BoolThms := B
unsafe def sessionC : ClassThms := C
unsafe def sessionT : TheoremThms := T

/-- The core bundles for the HolMath setups written against HolLight.Base. -/
private unsafe instance sessionHolBase : HolLight.HolBase := ⟨B, C, T⟩

/-- Expose class.ml theorems. -/
unsafe def EQ_EXT := C.EQ_EXT
unsafe def FUN_EQ_THM := C.FUN_EQ_THM
unsafe def EXISTS_THM := C.EXISTS_THM
unsafe def SELECT_REFL := C.SELECT_REFL
unsafe def SELECT_UNIQUE := C.SELECT_UNIQUE
unsafe def EXCLUDED_MIDDLE := C.EXCLUDED_MIDDLE
unsafe def BOOL_CASES_AX := C.BOOL_CASES_AX
unsafe def BOOL_CASES_TAC (p : term) : tactic := Classic.BOOL_CASES_TAC B C.BOOL_CASES_AX p
unsafe def ASM_CASES_TAC (t : term) : tactic := Classic.ASM_CASES_TAC B C.EXCLUDED_MIDDLE t
unsafe def TAUT (tm : term) : IO (Except String thm) := Classic.TAUT B C.BOOL_CASES_AX tm
unsafe def DE_MORGAN_THM := C.DE_MORGAN_THM
unsafe def NOT_CLAUSES := C.NOT_CLAUSES
unsafe def NOT_IMP := C.NOT_IMP
unsafe def CONTRAPOS_THM := C.CONTRAPOS_THM
unsafe def NOT_EXISTS_THM := C.NOT_EXISTS_THM
unsafe def EXISTS_NOT_THM := C.EXISTS_NOT_THM
unsafe def NOT_FORALL_THM := C.NOT_FORALL_THM
unsafe def FORALL_NOT_THM := C.FORALL_NOT_THM
unsafe def FORALL_BOOL_THM := C.FORALL_BOOL_THM
unsafe def EXISTS_BOOL_THM := C.EXISTS_BOOL_THM
/- These fixed proforma variables need no parser state, so they are built
   directly and stay PURE (verified identical to parsing "P:bool" etc.). -/
private def boolP  : term := mk_var "P" bool_ty
unsafe def CCONTR (tm : term) (th : thm) : Except String thm :=
  Classic.CCONTR B C.ccontrPth boolP tm th
unsafe def CONTRAPOS_CONV (tm : term) : Except String thm :=
  Classic.CONTRAPOS_CONV C.contraposConvPth C.contraposA C.contraposB tm
unsafe def LEFT_FORALL_OR_THM := C.LEFT_FORALL_OR_THM
unsafe def RIGHT_FORALL_OR_THM := C.RIGHT_FORALL_OR_THM
unsafe def LEFT_OR_FORALL_THM := C.LEFT_OR_FORALL_THM
unsafe def RIGHT_OR_FORALL_THM := C.RIGHT_OR_FORALL_THM
unsafe def LEFT_IMP_FORALL_THM := C.LEFT_IMP_FORALL_THM
unsafe def LEFT_EXISTS_IMP_THM := C.LEFT_EXISTS_IMP_THM
unsafe def RIGHT_IMP_EXISTS_THM := C.RIGHT_IMP_EXISTS_THM
unsafe def RIGHT_EXISTS_IMP_THM := C.RIGHT_EXISTS_IMP_THM
unsafe def COND_CLAUSES := C.COND_CLAUSES
unsafe def COND_EXPAND := C.COND_EXPAND
unsafe def COND_ID := C.COND_ID
unsafe def COND_RAND := C.COND_RAND
unsafe def COND_RATOR := C.COND_RATOR
unsafe def COND_ABS := C.COND_ABS
unsafe def COND_SWAP := C.COND_SWAP
unsafe def MONO_COND := C.MONO_COND
unsafe def COND_ELIM_THM := C.COND_ELIM_THM
unsafe def COND_ELIM_CONV : term → IO (Except String thm) := Classic.COND_ELIM_CONV B C.COND_ELIM_THM
unsafe def COND_CASES_TAC : tactic := Classic.COND_CASES_TAC B C.COND_ELIM_THM C.denegPth
def is_cond := Classic.is_cond
def mk_cond := Classic.mk_cond
def dest_cond := Classic.dest_cond
unsafe def SKOLEM_THM := C.SKOLEM_THM
unsafe def SKOLEM_THM_GEN := C.SKOLEM_THM_GEN
unsafe def UNIQUE_SKOLEM_ALT := C.UNIQUE_SKOLEM_ALT
unsafe def UNIQUE_SKOLEM_THM := C.UNIQUE_SKOLEM_THM
unsafe def COND_CONG := C.COND_CONG
unsafe def COND_EQ_CLAUSE := C.COND_EQ_CLAUSE
unsafe def bool_INDUCT := C.bool_INDUCT
unsafe def bool_RECURSION := C.bool_RECURSION
/-- SELECT_RULE / SELECT_CONV closed over their `pth` and `P = P:A->bool`. -/
private def selP : term := mk_var "P" (.Tyapp "fun" [aty, bool_ty])
unsafe def SELECT_RULE (th : thm) : Except String thm :=
  Classic.SELECT_RULE B C.selectRulePth selP th
unsafe def SELECT_CONV (tm : term) : Except String thm :=
  Classic.SELECT_CONV C.selectConvPth selP tm
unsafe def ETA_CONV (tm : term) : Except String thm :=
  Classic.ETA_CONV C.etaPth C.etaT tm

/-- `REFUTE_THEN ttac`: classical refutation tactic. -/
unsafe def REFUTE_THEN (ttac : thm_tactic) : tactic :=
  Classic.REFUTE_THEN B (Simp.REWR_CONV B C.refuteThenPth) C.refuteF ttac

/- ---------------------------------------------------------------------- -/
/- Now we can derive type definitions from existence; check benignity.    -/
/- (class.ml 116)                                                         -/
/- ---------------------------------------------------------------------- -/

/-- Registry of type definitions made via `new_type_definition`. -/
initialize theTypeDefinitions :
    IO.Ref (List ((String × String × String) × (thm × thm))) ← IO.mkRef []

/-- Registry of inductive types (name → arity, induction, recursion); seeded `bool`. -/
initialize theInductiveTypeStore : IO.Ref (Option (List (String × (Int × thm × thm)))) ← IO.mkRef none

/-- `!inductive_type_store` (class.ml 489): read the live store, so types
    added by `define_type` are seen. -/
unsafe def get_inductive_type_store : IO (List (String × (Int × thm × thm))) := do
  match ← theInductiveTypeStore.get with
  | some l => pure l
  | none => pure [("bool", (2, C.bool_INDUCT, C.bool_RECURSION))]
/-- `inductive_type_store := l`. -/
def set_inductive_type_store (l : List (String × (Int × thm × thm))) : IO Unit :=
  theInductiveTypeStore.set (some l)

/-- `new_type_definition tyname (absname, repname) th`: derive a type definition
    from an existence theorem `th : ?x. P x`, returning the abs/rep theorems. -/
unsafe def new_type_definition (tyname absname repname : String) (th : thm) :
    IO (Except String thm) := do
  let existing ← theTypeDefinitions.get
  -- OCaml's `failwith ""` on a conclusion mismatch is raised INSIDE the
  -- surrounding `try ... with Failure _ ->`, so it is caught and the type is
  -- defined afresh; only a cache hit whose conclusion AGREES is a benign
  -- redefinition that reuses the stored theorems.
  let cached : Option thm :=
    match HolCore.Lib.assoc (tyname, absname, repname) existing with
    | .ok (th', tth') => if concl th' == concl th then some tth' else none
    | .error _ => none
  match cached with
  | some tth' => do
      HolCore.Lib.warn true "Benign redefinition of type"
      return .ok tth'
  | none =>
    let conv : ioconv := Simp.thencIO (Simp.ratorConvIO (Simp.REWR_CONV B C.EXISTS_THM))
                          (fun t => pure (BETA_CONV t))
    match ← (Simp.convRuleIO conv th : IO (Except String thm)) with
    | .error e => return .error e
    | .ok th0 =>
      match ← (Kernel.new_basic_type_definition tyname absname repname th0
                : IO (Except String (thm × thm))) with
      | .error e => return .error e
      | .ok (th1, th2) =>
        match (do
          let g1 ← B.GEN_ALL th1
          let th2' ← CONV_RULE (LAND_CONV (TRY_CONV BETA_CONV)) th2
          let g2 ← B.GEN_ALL th2'
          B.CONJ g1 g2 : Except String thm) with
        | .error e => return .error e
        | .ok tth => do
          theTypeDefinitions.set (((tyname, absname, repname), (th, tth)) :: existing)
          return .ok tth

/- ---------------------------------------------------------------------- -/
/- trivia.ml: the one-element type `1` (stateful; lazy via unsafeIO)      -/
/- ---------------------------------------------------------------------- -/

/-- Cache for `(EXISTS_ONE_REP, one_tydef, one_DEF)`, computed once. -/
initialize theOneAux : IO.Ref (Option (thm × thm × thm)) ← IO.mkRef none

private unsafe def oneAux : thm × thm × thm :=
  match unsafeIO (do
    match ← theOneAux.get with
    | some x => pure x
    | none =>
      let goal ← (match ← HolCore.Parser.parse_term "?b:bool. b" with
                  | .ok t => pure t | .error e => panic! s!"EXISTS_ONE_REP goal: {e}")
      let tW ← (match ← HolCore.Parser.parse_term "T" with
                | .ok t => pure t | .error e => panic! s!"T: {e}")
      let existsOneRep ← (match ← (Tactics.prove B goal
            (Tactics.THEN B (Tactics.EXISTS_TAC B tW)
              (Tactics.THEN B (Tactics.BETA_TAC B) (Tactics.ACCEPT_TAC B B.TRUTH)))
            : IO (Except String thm)) with
        | .ok t => pure t | .error e => panic! s!"EXISTS_ONE_REP: {e}")
      let oneTydef ← (match ← (new_type_definition "1" "one_ABS" "one_REP" existsOneRep
                                : IO (Except String thm)) with
        | .ok t => pure t | .error e => panic! s!"one_tydef: {e}")
      let oneDefTm ← (match ← HolCore.Parser.parse_term "one = @x:1. T" with
        | .ok t => pure t | .error e => panic! s!"one_DEF parse: {e}")
      let oneDef ← (match ← (Drule.new_definition B oneDefTm : IO (Except String thm)) with
        | .ok t => pure t | .error e => panic! s!"one_DEF: {e}")
      let x := (existsOneRep, oneTydef, oneDef)
      theOneAux.set (some x); pure x) with
  | .ok x => x | _ => panic! "Session.oneAux: not initialised"

/-- Cache for the `trivia.ml` theorem layer. -/
initialize theTrivia : IO.Ref (Option TriviaThms) ← IO.mkRef none

private unsafe def Tv : TriviaThms :=
  match unsafeIO (do
    match ← theTrivia.get with
    | some t => pure t
    | none =>
      match ← (setupTrivia B T C o_DEF I_DEF oneAux.1 oneAux.2.1 oneAux.2.2).run with
      | .ok t => do
          theTrivia.set (some t)
          -- Add the type "1" to the inductive type store.  (trivia.ml 101)
          -- inductive_type_store := ("1",(1,one_INDUCT,one_RECURSION)) :: (!...)
          let cur ← theInductiveTypeStore.get
          let base := cur.getD [("bool", (2, C.bool_INDUCT, C.bool_RECURSION))]
          theInductiveTypeStore.set (some (("1", (1, t.one_INDUCT, t.one_RECURSION)) :: base))
          pure t
      | .error e => panic! s!"setupTrivia failed: {e}") with
  | .ok t => t | _ => panic! "Session.Tv: setupTrivia not run"

unsafe def o_THM := Tv.o_THM
unsafe def o_ASSOC := Tv.o_ASSOC
unsafe def I_THM := Tv.I_THM
unsafe def I_O_ID := Tv.I_O_ID
unsafe def one_tydef : thm := oneAux.2.1
unsafe def one_DEF : thm := oneAux.2.2
unsafe def EXISTS_ONE_REP := Tv.EXISTS_ONE_REP
unsafe def one := Tv.one
unsafe def one_axiom := Tv.one_axiom
unsafe def one_INDUCT := Tv.one_INDUCT
unsafe def one_RECURSION := Tv.one_RECURSION
unsafe def one_Axiom := Tv.one_Axiom
unsafe def FORALL_ONE_THM := Tv.FORALL_ONE_THM
unsafe def EXISTS_ONE_THM := Tv.EXISTS_ONE_THM
unsafe def ETA_ONE := Tv.ETA_ONE

/- ---------------------------------------------------------------------- -/
/- canon.ml conversions (canonical forms for MESON)                       -/
/- ---------------------------------------------------------------------- -/

/-- Cache for the full `canon.ml` auxiliary bundle. -/
initialize theCanon : IO.Ref (Option Canon.CanonThms) ← IO.mkRef none

private unsafe def Cn : Canon.CanonThms :=
  match unsafeIO (do
    match ← theCanon.get with
    | some k => pure k
    | none =>
      let propsimps ← Simp.basic_net
      match ← (Canon.setupCanon B T C ETA_AX SELECT_AX I_THM propsimps).run with
      | .ok k => do theCanon.set (some k); pure k
      | .error e => panic! s!"setupCanon failed: {e}") with
  | .ok k => k | _ => panic! "Session.Cn: setupCanon not run"

unsafe def PRESIMP_CONV : term → IO (Except String thm) := Canon.PRESIMP_CONV B T C
unsafe def SKOLEM_CONV : term → IO (Except String thm) := Canon.SKOLEM_CONV B T C
unsafe def PRENEX_CONV : term → IO (Except String thm) := Canon.PRENEX_CONV B T C
unsafe def CONJ_CANON_CONV : term → IO (Except String thm) := Canon.CONJ_CANON_CONV B
unsafe def DISJ_CANON_CONV : term → IO (Except String thm) := Canon.disjCanonConv B Cn
unsafe def NNF_CONV : term → IO (Except String thm) := Canon.NNF_CONV B Cn.nnf
unsafe def NNFC_CONV : term → IO (Except String thm) := Canon.NNFC_CONV B Cn.nnf
unsafe def WEAK_DNF_CONV : term → IO (Except String thm) := Canon.weakDnfConv B Cn
unsafe def DNF_CONV : term → IO (Except String thm) := Canon.dnfConv B Cn
unsafe def WEAK_CNF_CONV : term → IO (Except String thm) := Canon.weakCnfConv B Cn
unsafe def CNF_CONV : term → IO (Except String thm) := Canon.cnfConv B Cn
unsafe def SELECT_ELIM_TAC : tactic := Canon.SELECT_ELIM_TAC B Cn.selLam
unsafe def LAMBDA_ELIM_CONV : term → IO (Except String thm) := Canon.LAMBDA_ELIM_CONV B Cn.selLam
unsafe def CONDS_ELIM_CONV : term → IO (Except String thm) := Canon.CONDS_ELIM_CONV B Cn.conds
unsafe def CONDS_CELIM_CONV : term → IO (Except String thm) := Canon.CONDS_CELIM_CONV B Cn.conds
unsafe def ASSOC_CONV (th : thm) : Except String (term → IO (Except String thm)) :=
  Canon.ASSOC_CONV B th
def PROP_ATOM_CONV : (term → IO (Except String thm)) → term → IO (Except String thm) :=
  Canon.PROP_ATOM_CONV
unsafe def ASM_FOL_TAC : tactic := Canon.ASM_FOL_TAC B Cn.fol

/- ---------------------------------------------------------------------- -/
/- meson.ml (MESON first-order automation)                                -/
/- ---------------------------------------------------------------------- -/

initialize theMeson : IO.Ref (Option Meson.MesonThms) ← IO.mkRef none
initialize mesonInferences : IO.Ref Int ← IO.mkRef 0
initialize mesonContraposCache : Meson.ContraposCache ← IO.mkRef []
initialize mesonVstore : IO.Ref (List (term × Int)) ← IO.mkRef []
initialize mesonGstore : IO.Ref (List (term × Int)) ← IO.mkRef []
initialize mesonVcounter : IO.Ref Int ← IO.mkRef 0
initialize mesonCstore : IO.Ref (List (term × Int)) ← IO.mkRef []
initialize mesonCcounter : IO.Ref Int ← IO.mkRef 2

/-- MESON's term↔code stores. -/
def MesonS : Meson.FolStores :=
  { vstore := mesonVstore, gstore := mesonGstore, vcounter := mesonVcounter,
    cstore := mesonCstore, ccounter := mesonCcounter }

/-- Cached MESON auxiliary theorems (pths + equality axioms + Brand). -/
private unsafe def Mn : Meson.MesonThms :=
  match unsafeIO (do
    match ← theMeson.get with
    | some m => pure m
    | none =>
      match ← (Meson.setupMeson B T C).run with
      | .ok m => do theMeson.set (some m); pure m
      | .error e => panic! s!"setupMeson failed: {e}") with
  | .ok m => m | _ => panic! "Session.Mn: setupMeson not run"

/-- The Canon-derived conversions/tactics that `GEN_MESON_TAC` chains. -/
private unsafe def MesonD : Meson.MesonTacDeps :=
  { presimp    := Canon.PRESIMP_CONV B T C
    nnf        := Canon.NNF_CONV B Cn.nnf
    skolem     := Canon.SKOLEM_CONV B T C
    prenex     := Canon.PRENEX_CONV B T C
    condsCelim := Canon.CONDS_CELIM_CONV B Cn.conds
    weakCnf    := Canon.weakCnfConv B Cn
    quantBool  := Meson.QUANT_BOOL_CONV B T C
    lambdaElim := Canon.LAMBDA_ELIM_CONV B Cn.selLam
    assocDisj  := (match Canon.ASSOC_CONV B T.DISJ_ASSOC with
                   | .ok c => c | .error e => panic! s!"ASSOC_CONV DISJ_ASSOC: {e}")
    selectElim := Canon.SELECT_ELIM_TAC B Cn.selLam
    asmFol     := Canon.ASM_FOL_TAC B Cn.fol
    refuteThen := fun ttac => Classic.REFUTE_THEN B (Simp.REWR_CONV B C.refuteThenPth) C.refuteF ttac }

/-- meson.ml's settable parameters (`meson_depth := true`, ...). -/
abbrev meson_depth := Meson.meson_depth
abbrev meson_prefine := Meson.meson_prefine
abbrev meson_dcutin := Meson.meson_dcutin
abbrev meson_skew := Meson.meson_skew
abbrev meson_brand := Meson.meson_brand
abbrev meson_split_limit := Meson.meson_split_limit
abbrev meson_chatty := Meson.meson_chatty

/-- `GEN_MESON_TAC min max step ths`. -/
unsafe def GEN_MESON_TAC (min max step : Int) (ths : List thm) : tactic := fun g => do
  Meson.GEN_MESON_TAC B MesonD (← Meson.readConfig) MesonS mesonInferences
    Mn.pths Mn.eqAx Mn.brand mesonContraposCache min max step ths g

/-- `ASM_MESON_TAC ths = GEN_MESON_TAC 0 50 1 ths`. -/
unsafe def ASM_MESON_TAC (ths : List thm) : tactic := fun g => do
  Meson.ASM_MESON_TAC B MesonD (← Meson.readConfig) MesonS mesonInferences
    Mn.pths Mn.eqAx Mn.brand mesonContraposCache ths g

/-- `MESON_TAC ths`. -/
unsafe def MESON_TAC (ths : List thm) : tactic := fun g => do
  Meson.MESON_TAC B MesonD (← Meson.readConfig) MesonS mesonInferences
    Mn.pths Mn.eqAx Mn.brand mesonContraposCache ths g

/-- `MESON ths tm`: prove `tm` by MESON. -/
unsafe def MESON (ths : List thm) (tm : term) : IO (Except String thm) := do
  Meson.MESON B MesonD (← Meson.readConfig) MesonS mesonInferences
    Mn.pths Mn.eqAx Mn.brand mesonContraposCache ths tm

/- ---------------------------------------------------------------------- -/
/- firstorder.ml (Faerber/Kaliszyk first-order shadow-term facilities)    -/
/- ---------------------------------------------------------------------- -/

initialize foVstore : IO.Ref (List (term × Int)) ← IO.mkRef []
initialize foGstore : IO.Ref (List (term × Int)) ← IO.mkRef []
initialize foVcounter : IO.Ref Int ← IO.mkRef 0
initialize foCstore : IO.Ref (List (term × Int)) ← IO.mkRef []
initialize foCcounter : IO.Ref Int ← IO.mkRef 2

/-- FirstOrder's own term↔code stores (separate from MESON's). -/
def FoS : Meson.FolStores :=
  { vstore := foVstore, gstore := foGstore, vcounter := foVcounter,
    cstore := foCstore, ccounter := foCcounter }

unsafe def fo_reset_vars : IO Unit := FirstOrder.Mapping.reset_vars FoS
unsafe def fo_reset_consts : IO (Except String Unit) := FirstOrder.Mapping.reset_consts FoS
unsafe def fo_fol_of_term (env consts : List term) (tm : term) :
    IO (Except String Meson.fol_term) := FirstOrder.Mapping.fol_of_term FoS env consts tm
unsafe def fo_fol_of_form (env consts : List term) (tm : term) :
    IO (Except String Meson.fol_form) := FirstOrder.Mapping.fol_of_form FoS env consts tm
unsafe def fo_hol_of_term (ty : hol_type) (tm : Meson.fol_term) : IO (Except String term) :=
  FirstOrder.Mapping.hol_of_term FoS ty tm
unsafe def fo_fol_of_hol_clauses (thms : List thm) : IO (Except String Meson.ancestors) :=
  FirstOrder.Mapping.fol_of_hol_clauses FoS thms

/- ---------------------------------------------------------------------- -/
/- metis.ml (Metis first-order automation with proof reconstruction)      -/
/- ---------------------------------------------------------------------- -/

initialize metisRandGen  : IO.Ref StdGen ← IO.mkRef (mkStdGen 0)
initialize metisClauseId : IO.Ref Int    ← IO.mkRef 0
initialize metisGen      : IO.Ref Int    ← IO.mkRef 0
initialize metisRules    : IO.Ref (Option Metis.Metis_rules.MetisRulesDeps) ← IO.mkRef none

/-- Metis reuses MESON's term↔code stores (`fol_of_var`/`fol_of_const`). -/
unsafe def MetisS : Meson.FolStores := MesonS

/-- Metis's case-split limit (OCaml `split_limit` ref; default 0). -/
def metisSplitLimit : Int := 0

/-- `mk_eq` as a one-shot `(term×term) → IO (Except term)`. -/
private unsafe def metisMkEq (p : term × term) : IO (Except String term) := do
  match ← (mk_eq : IO (Except String ((term × term) → Except String term))) with
  | .ok f => return (f p)
  | .error e => return .error e

/-- `~`, `F`, `\/` as preterms (for building HOL literals during reconstruction). -/
private def metisQuotp (s : String) : IO HolCore.Preterm.preterm := do
  match ← HolCore.Parser.parse_term s with
  | .ok t => pure (HolCore.Preterm.preterm_of_term t)
  | .error e => panic! s!"Session.metisQuotp {s}: {e}"
-- metis.ml's Preterm module parses these quotations on every call.
private def metisNegp : IO HolCore.Preterm.preterm := metisQuotp "~"
private def metisFalsityp : IO HolCore.Preterm.preterm := metisQuotp "F"
private def metisDisjp : IO HolCore.Preterm.preterm := metisQuotp "\\/"

/-- `DISJ_ACI_RULE` as a `term → IO (Except thm)` (wraps Canon's pure form). -/
private unsafe def metisDisjAci (tm : term) : IO (Except String thm) :=
  pure (Canon.DISJ_ACI_RULE B Cn.disjPthLeft Cn.disjPthRight Cn.disjPth Cn.disjPthNeg
          Cn.aTm Cn.bTm tm)

/-- `CONJ_ACI_RULE` (canon.ml 28): prove `p <=> p'` for conjunctions equal up
    to associativity, commutativity and idempotence. -/
unsafe def CONJ_ACI_RULE : term → Except String thm := Canon.CONJ_ACI_RULE B

/-- `DISJ_ACI_RULE` (canon.ml 46): the same for disjunctions. -/
unsafe def DISJ_ACI_RULE (tm : term) : Except String thm :=
  Canon.DISJ_ACI_RULE B Cn.disjPthLeft Cn.disjPthRight Cn.disjPth Cn.disjPthNeg Cn.aTm Cn.bTm tm

/-- The RESOLVE / IMPL_NOT TAUT lemmas, proved once and cached. -/
private unsafe def MtRules : Metis.Metis_rules.MetisRulesDeps :=
  match unsafeIO (do
    match ← metisRules.get with
    | some r => pure r
    | none =>
      match ← (do
        let mkTaut (s : String) : ExceptT String IO thm := do
          (Classic.TAUT B C.BOOL_CASES_AX (← HolCore.Parser.parse_term s) : IO (Except String thm))
        let r1  ← mkTaut "!a. a ==> ~a ==> F"
        let r2l ← mkTaut "!a b. a \\/ b ==> ~a ==> b"
        let r2r ← mkTaut "!a c. a ==> ~a \\/ c ==> c"
        let r3  ← mkTaut "!a b c. a \\/ b ==> ~a \\/ c ==> b \\/ c"
        let inl ← mkTaut "!a b. ~a ==> b <=> a \\/ b"
        let inr ← mkTaut "!a b. a ==> b <=> ~a \\/ b"
        pure ({ RESOLVE_1 := r1, RESOLVE_2L := r2l, RESOLVE_2R := r2r, RESOLVE_3 := r3,
                IMPL_NOT_L := inl, IMPL_NOT_R := inr,
                DISJ_ACI_RULE := metisDisjAci,
                PURE_ONCE_REWRITE_RULE := fun thl th => Simp.PURE_ONCE_REWRITE_RULE B thl th,
                mk_eq := metisMkEq } : Metis.Metis_rules.MetisRulesDeps)).run with
      | .ok r => do metisRules.set (some r); pure r
      | .error e => panic! s!"Metis rules setup failed: {e}") with
  | .ok r => r | _ => panic! "Session.MtRules"

/-- The reconstruction dependency bundle. -/
private unsafe def MetisRecon : Metis.Metis_reconstruct2.MetisReconDeps :=
  { S := MetisS, negp := metisNegp, falsityp := metisFalsityp, disjp := metisDisjp,
    rules := MtRules,
    EXCLUDED_MIDDLE := C.EXCLUDED_MIDDLE,
    term_type_unify := fun t1 t2 i => (Drule.term_type_unify t1 t2 i : IO (Except String _)),
    type_unify := fun a b s => pure (Drule.type_unify a b s),
    INSTANTIATE := fun i th => pure (Drule.INSTANTIATE i th),
    DISJ_CANON_CONV := Canon.disjCanonConv B Cn,
    PURE_ONCE_REWRITE_CONV := fun thl => Simp.PURE_ONCE_REWRITE_CONV B thl }

/-- `GEN_METIS_TAC ths`. -/
unsafe def GEN_METIS_TAC (ths : List thm) : tactic :=
  Metis.Metis.GEN_METIS_TAC B MesonD MetisS mesonContraposCache metisRandGen metisClauseId
    metisGen MetisRecon (Canon.disjCanonConv B Cn) metisSplitLimit ths

/-- `ASM_METIS_TAC = GEN_METIS_TAC`. -/
unsafe def ASM_METIS_TAC (ths : List thm) : tactic :=
  Metis.ASM_METIS_TAC B MesonD MetisS mesonContraposCache metisRandGen metisClauseId
    metisGen MetisRecon (Canon.disjCanonConv B Cn) metisSplitLimit ths

/-- `METIS_TAC ths = POP_ASSUM_LIST (K ALL_TAC) THEN ASM_METIS_TAC ths`. -/
unsafe def METIS_TAC (ths : List thm) : tactic :=
  Metis.METIS_TAC B MesonD MetisS mesonContraposCache metisRandGen metisClauseId
    metisGen MetisRecon (Canon.disjCanonConv B Cn) metisSplitLimit ths

/-- `METIS ths tm`: prove `tm` by Metis. -/
unsafe def METIS (ths : List thm) (tm : term) : IO (Except String thm) :=
  Metis.METIS B MesonD MetisS mesonContraposCache metisRandGen metisClauseId
    metisGen MetisRecon (Canon.disjCanonConv B Cn) metisSplitLimit ths tm

/-- `GEN_METIS_TAC_SPLIT n ths`: like `GEN_METIS_TAC` but with an explicit
    case-split limit `n` (OCaml sets the `split_limit` ref before calling). -/
unsafe def GEN_METIS_TAC_SPLIT (n : Int) (ths : List thm) : tactic :=
  Metis.Metis.GEN_METIS_TAC B MesonD MetisS mesonContraposCache metisRandGen metisClauseId
    metisGen MetisRecon (Canon.disjCanonConv B Cn) n ths

/-- `METIS_SPLIT n ths tm`: prove `tm` by Metis with case-split limit `n`. -/
unsafe def METIS_SPLIT (n : Int) (ths : List thm) (tm : term) : IO (Except String thm) :=
  Tactics.TAC_PROOF B ([], tm)
    (THEN (Tactics.POP_ASSUM_LIST (fun _ => Tactics.ALL_TAC)) (GEN_METIS_TAC_SPLIT n ths))

/- ---------------------------------------------------------------------- -/
/- thecops.ml (leanCoP + nanoCoP connection provers)                      -/
/- ---------------------------------------------------------------------- -/

/-- Cached CoP support: Hashek theorems, the symmetry-augmented equality
    axioms, and the `~t==>F<=>t` tautology. -/
structure CopSupport where
  hashek : TheCops.Hashek.HashekThms
  eqSym : Meson.EqAxPths
  deriving Inhabited

initialize theCopSupport : IO.Ref (Option CopSupport) ← IO.mkRef none
initialize leancopDb : TheCops.Database.DB ← IO.mkRef []
initialize nanocopDb : TheCops.Ncdatabase.DB ← IO.mkRef []

private unsafe def Cs : CopSupport :=
  match unsafeIO (do
    match ← theCopSupport.get with
    | some c => pure c
    | none =>
      match ← (do
        -- Hashek: hashek = T, and its supporting theorems.  Define FIRST so that
        -- `hashek` parses as the (bool) constant, not an untyped variable.
        let hashek_def ← (Drule.new_definition B (← parse_term "hashek = T") : IO (Except String thm))
        let hashek_tm ← parse_term "hashek"
        let hashek_thm ← (Tactics.prove B (← parse_term "hashek") (Simp.SIMP_TAC B [hashek_def]) : IO (Except String thm))
        let hashek_prop ← (Tactics.prove B
          (← parse_term "((x /\\ hashek) ==> (y /\\ hashek)) ==> (x ==> y)")
          (Simp.SIMP_TAC B [hashek_def]) : IO (Except String thm))
        let hashek_eq ← (Tactics.prove B (← parse_term "~ hashek <=> F")
          (Simp.SIMP_TAC B [hashek_def]) : IO (Except String thm))
        -- thecops.ml 43: MARK_ASSUMS = RULE_ASSUM_TAC (DISCH `hashek`).
        let mark_tm ← parse_term "hashek"
        let H : TheCops.Hashek.HashekThms :=
          { hashek_def, hashek_tm, hashek_thm, hashek_prop, hashek_eq, mark_tm }
        -- leanCoP equality axioms (Meson's + symmetry conjunct).
        let TAUT (s : String) : ExceptT String IO thm := do
          (Classic.TAUT B C.BOOL_CASES_AX (← parse_term s) : IO (Except String thm))
        let ASM_CASES_TAC := Classic.ASM_CASES_TAC B C.EXCLUDED_MIDDLE
        let tautConv : ioconv := fun w => (Classic.TAUT B C.BOOL_CASES_AX w : IO (Except String thm))
        let xeqy ← parse_term "x:A = y"
        let eqConj ← (Tactics.prove B
          (← parse_term "(x:A = x) /\\ (~(x = y) \\/ y = x) /\\ (~(x:A = y) \\/ ~(x = z) \\/ (y = z))")
          (Tactics.THEN B (Simp.REWRITE_TAC B [])
            (Tactics.THEN B (ASM_CASES_TAC xeqy)
              (Tactics.THEN B (Simp.ASM_REWRITE_TAC B []) (Tactics.CONV_TAC B tautConv)))) : IO (Except String thm))
        let eqThms := B.CONJUNCTS eqConj
        let impElim ← TAUT "(a ==> b) <=> ~a \\/ b"
        let eqElim ← TAUT "(a <=> b) ==> b \\/ ~a"
        let veqTm ← liftExcept (do match eqThms with
          | e0 :: _ => rator (← rator (concl e0)) | [] => .error "eqSym: no eq_thms")
        let eqSym : Meson.EqAxPths := { eqThms, impElim, eqElim, veqTm }
        -- thecops.ml 1256-1270: the three load-time `assert`s.  OCaml
        -- evaluates `x = y` and the list right to left.  They run when
        -- thecops.ml loads, with `copverb` at its default (false); this
        -- setup may be built later, so CONTRADICTION's trace is switched off.
        let verb ← HolCore.FirstOrder.copverb.get
        HolCore.FirstOrder.copverb.set false
        let want ← parse_term "c \\/ b \\/ a"
        let pc ← liftExcept (B.UNDISCH (← TAUT "c ==> c \\/ b \\/ a"))
        let pb ← liftExcept (B.UNDISCH (← TAUT "b ==> c \\/ b \\/ a"))
        let pa ← liftExcept (B.UNDISCH (← TAUT "a ==> c \\/ b \\/ a"))
        let abc ← liftExcept (HolCore.Kernel.ASSUME (← parse_term "a \\/ b \\/ c"))
        let got ← liftExcept (TheCops.Ncrecon.DISJ_CASES_LIST B abc [pa, pb, pc])
        unless concl got == want do throw "thecops.ml 1256: Assert_failure"
        for swap in [false, true] do
          let f ← parse_term "F"
          let (x, y) ← if swap then do
              let x ← parse_term "~p"; let y ← parse_term "p:bool"; pure (x, y)
            else do
              let y ← parse_term "p:bool"; let x ← parse_term "~p"; pure (x, y)
          let (tx, ty) ← liftExcept (do pure (← HolCore.Kernel.ASSUME x, ← HolCore.Kernel.ASSUME y))
          let c ← ExceptT.mk (if swap then TheCops.Ncrecon.CONTRADICTION B ty tx else TheCops.Ncrecon.CONTRADICTION B tx ty)
          unless concl c == f do throw "thecops.ml 1269: Assert_failure"
        HolCore.FirstOrder.copverb.set verb
        pure ({ hashek := H, eqSym } : CopSupport) : ExceptT String IO CopSupport).run with
      | .ok c => do theCopSupport.set (some c); pure c
      | .error e => panic! s!"CoP support setup failed: {e}") with
  | .ok c => c | _ => panic! "Session.Cs"

/-- thecops.ml 33: MARK_CONCL's `TAUT `!t. (~t ==> F <=> t)``, proved each
    time PREPARE_COP_TAC is applied. -/
private unsafe def copNotTFimp : IO (Except String thm) := do
  match ← parse_term "!t. (~t ==> F <=> t)" with
  | .ok t => Classic.TAUT B C.BOOL_CASES_AX t
  | .error e => return .error e

private unsafe def LeancopD : TheCops.Leancop.LeancopDeps :=
  { S := MesonS, P := Mn.pths, mem := mesonContraposCache, db := leancopDb,
    E := Cs.eqSym, Emeson := Mn.eqAx, hashek := Cs.hashek, D := MesonD, notTFimp := copNotTFimp }

private unsafe def NanocopD : TheCops.Nanocop.NanocopDeps :=
  { S := MesonS, P := Mn.pths, mem := mesonContraposCache, db := nanocopDb,
    E := Cs.eqSym, Emeson := Mn.eqAx, hashek := Cs.hashek, D := MesonD, notTFimp := copNotTFimp,
    CONJ_ASSOC := T.CONJ_ASSOC, DISJ_ASSOC := T.DISJ_ASSOC }

/- ---------------------------------------------------------------------- -/
/- Expose the key functions at the top level.                             -/
/- (thecops.ml 1482)                                                      -/
/- ---------------------------------------------------------------------- -/

unsafe def LEANCOP_TAC (ths : List thm) : tactic := TheCops.Leancop.LEANCOP_TAC B LeancopD ths
unsafe def LEANCOP (ths : List thm) (tm : term) : IO (Except String thm) :=
  TheCops.Leancop.LEANCOP B LeancopD ths tm
/-- thecops.ml's `Hashek` theorems (`Hashek.hashek_def`, ...). -/
unsafe def hashekThms : TheCops.Hashek.HashekThms := Cs.hashek

unsafe def NANOCOP_TAC (ths : List thm) : tactic := TheCops.Nanocop.NANOCOP_TAC B NanocopD ths

/- ---------------------------------------------------------------------- -/
/- Probe accessors for the two DISTINCT equality-axiom bundles.            -/
/- ---------------------------------------------------------------------- -/
/-
  leanCoP and MESON must NOT share these.  thecops.ml 510-514 proves a
  THREE-conjunct `eq_thms` including the SYMMETRY clause `~(x = y) \/ y = x`;
  meson.ml 583-587 proves only TWO (reflexivity and transitivity).  Session
  wires `E := Cs.eqSym` (three) and `Emeson := Mn.eqAx` (two) accordingly.

  These accessors exist so a test can PIN that distinction, and so the cached
  `CopSupport` bundle is REACHABLE at all: it derives `Inhabited` and `panic!`s
  on setup failure, so without a public accessor a degenerate `|-  = ` bundle
  would be invisible unless a test actually ran leanCoP.
-/
unsafe def COP_EQ_THMS : List thm := Cs.eqSym.eqThms
unsafe def MESON_EQ_THMS : List thm := Mn.eqAx.eqThms
/- The tracing switches (HOL Light refs): `copverb` (firstorder.ml 13, the
   CoPs), `metisverb` (metis.ml 21) and `Metis_unify.verb` (metis.ml 9647).
   All off by default.  Set with e.g. `copverb.set true`. -/
export HolCore.FirstOrder (copverb)
export HolCore.Metis (metisverb metis_unify_verb)

/-- `PRINT_TAC`, `PRINT_ID_TAC` (thecops.ml 1462-1463). -/
def PRINT_TAC : tactic := TheCops.Nanocop.PRINT_TAC
def PRINT_ID_TAC (s : String) : tactic := TheCops.Nanocop.PRINT_ID_TAC s

unsafe def NANOCOP (ths : List thm) (tm : term) : IO (Except String thm) :=
  TheCops.Nanocop.NANOCOP B NanocopD ths tm

/-- `Equality.create_eq_axs sym` (thecops.ml 578): equality and congruence
    axioms for the constants in `tms`, with the symmetry axiom if `sym`. -/
unsafe def create_eq_axs (sym : Bool) (tms : List term) : IO (Except String (List thm)) :=
  TheCops.Equality.create_eq_axs B NanocopD.E NanocopD.Emeson sym tms
/-- `Nanocop.PREPARE_NANOCOP_TAC` (thecops.ml 1466). -/
unsafe def PREPARE_NANOCOP_TAC (ths : List thm) : tactic :=
  TheCops.Nanocop.PREPARE_NANOCOP_TAC B NanocopD ths

/- ---------------------------------------------------------------------- -/
/- quot.ml : quotient types and lifting of first-order theorems.          -/
/- ---------------------------------------------------------------------- -/

/-- Support lemmas for `quot.ml`, proved once: `SELECT_LEMMA`
    (`|- !x. (@y. x = y) = x`) and `pth` (the big `lift_theorem` implication). -/
structure QuotSupport where
  selectLemma : thm
  pth : thm
  deriving Inhabited

initialize theQuotSupport : IO.Ref (Option QuotSupport) ← IO.mkRef none

private unsafe def Qs : QuotSupport :=
  match unsafeIO (do
    match ← theQuotSupport.get with
    | some q => pure q
    | none =>
      match ← (do
        let TAUT (s : String) : ExceptT String IO thm := do
          (Classic.TAUT B C.BOOL_CASES_AX (← parse_term s) : IO (Except String thm))
        let selectConvIO : ioconv := fun t => pure (SELECT_CONV t)
        -- SELECT_LEMMA = prove(`!x:A. (@y. x = y) = x`,
        --   GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [EQ_SYM_EQ] THEN
        --   MATCH_ACCEPT_TAC SELECT_REFL)
        let selectLemma ← (Tactics.prove B (← parse_term "!x:A. (@y. x = y) = x")
          (Tactics.THEN B GEN_TAC
            (Tactics.THEN B
              (GEN_REWRITE_TAC (fun c => Simp.landConvIO (Simp.binderConvIO c)) [EQ_SYM_EQ])
              (MATCH_ACCEPT_TAC SELECT_REFL))) : IO (Except String thm))
        -- pth: STRIP_TAC THEN SUBGOAL_THEN ... ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN ...
        let pthGoal ← parse_term
          ("(!x:Repty. R x x) /\\ (!x y. R x y <=> R y x) /\\ " ++
           "(!x y z. R x y /\\ R y z ==> R x z) /\\ (!a. mk(dest a) = a) /\\ " ++
           "(!r. (?x. r = R x) <=> (dest(mk r) = r)) " ++
           "==> (!x y. R x y <=> (mk(R x) = mk(R y))) /\\ " ++
           "(!P. (!x. P(mk(R x))) <=> (!x. P x)) /\\ " ++
           "(!P. (?x. P(mk(R x))) <=> (?x. P x)) /\\ " ++
           "(!x:Absty. mk(R((@)(dest x))) = x)")
        let subgoal1 ← parse_term
          "!x y. (mk((R:Repty->Repty->bool) x):Absty = mk(R y)) <=> (R x = R y)"
        let subgoal2 ← parse_term
          "dest(mk((R:Repty->Repty->bool) x):Absty) = R x"
        let mmpTaut ← TAUT "(a /\\ b /\\ c) /\\ (b ==> a ==> d) ==> a /\\ b /\\ c /\\ d"
        let xRepty ← parse_term "x:Repty"
        let etaAxSym ← liftExcept (GSYM ETA_AX)
        let pth ← (Tactics.prove B pthGoal
          (Tactics.EVERY B [
            STRIP_TAC,
            Tactics.THENL B (SUBGOAL_THEN subgoal1 ASSUME_TAC)
              [ASM_MESON_TAC [], Tactics.ALL_TAC],
            MATCH_MP_TAC mmpTaut,
            Tactics.THENL B CONJ_TAC
              [Tactics.THEN B (ASM_REWRITE_TAC [])
                 (Tactics.THEN B (REWRITE_TAC [FUN_EQ_THM]) (ASM_MESON_TAC [])),
               Tactics.ALL_TAC],
            Tactics.REPEAT B (DISCH_THEN (fun th =>
              match GSYM th with
              | .ok g => REWRITE_TAC [g]
              | .error _ => Tactics.ALL_TAC)),
            X_GEN_TAC xRepty,
            Tactics.THENL B (SUBGOAL_THEN subgoal2 SUBST1_TAC)
              [ASM_MESON_TAC [], Tactics.ALL_TAC],
            GEN_REWRITE_TAC (fun c => Simp.landConvIO (Simp.randConvIO c)) [etaAxSym],
            FIRST_ASSUM (fun th => GEN_REWRITE_TAC id [th]),
            Tactics.THEN B (CONV_TAC selectConvIO) (ASM_MESON_TAC []) ]) : IO (Except String thm))
        pure ({ selectLemma, pth } : QuotSupport) : ExceptT String IO QuotSupport).run with
      | .ok q => do theQuotSupport.set (some q); pure q
      | .error e => panic! s!"Quot support setup failed: {e}") with
  | .ok q => q | _ => panic! "Session.Qs"

/-- `define_quotient_type tyname (absname, repname) eqv`. -/
unsafe def define_quotient_type (tyname : String) (absrep : String × String) (eqv : term) :
    IO (Except String (thm × thm)) :=
  Quot.define_quotient_type B tyname absrep eqv

/-- `lift_function tybij2 (refl_th, trans_th) fname wth`. -/
unsafe def lift_function (tybij2 : thm) (reflTrans : thm × thm) (fname : String) (wth : thm) :
    IO (Except String (thm × thm)) :=
  Quot.lift_function B Qs.selectLemma ETA_CONV tybij2 reflTrans fname wth

/-- `lift_theorem tybij (refl_th, sym_th, trans_th) trths th`. -/
unsafe def lift_theorem (tybij : thm × thm) (reflSymTrans : thm × thm × thm)
    (trths : List thm) (th : thm) : IO (Except String thm) :=
  Quot.lift_theorem B Qs.pth tybij reflSymTrans trths th

/- ---------------------------------------------------------------------- -/
/- impconv.ml : implicational rewriting (IMP_REWRITE_TAC etc.).           -/
/- ---------------------------------------------------------------------- -/

initialize theImpConvVars : IO.Ref (Option ImpConv.ImpConvVars) ← IO.mkRef none
initialize theImpConvDeps : IO.Ref (Option ImpConv.ImpConvDeps) ← IO.mkRef none

/-- The `A/B/C/D/T : bool` instantiation-target constants for `impconv`. -/
private unsafe def Icv : ImpConv.ImpConvVars :=
  match unsafeIO (do
    match ← theImpConvVars.get with
    | some v => pure v
    | none =>
      match ← (do
        let and_tm ← parse_term "(/\\)"                    -- impconv.ml 41
        let A_ ← parse_term "A:bool"
        let B_ ← parse_term "B:bool"
        let C_ ← parse_term "C:bool"
        let D_ ← parse_term "D:bool"
        let T_ ← parse_term "T:bool"
        pure ({ and_tm, A_, B_, C_, D_, T_ } : ImpConv.ImpConvVars) : ExceptT String IO ImpConv.ImpConvVars).run with
      | .ok v => do theImpConvVars.set (some v); pure v
      | .error e => panic! s!"ImpConv vars setup failed: {e}") with
  | .ok v => v | _ => panic! "Session.Icv"

/-- The pre-proved theorems `impconv.ml` closes over (proved once). -/
private unsafe def Icd : ImpConv.ImpConvDeps :=
  match unsafeIO (do
    match ← theImpConvDeps.get with
    | some d => pure d
    | none =>
      match ← (do
        let TAUT (s : String) : ExceptT String IO thm := do
          (Classic.TAUT B C.BOOL_CASES_AX (← parse_term s) : IO (Except String thm))
        let imp_refl ← TAUT "A ==> A"
        let imp_swap ← TAUT "(p ==> q ==> r) <=> (q ==> p ==> r)"
        let IMPLY_AND_RDISTRIB ← TAUT "(x ==> y /\\ z) <=> (x==>y) /\\ (x==>z)"
        let mkimp_iff ← TAUT
          "((A ==> B) ==> (C ==> D)) /\\ ((B ==> A) ==> (D ==> C)) ==> (A <=> B) ==> (C <=> D)"
        let mkimp_contra_iff ← TAUT
          "((A ==> B) ==> C) /\\ ((B ==> A) ==> D) ==> (A <=> B) ==> C /\\ D"
        let mkimpl_contra_iff ← TAUT "((A ==> B) ==> C) ==> (A <=> B) ==> C /\\ (B ==> A)"
        let mkimpr_contra_iff ← TAUT "((B ==> A) ==> D) ==> (A <=> B) ==> (A ==> B) /\\ D"
        let mkimp_co_iff ← TAUT
          "(C ==> A ==> B) /\\ (D ==> B ==> A) ==> C /\\ D ==> (A <=> B)"
        let mkimpl_co_iff ← TAUT "(C ==> A ==> B) ==> C /\\ (B ==> A) ==> (A <=> B)"
        let mkimpr_co_iff ← TAUT "(D ==> B ==> A) ==> (A ==> B) /\\ D ==> (A <=> B)"
        let mkimp_imp_contra_ctxt ← TAUT
          "(B==>A) /\\ (A==>B==>C==>D) ==> (A==>C) ==> (B==>D)"
        let mkimp_imp_co_ctxt ← TAUT "(A==>B) /\\ (A==>B==>D==>C) ==> (B==>D) ==> (A==>C)"
        let mkimpr_imp_ctxt ← TAUT "(A==>C==>D) ==> (A==>C) ==> (A==>D)"
        let mkimp_conj_contra_ctxt ← TAUT "(C==>A==>B) /\\ (A==>B==>C==>D) ==> (A/\\C==>B/\\D)"
        let mkimpl_conj_contra_ctxt ← TAUT "(C==>A==>B) ==> (A/\\C==>B/\\C)"
        let mkimpr_conj_contra_ctxt ← TAUT "(A==>C==>D) ==> (A/\\C==>A/\\D)"
        let mkimp_conj_co_ctxt ← TAUT "(B==>A) /\\ (B==>D==>C) ==> (B/\\D==>A/\\C)"
        let mkimpl_conj_co_ctxt ← TAUT "(B==>A) ==> (B/\\C==>A/\\C)"
        let mkimpl_conj_co2_ctxt ← TAUT "(C==>B==>A) ==> (B/\\C==>A/\\C)"
        -- impconv.ml 1346: REWR_IMPCONV_OF_CONV's IMP_SYM.
        let imp_sym ← TAUT "A ==> B ==> C <=> B ==> A ==> C"
        let case_lem1 ← TAUT "(~P ==> Q = R) ==> (Q <=> (~P ==> R) /\\ (P ==> Q))"
        let case_lem2 ← TAUT "(P ==> Q = R) ==> (Q <=> (P ==> R) /\\ (~P ==> Q))"
        -- impconv.ml 1716: REWR_IMPMCONV_OF_MCONV proves its own IMP_SYM.
        let imp_sym' ← TAUT "A ==> B ==> C <=> B ==> A ==> C"
        pure ({ imp_refl, imp_swap, IMP_CONJ, IMP_IMP, IMPLY_AND_RDISTRIB,
                AND_FORALL_THM, RIGHT_IMP_FORALL_THM, CONJ_ASSOC,
                MONO_AND, MONO_OR, MONO_IMP, MONO_NOT, MONO_FORALL, MONO_EXISTS,
                mkimp_iff, mkimp_contra_iff, mkimpl_contra_iff, mkimpr_contra_iff,
                mkimp_co_iff, mkimpl_co_iff, mkimpr_co_iff,
                mkimp_imp_contra_ctxt, mkimp_imp_co_ctxt, mkimpr_imp_ctxt,
                mkimp_conj_contra_ctxt, mkimpl_conj_contra_ctxt, mkimpr_conj_contra_ctxt,
                mkimp_conj_co_ctxt, mkimpl_conj_co_ctxt, mkimpl_conj_co2_ctxt,
                NOT_FORALL_THM, NOT_IMP, imp_sym, imp_sym', LEFT_IMP_EXISTS_THM,
                LEFT_FORALL_IMP_THM, case_lem1, case_lem2 } : ImpConv.ImpConvDeps)
          : ExceptT String IO ImpConv.ImpConvDeps).run with
      | .ok d => do theImpConvDeps.set (some d); pure d
      | .error e => panic! s!"ImpConv deps setup failed: {e}") with
  | .ok d => d | _ => panic! "Session.Icd"

/-- `IMP_REWRITE_TAC ths`: implicational rewriting. -/
unsafe def IMP_REWRITE_TAC (ths : List thm) : tactic := ImpConv.IMP_REWRITE_TAC B Icd Icv ths
/-- `SEQ_IMP_REWRITE_TAC ths`. -/
unsafe def SEQ_IMP_REWRITE_TAC (ths : List thm) : tactic := ImpConv.SEQ_IMP_REWRITE_TAC B Icd Icv ths
/-- `ASM_IMP_REWRITE_TAC ths`. -/
unsafe def ASM_IMP_REWRITE_TAC (ths : List thm) : tactic := ImpConv.ASM_IMP_REWRITE_TAC B Icd Icv ths
/-- `CASE_REWRITE_TAC th`. -/
unsafe def CASE_REWRITE_TAC (th : thm) : tactic := ImpConv.CASE_REWRITE_TAC B Icd Icv th
/-- `TARGET_REWRITE_TAC sths th`. -/
unsafe def TARGET_REWRITE_TAC (sths : List thm) (th : thm) : tactic :=
  ImpConv.TARGET_REWRITE_TAC B Icd Icv sths th
/-- `HINT_EXISTS_TAC`. -/
unsafe def HINT_EXISTS_TAC : tactic := ImpConv.HINT_EXISTS_TAC B Icd Icv

/- ---------------------------------------------------------------------- -/
/- pair.ml: syntactic sugar constants + the `prod` (pairing) type         -/
/- ---------------------------------------------------------------------- -/

/-- Helper: `new_definition` a parsed term, panicking with context on failure. -/
private unsafe def pairDef (label s : String) : IO thm := do
  let tm ← (match ← HolCore.Parser.parse_term s with
            | .ok t => pure t | .error e => panic! s!"{label} parse: {e}")
  match ← (Drule.new_definition B tm : IO (Except String thm)) with
  | .ok t => pure t | .error e => panic! s!"{label}: {e}"

/-- Cache for the pair.ml sugar definitions, the `prod` type bijection, and the
    projection definitions.  Order mirrors `pair.ml`: sugar consts and
    `mk_pair_def` first, then `PAIR_EXISTS_THM` (MESON), the type definition,
    then `COMMA_DEF`/`FST_DEF`/`SND_DEF`.  Returns everything downstream needs. -/
initialize thePairAux : IO.Ref (Option HolMath.Pair.PairDefs) ← IO.mkRef none

private unsafe def pairAux : HolMath.Pair.PairDefs :=
  match unsafeIO (do
    match ← thePairAux.get with
    | some x => pure x
    | none =>
      let LET_DEF ← pairDef "LET_DEF" "LET (f:A->B) x = f x"
      let LET_END_DEF ← pairDef "LET_END_DEF" "LET_END (t:A) = t"
      let GABS_DEF ← pairDef "GABS_DEF" "GABS (P:A->bool) = (@) P"
      let GEQ_DEF ← pairDef "GEQ_DEF" "GEQ a b = (a:A = b)"
      let _SEQPATTERN ← pairDef "_SEQPATTERN"
        "_SEQPATTERN = \\(r:A->B->bool) s x. if ?y. r x y then r x else s x"
      let _UNGUARDED_PATTERN ← pairDef "_UNGUARDED_PATTERN"
        "_UNGUARDED_PATTERN = \\p r. p /\\ r"
      let _GUARDED_PATTERN ← pairDef "_GUARDED_PATTERN"
        "_GUARDED_PATTERN = \\p g r. p /\\ g /\\ r"
      let _MATCH ← pairDef "_MATCH"
        "_MATCH =  \\e (r:A->B->bool). if (?!) (r e) then (@) (r e) else @z. F"
      let _FUNCTION ← pairDef "_FUNCTION"
        "_FUNCTION = \\(r:A->B->bool) x. if (?!) (r x) then (@) (r x) else @z. F"
      -- Pair type.
      let mk_pair_def ← pairDef "mk_pair_def"
        "mk_pair (x:A) (y:B) = \\a b. (a = x) /\\ (b = y)"
      let PAIR_EXISTS_THM ← (match ← (MESON [] (← (match ← HolCore.Parser.parse_term
            "?x. ?(a:A) (b:B). x = mk_pair a b" with
            | .ok t => pure t | .error e => panic! s!"PAIR_EXISTS_THM parse: {e}"))
            : IO (Except String thm)) with
        | .ok t => pure t | .error e => panic! s!"PAIR_EXISTS_THM: {e}")
      let prod_tybij ← (match ← (new_type_definition "prod" "ABS_prod" "REP_prod"
            PAIR_EXISTS_THM : IO (Except String thm)) with
        | .ok t => pure t | .error e => panic! s!"prod_tybij: {e}")
      -- parse_as_infix (",",(14,"right")) — must precede parsing of `,`-terms.
      HolCore.Printer.parse_as_infix (",", (14, "right"))
      let COMMA_DEF ← pairDef "COMMA_DEF" "(x:A),(y:B) = ABS_prod(mk_pair x y)"
      let FST_DEF ← pairDef "FST_DEF" "FST (p:A#B) = @x. ?y. p = x,y"
      let SND_DEF ← pairDef "SND_DEF" "SND (p:A#B) = @y. ?x. p = x,y"
      let x : HolMath.Pair.PairDefs :=
        { LET_DEF, LET_END_DEF, GABS_DEF, GEQ_DEF
          SEQPATTERN        := _SEQPATTERN
          UNGUARDED_PATTERN := _UNGUARDED_PATTERN
          GUARDED_PATTERN   := _GUARDED_PATTERN
          MATCH             := _MATCH
          FUNCTION          := _FUNCTION
          mk_pair_def, PAIR_EXISTS_THM, prod_tybij, COMMA_DEF, FST_DEF, SND_DEF }
      thePairAux.set (some x); pure x) with
  | .ok x => x | _ => panic! "Session.pairAux: not initialised"

/- ---------------------------------------------------------------------- -/
/- pair.ml: general beta-conversion over nested constructor patterns      -/
/- ---------------------------------------------------------------------- -/

/-- Mutable projection cache backing `GEN_BETA_CONV`'s `projection_cache` ref. -/
initialize theProjectionCache : IO.Ref (List (String × List thm)) ← IO.mkRef []

/-- The `GABS_RULE` lemma: `|- (?) P ==> P (GABS P)` (pair.ml, proved once via
    `SIMP_TAC[GABS_DEF; SELECT_AX; ETA_AX]`). -/
initialize theGabsRulePth : IO.Ref (Option thm) ← IO.mkRef none

private unsafe def gabsRulePth : thm :=
  match unsafeIO (do
    match ← theGabsRulePth.get with
    | some t => pure t
    | none =>
      let goal ← (match ← HolCore.Parser.parse_term "(?) P ==> P (GABS P)" with
                  | .ok t => pure t | .error e => panic! s!"GABS_RULE pth parse: {e}")
      let th ← (match ← (Tactics.prove B goal
            (Simp.SIMP_TAC B [pairAux.GABS_DEF, SELECT_AX, ETA_AX]) : IO (Except String thm)) with
        | .ok t => pure t | .error e => panic! s!"GABS_RULE pth: {e}")
      theGabsRulePth.set (some th); pure th) with
  | .ok t => t | _ => panic! "Session.gabsRulePth"

/-- The session state/lemmas `GEN_BETA_CONV` closes over (see
    `HolMath.HolMath.Pair.GenBetaDeps`): the projection cache, a reader for the
    `inductive_type_store`, `GEQ_DEF`, the `GABS_RULE` lemma, and
    `SELECT_RULE`'s `pth`/`P`. -/
private unsafe def genBetaDeps : HolMath.Pair.GenBetaDeps :=
  { cache         := theProjectionCache
    store         := (do return (← theInductiveTypeStore.get).get!)
    GEQ_DEF       := pairAux.GEQ_DEF
    gabsRulePth   := gabsRulePth }

/-- `GEN_BETA_CONV` (pair.ml), applied to the session state. -/
unsafe def GEN_BETA_CONV : term → IO (Except String thm) := HolMath.Pair.GEN_BETA_CONV genBetaDeps

/-- Install `GEN_BETA_CONV` and the `prod` inductive-type-store entry / basic
    rewrites (the stateful step pair.ml performs before the paired-abstraction
    theorems).  Passed to `setupPair` as `installGenBeta`. -/
private unsafe def installGenBeta (fstT sndT pairT indT recT : thm) : IO (Except String Unit) :=
  ExceptT.run do
    -- extend_basic_rewrites [FST; SND; PAIR]
    let _ ← ExceptT.mk (extend_basic_rewrites [fstT, sndT, pairT])
    -- inductive_type_store := ("prod",(1,pair_INDUCT,pair_RECURSION)) :: (!...)
    let cur ← theInductiveTypeStore.get
    let base := cur.getD [("bool", (2, C.bool_INDUCT, C.bool_RECURSION))]
    theInductiveTypeStore.set (some (("prod", (1, indT, recT)) :: base))
    -- GEN_BETA_CONV's GABS_RULE lemma is proved when GEN_BETA_CONV is defined,
    -- before the extend_basic_convs below.
    let _ ← IO.mkRef (concl gabsRulePth)
    -- extend_basic_convs ("GEN_BETA_CONV", (`GABS (\a. b) c`, GEN_BETA_CONV))
    let pat ← ExceptT.mk (HolCore.Parser.parse_term "GABS (\\a. b) c")
    ExceptT.mk (Simp.extend_basic_convs B "GEN_BETA_CONV" (pat, GEN_BETA_CONV))

/-- Cache for the `pair.ml` theorem layer. -/
initialize thePair : IO.Ref (Option PairThms) ← IO.mkRef none

private unsafe def Pr : PairThms :=
  match unsafeIO (do
    match ← thePair.get with
    | some t => pure t
    | none =>
      let P := pairAux
      match ← (setupPair DSL ETA_AX
                 P.PAIR_EXISTS_THM P.prod_tybij P.mk_pair_def P.COMMA_DEF P.FST_DEF P.SND_DEF
                 o_DEF MESON_TAC ASM_MESON_TAC MESON SELECT_ELIM_TAC installGenBeta).run with
      | .ok t => do
          thePair.set (some t)
          pure t
      | .error e => panic! s!"setupPair failed: {e}") with
  | .ok t => t | _ => panic! "Session.Pr: setupPair not run"

-- Expose the pair.ml definitions.
unsafe def LET_DEF : thm := pairAux.LET_DEF
unsafe def LET_END_DEF : thm := pairAux.LET_END_DEF
unsafe def GABS_DEF : thm := pairAux.GABS_DEF
/-- The pair.ml syntactic-sugar definitions (`_SEQPATTERN`, `_MATCH`, ...),
    whose OCaml names begin with `_`; `Database.lean` names them. -/
unsafe def pairSugarDefs : HolMath.Pair.PairDefs := pairAux
unsafe def GEQ_DEF : thm := pairAux.GEQ_DEF
unsafe def mk_pair_def : thm := pairAux.mk_pair_def
unsafe def prod_tybij : thm := pairAux.prod_tybij
unsafe def COMMA_DEF : thm := pairAux.COMMA_DEF
unsafe def FST_DEF : thm := pairAux.FST_DEF
unsafe def SND_DEF : thm := pairAux.SND_DEF

-- Expose the pair.ml theorems.
unsafe def PAIR_EXISTS_THM := Pr.PAIR_EXISTS_THM
unsafe def REP_ABS_PAIR := Pr.REP_ABS_PAIR
unsafe def PAIR_EQ := Pr.PAIR_EQ
unsafe def PAIR_SURJECTIVE := Pr.PAIR_SURJECTIVE
unsafe def FST := Pr.FST
unsafe def SND := Pr.SND
unsafe def PAIR := Pr.PAIR
unsafe def pair_INDUCT := Pr.pair_INDUCT
unsafe def pair_RECURSION := Pr.pair_RECURSION
unsafe def FORALL_PAIR_THM := Pr.FORALL_PAIR_THM
unsafe def EXISTS_PAIR_THM := Pr.EXISTS_PAIR_THM
unsafe def LAMBDA_PAIR_THM := Pr.LAMBDA_PAIR_THM
unsafe def LAMBDA_PAIR := Pr.LAMBDA_PAIR
unsafe def LAMBDA_TRIPLE_THM := Pr.LAMBDA_TRIPLE_THM
unsafe def LAMBDA_TRIPLE := Pr.LAMBDA_TRIPLE
unsafe def PAIRED_ETA_THM := Pr.PAIRED_ETA_THM
unsafe def FORALL_UNCURRY := Pr.FORALL_UNCURRY
unsafe def EXISTS_UNCURRY := Pr.EXISTS_UNCURRY
unsafe def EXISTS_CURRY := Pr.EXISTS_CURRY
unsafe def FORALL_CURRY := Pr.FORALL_CURRY
unsafe def FORALL_UNPAIR_THM := Pr.FORALL_UNPAIR_THM
unsafe def EXISTS_UNPAIR_THM := Pr.EXISTS_UNPAIR_THM
unsafe def FORALL_PAIR_FUN_THM := Pr.FORALL_PAIR_FUN_THM
unsafe def EXISTS_PAIR_FUN_THM := Pr.EXISTS_PAIR_FUN_THM
unsafe def FORALL_UNPAIR_FUN_THM := Pr.FORALL_UNPAIR_FUN_THM
unsafe def EXISTS_UNPAIR_FUN_THM := Pr.EXISTS_UNPAIR_FUN_THM
unsafe def EXISTS_SWAP_FUN_THM := Pr.EXISTS_SWAP_FUN_THM
unsafe def FORALL_PAIRED_THM := Pr.FORALL_PAIRED_THM
unsafe def EXISTS_PAIRED_THM := Pr.EXISTS_PAIRED_THM
unsafe def FORALL_TRIPLED_THM := Pr.FORALL_TRIPLED_THM
unsafe def EXISTS_TRIPLED_THM := Pr.EXISTS_TRIPLED_THM
unsafe def CHOICE_UNPAIR_THM := Pr.CHOICE_UNPAIR_THM
unsafe def CHOICE_PAIRED_THM := Pr.CHOICE_PAIRED_THM

/- ---------------------------------------------------------------------- -/
/- pair.ml: syntax operations                                             -/
/- ---------------------------------------------------------------------- -/

/-- `is_pair = is_binary ","` (`HolMath.Pair`). -/
def is_pair : term → Bool := HolMath.Pair.is_pair

/-- `dest_pair = dest_binary ","` (`HolMath.Pair`). -/
def dest_pair : term → Except String (term × term) := HolMath.Pair.dest_pair

/-- `lex` (parser.ml 102) on the current lexical tables. -/
def lex (chars : List String) : IO (Except String (List HolCore.Parser.lexcode)) := do
  match HolCore.Parser.lex (← HolCore.Parser.mkCtx) chars with
  | .ok l => return .ok l
  | .error e => return .error (HolCore.Parser.perrMsg e)

/-- `GABS_CONV conv` (pair.ml 200): apply `conv` to the body of a generalized
    abstraction `\(x,y). t`, or of an ordinary one. -/
unsafe def GABS_CONV (conv : ioconv) : ioconv := HolMath.Pair.GABS_CONV conv

/-- `mk_pair (l,r)`: build the pair `l,r` (`HolMath.Pair`). -/
def mk_pair : term × term → IO (Except String term) := HolMath.Pair.mk_pair

/- ---------------------------------------------------------------------- -/
/- pair.ml: extend `new_definition` to paired varstructs (benign check)   -/
/- ---------------------------------------------------------------------- -/

/- ---------------------------------------------------------------------- -/
/- Extend definitions to paired varstructs with benignity checking.       -/
/- (pair.ml 145)                                                          -/
/- ---------------------------------------------------------------------- -/

/-- `the_definitions`: the running list of definitions, for benign-redefinition
    checking (pair.ml `the_definitions` ref). Seeded with the pairing/sugar
    definitions plus the earlier core definitions. -/
initialize theDefinitions : IO.Ref (Option (List thm)) ← IO.mkRef none

private unsafe def theDefinitionsInit : List thm :=
  let P := pairAux
  [P.SND_DEF, P.FST_DEF, P.COMMA_DEF, P.mk_pair_def, P.GEQ_DEF, P.GABS_DEF,
   P.LET_END_DEF, P.LET_DEF,
   one_DEF, I_DEF, o_DEF, COND_DEF, falsityDef,
   B.EXISTS_UNIQUE_DEF, B.NOT_DEF, B.F_DEF, B.OR_DEF, B.EXISTS_DEF,
   B.FORALL_DEF, B.IMP_DEF, B.AND_DEF, B.T_DEF]

private unsafe def getTheDefinitions : IO (List thm) := do
  match ← theDefinitions.get with
  | some l => pure l
  | none => let l := theDefinitionsInit; theDefinitions.set (some l); pure l

/-- `!the_definitions` (pair.ml 148). -/
unsafe def get_the_definitions : IO (List thm) := getTheDefinitions
/-- `the_definitions := l`. -/
def set_the_definitions (l : List thm) : IO Unit := theDefinitions.set (some l)

/-- `new_definition` redefined to allow paired varstructs (pair.ml).  Depairs
    paired arguments on the LHS via `FST`/`SND`, defines the depaired equation
    with the primitive `new_definition`, then reconstitutes the paired form. -/
unsafe def new_definition_pair (tm : term) : IO (Except String thm) := ExceptT.run do
  -- depair gv arg : split a paired arg into (genvar, [(projected-gv, leaf)]).
  let rec depairAcc (gv arg : term) : IO (Except String (List (term × term))) := ExceptT.run do
    match dest_pair arg with
    | .ok (l, r) =>
        let fstGv ← ExceptT.mk (Basics.list_mk_icomb "FST" [gv])
        let sndGv ← ExceptT.mk (Basics.list_mk_icomb "SND" [gv])
        let ls ← ExceptT.mk (depairAcc fstGv l)
        let rs ← ExceptT.mk (depairAcc sndGv r)
        pure (ls ++ rs)
    | .error _ => pure [(gv, arg)]
  let depair (arg : term) : IO (Except String (term × List (term × term))) := ExceptT.run do
    let gv ← (Basics.genvar (type_of arg) : IO term)
    let reps ← ExceptT.mk (depairAcc gv arg)
    pure (gv, reps)
  let (avs, def0) := Basics.strip_forall tm
  -- Benign-redefinition check: try to PART_MATCH an existing definition.
  let idFn : term → Except String term := fun t => .ok t
  let defs ← getTheDefinitions
  -- `try let th,th' = tryfind (fun th -> th,PART_MATCH I th def) defs in
  --      ignore(PART_MATCH I th' ...); warn ...; GEN_ALL (GENL avs th')
  --  with Failure _ -> <define>`: the FIRST definition that matches decides;
  -- if its converse check fails, the whole `try` falls through to defining.
  let tryBenign : IO (Option thm) := do
    let rec first : List thm → IO (Option (thm × thm))
      | [] => pure none
      | th :: rest => do
        match ← (Drule.PART_MATCH B idFn th def0 : IO (Except String thm)) with
        | .ok th' => pure (some (th, th'))
        | .error _ => first rest
    match ← first defs with
    | none => pure none
    | some (th, th') =>
      match ← (Drule.PART_MATCH B idFn th' (Basics.strip_forall (concl th)).2 : IO (Except String thm)) with
      | .error _ => pure none
      | .ok _ =>
        HolCore.Lib.warn true "Benign redefinition"
        match (do B.GEN_ALL (← B.GENL avs th') : Except String thm) with
        | .ok r => pure (some r)
        | .error _ => pure none
  match ← tryBenign with
  | some r => pure r
  | none =>
    let (l, r) ← liftExcept (dest_eq def0)
    let (fn, args) := Basics.strip_comb l
    -- (gargs, reps) = (I F_F unions) (unzip (map depair args))
    let mut pairs : List (term × List (term × term)) := []
    for a in args do
      let p ← (depair a : IO (Except String (term × List (term × term))))
      pairs := pairs ++ [p]
    let gargs := pairs.map Prod.fst
    let reps := Lib.unions (pairs.map Prod.snd)
    let l' ← liftExcept (Basics.list_mk_comb fn gargs)
    let substFn ← (Basics.subst reps : IO (Except String (term → IO (Except String term))))
    let r' ← (substFn r : IO (Except String term))
    let eqtm := safe_mk_eq l' r'
    let th1 ← ExceptT.mk (Drule.new_definition B eqtm)
    let slist ← liftExcept (Lib.zip args gargs)
    let th2 ← liftExcept (Drule.INSTANTIATE ([], slist, []) (← SPEC_ALL th1))
    -- xreps = map (subst slist o fst) reps
    let substSl ← (Basics.subst slist : IO (Except String (term → IO (Except String term))))
    let mut xreps : List term := []
    for rep in reps do
      let x ← (substSl rep.1 : IO (Except String term))
      xreps := xreps ++ [x]
    -- threps = map (SYM o PURE_REWRITE_CONV[FST; SND]) xreps
    let mut threps : List thm := []
    for x in xreps do
      let c ← (Simp.PURE_REWRITE_CONV' B [FST, SND] x : IO (Except String thm))
      threps := threps ++ [(← liftExcept (Equal.SYM c))]
    -- th3 = TRANS th2 (SYM (SUBS_CONV threps r))
    let subsc ← ExceptT.mk (Equal.SUBS_CONV threps r)
    let th3 ← liftExcept (do TRANS th2 (← Equal.SYM subsc))
    let th4 ← liftExcept (do B.GEN_ALL (← B.GENL avs th3))
    -- `the_definitions := th4::(!the_definitions)` (pair.ml 181).
    theDefinitions.set (some (th4 :: (← getTheDefinitions)))
    pure th4

/-- `new_definition` from pair.ml 154 on.  pair.ml rebinds the name, so every
    later file (nums.ml onwards, and the toplevel) gets this version, whose
    `GEN_ALL` result quantifies the variables in `frees` order (`GE` is
    `!n m. m >= n <=> n <= m`) and which records `the_definitions`.  The
    drule.ml primitive stays `Drule.new_definition`, used by the earlier files. -/
unsafe def new_definition : term → IO (Except String thm) := new_definition_pair

/-- CURRY/UNCURRY/PASSOC (pair.ml), defined via the depairing `new_definition`. -/
initialize theCurryDefs : IO.Ref (Option (thm × thm × thm)) ← IO.mkRef none

private unsafe def curryDefs : thm × thm × thm :=
  match unsafeIO (do
    match ← theCurryDefs.get with
    | some x => pure x
    | none =>
      let defP (label s : String) : IO thm := do
        let tm ← (match ← HolCore.Parser.parse_term s with
                  | .ok t => pure t | .error e => panic! s!"{label} parse: {e}")
        match ← (new_definition_pair tm : IO (Except String thm)) with
        | .ok t => pure t | .error e => panic! s!"{label}: {e}"
      -- A few more useful definitions.  (pair.ml 184)
      -- pair.ml up to 183 (the prod type, its theorems and store entry) first.
      let _ ← IO.mkRef (concl Pr.PAIR_EQ)
      let curryD ← defP "CURRY_DEF" "CURRY(f:A#B->C) x y = f(x,y)"
      let uncurryD ← defP "UNCURRY_DEF" "!f x y. UNCURRY(f:A->B->C)(x,y) = f x y"
      let passocD ← defP "PASSOC_DEF" "!f x y z. PASSOC (f:(A#B)#C->D) (x,y,z) = f ((x,y),z)"
      let x := (curryD, uncurryD, passocD)
      theCurryDefs.set (some x); pure x) with
  | .ok x => x | _ => panic! "Session.curryDefs: not initialised"

unsafe def CURRY_DEF : thm := curryDefs.1
unsafe def UNCURRY_DEF : thm := curryDefs.2.1
unsafe def PASSOC_DEF : thm := curryDefs.2.2

/- ---------------------------------------------------------------------- -/
/- Expansion of a let-term; SUBLET_CONV; LET_TAC.  The conversions and the-/
/- tactic live in `HolMath.Pair`; only the definitions/lemmas they close  -/
/- over are session state.                                                -/
/- ---------------------------------------------------------------------- -/

initialize theLetTacPth : IO.Ref (Option (thm × thm × thm)) ← IO.mkRef none

private unsafe def letTacPths : thm × thm × thm :=
  match unsafeIO (do
    match ← theLetTacPth.get with
    | some x => pure x
    | none =>
      let goal ← (match ← HolCore.Parser.parse_term "((x,y) = a) <=> (x = FST a) /\\ (y = SND a)" with
                  | .ok t => pure t | .error e => panic! s!"LET_TAC pth parse: {e}")
      let pth ← (match ← (MESON [PAIR, PAIR_EQ] goal : IO (Except String thm)) with
                 | .ok t => pure t | .error e => panic! s!"LET_TAC pth: {e}")
      -- OCaml builds the list [TAUT ..; TAUT ..] right to left.
      let taut2 ← (match ← (TAUT (← (match ← HolCore.Parser.parse_term "a /\\ T <=> a" with
                    | .ok t => pure t | .error e => panic! e)) : IO (Except String thm)) with
                   | .ok t => pure t | .error e => panic! s!"LET_TAC taut2: {e}")
      let taut1 ← (match ← (TAUT (← (match ← HolCore.Parser.parse_term "(x = x) <=> T" with
                    | .ok t => pure t | .error e => panic! e)) : IO (Except String thm)) with
                   | .ok t => pure t | .error e => panic! s!"LET_TAC taut1: {e}")
      let x := (pth, taut1, taut2)
      theLetTacPth.set (some x); pure x) with
  | .ok x => x | _ => panic! "Session.letTacPths"

/-- The definitions/lemmas the `let` machinery closes over
    (`HolMath.Pair.LetDeps`). -/
private unsafe def letDeps : HolMath.Pair.LetDeps :=
  { LET_DEF     := pairAux.LET_DEF
    LET_END_DEF := pairAux.LET_END_DEF
    letTacPth   := letTacPths.1
    taut1       := letTacPths.2.1
    taut2       := letTacPths.2.2 }

/-- `let_CONV`: expand a `let`-term (pair.ml). -/
unsafe def let_CONV : term → IO (Except String thm) :=
  HolMath.Pair.let_CONV letDeps GEN_BETA_CONV

/-- `SUBLET_CONV conv`: apply `conv` to the RHS of a top-level `let`-term. -/
def SUBLET_CONV : ioconv → term → IO (Except String thm) :=
  HolMath.Pair.SUBLET_CONV

/-- `LET_TAC` (pair.ml). -/
unsafe def LET_TAC : tactic := HolMath.Pair.LET_TAC letDeps GEN_BETA_CONV

/- ---------------------------------------------------------------------- -/
/- compute.ml : call-by-value reduction of terms (HOL4's computeLib).     -/
/- The pure library lives in `HolMath.Compute`; the module-level mutable  -/
/- state (the flags and the global compset) lives here.                   -/
/- ---------------------------------------------------------------------- -/

/-- `monitoring`: when `Some p`, the instance of each rewrite rule used to reduce
    a constant satisfying `p` is printed. -/
initialize monitoring : IO.Ref (Option (term → Bool)) ← IO.mkRef none

/-- `stoppers`: when `Some p`, reduction stops at constants satisfying `p`
    (this is how `RESTR_EVAL_CONV` restricts evaluation). -/
initialize stoppers : IO.Ref (Option (term → Bool)) ← IO.mkRef none

/-- The two `compute.ml` module-level flags, bundled for the pure library. -/
private def computeFlags : HolMath.Compute.ComputeFlags :=
  { monitoring := monitoring, stoppers := stoppers }

/-- The `t:A->B` witness that `ETA_CONV`/`try_eta` instantiate: compute.ml
    calls class.ml's ETA_CONV, so it is ETA_CONV's own `t`. -/
private unsafe def computeEtaT : term := C.etaT

/-- The `COND` constant, whose branches `CBV_CONV` is told to skip.  An action:
    compute.ml parses the quotation in each `bool_compset ()` and
    `basic_compset ()` call. -/
private unsafe def condTm : IO term := do
  match ← HolCore.Parser.parse_term "COND: bool -> A -> A -> A" with
  | .ok t => pure t | .error e => panic! s!"Session.condTm: {e}"

/-- The `LET` constant, to which `let_CONV` is attached at arity 2 (parsed in
    each `basic_compset ()` call, as in compute.ml). -/
private unsafe def letTm : IO term := do
  match ← HolCore.Parser.parse_term "LET:(A->B)->A->B" with
  | .ok t => pure t | .error e => panic! s!"Session.letTm: {e}"

/-- `lazyfy_thm`: use a lazy rule to avoid computing arguments. -/
unsafe def lazyfy_thm : thm → IO (Except String thm) :=
  HolMath.Compute.lazyfy_thm ETA_AX

/-- `strictify_thm`: the converse of `lazyfy_thm`. -/
unsafe def strictify_thm : thm → Except String thm :=
  HolMath.Compute.strictify_thm

/-- `new_compset`: a compset built from a list of rewrite theorems. -/
unsafe def new_compset (lthm : List thm) : IO (Except String HolMath.Compute.compset) :=
  HolMath.Compute.from_list REFL_CLAUSE lthm

/-- `bool_compset ()`: the boolean reductions. -/
unsafe def bool_compset : IO (Except String HolMath.Compute.compset) :=
  HolMath.Compute.bool_compset ETA_AX REFL_CLAUSE LET_DEF COND_CLAUSES COND_ID
    NOT_CLAUSES AND_CLAUSES OR_CLAUSES IMP_CLAUSES EQ_CLAUSES condTm

/-- `basic_compset ()`: the boolean reductions plus the basic rewrites and
    conversions, and `let_CONV`. -/
unsafe def basic_compset : IO (Except String HolMath.Compute.compset) :=
  HolMath.Compute.basic_compset ETA_AX REFL_CLAUSE SELECT_REFL FORALL_SIMP
    EXISTS_SIMP letTm let_CONV condTm

/-- `add_thms`: add rewrite theorems to a compset. -/
unsafe def add_thms (lthm : List thm) (cs : HolMath.Compute.compset) :
    IO (Except String Unit) :=
  HolMath.Compute.add_thms lthm cs

/-- `add_conv (cst, arity, conv)`: attach a conversion to a constant. -/
def add_conv (cst : term) (arity : Int) (conv : ioconv)
    (cs : HolMath.Compute.compset) : IO (Except String Unit) :=
  HolMath.Compute.add_conv cst arity conv cs

/-- `set_skip`: mark arguments of a constant as not to be evaluated. -/
def set_skip (cs : HolMath.Compute.compset) (c : term) (opt : Option Int) :
    IO (Except String Unit) :=
  HolMath.Compute.set_skip cs c opt

/-- `scrub_const`: remove all rules attached to a constant. -/
def scrub_const (cs : HolMath.Compute.compset) (c : term) :
    IO (Except String Unit) :=
  HolMath.Compute.scrub_const cs c

/-- `scrub_thms`: remove the rules of the given theorems. -/
unsafe def scrub_thms (lthm : List thm) (cs : HolMath.Compute.compset) :
    IO (Except String Unit) :=
  HolMath.Compute.scrub_thms lthm cs

/-- `CBV_CONV rws`: full call-by-value normalization. -/
unsafe def CBV_CONV (cs : HolMath.Compute.compset) : term → IO (Except String thm) :=
  HolMath.Compute.CBV_CONV computeFlags C.etaPth computeEtaT cs

/-- `WEAK_CBV_CONV rws`: as `CBV_CONV`, but does not reduce under abstractions. -/
unsafe def WEAK_CBV_CONV (cs : HolMath.Compute.compset) : term → IO (Except String thm) :=
  HolMath.Compute.WEAK_CBV_CONV computeFlags cs

/-- `listItems`: the transforms attached to each constant of a compset. -/
def listItems (cs : HolMath.Compute.compset) :
    IO (List (String × List HolMath.Compute.transform)) :=
  HolMath.Compute.deplist cs

/-- The global compset, `the_compset = bool_compset()`. -/
initialize theComputeCompset : IO.Ref (Option HolMath.Compute.compset) ← IO.mkRef none

/-- `the_compset`.  OCaml evaluates `bool_compset()` once at module
    initialization; the compset is mutable and shared, so it is built on first
    use and cached. -/
unsafe def the_compset : IO HolMath.Compute.compset := do
  match ← theComputeCompset.get with
  | some cs => pure cs
  | none =>
    match ← bool_compset with
    | .error e => throw (IO.userError s!"Session.the_compset: {e}")
    | .ok cs => do theComputeCompset.set (some cs); pure cs

/-- `add_funs`: add rewrite theorems to the global compset. -/
unsafe def add_funs (lthm : List thm) : IO (Except String Unit) := do
  add_thms lthm (← the_compset)

/-- `add_convs`: add conversions to the global compset. -/
unsafe def add_convs (l : List (term × Int × ioconv)) : IO (Except String Unit) := do
  let cs ← the_compset
  for (cst, arity, conv) in l do
    match ← add_conv cst arity conv cs with
    | .error e => return .error e
    | .ok _ => pure ()
  return .ok ()

/-- `del_consts`: remove all rules for the given constants from the global
    compset. -/
unsafe def del_consts (l : List term) : IO (Except String Unit) := do
  let cs ← the_compset
  for c in l do
    match ← scrub_const cs c with
    | .error e => return .error e
    | .ok _ => pure ()
  return .ok ()

/-- `del_funs`: remove the given theorems' rules from the global compset. -/
unsafe def del_funs (lthm : List thm) : IO (Except String Unit) := do
  scrub_thms lthm (← the_compset)

/-- `EVAL_CONV`: call-by-value evaluation with the global compset. -/
unsafe def EVAL_CONV : term → IO (Except String thm) :=
  fun t => do CBV_CONV (← the_compset) t

/-- `EVAL_RULE`. -/
unsafe def EVAL_RULE : thm → IO (Except String thm) := Simp.convRuleIO EVAL_CONV

/-- `EVAL_TAC`. -/
unsafe def EVAL_TAC : tactic := CONV_TAC EVAL_CONV

/-- `OR clist`: does a term match any of the constants in `clist`? -/
def OR : List term → term → Bool := HolMath.Compute.OR

/-- `RESTR_EVAL_CONV clist`: evaluate, but stop at the constants in `clist`. -/
unsafe def RESTR_EVAL_CONV (clist : List term) : term → IO (Except String thm) :=
  HolMath.Compute.with_flag stoppers (some (HolMath.Compute.OR clist)) EVAL_CONV

/-- `RESTR_EVAL_TAC`. -/
unsafe def RESTR_EVAL_TAC (clist : List term) : tactic :=
  CONV_TAC (RESTR_EVAL_CONV clist)

/-- `RESTR_EVAL_RULE`. -/
unsafe def RESTR_EVAL_RULE (clist : List term) : thm → IO (Except String thm) :=
  Simp.convRuleIO (RESTR_EVAL_CONV clist)

/- ---------------------------------------------------------------------- -/
/- nums.ml : the axiom of infinity and the natural numbers.               -/
/- ---------------------------------------------------------------------- -/

/-- Cache for the `nums.ml` layer (runs the whole nums.ml script once). -/
initialize theNums : IO.Ref (Option HolMath.Nums.NumsThms) ← IO.mkRef none

private unsafe def Nm : HolMath.Nums.NumsThms :=
  match unsafeIO (do
    match ← theNums.get with
    | some t => pure t
    | none =>
      match ← (HolMath.Nums.setupNums new_definition MESON_TAC SELECT_RULE
                 new_inductive_definition prove_inductive_relations_exist).run with
      | .ok t => do
          theNums.set (some t)
          -- inductive_type_store := ("num",(2,num_INDUCTION,num_RECURSION))::(!...)
          let cur ← theInductiveTypeStore.get
          let base := cur.getD [("bool", (2, C.bool_INDUCT, C.bool_RECURSION))]
          theInductiveTypeStore.set
            (some (("num", (2, t.num_INDUCTION, t.num_RECURSION)) :: base))
          pure t
      | .error e => panic! s!"setupNums failed: {e}") with
  | .ok t => t | _ => panic! "Session.Nm: setupNums not run"

-- Expose the nums.ml definitions and theorems.
unsafe def ONE_ONE          : thm := Nm.ONE_ONE
unsafe def ONTO             : thm := Nm.ONTO
unsafe def INFINITY_AX      : thm := Nm.INFINITY_AX
unsafe def IND_SUC_0_EXISTS : thm := Nm.IND_SUC_0_EXISTS
unsafe def IND_SUC_SPEC     : thm := Nm.IND_SUC_SPEC
unsafe def IND_SUC_INJ      : thm := Nm.IND_SUC_INJ
unsafe def IND_SUC_0        : thm := Nm.IND_SUC_0
unsafe def NUM_REP_RULES    : thm := Nm.NUM_REP_RULES
unsafe def NUM_REP_INDUCT   : thm := Nm.NUM_REP_INDUCT
unsafe def NUM_REP_CASES    : thm := Nm.NUM_REP_CASES
unsafe def num_tydef        : thm × thm := Nm.num_tydef
unsafe def ZERO_DEF         : thm := Nm.ZERO_DEF
unsafe def SUC_DEF          : thm := Nm.SUC_DEF
unsafe def NOT_SUC          : thm := Nm.NOT_SUC
unsafe def SUC_INJ          : thm := Nm.SUC_INJ
unsafe def num_INDUCTION    : thm := Nm.num_INDUCTION
unsafe def num_Axiom        : thm := Nm.num_Axiom
unsafe def NUMERAL          : thm := Nm.NUMERAL
unsafe def num_RECURSION    : thm := Nm.num_RECURSION
unsafe def num_CASES        : thm := Nm.num_CASES
unsafe def BIT0_DEF         : thm := Nm.BIT0_DEF
unsafe def BIT1_DEF         : thm := Nm.BIT1_DEF

/-- `INDUCT_TAC` (nums.ml), over the rewritten `num_INDUCTION`. -/
unsafe def INDUCT_TAC : tactic := HolMath.Nums.INDUCT_TAC num_INDUCTION

/-- `mk_numeral`. -/
unsafe def mk_numeral (n : Rat) : Except String term := HolMath.Nums.mk_numeral Nm.numK n
/-- The `num` numeral constants (for library code that builds a Grobner
    `RingCtx`, as ringtheory.ml's `RING_AND_IDEAL_CONV` calls do). -/
unsafe def numeralConstsNum : HolMath.Nums.NumeralConsts := Nm.numK

/-- `mk_small_numeral`. -/
unsafe def mk_small_numeral (n : Int) : Except String term :=
  HolMath.Nums.mk_small_numeral Nm.numK n

/-- `dest_small_numeral`. -/
def dest_small_numeral : term → Except String Int := HolMath.Nums.dest_small_numeral

/-- `is_numeral`. -/
def is_numeral : term → Bool := HolMath.Nums.is_numeral

/-- `the_specifications`: the constants introduced by `new_specification`. -/
initialize theSpecifications : IO.Ref (List HolMath.Nums.specification) ← IO.mkRef []
/- This is put here because we use numerals as tags to force different    -/
/- constants specified with equivalent theorems to have different         -/
/- underlying definitions, ensuring that there are no provable            -/
/- equalities between them and so in some sense the constants are         -/
/- "underspecified" as the user might want for some applications.         -/

/-- `new_specification names th`: a derived principle of definition based on
    existence.  Benign respecifications reuse the stored theorem. -/
unsafe def new_specification (names : List String) (th : thm) :
    IO (Except String thm) := do
  -- `new_specification` tags constants with pair-coded numerals, so pair.ml's
  -- `,` must be declared.  OCaml's load order guarantees this (pair.ml precedes
  -- nums.ml); with our lazy bootstrap the pair layer is forced explicitly.
  let _ ← IO.mkRef (concl mk_pair_def)
  let existing ← theSpecifications.get
  match ← (HolMath.Nums.new_specification_core Nm.numK new_definition existing names th
            : IO (Except String (thm × Option HolMath.Nums.specification))) with
  | .error e => return .error e
  | .ok (sth, entry) => do
      match entry with
      | some e => theSpecifications.set (e :: existing)
      | none => pure ()
      return .ok sth

/- ---------------------------------------------------------------------- -/
/- recursion.ml : definition by primitive recursion.                      -/
/- ---------------------------------------------------------------------- -/

/-- `prove_recursive_functions_exist ax tm`. -/
unsafe def prove_recursive_functions_exist (ax : thm) (tm : term) :
    IO (Except String thm) :=
  HolMath.Recursion.prove_recursive_functions_exist T.BETA_THM ax tm

/-- `prove_canon_recursive_functions_exist ax tm`. -/
unsafe def prove_canon_recursive_functions_exist (ax : thm) (tm : term) :
    IO (Except String thm) :=
  HolMath.Recursion.prove_canon_recursive_functions_exist ax tm

/-- `prove_raw_recursive_functions_exist ax tm`. -/
unsafe def prove_raw_recursive_functions_exist (ax : thm) (tm : term) :
    IO (Except String thm) :=
  HolMath.Recursion.prove_raw_recursive_functions_exist ax tm

/-- `the_recursive_definitions`. -/
initialize theRecursiveDefinitions : IO.Ref (List thm) ← IO.mkRef []

/-- `new_recursive_definition ax tm`: define function(s) by primitive recursion.
    Benign redefinitions reuse the stored theorem. -/
unsafe def new_recursive_definition (ax : thm) (tm : term) :
    IO (Except String thm) := do
  let existing ← theRecursiveDefinitions.get
  match ← (HolMath.Recursion.new_recursive_definition_core T.BETA_THM
             new_specification existing ax tm : IO (Except String (thm × Option thm))) with
  | .error e => return .error e
  | .ok (th, entry) => do
      match entry with
      | some t => theRecursiveDefinitions.set (t :: existing)
      | none => pure ()
      return .ok th

/- ---------------------------------------------------------------------- -/
/- arith.ml : natural number arithmetic.                                  -/
/- ---------------------------------------------------------------------- -/

/-- Cache for `arith.ml` part 1. -/
initialize theArith1 : IO.Ref (Option HolMath.Arith.ArithThms1) ← IO.mkRef none

private unsafe def Ar1 : HolMath.Arith.ArithThms1 :=
  match unsafeIO (do
    match ← theArith1.get with
    | some t => pure t
    | none => do
      -- arith.ml registers its infixes at the top of the file, before any
      -- arithmetic term is parsed.
      HolMath.Arith.setupArithInfixes
      match ← (HolMath.Arith.setupArith1 Nm MESON_TAC new_recursive_definition).run with
      | .ok t => do theArith1.set (some t); pure t
      | .error e => panic! s!"setupArith1 failed: {e}") with
  | .ok t => t | _ => panic! "Session.Ar1: setupArith1 not run"

unsafe def PRE              : thm := Ar1.PRE
unsafe def ADD              : thm := Ar1.ADD
unsafe def ADD_0            : thm := Ar1.ADD_0
unsafe def ADD_SUC          : thm := Ar1.ADD_SUC
unsafe def ADD_CLAUSES      : thm := Ar1.ADD_CLAUSES
unsafe def ADD_SYM          : thm := Ar1.ADD_SYM
unsafe def ADD_ASSOC        : thm := Ar1.ADD_ASSOC
unsafe def ADD_AC           : thm := Ar1.ADD_AC
unsafe def ADD_EQ_0         : thm := Ar1.ADD_EQ_0
unsafe def EQ_ADD_LCANCEL   : thm := Ar1.EQ_ADD_LCANCEL
unsafe def EQ_ADD_RCANCEL   : thm := Ar1.EQ_ADD_RCANCEL
unsafe def EQ_ADD_LCANCEL_0 : thm := Ar1.EQ_ADD_LCANCEL_0
unsafe def EQ_ADD_RCANCEL_0 : thm := Ar1.EQ_ADD_RCANCEL_0
unsafe def BIT0             : thm := Ar1.BIT0
unsafe def BIT1             : thm := Ar1.BIT1
unsafe def BIT0_THM         : thm := Ar1.BIT0_THM
unsafe def BIT1_THM         : thm := Ar1.BIT1_THM
unsafe def ONE              : thm := Ar1.ONE
unsafe def TWO              : thm := Ar1.TWO
unsafe def ADD1             : thm := Ar1.ADD1

/-- Cache for `arith.ml` part 2. -/
initialize theArith2 : IO.Ref (Option HolMath.Arith.ArithThms2) ← IO.mkRef none

private unsafe def Ar2 : HolMath.Arith.ArithThms2 :=
  match unsafeIO (do
    match ← theArith2.get with
    | some t => pure t
    | none => do
      match ← (HolMath.Arith.setupArith2 Nm new_definition Ar1 MESON_TAC
                 new_recursive_definition).run with
      | .ok t => do theArith2.set (some t); pure t
      | .error e => panic! s!"setupArith2 failed: {e}") with
  | .ok t => t | _ => panic! "Session.Ar2: setupArith2 not run"

unsafe def MULT             : thm := Ar2.MULT
unsafe def MULT_0           : thm := Ar2.MULT_0
unsafe def MULT_SUC         : thm := Ar2.MULT_SUC
unsafe def MULT_CLAUSES     : thm := Ar2.MULT_CLAUSES
unsafe def MULT_SYM         : thm := Ar2.MULT_SYM
unsafe def LEFT_ADD_DISTRIB : thm := Ar2.LEFT_ADD_DISTRIB
unsafe def RIGHT_ADD_DISTRIB : thm := Ar2.RIGHT_ADD_DISTRIB
unsafe def MULT_ASSOC       : thm := Ar2.MULT_ASSOC
unsafe def MULT_AC          : thm := Ar2.MULT_AC
unsafe def MULT_EQ_0        : thm := Ar2.MULT_EQ_0
unsafe def EQ_MULT_LCANCEL  : thm := Ar2.EQ_MULT_LCANCEL
unsafe def EQ_MULT_RCANCEL  : thm := Ar2.EQ_MULT_RCANCEL
unsafe def MULT_2           : thm := Ar2.MULT_2
unsafe def MULT_EQ_1        : thm := Ar2.MULT_EQ_1
unsafe def EXP              : thm := Ar2.EXP
unsafe def EXP_EQ_0         : thm := Ar2.EXP_EQ_0
unsafe def EXP_EQ_1         : thm := Ar2.EXP_EQ_1
unsafe def EXP_ZERO         : thm := Ar2.EXP_ZERO
unsafe def EXP_ADD          : thm := Ar2.EXP_ADD
unsafe def EXP_ONE          : thm := Ar2.EXP_ONE
unsafe def EXP_1            : thm := Ar2.EXP_1
unsafe def EXP_2            : thm := Ar2.EXP_2
unsafe def MULT_EXP         : thm := Ar2.MULT_EXP
unsafe def EXP_MULT         : thm := Ar2.EXP_MULT
unsafe def EXP_EXP          : thm := Ar2.EXP_EXP
unsafe def LE               : thm := Ar2.LE
unsafe def LT               : thm := Ar2.LT
unsafe def GE               : thm := Ar2.GE
unsafe def GT               : thm := Ar2.GT
unsafe def MAX              : thm := Ar2.MAX
unsafe def MIN              : thm := Ar2.MIN
unsafe def LE_SUC_LT        : thm := Ar2.LE_SUC_LT
unsafe def LT_SUC_LE        : thm := Ar2.LT_SUC_LE
unsafe def LE_SUC           : thm := Ar2.LE_SUC
unsafe def LT_SUC           : thm := Ar2.LT_SUC
unsafe def LE_0             : thm := Ar2.LE_0
unsafe def LT_0             : thm := Ar2.LT_0

/-- Cache for `arith.ml` part 3. -/
initialize theArith3 : IO.Ref (Option HolMath.Arith.ArithThms3) ← IO.mkRef none

private unsafe def Ar3 : HolMath.Arith.ArithThms3 :=
  match unsafeIO (do
    match ← theArith3.get with
    | some t => pure t
    | none => do
      match ← (HolMath.Arith.setupArith3 Nm Ar1 Ar2 MESON_TAC).run with
      | .ok t => do theArith3.set (some t); pure t
      | .error e => panic! s!"setupArith3 failed: {e}") with
  | .ok t => t | _ => panic! "Session.Ar3: setupArith3 not run"

unsafe def LE_REFL          : thm := Ar3.LE_REFL
unsafe def LT_REFL          : thm := Ar3.LT_REFL
unsafe def LT_IMP_NE        : thm := Ar3.LT_IMP_NE
unsafe def LE_ANTISYM       : thm := Ar3.LE_ANTISYM
unsafe def LT_ANTISYM       : thm := Ar3.LT_ANTISYM
unsafe def LET_ANTISYM      : thm := Ar3.LET_ANTISYM
unsafe def LTE_ANTISYM      : thm := Ar3.LTE_ANTISYM
unsafe def LE_TRANS         : thm := Ar3.LE_TRANS
unsafe def LT_TRANS         : thm := Ar3.LT_TRANS
unsafe def LET_TRANS        : thm := Ar3.LET_TRANS
unsafe def LTE_TRANS        : thm := Ar3.LTE_TRANS
unsafe def LE_CASES         : thm := Ar3.LE_CASES
unsafe def LT_CASES         : thm := Ar3.LT_CASES
unsafe def LET_CASES        : thm := Ar3.LET_CASES
unsafe def LTE_CASES        : thm := Ar3.LTE_CASES
unsafe def LE_LT            : thm := Ar3.LE_LT
unsafe def LT_LE            : thm := Ar3.LT_LE
unsafe def NOT_LE           : thm := Ar3.NOT_LE
unsafe def NOT_LT           : thm := Ar3.NOT_LT
unsafe def LT_IMP_LE        : thm := Ar3.LT_IMP_LE
unsafe def EQ_IMP_LE        : thm := Ar3.EQ_IMP_LE
unsafe def LT_NZ            : thm := Ar3.LT_NZ
unsafe def LE_1             : thm := Ar3.LE_1

/-- Cache for `arith.ml` part 4. -/
initialize theArith4 : IO.Ref (Option HolMath.Arith.ArithThms4) ← IO.mkRef none

private unsafe def Ar4 : HolMath.Arith.ArithThms4 :=
  match unsafeIO (do
    match ← theArith4.get with
    | some t => pure t
    | none => do
      match ← (HolMath.Arith.setupArith4 Nm Ar1 Ar2 Ar3 MESON_TAC
                 ASM_MESON_TAC MESON).run with
      | .ok t => do theArith4.set (some t); pure t
      | .error e => panic! s!"setupArith4 failed: {e}") with
  | .ok t => t | _ => panic! "Session.Ar4: setupArith4 not run"

unsafe def LE_EXISTS          : thm := Ar4.LE_EXISTS
unsafe def LT_EXISTS          : thm := Ar4.LT_EXISTS
unsafe def LE_ADD             : thm := Ar4.LE_ADD
unsafe def LE_ADDR            : thm := Ar4.LE_ADDR
unsafe def LT_ADD             : thm := Ar4.LT_ADD
unsafe def LT_ADDR            : thm := Ar4.LT_ADDR
unsafe def LE_ADD_LCANCEL     : thm := Ar4.LE_ADD_LCANCEL
unsafe def LE_ADD_RCANCEL     : thm := Ar4.LE_ADD_RCANCEL
unsafe def LT_ADD_LCANCEL     : thm := Ar4.LT_ADD_LCANCEL
unsafe def LT_ADD_RCANCEL     : thm := Ar4.LT_ADD_RCANCEL
unsafe def LE_ADD2            : thm := Ar4.LE_ADD2
unsafe def LET_ADD2           : thm := Ar4.LET_ADD2
unsafe def LTE_ADD2           : thm := Ar4.LTE_ADD2
unsafe def LT_ADD2            : thm := Ar4.LT_ADD2
unsafe def LT_MULT            : thm := Ar4.LT_MULT
unsafe def LE_MULT2           : thm := Ar4.LE_MULT2
unsafe def LT_LMULT           : thm := Ar4.LT_LMULT
unsafe def LE_MULT_LCANCEL    : thm := Ar4.LE_MULT_LCANCEL
unsafe def LE_MULT_RCANCEL    : thm := Ar4.LE_MULT_RCANCEL
unsafe def LT_MULT_LCANCEL    : thm := Ar4.LT_MULT_LCANCEL
unsafe def LT_MULT_RCANCEL    : thm := Ar4.LT_MULT_RCANCEL
unsafe def LT_MULT2           : thm := Ar4.LT_MULT2
unsafe def LE_SQUARE_REFL     : thm := Ar4.LE_SQUARE_REFL
unsafe def LT_POW2_REFL       : thm := Ar4.LT_POW2_REFL
unsafe def WLOG_LE            : thm := Ar4.WLOG_LE
unsafe def WLOG_LT            : thm := Ar4.WLOG_LT
unsafe def WLOG_LE_3          : thm := Ar4.WLOG_LE_3
unsafe def num_WF             : thm := Ar4.num_WF
unsafe def num_WOP            : thm := Ar4.num_WOP
unsafe def num_MAX            : thm := Ar4.num_MAX
unsafe def LE_INDUCT          : thm := Ar4.LE_INDUCT
unsafe def num_INDUCTION_DOWN : thm := Ar4.num_INDUCTION_DOWN

/-- Cache for `arith.ml` part 5. -/
initialize theArith5 : IO.Ref (Option HolMath.Arith.ArithThms5) ← IO.mkRef none

private unsafe def Ar5 : HolMath.Arith.ArithThms5 :=
  match unsafeIO (do
    match ← theArith5.get with
    | some t => pure t
    | none => do
      match ← (HolMath.Arith.setupArith5 Nm Ar1 Ar2 Ar3 Ar4 MESON_TAC
                 ASM_MESON_TAC new_recursive_definition).run with
      | .ok t => do theArith5.set (some t); pure t
      | .error e => panic! s!"setupArith5 failed: {e}") with
  | .ok t => t | _ => panic! "Session.Ar5: setupArith5 not run"

unsafe def EVEN                   : thm := Ar5.EVEN
unsafe def ODD                    : thm := Ar5.ODD
unsafe def NOT_EVEN               : thm := Ar5.NOT_EVEN
unsafe def NOT_ODD                : thm := Ar5.NOT_ODD
unsafe def EVEN_OR_ODD            : thm := Ar5.EVEN_OR_ODD
unsafe def EVEN_AND_ODD           : thm := Ar5.EVEN_AND_ODD
unsafe def EVEN_ADD               : thm := Ar5.EVEN_ADD
unsafe def EVEN_MULT              : thm := Ar5.EVEN_MULT
unsafe def EVEN_EXP               : thm := Ar5.EVEN_EXP
unsafe def ODD_ADD                : thm := Ar5.ODD_ADD
unsafe def ODD_MULT               : thm := Ar5.ODD_MULT
unsafe def ODD_EXP                : thm := Ar5.ODD_EXP
unsafe def EVEN_DOUBLE            : thm := Ar5.EVEN_DOUBLE
unsafe def ODD_DOUBLE             : thm := Ar5.ODD_DOUBLE
unsafe def EVEN_EXISTS_LEMMA      : thm := Ar5.EVEN_EXISTS_LEMMA
unsafe def EVEN_EXISTS            : thm := Ar5.EVEN_EXISTS
unsafe def ODD_EXISTS             : thm := Ar5.ODD_EXISTS
unsafe def EVEN_ODD_DECOMPOSITION : thm := Ar5.EVEN_ODD_DECOMPOSITION
unsafe def SUB                    : thm := Ar5.SUB
unsafe def SUB_0                  : thm := Ar5.SUB_0
unsafe def SUB_PRESUC             : thm := Ar5.SUB_PRESUC
unsafe def SUB_SUC                : thm := Ar5.SUB_SUC
unsafe def SUB_REFL               : thm := Ar5.SUB_REFL
unsafe def ADD_SUB                : thm := Ar5.ADD_SUB
unsafe def ADD_SUB2               : thm := Ar5.ADD_SUB2
unsafe def SUB_EQ_0               : thm := Ar5.SUB_EQ_0
unsafe def ADD_SUBR2              : thm := Ar5.ADD_SUBR2
unsafe def ADD_SUBR               : thm := Ar5.ADD_SUBR
unsafe def SUB_ADD                : thm := Ar5.SUB_ADD
unsafe def SUB_ADD_LCANCEL        : thm := Ar5.SUB_ADD_LCANCEL
unsafe def SUB_ADD_RCANCEL        : thm := Ar5.SUB_ADD_RCANCEL
unsafe def LEFT_SUB_DISTRIB       : thm := Ar5.LEFT_SUB_DISTRIB
unsafe def RIGHT_SUB_DISTRIB      : thm := Ar5.RIGHT_SUB_DISTRIB
unsafe def SUC_SUB1               : thm := Ar5.SUC_SUB1
unsafe def EVEN_SUB               : thm := Ar5.EVEN_SUB
unsafe def ODD_SUB                : thm := Ar5.ODD_SUB
unsafe def FACT                   : thm := Ar5.FACT
unsafe def FACT_LT                : thm := Ar5.FACT_LT
unsafe def FACT_LE                : thm := Ar5.FACT_LE
unsafe def FACT_NZ                : thm := Ar5.FACT_NZ
unsafe def FACT_MONO              : thm := Ar5.FACT_MONO

/-- Cache for `arith.ml` part 6. -/
initialize theArith6 : IO.Ref (Option HolMath.Arith.ArithThms6) ← IO.mkRef none

private unsafe def Ar6 : HolMath.Arith.ArithThms6 :=
  match unsafeIO (do
    match ← theArith6.get with
    | some t => pure t
    | none => do
      match ← (HolMath.Arith.setupArith6 Nm Ar1 Ar2 Ar3 Ar4
                 ASM_MESON_TAC).run with
      | .ok t => do theArith6.set (some t); pure t
      | .error e => panic! s!"setupArith6 failed: {e}") with
  | .ok t => t | _ => panic! "Session.Ar6: setupArith6 not run"

unsafe def EXP_LT_0        : thm := Ar6.EXP_LT_0
unsafe def LT_EXP          : thm := Ar6.LT_EXP
unsafe def LE_EXP          : thm := Ar6.LE_EXP
unsafe def EQ_EXP          : thm := Ar6.EQ_EXP
unsafe def EXP_MONO_LE_IMP : thm := Ar6.EXP_MONO_LE_IMP
unsafe def EXP_MONO_LT_IMP : thm := Ar6.EXP_MONO_LT_IMP
unsafe def EXP_MONO_LE     : thm := Ar6.EXP_MONO_LE
unsafe def EXP_MONO_LT     : thm := Ar6.EXP_MONO_LT
unsafe def EXP_MONO_EQ     : thm := Ar6.EXP_MONO_EQ


/-- Cache for `arith.ml` part 7. -/
initialize theArith7 : IO.Ref (Option HolMath.Arith.ArithThms7) ← IO.mkRef none

private unsafe def Ar7 : HolMath.Arith.ArithThms7 :=
  match unsafeIO (do
    match ← theArith7.get with
    | some t => pure t
    | none => do
      match ← (HolMath.Arith.setupArith7 Nm Ar1 Ar2 Ar3 Ar4 Ar5
                 MESON_TAC ASM_MESON_TAC MESON IMP_REWRITE_TAC new_specification).run with
      | .ok t => do theArith7.set (some t); pure t
      | .error e => panic! s!"setupArith7 failed: {e}") with
  | .ok t => t | _ => panic! "Session.Ar7: setupArith7 not run"

unsafe def DIVMOD_EXIST      : thm := Ar7.DIVMOD_EXIST
unsafe def DIVMOD_EXIST_0    : thm := Ar7.DIVMOD_EXIST_0
unsafe def DIVISION_0        : thm := Ar7.DIVISION_0
unsafe def DIVISION          : thm := Ar7.DIVISION
unsafe def DIV_ZERO          : thm := Ar7.DIV_ZERO
unsafe def MOD_ZERO          : thm := Ar7.MOD_ZERO
unsafe def DIVISION_SIMP     : thm := Ar7.DIVISION_SIMP
unsafe def EQ_DIVMOD         : thm := Ar7.EQ_DIVMOD
unsafe def MOD_LT_EQ         : thm := Ar7.MOD_LT_EQ
unsafe def MOD_LT_EQ_LT      : thm := Ar7.MOD_LT_EQ_LT
unsafe def DIVMOD_UNIQ_LEMMA : thm := Ar7.DIVMOD_UNIQ_LEMMA
unsafe def DIVMOD_UNIQ       : thm := Ar7.DIVMOD_UNIQ
unsafe def MOD_UNIQ          : thm := Ar7.MOD_UNIQ
unsafe def DIV_UNIQ          : thm := Ar7.DIV_UNIQ
unsafe def DIV_0             : thm := Ar7.DIV_0
unsafe def MOD_0             : thm := Ar7.MOD_0
unsafe def DIV_MULT          : thm := Ar7.DIV_MULT
unsafe def MOD_MULT          : thm := Ar7.MOD_MULT
unsafe def MOD_LT            : thm := Ar7.MOD_LT
unsafe def MOD_EQ_SELF       : thm := Ar7.MOD_EQ_SELF
unsafe def MOD_CASES         : thm := Ar7.MOD_CASES
unsafe def MOD_ADD_CASES     : thm := Ar7.MOD_ADD_CASES
unsafe def MOD_EQ            : thm := Ar7.MOD_EQ
unsafe def DIV_LE            : thm := Ar7.DIV_LE
unsafe def DIV_MUL_LE        : thm := Ar7.DIV_MUL_LE
unsafe def MOD_LE_TWICE      : thm := Ar7.MOD_LE_TWICE
unsafe def DIV_1             : thm := Ar7.DIV_1
unsafe def MOD_1             : thm := Ar7.MOD_1
unsafe def DIV_LT            : thm := Ar7.DIV_LT
unsafe def MOD_MOD           : thm := Ar7.MOD_MOD
unsafe def MOD_MOD_REFL      : thm := Ar7.MOD_MOD_REFL
unsafe def MOD_MOD_LE        : thm := Ar7.MOD_MOD_LE
unsafe def MOD_EVEN_2        : thm := Ar7.MOD_EVEN_2
unsafe def DIV_MULT2         : thm := Ar7.DIV_MULT2
unsafe def MOD_MULT2         : thm := Ar7.MOD_MULT2
unsafe def MOD_EXISTS        : thm := Ar7.MOD_EXISTS
unsafe def LE_RDIV_EQ        : thm := Ar7.LE_RDIV_EQ
unsafe def RDIV_LT_EQ        : thm := Ar7.RDIV_LT_EQ
unsafe def LE_LDIV_EQ        : thm := Ar7.LE_LDIV_EQ
unsafe def LDIV_LT_EQ        : thm := Ar7.LDIV_LT_EQ
unsafe def LE_LDIV           : thm := Ar7.LE_LDIV
unsafe def DIV_MONO          : thm := Ar7.DIV_MONO
unsafe def DIV_MONO_LT       : thm := Ar7.DIV_MONO_LT
unsafe def DIV_EQ_0          : thm := Ar7.DIV_EQ_0
unsafe def MOD_DIV_EQ_0      : thm := Ar7.MOD_DIV_EQ_0
unsafe def MOD_EQ_0          : thm := Ar7.MOD_EQ_0
unsafe def DIV_EQ_SELF       : thm := Ar7.DIV_EQ_SELF
unsafe def MOD_REFL          : thm := Ar7.MOD_REFL

/-- Cache for `arith.ml` part 8. -/
initialize theArith8 : IO.Ref (Option HolMath.Arith.ArithThms8) ← IO.mkRef none

private unsafe def Ar8 : HolMath.Arith.ArithThms8 :=
  match unsafeIO (do
    match ← theArith8.get with
    | some t => pure t
    | none => do
      match ← (HolMath.Arith.setupArith8 Nm Ar1 Ar2 Ar3 Ar4 Ar5 Ar6 Ar7
                 MESON_TAC ASM_MESON_TAC MESON METIS_TAC ASM_METIS_TAC).run with
      | .ok t => do theArith8.set (some t); pure t
      | .error e => panic! s!"setupArith8 failed: {e}") with
  | .ok t => t | _ => panic! "Session.Ar8: setupArith8 not run"

unsafe def EVEN_MOD          : thm := Ar8.EVEN_MOD
unsafe def ODD_MOD           : thm := Ar8.ODD_MOD
unsafe def MOD_2_CASES       : thm := Ar8.MOD_2_CASES
unsafe def EVEN_MOD_EVEN     : thm := Ar8.EVEN_MOD_EVEN
unsafe def ODD_MOD_EVEN      : thm := Ar8.ODD_MOD_EVEN
unsafe def HALF_DOUBLE       : thm := Ar8.HALF_DOUBLE
unsafe def DOUBLE_HALF       : thm := Ar8.DOUBLE_HALF
unsafe def MOD_MULT_RMOD     : thm := Ar8.MOD_MULT_RMOD
unsafe def MOD_MULT_LMOD     : thm := Ar8.MOD_MULT_LMOD
unsafe def MOD_MULT_MOD2     : thm := Ar8.MOD_MULT_MOD2
unsafe def MOD_EXP_MOD       : thm := Ar8.MOD_EXP_MOD
unsafe def MOD_MULT_ADD      : thm := Ar8.MOD_MULT_ADD
unsafe def DIV_MULT_ADD      : thm := Ar8.DIV_MULT_ADD
unsafe def MOD_ADD_MOD       : thm := Ar8.MOD_ADD_MOD
unsafe def DIV_ADD_MOD       : thm := Ar8.DIV_ADD_MOD
unsafe def MOD_ADD_EQ_EQ     : thm := Ar8.MOD_ADD_EQ_EQ
unsafe def DIV_ADD_EQ_EQ     : thm := Ar8.DIV_ADD_EQ_EQ
unsafe def DIV_ADD_EQ        : thm := Ar8.DIV_ADD_EQ
unsafe def MOD_ADD_EQ        : thm := Ar8.MOD_ADD_EQ
unsafe def DIV_REFL          : thm := Ar8.DIV_REFL
unsafe def MOD_LE            : thm := Ar8.MOD_LE
unsafe def DIV_MONO2         : thm := Ar8.DIV_MONO2
unsafe def DIV_LE_EXCLUSION  : thm := Ar8.DIV_LE_EXCLUSION
unsafe def DIV_EQ_EXCLUSION  : thm := Ar8.DIV_EQ_EXCLUSION
unsafe def MULT_DIV_LE       : thm := Ar8.MULT_DIV_LE
unsafe def DIV_DIV           : thm := Ar8.DIV_DIV
unsafe def DIV_MOD           : thm := Ar8.DIV_MOD
unsafe def MOD_MULT_MOD      : thm := Ar8.MOD_MULT_MOD
unsafe def MOD_MOD_EXP_MIN   : thm := Ar8.MOD_MOD_EXP_MIN
unsafe def DIV_EXP           : thm := Ar8.DIV_EXP
unsafe def MOD_EXP           : thm := Ar8.MOD_EXP
unsafe def FORALL_LT_MOD_THM : thm := Ar8.FORALL_LT_MOD_THM
unsafe def FORALL_MOD_THM    : thm := Ar8.FORALL_MOD_THM
unsafe def EXISTS_LT_MOD_THM : thm := Ar8.EXISTS_LT_MOD_THM
unsafe def EXISTS_MOD_THM    : thm := Ar8.EXISTS_MOD_THM

/-- Cache for `arith.ml` part 9. -/
initialize theArith9 : IO.Ref (Option HolMath.Arith.ArithThms9) ← IO.mkRef none

private unsafe def Ar9 : HolMath.Arith.ArithThms9 :=
  match unsafeIO (do
    match ← theArith9.get with
    | some t => pure t
    | none => do
      -- `parse_as_binder "minimal"` must run before `minimal` is parsed.
      HolMath.Arith.setupMinimalBinder
      match ← (HolMath.Arith.setupArith9 Nm Ar1 Ar2 Ar3 Ar4 Ar5 Ar7
                 MESON_TAC ASM_MESON_TAC MESON SELECT_CONV
                 new_definition prove_recursive_functions_exist).run with
      | .ok t => do theArith9.set (some t); pure t
      | .error e => panic! s!"setupArith9 failed: {e}") with
  | .ok t => t | _ => panic! "Session.Ar9: setupArith9 not run"

unsafe def PRE_ELIM_THM             : thm := Ar9.PRE_ELIM_THM
unsafe def PRE_ELIM_THM'            : thm := Ar9.PRE_ELIM_THM'
unsafe def SUB_ELIM_THM             : thm := Ar9.SUB_ELIM_THM
unsafe def SUB_ELIM_THM'            : thm := Ar9.SUB_ELIM_THM'
unsafe def DIVMOD_ELIM_THM          : thm := Ar9.DIVMOD_ELIM_THM
unsafe def DIVMOD_ELIM_THM'         : thm := Ar9.DIVMOD_ELIM_THM'
unsafe def minimal                  : thm := Ar9.minimal
unsafe def MINIMAL                  : thm := Ar9.MINIMAL
unsafe def MINIMAL_UNIQUE           : thm := Ar9.MINIMAL_UNIQUE
unsafe def LE_MINIMAL               : thm := Ar9.LE_MINIMAL
unsafe def MINIMAL_LE               : thm := Ar9.MINIMAL_LE
unsafe def MINIMAL_UBOUND           : thm := Ar9.MINIMAL_UBOUND
unsafe def MINIMAL_LBOUND           : thm := Ar9.MINIMAL_LBOUND
unsafe def MINIMAL_MONO             : thm := Ar9.MINIMAL_MONO
unsafe def TRANSITIVE_STEPWISE_LT_EQ : thm := Ar9.TRANSITIVE_STEPWISE_LT_EQ
unsafe def TRANSITIVE_STEPWISE_LT   : thm := Ar9.TRANSITIVE_STEPWISE_LT
unsafe def TRANSITIVE_STEPWISE_LE_EQ : thm := Ar9.TRANSITIVE_STEPWISE_LE_EQ
unsafe def TRANSITIVE_STEPWISE_LE   : thm := Ar9.TRANSITIVE_STEPWISE_LE
unsafe def DEPENDENT_CHOICE_FIXED   : thm := Ar9.DEPENDENT_CHOICE_FIXED
unsafe def DEPENDENT_CHOICE         : thm := Ar9.DEPENDENT_CHOICE

/-- arith.ml's procedures `MOD_DOWN_CONV`, `NUM_CANCEL_CONV`, `LE_IMP` and
    `BITS_ELIM_CONV`.  Each is `let <proformas> in fun tm -> ...` in OCaml, so
    its proformas are built once, when arith.ml loads; here they are built
    once by `ensureArithProcs` (forced at arith.ml's position in
    `ensureHolPrefixThroughInt`) and cached. -/
initialize theModDownConv : IO.Ref (Option ioconv) ← IO.mkRef none
initialize theNumCancelConv : IO.Ref (Option ioconv) ← IO.mkRef none
initialize theLeImp : IO.Ref (Option (thm → ExceptT String IO thm)) ← IO.mkRef none
initialize theBitsElimConv : IO.Ref (Option conv) ← IO.mkRef none

private unsafe def cachedProc {α : Type} (r : IO.Ref (Option α))
    (mk : ExceptT String IO α) (name : String) : IO α := do
  match ← r.get with
  | some x => pure x
  | none =>
    match ← mk.run with
    | .ok x => do r.set (some x); pure x
    | .error e => panic! s!"Session.{name}: setup failed: {e}"

/-- `MOD_DOWN_CONV` (arith.ml 1713-1726). -/
unsafe def MOD_DOWN_CONV : ioconv := fun tm => do
  (← cachedProc theModDownConv
      (HolMath.Arith.MOD_DOWN_CONV METIS ADD1 MOD_ADD_MOD MOD_MOD_REFL
        MOD_MULT_MOD2 MOD_EXP_MOD) "MOD_DOWN_CONV") tm

/-- `NUM_CANCEL_CONV` (arith.ml 1732-1756). -/
unsafe def NUM_CANCEL_CONV : ioconv := fun tm => do
  (← cachedProc theNumCancelConv
      (HolMath.Arith.NUM_CANCEL_CONV EQ_ADD_LCANCEL EQ_ADD_LCANCEL_0 ADD_AC)
      "NUM_CANCEL_CONV") tm

/-- `LE_IMP` (arith.ml 1762-1764). -/
unsafe def LE_IMP (th : thm) : IO (Except String thm) := do
  ((← cachedProc theLeImp (HolMath.Arith.LE_IMP T.IMP_CONJ LE_TRANS) "LE_IMP") th).run

/-- `BITS_ELIM_CONV` (arith.ml 1877-1904). -/
unsafe def BITS_ELIM_CONV : IO (Except String conv) := do
  return .ok (← cachedProc theBitsElimConv
    (HolMath.Arith.BITS_ELIM_CONV NUMERAL BIT0 BIT1 ADD1 EQ_ADD_RCANCEL MULT_2
      EQ_MULT_LCANCEL TWO NOT_SUC) "BITS_ELIM_CONV")

/-- Build arith.ml's procedures in file order (arith.ml 1713, 1732, 1762,
    1877), as OCaml does when arith.ml loads. -/
unsafe def ensureArithProcs : IO Unit := do
  let _ ← cachedProc theModDownConv
      (HolMath.Arith.MOD_DOWN_CONV METIS ADD1 MOD_ADD_MOD MOD_MOD_REFL
        MOD_MULT_MOD2 MOD_EXP_MOD) "MOD_DOWN_CONV"
  let _ ← cachedProc theNumCancelConv
      (HolMath.Arith.NUM_CANCEL_CONV EQ_ADD_LCANCEL EQ_ADD_LCANCEL_0 ADD_AC)
      "NUM_CANCEL_CONV"
  let _ ← cachedProc theLeImp (HolMath.Arith.LE_IMP T.IMP_CONJ LE_TRANS) "LE_IMP"
  let _ ← BITS_ELIM_CONV
/- ---------------------------------------------------------------------- -/
/- wf.ml : theory of wellfounded relations.                               -/
/- ---------------------------------------------------------------------- -/

/-- Cache for the `wf.ml` layer. -/
initialize theWf : IO.Ref (Option HolMath.Wf.WfThms) ← IO.mkRef none

private unsafe def Wf : HolMath.Wf.WfThms :=
  match unsafeIO (do
    match ← theWf.get with
    | some t => pure t
    | none => do
      -- wf.ml declares `<<` (and later `<<<`) before its terms are parsed.
      HolMath.Wf.setupWfInfixes
      match ← (@HolMath.Wf.setupWf ⟨B, C, T⟩ new_definition Ar2 Ar3 Ar4 Ar9 Nm Pr ETA_AX
                 MESON_TAC ASM_MESON_TAC
                 prove_recursive_functions_exist prove_inductive_relations_exist
                 SELECT_CONV).run with
      | .ok t => do theWf.set (some t); pure t
      | .error e => panic! s!"setupWf failed: {e}") with
  | .ok t => t | _ => panic! "Session.Wf: setupWf not run"

unsafe def WF                   : thm := Wf.WF
unsafe def WF_EQ                : thm := Wf.WF_EQ
unsafe def WF_IND               : thm := Wf.WF_IND
unsafe def WF_DCHAIN            : thm := Wf.WF_DCHAIN
unsafe def WF_DCHAIN_TRANSITIVE : thm := Wf.WF_DCHAIN_TRANSITIVE
unsafe def WF_UREC              : thm := Wf.WF_UREC
unsafe def WF_UREC_WF           : thm := Wf.WF_UREC_WF
unsafe def WF_REC_INVARIANT     : thm := Wf.WF_REC_INVARIANT
unsafe def WF_REC               : thm := Wf.WF_REC
unsafe def WF_REC_WF            : thm := Wf.WF_REC_WF
unsafe def WF_EREC              : thm := Wf.WF_EREC
unsafe def WF_REC_EXISTS        : thm := Wf.WF_REC_EXISTS
unsafe def WF_SUBSET            : thm := Wf.WF_SUBSET
unsafe def WF_RESTRICT          : thm := Wf.WF_RESTRICT
unsafe def WF_MEASURE_GEN       : thm := Wf.WF_MEASURE_GEN
unsafe def WF_LEX_DEPENDENT     : thm := Wf.WF_LEX_DEPENDENT
unsafe def WF_LEX               : thm := Wf.WF_LEX
unsafe def WF_POINTWISE         : thm := Wf.WF_POINTWISE
unsafe def WF_num               : thm := Wf.WF_num
unsafe def WF_REC_num           : thm := Wf.WF_REC_num
unsafe def MEASURE              : thm := Wf.MEASURE
unsafe def WF_MEASURE           : thm := Wf.WF_MEASURE
unsafe def MEASURE_LE           : thm := Wf.MEASURE_LE
unsafe def WF_ANTISYM           : thm := Wf.WF_ANTISYM
unsafe def WF_REFL              : thm := Wf.WF_REFL
unsafe def WF_FALSE             : thm := Wf.WF_FALSE
unsafe def MINIMAL_BAD_SEQUENCE : thm := Wf.MINIMAL_BAD_SEQUENCE
unsafe def WF_REC_TAIL          : thm := Wf.WF_REC_TAIL
unsafe def WF_REC_TAIL_GENERAL  : thm := Wf.WF_REC_TAIL_GENERAL

/-- Cache for `WF_INDUCT_TAC`'s two `MESON`-proved proformas, built by
    `setupWfInductPths` in a clean parser context (see the note there). -/
initialize theWfInductPths : IO.Ref (Option (thm × thm)) ← IO.mkRef none

private unsafe def WfInductPths : thm × thm :=
  match unsafeIO (do
    match ← theWfInductPths.get with
    | some p => pure p
    | none => do
      match ← (@HolMath.Wf.setupWfInductPths ⟨B, C, T⟩ MESON_TAC).run with
      | .ok p => do theWfInductPths.set (some p); pure p
      | .error e => panic! s!"setupWfInductPths failed: {e}") with
  | .ok p => p | _ => panic! "Session.WfInductPths: not run"

/-- `WF_INDUCT_TAC` (wf.ml): wellfounded induction on a free measured term.
    The two `MESON`-proved proformas come from `setupWfInductPths`; `num_WF`
    from arith.ml. -/
initialize theWfQqconv : IO.Ref (Option ioconv) ← IO.mkRef none

/-- WF_INDUCT_TAC's `qqconv = GEN_REWRITE_CONV I [pth]`, with its net built
    once, as wf.ml builds it. -/
private unsafe def WfQqconv : ioconv :=
  match unsafeIO (do
    match ← theWfQqconv.get with
    | some c => pure c
    | none => do
      match ← (Simp.GEN_REWRITE_CONV B id [WfInductPths.1] : IO (Except String ioconv)) with
      | .ok c => do theWfQqconv.set (some c); pure c
      | .error e => panic! s!"WF_INDUCT_TAC qqconv failed: {e}") with
  | .ok c => c | _ => panic! "Session.WfQqconv: not run"

unsafe def WF_INDUCT_TAC (tm : term) : tactic :=
  @HolMath.Wf.WF_INDUCT_TAC ⟨B, C, T⟩ WfQqconv WfInductPths.2 Ar4.num_WF tm

/- ---------------------------------------------------------------------- -/
/- calc_num.ml : the `ARITH_*` trivial-arithmetic rewrite collection.     -/
/- ---------------------------------------------------------------------- -/

/-- Cache for the `calc_num.ml` `ARITH_*` rewrites. -/
initialize theCalcNumArith : IO.Ref (Option HolMath.CalcNum.ArithRewrites) ←
  IO.mkRef none

private unsafe def CnA : HolMath.CalcNum.ArithRewrites :=
  match unsafeIO (do
    match ← theCalcNumArith.get with
    | some t => pure t
    | none => do
      match ← (HolMath.CalcNum.setupArithRewrites Nm Ar1 Ar2 Ar3 Ar4 Ar5).run with
      | .ok t => do theCalcNumArith.set (some t); pure t
      | .error e => panic! s!"setupArithRewrites failed: {e}") with
  | .ok t => t | _ => panic! "Session.CnA: setupArithRewrites not run"

unsafe def ARITH_ZERO : thm := CnA.ARITH_ZERO
unsafe def BIT0_0     : thm := CnA.BIT0_0
unsafe def BIT1_0     : thm := CnA.BIT1_0
unsafe def ARITH_SUC  : thm := CnA.ARITH_SUC
unsafe def ARITH_PRE  : thm := CnA.ARITH_PRE
unsafe def ARITH_ADD  : thm := CnA.ARITH_ADD
unsafe def ARITH_MULT : thm := CnA.ARITH_MULT
unsafe def ARITH_EXP  : thm := CnA.ARITH_EXP
unsafe def ARITH_EVEN : thm := CnA.ARITH_EVEN
unsafe def ARITH_ODD  : thm := CnA.ARITH_ODD
unsafe def ARITH_LE   : thm := CnA.ARITH_LE
unsafe def ARITH_LT   : thm := CnA.ARITH_LT
unsafe def ARITH_GE   : thm := CnA.ARITH_GE
unsafe def ARITH_GT   : thm := CnA.ARITH_GT
unsafe def ARITH_EQ   : thm := CnA.ARITH_EQ
unsafe def ARITH_SUB  : thm := CnA.ARITH_SUB
unsafe def ARITH      : thm := CnA.ARITH
unsafe def EXP_2_NE_0 : thm := CnA.EXP_2_NE_0

/- ---------------------------------------------------------------------- -/
/- calc_num.ml : the delicate numeral conversions (lines 208-603).        -/
/- ---------------------------------------------------------------------- -/


/-- Cache for the shared `calc_num.ml` numeral-conversion term constants. -/
initialize theCalcNumConsts : IO.Ref (Option HolMath.CalcNum.CalcNumConsts) ←
  IO.mkRef none

private unsafe def CnK : HolMath.CalcNum.CalcNumConsts :=
  match unsafeIO (do
    match ← theCalcNumConsts.get with
    | some t => pure t
    | none => do
      match ← (HolMath.CalcNum.setupCalcNumConsts ZERO_DEF TWO ADD_0 EXP_2 DIVISION
                 SUB_0 LE_0 mk_small_numeral).run with
      | .ok t => do theCalcNumConsts.set (some t); pure t
      | .error e => panic! s!"setupCalcNumConsts failed: {e}") with
  | .ok t => t | _ => panic! "Session.CnK: setupCalcNumConsts not run"

/-- Cache for the `calc_num.ml` delicate-conversion proformas. -/
initialize theCalcNumProformas : IO.Ref (Option HolMath.CalcNum.CalcNumProformas) ←
  IO.mkRef none

private unsafe def CnP : HolMath.CalcNum.CalcNumProformas :=
  match unsafeIO (do
    match ← theCalcNumProformas.get with
    | some t => pure t
    | none => do
      -- `setupCalcNumProformas` PARSES terms mentioning `DIV` and `MOD`, so
      -- those constants must already be DECLARED.  An undeclared constant
      -- parses as a free VARIABLE, and the proforma proofs then fail with
      -- `TAC_PROOF: Unsolved goals`.  In OCaml the situation cannot arise
      -- because `calc_num.ml` loads strictly after `DIVISION` is proved; here
      -- the layers are lazy, so force the declaration explicitly first.
      -- (`let _ := DIVISION` would NOT force a Lean CAF - it needs an IO
      -- action.)
      let _ ← IO.mkRef (concl DIVISION)
      match ← (HolMath.CalcNum.setupCalcNumProformas CnK CnA
                 NUMERAL BIT0 BIT1 ADD_CLAUSES MULT_CLAUSES SUC_INJ
                 EQ_MULT_LCANCEL MULT_2 MULT_ASSOC LEFT_ADD_DISTRIB
                 ADD_EQ_0 MULT_EQ_0
                 RIGHT_ADD_DISTRIB EXP_2 MULT_AC ADD_AC EQ_ADD_LCANCEL
                 EQ_ADD_RCANCEL ADD_SYM ADD1 ADD_ASSOC NOT_SUC MULT_SYM
                 EXP EXP_ADD LT_EXISTS LE_ADD NOT_LT NOT_LE
                 LE_ANTISYM LT_REFL LE_REFL
                 PRE SUB_EQ_0 ADD_SUB DIVMOD_UNIQ DIV_ZERO MOD_ZERO FACT LT
                 MESON_TAC MOD_DOWN_CONV NUM_CANCEL_CONV mk_small_numeral).run with
      | .ok t => do theCalcNumProformas.set (some t); pure t
      | .error e => panic! s!"setupCalcNumProformas failed: {e}") with
  | .ok t => t | _ => panic! "Session.CnP: setupCalcNumProformas not run"

/-- Cache for what calc_num.ml's later conversions build before their
    `fun tm ->` (`HolMath.CalcNum.CalcNumNets`).  Forced at calc_num.ml's
    position in `ensureHolPrefixThroughInt`, because `REWRITE_CONV[GSYM
    CONJ_ASSOC]` captures the basic rewrites current then. -/
initialize theCalcNumNets : IO.Ref (Option HolMath.CalcNum.CalcNumNets) ← IO.mkRef none

private unsafe def CnN : HolMath.CalcNum.CalcNumNets :=
  match unsafeIO (do
    match ← theCalcNumNets.get with
    | some t => pure t
    | none => do
      match ← (HolMath.CalcNum.setupCalcNumNets CnA CnK CnP GT GE COND_CLAUSES
                 CONJ_ASSOC MOD_ZERO).run with
      | .ok t => do theCalcNumNets.set (some t); pure t
      | .error e => panic! s!"setupCalcNumNets failed: {e}") with
  | .ok t => t | _ => panic! "Session.CnN: setupCalcNumNets not run"

/-- The shared `calc_num.ml` numeral-conversion constants. -/
unsafe def calcNumConsts : HolMath.CalcNum.CalcNumConsts := CnK

/-- `NUM_EVEN_CONV` (calc_num.ml 211). -/
unsafe def NUM_EVEN_CONV : ioconv := fun tm => CnN.even_conv tm

/-- `NUM_ODD_CONV` (calc_num.ml 215). -/
unsafe def NUM_ODD_CONV : ioconv := fun tm => CnN.odd_conv tm

/-- The `calc_num.ml` delicate-conversion proformas. -/
unsafe def calcNumProformas : HolMath.CalcNum.CalcNumProformas := CnP

/-- `NUM_ADD_RULE mtm ntm` (calc_num.ml): add two raw numerals. -/
unsafe def NUM_ADD_RULE (mtm ntm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_ADD_RULE CnK CnP mtm ntm

/-- `NUM_ADC_RULE mtm ntm` (calc_num.ml): add two raw numerals with carry. -/
unsafe def NUM_ADC_RULE (mtm ntm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_ADC_RULE CnK CnP mtm ntm

/-- `NUM_SHIFT_CONV k tm` (calc_num.ml). -/
unsafe def NUM_SHIFT_CONV (k : Int) (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_SHIFT_CONV CnK CnP k tm

/-- `NUM_UNSHIFT_CONV tm` (calc_num.ml). -/
unsafe def NUM_UNSHIFT_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_UNSHIFT_CONV CnK CnP tm

/-- `TOOM3_CONV` (calc_num.ml). -/
unsafe def TOOM3_CONV : ioconv := HolMath.CalcNum.TOOM3_CONV CnK CnP

/-- `NUM_SQUARE_RULE tm` (calc_num.ml). -/
unsafe def NUM_SQUARE_RULE (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_SQUARE_RULE CnK CnP mk_numeral tm

/-- `NUM_MUL_RULE k l tm tm'` (calc_num.ml). -/
unsafe def NUM_MUL_RULE (k l : Int) (tm tm' : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_MUL_RULE CnK CnP mk_numeral k l tm tm'

/-- `NUM_SUC_CONV tm` (calc_num.ml): `|- SUC (NUMERAL m) = NUMERAL n`. -/
unsafe def NUM_SUC_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_SUC_CONV CnK CnP tm

/-- `NUM_ADD_CONV tm` (calc_num.ml): `|- NUMERAL m + NUMERAL n = NUMERAL p`. -/
unsafe def NUM_ADD_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_ADD_CONV CnK CnP tm

/-- `NUM_MULT_CONV tm` (calc_num.ml): `|- NUMERAL m * NUMERAL n = NUMERAL p`. -/
unsafe def NUM_MULT_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_MULT_CONV CnK CnP mk_numeral tm

/-- `NUM_EXP_CONV tm` (calc_num.ml): `|- NUMERAL m EXP NUMERAL n = NUMERAL p`. -/
unsafe def NUM_EXP_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_EXP_CONV CnK CnP mk_numeral CnN.exp_tconv tm

/-- `NUM_LT_CONV tm` (calc_num.ml): `|- (NUMERAL m < NUMERAL n) <=> T/F`. -/
unsafe def NUM_LT_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_LT_CONV CnK CnP tm

/-- `NUM_LE_CONV tm` (calc_num.ml): `|- (NUMERAL m <= NUMERAL n) <=> T/F`. -/
unsafe def NUM_LE_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_LE_CONV CnK CnP tm

/-- `NUM_EQ_CONV tm` (calc_num.ml): `|- (NUMERAL m = NUMERAL n) <=> T/F`. -/
unsafe def NUM_EQ_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_EQ_CONV CnK CnP tm

/- ---------------------------------------------------------------------- -/
/- calc_num.ml : the remaining conversions (lines 1314-1560).             -/
/- ---------------------------------------------------------------------- -/

/-- `NUM_GT_CONV` (calc_num.ml). -/
unsafe def NUM_GT_CONV : ioconv := HolMath.CalcNum.NUM_GT_CONV CnN CnK CnP

/-- `NUM_GE_CONV` (calc_num.ml). -/
unsafe def NUM_GE_CONV : ioconv := HolMath.CalcNum.NUM_GE_CONV CnN CnK CnP

/-- `NUM_PRE_CONV tm` (calc_num.ml): `|- PRE (NUMERAL n) = NUMERAL m`. -/
unsafe def NUM_PRE_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_PRE_CONV CnN CnK CnP mk_numeral tm

/-- `NUM_SUB_CONV tm` (calc_num.ml): `|- NUMERAL m - NUMERAL n = NUMERAL p`. -/
unsafe def NUM_SUB_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_SUB_CONV CnK CnP mk_numeral tm

/-- `NUM_DIV_CONV tm` (calc_num.ml): `|- NUMERAL m DIV NUMERAL n = NUMERAL q`. -/
unsafe def NUM_DIV_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_DIV_CONV CnN CnK CnP mk_numeral tm

/-- `NUM_MOD_CONV tm` (calc_num.ml): `|- NUMERAL m MOD NUMERAL n = NUMERAL r`. -/
unsafe def NUM_MOD_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_MOD_CONV CnN CnK CnP mk_numeral tm

/-- `NUM_FACT_CONV tm` (calc_num.ml): `|- FACT (NUMERAL n) = NUMERAL z`. -/
unsafe def NUM_FACT_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_FACT_CONV CnN CnK CnP mk_numeral tm

/-- `NUM_MAX_CONV` (calc_num.ml). -/
unsafe def NUM_MAX_CONV : ioconv :=
  HolMath.CalcNum.NUM_MAX_CONV CnN MAX CnK CnP

/-- `NUM_MIN_CONV` (calc_num.ml). -/
unsafe def NUM_MIN_CONV : ioconv :=
  HolMath.CalcNum.NUM_MIN_CONV CnN MIN CnK CnP

/-- `num_CONV tm` (calc_num.ml): `|- NUMERAL n = SUC (NUMERAL (n-1))`. -/
unsafe def num_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.num_CONV CnK CnP mk_numeral tm

/-- `EXPAND_CASES_CONV` (calc_num.ml): expand `!n. n < k ==> P n` into cases. -/
unsafe def EXPAND_CASES_CONV : ioconv :=
  HolMath.CalcNum.EXPAND_CASES_CONV CnN CnK CnP mk_numeral

/-- `NUM_EVEN_CONV` as a plain `ioconv` (forcing the cached ARITH_EVEN conv). -/
unsafe def numEvenConvIO : ioconv := NUM_EVEN_CONV

/-- `NUM_ODD_CONV` as a plain `ioconv` (forcing the cached ARITH_ODD conv). -/
unsafe def numOddConvIO : ioconv := NUM_ODD_CONV

/-- The 18-entry `num_red_conv_list` (calc_num.ml), cached. -/
initialize theNumRedConvList :
    IO.Ref (Option (List (term × ioconv))) ← IO.mkRef none

private unsafe def numRedConvListIO : IO (Except String (List (term × ioconv))) := do
  match ← theNumRedConvList.get with
  | some l => return .ok l
  | none =>
    match ← HolMath.CalcNum.num_red_conv_list
        NUM_SUC_CONV NUM_PRE_CONV NUM_FACT_CONV NUM_LT_CONV NUM_LE_CONV
        NUM_GT_CONV NUM_GE_CONV NUM_EQ_CONV numEvenConvIO numOddConvIO
        NUM_ADD_CONV NUM_SUB_CONV NUM_MULT_CONV NUM_EXP_CONV NUM_DIV_CONV
        NUM_MOD_CONV NUM_MAX_CONV NUM_MIN_CONV with
    | .error e => return .error e
    | .ok l => do theNumRedConvList.set (some l); return .ok l

/-- The cached `NUM_RED_CONV` net conversion (calc_num.ml). -/
initialize theNumRedConv : IO.Ref (Option ioconv) ← IO.mkRef none

private unsafe def numRedConvIO : IO (Except String ioconv) := do
  match ← theNumRedConv.get with
  | some c => return .ok c
  | none =>
    match ← numRedConvListIO with
    | .error e => return .error e
    | .ok l =>
      match ← HolMath.CalcNum.NUM_RED_CONV l with
      | .error e => return .error e
      | .ok c => do theNumRedConv.set (some c); return .ok c

/-- The `NUM_REL_CONV` net conversion (calc_num.ml 1443-1451), built once. -/
initialize theNumRelConv : IO.Ref (Option ioconv) ← IO.mkRef none

private unsafe def numRelConvIO : IO (Except String ioconv) := do
  match ← theNumRelConv.get with
  | some c => return .ok c
  | none =>
    match ← HolMath.CalcNum.NUM_REL_CONV NUM_LT_CONV NUM_LE_CONV NUM_GT_CONV
        NUM_GE_CONV NUM_EQ_CONV with
    | .error e => return .error e
    | .ok c => do theNumRelConv.set (some c); return .ok c

/-- `NUM_REL_CONV` (calc_num.ml 1443-1451): the five relational reductions. -/
unsafe def NUM_REL_CONV (tm : term) : IO (Except String thm) := do
  match ← numRelConvIO with
  | .error e => return .error e
  | .ok c => c tm

/-- `NUM_RED_CONV tm` (calc_num.ml): a single numeral reduction step. -/
unsafe def NUM_RED_CONV (tm : term) : IO (Except String thm) := do
  match ← numRedConvIO with
  | .error e => return .error e
  | .ok c => c tm

/-- `NUM_REDUCE_CONV tm` (calc_num.ml): `DEPTH_CONV NUM_RED_CONV`. -/
unsafe def NUM_REDUCE_CONV (tm : term) : IO (Except String thm) := do
  match ← numRedConvIO with
  | .error e => return .error e
  | .ok c => HolMath.CalcNum.NUM_REDUCE_CONV c tm

/-- `NUM_REDUCE_TAC` (calc_num.ml): `CONV_TAC NUM_REDUCE_CONV`. -/
unsafe def NUM_REDUCE_TAC : tactic :=
  HolMath.CalcNum.NUM_REDUCE_TAC NUM_REDUCE_CONV

/-- `NUM_COMPUTE_CONV tm` (calc_num.ml): call-by-value numeral evaluation via a
    `bool_compset ()` extended with the reduction conversions. -/
initialize theNumComputeConv : IO.Ref (Option ioconv) ← IO.mkRef none

private unsafe def numComputeConvIO : IO (Except String ioconv) := do
  match ← theNumComputeConv.get with
  | some c => return .ok c
  | none =>
    match ← numRedConvListIO with
    | .error e => return .error e
    | .ok l =>
      match ← HolMath.CalcNum.NUM_COMPUTE_CONV l bool_compset
          set_skip add_conv WEAK_CBV_CONV [[ COND: bool -> A -> A -> A ]] with
      | .error e => return .error e
      | .ok c => do theNumComputeConv.set (some c); return .ok c

unsafe def NUM_COMPUTE_CONV (tm : term) : IO (Except String thm) := do
  match ← numComputeConvIO with
  | .error e => return .error e
  | .ok c => c tm

/-- `EXP_MOD_CONV tm` (calc_num.ml): compute `(a EXP k) MOD n` with reduced
    intermediates. -/
unsafe def EXP_MOD_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.EXP_MOD_CONV CnN NUM_EXP_CONV NUM_MULT_CONV NUM_MOD_CONV tm

/- ---------------------------------------------------------------------- -/
/- normalizer.ml : canonical polynomial normalization for the naturals.   -/
/- ---------------------------------------------------------------------- -/

/-- Cache for the natural-number `SemiringCtx` built by
    `setupNumNormalizeCtx` (normalizer.ml 542-565).  Building it proves the
    38-conjunct `SEMIRING_PTHS` bundle once and destructures it, so it is
    cached like `theCalcNumConsts`/`theCalcNumProformas`. -/
initialize theNormalizerCtx :
    IO.Ref (Option (HolMath.Normalizer.SemiringCtx × thm)) ← IO.mkRef none

/-- The natural-number `SemiringCtx` and normalizer.ml's `SEMIRING_PTHS`,
    proved once while it is built. -/
private unsafe def NmzP : HolMath.Normalizer.SemiringCtx × thm :=
  match unsafeIO (do
    match ← theNormalizerCtx.get with
    | some t => pure t
    | none => do
      match ← (HolMath.Normalizer.setupNumNormalizeCtx' TRUTH ADD_CLAUSES
                 MULT_CLAUSES EXP LEFT_ADD_DISTRIB ADD_AC MULT_AC ASM_MESON_TAC
                 INDUCT_TAC num_CONV
                 NUM_ADD_CONV NUM_MULT_CONV NUM_EXP_CONV).run with
      | .ok t => do theNormalizerCtx.set (some t); pure t
      | .error e => panic! s!"setupNumNormalizeCtx failed: {e}") with
  | .ok t => t | _ => panic! "Session.Nmz: setupNumNormalizeCtx not run"

private unsafe def Nmz : HolMath.Normalizer.SemiringCtx := NmzP.1

/-- The natural-number `SemiringCtx` (normalizer.ml 542-565). -/
unsafe def numSemiringCtx : HolMath.Normalizer.SemiringCtx := Nmz

/-- `SEMIRING_NORMALIZERS_CONV` with the OCaml interface (normalizer.ml 9):
    `sth rth (is_semiring_constant, ADD_CONV, MUL_CONV, POW_CONV)
    variable_order`, returning the six conversions as a tuple.  The Lean
    version takes a prebuilt `SemiringCtx`; this builds it, as the OCaml
    does on each call, from the `SEMIRING_PTHS` proved once. -/
unsafe def SEMIRING_NORMALIZERS_CONV (sth rth : thm)
    (cs : (term → Bool) × ioconv × ioconv × ioconv)
    (variable_order : term → term → Bool) :
    ExceptT String IO (ioconv × ioconv × ioconv × ioconv × ioconv × ioconv) := do
  let (is_semiring_constant, add_conv, mul_conv, pow_conv) := cs
  -- `SEMIRING_PTHS` is proved once, when normalizer.ml defines
  -- SEMIRING_NORMALIZERS_CONV (here: when the natural-number normalizer is
  -- built), not on each call.
  let K ← HolMath.Normalizer.setupSemiringCtxFrom NmzP.2 TRUTH sth rth
            is_semiring_constant add_conv mul_conv pow_conv variable_order
  let P := HolMath.Normalizer.SEMIRING_NORMALIZERS_CONV K
             NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV num_CONV
  return (P.POLYNOMIAL_NEG_CONV, P.POLYNOMIAL_ADD_CONV, P.POLYNOMIAL_SUB_CONV,
          P.POLYNOMIAL_MUL_CONV, P.POLYNOMIAL_POW_CONV, P.POLYNOMIAL_CONV)

/-- The six polynomial conversions for the naturals, bundled by
    `SEMIRING_NORMALIZERS_CONV` (normalizer.ml 537-538).  The IO-valued
    exponent conversions and `num_CONV` — which are NOT stored in the
    `SemiringCtx` — are threaded in here, matching the OCaml.  `NUM_SUC_CONV`
    is the caller-supplied successor conversion the monomial layer needs. -/
unsafe def numPolynomialConvs : HolMath.Normalizer.PolynomialConvs :=
  HolMath.Normalizer.SEMIRING_NORMALIZERS_CONV Nmz
    NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV num_CONV

/-- `POLYNOMIAL_NEG_CONV` for the naturals (normalizer.ml 491-497).  In this
    instance `rth = TRUTH`, so `neg_tm` is a DUMMY and a real negation never
    matches — the conversion fails, exactly as the OCaml intends. -/
unsafe def NORM_POLYNOMIAL_NEG_CONV : ioconv := numPolynomialConvs.POLYNOMIAL_NEG_CONV

/-- `POLYNOMIAL_ADD_CONV` for the naturals (normalizer.ml 374-440). -/
unsafe def NORM_POLYNOMIAL_ADD_CONV : ioconv := numPolynomialConvs.POLYNOMIAL_ADD_CONV

/-- `POLYNOMIAL_SUB_CONV` for the naturals (normalizer.ml 502-509).  DUMMY
    `sub_tm` in this instance; never routed to for a real subtraction. -/
unsafe def NORM_POLYNOMIAL_SUB_CONV : ioconv := numPolynomialConvs.POLYNOMIAL_SUB_CONV

/-- `POLYNOMIAL_MUL_CONV` for the naturals (normalizer.ml 445-467). -/
unsafe def NORM_POLYNOMIAL_MUL_CONV : ioconv := numPolynomialConvs.POLYNOMIAL_MUL_CONV

/-- `POLYNOMIAL_POW_CONV` for the naturals (normalizer.ml 472-486). -/
unsafe def NORM_POLYNOMIAL_POW_CONV : ioconv := numPolynomialConvs.POLYNOMIAL_POW_CONV

/-- `NUM_NORMALIZE_CONV tm` (normalizer.ml 541-565): put a natural-number
    term into canonical polynomial form.  This is the SIXTH component
    (`POLYNOMIAL_CONV`) of the tuple `SEMIRING_NORMALIZERS_CONV` returns; the
    OCaml discards the other five with
    `let _,_,_,_,_,NUM_NORMALIZE_CONV = ... in NUM_NORMALIZE_CONV`. -/
unsafe def NUM_NORMALIZE_CONV : ioconv := numPolynomialConvs.POLYNOMIAL_CONV

/- ---------------------------------------------------------------------- -/
/- grobner.ml : the Grobner-basis ring/ideal decision procedure.          -/
/- ---------------------------------------------------------------------- -/

/-- Cache for the `NUM_SIMPLIFY_CONV`-local constants (grobner.ml 628-650):
    `pre_tm`/`div_tm`/`mod_tm`/`sub_tm` recovered from the elimination
    theorems, the three primed'' theorems (`CONV_RULE(RAND_CONV NNF_CONV)`) and
    `pth_evenodd`.  Built once and cached like `theNormalizerCtx`. -/
initialize theNumSimplifyConsts :
    IO.Ref (Option HolMath.Grobner.NumSimplifyConsts) ← IO.mkRef none

private unsafe def NsC : HolMath.Grobner.NumSimplifyConsts :=
  match unsafeIO (do
    match ← theNumSimplifyConsts.get with
    | some t => pure t
    | none => do
      match ← (HolMath.Grobner.setupNumSimplifyConsts NNF_CONV
                 PRE_ELIM_THM SUB_ELIM_THM DIVMOD_ELIM_THM
                 PRE_ELIM_THM' SUB_ELIM_THM' DIVMOD_ELIM_THM'
                 NOT_EXISTS_THM EVEN_EXISTS ODD_EXISTS NOT_EVEN NOT_ODD).run with
      | .ok t => do theNumSimplifyConsts.set (some t); pure t
      | .error e => panic! s!"setupNumSimplifyConsts failed: {e}") with
  | .ok t => t | _ => panic! "Session.NsC: setupNumSimplifyConsts not run"

/-- `NUM_MULTIPLY_CONV pos tm` (grobner.ml 651-687). -/
unsafe def NUM_MULTIPLY_CONV (pos : Bool) (tm : term) : IO (Except String thm) :=
  HolMath.Grobner.numMultiplyConv NsC pos tm

/-- Cache for the assembled `NUM_SIMPLIFY_CONV` ioconv (grobner.ml 651-703). -/
initialize theNumSimplifyConv : IO.Ref (Option ioconv) ← IO.mkRef none

/-- `NUM_SIMPLIFY_CONV tm` (grobner.ml 651-703): the six-link `THENC` chain
    `NUM_REDUCE_CONV THENC CONDS_CELIM_CONV THENC NNF_CONV THENC
     NUM_MULTIPLY_CONV true THENC NUM_REDUCE_CONV THENC
     GEN_REWRITE_CONV ONCE_DEPTH_CONV [pth_evenodd]`. -/
private unsafe def numSimplifyConvIO : IO (Except String ioconv) := do
  match ← theNumSimplifyConv.get with
  | some c => return .ok c
  | none =>
    match ← (HolMath.Grobner.NUM_SIMPLIFY_CONV NsC
               NUM_REDUCE_CONV CONDS_CELIM_CONV NNF_CONV).run with
    | .error e => return .error e
    | .ok c => do theNumSimplifyConv.set (some c); return .ok c

unsafe def NUM_SIMPLIFY_CONV : ioconv := fun tm => do
  match ← numSimplifyConvIO with
  | .ok c => c tm
  | .error e => return .error e

/-- Cache for `NUM_INTEGRAL_LEMMA` (grobner.ml 708-715). -/
initialize theNumIntegralLemma : IO.Ref (Option thm) ← IO.mkRef none

private unsafe def NUM_INTEGRAL_LEMMA : thm :=
  match unsafeIO (do
    match ← theNumIntegralLemma.get with
    | some t => pure t
    | none => do
      match ← (HolMath.Grobner.NUM_INTEGRAL_LEMMA ADD_AC
                 LEFT_ADD_DISTRIB RIGHT_ADD_DISTRIB ADD_ASSOC
                 EQ_ADD_LCANCEL EQ_ADD_LCANCEL_0 MULT_EQ_0).run with
      | .ok t => do theNumIntegralLemma.set (some t); pure t
      | .error e => panic! s!"NUM_INTEGRAL_LEMMA failed: {e}") with
  | .ok t => t | _ => panic! "Session.NUM_INTEGRAL_LEMMA: not run"

/-- Cache for `NUM_INTEGRAL` (grobner.ml 716-726). -/
initialize theNumIntegral : IO.Ref (Option thm) ← IO.mkRef none

unsafe def NUM_INTEGRAL : thm :=
  match unsafeIO (do
    match ← theNumIntegral.get with
    | some t => pure t
    | none => do
      match ← (HolMath.Grobner.NUM_INTEGRAL ASM_MESON_TAC
                 NUM_INTEGRAL_LEMMA MULT_CLAUSES EQ_ADD_LCANCEL LE_CASES
                 LE_EXISTS ADD_SYM MULT_SYM).run with
      | .ok t => do theNumIntegral.set (some t); pure t
      | .error e => panic! s!"NUM_INTEGRAL failed: {e}") with
  | .ok t => t | _ => panic! "Session.NUM_INTEGRAL: not run"

/-- Cache for the natural-number `RingParms` bundle (grobner.ml 727-732).
    `ring_dest_const = dest_numeral`, `ring_mk_const = mk_numeral`,
    `RING_EQ_CONV = NUM_EQ_CONV`, `add/mul/pow_tm` are the genuine `num`
    constants (threaded from `CnK`), the neg/sub/inv/div slots are fresh
    `genvar bool_ty` dummies, `RING_INTEGRAL = NUM_INTEGRAL`,
    `RABINOWITSCH_THM = TRUTH` (selects the SCALED runner), and
    `RING_NORMALIZE_CONV = NUM_NORMALIZE_CONV`. -/
initialize theNumRingParms :
    IO.Ref (Option HolMath.Grobner.RingParms) ← IO.mkRef none

private unsafe def NRP : HolMath.Grobner.RingParms :=
  match unsafeIO (do
    match ← theNumRingParms.get with
    | some t => pure t
    | none => do
      -- grobner.ml 727-732 parses the three operators; OCaml builds the
      -- argument tuple right to left.
      let q (s : String) : IO term := do
        match ← HolCore.Parser.parse_term s with
        | .ok t => pure t | .error e => panic! s!"NUM_RING {s}: {e}"
      let exp_tm ← q "(EXP):num->num->num"
      let mul_tm ← q "(*):num->num->num"
      let add_tm ← q "(+):num->num->num"
      let t ← HolMath.Grobner.numRingParms Nm.numK NUM_EQ_CONV NUM_NORMALIZE_CONV
                add_tm mul_tm exp_tm NUM_INTEGRAL TRUTH
      theNumRingParms.set (some t); pure t) with
  | .ok t => t | _ => panic! "Session.NRP: numRingParms not run"

/-- The natural-number `RingParms` bundle (grobner.ml 727-732). -/
unsafe def numRingParms : HolMath.Grobner.RingParms := NRP

/-- Cache for the parameter-independent part of `RING_AND_IDEAL_CONV`
    (grobner.ml 336-354): `pth_step`, `FINAL_RULE`, `false_tm`. -/
initialize theGrobnerGlobals :
    IO.Ref (Option HolMath.Grobner.GrobnerGlobals) ← IO.mkRef none

unsafe def GrG : HolMath.Grobner.GrobnerGlobals :=
  match unsafeIO (do
    match ← theGrobnerGlobals.get with
    | some t => pure t
    | none => do
      match ← (HolMath.Grobner.setupGrobnerGlobals DE_MORGAN_THM CONTRAPOS_THM).run with
      | .ok t => do theGrobnerGlobals.set (some t); pure t
      | .error e => panic! s!"setupGrobnerGlobals failed: {e}") with
  | .ok t => t | _ => panic! "Session.GrG: setupGrobnerGlobals not run"

/-- Cache for what `RING_AND_IDEAL_CONV` builds from the natural-number
    parameters (grobner.ml 364-465). -/
initialize theNumRingCtx : IO.Ref (Option HolMath.Grobner.RingCtx) ← IO.mkRef none

private unsafe def NRC : HolMath.Grobner.RingCtx :=
  match unsafeIO (do
    match ← theNumRingCtx.get with
    | some t => pure t
    | none => do
      match ← (HolMath.Grobner.setupRingCtx GrG Nm.numK (concl TRUTH)
                 PRESIMP_CONV CONDS_ELIM_CONV NNF_CONV WEAK_DNF_CONV
                 AND_FORALL_THM LEFT_AND_FORALL_THM RIGHT_AND_FORALL_THM
                 LEFT_OR_FORALL_THM RIGHT_OR_FORALL_THM OR_EXISTS_THM
                 LEFT_OR_EXISTS_THM RIGHT_OR_EXISTS_THM LEFT_AND_EXISTS_THM
                 RIGHT_AND_EXISTS_THM NRP).run with
      | .ok t => do theNumRingCtx.set (some t); pure t
      | .error e => panic! s!"setupRingCtx (num) failed: {e}") with
  | .ok t => t | _ => panic! "Session.NRC: setupRingCtx not run"

/-- `RING` at the natural-number parameters (grobner.ml 582-601); the
    `rawring` of `NUM_RING`. -/
unsafe def RING (tm : term) : IO (Except String thm) :=
  HolMath.Grobner.RING NRC tm

/-- `ideal_cofactors` at the natural-number parameters (grobner.ml 618). -/
unsafe def ideal_cofactors (tms : List term) (tm : term) :
    IO (Except String (List term)) :=
  HolMath.Grobner.ideal_cofactors NRC tms tm

/-- `grobner_ideal vars pols pol` (grobner.ml 304-308), exposed for direct
    testing. -/
def grobner_ideal (vars : List term) (pols : List HolMath.Grobner.poly)
    (pol : HolMath.Grobner.poly) :
    IO (Except String (List (Int × HolMath.Grobner.poly))) :=
  (HolMath.Grobner.grobner_ideal vars pols pol).run

/-- Cache for `NUM_RING` (grobner.ml 707-737). -/
initialize theNumRing : IO.Ref (Option ioconv) ← IO.mkRef none

/-- Build (once) the `NUM_RING` procedure (grobner.ml 707-737). -/
private unsafe def numRingIO : IO (Except String ioconv) := do
  match ← theNumRing.get with
  | some c => return .ok c
  | none =>
    match ← (HolMath.Grobner.NUM_RING NUM_SIMPLIFY_CONV ADD1 RING).run with
    | .error e => return .error e
    | .ok c => do theNumRing.set (some c); return .ok c

/-- `NUM_RING tm` (grobner.ml 707-737). -/
unsafe def NUM_RING : ioconv := fun tm => do
  match ← numRingIO with
  | .ok c => c tm
  | .error e => return .error e

/- ---------------------------------------------------------------------- -/
/- ind_types.ml: nested-recursion stores and lookups (lines 1009-1080).    -/
/- ---------------------------------------------------------------------- -/

/-- `basic_rectype_net = ref empty_net` (ind_types.ml 1022).  Seeded with the
    empty net; extended by `extend_rectype_net`. -/
initialize theBasicRectypeNet :
    IO.Ref (HolCore.Nets.net Simp.gconv) ← IO.mkRef HolCore.Nets.empty_net

/-- `distinctness_store = ref ["bool", TAUT `(T <=> F) <=> F`]` (ind_types.ml
    1023).  The seed `TAUT` is an IO computation, so the ref starts `none` and
    is lazily seeded on first access. -/
initialize theDistinctnessStore :
    IO.Ref (Option HolMath.IndTypes.RectypeStore) ← IO.mkRef none

/-- `injectivity_store = ref []` (ind_types.ml 1024). -/
initialize theInjectivityStore :
    IO.Ref HolMath.IndTypes.RectypeStore ← IO.mkRef []

/-- Read the `distinctness_store`, lazily seeding it with `["bool", TAUT `(T
    <=> F) <=> F`]` on first access.  This is a genuine IO read (NOT a memoised
    CAF), so it always reflects the latest ref state. -/
unsafe def readDistinctnessStore : IO HolMath.IndTypes.RectypeStore := do
  match ← theDistinctnessStore.get with
  | some l => pure l
  | none =>
    let boolThm ← (match ← (TAUT (← (match ← Parser.parse_term "(T <=> F) <=> F" with
                      | .ok t => pure t | .error e => panic! s!"distinctness seed parse: {e}"))
                      : IO (Except String thm)) with
      | .ok t => pure t | .error e => panic! s!"distinctness seed TAUT: {e}")
    let l := [("bool", boolThm)]
    theDistinctnessStore.set (some l); pure l

/-- `!distinctness_store` — the current distinctness store contents. -/
unsafe def distinctness_store : HolMath.IndTypes.RectypeStore :=
  match unsafeIO readDistinctnessStore with
  | .ok l => l | _ => panic! "Session.distinctness_store"

/-- `!injectivity_store` — the current injectivity store contents. -/
unsafe def injectivity_store : HolMath.IndTypes.RectypeStore :=
  match unsafeIO theInjectivityStore.get with
  | .ok l => l | _ => panic! "Session.injectivity_store"

/-- `!basic_rectype_net` — the current basic rectype net. -/
unsafe def basic_rectype_net : HolCore.Nets.net Simp.gconv :=
  match unsafeIO theBasicRectypeNet.get with
  | .ok n => n | _ => panic! "Session.basic_rectype_net"

/-- Cache for `prove_constructors_injective` (ind_types.ml 902-926), whose
    `DEPAIR` net is built once. -/
initialize thePcInjective : IO.Ref (Option (thm → ExceptT String IO thm)) ← IO.mkRef none

/-- `prove_constructors_injective` as built once. -/
private unsafe def pcInjective (ax : thm) : ExceptT String IO thm := do
  match ← thePcInjective.get with
  | some f => f ax
  | none =>
    let f ← HolMath.IndTypes.prove_constructors_injective BETA_THM PAIR_EQ mk_pair
    thePcInjective.set (some f)
    f ax

/-- Cache for `prove_constructors_distinct` (ind_types.ml 928-959), whose
    `num_ty` and `NEGATE` tautology are made once. -/
initialize thePcDistinct : IO.Ref (Option (thm → ExceptT String IO thm)) ← IO.mkRef none

/-- `prove_constructors_distinct` as built once. -/
private unsafe def pcDistinct (ax : thm) : ExceptT String IO thm := do
  match ← thePcDistinct.get with
  | some f => f ax
  | none =>
    let f ← HolMath.IndTypes.prove_constructors_distinct BETA_THM Nm.numK NUM_EQ_CONV
    thePcDistinct.set (some f)
    f ax

/-- `extend_rectype_net (tyname,(_,_,rth))` (ind_types.ml 1026-1033), the
    stateful Session wrapper: reads the current three store contents from their
    refs, calls the pure library `extend_rectype_net`, and writes the updated
    contents back.  The library performs the actual proofs and net/store
    construction. -/
unsafe def extend_rectype_net (entry : String × (Int × thm × thm)) :
    IO (Except String Unit) := do
  let curNet ← theBasicRectypeNet.get
  let curDist ← readDistinctnessStore
  let curInj ← theInjectivityStore.get
  match ← (HolMath.IndTypes.extend_rectype_net pcDistinct pcInjective
            entry curNet curDist curInj).run with
  | .error e => return .error e
  | .ok (net', dist', inj') => do
      theBasicRectypeNet.set net'
      theDistinctnessStore.set (some dist')
      theInjectivityStore.set inj'
      return .ok ()

/-- `do_list extend_rectype_net (!inductive_type_store)` (ind_types.ml 1035):
    run `extend_rectype_net` over every type currently in the inductive type
    store. -/
unsafe def do_extend_rectype_net : IO (Except String Unit) := do
  let rec go : List (String × (Int × thm × thm)) → IO (Except String Unit)
    | [] => return .ok ()
    | e :: es => do
      match ← extend_rectype_net e with
      | .error err => return .error err
      | .ok _ => go es
  go (← get_inductive_type_store)

/-- `inductive_type_store := ["list",(2,list_INDUCT,list_RECURSION);
    "option",(2,option_INDUCT,option_RECURSION);
    "sum",(2,sum_INDUCT,sum_RECURSION)] @ (!inductive_type_store)`
    (ind_types.ml 1009-1013).

    Prepends the `list`/`option`/`sum` entries (in that OCaml order, so `list`
    ends up first) onto the current store.  Each entry is `(2, INDUCT,
    RECURSION)`.  Because these three type constructors are defined
    once-per-process by the IndTypes bootstrap, the caller that defines them
    passes their `INDUCT`/`RECURSION` theorems here to register them. -/
unsafe def add_list_option_sum_to_store
    (list_INDUCT list_RECURSION option_INDUCT option_RECURSION
     sum_INDUCT sum_RECURSION : thm) : IO Unit := do
  let cur ← theInductiveTypeStore.get
  let base := cur.getD [("bool", (2, C.bool_INDUCT, C.bool_RECURSION))]
  theInductiveTypeStore.set (some (
    ("list",   (2, list_INDUCT,   list_RECURSION))   ::
    ("option", (2, option_INDUCT, option_RECURSION)) ::
    ("sum",    (2, sum_INDUCT,    sum_RECURSION))     :: base))

/-- Caches for `option_DISTINCT` and `option_INJ`, proved once when
    ind_types.ml's bootstrap runs (`buildRaw3Ctx`). -/
initialize theOptionDistinct : IO.Ref (Option thm) ← IO.mkRef none
initialize theOptionInj : IO.Ref (Option thm) ← IO.mkRef none

/-- `option_DISTINCT` (ind_types.ml 1049-1051):
    `prove (`!a:A. ~(SOME a = NONE)`, REWRITE_TAC[distinctness "option"])`.
    Reads the distinctness store (populated by `extend_rectype_net`). -/
unsafe def option_DISTINCT : IO (Except String thm) := do
  if let some th := ← theOptionDistinct.get then return .ok th
  let store ← readDistinctnessStore
  match HolMath.IndTypes.distinctness store "option" with
  | .error e => return .error e
  | .ok th =>
    match ← (HolMath.IndTypes.prove_option_DISTINCT th).run with
    | .ok r => do theOptionDistinct.set (some r); return .ok r
    | .error e => return .error e

/-- `option_INJ` (ind_types.ml 1053-1055):
    `prove (`!a b:A. SOME a = SOME b <=> a = b`, REWRITE_TAC[injectivity "option"])`.
    Reads the injectivity store (populated by `extend_rectype_net`). -/
unsafe def option_INJ : IO (Except String thm) := do
  if let some th := ← theOptionInj.get then return .ok th
  let store ← theInjectivityStore.get
  match HolMath.IndTypes.injectivity store "option" with
  | .error e => return .error e
  | .ok th =>
    match ← (HolMath.IndTypes.prove_option_INJ th).run with
    | .ok r => do theOptionInj.set (some r); return .ok r
    | .error e => return .error e

/-- `ISO`, `ISO_REFL`, `ISO_FUN`, `ISO_USAGE` (ind_types.ml 1061-1080),
    threading the Session `new_definition` and `MESON_TAC`. -/
unsafe def setupISO : IO (Except String (thm × thm × thm × thm)) :=
  HolMath.IndTypes.setupISO new_definition MESON_TAC

/- ---------------------------------------------------------------------- -/
/- Layer-record accessors, exposed so an external process (e.g. a probe or -/
/- a consumer that bootstraps the once-per-process IndTypes types) can     -/
/- build `setupIndTypes` / `define_type_raw3`.  These simply surface the   -/
/- private cached bundles.                                                 -/
/- ---------------------------------------------------------------------- -/

/-- The `theorems.ml` layer record. -/
unsafe def theoremThms : TheoremThms := T
/-- The `class.ml` layer record. -/
unsafe def classThms : ClassThms := C
/-- TEMP (ChkT2 verification, revert): expose BoolThms. -/
unsafe def boolThmsTMP : BoolThms := B
/-- The `nums.ml` layer record. -/
unsafe def numsThms : HolMath.Nums.NumsThms := Nm
/-- The `arith.ml` part-1 record. -/
unsafe def arith1Thms : HolMath.Arith.ArithThms1 := Ar1
/-- The `arith.ml` part-2 record. -/
unsafe def arith2Thms : HolMath.Arith.ArithThms2 := Ar2
/-- The `arith.ml` part-5 record. -/
unsafe def arith5Thms : HolMath.Arith.ArithThms5 := Ar5
/-- The `arith.ml` part-3 record. -/
unsafe def arith3Thms : HolMath.Arith.ArithThms3 := Ar3
/-- The `arith.ml` part-4 record. -/
unsafe def arith4Thms : HolMath.Arith.ArithThms4 := Ar4
/-- The `pair.ml` theorem record. -/
unsafe def pairThms : PairThms := Pr
/-- The `calc_num.ml` `ARITH_*` rewrites record. -/
unsafe def calcNumArith : HolMath.CalcNum.ArithRewrites := CnA
/-- The `trivia.ml` layer record. -/
unsafe def triviaThms : TriviaThms := Tv

/- ---------------------------------------------------------------------- -/
/- ind_types.ml: the overall `define_type` (lines 1388-1414).             -/
/- ---------------------------------------------------------------------- -/

/-- `the_inductive_types = ref [...]` (ind_types.ml 1390-1394), keyed by the
    RAW SPEC STRING and seeded with the `list`/`option`/`sum` entries (in that
    OCaml order, `list` first).  The seed theorems are produced once-per-process
    by the IndTypes bootstrap (they are NOT Session CAFs), so the ref starts
    `none` and a bootstrapping caller seeds it via `seed_the_inductive_types`.
    The library `define_type` takes/returns the contents; this ref holds them. -/
initialize theTheInductiveTypes :
    IO.Ref (Option (List (String × (thm × thm)))) ← IO.mkRef none

/-- Seed `the_inductive_types` with the three bootstrap entries (ind_types.ml
    1390-1394): `"list = NIL | CONS A list"`, `"option = NONE | SOME A"`,
    `"sum = INL A | INR B"`, in that order.  Called by the process that
    bootstraps the `list`/`option`/`sum` types, passing their induction and
    recursion theorems. -/
unsafe def seed_the_inductive_types
    (list_INDUCT list_RECURSION option_INDUCT option_RECURSION
     sum_INDUCT sum_RECURSION : thm) : IO Unit :=
  theTheInductiveTypes.set (some [
    ("list = NIL | CONS A list", (list_INDUCT, list_RECURSION)),
    ("option = NONE | SOME A", (option_INDUCT, option_RECURSION)),
    ("sum = INL A | INR B", (sum_INDUCT, sum_RECURSION))])

/-- `!the_inductive_types` — the current contents (defaulting to `[]` before the
    bootstrap seeding runs). -/
def the_inductive_types : IO (List (String × (thm × thm))) := do
  return (← theTheInductiveTypes.get).getD []

/- ---------------------------------------------------------------------- -/
/- ind_types.ml: the once-per-process bootstrap.                           -/
/- ---------------------------------------------------------------------- -/

/-- Cache for the two option theorems (ind_types.ml 889-896). -/
initialize theOptionThms : IO.Ref (Option (thm × thm)) ← IO.mkRef none

/-- Cache for the `ind_types.ml` injection-infrastructure bundle
    (`setupIndTypes`, ind_types.ml 13-300).  It DECLARES constants (`NUMPAIR`,
    `INJN`, `ZCONSTR`, `FCONS`, ...), the `ZRECSPACE` inductive predicate and
    the `recspace` TYPE, so it must run exactly once per process. -/
initialize theIndTypes : IO.Ref (Option HolMath.IndTypes.IndTypesThms) ← IO.mkRef none

/-- Cache for the fully-assembled nested-type capability bundle, together with
    the bootstrap types it needs.  Building it runs, in order: `setupIndTypes`,
    `mkRawCtx`, `setupISO`, then `sum` (via `define_type_raw1`), `OUTL`/`OUTR`,
    `option` and `list` (via `define_type_raw2`).  Every one of those DEFINES A
    TYPE, and each type name is definable only ONCE PER PROCESS, so this is a
    strict one-shot: the cache is what makes `define_type` callable more than
    once. -/
initialize theRaw3Ctx : IO.Ref (Option HolMath.IndTypes.DefTypeRaw3) ← IO.mkRef none

private unsafe def buildRaw3Ctx : IO (Except String HolMath.IndTypes.DefTypeRaw3) :=
  ExceptT.run do
  let nbtd := fun a b c d => Kernel.new_basic_type_definition a b c d
  let dnir := derive_nonschematic_inductive_relations
  let pmh  := prove_monotonicity_hyps
  -- ind_types.ml 13-300: the injection infrastructure.
  let K ← (HolMath.IndTypes.setupIndTypes numsThms arith1Thms arith2Thms
             arith5Thms calcNumArith triviaThms ETA_AX new_definition
             new_specification new_inductive_definition new_recursive_definition
             prove_inductive_relations_exist : IO (Except String _))
  theIndTypes.set (some K)
  -- ind_types.ml 302-738: the first define_type_raw.
  let D ← HolMath.IndTypes.setupDefTypeRaw FST SND K.FCONS BETA_THM K.CONSTR_REC indAux.1
            mk_pair dnir pmh new_definition nbtd
  -- ind_types.ml 768-774: the sum type, then OUTL/OUTR.
  let (sumI, sumR) ← HolMath.IndTypes.sum_INDUCT_RECURSION D
  let outl ← HolMath.IndTypes.defineOUTL new_recursive_definition sumR
  let outr ← HolMath.IndTypes.defineOUTR new_recursive_definition sumR
  -- ind_types.ml 785-886: the second define_type_raw; option and list.
  let D2 ← HolMath.IndTypes.setupDefTypeRaw2 D outl outr
  let (optI, optR) ← HolMath.IndTypes.option_INDUCT_RECURSION D2
  let (lstI, lstR) ← HolMath.IndTypes.list_INDUCT_RECURSION D2
  -- ind_types.ml 889-896: FORALL_OPTION_THM and EXISTS_OPTION_THM.
  if (← theOptionThms.get).isNone then
    let fa ← HolMath.IndTypes.prove_FORALL_OPTION_THM optI
    let ex ← HolMath.IndTypes.prove_EXISTS_OPTION_THM fa MESON MESON_TAC
    theOptionThms.set (some (fa, ex))
  -- ind_types.ml 1009-1013: add list/option/sum to `inductive_type_store`, in
  -- OCaml order, ahead of whatever is already there (`bool`, `prod`, `1`).
  let existing ← (theInductiveTypeStore.get : IO (Option _))
  let base := existing.getD [("bool", (2, C.bool_INDUCT, C.bool_RECURSION))]
  let seeded := [("list", (2, lstI, lstR)), ("option", (2, optI, optR)),
                 ("sum", (2, sumI, sumR))] ++ base
  theInductiveTypeStore.set (some seeded)
  -- ind_types.ml 1035: `do_list extend_rectype_net (!inductive_type_store)`.
  for entry in seeded do
    let _ ← (extend_rectype_net entry : IO (Except String Unit))
  -- ind_types.ml 1049-1055: option_DISTINCT and option_INJ.
  let _ ← ExceptT.mk option_DISTINCT
  let _ ← ExceptT.mk option_INJ
  -- ind_types.ml 1061: ISO is defined after sum, option and list (1009-1035).
  let (iso, isoRefl, isoFun, isoUsage) ← (setupISO : IO (Except String _))
  -- ind_types.ml 1084-1281: the third define_type_raw.  `getStore` and
  -- `addEntries` act on the live refs: `create_auxiliary_clauses` must see
  -- types added after this bootstrap ran.  `addEntries` does both of
  -- ind_types.ml 1385-1386's side effects, in order.
  let R ← HolMath.IndTypes.setupDefTypeRaw3 D2 iso isoRefl isoFun isoUsage
    ETA_AX SELECT_AX C.FUN_EQ_THM
    (do return (← theInductiveTypeStore.get).getD [])
    (fun es => do
      let cur ← theInductiveTypeStore.get
      theInductiveTypeStore.set (some (es ++ cur.getD []))
      -- `do_list extend_rectype_net newentries` (ind_types.ml 1386) is part of
      -- a `;`-sequence, so its failure propagates.
      for e in es do
        match ← extend_rectype_net e with
        | .error err => return .error err
        | .ok _ => pure ()
      return .ok ())
  -- ind_types.ml 1390-1394: seed the spec-string keyed store.
  liftM (seed_the_inductive_types lstI lstR optI optR sumI sumR)
  return R

/- ---------------------------------------------------------------------- -/
/- The three derived-theorem provers (ind_types.ml 902-1006), with their   -/
/- dependencies supplied.  `prove_constructors_distinct` returns a LIST in  -/
/- the library (the OCaml conjoins the pairwise inequalities), so the       -/
/- wrapper conjoins it back to match the OCaml's single theorem.           -/
/- ---------------------------------------------------------------------- -/

/-- `prove_constructors_injective ax` (ind_types.ml 902-926). -/
unsafe def prove_constructors_injective (ax : thm) : IO (Except String thm) :=
  (pcInjective ax).run

/-- `prove_constructors_distinct ax` (ind_types.ml 929-959).  The OCaml returns
    `end_itlist CONJ` of the pairwise inequalities; the library returns them as
    a list, so conjoin here. -/
unsafe def prove_constructors_distinct (ax : thm) : IO (Except String thm) :=
  (pcDistinct ax).run

/-- `prove_cases_thm th` (ind_types.ml 964-1006). -/
unsafe def prove_cases_thm (th : thm) : IO (Except String thm) :=
  (HolMath.IndTypes.prove_cases_thm indAux.1 th).run

/-- The nested-type capability bundle, built once per process and cached. -/
unsafe def raw3Ctx : HolMath.IndTypes.DefTypeRaw3 :=
  match unsafeIO (do
    match ← theRaw3Ctx.get with
    | some X => pure X
    | none =>
      match ← buildRaw3Ctx with
      | .ok X => do theRaw3Ctx.set (some X); pure X
      | .error e => panic! s!"buildRaw3Ctx failed: {e}") with
  | .ok X => X | _ => panic! "Session.raw3Ctx: bootstrap not run"

/- ---------------------------------------------------------------------- -/
/- The store readers, forcing the bootstrap first.                        -/
/-                                                                        -/
/- OCaml runs ALL of ind_types.ml EAGERLY at load time, so by the time any -/
/- caller can ask `distinctness "list"` or `cases "list"` the stores are   -/
/- already populated.  This project is lazy-on-demand instead, so without  -/
/- forcing, those queries would report an empty store and FAIL where the   -/
/- OCaml succeeds.  Each reader below therefore forces the once-per-       -/
/- process bootstrap and then reads the LIVE ref (never a snapshot).       -/
/- ---------------------------------------------------------------------- -/

/-- Force the `ind_types.ml` bootstrap, then run `act` against the live refs. -/
private unsafe def withIndTypesBootstrap {α : Type} [Inhabited α] (act : IO α) : α :=
  match unsafeIO (do let _ ← raw3Ctx.getStore; act) with
  | .ok a => a
  | _ => panic! "Session.withIndTypesBootstrap: ind_types bootstrap failed"

/-- `distinctness ty = assoc ty (!distinctness_store)` (ind_types.ml 1041).

    Reads the LIVE ref, not the `distinctness_store` CAF: Lean memoizes that
    CAF, so if it were evaluated before the bootstrap populated the ref it would
    be frozen with the empty contents. -/
unsafe def distinctness (ty : String) : Except String thm :=
  withIndTypesBootstrap (do
    return HolMath.IndTypes.distinctness (← readDistinctnessStore) ty)

/-- `injectivity ty = assoc ty (!injectivity_store)` (ind_types.ml 1043).
    Reads the LIVE ref, for the same reason as `distinctness`. -/
unsafe def injectivity (ty : String) : Except String thm :=
  withIndTypesBootstrap (do
    return HolMath.IndTypes.injectivity (← theInjectivityStore.get) ty)

/-- `cases ty` (ind_types.ml 1045-1047).  Reads the LIVE store ref. -/
unsafe def cases (ty : String) : IO (Except String thm) := do
  let store ← raw3Ctx.getStore
  (HolMath.IndTypes.cases indAux.1 num_CASES store ty).run

/-- `list_INDUCT` / `list_RECURSION` (ind_types.ml 884-886).  Read out of the
    inductive type store, which forces the once-per-process bootstrap.  These
    are what `lists.ml` threads into every one of its ~28
    `new_recursive_definition list_RECURSION` calls and into
    `LIST_INDUCT_TAC`. -/
private unsafe def storeEntry (ty : String) : Int × thm × thm :=
  withIndTypesBootstrap (do
    let store := (← theInductiveTypeStore.get).getD []
    match HolCore.Lib.assoc ty store with
    | Except.ok e => return e
    | Except.error _ => panic! s!"Session.storeEntry: no entry for {ty}")

unsafe def list_INDUCT : thm := (storeEntry "list").2.1
unsafe def list_RECURSION : thm := (storeEntry "list").2.2
unsafe def option_INDUCT : thm := (storeEntry "option").2.1
unsafe def option_RECURSION : thm := (storeEntry "option").2.2
unsafe def sum_INDUCT : thm := (storeEntry "sum").2.1
unsafe def sum_RECURSION : thm := (storeEntry "sum").2.2

/-- The ind_types.ml 13-300 injection infrastructure, filled in by
    `buildRaw3Ctx` (forced here through the `option` store entry). -/
private unsafe def IndK : HolMath.IndTypes.IndTypesThms :=
  match unsafeIO (do
    let _ ← IO.mkRef (concl option_INDUCT)
    theIndTypes.get) with
  | .ok (some k) => k
  | _ => panic! "Session.IndK: ind_types layer not initialised"

unsafe def NUMPAIR : thm := IndK.NUMPAIR
unsafe def NUMPAIR_INJ_LEMMA : thm := IndK.NUMPAIR_INJ_LEMMA
unsafe def NUMPAIR_INJ : thm := IndK.NUMPAIR_INJ
unsafe def NUMPAIR_DEST : thm := IndK.NUMPAIR_DEST
unsafe def NUMSUM : thm := IndK.NUMSUM
unsafe def NUMSUM_INJ : thm := IndK.NUMSUM_INJ
unsafe def NUMSUM_DEST : thm := IndK.NUMSUM_DEST
unsafe def INJN : thm := IndK.INJN
unsafe def INJN_INJ : thm := IndK.INJN_INJ
unsafe def INJA : thm := IndK.INJA
unsafe def INJA_INJ : thm := IndK.INJA_INJ
unsafe def INJF : thm := IndK.INJF
unsafe def INJF_INJ : thm := IndK.INJF_INJ
unsafe def INJP : thm := IndK.INJP
unsafe def INJP_INJ : thm := IndK.INJP_INJ
unsafe def ZCONSTR : thm := IndK.ZCONSTR
unsafe def ZBOT : thm := IndK.ZBOT
unsafe def ZCONSTR_ZBOT : thm := IndK.ZCONSTR_ZBOT
unsafe def ZRECSPACE_RULES : thm := IndK.ZRECSPACE_RULES
unsafe def ZRECSPACE_INDUCT : thm := IndK.ZRECSPACE_INDUCT
unsafe def ZRECSPACE_CASES : thm := IndK.ZRECSPACE_CASES
unsafe def BOTTOM : thm := IndK.BOTTOM
unsafe def CONSTR : thm := IndK.CONSTR
unsafe def MK_REC_INJ : thm := IndK.MK_REC_INJ
unsafe def DEST_REC_INJ : thm := IndK.DEST_REC_INJ
unsafe def CONSTR_BOT : thm := IndK.CONSTR_BOT
unsafe def CONSTR_INJ : thm := IndK.CONSTR_INJ
unsafe def CONSTR_IND : thm := IndK.CONSTR_IND
unsafe def FCONS_UNDO : thm := IndK.FCONS_UNDO
unsafe def FNIL : thm := IndK.FNIL
unsafe def INJ_INVERSE2 : thm := IndK.INJ_INVERSE2

private unsafe def optionThms : thm × thm :=
  match unsafeIO (do
    match ← theOptionThms.get with
    | some p => pure p
    | none =>
      match ← (HolMath.IndTypes.prove_FORALL_OPTION_THM option_INDUCT).run with
      | .error e => panic! s!"FORALL_OPTION_THM failed: {e}"
      | .ok fa =>
        match ← (HolMath.IndTypes.prove_EXISTS_OPTION_THM fa MESON MESON_TAC).run with
        | .error e => panic! s!"EXISTS_OPTION_THM failed: {e}"
        | .ok ex => do theOptionThms.set (some (fa, ex)); pure (fa, ex)) with
  | .ok p => p
  | _ => panic! "Session.optionThms: not initialised"

/-- `FORALL_OPTION_THM` (ind_types.ml 889). -/
unsafe def FORALL_OPTION_THM : thm := optionThms.1
/-- `EXISTS_OPTION_THM` (ind_types.ml 893). -/
unsafe def EXISTS_OPTION_THM : thm := optionThms.2

/-- `define_type s` (ind_types.ml 1396-1414), the stateful Session wrapper.
    Reads the current `the_inductive_types` contents, calls the pure-ish library
    `define_type` (which does the crude RAW-STRING benignity check, the four
    validation checks, and `define_type_raw3` on a miss), then writes back the
    (possibly) updated store.  The nested-recursion machinery is supplied via
    the `Raw3Ctx` `X`; prefer `define_type`, which supplies it from the cached
    once-per-process bootstrap. -/
unsafe def define_type_with (X : HolMath.IndTypes.DefTypeRaw3) (s : String) :
    IO (Except String (thm × thm)) := do
  let store ← the_inductive_types
  match ← (HolMath.IndTypes.define_type X store s).run with
  | .error e => return .error e
  | .ok (retval, store') => do
      theTheInductiveTypes.set (some store')
      return .ok retval

/-- `define_type s` (ind_types.ml 1396-1414) — the USER-FACING entry point, with
    the `Raw3Ctx` supplied automatically from the cached bootstrap. -/
unsafe def define_type (s : String) : IO (Except String (thm × thm)) :=
  define_type_with raw3Ctx s

/- ---------------------------------------------------------------------- -/
/- ind_types.ml: UNWIND_CONV / MATCH_CONV / FORALL_UNWIND_CONV            -/
/- (lines 1421-1572).                                                     -/
/- ---------------------------------------------------------------------- -/

/-- Cache for the `(UNWIND_CONV, MATCH_CONV)` pair, built once by
    `setupUnwindMatch` (which also performs the `do_list extend_basic_convs`
    side effect).  `BREAK_CONS_CONV`'s `!basic_rectype_net` is threaded in as
    `theBasicRectypeNet.get`, an IO action RE-READ on every application - NOT a
    snapshot.  A snapshot would freeze the net and silently lose the rewrites
    for every type defined after this cache was populated. -/
initialize theUnwindMatch : IO.Ref (Option (ioconv × ioconv)) ← IO.mkRef none

private unsafe def unwindMatchPair : ioconv × ioconv :=
  match unsafeIO (do
    match ← theUnwindMatch.get with
    | some p => pure p
    | none =>
      let P := pairAux
      -- ind_types.ml 1421 follows the third define_type_raw (1084), whose
      -- REWRITE_FUN_EQ_RULE net is made from basic_net() before these
      -- basic convs are added.
      let _ ← raw3Ctx.getStore
      match ← (HolMath.IndTypes.setupUnwindMatch
                 P.MATCH P.SEQPATTERN P.FUNCTION P.UNGUARDED_PATTERN P.GUARDED_PATTERN
                 P.GEQ_DEF C.COND_ID C.COND_CLAUSES T.CONJ_ASSOC
                 MESON_TAC theBasicRectypeNet.get extend_basic_convs).run with
      | .ok p => do theUnwindMatch.set (some p); pure p
      | .error e => panic! s!"setupUnwindMatch failed: {e}") with
  | .ok p => p | _ => panic! "Session.unwindMatchPair: setupUnwindMatch not run"

/-- `UNWIND_CONV` (ind_types.ml 1421-1539): `CHANGED_CONV UNWIND_CONV`. -/
unsafe def UNWIND_CONV : ioconv := unwindMatchPair.1

/-- `MATCH_CONV` (ind_types.ml 1421-1539):
    `MATCH_SEQPATTERN_CONV_GEN ORELSEC MATCH_ONEPATTERN_CONV_GEN`. -/
unsafe def MATCH_CONV : ioconv := unwindMatchPair.2

/-- Cache for `FORALL_UNWIND_CONV` (ind_types.ml 1540-1572). -/
initialize theForallUnwind : IO.Ref (Option ioconv) ← IO.mkRef none

/-- `FORALL_UNWIND_CONV` (ind_types.ml 1540-1572). -/
private unsafe def forallUnwindIO : IO (Except String ioconv) := do
  match ← theForallUnwind.get with
  | some c => return .ok c
  | none =>
    match ← (HolMath.IndTypes.setupForallUnwind MESON).run with
    | .error e => return .error e
    | .ok c => do theForallUnwind.set (some c); return .ok c

unsafe def FORALL_UNWIND_CONV : ioconv := fun tm => do
  match ← forallUnwindIO with
  | .ok c => c tm
  | .error e => return .error e

/- ---------------------------------------------------------------------- -/
/- lists.ml: the reproved list induction and the basic definitions layer.  -/
/- ---------------------------------------------------------------------- -/

/-- `list_INDUCT'` (lists.ml 18-20): the `!h t. P t ==> P (CONS h t)`-shaped
    re-proof of the stored `list_INDUCT`, used by `LIST_INDUCT_TAC`.  Computed
    once and cached. -/
initialize theListInduct' : IO.Ref (Option thm) ← IO.mkRef none

unsafe def list_INDUCT' : thm :=
  match unsafeIO (do
    match ← theListInduct'.get with
    | some th => pure th
    | none =>
      match ← (HolMath.Lists.prove_list_INDUCT' list_INDUCT).run with
      | .ok th => do theListInduct'.set (some th); pure th
      | .error e => panic! s!"prove_list_INDUCT' failed: {e}") with
  | .ok th => th | _ => panic! "Session.list_INDUCT': not initialised"

/-- `LIST_INDUCT_TAC` (lists.ml 17): structural induction on lists. -/
unsafe def LIST_INDUCT_TAC : tactic := HolMath.Lists.LIST_INDUCT_TAC list_INDUCT'

/-- Cache for the `lists.ml` basic-definitions layer (the 28 recursive
    definitions of lines 28-143).  `setupListDefs` DECLARES CONSTANTS (`HD`,
    `TL`, `APPEND`, ...), so it must run exactly ONCE PER PROCESS. -/
initialize theListDefs : IO.Ref (Option HolMath.Lists.ListDefs) ← IO.mkRef none

unsafe def listDefs : HolMath.Lists.ListDefs :=
  match unsafeIO (do
    match ← theListDefs.get with
    | some d => pure d
    | none =>
      let distinctness_list ← (match distinctness "list" with
        | .ok th => pure th | .error e => panic! s!"distinctness list: {e}")
      match ← (HolMath.Lists.setupListDefs list_RECURSION num_RECURSION
                 distinctness_list new_recursive_definition).run with
      | .ok d => do theListDefs.set (some d); pure d
      | .error e => panic! s!"setupListDefs failed: {e}") with
  | .ok d => d | _ => panic! "Session.listDefs: setupListDefs not run"

/- ---------------------------------------------------------------------- -/
/- lists.ml: the theorem bundles and the evaluation conversions.           -/
/- ---------------------------------------------------------------------- -/

/-- Cache for `ListThms1` (lists.ml 148-400, 50 theorems). -/
initialize theListThms1 : IO.Ref (Option HolMath.Lists.ListThms1) ← IO.mkRef none

unsafe def listThms1 : HolMath.Lists.ListThms1 :=
  match unsafeIO (do
    match ← theListThms1.get with
    | some t => pure t
    | none =>
      let dl ← (match distinctness "list" with
        | .ok th => pure th | .error e => panic! s!"distinctness list: {e}")
      let il ← (match injectivity "list" with
        | .ok th => pure th | .error e => panic! s!"injectivity list: {e}")
      match ← (HolMath.Lists.setupListThms1 listDefs dl il list_INDUCT'
                 MESON_TAC ASM_MESON_TAC MESON Nm Ar1 Ar2 Ar3 Tv Pr).run with
      | .ok t => do theListThms1.set (some t); pure t
      | .error e => panic! s!"setupListThms1 failed: {e}") with
  | .ok t => t | _ => panic! "Session.listThms1: setupListThms1 not run"

/-- Cache for `ListThms2` (lists.ml 405-697, 51 theorems). -/
initialize theListThms2 : IO.Ref (Option HolMath.Lists.ListThms2) ← IO.mkRef none

unsafe def listThms2 : HolMath.Lists.ListThms2 :=
  match unsafeIO (do
    match ← theListThms2.get with
    | some t => pure t
    | none =>
      match ← (HolMath.Lists.setupListThms2 listDefs listThms1 list_INDUCT list_INDUCT'
                 MESON_TAC ASM_MESON_TAC MESON Nm Ar1 Ar2 Ar3 Ar5 Tv CnA o_DEF I_DEF).run with
      | .ok t => do theListThms2.set (some t); pure t
      | .error e => panic! s!"setupListThms2 failed: {e}") with
  | .ok t => t | _ => panic! "Session.listThms2: setupListThms2 not run"

/-- Cache for the `LENGTH_CONV`/`EL_CONV`/`REVERSE_CONV`/`LIST_OF_SEQ_CONV`
    proformas (lists.ml 751-876). -/
initialize theListEvalConvs :
    IO.Ref (Option HolMath.Lists.ListEvalConvs) ← IO.mkRef none

private unsafe def listEvalConvs : HolMath.Lists.ListEvalConvs :=
  match unsafeIO (do
    match ← theListEvalConvs.get with
    | some p => pure p
    | none =>
      match ← (HolMath.Lists.setupListEvalConvs listDefs listThms1 Ar1
                 NUM_SUC_CONV num_CONV).run with
      | .ok p => do theListEvalConvs.set (some p); pure p
      | .error e => panic! s!"setupListEvalConvs failed: {e}") with
  | .ok p => p | _ => panic! "Session.listEvalConvs: not run"

/-- `LENGTH_CONV` (lists.ml 751-778). -/
unsafe def LENGTH_CONV : ioconv := fun tm => listEvalConvs.LENGTH_CONV tm

/-- `EL_CONV` (lists.ml 780-807). -/
unsafe def EL_CONV : ioconv := fun tm => listEvalConvs.EL_CONV tm

/-- `REVERSE_CONV` (lists.ml 809-834). -/
unsafe def REVERSE_CONV : ioconv := fun tm => listEvalConvs.REVERSE_CONV tm

/-- `LIST_OF_SEQ_CONV` (lists.ml 836-876). -/
unsafe def LIST_OF_SEQ_CONV : ioconv := fun tm => listEvalConvs.LIST_OF_SEQ_CONV tm

/-- `LIST_CONV conv` (lists.ml 740-746): apply `conv` down a list. -/
def LIST_CONV : conv → conv := HolMath.Lists.LIST_CONV

/-- `LIST_CONV` for IO-valued conversions (e.g. `num_CONV`), which is the form
    HOL Light's documented `LIST_CONV num_CONV` usage needs here. -/
unsafe def LIST_CONV_IO : ioconv → ioconv := HolMath.Lists.LIST_CONV_IO

/-- `mk_cons h t` (lists.ml 702-705). -/
def mk_cons : term → term → IO (Except String term) := HolMath.Lists.mk_cons

/-- `mk_list (tms,ty)` (lists.ml 707-712). -/
def mk_list : List term → hol_type → IO (Except String term) :=
  HolMath.Lists.mk_list

/-- `mk_flist tms` (lists.ml 714-716). -/
def mk_flist : List term → IO (Except String term) := HolMath.Lists.mk_flist

/-- Cache for the two extra monotonicity theorems `MONO_ALL`/`MONO_ALL2`
    (lists.ml 722-731).  Forcing this bundle performs the lists.ml 733
    registration side effect:
      `monotonicity_theorems := [MONO_ALL; MONO_ALL2] @ !monotonicity_theorems`
    i.e. it PREPENDS both, in that order, onto the LIVE `theMonotonicityTheorems`
    ref — mirroring `class.ml`'s `MONO_COND` registration.  The ref (not a
    captured snapshot) is updated so that `MONO_TAC`/`prove_monotonicity_hyps`,
    which RE-READ `theMonotonicityTheorems` on every use, see the additions. -/
initialize theListsMono : IO.Ref (Option HolMath.Lists.MonoAllThms) ← IO.mkRef none

unsafe def listsMono : HolMath.Lists.MonoAllThms :=
  match unsafeIO (do
    match ← theListsMono.get with
    | some m => pure m
    | none =>
      match ← (HolMath.Lists.setupMonoAll listDefs list_INDUCT' ASM_MESON_TAC).run with
      | .ok m => do
          theListsMono.set (some m)
          -- lists.ml 733:
          --   monotonicity_theorems := [MONO_ALL; MONO_ALL2] @ !monotonicity_theorems
          let cur ← theMonotonicityTheorems.get
          let base := cur.getD
            [T.MONO_AND, T.MONO_OR, T.MONO_IMP, T.MONO_NOT, T.MONO_EXISTS, T.MONO_FORALL]
          theMonotonicityTheorems.set (some (m.MONO_ALL :: m.MONO_ALL2 :: base))
          pure m
      | .error e => panic! s!"setupMonoAll failed: {e}") with
  | .ok m => m | _ => panic! "Session.listsMono: setupMonoAll not run"

/-- `MONO_ALL` (lists.ml 722-725); forcing it registers both extra monotonicity
    theorems onto `theMonotonicityTheorems`. -/
unsafe def MONO_ALL : thm := listsMono.MONO_ALL
/-- `MONO_ALL2` (lists.ml 727-731). -/
unsafe def MONO_ALL2 : thm := listsMono.MONO_ALL2

/- ---------------------------------------------------------------------- -/
/- lists.ml: the `char` type, `string` abbreviation, and the char/string  -/
/- syntax constructors + equality conversions (lines 877-998).            -/
/- ---------------------------------------------------------------------- -/

/-- `new_type_abbrev (s, ty)` (Preterm): install `s` as a parsing abbreviation
    for the type `ty`.  Session wrapper matching the OCaml one-pair call
    `new_type_abbrev("string",`:char list`)`. -/
def new_type_abbrev (s : String) (ty : hol_type) : IO Unit :=
  HolCore.Preterm.new_type_abbrev s ty
/- ---------------------------------------------------------------------- -/
/- Type of characters, like the HOL88 "ascii" type, with syntax           -/
/- constructors and equality conversions for chars and strings.           -/
/- ---------------------------------------------------------------------- -/

/-- Cache for `(char_INDUCT, char_RECURSION)` (lists.ml 881-882):
    `define_type "char = ASCII bool bool bool bool bool bool bool bool"`.
    `define_type` is an END-TO-END exercise of the ind_types machinery on an
    EIGHT-argument constructor, and each type name is definable only ONCE PER
    PROCESS, so the result is cached.  Forcing it also installs the `string`
    type abbreviation (lists.ml 884). -/
initialize theCharType : IO.Ref (Option (thm × thm)) ← IO.mkRef none

private unsafe def charType : thm × thm :=
  match unsafeIO (do
    match ← theCharType.get with
    | some x => pure x
    | none => do
      match ← define_type
          "char = ASCII bool bool bool bool bool bool bool bool" with
      | .error e => panic! s!"define_type char: {e}"
      | .ok x => do
          -- lists.ml 884: new_type_abbrev("string",`:char list`).
          match ← HolCore.Parser.parse_type "char list" with
          | .error e => panic! s!"string abbrev parse: {e}"
          | .ok ty => do new_type_abbrev "string" ty; theCharType.set (some x); pure x) with
  | .ok x => x | _ => panic! "Session.charType: define_type char not run"

/-- `char_INDUCT` (lists.ml 881): the induction theorem for `char`, quantifying
    over a predicate on `char` with one clause for the 8-argument `ASCII`
    constructor. -/
unsafe def char_INDUCT : thm := charType.1
/-- `char_RECURSION` (lists.ml 882): the recursion theorem for `char`. -/
unsafe def char_RECURSION : thm := charType.2

/-- The `char` `hol_type` (forces `define_type "char"`), used as `mk_string`'s
    element type. -/
unsafe def charTy : hol_type :=
  match unsafeIO (do
    -- Force `define_type "char"` so `parse_type "char"` can resolve the name.
    -- `let _ := charType` does NOT force a Lean CAF, so the CAF is DEMANDED
    -- through a ref.
    let _ ← IO.mkRef charType
    HolCore.Parser.parse_type "char") with
  | .ok (.ok ty) => ty
  | _ => panic! "Session.charTy: parse char failed"

/-- Cache for the `CharStringMachinery` bundle (lists.ml 886-998): the
    pre-proved `ASCII` inequality families, the string-cons lemmas, the
    256-entry `codes` array, and the schematic variables.  Forcing it also
    forces `define_type "char"` (needed for `injectivity "char"`) and proves
    the two `lists.ml` cons lemmas `CONS_11`/`NOT_CONS_NIL` it depends on. -/
initialize theCharStringMachinery :
    IO.Ref (Option HolMath.Lists.CharStringMachinery) ← IO.mkRef none

private unsafe def charStringMachinery : HolMath.Lists.CharStringMachinery :=
  match unsafeIO (do
    match ← theCharStringMachinery.get with
    | some m => pure m
    | none => do
      -- Force `define_type "char"` so `injectivity "char"` is populated.
      -- Must DEMAND the CAF: `let _ := charType` does not force one.
      let _ ← IO.mkRef charType
      let injChar ← (match injectivity "char" with
        | .ok th => pure th | .error e => panic! s!"injectivity char: {e}")
      match ← (HolMath.Lists.setupCharStringMachinery injChar listThms1.CONS_11
                 listThms1.NOT_CONS_NIL MESON_TAC).run with
      | .ok m => do theCharStringMachinery.set (some m); pure m
      | .error e => panic! s!"setupCharStringMachinery failed: {e}") with
  | .ok m => m | _ => panic! "Session.charStringMachinery: not run"

/-- `dest_char` (lists.ml 886, 900): `char_of_term`. -/
def dest_char : term → Except String Char := HolMath.Lists.dest_char

/-- `mk_char` (lists.ml 919): the `ASCII` term for a character. -/
unsafe def mk_char (c : Char) : Except String term :=
  HolMath.Lists.mk_char charStringMachinery c

/-- `dest_string` (lists.ml 901-908): the (escaped) string a `char list`
    denotes. -/
def dest_string : term → Except String String := HolMath.Lists.dest_string

/-- `mk_string` (lists.ml 920-923): the `char list` term for a string. -/
unsafe def mk_string (s : String) : IO (Except String term) :=
  HolMath.Lists.mk_string charStringMachinery s

/-- `CHAR_EQ_CONV` (lists.ml 980-984): decide equality of two chars. -/
unsafe def CHAR_EQ_CONV : conv := HolMath.Lists.CHAR_EQ_CONV charStringMachinery

/-- `STRING_EQ_CONV` (lists.ml 985-988): decide equality of two strings. -/
unsafe def STRING_EQ_CONV : conv := HolMath.Lists.STRING_EQ_CONV charStringMachinery

/- ---------------------------------------------------------------------- -/
/- realax.ml: the overloading / interface primitives.  These live in       -/
/- HolCore.Preterm and HolCore.Printer and mutate global parser state;     -/
/- realax.ml drives them directly, so re-export them under their OCaml     -/
/- names for the `setupRealAx*` functions to consume.                      -/
/- ---------------------------------------------------------------------- -/

/-- `make_overloadable` (preterm.ml): declare a symbol overloadable at a
    generic type. -/
def make_overloadable (s : String) (ty : hol_type) :
    IO (Except String Unit) := Preterm.make_overloadable s ty

/-- `overload_interface` (preterm.ml): add a mapping for an overloaded symbol. -/
def overload_interface (s : String) (tm : term) :
    IO (Except String Unit) := Preterm.overload_interface s tm

/-- `override_interface` (preterm.ml): replace all mappings for a symbol. -/
def override_interface (s : String) (tm : term) :
    IO (Except String Unit) := Preterm.override_interface s tm

/-- `reduce_interface` (preterm.ml): remove ONE mapping for a symbol. -/
def reduce_interface (s : String) (tm : term) :
    IO (Except String Unit) := Preterm.reduce_interface s tm

/-- `remove_interface` (preterm.ml): remove ALL mappings for a symbol. -/
def remove_interface (s : String) : IO Unit := Preterm.remove_interface s

/-- `prioritize_overload` (preterm.ml): make a type the default for overloads. -/
def prioritize_overload (ty : hol_type) : IO Unit :=
  Preterm.prioritize_overload ty

/-- `parse_as_infix` (printer.ml). -/
unsafe def parse_as_infix (p : String × (Int × String)) : IO Unit :=
  Printer.parse_as_infix p

/-- `parse_as_prefix` (printer.ml). -/
def parse_as_prefix (s : String) : IO Unit := Printer.parse_as_prefix s

/-- `AC ADD_AC`: the AC-normalising rule for natural-number addition.  The
    library's `Theorems.AC` takes its AC-suite as a parameter; realax.ml uses
    both this and the multiplicative form, so name them here. -/
unsafe def AC_ADD (tm : term) : IO (Except String thm) :=
  Theorems.AC B T.REFL_CLAUSE Ar1.ADD_AC tm

/-- `AC MULT_AC`: the AC-normalising rule for natural-number multiplication. -/
unsafe def AC_MULT (tm : term) : IO (Except String thm) :=
  Theorems.AC B T.REFL_CLAUSE Ar2.MULT_AC tm

/- ---------------------------------------------------------------------- -/
/- realax.ml: the construction of the real numbers, in TEN stages.         -/
/-                                                                        -/
/- The stages MUST run in realax.ml's own order, because each mutates      -/
/- global state the next one depends on: `setupRealAxOverloads` installs   -/
/- the infix/overload declarations without which `x === y` will not parse, -/
/- and `setupNadd`/`setupHreal`/`setupReal` each DECLARE CONSTANTS AND A   -/
/- TYPE (`nadd`, `hreal`, `real`) so each may run only ONCE PER PROCESS.   -/
/- That ordering is enforced structurally: every stage takes the previous  -/
/- stage's record as a parameter, so forcing a later bundle forces all its -/
/- predecessors first, in order.                                           -/
/- ---------------------------------------------------------------------- -/

/-- Guard for realax.ml 17-48 (the overloading head).  It returns no theorems,
    only parser-state side effects, so it needs its own once-only flag.

    This is deliberately an `IO` ACTION rather than a memoised `Unit` CAF: a
    `let _ := <caf>` does NOT force a Lean CAF, so a CAF here would silently
    never run and the `===`/`<<=`/`++`/`**` infixes would be missing, making
    every later stage fail to parse its own statements.  Each stage below
    `await`s this instead. -/
initialize theRealAxOverloads : IO.Ref Bool ← IO.mkRef false

private unsafe def ensureRealAxOverloads : IO Unit := do
  if ← theRealAxOverloads.get then pure () else
    -- realax.ml 27-41 builds the generic types of the overloadable symbols with
    -- `mk_type "num" []`, so the `nums.ml` layer must already have run.  This
    -- stage takes no bundle parameters, so nothing would force it implicitly;
    -- read a `nums` theorem to force that layer first.  (`let _ := Nm...` would
    -- NOT force it — a Lean CAF needs an IO action to be forced.)
    let _ ← IO.mkRef (concl Nm.num_RECURSION)
    -- Load-order fidelity (load-bearing): `hol_lib.ml` loads calc_num.ml
    -- BEFORE realax.ml, so every calc_num proforma is built while `:num` is
    -- still the default for the overloaded arithmetic symbols.  realax.ml's
    -- `overload_interface` calls then make `:real` the schematic default
    -- (`m + n` parses as `num` before this stage, `real` after; closed terms
    -- like `1 + 2` are unaffected, so a check on `1 + 2` alone cannot detect
    -- it).  Our layers are lazy, so force `CnP` here to reproduce the order;
    -- without it `CnP` could build after the overloads and fail with
    -- `TAC_PROOF: Unsolved goals`.
    let _ ← IO.mkRef (concl CnP.BITS_INJ)
    -- normalizer.ml (also before realax.ml): SEMIRING_PTHS parses `m + n`-style
    -- terms too, and the real-arithmetic layers now use this proved instance.
    let _ ← IO.mkRef (concl NmzP.2)
    match ← (HolMath.RealAx.setupRealAxOverloads parse_as_infix
               make_overloadable overload_interface).run with
    | .ok () => theRealAxOverloads.set true
    | .error e => panic! s!"setupRealAxOverloads failed: {e}"

/-- Cache for `DistThms` (realax.ml 54-247): `dist` and the bounds lemmas.
    NOTE `dist(m,n) = ...` has a PAIRED left-hand side, so this stage must be
    given `new_definition_pair`, not `new_definition`. -/
initialize theDist : IO.Ref (Option HolMath.RealAx.DistThms) ← IO.mkRef none

private unsafe def Dst : HolMath.RealAx.DistThms :=
  match unsafeIO (do
    match ← theDist.get with
    | some d => pure d
    | none =>
      ensureRealAxOverloads
      match ← (HolMath.RealAx.setupDist Nm Ar1 Ar2 Ar3 Ar4 Ar5
                 SUB_ELIM_THM (Drule.HIGHER_REWRITE_CONV_ths B) NUM_CANCEL_CONV
                 new_definition_pair).run with
      | .ok d => do theDist.set (some d); pure d
      | .error e => panic! s!"setupDist failed: {e}") with
  | .ok d => d | _ => panic! "Session.Dst: setupDist not run"

/-- Cache for `NaddThms` (realax.ml 253-363): the `nadd` type of nearly
    multiplicative functions.  DECLARES the `nadd` type — once per process. -/
initialize theNadd : IO.Ref (Option HolMath.RealAx.NaddThms) ← IO.mkRef none

private unsafe def Nad : HolMath.RealAx.NaddThms :=
  match unsafeIO (do
    match ← theNadd.get with
    | some d => pure d
    | none =>
      ensureRealAxOverloads
      match ← (HolMath.RealAx.setupNadd Nm Ar1 Ar2 Ar3 Ar4 Dst ETA_AX
                 NUM_CANCEL_CONV CnA.ARITH
                 LE_IMP new_definition
                 (fun a b c d => Kernel.new_basic_type_definition a b c d)
                 override_interface).run with
      | .ok d => do theNadd.set (some d); pure d
      | .error e => panic! s!"setupNadd failed: {e}") with
  | .ok d => d | _ => panic! "Session.Nad: setupNadd not run"

/-- Cache for `NaddOrderThms` (realax.ml 366-511): `===`, `&` and `<<=`. -/
initialize theNaddOrder : IO.Ref (Option HolMath.RealAx.NaddOrderThms) ←
  IO.mkRef none

private unsafe def NOr : HolMath.RealAx.NaddOrderThms :=
  match unsafeIO (do
    match ← theNaddOrder.get with
    | some d => pure d
    | none =>
      ensureRealAxOverloads
      match ← (HolMath.RealAx.setupNaddOrder Ar1 Ar2 Ar3 Ar4 Dst Nad
                 LE_IMP new_definition override_interface).run with
      | .ok d => do theNaddOrder.set (some d); pure d
      | .error e => panic! s!"setupNaddOrder failed: {e}") with
  | .ok d => d | _ => panic! "Session.NOr: setupNaddOrder not run"

/-- Cache for `NaddArithThms` (realax.ml 514-700): `++` and `**`. -/
initialize theNaddArith : IO.Ref (Option HolMath.RealAx.NaddArithThms) ←
  IO.mkRef none

private unsafe def NAr : HolMath.RealAx.NaddArithThms :=
  match unsafeIO (do
    match ← theNaddArith.get with
    | some d => pure d
    | none =>
      ensureRealAxOverloads
      match ← (HolMath.RealAx.setupNaddArith Ar1 Ar2 Ar3 Ar4 Dst Nad NOr
                 ETA_AX LE_IMP new_definition override_interface).run with
      | .ok d => do theNaddArith.set (some d); pure d
      | .error e => panic! s!"setupNaddArith failed: {e}") with
  | .ok d => d | _ => panic! "Session.NAr: setupNaddArith not run"

/-- Cache for `NaddCompleteThms` (realax.ml 703-929): the Archimedean property
    and `NADD_COMPLETE`. -/
initialize theNaddComplete : IO.Ref (Option HolMath.RealAx.NaddCompleteThms) ←
  IO.mkRef none

private unsafe def NCm : HolMath.RealAx.NaddCompleteThms :=
  match unsafeIO (do
    match ← theNaddComplete.get with
    | some d => pure d
    | none =>
      ensureRealAxOverloads
      match ← (HolMath.RealAx.setupNaddComplete Ar1 Ar2 Ar3 Ar4 Dst Nad
                 NOr NAr MESON_TAC ASM_MESON_TAC).run with
      | .ok d => do theNaddComplete.set (some d); pure d
      | .error e => panic! s!"setupNaddComplete failed: {e}") with
  | .ok d => d | _ => panic! "Session.NCm: setupNaddComplete not run"

/-- Cache for `NaddInvAuxThms` (realax.ml 933-1179): `nadd_rinv` and the eleven
    lemmas leading to the multiplicative inverse. -/
initialize theNaddInvAux : IO.Ref (Option HolMath.RealAx.NaddInvAuxThms) ←
  IO.mkRef none

private unsafe def NIv : HolMath.RealAx.NaddInvAuxThms :=
  match unsafeIO (do
    match ← theNaddInvAux.get with
    | some d => pure d
    | none =>
      ensureRealAxOverloads
      match ← (HolMath.RealAx.setupNaddInvAux Nm Ar1 Ar2 Ar3 Ar4 DIVISION
                 Dst Nad NOr NAr NCm CnA.ARITH ARITH_SUC new_definition).run with
      | .ok d => do theNaddInvAux.set (some d); pure d
      | .error e => panic! s!"setupNaddInvAux failed: {e}") with
  | .ok d => d | _ => panic! "Session.NIv: setupNaddInvAux not run"

/-- Cache for `HrealThms` (realax.ml 1182-1381): the SECOND type construction,
    `hreal` = `nadd` quotiented by `===`.  DECLARES the `hreal` type — once per
    process. -/
initialize theHreal : IO.Ref (Option HolMath.RealAx.HrealThms) ← IO.mkRef none

private unsafe def Hrl : HolMath.RealAx.HrealThms :=
  match unsafeIO (do
    match ← theHreal.get with
    | some d => pure d
    | none =>
      ensureRealAxOverloads
      match ← (HolMath.RealAx.setupHreal Ar1 Ar2 Ar3 Ar4 Dst Nad NOr NAr NCm NIv
                 ASM_MESON_TAC new_definition
                 define_quotient_type lift_function lift_theorem
                 override_interface overload_interface).run with
      | .ok d => do theHreal.set (some d); pure d
      | .error e => panic! s!"setupHreal failed: {e}") with
  | .ok d => d | _ => panic! "Session.Hrl: setupHreal not run"

/-- Cache for `TrealThms` (realax.ml 1385-1708): the signed-real
    representatives on `hreal#hreal`.  All seven definitions here have PAIRED
    left-hand sides, so this stage takes `new_definition_pair`. -/
initialize theTreal : IO.Ref (Option HolMath.RealAx.TrealThms) ← IO.mkRef none

private unsafe def Trl : HolMath.RealAx.TrealThms :=
  match unsafeIO (do
    match ← theTreal.get with
    | some d => pure d
    | none =>
      ensureRealAxOverloads
      match ← (HolMath.RealAx.setupTreal Pr Ar1 Ar2 Hrl
                 new_definition_pair).run with
      | .ok d => do theTreal.set (some d); pure d
      | .error e => panic! s!"setupTreal failed: {e}") with
  | .ok d => d | _ => panic! "Session.Trl: setupTreal not run"

/-- Cache for `RealThms` (realax.ml 1711-1973): the THIRD AND FINAL type
    construction — `real` = `hreal#hreal` quotiented by `treal_eq` — plus the
    friendly interface, the additional definitions, and `REAL_COMPLETE` (the
    supremum property).  DECLARES the `real` type — once per process.
    Its last act is realax.ml's own interface cleanup, which retires the
    `hreal` overloads and DELETES the nadd notations `**`, `++`, `<<=`, `===`,
    `fn` and `afn`; those no longer parse once this has run. -/
initialize theReal : IO.Ref (Option HolMath.RealAx.RealThms) ← IO.mkRef none

private unsafe def Rl : HolMath.RealAx.RealThms :=
  match unsafeIO (do
    match ← theReal.get with
    | some d => pure d
    | none =>
      ensureRealAxOverloads
      match ← (HolMath.RealAx.setupReal Pr Hrl Trl
                 Nm.num_RECURSION new_definition
                 new_recursive_definition define_quotient_type lift_function
                 lift_theorem overload_interface parse_as_prefix parse_as_infix
                 prioritize_overload reduce_interface remove_interface).run with
      | .ok d => do theReal.set (some d); pure d
      | .error e => panic! s!"setupReal failed: {e}") with
  | .ok d => d | _ => panic! "Session.Rl: setupReal not run"

/- Public accessors for the realax.ml bundles.  Reading any of these forces
   the whole chain up to and including it, in realax.ml's order. -/

/-- The `realax.ml` `dist` record (54-247). -/
unsafe def distThms : HolMath.RealAx.DistThms := Dst
/-- The `realax.ml` `nadd` record (253-363). -/
unsafe def naddThms : HolMath.RealAx.NaddThms := Nad
/-- The `realax.ml` nadd-ordering record (366-511). -/
unsafe def naddOrderThms : HolMath.RealAx.NaddOrderThms := NOr
/-- The `realax.ml` nadd-arithmetic record (514-700). -/
unsafe def naddArithThms : HolMath.RealAx.NaddArithThms := NAr
/-- The `realax.ml` nadd-completeness record (703-929). -/
unsafe def naddCompleteThms : HolMath.RealAx.NaddCompleteThms := NCm
/-- The `realax.ml` inverse-auxiliary record (933-1179). -/
unsafe def naddInvAuxThms : HolMath.RealAx.NaddInvAuxThms := NIv
/-- The `realax.ml` `hreal` record (1182-1381). -/
unsafe def hrealThms : HolMath.RealAx.HrealThms := Hrl
/-- The `realax.ml` signed-real record (1385-1708). -/
unsafe def trealThms : HolMath.RealAx.TrealThms := Trl
/-- The `realax.ml` `real` record (1711-1973). -/
unsafe def realThms : HolMath.RealAx.RealThms := Rl

/-- `prioritize_real` (realax.ml 1780): make `:real` the default for overloaded
    symbols.  Forces the `real` construction first, since the type must exist. -/
unsafe def prioritize_real : IO Unit := do
  let _ ← IO.mkRef (concl Rl.REAL_COMPLETE)
  match ← (mk_type "real" []) with
  | .ok ty => prioritize_overload ty
  | .error e => panic! s!"prioritize_real: {e}"

/- Selected `real` theorems, for convenience at the top level. -/

/-- `REAL_COMPLETE` (realax.ml 1907): the supremum property. -/
unsafe def REAL_COMPLETE     : thm := Rl.REAL_COMPLETE
/-- `REAL_ADD_LINV` (realax.ml 1738): `|- !x. --x + x = &0`. -/
unsafe def REAL_ADD_LINV     : thm := Rl.REAL_ADD_LINV
/-- `REAL_MUL_LINV` (realax.ml 1738): `|- !x. ~(x = &0) ==> inv x * x = &1`. -/
unsafe def REAL_MUL_LINV     : thm := Rl.REAL_MUL_LINV
/-- `REAL_LE_TOTAL` (realax.ml 1738): `|- !x y. x <= y \/ y <= x`. -/
unsafe def REAL_LE_TOTAL     : thm := Rl.REAL_LE_TOTAL
/-- `REAL_ADD_LDISTRIB` (realax.ml 1738). -/
unsafe def REAL_ADD_LDISTRIB : thm := Rl.REAL_ADD_LDISTRIB
/-- `real_sub` (realax.ml 1786): `|- !x y. x - y = x + --y`. -/
unsafe def real_sub          : thm := Rl.real_sub
/-- `real_abs` (realax.ml 1801). -/
unsafe def real_abs          : thm := Rl.real_abs
/-- `real_pow` (realax.ml 1804): the two recursion clauses. -/
unsafe def real_pow          : thm := Rl.real_pow

/- ---------------------------------------------------------------------- -/
/- calc_int.ml: calculation with integer-valued reals.                     -/
/-                                                                        -/
/- Seven stages, in calc_int.ml's own order.  As with realax.ml the order  -/
/- is enforced STRUCTURALLY - each stage takes the previous stage's record  -/
/- as a parameter - so forcing a later one forces its predecessors.        -/
/- ---------------------------------------------------------------------- -/

/-- Cache for `RatSyntax` (calc_int.ml 32-60): the terms `mk_realintconst` and
    `term_of_rat` close over. -/
initialize theRatSyntax : IO.Ref (Option HolMath.CalcInt.RatSyntax) ← IO.mkRef none

private unsafe def RSyn : HolMath.CalcInt.RatSyntax :=
  match unsafeIO (do
    match ← theRatSyntax.get with
    | some d => pure d
    | none => do
      -- This stage PARSES `real_of_num`, `(--)` and `(/)`, so the real layer
      -- must already exist.  It takes no bundle parameter, so nothing would
      -- force it implicitly - force it here.  (`let _ := Rl...` would NOT
      -- force a Lean CAF; it needs an IO action.)
      let _ ← IO.mkRef (concl Rl.REAL_COMPLETE)
      match ← (HolMath.CalcInt.setupRatSyntax mk_numeral).run with
      | .ok d => do theRatSyntax.set (some d); pure d
      | .error e => panic! s!"setupRatSyntax failed: {e}") with
  | .ok d => d | _ => panic! "Session.RSyn: setupRatSyntax not run"

/-- Cache for `CalcIntThms` (calc_int.ml 66-171): the nineteen elementary real
    theorems derived from the realax.ml axioms. -/
initialize theCalcInt : IO.Ref (Option HolMath.CalcInt.CalcIntThms) ← IO.mkRef none

private unsafe def CiT : HolMath.CalcInt.CalcIntThms :=
  match unsafeIO (do
    match ← theCalcInt.get with
    | some d => pure d
    | none =>
      match ← (HolMath.CalcInt.setupCalcInt Ar2 Ar5 Nm Rl MESON_TAC).run with
      | .ok d => do theCalcInt.set (some d); pure d
      | .error e => panic! s!"setupCalcInt failed: {e}") with
  | .ok d => d | _ => panic! "Session.CiT: setupCalcInt not run"

/-- Cache for the five comparison conversions (calc_int.ml 177-246). -/
initialize theRealIntCompare :
  IO.Ref (Option HolMath.CalcInt.RealIntCompareConvs) ← IO.mkRef none

private unsafe def CiV : HolMath.CalcInt.RealIntCompareConvs :=
  match unsafeIO (do
    match ← theRealIntCompare.get with
    | some d => pure d
    | none =>
      match ← (HolMath.CalcInt.setupRealIntCompareConvs NUM_EQ_CONV
                 NUM_LE_CONV NUM_LT_CONV CiT Rl Ar1 Ar2 Ar3).run with
      | .ok d => do theRealIntCompare.set (some d); pure d
      | .error e => panic! s!"setupRealIntCompareConvs failed: {e}") with
  | .ok d => d | _ => panic! "Session.CiV: setupRealIntCompareConvs not run"

/-- Cache for the six arithmetic conversions (calc_int.ml 248-374). -/
initialize theRealIntArith :
  IO.Ref (Option HolMath.CalcInt.RealIntArithConvs) ← IO.mkRef none

private unsafe def CiW : HolMath.CalcInt.RealIntArithConvs :=
  match unsafeIO (do
    match ← theRealIntArith.get with
    | some d => pure d
    | none => do
      match ← (HolMath.CalcInt.setupRealIntArithConvs NUM_MULT_CONV NUM_ADD_CONV
                 NUM_EXP_CONV NUM_EVEN_CONV mk_numeral CiT Rl).run with
      | .ok d => do theRealIntArith.set (some d); pure d
      | .error e => panic! s!"setupRealIntArithConvs failed: {e}") with
  | .ok d => d | _ => panic! "Session.CiW: setupRealIntArithConvs not run"

/- Public accessors for the calc_int.ml bundles. -/

/-- The `calc_int.ml` rational-syntax record (32-60). -/
unsafe def ratSyntax : HolMath.CalcInt.RatSyntax := RSyn
/-- The `calc_int.ml` elementary-real-theorem record (66-171). -/
unsafe def calcIntThms : HolMath.CalcInt.CalcIntThms := CiT
/-- The `calc_int.ml` comparison conversions (177-246). -/
unsafe def realIntCompareConvs : HolMath.CalcInt.RealIntCompareConvs := CiV
/-- The `calc_int.ml` arithmetic conversions (248-374). -/
unsafe def realIntArithConvs : HolMath.CalcInt.RealIntArithConvs := CiW

/- The six syntax operations, with the `RatSyntax` record already supplied. -/

/-- `is_realintconst` (calc_int.ml 16). -/
def is_realintconst : term → Bool := HolMath.CalcInt.is_realintconst
/-- `dest_realintconst` (calc_int.ml 23). -/
def dest_realintconst : term → Except String Rat :=
  HolMath.CalcInt.dest_realintconst
/-- `mk_realintconst` (calc_int.ml 32). -/
unsafe def mk_realintconst (x : Rat) : Except String term :=
  HolMath.CalcInt.mk_realintconst RSyn x
/-- `is_ratconst` (calc_int.ml 38). -/
def is_ratconst : term → Bool := HolMath.CalcInt.is_ratconst
/-- `rat_of_term` (calc_int.ml 46). -/
def rat_of_term : term → Except String Rat := HolMath.CalcInt.rat_of_term
/-- `term_of_rat` (calc_int.ml 54). -/
unsafe def term_of_rat (x : Rat) : Except String term :=
  HolMath.CalcInt.term_of_rat RSyn x

/- The five comparison and six arithmetic conversions, as plain `ioconv`s. -/

/-- `REAL_INT_LE_CONV` (calc_int.ml 177). -/
unsafe def REAL_INT_LE_CONV  : ioconv := CiV.REAL_INT_LE_CONV
/-- `REAL_INT_LT_CONV` (calc_int.ml 177). -/
unsafe def REAL_INT_LT_CONV  : ioconv := CiV.REAL_INT_LT_CONV
/-- `REAL_INT_GE_CONV` (calc_int.ml 177). -/
unsafe def REAL_INT_GE_CONV  : ioconv := CiV.REAL_INT_GE_CONV
/-- `REAL_INT_GT_CONV` (calc_int.ml 177). -/
unsafe def REAL_INT_GT_CONV  : ioconv := CiV.REAL_INT_GT_CONV
/-- `REAL_INT_EQ_CONV` (calc_int.ml 177). -/
unsafe def REAL_INT_EQ_CONV  : ioconv := CiV.REAL_INT_EQ_CONV
/-- `REAL_INT_NEG_CONV` (calc_int.ml 248). -/
unsafe def REAL_INT_NEG_CONV : ioconv := CiW.REAL_INT_NEG_CONV
/-- `REAL_INT_MUL_CONV` (calc_int.ml 255). -/
unsafe def REAL_INT_MUL_CONV : ioconv := CiW.REAL_INT_MUL_CONV
/-- `REAL_INT_ADD_CONV` (calc_int.ml 274). -/
unsafe def REAL_INT_ADD_CONV : ioconv := CiW.REAL_INT_ADD_CONV
/-- `REAL_INT_SUB_CONV` (calc_int.ml 348). -/
unsafe def REAL_INT_SUB_CONV : ioconv := CiW.REAL_INT_SUB_CONV
/-- `REAL_INT_POW_CONV` (calc_int.ml 353). -/
unsafe def REAL_INT_POW_CONV : ioconv := CiW.REAL_INT_POW_CONV
/-- `REAL_INT_ABS_CONV` (calc_int.ml 369). -/
unsafe def REAL_INT_ABS_CONV : ioconv := CiW.REAL_INT_ABS_CONV

/-- Cache for `real_int_red_conv_list` (calc_int.ml 376-387). -/
initialize theRealIntRedConvList : IO.Ref (Option (List (term × ioconv))) ← IO.mkRef none

/-- `real_int_red_conv_list` (calc_int.ml 376-387), built once. -/
unsafe def real_int_red_conv_list : IO (Except String (List (term × ioconv))) := do
  match ← theRealIntRedConvList.get with
  | some l => return .ok l
  | none =>
    match ← (HolMath.CalcInt.real_int_red_conv_list CiV CiW).run with
    | .ok l => do theRealIntRedConvList.set (some l); return .ok l
    | .error e => return .error e

/-- Cache for `REAL_INT_RED_CONV` (calc_int.ml 389).  Memoised because the
    OCaml SNAPSHOTS `basic_net()` once when the conversion is defined; building
    the net afresh on every call would not reproduce that. -/
initialize theRealIntRed : IO.Ref (Option ioconv) ← IO.mkRef none

/-- `REAL_INT_RED_CONV` (calc_int.ml 389): one reduction step on an
    integer-constant term, via the eleven-entry net over `basic_net()`. -/
unsafe def REAL_INT_RED_CONV : ioconv := fun tm => do
  match ← theRealIntRed.get with
  | some c => c tm
  | none =>
    match ← (do HolMath.CalcInt.REAL_INT_RED_CONV (← ExceptT.mk real_int_red_conv_list)).run with
    | .ok c => do theRealIntRed.set (some c); c tm
    | .error e => return .error s!"REAL_INT_RED_CONV: {e}"

/-- `REAL_INT_REDUCE_CONV` (calc_int.ml 394): `DEPTH_CONV REAL_INT_RED_CONV`. -/
unsafe def REAL_INT_REDUCE_CONV : ioconv := Simp.depthConvIO REAL_INT_RED_CONV

/-- `real_int_compute_add_convs` (calc_int.ml 396): register the eleven
    conversions with a `compset`. -/
unsafe def real_int_compute_add_convs (cs : HolMath.Compute.compset) :
    IO (Except String Unit) :=
  (do HolMath.CalcInt.real_int_compute_add_convs (← ExceptT.mk real_int_red_conv_list) cs).run

/-- Cache for `REAL_INT_COMPUTE_CONV` (calc_int.ml 403): call-by-value
    reduction over the boolean compset extended with those conversions.  The
    OCaml builds its compset once, so memoise. -/
initialize theRealIntCompute : IO.Ref (Option ioconv) ← IO.mkRef none

/-- `REAL_INT_COMPUTE_CONV` (calc_int.ml 403). -/
unsafe def REAL_INT_COMPUTE_CONV : ioconv := fun tm => do
  match ← theRealIntCompute.get with
  | some c => c tm
  | none =>
    let cl ← real_int_red_conv_list
    let mk : ExceptT String IO ioconv := do
      HolMath.CalcInt.REAL_INT_COMPUTE_CONV (← liftExcept cl) bool_compset WEAK_CBV_CONV
    match ← mk.run with
    | .ok c => do theRealIntCompute.set (some c); c tm
    | .error e => return .error s!"REAL_INT_COMPUTE_CONV: {e}"

/- ---------------------------------------------------------------------- -/
/- realarith.ml: universal linear real decision procedure.                 -/
/-                                                                        -/
/- Six layers, in realarith.ml's own order.  Each `setupX` takes the       -/
/- previous layers' records as parameters, so forcing a later one forces   -/
/- its predecessors.  The ONE non-structural dependency is that            -/
/- `setupGenRealArith2Ctx` proves its 42-clause ABSMAXMIN proforma by       -/
/- running the fully-applied bootstrapping `REAL_ARITH1` closure - which is -/
/- the whole reason HOL Light defines REAL_ARITH twice.  The CAF order is   -/
/- therefore  L -> G -> A -> RA1 -> (real_arith1 closure) -> G2 -> RA2.     -/
/- ---------------------------------------------------------------------- -/

/- `RealArith1Ctx`/`RealArith2Ctx` carry only `ioconv`/`PolynomialConvs`
   fields and are NOT declared `Inhabited` in the pure library, but the CAF
   extraction pattern below (`match unsafeIO ... | _ => panic!`) needs an
   `Inhabited` fallback.  Every field is ultimately an `ioconv` (a function
   into `IO`, hence inhabited), so Lean can derive these. -/
deriving instance Inhabited for HolMath.Normalizer.PolynomialConvs
deriving instance Inhabited for HolMath.RealArith.RealArith1Ctx
deriving instance Inhabited for HolMath.RealArith.RealArith2Ctx

/-- REAL_LINEAR_PROVER's constants: linear_ineqs' `&1` (realarith.ml 388),
    then lin_of_hol's `&1`, `&0`, `(+):real->real->real`,
    `(*):real->real->real` (realarith.ml 446-449).  Parsed once. -/
initialize theRealArithConsts :
  IO.Ref (Option (term × term × term × term × term)) ← IO.mkRef none

private unsafe def RaC : term × term × term × term × term :=
  match unsafeIO (do
    match ← theRealArithConsts.get with
    | some d => pure d
    | none =>
      match ← (do
        -- realarith.ml 446-447 parse them untyped; Session builds this at
        -- realarith.ml's position, where `&` means `real_of_num`.
        let lpOne ← Parser.parse_term "&1"
        let one  ← Parser.parse_term "&1"
        let zero ← Parser.parse_term "&0"
        let add  ← Parser.parse_term "(+):real->real->real"
        let mul  ← Parser.parse_term "(*):real->real->real"
        pure (lpOne, one, zero, add, mul) : ExceptT String IO (term × term × term × term × term)).run with
      | .ok d => do theRealArithConsts.set (some d); pure d
      | .error e => panic! s!"RealArith consts parse failed: {e}") with
  | .ok d => d | _ => panic! "Session.RaC: RealArith consts not parsed"

/-- Cache for the twenty-nine driving lemmas (realarith.ml 16-160). -/
initialize theRealArithLemmas :
  IO.Ref (Option HolMath.RealArith.RealArithLemmas) ← IO.mkRef none

private unsafe def RaL : HolMath.RealArith.RealArithLemmas :=
  match unsafeIO (do
    match ← theRealArithLemmas.get with
    | some d => pure d
    | none =>
      match ← (HolMath.RealArith.setupRealArithLemmas Ar2 Ar3 CiT Rl
                 MESON_TAC num_CONV).run with
      | .ok d => do theRealArithLemmas.set (some d); pure d
      | .error e => panic! s!"setupRealArithLemmas failed: {e}") with
  | .ok d => d | _ => panic! "Session.RaL: setupRealArithLemmas not run"

/-- Cache for `GenRealArith1Ctx` (realarith.ml 185-256): the six proformas and
    the term constants of the bootstrapping framework. -/
initialize theGenRealArith1Ctx :
  IO.Ref (Option HolMath.RealArith.GenRealArith1Ctx) ← IO.mkRef none

private unsafe def GrA1 : HolMath.RealArith.GenRealArith1Ctx :=
  match unsafeIO (do
    match ← theGenRealArith1Ctx.get with
    | some d => pure d
    | none =>
      match ← (HolMath.RealArith.setupGenRealArith1Ctx CiT Rl RaL MESON_TAC).run with
      | .ok d => do theGenRealArith1Ctx.set (some d); pure d
      | .error e => panic! s!"setupGenRealArith1Ctx failed: {e}") with
  | .ok d => d | _ => panic! "Session.GrA1: setupGenRealArith1Ctx not run"

/-- Cache for `LinearProverAliens` (realarith.ml 477-479): the two alien
    lemmas. -/
initialize theLinearProverAliens :
  IO.Ref (Option HolMath.RealArith.LinearProverAliens) ← IO.mkRef none

private unsafe def LpA : HolMath.RealArith.LinearProverAliens :=
  match unsafeIO (do
    match ← theLinearProverAliens.get with
    | some d => pure d
    | none =>
      match ← (HolMath.RealArith.setupLinearProverAliens Rl RaL).run with
      | .ok d => do theLinearProverAliens.set (some d); pure d
      | .error e => panic! s!"setupLinearProverAliens failed: {e}") with
  | .ok d => d | _ => panic! "Session.LpA: setupLinearProverAliens not run"

/-- Cache for `RealArith1Ctx` (realarith.ml 495-509): the six polynomial
    conversions and `deabs_conv` of the bootstrapping instance. -/
initialize theRealArith1Ctx :
  IO.Ref (Option HolMath.RealArith.RealArith1Ctx) ← IO.mkRef none

private unsafe def RA1c : HolMath.RealArith.RealArith1Ctx :=
  match unsafeIO (do
    match ← theRealArith1Ctx.get with
    | some d => pure d
    | none =>
      match ← (HolMath.RealArith.setupRealArith1Ctx Rl RaL
                 TRUTH NmzP.2 num_CONV
                 is_realintconst
                 REAL_INT_ADD_CONV REAL_INT_MUL_CONV REAL_INT_POW_CONV
                 NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV).run with
      | .ok d => do theRealArith1Ctx.set (some d); pure d
      | .error e => panic! s!"setupRealArith1Ctx failed: {e}") with
  | .ok d => d | _ => panic! "Session.RA1c: setupRealArith1Ctx not run"

/-- `REAL_LINEAR_PROVER` (realarith.ml 385-489), with its `RatSyntax`,
    alien lemmas and `lin_of_hol` constants supplied. -/
unsafe def REAL_LINEAR_PROVER : HolMath.RealArith.PsProver :=
  let (lp_one_tm, one_tm, zero_tm, add_tm, mul_tm) := RaC
  HolMath.RealArith.REAL_LINEAR_PROVER RSyn LpA lp_one_tm one_tm zero_tm add_tm mul_tm

/-- Cache for the first `REAL_ARITH` (realarith.ml 494-511). -/
initialize theRealArith1 : IO.Ref (Option ioconv) ← IO.mkRef none

/-- The first `REAL_ARITH` (realarith.ml 494-511), built once.  It proves
    `setupGenRealArith2Ctx`'s ABSMAXMIN proforma. -/
private unsafe def realArith1Closure : ioconv := fun tm => do
  match ← theRealArith1.get with
  | some c => c tm
  | none =>
    match ← (HolMath.RealArith.REAL_ARITH1 Cn.nnf GrA1 RA1c
               PRESIMP_CONV NNF_CONV CONDS_ELIM_CONV SKOLEM_CONV PRENEX_CONV WEAK_DNF_CONV
               mk_realintconst REAL_INT_EQ_CONV REAL_INT_GE_CONV REAL_INT_GT_CONV
               REAL_LINEAR_PROVER).run with
    | .error e => return .error e
    | .ok c => do theRealArith1.set (some c); c tm

/-- Cache for `GenRealArith2Ctx` (realarith.ml 518-641): the two hardwired
    abs/max/min elimination conversions and the three `pth`s.

    THIS LAYER IS EXPENSIVE - about 8.8 seconds - because its 42-clause
    ABSMAXMIN proforma is proved by the full linear decision procedure
    (`realArith1Closure`).  HOL Light itself wraps that proof in `time` for the
    same reason.  Memoised here, and never forced by any cheaper accessor. -/
initialize theGenRealArith2Ctx :
  IO.Ref (Option HolMath.RealArith.GenRealArith2Ctx) ← IO.mkRef none

private unsafe def GrA2 : HolMath.RealArith.GenRealArith2Ctx :=
  match unsafeIO (do
    match ← theGenRealArith2Ctx.get with
    | some d => pure d
    | none =>
      match ← (HolMath.RealArith.setupGenRealArith2Ctx Rl realArith1Closure).run with
      | .ok d => do theGenRealArith2Ctx.set (some d); pure d
      | .error e => panic! s!"setupGenRealArith2Ctx failed: {e}") with
  | .ok d => d | _ => panic! "Session.GrA2: setupGenRealArith2Ctx not run"

/-- Cache for `RealArith2Ctx` (realarith.ml 652-657): the six polynomial
    conversions of the second instance (identical semiring recipe to
    `RA1c`, MINUS `deabs_conv`). -/
initialize theRealArith2Ctx :
  IO.Ref (Option HolMath.RealArith.RealArith2Ctx) ← IO.mkRef none

private unsafe def RA2c : HolMath.RealArith.RealArith2Ctx :=
  match unsafeIO (do
    match ← theRealArith2Ctx.get with
    | some d => pure d
    | none =>
      match ← (HolMath.RealArith.setupRealArith2Ctx RaL
                 TRUTH NmzP.2 num_CONV
                 is_realintconst
                 REAL_INT_ADD_CONV REAL_INT_MUL_CONV REAL_INT_POW_CONV
                 NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV).run with
      | .ok d => do theRealArith2Ctx.set (some d); pure d
      | .error e => panic! s!"setupRealArith2Ctx failed: {e}") with
  | .ok d => d | _ => panic! "Session.RA2c: setupRealArith2Ctx not run"

/- Public accessors for the realarith.ml bundles. -/

/-- The `realarith.ml` twenty-nine driving lemmas (16-160). -/
unsafe def realArithLemmas : HolMath.RealArith.RealArithLemmas := RaL
/-- The `realarith.ml` bootstrapping-framework context (185-256): six
    proformas and the ~20 term constants of `GEN_REAL_ARITH1`. -/
unsafe def genRealArith1Ctx : HolMath.RealArith.GenRealArith1Ctx := GrA1
/-- The `realarith.ml` alien lemmas (477-479). -/
unsafe def linearProverAliens : HolMath.RealArith.LinearProverAliens := LpA
/-- The `realarith.ml` bootstrapping-instance context (495-509): six
    polynomial conversions plus `deabs_conv`. -/
unsafe def realArith1Ctx : HolMath.RealArith.RealArith1Ctx := RA1c
/-- The `realarith.ml` second-framework context (518-641): the two hardwired
    abs/max/min elimination conversions and the three `pth`s.  Forcing this
    runs the ~8.8s ABSMAXMIN proof. -/
unsafe def genRealArith2Ctx : HolMath.RealArith.GenRealArith2Ctx := GrA2
/-- The `realarith.ml` second-instance context (652-657): six polynomial
    conversions, NO `deabs_conv`. -/
unsafe def realArith2Ctx : HolMath.RealArith.RealArith2Ctx := RA2c

/-- The `GEN_NNF_CONV` auxiliary theorem bundle (`NNFPths`) that
    `GEN_REAL_ARITH1`/`GEN_REAL_ARITH2` need.  `Cn` (the full canon.ml bundle)
    is a private CAF, so this public accessor lets test modules outside
    `Session` supply the same `Cn.nnf` these procedures use internally. -/
unsafe def nnfPths : HolCore.Canon.NNFPths := Cn.nnf

/-- `positivstellensatz` (realarith.ml 166-177): the refutation-certificate
    datatype.  A pure datatype in `HolMath.RealArith` needing no session state;
    re-exported here as an abbreviation so callers can name it unqualified
    through `Session`. -/
abbrev positivstellensatz := HolMath.RealArith.positivstellensatz

/-- `GEN_REAL_ARITH1` (realarith.ml 185-379): the BOOTSTRAPPING parametrized
    framework, exposed with its ELEVEN caller-supplied parameters (plus `tm`)
    still open - `mk_numeric`, the three numeric comparison convs, the four
    polynomial convs, `absconv1`, `absconv2`, and `prover`.  The ambient
    `BoolThms`/`NNFPths`/`GenRealArith1Ctx` and the six `init_conv` conversions
    are pre-supplied.  This is the eleven-slot version (both abs-elimination
    slots caller-supplied); contrast `GEN_REAL_ARITH2`, which hardwires them
    and so takes only nine. -/
unsafe def GEN_REAL_ARITH1
    (mk_numeric : Rat → Except String term)
    (NUMERIC_EQ_CONV NUMERIC_GE_CONV NUMERIC_GT_CONV : ioconv)
    (POLY_CONV POLY_NEG_CONV POLY_ADD_CONV POLY_MUL_CONV : ioconv)
    (absconv1 absconv2 : ioconv)
    (prover : ((List thm × List thm × List thm) →
               HolMath.RealArith.positivstellensatz → IO (Except String thm)) →
              (List thm × List thm × List thm) → IO (Except String thm))
    (tm : term) : IO (Except String thm) := ExceptT.run do
  let rule ← HolMath.RealArith.GEN_REAL_ARITH1 Cn.nnf GrA1
    PRESIMP_CONV NNF_CONV CONDS_ELIM_CONV SKOLEM_CONV PRENEX_CONV WEAK_DNF_CONV
    mk_numeric NUMERIC_EQ_CONV NUMERIC_GE_CONV NUMERIC_GT_CONV
    POLY_CONV POLY_NEG_CONV POLY_ADD_CONV POLY_MUL_CONV
    absconv1 absconv2 prover
  ExceptT.mk (rule tm)

/-- `GEN_REAL_ARITH2` (realarith.ml 517-646): the "slightly less parametrized"
    framework with abs/max/min elimination HARDWIRED, exposed with its NINE
    caller-supplied parameters (plus `tm`) still open - `mkconst`, `EQ`/`GE`/
    `GT`, `NORM`/`NEG`/`ADD`/`MUL`, and `PROVER`.  The two abs-elimination
    conversion slots are GONE (that is the nine-vs-eleven distinction from
    `GEN_REAL_ARITH1`); they come from `genRealArith2Ctx`, whose ~8.8s
    ABSMAXMIN proof this accessor therefore forces. -/
unsafe def GEN_REAL_ARITH2
    (mkconst : Rat → Except String term)
    (EQ GE GT : ioconv)
    (NORM NEG ADD MUL : ioconv)
    (PROVER : ((List thm × List thm × List thm) →
               HolMath.RealArith.positivstellensatz → IO (Except String thm)) →
              (List thm × List thm × List thm) → IO (Except String thm))
    (tm : term) : IO (Except String thm) := ExceptT.run do
  let rule ← HolMath.RealArith.GEN_REAL_ARITH2 Cn.nnf GrA1 GrA2
    PRESIMP_CONV NNF_CONV CONDS_ELIM_CONV SKOLEM_CONV PRENEX_CONV WEAK_DNF_CONV
    mkconst EQ GE GT NORM NEG ADD MUL PROVER
  ExceptT.mk (rule tm)

/-- `REAL_ARITH1` (realarith.ml 494): the BOOTSTRAPPING decision procedure.
    It exists to prove version 2's 42-clause ABSMAXMIN proforma
    (`genRealArith2Ctx`); it is NOT the procedure general code should call.
    Trivial abs-elimination (both `absconv` slots `NO_CONV`, with a separate
    `deabs_conv` rewrite first) and integer constants only. -/
unsafe def REAL_ARITH1 : term → IO (Except String thm) := fun tm => realArith1Closure tm

/-- `REAL_ARITH2` (realarith.ml 651): the instance the rest of HOL Light sees
    at this point - abs/max/min eliminated intelligently by the hardwired
    conversions, no crude `deabs_conv`/`EQ_MP` wrapper.

    IMPORTANT: this is NOT the final `REAL_ARITH` the full HOL Light system
    exposes.  `calc_rat.ml` (hol_lib.ml line 97) OVERWRITES `REAL_ARITH` A
    THIRD TIME; until that layer is translated, `REAL_ARITH2` is the latest
    version. -/
initialize theRealArith2 : IO.Ref (Option ioconv) ← IO.mkRef none

unsafe def REAL_ARITH2 : term → IO (Except String thm) := fun tm => do
  match ← theRealArith2.get with
  | some c => c tm
  | none =>
    match ← (HolMath.RealArith.REAL_ARITH2 Cn.nnf GrA1 GrA2 RA2c
               PRESIMP_CONV NNF_CONV CONDS_ELIM_CONV SKOLEM_CONV PRENEX_CONV WEAK_DNF_CONV
               mk_realintconst REAL_INT_EQ_CONV REAL_INT_GE_CONV REAL_INT_GT_CONV
               REAL_LINEAR_PROVER).run with
    | .error e => return .error e
    | .ok c => do theRealArith2.set (some c); c tm

/- The realax.ml theorems as bare names, as HOL Light has them.          -/
/- In HOL Light every theorem is a global name; the bundle records are   -/
/- an artefact of this translation, so re-export each field bare too.    -/
unsafe def real_tybij1           : thm := Rl.real_tybij1
unsafe def real_tybij2           : thm := Rl.real_tybij2
unsafe def real_of_num           : thm := Rl.real_of_num
unsafe def real_of_num_th        : thm := Rl.real_of_num_th
unsafe def real_neg              : thm := Rl.real_neg
unsafe def real_neg_th           : thm := Rl.real_neg_th
unsafe def real_add              : thm := Rl.real_add
unsafe def real_add_th           : thm := Rl.real_add_th
unsafe def real_mul              : thm := Rl.real_mul
unsafe def real_mul_th           : thm := Rl.real_mul_th
unsafe def real_le               : thm := Rl.real_le
unsafe def real_le_th            : thm := Rl.real_le_th
unsafe def real_inv              : thm := Rl.real_inv
unsafe def real_inv_th           : thm := Rl.real_inv_th
unsafe def REAL_ADD_SYM          : thm := Rl.REAL_ADD_SYM
unsafe def REAL_ADD_ASSOC        : thm := Rl.REAL_ADD_ASSOC
unsafe def REAL_ADD_LID          : thm := Rl.REAL_ADD_LID
unsafe def REAL_MUL_SYM          : thm := Rl.REAL_MUL_SYM
unsafe def REAL_MUL_ASSOC        : thm := Rl.REAL_MUL_ASSOC
unsafe def REAL_MUL_LID          : thm := Rl.REAL_MUL_LID
unsafe def REAL_LE_REFL          : thm := Rl.REAL_LE_REFL
unsafe def REAL_LE_ANTISYM       : thm := Rl.REAL_LE_ANTISYM
unsafe def REAL_LE_TRANS         : thm := Rl.REAL_LE_TRANS
unsafe def REAL_LE_LADD_IMP      : thm := Rl.REAL_LE_LADD_IMP
unsafe def REAL_LE_MUL           : thm := Rl.REAL_LE_MUL
unsafe def REAL_INV_0            : thm := Rl.REAL_INV_0
unsafe def REAL_OF_NUM_EQ        : thm := Rl.REAL_OF_NUM_EQ
unsafe def REAL_OF_NUM_LE        : thm := Rl.REAL_OF_NUM_LE
unsafe def REAL_OF_NUM_ADD       : thm := Rl.REAL_OF_NUM_ADD
unsafe def REAL_OF_NUM_MUL       : thm := Rl.REAL_OF_NUM_MUL
unsafe def real_lt               : thm := Rl.real_lt
unsafe def real_ge               : thm := Rl.real_ge
unsafe def real_gt               : thm := Rl.real_gt
unsafe def real_div              : thm := Rl.real_div
unsafe def real_max              : thm := Rl.real_max
unsafe def real_min              : thm := Rl.real_min
unsafe def REAL_HREAL_LEMMA1     : thm := Rl.REAL_HREAL_LEMMA1
unsafe def REAL_HREAL_LEMMA2     : thm := Rl.REAL_HREAL_LEMMA2
unsafe def REAL_COMPLETE_SOMEPOS : thm := Rl.REAL_COMPLETE_SOMEPOS

/- The calc_int.ml theorems as bare names, as HOL Light has them.        -/
/- In HOL Light every theorem is a global name; the bundle records are   -/
/- an artefact of this translation, so re-export each field bare too.    -/
unsafe def REAL_ADD_AC         : thm := CiT.REAL_ADD_AC
unsafe def REAL_ADD_RINV       : thm := CiT.REAL_ADD_RINV
unsafe def REAL_EQ_ADD_LCANCEL : thm := CiT.REAL_EQ_ADD_LCANCEL
unsafe def REAL_EQ_ADD_RCANCEL : thm := CiT.REAL_EQ_ADD_RCANCEL
unsafe def REAL_MUL_RZERO      : thm := CiT.REAL_MUL_RZERO
unsafe def REAL_MUL_LZERO      : thm := CiT.REAL_MUL_LZERO
unsafe def REAL_NEG_NEG        : thm := CiT.REAL_NEG_NEG
unsafe def REAL_MUL_RNEG       : thm := CiT.REAL_MUL_RNEG
unsafe def REAL_MUL_LNEG       : thm := CiT.REAL_MUL_LNEG
unsafe def REAL_NEG_ADD        : thm := CiT.REAL_NEG_ADD
unsafe def REAL_ADD_RID        : thm := CiT.REAL_ADD_RID
unsafe def REAL_NEG_0          : thm := CiT.REAL_NEG_0
unsafe def REAL_LE_LNEG        : thm := CiT.REAL_LE_LNEG
unsafe def REAL_LE_NEG2        : thm := CiT.REAL_LE_NEG2
unsafe def REAL_LE_RNEG        : thm := CiT.REAL_LE_RNEG
unsafe def REAL_OF_NUM_POW     : thm := CiT.REAL_OF_NUM_POW
unsafe def REAL_POW_NEG        : thm := CiT.REAL_POW_NEG
unsafe def REAL_ABS_NUM        : thm := CiT.REAL_ABS_NUM
unsafe def REAL_ABS_NEG        : thm := CiT.REAL_ABS_NEG

/- The realarith.ml driving lemmas as bare names, as HOL Light has them. -/
/- In HOL Light every theorem is a global name; the bundle records are   -/
/- an artefact of this translation, so re-export each field bare too.    -/
unsafe def REAL_LTE_TOTAL        : thm := RaL.REAL_LTE_TOTAL
unsafe def REAL_LET_TOTAL        : thm := RaL.REAL_LET_TOTAL
unsafe def REAL_LT_IMP_LE        : thm := RaL.REAL_LT_IMP_LE
unsafe def REAL_LTE_TRANS        : thm := RaL.REAL_LTE_TRANS
unsafe def REAL_LET_TRANS        : thm := RaL.REAL_LET_TRANS
unsafe def REAL_LT_TRANS         : thm := RaL.REAL_LT_TRANS
unsafe def REAL_LE_ADD           : thm := RaL.REAL_LE_ADD
unsafe def REAL_LTE_ANTISYM      : thm := RaL.REAL_LTE_ANTISYM
unsafe def REAL_SUB_LE           : thm := RaL.REAL_SUB_LE
unsafe def REAL_NEG_SUB          : thm := RaL.REAL_NEG_SUB
unsafe def REAL_LE_LT            : thm := RaL.REAL_LE_LT
unsafe def REAL_SUB_LT           : thm := RaL.REAL_SUB_LT
unsafe def REAL_NOT_LT           : thm := RaL.REAL_NOT_LT
unsafe def REAL_SUB_0            : thm := RaL.REAL_SUB_0
unsafe def REAL_LT_LE            : thm := RaL.REAL_LT_LE
unsafe def REAL_LT_REFL          : thm := RaL.REAL_LT_REFL
unsafe def REAL_LTE_ADD          : thm := RaL.REAL_LTE_ADD
unsafe def REAL_LET_ADD          : thm := RaL.REAL_LET_ADD
unsafe def REAL_LT_ADD           : thm := RaL.REAL_LT_ADD
unsafe def REAL_ENTIRE           : thm := RaL.REAL_ENTIRE
unsafe def REAL_LE_NEGTOTAL      : thm := RaL.REAL_LE_NEGTOTAL
unsafe def REAL_LE_SQUARE        : thm := RaL.REAL_LE_SQUARE
unsafe def REAL_MUL_RID          : thm := RaL.REAL_MUL_RID
unsafe def REAL_POW_2            : thm := RaL.REAL_POW_2
unsafe def REAL_POLY_CLAUSES     : thm := RaL.REAL_POLY_CLAUSES
unsafe def REAL_POLY_NEG_CLAUSES : thm := RaL.REAL_POLY_NEG_CLAUSES
unsafe def REAL_POS              : thm := RaL.REAL_POS
unsafe def REAL_LT_NZ            : thm := RaL.REAL_LT_NZ
unsafe def REAL_POS_LT           : thm := RaL.REAL_POS_LT


/- ---------------------------------------------------------------------- -/
/- real.ml (hol_lib.ml 96): derived properties of the reals.              -/
/-                                                                        -/
/- Twelve setups wired in dependency order.  `REAL_ARITH` throughout      -/
/- means `REAL_ARITH2` (realarith.ml's second REAL_ARITH), which is what  -/
/- real.ml's `REAL_ARITH` denotes at this point in the load order.  Each  -/
/- setup is memoised behind an `IO.Ref` cache and read by a private CAF   -/
/- that runs the setup once and `panic!`s with a clear message on error;  -/
/- PUBLIC accessors below expose each bundle with its real.ml line range. -/
/- ---------------------------------------------------------------------- -/

/-- Cache for `RealThms1` (real.ml 14-102). -/
initialize theRealThms1 : IO.Ref (Option HolMath.Real.RealThms1) ← IO.mkRef none

private unsafe def RT1 : HolMath.Real.RealThms1 :=
  match unsafeIO (do
    match ← theRealThms1.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Real.setupRealThms1 Ar1 Ar2 Ar3 Ar4 Ar5 CiT Rl RaL
                 MESON_TAC ASM_MESON_TAC).run with
      | .ok d => do theRealThms1.set (some d); pure d
      | .error e => panic! s!"setupRealThms1 failed: {e}") with
  | .ok d => d | _ => panic! "Session.RT1: setupRealThms1 not run"

/-- Cache for `RealThms2` (real.ml 109-255). -/
initialize theRealThms2 : IO.Ref (Option HolMath.Real.RealThms2) ← IO.mkRef none

private unsafe def RT2 : HolMath.Real.RealThms2 :=
  match unsafeIO (do
    match ← theRealThms2.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Real.setupRealThms2 REAL_ARITH2 Rl CiT).run with
      | .ok d => do theRealThms2.set (some d); pure d
      | .error e => panic! s!"setupRealThms2 failed: {e}") with
  | .ok d => d | _ => panic! "Session.RT2: setupRealThms2 not run"

/-- Cache for `RealThms3` (real.ml 256-400). -/
initialize theRealThms3 : IO.Ref (Option HolMath.Real.RealThms3) ← IO.mkRef none

private unsafe def RT3 : HolMath.Real.RealThms3 :=
  match unsafeIO (do
    match ← theRealThms3.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Real.setupRealThms3 REAL_ARITH2).run with
      | .ok d => do theRealThms3.set (some d); pure d
      | .error e => panic! s!"setupRealThms3 failed: {e}") with
  | .ok d => d | _ => panic! "Session.RT3: setupRealThms3 not run"

/-- Cache for `RealThms4` (real.ml 401-510). -/
initialize theRealThms4 : IO.Ref (Option HolMath.Real.RealThms4) ← IO.mkRef none

private unsafe def RT4 : HolMath.Real.RealThms4 :=
  match unsafeIO (do
    match ← theRealThms4.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Real.setupRealThms4 REAL_ARITH2).run with
      | .ok d => do theRealThms4.set (some d); pure d
      | .error e => panic! s!"setupRealThms4 failed: {e}") with
  | .ok d => d | _ => panic! "Session.RT4: setupRealThms4 not run"

/-- Cache for `RealThms5` (real.ml 511-594). -/
initialize theRealThms5 : IO.Ref (Option HolMath.Real.RealThms5) ← IO.mkRef none

private unsafe def RT5 : HolMath.Real.RealThms5 :=
  match unsafeIO (do
    match ← theRealThms5.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Real.setupRealThms5 REAL_ARITH2).run with
      | .ok d => do theRealThms5.set (some d); pure d
      | .error e => panic! s!"setupRealThms5 failed: {e}") with
  | .ok d => d | _ => panic! "Session.RT5: setupRealThms5 not run"

/-- Cache for `RealBackchain` (real.ml 595-606): the two backchaining `pth`s. -/
initialize theRealBackchain : IO.Ref (Option HolMath.Real.RealBackchain) ← IO.mkRef none

private unsafe def RBc : HolMath.Real.RealBackchain :=
  match unsafeIO (do
    match ← theRealBackchain.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Real.setupRealBackchain IMP_CONJ Rl.REAL_LE_TRANS RaL.REAL_LET_TRANS).run with
      | .ok d => do theRealBackchain.set (some d); pure d
      | .error e => panic! s!"setupRealBackchain failed: {e}") with
  | .ok d => d | _ => panic! "Session.RBc: setupRealBackchain not run"

/-- Cache for `RealThms6` (real.ml 607-855). -/
initialize theRealThms6 : IO.Ref (Option HolMath.Real.RealThms6) ← IO.mkRef none

private unsafe def RT6 : HolMath.Real.RealThms6 :=
  match unsafeIO (do
    match ← theRealThms6.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Real.setupRealThms6 Nm Ar1 Ar4 Ar5 CnA Rl CiT RaL
                 RT1 RT2 RT3 RT4 REAL_ARITH2 MESON_TAC ASM_MESON_TAC).run with
      | .ok d => do theRealThms6.set (some d); pure d
      | .error e => panic! s!"setupRealThms6 failed: {e}") with
  | .ok d => d | _ => panic! "Session.RT6: setupRealThms6 not run"

/-- Cache for `RealThms7` (real.ml 856-1114). -/
initialize theRealThms7 : IO.Ref (Option HolMath.Real.RealThms7) ← IO.mkRef none

private unsafe def RT7 : HolMath.Real.RealThms7 :=
  match unsafeIO (do
    match ← theRealThms7.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Real.setupRealThms7 Nm Rl CiT RaL
                 RT1 RT2 RT3 RT6 num_CONV REAL_ARITH2 MESON_TAC).run with
      | .ok d => do theRealThms7.set (some d); pure d
      | .error e => panic! s!"setupRealThms7 failed: {e}") with
  | .ok d => d | _ => panic! "Session.RT7: setupRealThms7 not run"

/-- Cache for `RealThms8` (real.ml 1115-1389). -/
initialize theRealThms8 : IO.Ref (Option HolMath.Real.RealThms8) ← IO.mkRef none

private unsafe def RT8 : HolMath.Real.RealThms8 :=
  match unsafeIO (do
    match ← theRealThms8.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Real.setupRealThms8 Nm Ar1 Ar2 Ar3 Ar4 Ar5 Ar7 CnA Rl CiT RaL
                 RT1 RT2 RT3 RT4 RT6 RT7 NUM_EQ_CONV REAL_ARITH2 MESON_TAC ASM_MESON_TAC).run with
      | .ok d => do theRealThms8.set (some d); pure d
      | .error e => panic! s!"setupRealThms8 failed: {e}") with
  | .ok d => d | _ => panic! "Session.RT8: setupRealThms8 not run"

/-- Cache for `RealThms9` (real.ml 1390-1517). -/
initialize theRealThms9 : IO.Ref (Option HolMath.Real.RealThms9) ← IO.mkRef none

private unsafe def RT9 : HolMath.Real.RealThms9 :=
  match unsafeIO (do
    match ← theRealThms9.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Real.setupRealThms9 Nm CnA Rl CiT RaL
                 RT1 RT2 RT3 RT6 RT7 REAL_ARITH2 MESON_TAC ASM_MESON_TAC).run with
      | .ok d => do theRealThms9.set (some d); pure d
      | .error e => panic! s!"setupRealThms9 failed: {e}") with
  | .ok d => d | _ => panic! "Session.RT9: setupRealThms9 not run"

/-- Cache for `RealThms10` (real.ml 1518-1656).  `real_sgn` is a new
    definition here, so this setup is NOT idempotent - the cache guarantees it
    runs at most once. -/
initialize theRealThms10 : IO.Ref (Option HolMath.Real.RealThms10) ← IO.mkRef none

private unsafe def RT10 : HolMath.Real.RealThms10 :=
  match unsafeIO (do
    match ← theRealThms10.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Real.setupRealThms10 Nm CnA Rl CiT RaL
                 RT2 RT4 RT6 RT7 RT8 new_definition REAL_ARITH2 MESON_TAC).run with
      | .ok d => do theRealThms10.set (some d); pure d
      | .error e => panic! s!"setupRealThms10 failed: {e}") with
  | .ok d => d | _ => panic! "Session.RT10: setupRealThms10 not run"

/-- Cache for `RealThms11` (real.ml 1657-1993).  `sqrt` is a new definition
    here, so this setup is NOT idempotent - the cache guarantees it runs at
    most once. -/
initialize theRealThms11 : IO.Ref (Option HolMath.Real.RealThms11) ← IO.mkRef none

private unsafe def RT11 : HolMath.Real.RealThms11 :=
  match unsafeIO (do
    match ← theRealThms11.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Real.setupRealThms11 Ar2 Ar5 Ar7 CnA Rl CiT RaL
                 RT2 RT3 RT4 RT5 RT6 RT7 RT8 RT10
                 SELECT_CONV NUM_REDUCE_CONV new_definition REAL_ARITH2
                 MESON_TAC ASM_MESON_TAC).run with
      | .ok d => do theRealThms11.set (some d); pure d
      | .error e => panic! s!"setupRealThms11 failed: {e}") with
  | .ok d => d | _ => panic! "Session.RT11: setupRealThms11 not run"

/- Public accessors for the real.ml bundles. -/

/-- The `real.ml` first block (14-102): `REAL_OF_NUM_*` bridges, `REAL_MUL_AC`,
    distributivity and the two strict-order lemmas. -/
unsafe def realThms1 : HolMath.Real.RealThms1 := RT1
/-- The `real.ml` second block (109-255): the thirty-six linear theorems proved
    automatically (thirty-four by `REAL_ARITH_TAC`). -/
unsafe def realThms2 : HolMath.Real.RealThms2 := RT2
/-- The `real.ml` third block (256-400): further linear/subtraction theorems. -/
unsafe def realThms3 : HolMath.Real.RealThms3 := RT3
/-- The `real.ml` fourth block (401-510): the absolute-value theorems. -/
unsafe def realThms4 : HolMath.Real.RealThms4 := RT4
/-- The `real.ml` fifth block (511-594): the min/max theorems. -/
unsafe def realThms5 : HolMath.Real.RealThms5 := RT5
/-- The `real.ml` backchaining rules' context (595-606): the two `pth`s that
    `REAL_LE_IMP`/`REAL_LET_IMP` rewrite with. -/
unsafe def realBackchain : HolMath.Real.RealBackchain := RBc
/-- The `real.ml` sixth block (607-855): multiplication/inverse/division/power
    theorems. -/
unsafe def realThms6 : HolMath.Real.RealThms6 := RT6
/-- The `real.ml` seventh block (856-1114): cancellation and division/inverse
    ordering theorems. -/
unsafe def realThms7 : HolMath.Real.RealThms7 := RT7
/-- The `real.ml` eighth block (1115-1389): power monotonicity and squares. -/
unsafe def realThms8 : HolMath.Real.RealThms8 := RT8
/-- The `real.ml` ninth block (1390-1517): convex bounds and the Archimedean
    theorems. -/
unsafe def realThms9 : HolMath.Real.RealThms9 := RT9
/-- The `real.ml` tenth block (1518-1656): the `real_sgn` definition and its
    theorems, plus the WLOG rules. -/
unsafe def realThms10 : HolMath.Real.RealThms10 := RT10
/-- The `real.ml` eleventh block (1657-1993): the `sqrt` definition and its
    theory.  Forcing this pulls in every other real.ml bundle. -/
unsafe def realThms11 : HolMath.Real.RealThms11 := RT11

/-- `REAL_ARITH_TAC` (real.ml 106): `CONV_TAC REAL_ARITH`, with `REAL_ARITH2`
    pre-supplied so callers get a plain `tactic`.  NOTE: `ASM_REAL_ARITH_TAC`
    is NOT defined in real.ml - it arrives with calc_rat.ml - so it is not
    exposed here. -/
unsafe def REAL_ARITH_TAC : tactic := HolMath.Real.REAL_ARITH_TAC REAL_ARITH2

/-- `REAL_LE_IMP` (real.ml 597-599): a RULE (`thm -> IO (Except String thm)`),
    NOT a theorem.  Given `th`, returns `GEN_ALL (MATCH_MP le_pth (SPEC_ALL
    th))`, with the once-computed `RealBackchain` pre-supplied. -/
unsafe def REAL_LE_IMP (th : thm) : IO (Except String thm) :=
  HolMath.Real.REAL_LE_IMP RBc th
/-- `REAL_LET_IMP` (real.ml 601-603): a RULE (`thm -> IO (Except String thm)`),
    NOT a theorem.  Given `th`, returns `GEN_ALL (MATCH_MP let_pth (SPEC_ALL
    th))`, with the once-computed `RealBackchain` pre-supplied. -/
unsafe def REAL_LET_IMP (th : thm) : IO (Except String thm) :=
  HolMath.Real.REAL_LET_IMP RBc th

/- The real.ml theorems as bare names, as HOL Light has them.            -/
/- In HOL Light every theorem is a global name; the bundle records are   -/
/- an artefact of this translation, so re-export each field bare too.    -/
/- Includes the two definition theorems `real_sgn` (T10) and `sqrt`      -/
/- (T11).  All 331 names are new; none collides with an earlier bundle.  -/
unsafe def REAL_OF_NUM_LT        : thm := realThms1.REAL_OF_NUM_LT
unsafe def REAL_OF_NUM_GE        : thm := realThms1.REAL_OF_NUM_GE
unsafe def REAL_OF_NUM_GT        : thm := realThms1.REAL_OF_NUM_GT
unsafe def REAL_OF_NUM_MAX       : thm := realThms1.REAL_OF_NUM_MAX
unsafe def REAL_OF_NUM_MIN       : thm := realThms1.REAL_OF_NUM_MIN
unsafe def REAL_OF_NUM_SUC       : thm := realThms1.REAL_OF_NUM_SUC
unsafe def REAL_OF_NUM_SUB       : thm := realThms1.REAL_OF_NUM_SUB
unsafe def REAL_OF_NUM_SUB_CASES : thm := realThms1.REAL_OF_NUM_SUB_CASES
unsafe def REAL_OF_NUM_CLAUSES   : thm := realThms1.REAL_OF_NUM_CLAUSES
unsafe def REAL_MUL_AC           : thm := realThms1.REAL_MUL_AC
unsafe def REAL_ADD_RDISTRIB     : thm := realThms1.REAL_ADD_RDISTRIB
unsafe def REAL_LT_LADD_IMP      : thm := realThms1.REAL_LT_LADD_IMP
unsafe def REAL_LT_MUL           : thm := realThms1.REAL_LT_MUL
unsafe def REAL_EQ_ADD_LCANCEL_0 : thm := realThms2.REAL_EQ_ADD_LCANCEL_0
unsafe def REAL_EQ_ADD_RCANCEL_0 : thm := realThms2.REAL_EQ_ADD_RCANCEL_0
unsafe def REAL_LNEG_UNIQ        : thm := realThms2.REAL_LNEG_UNIQ
unsafe def REAL_RNEG_UNIQ        : thm := realThms2.REAL_RNEG_UNIQ
unsafe def REAL_NEG_LMUL         : thm := realThms2.REAL_NEG_LMUL
unsafe def REAL_NEG_RMUL         : thm := realThms2.REAL_NEG_RMUL
unsafe def REAL_NEG_MUL2         : thm := realThms2.REAL_NEG_MUL2
unsafe def REAL_LT_LADD          : thm := realThms2.REAL_LT_LADD
unsafe def REAL_LT_RADD          : thm := realThms2.REAL_LT_RADD
unsafe def REAL_LT_ANTISYM       : thm := realThms2.REAL_LT_ANTISYM
unsafe def REAL_LT_GT            : thm := realThms2.REAL_LT_GT
unsafe def REAL_NOT_EQ           : thm := realThms2.REAL_NOT_EQ
unsafe def REAL_NOT_LE           : thm := realThms2.REAL_NOT_LE
unsafe def REAL_LET_ANTISYM      : thm := realThms2.REAL_LET_ANTISYM
unsafe def REAL_NEG_LT0          : thm := realThms2.REAL_NEG_LT0
unsafe def REAL_NEG_GT0          : thm := realThms2.REAL_NEG_GT0
unsafe def REAL_NEG_LE0          : thm := realThms2.REAL_NEG_LE0
unsafe def REAL_NEG_GE0          : thm := realThms2.REAL_NEG_GE0
unsafe def REAL_LT_TOTAL         : thm := realThms2.REAL_LT_TOTAL
unsafe def REAL_LT_NEGTOTAL      : thm := realThms2.REAL_LT_NEGTOTAL
unsafe def REAL_LE_01            : thm := realThms2.REAL_LE_01
unsafe def REAL_LT_01            : thm := realThms2.REAL_LT_01
unsafe def REAL_LE_LADD          : thm := realThms2.REAL_LE_LADD
unsafe def REAL_LE_RADD          : thm := realThms2.REAL_LE_RADD
unsafe def REAL_LT_ADD2          : thm := realThms2.REAL_LT_ADD2
unsafe def REAL_LE_ADD2          : thm := realThms2.REAL_LE_ADD2
unsafe def REAL_LT_LNEG          : thm := realThms2.REAL_LT_LNEG
unsafe def REAL_LT_RNEG          : thm := realThms2.REAL_LT_RNEG
unsafe def REAL_LT_ADDNEG        : thm := realThms2.REAL_LT_ADDNEG
unsafe def REAL_LT_ADDNEG2       : thm := realThms2.REAL_LT_ADDNEG2
unsafe def REAL_LT_ADD1          : thm := realThms2.REAL_LT_ADD1
unsafe def REAL_SUB_ADD          : thm := realThms2.REAL_SUB_ADD
unsafe def REAL_SUB_ADD2         : thm := realThms2.REAL_SUB_ADD2
unsafe def REAL_SUB_REFL         : thm := realThms2.REAL_SUB_REFL
unsafe def REAL_LE_DOUBLE        : thm := realThms2.REAL_LE_DOUBLE
unsafe def REAL_LE_NEGL          : thm := realThms2.REAL_LE_NEGL
unsafe def REAL_LE_NEGR          : thm := realThms3.REAL_LE_NEGR
unsafe def REAL_NEG_EQ_0         : thm := realThms3.REAL_NEG_EQ_0
unsafe def REAL_ADD_SUB          : thm := realThms3.REAL_ADD_SUB
unsafe def REAL_NEG_EQ           : thm := realThms3.REAL_NEG_EQ
unsafe def REAL_NEG_MINUS1       : thm := realThms3.REAL_NEG_MINUS1
unsafe def REAL_LT_IMP_NE        : thm := realThms3.REAL_LT_IMP_NE
unsafe def REAL_LE_ADDR          : thm := realThms3.REAL_LE_ADDR
unsafe def REAL_LE_ADDL          : thm := realThms3.REAL_LE_ADDL
unsafe def REAL_LT_ADDR          : thm := realThms3.REAL_LT_ADDR
unsafe def REAL_LT_ADDL          : thm := realThms3.REAL_LT_ADDL
unsafe def REAL_SUB_SUB          : thm := realThms3.REAL_SUB_SUB
unsafe def REAL_LT_ADD_SUB       : thm := realThms3.REAL_LT_ADD_SUB
unsafe def REAL_LT_SUB_RADD      : thm := realThms3.REAL_LT_SUB_RADD
unsafe def REAL_LT_SUB_LADD      : thm := realThms3.REAL_LT_SUB_LADD
unsafe def REAL_LE_SUB_LADD      : thm := realThms3.REAL_LE_SUB_LADD
unsafe def REAL_LE_SUB_RADD      : thm := realThms3.REAL_LE_SUB_RADD
unsafe def REAL_ADD2_SUB2        : thm := realThms3.REAL_ADD2_SUB2
unsafe def REAL_SUB_LZERO        : thm := realThms3.REAL_SUB_LZERO
unsafe def REAL_SUB_RZERO        : thm := realThms3.REAL_SUB_RZERO
unsafe def REAL_LET_ADD2         : thm := realThms3.REAL_LET_ADD2
unsafe def REAL_LTE_ADD2         : thm := realThms3.REAL_LTE_ADD2
unsafe def REAL_SUB_LNEG         : thm := realThms3.REAL_SUB_LNEG
unsafe def REAL_SUB_RNEG         : thm := realThms3.REAL_SUB_RNEG
unsafe def REAL_SUB_NEG2         : thm := realThms3.REAL_SUB_NEG2
unsafe def REAL_SUB_TRIANGLE     : thm := realThms3.REAL_SUB_TRIANGLE
unsafe def REAL_EQ_SUB_LADD      : thm := realThms3.REAL_EQ_SUB_LADD
unsafe def REAL_EQ_SUB_RADD      : thm := realThms3.REAL_EQ_SUB_RADD
unsafe def REAL_SUB_SUB2         : thm := realThms3.REAL_SUB_SUB2
unsafe def REAL_ADD_SUB2         : thm := realThms3.REAL_ADD_SUB2
unsafe def REAL_EQ_IMP_LE        : thm := realThms3.REAL_EQ_IMP_LE
unsafe def REAL_LT_IMP_NZ        : thm := realThms3.REAL_LT_IMP_NZ
unsafe def REAL_DIFFSQ           : thm := realThms3.REAL_DIFFSQ
unsafe def REAL_EQ_NEG2          : thm := realThms3.REAL_EQ_NEG2
unsafe def REAL_LT_NEG2          : thm := realThms3.REAL_LT_NEG2
unsafe def REAL_SUB_LDISTRIB     : thm := realThms3.REAL_SUB_LDISTRIB
unsafe def REAL_SUB_RDISTRIB     : thm := realThms3.REAL_SUB_RDISTRIB
unsafe def REAL_ABS_ZERO         : thm := realThms4.REAL_ABS_ZERO
unsafe def REAL_ABS_0            : thm := realThms4.REAL_ABS_0
unsafe def REAL_ABS_1            : thm := realThms4.REAL_ABS_1
unsafe def REAL_ABS_TRIANGLE     : thm := realThms4.REAL_ABS_TRIANGLE
unsafe def REAL_ABS_TRIANGLE_LE  : thm := realThms4.REAL_ABS_TRIANGLE_LE
unsafe def REAL_ABS_TRIANGLE_LT  : thm := realThms4.REAL_ABS_TRIANGLE_LT
unsafe def REAL_ABS_POS          : thm := realThms4.REAL_ABS_POS
unsafe def REAL_ABS_SUB          : thm := realThms4.REAL_ABS_SUB
unsafe def REAL_ABS_NZ           : thm := realThms4.REAL_ABS_NZ
unsafe def REAL_ABS_ABS          : thm := realThms4.REAL_ABS_ABS
unsafe def REAL_ABS_LE           : thm := realThms4.REAL_ABS_LE
unsafe def REAL_ABS_REFL         : thm := realThms4.REAL_ABS_REFL
unsafe def REAL_ABS_BETWEEN      : thm := realThms4.REAL_ABS_BETWEEN
unsafe def REAL_ABS_BOUND        : thm := realThms4.REAL_ABS_BOUND
unsafe def REAL_ABS_STILLNZ      : thm := realThms4.REAL_ABS_STILLNZ
unsafe def REAL_ABS_CASES        : thm := realThms4.REAL_ABS_CASES
unsafe def REAL_ABS_BETWEEN1     : thm := realThms4.REAL_ABS_BETWEEN1
unsafe def REAL_ABS_SIGN         : thm := realThms4.REAL_ABS_SIGN
unsafe def REAL_ABS_SIGN2        : thm := realThms4.REAL_ABS_SIGN2
unsafe def REAL_ABS_CIRCLE       : thm := realThms4.REAL_ABS_CIRCLE
unsafe def REAL_SUB_ABS          : thm := realThms4.REAL_SUB_ABS
unsafe def REAL_ABS_SUB_ABS      : thm := realThms4.REAL_ABS_SUB_ABS
unsafe def REAL_ABS_BETWEEN2     : thm := realThms4.REAL_ABS_BETWEEN2
unsafe def REAL_ABS_BOUNDS       : thm := realThms4.REAL_ABS_BOUNDS
unsafe def REAL_BOUNDS_LE        : thm := realThms4.REAL_BOUNDS_LE
unsafe def REAL_BOUNDS_LT        : thm := realThms4.REAL_BOUNDS_LT
unsafe def REAL_MIN_MAX          : thm := realThms5.REAL_MIN_MAX
unsafe def REAL_MAX_MIN          : thm := realThms5.REAL_MAX_MIN
unsafe def REAL_MAX_MAX          : thm := realThms5.REAL_MAX_MAX
unsafe def REAL_MIN_MIN          : thm := realThms5.REAL_MIN_MIN
unsafe def REAL_MAX_SYM          : thm := realThms5.REAL_MAX_SYM
unsafe def REAL_MIN_SYM          : thm := realThms5.REAL_MIN_SYM
unsafe def REAL_LE_MAX           : thm := realThms5.REAL_LE_MAX
unsafe def REAL_LE_MIN           : thm := realThms5.REAL_LE_MIN
unsafe def REAL_LT_MAX           : thm := realThms5.REAL_LT_MAX
unsafe def REAL_LT_MIN           : thm := realThms5.REAL_LT_MIN
unsafe def REAL_MAX_LE           : thm := realThms5.REAL_MAX_LE
unsafe def REAL_MIN_LE           : thm := realThms5.REAL_MIN_LE
unsafe def REAL_MAX_LT           : thm := realThms5.REAL_MAX_LT
unsafe def REAL_MIN_LT           : thm := realThms5.REAL_MIN_LT
unsafe def REAL_MAX_ASSOC        : thm := realThms5.REAL_MAX_ASSOC
unsafe def REAL_MIN_ASSOC        : thm := realThms5.REAL_MIN_ASSOC
unsafe def REAL_MAX_ACI          : thm := realThms5.REAL_MAX_ACI
unsafe def REAL_MIN_ACI          : thm := realThms5.REAL_MIN_ACI
unsafe def REAL_ABS_MUL          : thm := realThms6.REAL_ABS_MUL
unsafe def REAL_POW_LE           : thm := realThms6.REAL_POW_LE
unsafe def REAL_POW_LT           : thm := realThms6.REAL_POW_LT
unsafe def REAL_ABS_POW          : thm := realThms6.REAL_ABS_POW
unsafe def REAL_LE_LMUL          : thm := realThms6.REAL_LE_LMUL
unsafe def REAL_LE_RMUL          : thm := realThms6.REAL_LE_RMUL
unsafe def REAL_LT_LMUL          : thm := realThms6.REAL_LT_LMUL
unsafe def REAL_LT_RMUL          : thm := realThms6.REAL_LT_RMUL
unsafe def REAL_EQ_MUL_LCANCEL   : thm := realThms6.REAL_EQ_MUL_LCANCEL
unsafe def REAL_EQ_MUL_RCANCEL   : thm := realThms6.REAL_EQ_MUL_RCANCEL
unsafe def REAL_MUL_LINV_UNIQ    : thm := realThms6.REAL_MUL_LINV_UNIQ
unsafe def REAL_MUL_RINV_UNIQ    : thm := realThms6.REAL_MUL_RINV_UNIQ
unsafe def REAL_INV_INV          : thm := realThms6.REAL_INV_INV
unsafe def REAL_EQ_INV2          : thm := realThms6.REAL_EQ_INV2
unsafe def REAL_INV_EQ_0         : thm := realThms6.REAL_INV_EQ_0
unsafe def REAL_LT_INV           : thm := realThms6.REAL_LT_INV
unsafe def REAL_LT_INV_EQ        : thm := realThms6.REAL_LT_INV_EQ
unsafe def REAL_INV_NEG          : thm := realThms6.REAL_INV_NEG
unsafe def REAL_LE_INV_EQ        : thm := realThms6.REAL_LE_INV_EQ
unsafe def REAL_LE_INV           : thm := realThms6.REAL_LE_INV
unsafe def REAL_MUL_RINV         : thm := realThms6.REAL_MUL_RINV
unsafe def REAL_INV_1            : thm := realThms6.REAL_INV_1
unsafe def REAL_INV_EQ_1         : thm := realThms6.REAL_INV_EQ_1
unsafe def REAL_DIV_1            : thm := realThms6.REAL_DIV_1
unsafe def REAL_DIV_REFL         : thm := realThms6.REAL_DIV_REFL
unsafe def REAL_DIV_RMUL         : thm := realThms6.REAL_DIV_RMUL
unsafe def REAL_DIV_LMUL         : thm := realThms6.REAL_DIV_LMUL
unsafe def REAL_DIV_EQ_1         : thm := realThms6.REAL_DIV_EQ_1
unsafe def REAL_ABS_INV          : thm := realThms6.REAL_ABS_INV
unsafe def REAL_ABS_DIV          : thm := realThms6.REAL_ABS_DIV
unsafe def REAL_INV_MUL          : thm := realThms6.REAL_INV_MUL
unsafe def REAL_INV_DIV          : thm := realThms6.REAL_INV_DIV
unsafe def REAL_POW_MUL          : thm := realThms6.REAL_POW_MUL
unsafe def REAL_POW_INV          : thm := realThms6.REAL_POW_INV
unsafe def REAL_INV_POW          : thm := realThms6.REAL_INV_POW
unsafe def REAL_POW_DIV          : thm := realThms6.REAL_POW_DIV
unsafe def REAL_DIV_EQ_0         : thm := realThms6.REAL_DIV_EQ_0
unsafe def REAL_POW_ADD          : thm := realThms6.REAL_POW_ADD
unsafe def REAL_POW_NZ           : thm := realThms6.REAL_POW_NZ
unsafe def REAL_POW_SUB          : thm := realThms6.REAL_POW_SUB
unsafe def REAL_LT_LCANCEL_IMP   : thm := realThms7.REAL_LT_LCANCEL_IMP
unsafe def REAL_LT_RCANCEL_IMP   : thm := realThms7.REAL_LT_RCANCEL_IMP
unsafe def REAL_LE_LCANCEL_IMP   : thm := realThms7.REAL_LE_LCANCEL_IMP
unsafe def REAL_LE_RCANCEL_IMP   : thm := realThms7.REAL_LE_RCANCEL_IMP
unsafe def REAL_LE_RMUL_EQ       : thm := realThms7.REAL_LE_RMUL_EQ
unsafe def REAL_LE_LMUL_EQ       : thm := realThms7.REAL_LE_LMUL_EQ
unsafe def REAL_LT_RMUL_EQ       : thm := realThms7.REAL_LT_RMUL_EQ
unsafe def REAL_LT_LMUL_EQ       : thm := realThms7.REAL_LT_LMUL_EQ
unsafe def REAL_LE_MUL_EQ        : thm := realThms7.REAL_LE_MUL_EQ
unsafe def REAL_LT_MUL_EQ        : thm := realThms7.REAL_LT_MUL_EQ
unsafe def REAL_MUL_POS_LT       : thm := realThms7.REAL_MUL_POS_LT
unsafe def REAL_MUL_POS_LE       : thm := realThms7.REAL_MUL_POS_LE
unsafe def REAL_LE_RDIV_EQ       : thm := realThms7.REAL_LE_RDIV_EQ
unsafe def REAL_LE_LDIV_EQ       : thm := realThms7.REAL_LE_LDIV_EQ
unsafe def REAL_LT_RDIV_EQ       : thm := realThms7.REAL_LT_RDIV_EQ
unsafe def REAL_LT_LDIV_EQ       : thm := realThms7.REAL_LT_LDIV_EQ
unsafe def REAL_EQ_RDIV_EQ       : thm := realThms7.REAL_EQ_RDIV_EQ
unsafe def REAL_EQ_LDIV_EQ       : thm := realThms7.REAL_EQ_LDIV_EQ
unsafe def REAL_LT_DIV2_EQ       : thm := realThms7.REAL_LT_DIV2_EQ
unsafe def REAL_LE_DIV2_EQ       : thm := realThms7.REAL_LE_DIV2_EQ
unsafe def REAL_MUL_2            : thm := realThms7.REAL_MUL_2
unsafe def REAL_POW_EQ_0         : thm := realThms7.REAL_POW_EQ_0
unsafe def REAL_LE_MUL2          : thm := realThms7.REAL_LE_MUL2
unsafe def REAL_LT_MUL2          : thm := realThms7.REAL_LT_MUL2
unsafe def REAL_LT_SQUARE        : thm := realThms7.REAL_LT_SQUARE
unsafe def REAL_POW_1            : thm := realThms7.REAL_POW_1
unsafe def REAL_POW_ONE          : thm := realThms7.REAL_POW_ONE
unsafe def REAL_LT_INV2          : thm := realThms7.REAL_LT_INV2
unsafe def REAL_LE_INV2          : thm := realThms7.REAL_LE_INV2
unsafe def REAL_LT_LINV          : thm := realThms7.REAL_LT_LINV
unsafe def REAL_LT_RINV          : thm := realThms7.REAL_LT_RINV
unsafe def REAL_LE_LINV          : thm := realThms7.REAL_LE_LINV
unsafe def REAL_LE_RINV          : thm := realThms7.REAL_LE_RINV
unsafe def REAL_INV_LE_1         : thm := realThms7.REAL_INV_LE_1
unsafe def REAL_INV_1_LE         : thm := realThms7.REAL_INV_1_LE
unsafe def REAL_INV_LT_1         : thm := realThms7.REAL_INV_LT_1
unsafe def REAL_INV_1_LT         : thm := realThms7.REAL_INV_1_LT
unsafe def REAL_SUB_INV          : thm := realThms7.REAL_SUB_INV
unsafe def REAL_DOWN             : thm := realThms7.REAL_DOWN
unsafe def REAL_DOWN2            : thm := realThms7.REAL_DOWN2
unsafe def REAL_POW_LE2          : thm := realThms7.REAL_POW_LE2
unsafe def REAL_POW_LE_1         : thm := realThms8.REAL_POW_LE_1
unsafe def REAL_POW_1_LE         : thm := realThms8.REAL_POW_1_LE
unsafe def REAL_POW_MONO         : thm := realThms8.REAL_POW_MONO
unsafe def REAL_POW_LT2          : thm := realThms8.REAL_POW_LT2
unsafe def REAL_POW_LT_1         : thm := realThms8.REAL_POW_LT_1
unsafe def REAL_POW_1_LT         : thm := realThms8.REAL_POW_1_LT
unsafe def REAL_POW_MONO_LT      : thm := realThms8.REAL_POW_MONO_LT
unsafe def REAL_POW_POW          : thm := realThms8.REAL_POW_POW
unsafe def REAL_EQ_RCANCEL_IMP   : thm := realThms8.REAL_EQ_RCANCEL_IMP
unsafe def REAL_EQ_LCANCEL_IMP   : thm := realThms8.REAL_EQ_LCANCEL_IMP
unsafe def REAL_LT_DIV           : thm := realThms8.REAL_LT_DIV
unsafe def REAL_LE_DIV           : thm := realThms8.REAL_LE_DIV
unsafe def REAL_DIV_POW2         : thm := realThms8.REAL_DIV_POW2
unsafe def REAL_DIV_POW2_ALT     : thm := realThms8.REAL_DIV_POW2_ALT
unsafe def REAL_LT_POW2          : thm := realThms8.REAL_LT_POW2
unsafe def REAL_LE_POW2          : thm := realThms8.REAL_LE_POW2
unsafe def REAL_POW2_ABS         : thm := realThms8.REAL_POW2_ABS
unsafe def REAL_LE_SQUARE_ABS    : thm := realThms8.REAL_LE_SQUARE_ABS
unsafe def REAL_LT_SQUARE_ABS    : thm := realThms8.REAL_LT_SQUARE_ABS
unsafe def REAL_EQ_SQUARE_ABS    : thm := realThms8.REAL_EQ_SQUARE_ABS
unsafe def REAL_LE_POW_2         : thm := realThms8.REAL_LE_POW_2
unsafe def REAL_LT_POW_2         : thm := realThms8.REAL_LT_POW_2
unsafe def REAL_SOS_EQ_0         : thm := realThms8.REAL_SOS_EQ_0
unsafe def REAL_POW_ZERO         : thm := realThms8.REAL_POW_ZERO
unsafe def REAL_POW_MONO_INV     : thm := realThms8.REAL_POW_MONO_INV
unsafe def REAL_POW_LE2_REV      : thm := realThms8.REAL_POW_LE2_REV
unsafe def REAL_POW_LT2_REV      : thm := realThms8.REAL_POW_LT2_REV
unsafe def REAL_POW_EQ           : thm := realThms8.REAL_POW_EQ
unsafe def REAL_POW_EQ_ABS       : thm := realThms8.REAL_POW_EQ_ABS
unsafe def REAL_POW_EQ_1_IMP     : thm := realThms8.REAL_POW_EQ_1_IMP
unsafe def REAL_POW_EQ_1         : thm := realThms8.REAL_POW_EQ_1
unsafe def REAL_POW_LT2_ODD      : thm := realThms8.REAL_POW_LT2_ODD
unsafe def REAL_POW_LE2_ODD      : thm := realThms8.REAL_POW_LE2_ODD
unsafe def REAL_POW_LT2_ODD_EQ   : thm := realThms8.REAL_POW_LT2_ODD_EQ
unsafe def REAL_POW_LE2_ODD_EQ   : thm := realThms8.REAL_POW_LE2_ODD_EQ
unsafe def REAL_POW_EQ_ODD_EQ    : thm := realThms8.REAL_POW_EQ_ODD_EQ
unsafe def REAL_POW_EQ_ODD       : thm := realThms8.REAL_POW_EQ_ODD
unsafe def REAL_POW_EQ_EQ        : thm := realThms8.REAL_POW_EQ_EQ
unsafe def REAL_EVENPOW_ABS      : thm := realThms8.REAL_EVENPOW_ABS
unsafe def REAL_OF_NUM_MOD       : thm := realThms8.REAL_OF_NUM_MOD
unsafe def REAL_OF_NUM_DIV       : thm := realThms8.REAL_OF_NUM_DIV
unsafe def REAL_CONVEX_BOUND2_LT : thm := realThms9.REAL_CONVEX_BOUND2_LT
unsafe def REAL_CONVEX_BOUND2_LE : thm := realThms9.REAL_CONVEX_BOUND2_LE
unsafe def REAL_CONVEX_BOUND_LT  : thm := realThms9.REAL_CONVEX_BOUND_LT
unsafe def REAL_CONVEX_BOUND_LE  : thm := realThms9.REAL_CONVEX_BOUND_LE
unsafe def REAL_CONVEX_BOUND_GT  : thm := realThms9.REAL_CONVEX_BOUND_GT
unsafe def REAL_CONVEX_BOUND_GE  : thm := realThms9.REAL_CONVEX_BOUND_GE
unsafe def REAL_CONVEX_BOUNDS_LE : thm := realThms9.REAL_CONVEX_BOUNDS_LE
unsafe def REAL_CONVEX_BOUNDS_LT : thm := realThms9.REAL_CONVEX_BOUNDS_LT
unsafe def REAL_ARCH_SIMPLE      : thm := realThms9.REAL_ARCH_SIMPLE
unsafe def REAL_ARCH_LT          : thm := realThms9.REAL_ARCH_LT
unsafe def REAL_ARCH             : thm := realThms9.REAL_ARCH
unsafe def REAL_ARCH_INV         : thm := realThms9.REAL_ARCH_INV
unsafe def REAL_POW_LBOUND       : thm := realThms9.REAL_POW_LBOUND
unsafe def REAL_ARCH_POW         : thm := realThms9.REAL_ARCH_POW
unsafe def REAL_ARCH_POW2        : thm := realThms9.REAL_ARCH_POW2
unsafe def REAL_ARCH_POW_INV     : thm := realThms9.REAL_ARCH_POW_INV
unsafe def real_sgn              : thm := realThms10.real_sgn
unsafe def REAL_SGN_0            : thm := realThms10.REAL_SGN_0
unsafe def REAL_SGN_NEG          : thm := realThms10.REAL_SGN_NEG
unsafe def REAL_SGN_ABS          : thm := realThms10.REAL_SGN_ABS
unsafe def REAL_SGN_ABS_ALT      : thm := realThms10.REAL_SGN_ABS_ALT
unsafe def REAL_EQ_SGN_ABS       : thm := realThms10.REAL_EQ_SGN_ABS
unsafe def REAL_ABS_SGN          : thm := realThms10.REAL_ABS_SGN
unsafe def REAL_SGN              : thm := realThms10.REAL_SGN
unsafe def REAL_SGN_MUL          : thm := realThms10.REAL_SGN_MUL
unsafe def REAL_SGN_INV          : thm := realThms10.REAL_SGN_INV
unsafe def REAL_SGN_DIV          : thm := realThms10.REAL_SGN_DIV
unsafe def REAL_SGN_EQ           : thm := realThms10.REAL_SGN_EQ
unsafe def REAL_SGN_CASES        : thm := realThms10.REAL_SGN_CASES
unsafe def REAL_SGN_INEQS        : thm := realThms10.REAL_SGN_INEQS
unsafe def REAL_SGN_POW          : thm := realThms10.REAL_SGN_POW
unsafe def REAL_SGN_POW_2        : thm := realThms10.REAL_SGN_POW_2
unsafe def REAL_SGN_REAL_SGN     : thm := realThms10.REAL_SGN_REAL_SGN
unsafe def REAL_INV_SGN          : thm := realThms10.REAL_INV_SGN
unsafe def REAL_SGN_EQ_INEQ      : thm := realThms10.REAL_SGN_EQ_INEQ
unsafe def REAL_SGNS_EQ          : thm := realThms10.REAL_SGNS_EQ
unsafe def REAL_SGNS_EQ_ALT      : thm := realThms10.REAL_SGNS_EQ_ALT
unsafe def REAL_WLOG_LE          : thm := realThms10.REAL_WLOG_LE
unsafe def REAL_WLOG_LT          : thm := realThms10.REAL_WLOG_LT
unsafe def REAL_WLOG_LE_3        : thm := realThms10.REAL_WLOG_LE_3
unsafe def sqrt                  : thm := realThms11.sqrt
unsafe def SQRT_UNIQUE           : thm := realThms11.SQRT_UNIQUE
unsafe def POW_2_SQRT            : thm := realThms11.POW_2_SQRT
unsafe def SQRT_0                : thm := realThms11.SQRT_0
unsafe def SQRT_1                : thm := realThms11.SQRT_1
unsafe def POW_2_SQRT_ABS        : thm := realThms11.POW_2_SQRT_ABS
unsafe def SQRT_WORKS_GEN        : thm := realThms11.SQRT_WORKS_GEN
unsafe def SQRT_UNIQUE_GEN       : thm := realThms11.SQRT_UNIQUE_GEN
unsafe def SQRT_NEG              : thm := realThms11.SQRT_NEG
unsafe def REAL_SGN_SQRT         : thm := realThms11.REAL_SGN_SQRT
unsafe def SQRT_WORKS            : thm := realThms11.SQRT_WORKS
unsafe def REAL_POS_EQ_SQUARE    : thm := realThms11.REAL_POS_EQ_SQUARE
unsafe def SQRT_POS_LE           : thm := realThms11.SQRT_POS_LE
unsafe def SQRT_POW_2            : thm := realThms11.SQRT_POW_2
unsafe def SQRT_POW2             : thm := realThms11.SQRT_POW2
unsafe def SQRT_MUL              : thm := realThms11.SQRT_MUL
unsafe def SQRT_INV              : thm := realThms11.SQRT_INV
unsafe def SQRT_DIV              : thm := realThms11.SQRT_DIV
unsafe def SQRT_LT_0             : thm := realThms11.SQRT_LT_0
unsafe def SQRT_EQ_0             : thm := realThms11.SQRT_EQ_0
unsafe def SQRT_LE_0             : thm := realThms11.SQRT_LE_0
unsafe def REAL_ABS_SQRT         : thm := realThms11.REAL_ABS_SQRT
unsafe def SQRT_MONO_LT          : thm := realThms11.SQRT_MONO_LT
unsafe def SQRT_MONO_LE          : thm := realThms11.SQRT_MONO_LE
unsafe def SQRT_MONO_LT_EQ       : thm := realThms11.SQRT_MONO_LT_EQ
unsafe def SQRT_MONO_LE_EQ       : thm := realThms11.SQRT_MONO_LE_EQ
unsafe def SQRT_INJ              : thm := realThms11.SQRT_INJ
unsafe def SQRT_EQ_1             : thm := realThms11.SQRT_EQ_1
unsafe def SQRT_POS_LT           : thm := realThms11.SQRT_POS_LT
unsafe def REAL_LE_LSQRT         : thm := realThms11.REAL_LE_LSQRT
unsafe def REAL_LE_RSQRT         : thm := realThms11.REAL_LE_RSQRT
unsafe def REAL_LT_LSQRT         : thm := realThms11.REAL_LT_LSQRT
unsafe def REAL_LT_RSQRT         : thm := realThms11.REAL_LT_RSQRT
unsafe def SQRT_EVEN_POW2        : thm := realThms11.SQRT_EVEN_POW2
unsafe def REAL_DIV_SQRT         : thm := realThms11.REAL_DIV_SQRT
unsafe def REAL_RSQRT_LE         : thm := realThms11.REAL_RSQRT_LE
unsafe def REAL_LSQRT_LE         : thm := realThms11.REAL_LSQRT_LE
unsafe def REAL_SQRT_POW_2       : thm := realThms11.REAL_SQRT_POW_2
unsafe def REAL_ABS_LE_SQRT_POS  : thm := realThms11.REAL_ABS_LE_SQRT_POS
unsafe def REAL_ABS_LE_SQRT      : thm := realThms11.REAL_ABS_LE_SQRT

/- ---------------------------------------------------------------------- -/
/- calc_rat.ml (hol_lib.ml 97): calculation with rational-valued reals.   -/
/-                                                                        -/
/- Fifteen setups wired in dependency order.  This is the THIRD and final -/
/- redefinition of GEN_REAL_ARITH / REAL_ARITH / REAL_ARITH_TAC: the      -/
/- final tools here SUPERSEDE realarith.ml's REAL_ARITH2 / real.ml's      -/
/- REAL_ARITH_TAC and are what general code should now use.  Each setup   -/
/- is memoised behind an `IO.Ref` cache read by a private CAF that runs   -/
/- the setup once and `panic!`s with a clear message on error; PUBLIC     -/
/- accessors below expose each bundle.                                    -/
/-                                                                        -/
/- `setupDecimal` CREATES the `DECIMAL` constant, so like `real_sgn`/     -/
/- `sqrt` its setup is NOT idempotent and must run exactly once.  Because -/
/- the relational/unary/arith setups PARSE terms mentioning `DECIMAL`     -/
/- (their `pth` proofs rewrite it away), the constant must be DECLARED    -/
/- before those parses.  Threading the `Dec` theorem as each such setup's -/
/- `DECIMAL` parameter forces the once-only CAF first, exactly as         -/
/- `ensureRealAxOverloads`/`RSyn` force their prerequisites; a bare       -/
/- `let _ := Dec` would NOT force a Lean CAF, so the                     -/
/- force is a genuine parameter dependency, not a discard.                -/
/- ---------------------------------------------------------------------- -/

/- `RealRingConvs`/`FinalRealArith` carry only function-typed fields (`term →
   IO ...` etc.) and are NOT declared `Inhabited` in the pure library, but the
   CAF extraction pattern below (`match unsafeIO ... | _ => panic!`) needs an
   `Inhabited` fallback.  Functions into `IO` are inhabited, so Lean derives
   these (same device as `RealArith1Ctx`/`RealArith2Ctx` above). -/
deriving instance Inhabited for HolMath.CalcRat.RealRingConvs
deriving instance Inhabited for HolMath.CalcRat.FinalRealArith
deriving instance Inhabited for HolMath.CalcRat.RealPolyConvs1

/-- Cache for `DECIMAL` (calc_rat.ml 16-17): `|- DECIMAL x y = &x / &y`.
    CREATES a new constant, so NOT idempotent - this once-only CAF guarantees
    `setupDecimal` runs exactly once.  Reading `Dec` declares the constant, so
    every downstream setup that parses a `DECIMAL`-mentioning term takes `Dec`
    as its `DECIMAL` parameter to force this first. -/
initialize theDecimal : IO.Ref (Option thm) ← IO.mkRef none

private unsafe def Dec : thm :=
  match unsafeIO (do
    match ← theDecimal.get with
    | some d => pure d
    | none => do
      -- calc_rat.ml sits above real.ml; force the real layer so `&x / &y`
      -- parses.  (`let _ := Rl...` would NOT force a Lean CAF.)
      let _ ← IO.mkRef (concl Rl.REAL_COMPLETE)
      match ← (HolMath.CalcRat.setupDecimal new_definition).run with
      | .ok d => do theDecimal.set (some d); pure d
      | .error e => panic! s!"setupDecimal failed: {e}") with
  | .ok d => d | _ => panic! "Session.Dec: setupDecimal not run"

/-- Cache for `RatLemmas` (calc_rat.ml 20-80): `RAT_LEMMA1..5`. -/
initialize theRatLemmas : IO.Ref (Option HolMath.CalcRat.RatLemmas) ← IO.mkRef none

private unsafe def RatLm : HolMath.CalcRat.RatLemmas :=
  match unsafeIO (do
    match ← theRatLemmas.get with
    | some d => pure d
    | none =>
      match ← (HolMath.CalcRat.setupRatLemmas Rl CiT RaL RT1 RT6
                 REAL_ARITH2).run with
      | .ok d => do theRatLemmas.set (some d); pure d
      | .error e => panic! s!"setupRatLemmas failed: {e}") with
  | .ok d => d | _ => panic! "Session.RatLm: setupRatLemmas not run"

/-- Cache for `RealRatRelConvs` (calc_rat.ml 81-171): `REAL_INT_RAT_CONV` and
    the six relational conversions (LE, LT, GE, GT, EQ, SGN). -/
initialize theRealRatRelConvs :
  IO.Ref (Option HolMath.CalcRat.RealRatRelConvs) ← IO.mkRef none

private unsafe def RRel : HolMath.CalcRat.RealRatRelConvs :=
  match unsafeIO (do
    match ← theRealRatRelConvs.get with
    | some d => pure d
    | none =>
      match ← (HolMath.CalcRat.setupRealRatRelConvs RatLm Dec CiV CiW
                 Rl CiT RT2 RT6 RT10).run with
      | .ok d => do theRealRatRelConvs.set (some d); pure d
      | .error e => panic! s!"setupRealRatRelConvs failed: {e}") with
  | .ok d => d | _ => panic! "Session.RRel: setupRealRatRelConvs not run"

/-- `REAL_INT_RAT_CONV` (calc_rat.ml 84). -/
unsafe def REAL_INT_RAT_CONV : ioconv := fun tm => RRel.REAL_INT_RAT_CONV tm

/-- Cache for `RealRatUnaryConvs` (calc_rat.ml 172-229): NEG, ABS, INV. -/
initialize theRealRatUnaryConvs :
  IO.Ref (Option HolMath.CalcRat.RealRatUnaryConvs) ← IO.mkRef none

private unsafe def RUn : HolMath.CalcRat.RealRatUnaryConvs :=
  match unsafeIO (do
    match ← theRealRatUnaryConvs.get with
    | some d => pure d
    | none =>
      match ← (HolMath.CalcRat.setupRealRatUnaryConvs Dec Rl CiT RaL RT1 RT6).run with
      | .ok d => do theRealRatUnaryConvs.set (some d); pure d
      | .error e => panic! s!"setupRealRatUnaryConvs failed: {e}") with
  | .ok d => d | _ => panic! "Session.RUn: setupRealRatUnaryConvs not run"

/-- Cache for `RealRatArithConvs` (calc_rat.ml 230-358): ADD, SUB, MUL, DIV. -/
initialize theRealRatArithConvs :
  IO.Ref (Option HolMath.CalcRat.RealRatArithConvs) ← IO.mkRef none

private unsafe def RAr : HolMath.CalcRat.RealRatArithConvs :=
  match unsafeIO (do
    match ← theRealRatArithConvs.get with
    | some d => pure d
    | none =>
      match ← (HolMath.CalcRat.setupRealRatArithConvs RatLm RRel RUn CiV CiW
                 RSyn Rl RaL RT1 RT6 REAL_INT_REDUCE_CONV).run with
      | .ok d => do theRealRatArithConvs.set (some d); pure d
      | .error e => panic! s!"setupRealRatArithConvs failed: {e}") with
  | .ok d => d | _ => panic! "Session.RAr: setupRealRatArithConvs not run"

/-- Cache for `RealRatPowMaxMinConvs` (calc_rat.ml 359-385): POW, MAX, MIN. -/
initialize theRealRatPowMaxMinConvs :
  IO.Ref (Option HolMath.CalcRat.RealRatPowMaxMinConvs) ← IO.mkRef none

private unsafe def RPmm : HolMath.CalcRat.RealRatPowMaxMinConvs :=
  match unsafeIO (do
    match ← theRealRatPowMaxMinConvs.get with
    | some d => pure d
    | none =>
      match ← (HolMath.CalcRat.setupRealRatPowMaxMinConvs RRel CiW Rl RT6).run with
      | .ok d => do theRealRatPowMaxMinConvs.set (some d); pure d
      | .error e => panic! s!"setupRealRatPowMaxMinConvs failed: {e}") with
  | .ok d => d | _ => panic! "Session.RPmm: setupRealRatPowMaxMinConvs not run"

/- Public accessors for the calc_rat.ml conversion bundles. -/

/-- The `calc_rat.ml` relational conversions (81-171). -/
unsafe def realRatRelConvs : HolMath.CalcRat.RealRatRelConvs := RRel
/-- The `calc_rat.ml` unary conversions (172-229). -/
unsafe def realRatUnaryConvs : HolMath.CalcRat.RealRatUnaryConvs := RUn
/-- The `calc_rat.ml` arithmetic conversions (230-358). -/
unsafe def realRatArithConvs : HolMath.CalcRat.RealRatArithConvs := RAr
/-- The `calc_rat.ml` powers/max/min conversions (359-385). -/
unsafe def realRatPowMaxMinConvs : HolMath.CalcRat.RealRatPowMaxMinConvs := RPmm

/- The rational-constant conversions as plain `ioconv`s. -/

/-- `REAL_RAT_LE_CONV` (calc_rat.ml 98). -/
unsafe def REAL_RAT_LE_CONV  : ioconv := RRel.REAL_RAT_LE_CONV
/-- `REAL_RAT_LT_CONV` (calc_rat.ml 117). -/
unsafe def REAL_RAT_LT_CONV  : ioconv := RRel.REAL_RAT_LT_CONV
/-- `REAL_RAT_GE_CONV` (calc_rat.ml 138). -/
unsafe def REAL_RAT_GE_CONV  : ioconv := RRel.REAL_RAT_GE_CONV
/-- `REAL_RAT_GT_CONV` (calc_rat.ml 141). -/
unsafe def REAL_RAT_GT_CONV  : ioconv := RRel.REAL_RAT_GT_CONV
/-- `REAL_RAT_EQ_CONV` (calc_rat.ml 144); also `RING_EQ_CONV` for `REAL_RING`. -/
unsafe def REAL_RAT_EQ_CONV  : ioconv := RRel.REAL_RAT_EQ_CONV
/-- `REAL_RAT_SGN_CONV` (calc_rat.ml 163). -/
unsafe def REAL_RAT_SGN_CONV : ioconv := RRel.REAL_RAT_SGN_CONV
/-- `REAL_RAT_NEG_CONV` (calc_rat.ml 175). -/
unsafe def REAL_RAT_NEG_CONV : ioconv := RUn.REAL_RAT_NEG_CONV
/-- `REAL_RAT_ABS_CONV` (calc_rat.ml 194). -/
unsafe def REAL_RAT_ABS_CONV : ioconv := RUn.REAL_RAT_ABS_CONV
/-- `REAL_RAT_INV_CONV` (calc_rat.ml 205). -/
unsafe def REAL_RAT_INV_CONV : ioconv := RUn.REAL_RAT_INV_CONV
/-- `REAL_RAT_ADD_CONV` (calc_rat.ml 233). -/
unsafe def REAL_RAT_ADD_CONV : ioconv := RAr.REAL_RAT_ADD_CONV
/-- `REAL_RAT_SUB_CONV` (calc_rat.ml 279). -/
unsafe def REAL_RAT_SUB_CONV : ioconv := RAr.REAL_RAT_SUB_CONV
/-- `REAL_RAT_MUL_CONV` (calc_rat.ml 290). -/
unsafe def REAL_RAT_MUL_CONV : ioconv := RAr.REAL_RAT_MUL_CONV
/-- `REAL_RAT_DIV_CONV` (calc_rat.ml 351). -/
unsafe def REAL_RAT_DIV_CONV : ioconv := RAr.REAL_RAT_DIV_CONV
/-- `REAL_RAT_POW_CONV` (calc_rat.ml 362). -/
unsafe def REAL_RAT_POW_CONV : ioconv := RPmm.REAL_RAT_POW_CONV
/-- `REAL_RAT_MAX_CONV` (calc_rat.ml 375). -/
unsafe def REAL_RAT_MAX_CONV : ioconv := RPmm.REAL_RAT_MAX_CONV
/-- `REAL_RAT_MIN_CONV` (calc_rat.ml 380). -/
unsafe def REAL_RAT_MIN_CONV : ioconv := RPmm.REAL_RAT_MIN_CONV

/-- Cache for `REAL_RAT_RED_CONV` (calc_rat.ml 407): one reduction step over a
    snapshot of `basic_net()` extended with the sixteen conversions.  The
    OCaml SNAPSHOTS `basic_net()` once when the conversion is defined; this
    `IO.Ref` reproduces that evaluate-once semantics (matching `CalcInt`'s
    `theRealIntRed`). -/
initialize theRealRatRedConvList : IO.Ref (Option (List (term × ioconv))) ← IO.mkRef none

/-- `real_rat_red_conv_list` (calc_rat.ml 389-405), built once. -/
unsafe def real_rat_red_conv_list : IO (Except String (List (term × ioconv))) := do
  match ← theRealRatRedConvList.get with
  | some l => return .ok l
  | none =>
    match ← (HolMath.CalcRat.real_rat_red_conv_list RRel RUn RAr RPmm).run with
    | .ok l => do theRealRatRedConvList.set (some l); return .ok l
    | .error e => return .error e

initialize theRealRatRed : IO.Ref (Option ioconv) ← IO.mkRef none

/-- `REAL_RAT_RED_CONV` (calc_rat.ml 407). -/
unsafe def REAL_RAT_RED_CONV : ioconv := fun tm => do
  match ← theRealRatRed.get with
  | some c => c tm
  | none =>
    match ← (do HolMath.CalcRat.REAL_RAT_RED_CONV (← ExceptT.mk real_rat_red_conv_list)).run with
    | .ok c => do theRealRatRed.set (some c); c tm
    | .error e => return .error s!"REAL_RAT_RED_CONV: {e}"

/-- `REAL_RAT_REDUCE_CONV` (calc_rat.ml 412): `DEPTH_CONV REAL_RAT_RED_CONV`.
    The entry point `REAL_FIELD` relies on, so it must work standalone. -/
unsafe def REAL_RAT_REDUCE_CONV : ioconv := Simp.depthConvIO REAL_RAT_RED_CONV

/-- `REAL_RAT_REDUCE_TAC`: `CONV_TAC REAL_RAT_REDUCE_CONV`. -/
unsafe def REAL_RAT_REDUCE_TAC : tactic := CONV_TAC REAL_RAT_REDUCE_CONV

/-- `real_rat_compute_add_convs` (calc_rat.ml 414): register the sixteen
    conversions with a `compset`. -/
unsafe def real_rat_compute_add_convs (cs : HolMath.Compute.compset) :
    IO (Except String Unit) :=
  (do HolMath.CalcRat.real_rat_compute_add_convs (← ExceptT.mk real_rat_red_conv_list) cs).run

/-- Cache for `REAL_RAT_COMPUTE_CONV` (calc_rat.ml 421): call-by-value
    reduction over the boolean compset extended with the sixteen conversions.
    The OCaml builds its compset once, so memoise. -/
initialize theRealRatCompute : IO.Ref (Option ioconv) ← IO.mkRef none

/-- `REAL_RAT_COMPUTE_CONV` (calc_rat.ml 421). -/
unsafe def REAL_RAT_COMPUTE_CONV : ioconv := fun tm => do
  match ← theRealRatCompute.get with
  | some c => c tm
  | none =>
    let cl ← real_rat_red_conv_list
    let mk : ExceptT String IO ioconv := do
      HolMath.CalcRat.REAL_RAT_COMPUTE_CONV (← liftExcept cl) bool_compset WEAK_CBV_CONV
    match ← mk.run with
    | .ok c => do theRealRatCompute.set (some c); c tm
    | .error e => return .error s!"REAL_RAT_COMPUTE_CONV: {e}"

/-- Cache for `RealPolyConvs1` (calc_rat.ml 428-438): the six rational
    normalizer conversions.  THE DECISIVE STEP - instantiated with
    `is_ratconst`, so rational constants become foldable coefficients (this is
    why the final `REAL_ARITH` beats realarith.ml's on `/ &2`-style goals). -/
initialize theRealPolyConvs1 :
  IO.Ref (Option HolMath.CalcRat.RealPolyConvs1) ← IO.mkRef none

private unsafe def Q1 : HolMath.CalcRat.RealPolyConvs1 :=
  match unsafeIO (do
    match ← theRealPolyConvs1.get with
    | some d => pure d
    | none =>
      match ← (HolMath.CalcRat.setupRealPolyConvs1 RaL RAr RPmm
                 TRUTH NmzP.2 num_CONV
                 NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV).run with
      | .ok d => do theRealPolyConvs1.set (some d); pure d
      | .error e => panic! s!"setupRealPolyConvs1 failed: {e}") with
  | .ok d => d | _ => panic! "Session.Q1: setupRealPolyConvs1 not run"

/-- Cache for `REAL_POLY_CONV` (calc_rat.ml 443-485): the SECOND normalizer,
    extending the first to `inv`, division by rational constants, and the
    abs/max/min wrappers. -/
initialize theRealPolyConv2 : IO.Ref (Option ioconv) ← IO.mkRef none

/-- `REAL_POLY_CONV` (the calc_rat.ml 443 redefinition, the `RING_NORMALIZE_CONV`
    for `REAL_RING`/`GEN_REAL_ARITH3`). -/
unsafe def REAL_POLY_CONV : ioconv := fun tm => do
  match ← theRealPolyConv2.get with
  | some c => c tm
  | none =>
    match ← (HolMath.CalcRat.setupRealPolyConv2 Rl RUn Q1).run with
    | .ok c => do theRealPolyConv2.set (some c); c tm
    | .error e => return .error s!"REAL_POLY_CONV: {e}"

/- The six first-normalizer polynomial conversions (calc_rat.ml 431). -/

/-- `REAL_POLY_NEG_CONV` (calc_rat.ml 431). -/
unsafe def REAL_POLY_NEG_CONV : ioconv := Q1.polys.POLYNOMIAL_NEG_CONV
/-- `REAL_POLY_ADD_CONV` (calc_rat.ml 431). -/
unsafe def REAL_POLY_ADD_CONV : ioconv := Q1.polys.POLYNOMIAL_ADD_CONV
/-- `REAL_POLY_SUB_CONV` (calc_rat.ml 431). -/
unsafe def REAL_POLY_SUB_CONV : ioconv := Q1.polys.POLYNOMIAL_SUB_CONV
/-- `REAL_POLY_MUL_CONV` (calc_rat.ml 431). -/
unsafe def REAL_POLY_MUL_CONV : ioconv := Q1.polys.POLYNOMIAL_MUL_CONV
/-- `REAL_POLY_POW_CONV` (calc_rat.ml 431). -/
unsafe def REAL_POLY_POW_CONV : ioconv := Q1.polys.POLYNOMIAL_POW_CONV

/-- Cache for `RealRingConvs` (calc_rat.ml 487-533): `REAL_RING`,
    `real_ideal_cofactors`, `REAL_IDEAL_CONV`.  The two nested `prove`s
    (`REAL_INTEGRAL`, `REAL_RABINOWITSCH`) use the EARLIER `REAL_ARITH`
    (`REAL_ARITH2`), the non-circular choice. -/
initialize theRealRingConvs :
  IO.Ref (Option HolMath.CalcRat.RealRingConvs) ← IO.mkRef none

private unsafe def RRing : HolMath.CalcRat.RealRingConvs :=
  match unsafeIO (do
    match ← theRealRingConvs.get with
    | some d => pure d
    | none =>
      match ← (HolMath.CalcRat.setupRealRing RSyn RRel REAL_POLY_CONV Dec Nm.numK
                 MULT_CLAUSES EQ_ADD_LCANCEL
                 REAL_OF_NUM_EQ REAL_OF_NUM_ADD REAL_OF_NUM_MUL
                 REAL_SUB_0 REAL_ENTIRE REAL_MUL_RINV REAL_MUL_LZERO
                 REAL_ARITH2 MESON_TAC
                 PRESIMP_CONV CONDS_ELIM_CONV NNF_CONV WEAK_DNF_CONV
                 AND_FORALL_THM LEFT_AND_FORALL_THM RIGHT_AND_FORALL_THM
                 LEFT_OR_FORALL_THM RIGHT_OR_FORALL_THM OR_EXISTS_THM
                 LEFT_OR_EXISTS_THM RIGHT_OR_EXISTS_THM LEFT_AND_EXISTS_THM
                 RIGHT_AND_EXISTS_THM
                 GrG TRUTH).run with
      | .ok d => do theRealRingConvs.set (some d); pure d
      | .error e => panic! s!"setupRealRing failed: {e}") with
  | .ok d => d | _ => panic! "Session.RRing: setupRealRing not run"

/-- `REAL_RING tm` (calc_rat.ml 490/514): the ring decision procedure. -/
unsafe def REAL_RING : term → IO (Except String thm) := RRing.REAL_RING
/-- `real_ideal_cofactors tms tm` (calc_rat.ml 490/515). -/
unsafe def real_ideal_cofactors : List term → term → IO (Except String (List term)) :=
  RRing.real_ideal_cofactors
/-- `REAL_IDEAL_CONV tms tm` (calc_rat.ml 524). -/
unsafe def REAL_IDEAL_CONV : List term → term → IO (Except String thm) :=
  RRing.REAL_IDEAL_CONV

/-- Cache for `FinalRealArith` (calc_rat.ml 534-559): `GEN_REAL_ARITH3`,
    `REAL_ARITH3`, `REAL_ARITH_TAC2`, `ASM_REAL_ARITH_TAC`.  These are the
    FINAL versions and SUPERSEDE realarith.ml's `REAL_ARITH2` / real.ml's
    `REAL_ARITH_TAC`; general code should now use these. -/
initialize theFinalRealArith :
  IO.Ref (Option HolMath.CalcRat.FinalRealArith) ← IO.mkRef none

private unsafe def FRA : HolMath.CalcRat.FinalRealArith :=
  match unsafeIO (do
    match ← theFinalRealArith.get with
    | some d => pure d
    | none =>
      match ← (HolMath.CalcRat.setupFinalRealArith nnfPths GrA1 GrA2
                 PRESIMP_CONV NNF_CONV CONDS_ELIM_CONV SKOLEM_CONV PRENEX_CONV
                 WEAK_DNF_CONV RSyn RRel Q1 REAL_POLY_CONV Dec
                 REAL_LINEAR_PROVER).run with
      | .ok d => do theFinalRealArith.set (some d); pure d
      | .error e => panic! s!"setupFinalRealArith failed: {e}") with
  | .ok d => d | _ => panic! "Session.FRA: setupFinalRealArith not run"

/-- The `calc_rat.ml` final real-arithmetic bundle (534-559). -/
unsafe def finalRealArith : HolMath.CalcRat.FinalRealArith := FRA

/-- `GEN_REAL_ARITH3 PROVER tm` (calc_rat.ml 537): the FINAL, one-parameter
    (just the `PROVER`) `GEN_REAL_ARITH`.  SUPERSEDES `GEN_REAL_ARITH1`
    (eleven params) and `GEN_REAL_ARITH2` (nine); all nine forwarded slots are
    rational versions from calc_rat.ml, which is what lets it beat the earlier
    versions on rational-denominator goals. -/
unsafe def GEN_REAL_ARITH3 :
    (((List thm × List thm × List thm) →
      HolMath.RealArith.positivstellensatz → IO (Except String thm)) →
     (List thm × List thm × List thm) → IO (Except String thm)) →
    term → IO (Except String thm) := FRA.GEN_REAL_ARITH3

/-- `REAL_ARITH3 tm` (calc_rat.ml 544): the FINAL real decision procedure,
    with the `DECIMAL` `init` path and the term-embedding error wrapper.
    SUPERSEDES realarith.ml's `REAL_ARITH2`; proves goals with rational
    denominators (`/ &2`, `/ &6`, ...) the earlier version cannot.  This is
    the `REAL_ARITH` general code should now use. -/
unsafe def REAL_ARITH3 : term → IO (Except String thm) := FRA.REAL_ARITH3

/-- `REAL_ARITH_TAC2` (calc_rat.ml 553): `CONV_TAC REAL_ARITH3`.  SUPERSEDES
    real.ml 106's `REAL_ARITH_TAC` (which was over `REAL_ARITH2`); this is the
    tactic general code should now use. -/
unsafe def REAL_ARITH_TAC2 : tactic := FRA.REAL_ARITH_TAC2

/-- `ASM_REAL_ARITH_TAC` (calc_rat.ml 555): move the non-universal assumptions
    into the goal, then `REAL_ARITH_TAC2`.  Appears here for the FIRST time in
    the whole development. -/
unsafe def ASM_REAL_ARITH_TAC : tactic := FRA.ASM_REAL_ARITH_TAC

/-- Cache for `RealFieldTrans` (calc_rat.ml 560-577): the three equivalential
    transitivity forms.  Uses this file's FINAL `REAL_ARITH` (`REAL_ARITH3`). -/
initialize theRealFieldTrans :
  IO.Ref (Option HolMath.CalcRat.RealFieldTrans) ← IO.mkRef none

private unsafe def RFT : HolMath.CalcRat.RealFieldTrans :=
  match unsafeIO (do
    match ← theRealFieldTrans.get with
    | some d => pure d
    | none =>
      match ← (HolMath.CalcRat.setupRealFieldTrans Rl MESON_TAC REAL_ARITH3).run with
      | .ok d => do theRealFieldTrans.set (some d); pure d
      | .error e => panic! s!"setupRealFieldTrans failed: {e}") with
  | .ok d => d | _ => panic! "Session.RFT: setupRealFieldTrans not run"

/-- `REAL_FIELD tm` (calc_rat.ml 581-630): the field decision procedure, for
    goals genuinely needing division and nonzero-denominator side conditions
    that `REAL_RING` alone cannot prove.  `core_rule` falls back to
    `REAL_ARITH3` when `REAL_RING` fails. -/
initialize theRealField : IO.Ref (Option (term → IO (Except String thm))) ← IO.mkRef none

/-- Build (once) the `REAL_FIELD` procedure (calc_rat.ml 581-630). -/
private unsafe def realFieldIO : IO (Except String (term → IO (Except String thm))) := do
  match ← theRealField.get with
  | some f => return .ok f
  | none =>
    match ← (HolMath.CalcRat.setupRealField Rl RT6 RT7
               NNF_CONV NNFC_CONV WEAK_CNF_CONV CONJ_CANON_CONV PRENEX_CONV
               CONDS_CELIM_CONV NUM_REDUCE_CONV REAL_RAT_REDUCE_CONV
               REAL_RING REAL_ARITH3 MESON).run with
    | .ok f => do theRealField.set (some f); return .ok f
    | .error e => return .error s!"REAL_FIELD: {e}"

unsafe def REAL_FIELD : term → IO (Except String thm) := fun tm => do
  match ← realFieldIO with
  | .ok f => f tm
  | .error e => return .error e

/-- Cache for `RealShrink` (calc_rat.ml 631-688): the eight monotone-mapping
    theorems between R and (-1,1). -/
initialize theRealShrink :
  IO.Ref (Option HolMath.CalcRat.RealShrink) ← IO.mkRef none

private unsafe def RShr : HolMath.CalcRat.RealShrink :=
  match unsafeIO (do
    match ← theRealShrink.get with
    | some d => pure d
    | none =>
      match ← (HolMath.CalcRat.setupRealShrink Rl CiT RaL RT6 RT7
                 REAL_ARITH3 REAL_FIELD MESON MESON_TAC).run with
      | .ok d => do theRealShrink.set (some d); pure d
      | .error e => panic! s!"setupRealShrink failed: {e}") with
  | .ok d => d | _ => panic! "Session.RShr: setupRealShrink not run"

/-- The `calc_rat.ml` transitivity forms (560-577). -/
unsafe def realFieldTrans : HolMath.CalcRat.RealFieldTrans := RFT
/-- The `calc_rat.ml` monotone-mapping theorems (631-688). -/
unsafe def realShrink : HolMath.CalcRat.RealShrink := RShr

/- The calc_rat.ml theorems as bare names, as HOL Light has them.        -/
/- In HOL Light every theorem is a global name; the bundle records are   -/
/- an artefact of this translation, so re-export each field bare too.    -/
/- All 18 names are new; none collides with an earlier bundle (checked   -/
/- against the ~790 existing bare accessors).                            -/
unsafe def RAT_LEMMA1          : thm := RatLm.RAT_LEMMA1
unsafe def RAT_LEMMA2          : thm := RatLm.RAT_LEMMA2
unsafe def RAT_LEMMA3          : thm := RatLm.RAT_LEMMA3
unsafe def RAT_LEMMA4          : thm := RatLm.RAT_LEMMA4
unsafe def RAT_LEMMA5          : thm := RatLm.RAT_LEMMA5
unsafe def DECIMAL             : thm := Dec
unsafe def REAL_LE_TRANS_LE    : thm := RFT.REAL_LE_TRANS_LE
unsafe def REAL_LE_TRANS_LTE   : thm := RFT.REAL_LE_TRANS_LTE
unsafe def REAL_LE_TRANS_LT    : thm := RFT.REAL_LE_TRANS_LT
unsafe def REAL_SHRINK_RANGE   : thm := RShr.REAL_SHRINK_RANGE
unsafe def REAL_SHRINK_LT      : thm := RShr.REAL_SHRINK_LT
unsafe def REAL_SHRINK_LE      : thm := RShr.REAL_SHRINK_LE
unsafe def REAL_SHRINK_EQ      : thm := RShr.REAL_SHRINK_EQ
unsafe def REAL_SHRINK_GALOIS  : thm := RShr.REAL_SHRINK_GALOIS
unsafe def REAL_GROW_SHRINK    : thm := RShr.REAL_GROW_SHRINK
unsafe def REAL_SHRINK_GROW_EQ : thm := RShr.REAL_SHRINK_GROW_EQ
unsafe def REAL_SHRINK_GROW    : thm := RShr.REAL_SHRINK_GROW

/-- `REAL_INTEGRAL` (calc_rat.ml 491), proved by the REAL_RING setup. -/
unsafe def REAL_INTEGRAL : thm := RRing.REAL_INTEGRAL

/-- `REAL_RABINOWITSCH` (calc_rat.ml 500), proved by the REAL_RING setup. -/
unsafe def REAL_RABINOWITSCH : thm := RRing.REAL_RABINOWITSCH

/- ---------------------------------------------------------------------- -/
/- int.ml (hol_lib.ml 98): the integers, embedded in the reals.           -/
/-                                                                        -/
/- Wired in int.ml's own order.  The `integer` predicate and the fourteen -/
/- operations CREATE CONSTANTS; `new_type_definition "int"` CREATES A     -/
/- TYPE; `setupIntInterface`, `setupIntDivRemInfixes` and                 -/
/- `setupIntDivisibility` mutate GLOBAL PARSER STATE - so every such       -/
/- setup is memoised behind an `IO.Ref` cache read by a private CAF that  -/
/- runs it exactly once and `panic!`s on error, and the parser side       -/
/- effects run in int.ml's exact sequence.  Public accessors below expose -/
/- each bundle with its int.ml line range; bare re-exports follow.        -/
/-                                                                        -/
/- `REAL_ARITH` throughout means calc_rat.ml's FINAL `REAL_ARITH3` (int.ml -/
/- sits at hol_lib.ml 98, above calc_rat.ml 97), matching the load order:  -/
/- `REAL_ARITH_TAC` here is `REAL_ARITH_TAC2 = CONV_TAC REAL_ARITH3`.      -/
/- ---------------------------------------------------------------------- -/

/- `IntRingConvs`/`IntDivisibility` carry function-typed fields and are NOT
   declared `Inhabited` in the pure library, but the CAF extraction pattern
   (`match unsafeIO ... | _ => panic!`) needs an `Inhabited` fallback.  Every
   field is a `thm` or a function into `IO` (both inhabited), so Lean derives
   these (same device as `RealRingConvs`/`RealArith1Ctx` above). -/
deriving instance Inhabited for HolMath.Int.IntRingConvs
deriving instance Inhabited for HolMath.Int.IntDivisibility

/-- Cache for the `integer` definition (int.ml 20): `integer(x) <=> ?n. abs
    x = &n`.  CREATES a new constant, so NOT idempotent - this once-only CAF
    guarantees `setupInteger` runs exactly once.  Forcing it declares `integer`. -/
initialize theInteger : IO.Ref (Option thm) ← IO.mkRef none

private unsafe def integerDef : thm :=
  match unsafeIO (do
    match ← theInteger.get with
    | some d => pure d
    | none => do
      -- int.ml sits above calc_rat.ml; force the real/calc_rat layers so
      -- `abs x = &n` parses at `:real`.  (`let _ := Rl...` would NOT force a
      -- Lean CAF; it needs an IO action.)
      let _ ← IO.mkRef (concl Rl.REAL_COMPLETE)
      match ← (HolMath.Int.setupInteger new_definition).run with
      | .ok d => do theInteger.set (some d); pure d
      | .error e => panic! s!"setupInteger failed: {e}") with
  | .ok d => d | _ => panic! "Session.integerDef: setupInteger not run"

/-- Cache for `IntExistence` (int.ml 23-34): `is_int` and the `?x. integer x`
    existence theorem fed to `new_type_definition`.  Pure over `integerDef`;
    uses the FINAL `REAL_ARITH3`. -/
initialize theIntExistence : IO.Ref (Option HolMath.Int.IntExistence) ← IO.mkRef none

private unsafe def IntEx : HolMath.Int.IntExistence :=
  match unsafeIO (do
    match ← theIntExistence.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Int.setupIntExistence Rl integerDef REAL_ARITH3).run with
      | .ok d => do theIntExistence.set (some d); pure d
      | .error e => panic! s!"setupIntExistence failed: {e}") with
  | .ok d => d | _ => panic! "Session.IntEx: setupIntExistence not run"

/-- Cache for the `int` type bijection (int.ml 31): the conjoined theorem
    `new_type_definition "int" "int_of_real" "real_of_int"` returns from the
    `?x. integer x` existence theorem.  CREATES THE `int` TYPE, so NOT
    idempotent - this once-only CAF guarantees the type definition runs exactly
    once (the same precedent as `one_tydef`).  Forcing `IntTb` declares `int`,
    `int_of_real` and `real_of_int`. -/
initialize theIntTybij : IO.Ref (Option HolMath.Int.IntTybij) ← IO.mkRef none

private unsafe def IntTb : HolMath.Int.IntTybij :=
  match unsafeIO (do
    match ← theIntTybij.get with
    | some d => pure d
    | none => do
      -- Create the `int` type (once per process) from `?x. integer x`.
      let int_tybij ← (match ← (new_type_definition "int" "int_of_real"
            "real_of_int" IntEx.int_exists : IO (Except String thm)) with
        | .ok th => pure th | .error e => panic! s!"int_tybij: {e}")
      match ← (HolMath.Int.setupIntTybij IntEx.is_int int_tybij MESON_TAC).run with
      | .ok d => do theIntTybij.set (some d); pure d
      | .error e => panic! s!"setupIntTybij failed: {e}") with
  | .ok d => d | _ => panic! "Session.IntTb: setupIntTybij not run"

/-- Guard for the int interface map (int.ml 55-71): thirteen
    `overload_interface` calls putting `+ - * < <= > >= -- pow abs max min &`
    onto `int`, then `prioritize_int`.  Returns no theorems, only global parser
    side effects, so it has its own once-only flag - exactly the
    `ensureRealAxOverloads` precedent.

    This is an `IO` ACTION, not a memoised `Unit` CAF: `let _ := <caf>` does NOT
    force a Lean CAF, so a CAF here would silently never run
    and every int operator would fail to parse at `:int`.  It forces the `int`
    TYPE first (via `IntTb`, since `prioritize_int` needs `mk_type "int"`), then
    runs `setupIntInterface`.  Every int stage below `await`s this so its
    definition/proof bodies parse `+`/`*`/`<`/... at `:int`. -/
initialize theIntInterface : IO.Ref Bool ← IO.mkRef false

private unsafe def ensureIntInterface : IO Unit := do
  if ← theIntInterface.get then pure () else
    -- Force the `int` type first: `prioritize_int` calls `mk_type "int"`, and
    -- the overloads target the int operation constants.  (Reading a field of
    -- `IntTb` via an IO action forces the type-creation CAF; a bare
    -- `let _ := IntTb` would NOT.)
    let _ ← IO.mkRef (concl IntTb.int_tybij)
    match ← (HolMath.Int.setupIntInterface overload_interface
               prioritize_overload).run with
    | .ok () => theIntInterface.set true
    | .error e => panic! s!"setupIntInterface failed: {e}"

/-- Cache for `IntOps` (int.ml 76-257): the fourteen operation definitions,
    their ten `_th` bridge theorems, `REAL_OF_INT_CLAUSES` and the six
    convenient theorems.  Each `new_definition` CREATES A CONSTANT, so NOT
    idempotent - this once-only CAF guarantees it runs once.  Forces the
    interface overloads first, so `x + y`/`x < y`/... in the definition bodies
    parse at `:int`. -/
initialize theIntOps : IO.Ref (Option HolMath.Int.IntOps) ← IO.mkRef none

private unsafe def IntO : HolMath.Int.IntOps :=
  match unsafeIO (do
    match ← theIntOps.get with
    | some d => pure d
    | none => do
      ensureIntInterface
      match ← (HolMath.Int.setupIntOps Nm Rl CiT RT1 RT2 RT3 RT10
                 Ar1 Ar2 Ar3 Ar4 CnA
                 IntTb.int_rep IntTb.int_abstr IntEx.is_int IntTb.dest_int_rep
                 IntTb.int_eq MESON_TAC REWRITE_CONV REAL_ARITH3
                 new_definition).run with
      | .ok d => do theIntOps.set (some d); pure d
      | .error e => panic! s!"setupIntOps failed: {e}") with
  | .ok d => d | _ => panic! "Session.IntO: setupIntOps not run"

/-- Cache for `IntConstSyntax` (int.ml 279-281): the `int_of_num`/`int_neg`
    term constants `mk_intconst` builds `&n`/`--(&n)` from.  The `int` type must
    already exist; forcing `IntO` (hence the interface and type) precedes it. -/
initialize theIntConstSyntax : IO.Ref (Option HolMath.Int.IntConstSyntax) ← IO.mkRef none

private unsafe def IntKs : HolMath.Int.IntConstSyntax :=
  match unsafeIO (do
    match ← theIntConstSyntax.get with
    | some d => pure d
    | none => do
      -- `int_of_num`/`int_neg` are int constants; force `IntO` so they exist.
      let _ ← IO.mkRef (concl IntO.int_of_num)
      match ← (HolMath.Int.setupIntConstSyntax mk_numeral).run with
      | .ok d => do theIntConstSyntax.set (some d); pure d
      | .error e => panic! s!"setupIntConstSyntax failed: {e}") with
  | .ok d => d | _ => panic! "Session.IntKs: setupIntConstSyntax not run"

/-- `INT_OF_REAL_THM` (int.ml 290): the lifting rule the following int bundles
    build on.  A `thm → IO (Except String thm)` closure that rewrites a
    universal `REAL_` theorem with the sixteen bridge equations under `GSYM` and
    re-quantifies over `:int`.  Cached because building it proves the inline
    `cond_th` lemma once. -/
initialize theIntOfRealThm :
    IO.Ref (Option (thm → IO (Except String thm))) ← IO.mkRef none

unsafe def INT_OF_REAL_THM : thm → IO (Except String thm) := fun th => do
  match ← theIntOfRealThm.get with
  | some f => f th
  | none =>
    match ← (HolMath.Int.setupIntOfRealThm IntTb.int_eq IntO).run with
    | .ok f => do theIntOfRealThm.set (some f); f th
    | .error e => return .error s!"setupIntOfRealThm: {e}"

/- The 276 lifts, in ten bundles (int.ml 322-598).  Each `setupIntThmsN` maps
   `INT_OF_REAL_THM` over a slice of the `REAL_` theorems; forcing any bundle
   forces `INT_OF_REAL_THM` (hence `IntO` and the whole int head) first. -/

/-- Cache for `IntThms1` (int.ml 322-359, the `INT_ABS_*` family). -/
initialize theIntThms1 : IO.Ref (Option HolMath.Int.IntThms1) ← IO.mkRef none

private unsafe def IT1 : HolMath.Int.IntThms1 :=
  match unsafeIO (do
    match ← theIntThms1.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Int.setupIntThms1 INT_OF_REAL_THM
                 REAL_ABS_0 REAL_ABS_1 REAL_ABS_ABS REAL_ABS_BETWEEN
                 REAL_ABS_BETWEEN1 REAL_ABS_BETWEEN2 REAL_ABS_BOUND
                 REAL_ABS_BOUNDS REAL_ABS_CASES REAL_ABS_CIRCLE REAL_ABS_LE
                 REAL_ABS_MUL REAL_ABS_NEG REAL_ABS_NUM REAL_ABS_NZ REAL_ABS_POS
                 REAL_ABS_POW REAL_ABS_REFL REAL_ABS_SGN REAL_ABS_SIGN
                 REAL_ABS_SIGN2 REAL_ABS_STILLNZ REAL_ABS_SUB REAL_ABS_SUB_ABS
                 REAL_ABS_TRIANGLE REAL_ABS_ZERO REAL_ADD2_SUB2 REAL_ADD_AC).run with
      | .ok d => do theIntThms1.set (some d); pure d
      | .error e => panic! s!"setupIntThms1 failed: {e}") with
  | .ok d => d | _ => panic! "Session.IT1: setupIntThms1 not run"

/-- Cache for `IntThms2` (int.ml, the `INT_ADD_*`/`INT_EQ_*` family). -/
initialize theIntThms2 : IO.Ref (Option HolMath.Int.IntThms2) ← IO.mkRef none

private unsafe def IT2 : HolMath.Int.IntThms2 :=
  match unsafeIO (do
    match ← theIntThms2.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Int.setupIntThms2 INT_OF_REAL_THM
                 REAL_ADD_ASSOC REAL_ADD_LDISTRIB REAL_ADD_LID REAL_ADD_LINV
                 REAL_ADD_RDISTRIB REAL_ADD_RID REAL_ADD_RINV REAL_ADD_SUB
                 REAL_ADD_SUB2 REAL_ADD_SYM REAL_BOUNDS_LE REAL_BOUNDS_LT
                 REAL_DIFFSQ REAL_ENTIRE REAL_EQ_ADD_LCANCEL
                 REAL_EQ_ADD_LCANCEL_0 REAL_EQ_ADD_RCANCEL REAL_EQ_ADD_RCANCEL_0
                 REAL_EQ_IMP_LE REAL_EQ_LCANCEL_IMP REAL_EQ_MUL_LCANCEL
                 REAL_EQ_MUL_RCANCEL REAL_EQ_NEG2 REAL_EQ_RCANCEL_IMP
                 REAL_EQ_SGN_ABS REAL_EQ_SQUARE_ABS REAL_EQ_SUB_LADD
                 REAL_EQ_SUB_RADD).run with
      | .ok d => do theIntThms2.set (some d); pure d
      | .error e => panic! s!"setupIntThms2 failed: {e}") with
  | .ok d => d | _ => panic! "Session.IT2: setupIntThms2 not run"

/-- Cache for `IntThms3` (the `INT_LE_*`/`INT_LET_*` family). -/
initialize theIntThms3 : IO.Ref (Option HolMath.Int.IntThms3) ← IO.mkRef none

private unsafe def IT3 : HolMath.Int.IntThms3 :=
  match unsafeIO (do
    match ← theIntThms3.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Int.setupIntThms3 INT_OF_REAL_THM
                 REAL_EVENPOW_ABS REAL_LET_ADD REAL_LET_ADD2 REAL_LET_ANTISYM
                 REAL_LET_TOTAL REAL_LET_TRANS REAL_LE_01 REAL_LE_ADD
                 REAL_LE_ADD2 REAL_LE_ADDL REAL_LE_ADDR REAL_LE_ANTISYM
                 REAL_LE_DOUBLE REAL_LE_LADD REAL_LE_LADD_IMP REAL_LE_LCANCEL_IMP
                 REAL_LE_LMUL REAL_LE_LMUL_EQ REAL_LE_LNEG REAL_LE_LT REAL_LE_MAX
                 REAL_LE_MIN REAL_LE_MUL REAL_LE_MUL2 REAL_LE_MUL_EQ REAL_LE_NEG2
                 REAL_LE_NEGL REAL_LE_NEGR).run with
      | .ok d => do theIntThms3.set (some d); pure d
      | .error e => panic! s!"setupIntThms3 failed: {e}") with
  | .ok d => d | _ => panic! "Session.IT3: setupIntThms3 not run"

/-- Cache for `IntThms4` (the `INT_LE_*`/`INT_LT_ADD*` family). -/
initialize theIntThms4 : IO.Ref (Option HolMath.Int.IntThms4) ← IO.mkRef none

private unsafe def IT4 : HolMath.Int.IntThms4 :=
  match unsafeIO (do
    match ← theIntThms4.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Int.setupIntThms4 INT_OF_REAL_THM
                 REAL_LE_NEGTOTAL REAL_LE_POW2 REAL_LE_POW_2 REAL_LE_RADD
                 REAL_LE_RCANCEL_IMP REAL_LE_REFL REAL_LE_RMUL REAL_LE_RMUL_EQ
                 REAL_LE_RNEG REAL_LE_SQUARE REAL_LE_SQUARE_ABS REAL_LE_SUB_LADD
                 REAL_LE_SUB_RADD REAL_LE_TOTAL REAL_LE_TRANS REAL_LNEG_UNIQ
                 REAL_LTE_ADD REAL_LTE_ADD2 REAL_LTE_ANTISYM REAL_LTE_TOTAL
                 REAL_LTE_TRANS REAL_LT_01 REAL_LT_ADD REAL_LT_ADD1 REAL_LT_ADD2
                 REAL_LT_ADDL REAL_LT_ADDNEG REAL_LT_ADDNEG2).run with
      | .ok d => do theIntThms4.set (some d); pure d
      | .error e => panic! s!"setupIntThms4 failed: {e}") with
  | .ok d => d | _ => panic! "Session.IT4: setupIntThms4 not run"

/-- Cache for `IntThms5` (the `INT_LT_*` family). -/
initialize theIntThms5 : IO.Ref (Option HolMath.Int.IntThms5) ← IO.mkRef none

private unsafe def IT5 : HolMath.Int.IntThms5 :=
  match unsafeIO (do
    match ← theIntThms5.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Int.setupIntThms5 INT_OF_REAL_THM
                 REAL_LT_ADDR REAL_LT_ADD_SUB REAL_LT_ANTISYM REAL_LT_GT
                 REAL_LT_IMP_LE REAL_LT_IMP_NE REAL_LT_LADD REAL_LT_LADD_IMP
                 REAL_LT_LCANCEL_IMP REAL_LT_LE REAL_LT_LMUL REAL_LT_LMUL_EQ
                 REAL_LT_LNEG REAL_LT_MAX REAL_LT_MIN REAL_LT_MUL REAL_LT_MUL2
                 REAL_LT_MUL_EQ REAL_LT_NEG2 REAL_LT_NEGTOTAL REAL_LT_POW2
                 REAL_LT_POW_2 REAL_LT_RADD REAL_LT_RCANCEL_IMP REAL_LT_REFL
                 REAL_LT_RMUL REAL_LT_RMUL_EQ REAL_LT_RNEG).run with
      | .ok d => do theIntThms5.set (some d); pure d
      | .error e => panic! s!"setupIntThms5 failed: {e}") with
  | .ok d => d | _ => panic! "Session.IT5: setupIntThms5 not run"

/-- Cache for `IntThms6` (the `INT_MAX_*`/`INT_MIN_*`/`INT_MUL_*` family). -/
initialize theIntThms6 : IO.Ref (Option HolMath.Int.IntThms6) ← IO.mkRef none

private unsafe def IT6 : HolMath.Int.IntThms6 :=
  match unsafeIO (do
    match ← theIntThms6.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Int.setupIntThms6 INT_OF_REAL_THM
                 REAL_LT_SQUARE REAL_LT_SQUARE_ABS REAL_LT_SUB_LADD
                 REAL_LT_SUB_RADD REAL_LT_TOTAL REAL_LT_TRANS REAL_MAX_ACI
                 REAL_MAX_ASSOC REAL_MAX_LE REAL_MAX_LT REAL_MAX_MAX REAL_MAX_MIN
                 REAL_MAX_SYM REAL_MIN_ACI REAL_MIN_ASSOC REAL_MIN_LE REAL_MIN_LT
                 REAL_MIN_MAX REAL_MIN_MIN REAL_MIN_SYM REAL_MUL_2 REAL_MUL_AC
                 REAL_MUL_ASSOC REAL_MUL_LID REAL_MUL_LNEG REAL_MUL_LZERO
                 REAL_MUL_POS_LE REAL_MUL_POS_LT).run with
      | .ok d => do theIntThms6.set (some d); pure d
      | .error e => panic! s!"setupIntThms6 failed: {e}") with
  | .ok d => d | _ => panic! "Session.IT6: setupIntThms6 not run"

/-- Cache for `IntThms7` (the `INT_MUL_R*`/`INT_NEG_*`/`INT_OF_NUM_*` family). -/
initialize theIntThms7 : IO.Ref (Option HolMath.Int.IntThms7) ← IO.mkRef none

private unsafe def IT7 : HolMath.Int.IntThms7 :=
  match unsafeIO (do
    match ← theIntThms7.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Int.setupIntThms7 INT_OF_REAL_THM
                 REAL_MUL_RID REAL_MUL_RNEG REAL_MUL_RZERO REAL_MUL_SYM
                 REAL_NEG_0 REAL_NEG_ADD REAL_NEG_EQ REAL_NEG_EQ_0 REAL_NEG_GE0
                 REAL_NEG_GT0 REAL_NEG_LE0 REAL_NEG_LMUL REAL_NEG_LT0
                 REAL_NEG_MINUS1 REAL_NEG_MUL2 REAL_NEG_NEG REAL_NEG_RMUL
                 REAL_NEG_SUB REAL_NOT_EQ REAL_NOT_LE REAL_NOT_LT REAL_OF_NUM_ADD
                 REAL_OF_NUM_CLAUSES REAL_OF_NUM_EQ REAL_OF_NUM_GE REAL_OF_NUM_GT
                 REAL_OF_NUM_LE REAL_OF_NUM_LT).run with
      | .ok d => do theIntThms7.set (some d); pure d
      | .error e => panic! s!"setupIntThms7 failed: {e}") with
  | .ok d => d | _ => panic! "Session.IT7: setupIntThms7 not run"

/-- Cache for `IntThms8` (the `INT_OF_NUM_*`/`INT_POS`/`INT_POW_*` family). -/
initialize theIntThms8 : IO.Ref (Option HolMath.Int.IntThms8) ← IO.mkRef none

private unsafe def IT8 : HolMath.Int.IntThms8 :=
  match unsafeIO (do
    match ← theIntThms8.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Int.setupIntThms8 INT_OF_REAL_THM
                 REAL_OF_NUM_MAX REAL_OF_NUM_MIN REAL_OF_NUM_MOD REAL_OF_NUM_MUL
                 REAL_OF_NUM_POW REAL_OF_NUM_SUB REAL_OF_NUM_SUB_CASES
                 REAL_OF_NUM_SUC REAL_POS REAL_POS_EQ_SQUARE REAL_LT_IMP_NZ
                 REAL_POW2_ABS REAL_POW_1 REAL_POW_1_LE REAL_POW_1_LT REAL_POW_2
                 REAL_POW_ADD REAL_POW_EQ REAL_POW_EQ_0 REAL_POW_EQ_1
                 REAL_POW_EQ_1_IMP REAL_POW_EQ_ABS REAL_POW_EQ_EQ REAL_POW_EQ_ODD
                 REAL_POW_EQ_ODD_EQ REAL_POW_LBOUND REAL_POW_LE REAL_POW_LE2).run with
      | .ok d => do theIntThms8.set (some d); pure d
      | .error e => panic! s!"setupIntThms8 failed: {e}") with
  | .ok d => d | _ => panic! "Session.IT8: setupIntThms8 not run"

/-- Cache for `IntThms9` (the `INT_POW_*`/`INT_SGN_*` family). -/
initialize theIntThms9 : IO.Ref (Option HolMath.Int.IntThms9) ← IO.mkRef none

private unsafe def IT9 : HolMath.Int.IntThms9 :=
  match unsafeIO (do
    match ← theIntThms9.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Int.setupIntThms9 INT_OF_REAL_THM
                 REAL_POW_LE2_ODD REAL_POW_LE2_ODD_EQ REAL_POW_LE2_REV
                 REAL_POW_LE_1 REAL_POW_LT REAL_POW_LT2 REAL_POW_LT2_ODD
                 REAL_POW_LT2_ODD_EQ REAL_POW_LT2_REV REAL_POW_LT_1 REAL_POW_MONO
                 REAL_POW_MONO_LT REAL_POW_MUL REAL_POW_NEG REAL_POW_NZ
                 REAL_POW_ONE REAL_POW_POW REAL_POW_ZERO REAL_RNEG_UNIQ real_sgn
                 REAL_SGNS_EQ REAL_SGNS_EQ_ALT REAL_SGN_0 REAL_SGN_ABS
                 REAL_SGN_ABS_ALT REAL_SGN_CASES).run with
      | .ok d => do theIntThms9.set (some d); pure d
      | .error e => panic! s!"setupIntThms9 failed: {e}") with
  | .ok d => d | _ => panic! "Session.IT9: setupIntThms9 not run"

/-- Cache for `IntThms10` (the `INT_SGN_*`/`INT_SUB_*` family). -/
initialize theIntThms10 : IO.Ref (Option HolMath.Int.IntThms10) ← IO.mkRef none

private unsafe def IT10 : HolMath.Int.IntThms10 :=
  match unsafeIO (do
    match ← theIntThms10.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Int.setupIntThms10 INT_OF_REAL_THM
                 REAL_SGN_EQ REAL_SGN_EQ_INEQ REAL_SGN_INEQS REAL_SGN_REAL_SGN
                 REAL_SGN_MUL REAL_SGN_NEG REAL_SGN_POW REAL_SGN_POW_2
                 REAL_SOS_EQ_0 REAL_SUB_0 REAL_SUB_ABS REAL_SUB_ADD REAL_SUB_ADD2
                 REAL_SUB_LDISTRIB REAL_SUB_LE REAL_SUB_LNEG REAL_SUB_LT
                 REAL_SUB_LZERO REAL_SUB_NEG2 REAL_SUB_RDISTRIB REAL_SUB_REFL
                 REAL_SUB_RNEG REAL_SUB_RZERO REAL_SUB_SUB REAL_SUB_SUB2
                 REAL_SUB_TRIANGLE).run with
      | .ok d => do theIntThms10.set (some d); pure d
      | .error e => panic! s!"setupIntThms10 failed: {e}") with
  | .ok d => d | _ => panic! "Session.IT10: setupIntThms10 not run"

/-- Cache for `IntWlog` (int.ml 603-616): the three integer WLOG theorems. -/
initialize theIntWlog : IO.Ref (Option HolMath.Int.IntWlog) ← IO.mkRef none

private unsafe def IWl : HolMath.Int.IntWlog :=
  match unsafeIO (do
    match ← theIntWlog.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Int.setupIntWlog IT4.INT_LE_TOTAL IT6.INT_LT_TOTAL
                 MESON_TAC).run with
      | .ok d => do theIntWlog.set (some d); pure d
      | .error e => panic! s!"setupIntWlog failed: {e}") with
  | .ok d => d | _ => panic! "Session.IWl: setupIntWlog not run"

/-- Cache for `IntArith1` (int.ml 619-709): the image theorems, pseudo-
    definitions and the BOOTSTRAPPING integer decision procedure `INT_ARITH1`
    / `INT_ARITH_TAC1` / `ASM_INT_ARITH_TAC1`.  The FIRST of two `INT_ARITH`
    definitions (the second, handling `div`/`rem`, arrives in a later stage). -/
initialize theIntArith1 : IO.Ref (Option HolMath.Int.IntArith1) ← IO.mkRef none

private unsafe def IA1 : HolMath.Int.IntArith1 :=
  match unsafeIO (do
    match ← theIntArith1.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Int.setupIntArith1 nnfPths IntO IntTb.int_eq
                 INT_OF_REAL_THM Rl Ar2
                 IT2.INT_ADD_LID IT4.INT_LE_RNEG
                 IT7.INT_OF_NUM_LE IT7.INT_NEG_0 IT7.INT_NOT_LE IT7.INT_NOT_LT
                 IT7.INT_NOT_EQ IT1.INT_ABS_POS IT1.INT_ABS_REFL
                 PRESIMP_CONV NNF_CONV CONDS_ELIM_CONV REAL_ARITH3
                 MESON_TAC).run with
      | .ok d => do theIntArith1.set (some d); pure d
      | .error e => panic! s!"setupIntArith1 failed: {e}") with
  | .ok d => d | _ => panic! "Session.IA1: setupIntArith1 not run"

/-- Guard for the `div`/`rem` infixes (int.ml 712): `parse_as_infix` for both.
    An `IO` action with its own once-only flag (a `Unit` CAF would not force).
    `setupIntDivMod` awaits this so its `div`/`rem` terms
    parse as infixes. -/
initialize theIntDivRemInfixes : IO.Ref Bool ← IO.mkRef false

private def ensureIntDivRemInfixes : IO Unit := do
  if ← theIntDivRemInfixes.get then pure () else do
    HolMath.Int.setupIntDivRemInfixes
    theIntDivRemInfixes.set true

/-- Cache for `IntDivMod` (int.ml 714-866): `INT_SUB`/`INT_MAX`/`INT_MIN`, the
    Euclidean division/remainder specification `INT_DIVISION` and its family.
    Uses `new_specification` (which CREATES the `div`/`rem` constants), so NOT
    idempotent - this once-only CAF guarantees it runs once.  Forces the
    `div`/`rem` infixes first. -/
initialize theIntDivMod : IO.Ref (Option HolMath.Int.IntDivMod) ← IO.mkRef none

private unsafe def IDm : HolMath.Int.IntDivMod :=
  match unsafeIO (do
    match ← theIntDivMod.get with
    | some d => pure d
    | none => do
      ensureIntDivRemInfixes
      match ← (HolMath.Int.setupIntDivMod IA1 IntO
                 IT8.INT_POS IT8.INT_OF_NUM_MUL
                 IT4.INT_LE_TRANS IT4.INT_LE_REFL IT4.INT_LE_TOTAL
                 IT6.INT_MUL_LNEG
                 IT7.INT_MUL_RNEG IT7.INT_NEG_NEG IT7.INT_OF_NUM_EQ IT7.INT_NEG_EQ
                 IT7.INT_OF_NUM_LE
                 IT1.INT_ABS_POS IT1.INT_ABS_MUL
                 IT2.INT_ADD_LID
                 IT3.INT_LE_LMUL IT3.INT_LET_TRANS
                 IT5.INT_LT_REFL
                 MULT_EQ_1 LE_REFL NOT_LE num_WOP
                 new_specification MESON MESON_TAC ASM_MESON_TAC).run with
      | .ok d => do theIntDivMod.set (some d); pure d
      | .error e => panic! s!"setupIntDivMod failed: {e}") with
  | .ok d => d | _ => panic! "Session.IDm: setupIntDivMod not run"

/-- Cache for `IntCompareConvs` (int.ml 871-940): the five relational numeral
    conversions `INT_LE_CONV`/`INT_LT_CONV`/`INT_GE_CONV`/`INT_GT_CONV`/
    `INT_EQ_CONV`. -/
initialize theIntCompareConvs : IO.Ref (Option HolMath.Int.IntCompareConvs) ← IO.mkRef none

private unsafe def ICv : HolMath.Int.IntCompareConvs :=
  match unsafeIO (do
    match ← theIntCompareConvs.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Int.setupIntCompareConvs
                 NUM_EQ_CONV NUM_LE_CONV NUM_LT_CONV IA1
                 IT3.INT_LE_NEG2 IT3.INT_LE_LNEG IT4.INT_LE_RNEG
                 IT7.INT_OF_NUM_ADD IT7.INT_OF_NUM_LE IT3.INT_LE_ANTISYM
                 LE LE_0 ADD_EQ_0 NOT_LE LE_ANTISYM).run with
      | .ok d => do theIntCompareConvs.set (some d); pure d
      | .error e => panic! s!"setupIntCompareConvs failed: {e}") with
  | .ok d => d | _ => panic! "Session.ICv: setupIntCompareConvs not run"

/-- Cache for `IntArithConvs` (int.ml 941-1084): the nine arithmetic numeral
    conversions `INT_NEG_CONV`/`INT_MUL_CONV`/`INT_ADD_CONV`/`INT_SUB_CONV`/
    `INT_POW_CONV`/`INT_ABS_CONV`/`INT_MAX_CONV`/`INT_MIN_CONV`/`INT_SGN_CONV`.
    `NUM_EVEN_CONV` is a FACTORY here (`IO (Except String ioconv)`), so unwrap
    it first (as calc_int's `CiW` does). -/
initialize theIntArithConvs : IO.Ref (Option HolMath.Int.IntArithConvs) ← IO.mkRef none

private unsafe def IAv : HolMath.Int.IntArithConvs :=
  match unsafeIO (do
    match ← theIntArithConvs.get with
    | some d => pure d
    | none => do
      let evenC : ioconv := NUM_EVEN_CONV
      match ← (HolMath.Int.setupIntArithConvs ICv
                 NUM_MULT_CONV NUM_ADD_CONV NUM_EXP_CONV evenC mk_numeral
                 IT7.INT_NEG_NEG IT7.INT_NEG_0
                 IT6.INT_MUL_LZERO IT7.INT_MUL_RZERO IT6.INT_MUL_LNEG
                 IT7.INT_MUL_RNEG
                 IT2.INT_ADD_LINV IT2.INT_ADD_RINV IT7.INT_NEG_ADD IT2.INT_ADD_LID
                 IT2.INT_ADD_ASSOC IT2.INT_ADD_SYM
                 IT8.INT_OF_NUM_MUL IT7.INT_OF_NUM_ADD IT8.INT_OF_NUM_POW
                 IT9.INT_POW_NEG
                 IT1.INT_ABS_NEG IT1.INT_ABS_NUM
                 IDm.INT_SUB IDm.INT_MAX IDm.INT_MIN IT9.INT_SGN).run with
      | .ok d => do theIntArithConvs.set (some d); pure d
      | .error e => panic! s!"setupIntArithConvs failed: {e}") with
  | .ok d => d | _ => panic! "Session.IAv: setupIntArithConvs not run"

/-- Cache for `IntPolyConvs` (int.ml 1091-1120): `INT_POLY_CONV`, the canonical
    polynomial normalizer for the integers, built from the ten-axiom semiring
    `sth` and the negation/subtraction `rth`. -/
initialize theIntPolyConvs : IO.Ref (Option HolMath.Int.IntPolyConvs) ← IO.mkRef none

private unsafe def IPc : HolMath.Int.IntPolyConvs :=
  match unsafeIO (do
    match ← theIntPolyConvs.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Int.setupIntPolyConvs IA1 IAv
                 TRUTH NmzP.2 num_CONV
                 NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV).run with
      | .ok d => do theIntPolyConvs.set (some d); pure d
      | .error e => panic! s!"setupIntPolyConvs failed: {e}") with
  | .ok d => d | _ => panic! "Session.IPc: setupIntPolyConvs not run"

/-- Cache for `IntRingConvs` (int.ml 1122-1147): `INT_RING`,
    `int_ideal_cofactors` and `INT_INTEGRAL`. -/
initialize theIntRingConvs : IO.Ref (Option HolMath.Int.IntRingConvs) ← IO.mkRef none

private unsafe def IRg : HolMath.Int.IntRingConvs :=
  match unsafeIO (do
    match ← theIntRingConvs.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Int.setupIntRing IntKs ICv IA1 IPc Nm.numK
                 MULT_CLAUSES EQ_ADD_LCANCEL
                 IT7.INT_OF_NUM_EQ IT7.INT_OF_NUM_ADD IT8.INT_OF_NUM_MUL
                 IT10.INT_SUB_0 IT2.INT_ENTIRE
                 PRESIMP_CONV CONDS_ELIM_CONV NNF_CONV WEAK_DNF_CONV
                 AND_FORALL_THM LEFT_AND_FORALL_THM RIGHT_AND_FORALL_THM
                 LEFT_OR_FORALL_THM RIGHT_OR_FORALL_THM OR_EXISTS_THM
                 LEFT_OR_EXISTS_THM RIGHT_OR_EXISTS_THM LEFT_AND_EXISTS_THM
                 RIGHT_AND_EXISTS_THM
                 GrG TRUTH).run with
      | .ok d => do theIntRingConvs.set (some d); pure d
      | .error e => panic! s!"setupIntRing failed: {e}") with
  | .ok d => d | _ => panic! "Session.IRg: setupIntRing not run"

/-- Guard for the divisibility/congruence/coprimality block (int.ml 1148-1223).
    It threads in `make_overloadable`/`parse_as_infix`/`parse_as_prefix`/
    `overload_interface`/`new_definition` and runs them in int.ml's EXACT order,
    including the three `overload_interface` calls that MUST PRECEDE the
    `new_definition` they refer to (1180 before 1182, 1197 before 1199, 1216
    before 1218) so `divides`/`mod`/`coprime` parse as CONSTANTS not variables.
    CREATES constants (`cong`/`real_mod`/`int_divides`/`int_mod`/`int_coprime`),
    so this once-only CAF guarantees it runs exactly once.  Forces `IA1` and the
    interface first (so `integer` and the int operators are in scope).
    `int_coprime`'s LHS `coprime(a,b)` is a PAIRED varstruct, which pair.ml's
    `new_definition` handles. -/
initialize theIntDivisibility : IO.Ref (Option HolMath.Int.IntDivisibility) ← IO.mkRef none

private unsafe def IDv : HolMath.Int.IntDivisibility :=
  match unsafeIO (do
    match ← theIntDivisibility.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Int.setupIntDivisibility IA1
                 IT1.INT_ABS_MUL IT2.INT_ENTIRE IT3.INT_LE_MUL
                 make_overloadable overload_interface parse_as_infix
                 parse_as_prefix new_definition_pair).run with
      | .ok d => do theIntDivisibility.set (some d); pure d
      | .error e => panic! s!"setupIntDivisibility failed: {e}") with
  | .ok d => d | _ => panic! "Session.IDv: setupIntDivisibility not run"

/- `INTEGER_TAC1`/`INTEGER_RULE1` (int.ml 1224-1327), the FIRST of the two     -/
/- integer decision procedures.  Pure (proves no new constant); memoised so    -/
/- its internal `INT_ARITH`/`MESON` lemmas are proved once.  Depends on IA1,    -/
/- IPc, IRg, IDv and the `INT_SUB_0`/`INT_ENTIRE` lifts.                        -/
initialize theIntTac1 : IO.Ref (Option HolMath.Int.IntTac1) ← IO.mkRef none

private unsafe def ITc1 : HolMath.Int.IntTac1 :=
  match unsafeIO (do
    match ← theIntTac1.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Int.setupIntTac1 IA1 IPc IRg IDv
                 IT10.INT_SUB_0 IT2.INT_ENTIRE MESON).run with
      | .ok d => do theIntTac1.set (some d); pure d
      | .error e => panic! s!"setupIntTac1 failed: {e}") with
  | .ok d => d | _ => panic! "Session.ITc1: setupIntTac1 not run"

/- The 47 further div/rem/congruence proofs (int.ml 1329-1763).  Pure; forces  -/
/- IA1, IDm, IRg, IDv, ITc1 and the ten lift bundles first.                     -/
initialize theIntDivRem1 : IO.Ref (Option HolMath.Int.IntDivRem1) ← IO.mkRef none

private unsafe def IDr1 : HolMath.Int.IntDivRem1 :=
  match unsafeIO (do
    match ← theIntDivRem1.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Int.setupIntDivRem1 Nm IntO IA1 IDm IRg IDv ITc1
                 IT1 IT2 IT3 IT4 IT5 IT6 IT7 IT8 IT9 IT10
                 Ar7.DIVISION Ar7.DIV_ZERO Ar7.MOD_ZERO Ar8.MOD_LE Ar3.LE_1
                 Ar7.RDIV_LT_EQ MESON_TAC ASM_MESON_TAC).run with
      | .ok d => do theIntDivRem1.set (some d); pure d
      | .error e => panic! s!"setupIntDivRem1 failed: {e}") with
  | .ok d => d | _ => panic! "Session.IDr1: setupIntDivRem1 not run"

/-- Cache for `IntDivRemConvs` (int.ml 1772-1801): `INT_DIV_CONV`/`INT_REM_CONV`,
    the numeral div/rem evaluators cut from the shared `INT_DIVMOD_CONV`. -/
initialize theIntDivRemConvs : IO.Ref (Option HolMath.Int.IntDivRemConvs) ← IO.mkRef none

private unsafe def IDrc : HolMath.Int.IntDivRemConvs :=
  match unsafeIO (do
    match ← theIntDivRemConvs.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Int.setupIntDivRemConvs IntKs ICv IAv IDr1 MESON_TAC).run with
      | .ok d => do theIntDivRemConvs.set (some d); pure d
      | .error e => panic! s!"setupIntDivRemConvs failed: {e}") with
  | .ok d => d | _ => panic! "Session.IDrc: setupIntDivRemConvs not run"

/-- Cache for `INT_RED_CONV` (int.ml 1821).  Memoised because the OCaml
    SNAPSHOTS `basic_net()` once when the conversion is defined; building the
    net afresh on every call would not reproduce that. -/
initialize theIntRed : IO.Ref (Option ioconv) ← IO.mkRef none

/-- Cache for `int_red_conv_list` (int.ml 1803). -/
initialize theIntRedConvList : IO.Ref (Option (List (term × ioconv))) ← IO.mkRef none

/-- `int_red_conv_list` (int.ml 1803): a top-level value in OCaml, so its
    sixteen patterns are parsed once, under `prioritize_int`. -/
unsafe def int_red_conv_list : IO (Except String (List (term × ioconv))) := do
  match ← theIntRedConvList.get with
  | some l => return .ok l
  | none =>
    match ← (HolMath.Int.int_red_conv_list ICv IAv IDrc).run with
    | .ok l => do theIntRedConvList.set (some l); return .ok l
    | .error e => return .error e

/-- `INT_RED_CONV` (int.ml 1821): one reduction step on an integer-constant
    term, via the sixteen-entry net over `basic_net()`. -/
unsafe def INT_RED_CONV : ioconv := fun tm => do
  match ← theIntRed.get with
  | some c => c tm
  | none =>
    match ← (do HolMath.Int.INT_RED_CONV (← ExceptT.mk int_red_conv_list)).run with
    | .ok c => do theIntRed.set (some c); c tm
    | .error e => return .error s!"INT_RED_CONV: {e}"

/-- `INT_REDUCE_CONV` (int.ml 1826): `DEPTH_CONV INT_RED_CONV`. -/
unsafe def INT_REDUCE_CONV : ioconv := Simp.depthConvIO INT_RED_CONV

/-- `int_compute_add_convs` (int.ml 1828): register the sixteen conversions
    with a `compset`. -/
unsafe def int_compute_add_convs (cs : HolMath.Compute.compset) :
    IO (Except String Unit) :=
  (do HolMath.Int.int_compute_add_convs (← ExceptT.mk int_red_conv_list) cs).run

/-- Build `INT_COMPUTE_CONV` from the shared `int_red_conv_list`. -/
private unsafe def intComputeConvIO : ExceptT String IO ioconv := do
  let l ← ExceptT.mk int_red_conv_list
  HolMath.Int.INT_COMPUTE_CONV l bool_compset WEAK_CBV_CONV

/-- Cache for `INT_COMPUTE_CONV` (int.ml 1835): call-by-value reduction over the
    boolean compset extended with those conversions.  The OCaml builds its
    compset once, so memoise. -/
initialize theIntCompute : IO.Ref (Option ioconv) ← IO.mkRef none

/-- `INT_COMPUTE_CONV` (int.ml 1835). -/
unsafe def INT_COMPUTE_CONV : ioconv := fun tm => do
  match ← theIntCompute.get with
  | some c => c tm
  | none =>
    match ← (intComputeConvIO).run with
    | .ok c => do theIntCompute.set (some c); c tm
    | .error e => return .error s!"INT_COMPUTE_CONV: {e}"

/-- Cache for `IntEvenOdd` (int.ml 1844-1877): the four `&2 divides`
    combining theorems `INT_2_DIVIDES_ADD`/`_SUB`/`_MUL`/`_POW`. -/
initialize theIntEvenOdd : IO.Ref (Option HolMath.Int.IntEvenOdd) ← IO.mkRef none

private unsafe def IEo : HolMath.Int.IntEvenOdd :=
  match unsafeIO (do
    match ← theIntEvenOdd.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Int.setupIntEvenOdd Nm INT_REDUCE_CONV
                 IDr1 IA1.INT_POW Nm.NOT_SUC).run with
      | .ok d => do theIntEvenOdd.set (some d); pure d
      | .error e => panic! s!"setupIntEvenOdd failed: {e}") with
  | .ok d => d | _ => panic! "Session.IEo: setupIntEvenOdd not run"

/-- Cache for `IntRemConvs` (int.ml 1880-1928): `INT_REM_DOWN_CONV` (combine
    nested `rem`s) and `INT_POW_REM_CONV` (reduce `(a pow k) rem n`). -/
initialize theIntRemConvs : IO.Ref (Option HolMath.Int.IntRemConvs) ← IO.mkRef none

private unsafe def IRc : HolMath.Int.IntRemConvs :=
  match unsafeIO (do
    match ← theIntRemConvs.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Int.setupIntRemConvs IDr1 IDrc IAv
                 IT9.INT_POW_NEG IT7.INT_OF_NUM_CLAUSES C.COND_CLAUSES
                 numEvenConvIO EXP_MOD_CONV).run with
      | .ok d => do theIntRemConvs.set (some d); pure d
      | .error e => panic! s!"setupIntRemConvs failed: {e}") with
  | .ok d => d | _ => panic! "Session.IRc: setupIntRemConvs not run"


/-- Cache for `IntGcdLcm` (int.ml 1929-2067): the two well-founded integer
    measures, the Bezout existence theorems, the `int_gcd`/`int_lcm` constants
    and their lcm lemmas, and the SECOND `INTEGER_TAC`/`INTEGER_RULE`.  Uses
    `new_specification` (which CREATES `int_gcd`) and `new_definition` (which
    CREATES `int_lcm`), plus two `overload_interface` calls, so NOT idempotent -
    this once-only CAF guarantees it runs once. -/
initialize theIntGcdLcm : IO.Ref (Option HolMath.Int.IntGcdLcm) ← IO.mkRef none

private unsafe def IGl : HolMath.Int.IntGcdLcm :=
  match unsafeIO (do
    match ← theIntGcdLcm.get with
    | some d => pure d
    | none => do
      match ← (HolMath.Int.setupIntGcdLcm
                 Pr.FORALL_PAIR_THM Pr.FORALL_UNCURRY IA1 ITc1 IDr1
                 num_WF IT7.INT_OF_NUM_LT IA1.INT_FORALL_POS
                 IT6.INT_MUL_LZERO IT2.INT_ADD_LID IT2.INT_ADD_RID IT7.INT_MUL_RID
                 IT4.INT_LE_NEGTOTAL
                 IA1.INT_ABS IT8.INT_POS IT1.INT_ABS_POS IT1.INT_ABS_NUM
                 IT1.INT_ABS_ZERO
                 IT7.INT_MUL_RZERO IT7.INT_MUL_SYM
                 Pr.EXISTS_UNCURRY C.SKOLEM_THM
                 MESON_TAC ASM_MESON_TAC
                 overload_interface new_specification new_definition_pair).run with
      | .ok d => do theIntGcdLcm.set (some d); pure d
      | .error e => panic! s!"setupIntGcdLcm failed: {e}") with
  | .ok d => d | _ => panic! "Session.IGl: setupIntGcdLcm not run"

/-- Cache for `IntNumOfInt` (int.ml 2070-2104): the map back from a nonnegative
    integer to the natural it names.  `new_definition` CREATES `num_of_int`, so
    this once-only CAF guarantees it runs exactly once. -/
initialize theIntNumOfInt : IO.Ref (Option HolMath.Int.IntNumOfInt) ← IO.mkRef none

private unsafe def INoI : HolMath.Int.IntNumOfInt :=
  match unsafeIO (do
    match ← theIntNumOfInt.get with
    | some d => pure d
    | none => do
      match ← (HolMath.Int.setupIntNumOfInt
                 IT7.INT_OF_NUM_EQ IT7.INT_OF_NUM_ADD IT8.INT_OF_NUM_MUL
                 IT8.INT_OF_NUM_POW IA1.INT_FORALL_POS IT8.INT_POS
                 T.RIGHT_FORALL_IMP_THM T.IMP_CONJ T.SWAP_FORALL_THM
                 SELECT_CONV MESON_TAC new_definition).run with
      | .ok d => do theIntNumOfInt.set (some d); pure d
      | .error e => panic! s!"setupIntNumOfInt failed: {e}") with
  | .ok d => d | _ => panic! "Session.INoI: setupIntNumOfInt not run"

/-- Cache for `IntNumNotions` (int.ml 2107-2149): the natural-number
    divisibility notions and `NUM_TO_INT_CONV`.  Runs FIVE `overload_interface`
    calls (registering `divides`/`mod`/`coprime`/`gcd`/`lcm` for `num`) BEFORE
    six definitions, so NOT idempotent - this once-only CAF guarantees it runs
    once.  Forces `INoI` first, so `num_of_int` is a registered constant when
    `num_gcd`/`num_lcm` are parsed.  `num_coprime`/`num_gcd`/`num_lcm` have
    PAIRED left-hand sides, which pair.ml's `new_definition` handles. -/
initialize theIntNumNotions : IO.Ref (Option HolMath.Int.IntNumNotions) ← IO.mkRef none

private unsafe def INoN : HolMath.Int.IntNumNotions :=
  match unsafeIO (do
    -- Force `num_of_int` (from `INoI`) to EXIST before `setupIntNumNotions`
    -- parses `num_gcd`/`num_lcm`, whose statements mention it.  A `let _ := INoI`
    -- would NOT force a Lean CAF, leaving `num_of_int` a free
    -- VARIABLE and `new_definition` failing with `term not closed: num_of_int`;
    -- read a field through `IO.mkRef` to actually force it.
    let _ ← IO.mkRef (concl INoI.num_of_int)
    match ← theIntNumNotions.get with
    | some d => pure d
    | none => do
      match ← (HolMath.Int.setupIntNumNotions IDv.cong
                 IA1.INT_EXISTS_POS IA1.INT_FORALL_POS
                 IT7.INT_OF_NUM_EQ IT7.INT_OF_NUM_LE IT7.INT_OF_NUM_LT
                 IT7.INT_OF_NUM_GE IT7.INT_OF_NUM_GT IT8.INT_OF_NUM_SUC
                 IT7.INT_OF_NUM_ADD IT8.INT_OF_NUM_MUL IT8.INT_OF_NUM_POW
                 NUM_SIMPLIFY_CONV MESON_TAC
                 overload_interface new_definition_pair).run with
      | .ok d => do theIntNumNotions.set (some d); pure d
      | .error e => panic! s!"setupIntNumNotions failed: {e}") with
  | .ok d => d | _ => panic! "Session.INoN: setupIntNumNotions not run"

/-- Cache for `IntArithRule` (int.ml 2153-2189): `ARITH_RULE`/`ARITH_TAC`/
    `ASM_ARITH_TAC`, the linear decision procedure for the naturals, delegating
    to `IA1.INT_ARITH1` (the enhanced `INT_ARITH2` is not yet defined here).
    Pure (no principle-of-definition side effects); cached for reuse. -/
initialize theIntArithRule : IO.Ref (Option HolMath.Int.IntArithRule) ← IO.mkRef none

private unsafe def IAr : HolMath.Int.IntArithRule :=
  match unsafeIO (do
    match ← theIntArithRule.get with
    | some d => pure d
    | none => do
      match ← (HolMath.Int.setupIntArithRule IA1.INT_ARITH1 IT8.INT_POS
                 IT7.INT_OF_NUM_EQ IT7.INT_OF_NUM_LE IT7.INT_OF_NUM_LT
                 IT7.INT_OF_NUM_GE IT7.INT_OF_NUM_GT IT7.INT_OF_NUM_ADD
                 IT8.INT_OF_NUM_MUL IT8.INT_OF_NUM_MAX IT8.INT_OF_NUM_MIN
                 Ar1.ADD1 NUM_SIMPLIFY_CONV NUM_NORMALIZE_CONV PRENEX_CONV).run with
      | .ok d => do theIntArithRule.set (some d); pure d
      | .error e => panic! s!"setupIntArithRule failed: {e}") with
  | .ok d => d | _ => panic! "Session.IAr: setupIntArithRule not run"

/-- Cache for `IntArith2` (int.ml 2192-2323): the ENHANCED integer decision
    procedure `INT_ARITH2`/`INT_ARITH_TAC2`/`ASM_INT_ARITH_TAC2`.  It is
    `INT_ARITH1` (int.ml 674) with an extra `INT_REDUCE_CONV THENC
    INT_DIVREM_ELIM_CONV` link in its `init_CONV`, so it can eliminate
    `div`/`rem` (which `INT_ARITH1` cannot) - it SUPERSEDES `INT_ARITH1`.  Pure
    (no principle-of-definition side effects); cached for reuse.  `IA1`'s own
    `INT_ARITH1` is NOT called - the enhanced version is built afresh. -/
initialize theIntArith2 : IO.Ref (Option HolMath.Int.IntArith2) ← IO.mkRef none

private unsafe def IA2 : HolMath.Int.IntArith2 :=
  match unsafeIO (do
    match ← theIntArith2.get with
    | some d => pure d
    | none => do
      match ← (HolMath.Int.setupIntArith2 nnfPths IA1 IntO IntTb.int_eq
                 IT7.INT_NOT_LE IT7.INT_NOT_LT IT7.INT_NOT_EQ
                 IT8.INT_POS IT3.INT_LE_ADD IT3.INT_LE_MUL IT8.INT_POW_LE
                 IT1.INT_ABS_NUM IT3.INT_LET_ANTISYM IDm.INT_DIV_0 IDm.INT_REM_0
                 IDm.INT_DIVISION IDr1.INT_LE_DIV IDr1.INT_DIVMOD_UNIQ
                 PRESIMP_CONV NNF_CONV CONDS_ELIM_CONV INT_REDUCE_CONV
                 REAL_ARITH3 ASM_METIS_TAC).run with
      | .ok d => do theIntArith2.set (some d); pure d
      | .error e => panic! s!"setupIntArith2 failed: {e}") with
  | .ok d => d | _ => panic! "Session.IA2: setupIntArith2 not run"

/-- Cache for `IntMiscNat` (int.ml 2326-2375): four miscellaneous `num`
    lemmas (`BINARY_INDUCT`/`NUM_CASES_BINARY`/`num_WF_DOWN`/
    `INT_REM_REM_POW_MIN`).  `INT_REM_REM_POW_MIN`'s final `ASM_INT_ARITH_TAC`
    is the ENHANCED `ASM_INT_ARITH_TAC2`, so this forces `IA2` first.  Pure;
    cached for reuse. -/
initialize theIntMiscNat : IO.Ref (Option HolMath.Int.IntMiscNat) ← IO.mkRef none

private unsafe def IMn : HolMath.Int.IntMiscNat :=
  match unsafeIO (do
    match ← theIntMiscNat.get with
    | some d => pure d
    | none => do
      match ← (HolMath.Int.setupIntMiscNat IAr IA2
                 Ar4.num_WF Ar2.LE_0 Ar4.LE_EXISTS Ar3.NOT_LE Ar3.LT_IMP_LE
                 IDr1.INT_REM_ZERO IT9.INT_POW_ZERO IDm.INT_REM_0 IDr1.INT_REM_1
                 IT8.INT_POW_ADD IDr1.INT_REM_REM_MUL IDr1.INT_REM_REM_LE
                 IT8.INT_POW_EQ_0 IT1.INT_ABS_POW IT9.INT_POW_MONO
                 MESON_TAC ASM_MESON_TAC).run with
      | .ok d => do theIntMiscNat.set (some d); pure d
      | .error e => panic! s!"setupIntMiscNat failed: {e}") with
  | .ok d => d | _ => panic! "Session.IMn: setupIntMiscNat not run"

/-- Cache for `IntNumber` (int.ml 2378-2566): the `num` divisibility layer and
    `NUMBER_TAC` (int.ml 2503), the natural-number decision procedure that
    reduces a `num` goal to an integer one and hands off to the ENHANCED
    `INTEGER_TAC2` (`IGl.INTEGER_TAC2`).  Uses `INT_ARITH2` throughout.  Pure;
    cached for reuse. -/
initialize theIntNumber : IO.Ref (Option HolMath.Int.IntNumber) ← IO.mkRef none

private unsafe def INum : HolMath.Int.IntNumber :=
  match unsafeIO (do
    match ← theIntNumber.get with
    | some d => pure d
    | none => do
      match ← (HolMath.Int.setupIntNumber IA1 IA2 IGl IAr INoN INoI
                 IDv.int_divides
                 IT7.INT_OF_NUM_EQ IT7.INT_OF_NUM_LE IT7.INT_OF_NUM_LT
                 IT7.INT_OF_NUM_GE IT7.INT_OF_NUM_GT
                 IT8.INT_OF_NUM_SUC IT7.INT_OF_NUM_ADD IT8.INT_OF_NUM_MUL
                 IT8.INT_OF_NUM_POW IDr1.INT_OF_NUM_DIV
                 IDr1.INT_REM_EQ IDr1.INT_OF_NUM_REM
                 IT1.INT_ABS_POS IT1.INT_ABS_ABS IT1.INT_ABS_MUL IA1.INT_ABS
                 IT3.INT_LE_LMUL IDr1.INT_MUL_DIV_EQ IDr1.INT_DIV_BY_DIV
                 IDr1.INT_DIVIDES_DIV_DIVIDES IDr1.INT_DIVIDES_DIV_SELF
                 IDr1.INT_DIVIDES_DIVIDES_DIV IDr1.INT_DIVIDES_DIVIDES_DIV_EQ
                 Ar8.DIV_MOD Ar7.MOD_MOD_REFL Ar7.MOD_EQ_0 Ar7.DIV_ZERO
                 Ar8.DIV_MULT_ADD Ar7.DIV_MULT Ar7.DIV_0
                 Ar1.ADD_CLAUSES Ar2.MULT_CLAUSES Ar2.MULT_EQ_1 Ar2.MULT_EQ_0
                 Ar4.LE_MULT_LCANCEL Ar2.MULT_SYM Ar2.MULT_ASSOC Ar3.LE_1
                 Ar2.LE_0 Ar3.LE_REFL
                 NUM_RING MESON_TAC).run with
      | .ok d => do theIntNumber.set (some d); pure d
      | .error e => panic! s!"setupIntNumber failed: {e}") with
  | .ok d => d | _ => panic! "Session.INum: setupIntNumber not run"

/-- Cache for `IntPrime` (int.ml 2571-2630): the definition of `prime` and its
    five theorems.  `new_definition` CREATES the `prime` constant, so this
    setup is NOT idempotent - this once-only CAF guarantees it runs exactly
    once.  Every proof runs over the `IntNumber` layer (`INum`). -/
initialize theIntPrime : IO.Ref (Option HolMath.Int.IntPrime) ← IO.mkRef none

private unsafe def IPr : HolMath.Int.IntPrime :=
  match unsafeIO (do
    match ← theIntPrime.get with
    | some d => pure d
    | none => do
      match ← (HolMath.Int.setupIntPrime INum
                 Ar2.MULT_EQ_0 Ar2.MULT_EQ_1 Ar2.MULT_CLAUSES
                 Ar4.LE_MULT_LCANCEL Ar4.LE_MULT_RCANCEL
                 new_definition IAr.ARITH_RULE ASM_MESON_TAC).run with
      | .ok d => do theIntPrime.set (some d); pure d
      | .error e => panic! s!"setupIntPrime failed: {e}") with
  | .ok d => d | _ => panic! "Session.IPr: setupIntPrime not run"

/-- Cache for `RealZpow` (int.ml 2633-2761): `real_zpow` and its 22 theorems.
    THREE parser side effects run BEFORE the definition (int.ml 2634-2636:
    `make_overloadable "zpow"`, `parse_as_infix("zpow",(24,"left"))`,
    `overload_interface "zpow" real_zpow`) so `zpow` parses as the CONSTANT in
    the definition's own statement; those mutators plus
    `new_definition` are threaded in, so this setup is NOT idempotent and this
    once-only CAF guarantees it runs exactly once and IN ORDER.  Uses the
    ENHANCED `INT_ARITH2`. -/
initialize theRealZpow : IO.Ref (Option HolMath.Int.RealZpow) ← IO.mkRef none

private unsafe def RZp : HolMath.Int.RealZpow :=
  match unsafeIO (do
    match ← theRealZpow.get with
    | some d => pure d
    | none => do
      match ← (HolMath.Int.setupRealZpow
                 IT8.INT_POS INoI.NUM_OF_INT_OF_NUM IntO.FORALL_INT_CASES
                 Ar4.WLOG_LE
                 real_pow REAL_POW_1 REAL_POW_2 REAL_POW_ONE
                 REAL_INV_1 REAL_INV_INV REAL_INV_0 REAL_INV_MUL REAL_INV_POW
                 REAL_POW_ZERO REAL_POW_POW REAL_POW_MUL REAL_POW_ADD
                 REAL_POW_EQ_0 REAL_POW_LE REAL_POW_LT
                 REAL_LE_INV_EQ REAL_LT_INV_EQ REAL_INV_EQ_0
                 REAL_EQ_INV2 REAL_MUL_LINV REAL_MUL_LID REAL_MUL_ASSOC
                 REAL_MUL_SYM REAL_MUL_AC real_div
                 REAL_ABS_INV REAL_ABS_POW REAL_SGN_POW REAL_SGN_INV REAL_INV_SGN
                 COND_ID COND_SWAP
                 IT7.INT_NEG_0 IT7.INT_NEG_NEG IT7.INT_NEG_EQ_0 IT7.INT_NEG_ADD
                 IT7.INT_OF_NUM_EQ IT7.INT_OF_NUM_ADD IT8.INT_OF_NUM_MUL
                 IT6.INT_MUL_LNEG IT7.INT_MUL_RNEG IT2.INT_ADD_SYM IDm.INT_SUB
                 T.SWAP_FORALL_THM T.RIGHT_FORALL_IMP_THM T.LEFT_IMP_EXISTS_THM
                 Ar4.LE_EXISTS
                 make_overloadable overload_interface parse_as_infix
                 new_definition IA2.INT_ARITH2 IAr.ARITH_RULE MESON_TAC).run with
      | .ok d => do theRealZpow.set (some d); pure d
      | .error e => panic! s!"setupRealZpow failed: {e}") with
  | .ok d => d | _ => panic! "Session.RZp: setupRealZpow not run"

/-- Guard for `prioritize_num` (int.ml 2765), the last int.ml effect.  It
    restores `num` as the default for overloaded symbols, undoing the
    `prioritize_int` set at int.ml 70, so every file loaded after int.ml parses
    a schematic arithmetic term as `num`, not `int`.

    An `IO` action with its own once-only flag, not a memoised `Unit` CAF (a
    `let _ := <caf>` does not force a Lean CAF, so a `Unit` CAF here would never
    run and `num` priority would never be restored).  It first forces `RZp`
    (whose three `zpow` parser effects at int.ml 2634-2636 are the last
    `int`-side parser mutations), so `prioritize_num` runs after every
    `overload_interface`/`prioritize_int` effect, matching int.ml's ordering. -/
initialize thePrioritizeNum : IO.Ref Bool ← IO.mkRef false

unsafe def ensurePrioritizeNum : IO Unit := do
  if ← thePrioritizeNum.get then pure () else do
    -- STEP 1 - build the int layer PROPER under `prioritize_int` (int.ml 70),
    -- in int.ml order.  These setups' goals are pinned to their intended type
    -- by explicit `&`/`:int` or num-only operators (`DIV`/`MOD`/`EXP`), so they
    -- elaborate correctly under int priority.  Force them in DEPENDENCY ORDER -
    -- `IGl` (int.ml 1929-2067) registers the `int` `gcd`/`lcm` overloads and MUST
    -- precede `INoN` (int.ml 2107), which registers the `num` ones; `INoN`
    -- itself needs `INoI`'s `num_of_int`.  `IMn` (int.ml 2326-2375) rounds out
    -- the int-priority body.  A `let _ := <caf>` would NOT force a Lean CAF;
    -- read a field of each via `IO.mkRef`.
    let _ ← IO.mkRef (concl IGl.int_gcd)
    let _ ← IO.mkRef (concl INoI.num_of_int)
    let _ ← IO.mkRef (concl INoN.num_divides)
    let _ ← IO.mkRef (concl IDv.int_divides)
    -- STEP 1b - BUILD THE TWO REDUCTION NETS WHILE `int` PRIORITY IS STILL IN
    -- FORCE.  int.ml 1803 parses `int_red_conv_list`'s sixteen patterns under
    -- the `prioritize_int` of line 71, and all but `x:int = y` are UNANNOTATED
    -- (`x + y`, `x <= y`, `x pow n`, ...), so their types come from the ambient
    -- priority.  Our `theIntRed`/`theIntCompute` caches build lazily on FIRST
    -- USE, which for any caller after STEP 2 would parse those patterns under
    -- `num` - keying the net on NUM addition so it could never match an INT
    -- term, and making the reducers silently no-ops (a wrong-type-at-parse-time
    -- hazard crossed with lazy CAF evaluation order).
    -- Forcing the nets here reproduces the OCaml's eager 1803-before-2765 order.
    match ← (do HolMath.Int.INT_RED_CONV (← ExceptT.mk int_red_conv_list)).run with
    | .ok c => theIntRed.set (some c)
    | .error e => panic! s!"INT_RED_CONV net (int.ml 1821): {e}"
    match ← (intComputeConvIO).run with
    | .ok c => theIntCompute.set (some c)
    | .error e => panic! s!"INT_COMPUTE_CONV net (int.ml 1835): {e}"
    -- STEP 2 - `prioritize_num()` (int.ml 2765).  int.ml keeps `prioritize_int`
    -- textually in force through the number/prime/zpow blocks, but their
    -- SCHEMATIC arithmetic goals (e.g. `m <= m * n \/ m * n = 0`) are `num`
    -- there because HOL Light's bare numerals are `num` (its `int` numerals wear
    -- `&`) and its `ARITH_TAC`/`NUM_RING` are `num` procedures.  This Lean parser
    -- makes such bare-numeral/overloaded terms `int` under int priority, so we
    -- RESTORE `num` FIRST and then build those blocks, reproducing HOL Light's
    -- effective typing.  `num` is also the final default for every file loaded
    -- after int.ml - the whole point of int.ml 2765; misplacing it parses
    -- those terms at the wrong type.
    match ← (HolMath.Int.prioritize_num prioritize_overload).run with
    | .ok () => pure ()
    | .error e => panic! s!"prioritize_num failed: {e}"
    -- STEP 3 - build the num divisibility/number layer (int.ml 2378-2566), the
    -- primality layer (2571-2630) and the zpow layer (2633-2761) under `num`
    -- priority.  `IPr` transitively forces `INum` (whose `NUMBER_TAC`/`NUM_RING`
    -- calls now run as `num` procedures); `RZp` registers the `zpow` overload
    -- (int.ml 2636, a fresh symbol that does not disturb num/int priority) and
    -- defines `real_zpow`.
    let _ ← IO.mkRef (concl IMn.INT_REM_REM_POW_MIN)
    let _ ← IO.mkRef (concl IPr.prime)
    let _ ← IO.mkRef (concl RZp.real_zpow)
    thePrioritizeNum.set true


/- ---------------------------------------------------------------------- -/
/- int.ml bare theorem re-exports.  In HOL Light every theorem is a       -/
/- global name; the bundle records are a translation artefact, so each    -/
/- field is re-exported bare here (checked for collisions - none).        -/
/- ---------------------------------------------------------------------- -/
-- integer definition + existence
unsafe def integer : thm := integerDef
unsafe def is_int  : thm := IntEx.is_int
-- IntTybij
unsafe def int_tybij              : thm := IntTb.int_tybij
unsafe def int_abstr              : thm := IntTb.int_abstr
unsafe def int_rep                : thm := IntTb.int_rep
unsafe def dest_int_rep           : thm := IntTb.dest_int_rep
unsafe def INTEGER_REAL_OF_INT    : thm := IntTb.INTEGER_REAL_OF_INT
unsafe def int_eq                 : thm := IntTb.int_eq
-- IntOps
unsafe def int_le                 : thm := IntO.int_le
unsafe def int_lt                 : thm := IntO.int_lt
unsafe def int_ge                 : thm := IntO.int_ge
unsafe def int_gt                 : thm := IntO.int_gt
unsafe def int_of_num             : thm := IntO.int_of_num
unsafe def int_of_num_th          : thm := IntO.int_of_num_th
unsafe def int_neg                : thm := IntO.int_neg
unsafe def int_neg_th             : thm := IntO.int_neg_th
unsafe def int_add                : thm := IntO.int_add
unsafe def int_add_th             : thm := IntO.int_add_th
unsafe def int_sub                : thm := IntO.int_sub
unsafe def int_sub_th             : thm := IntO.int_sub_th
unsafe def int_mul                : thm := IntO.int_mul
unsafe def int_mul_th             : thm := IntO.int_mul_th
unsafe def int_abs                : thm := IntO.int_abs
unsafe def int_abs_th             : thm := IntO.int_abs_th
unsafe def int_sgn                : thm := IntO.int_sgn
unsafe def int_sgn_th             : thm := IntO.int_sgn_th
unsafe def int_max                : thm := IntO.int_max
unsafe def int_max_th             : thm := IntO.int_max_th
unsafe def int_min                : thm := IntO.int_min
unsafe def int_min_th             : thm := IntO.int_min_th
unsafe def int_pow                : thm := IntO.int_pow
unsafe def int_pow_th             : thm := IntO.int_pow_th
unsafe def REAL_OF_INT_CLAUSES    : thm := IntO.REAL_OF_INT_CLAUSES
unsafe def INT_IMAGE              : thm := IntO.INT_IMAGE
unsafe def FORALL_INT_CASES       : thm := IntO.FORALL_INT_CASES
unsafe def EXISTS_INT_CASES       : thm := IntO.EXISTS_INT_CASES
unsafe def INT_LT_DISCRETE        : thm := IntO.INT_LT_DISCRETE
unsafe def INT_GT_DISCRETE        : thm := IntO.INT_GT_DISCRETE
-- IntThms1..10
unsafe def INT_ABS_0              : thm := IT1.INT_ABS_0
unsafe def INT_ABS_1              : thm := IT1.INT_ABS_1
unsafe def INT_ABS_ABS            : thm := IT1.INT_ABS_ABS
unsafe def INT_ABS_BETWEEN        : thm := IT1.INT_ABS_BETWEEN
unsafe def INT_ABS_BETWEEN1       : thm := IT1.INT_ABS_BETWEEN1
unsafe def INT_ABS_BETWEEN2       : thm := IT1.INT_ABS_BETWEEN2
unsafe def INT_ABS_BOUND          : thm := IT1.INT_ABS_BOUND
unsafe def INT_ABS_BOUNDS         : thm := IT1.INT_ABS_BOUNDS
unsafe def INT_ABS_CASES          : thm := IT1.INT_ABS_CASES
unsafe def INT_ABS_CIRCLE         : thm := IT1.INT_ABS_CIRCLE
unsafe def INT_ABS_LE             : thm := IT1.INT_ABS_LE
unsafe def INT_ABS_MUL            : thm := IT1.INT_ABS_MUL
unsafe def INT_ABS_NEG            : thm := IT1.INT_ABS_NEG
unsafe def INT_ABS_NUM            : thm := IT1.INT_ABS_NUM
unsafe def INT_ABS_NZ             : thm := IT1.INT_ABS_NZ
unsafe def INT_ABS_POS            : thm := IT1.INT_ABS_POS
unsafe def INT_ABS_POW            : thm := IT1.INT_ABS_POW
unsafe def INT_ABS_REFL           : thm := IT1.INT_ABS_REFL
unsafe def INT_ABS_SGN            : thm := IT1.INT_ABS_SGN
unsafe def INT_ABS_SIGN           : thm := IT1.INT_ABS_SIGN
unsafe def INT_ABS_SIGN2          : thm := IT1.INT_ABS_SIGN2
unsafe def INT_ABS_STILLNZ        : thm := IT1.INT_ABS_STILLNZ
unsafe def INT_ABS_SUB            : thm := IT1.INT_ABS_SUB
unsafe def INT_ABS_SUB_ABS        : thm := IT1.INT_ABS_SUB_ABS
unsafe def INT_ABS_TRIANGLE       : thm := IT1.INT_ABS_TRIANGLE
unsafe def INT_ABS_ZERO           : thm := IT1.INT_ABS_ZERO
unsafe def INT_ADD2_SUB2          : thm := IT1.INT_ADD2_SUB2
unsafe def INT_ADD_AC             : thm := IT1.INT_ADD_AC
unsafe def INT_ADD_ASSOC          : thm := IT2.INT_ADD_ASSOC
unsafe def INT_ADD_LDISTRIB       : thm := IT2.INT_ADD_LDISTRIB
unsafe def INT_ADD_LID            : thm := IT2.INT_ADD_LID
unsafe def INT_ADD_LINV           : thm := IT2.INT_ADD_LINV
unsafe def INT_ADD_RDISTRIB       : thm := IT2.INT_ADD_RDISTRIB
unsafe def INT_ADD_RID            : thm := IT2.INT_ADD_RID
unsafe def INT_ADD_RINV           : thm := IT2.INT_ADD_RINV
unsafe def INT_ADD_SUB            : thm := IT2.INT_ADD_SUB
unsafe def INT_ADD_SUB2           : thm := IT2.INT_ADD_SUB2
unsafe def INT_ADD_SYM            : thm := IT2.INT_ADD_SYM
unsafe def INT_BOUNDS_LE          : thm := IT2.INT_BOUNDS_LE
unsafe def INT_BOUNDS_LT          : thm := IT2.INT_BOUNDS_LT
unsafe def INT_DIFFSQ             : thm := IT2.INT_DIFFSQ
unsafe def INT_ENTIRE             : thm := IT2.INT_ENTIRE
unsafe def INT_EQ_ADD_LCANCEL     : thm := IT2.INT_EQ_ADD_LCANCEL
unsafe def INT_EQ_ADD_LCANCEL_0   : thm := IT2.INT_EQ_ADD_LCANCEL_0
unsafe def INT_EQ_ADD_RCANCEL     : thm := IT2.INT_EQ_ADD_RCANCEL
unsafe def INT_EQ_ADD_RCANCEL_0   : thm := IT2.INT_EQ_ADD_RCANCEL_0
unsafe def INT_EQ_IMP_LE          : thm := IT2.INT_EQ_IMP_LE
unsafe def INT_EQ_LCANCEL_IMP     : thm := IT2.INT_EQ_LCANCEL_IMP
unsafe def INT_EQ_MUL_LCANCEL     : thm := IT2.INT_EQ_MUL_LCANCEL
unsafe def INT_EQ_MUL_RCANCEL     : thm := IT2.INT_EQ_MUL_RCANCEL
unsafe def INT_EQ_NEG2            : thm := IT2.INT_EQ_NEG2
unsafe def INT_EQ_RCANCEL_IMP     : thm := IT2.INT_EQ_RCANCEL_IMP
unsafe def INT_EQ_SGN_ABS         : thm := IT2.INT_EQ_SGN_ABS
unsafe def INT_EQ_SQUARE_ABS      : thm := IT2.INT_EQ_SQUARE_ABS
unsafe def INT_EQ_SUB_LADD        : thm := IT2.INT_EQ_SUB_LADD
unsafe def INT_EQ_SUB_RADD        : thm := IT2.INT_EQ_SUB_RADD
unsafe def INT_EVENPOW_ABS        : thm := IT3.INT_EVENPOW_ABS
unsafe def INT_LET_ADD            : thm := IT3.INT_LET_ADD
unsafe def INT_LET_ADD2           : thm := IT3.INT_LET_ADD2
unsafe def INT_LET_ANTISYM        : thm := IT3.INT_LET_ANTISYM
unsafe def INT_LET_TOTAL          : thm := IT3.INT_LET_TOTAL
unsafe def INT_LET_TRANS          : thm := IT3.INT_LET_TRANS
unsafe def INT_LE_01              : thm := IT3.INT_LE_01
unsafe def INT_LE_ADD             : thm := IT3.INT_LE_ADD
unsafe def INT_LE_ADD2            : thm := IT3.INT_LE_ADD2
unsafe def INT_LE_ADDL            : thm := IT3.INT_LE_ADDL
unsafe def INT_LE_ADDR            : thm := IT3.INT_LE_ADDR
unsafe def INT_LE_ANTISYM         : thm := IT3.INT_LE_ANTISYM
unsafe def INT_LE_DOUBLE          : thm := IT3.INT_LE_DOUBLE
unsafe def INT_LE_LADD            : thm := IT3.INT_LE_LADD
unsafe def INT_LE_LADD_IMP        : thm := IT3.INT_LE_LADD_IMP
unsafe def INT_LE_LCANCEL_IMP     : thm := IT3.INT_LE_LCANCEL_IMP
unsafe def INT_LE_LMUL            : thm := IT3.INT_LE_LMUL
unsafe def INT_LE_LMUL_EQ         : thm := IT3.INT_LE_LMUL_EQ
unsafe def INT_LE_LNEG            : thm := IT3.INT_LE_LNEG
unsafe def INT_LE_LT              : thm := IT3.INT_LE_LT
unsafe def INT_LE_MAX             : thm := IT3.INT_LE_MAX
unsafe def INT_LE_MIN             : thm := IT3.INT_LE_MIN
unsafe def INT_LE_MUL             : thm := IT3.INT_LE_MUL
unsafe def INT_LE_MUL2            : thm := IT3.INT_LE_MUL2
unsafe def INT_LE_MUL_EQ          : thm := IT3.INT_LE_MUL_EQ
unsafe def INT_LE_NEG2            : thm := IT3.INT_LE_NEG2
unsafe def INT_LE_NEGL            : thm := IT3.INT_LE_NEGL
unsafe def INT_LE_NEGR            : thm := IT3.INT_LE_NEGR
unsafe def INT_LE_NEGTOTAL        : thm := IT4.INT_LE_NEGTOTAL
unsafe def INT_LE_POW2            : thm := IT4.INT_LE_POW2
unsafe def INT_LE_POW_2           : thm := IT4.INT_LE_POW_2
unsafe def INT_LE_RADD            : thm := IT4.INT_LE_RADD
unsafe def INT_LE_RCANCEL_IMP     : thm := IT4.INT_LE_RCANCEL_IMP
unsafe def INT_LE_REFL            : thm := IT4.INT_LE_REFL
unsafe def INT_LE_RMUL            : thm := IT4.INT_LE_RMUL
unsafe def INT_LE_RMUL_EQ         : thm := IT4.INT_LE_RMUL_EQ
unsafe def INT_LE_RNEG            : thm := IT4.INT_LE_RNEG
unsafe def INT_LE_SQUARE          : thm := IT4.INT_LE_SQUARE
unsafe def INT_LE_SQUARE_ABS      : thm := IT4.INT_LE_SQUARE_ABS
unsafe def INT_LE_SUB_LADD        : thm := IT4.INT_LE_SUB_LADD
unsafe def INT_LE_SUB_RADD        : thm := IT4.INT_LE_SUB_RADD
unsafe def INT_LE_TOTAL           : thm := IT4.INT_LE_TOTAL
unsafe def INT_LE_TRANS           : thm := IT4.INT_LE_TRANS
unsafe def INT_LNEG_UNIQ          : thm := IT4.INT_LNEG_UNIQ
unsafe def INT_LTE_ADD            : thm := IT4.INT_LTE_ADD
unsafe def INT_LTE_ADD2           : thm := IT4.INT_LTE_ADD2
unsafe def INT_LTE_ANTISYM        : thm := IT4.INT_LTE_ANTISYM
unsafe def INT_LTE_TOTAL          : thm := IT4.INT_LTE_TOTAL
unsafe def INT_LTE_TRANS          : thm := IT4.INT_LTE_TRANS
unsafe def INT_LT_01              : thm := IT4.INT_LT_01
unsafe def INT_LT_ADD             : thm := IT4.INT_LT_ADD
unsafe def INT_LT_ADD1            : thm := IT4.INT_LT_ADD1
unsafe def INT_LT_ADD2            : thm := IT4.INT_LT_ADD2
unsafe def INT_LT_ADDL            : thm := IT4.INT_LT_ADDL
unsafe def INT_LT_ADDNEG          : thm := IT4.INT_LT_ADDNEG
unsafe def INT_LT_ADDNEG2         : thm := IT4.INT_LT_ADDNEG2
unsafe def INT_LT_ADDR            : thm := IT5.INT_LT_ADDR
unsafe def INT_LT_ADD_SUB         : thm := IT5.INT_LT_ADD_SUB
unsafe def INT_LT_ANTISYM         : thm := IT5.INT_LT_ANTISYM
unsafe def INT_LT_GT              : thm := IT5.INT_LT_GT
unsafe def INT_LT_IMP_LE          : thm := IT5.INT_LT_IMP_LE
unsafe def INT_LT_IMP_NE          : thm := IT5.INT_LT_IMP_NE
unsafe def INT_LT_LADD            : thm := IT5.INT_LT_LADD
unsafe def INT_LT_LADD_IMP        : thm := IT5.INT_LT_LADD_IMP
unsafe def INT_LT_LCANCEL_IMP     : thm := IT5.INT_LT_LCANCEL_IMP
unsafe def INT_LT_LE              : thm := IT5.INT_LT_LE
unsafe def INT_LT_LMUL            : thm := IT5.INT_LT_LMUL
unsafe def INT_LT_LMUL_EQ         : thm := IT5.INT_LT_LMUL_EQ
unsafe def INT_LT_LNEG            : thm := IT5.INT_LT_LNEG
unsafe def INT_LT_MAX             : thm := IT5.INT_LT_MAX
unsafe def INT_LT_MIN             : thm := IT5.INT_LT_MIN
unsafe def INT_LT_MUL             : thm := IT5.INT_LT_MUL
unsafe def INT_LT_MUL2            : thm := IT5.INT_LT_MUL2
unsafe def INT_LT_MUL_EQ          : thm := IT5.INT_LT_MUL_EQ
unsafe def INT_LT_NEG2            : thm := IT5.INT_LT_NEG2
unsafe def INT_LT_NEGTOTAL        : thm := IT5.INT_LT_NEGTOTAL
unsafe def INT_LT_POW2            : thm := IT5.INT_LT_POW2
unsafe def INT_LT_POW_2           : thm := IT5.INT_LT_POW_2
unsafe def INT_LT_RADD            : thm := IT5.INT_LT_RADD
unsafe def INT_LT_RCANCEL_IMP     : thm := IT5.INT_LT_RCANCEL_IMP
unsafe def INT_LT_REFL            : thm := IT5.INT_LT_REFL
unsafe def INT_LT_RMUL            : thm := IT5.INT_LT_RMUL
unsafe def INT_LT_RMUL_EQ         : thm := IT5.INT_LT_RMUL_EQ
unsafe def INT_LT_RNEG            : thm := IT5.INT_LT_RNEG
unsafe def INT_LT_SQUARE          : thm := IT6.INT_LT_SQUARE
unsafe def INT_LT_SQUARE_ABS      : thm := IT6.INT_LT_SQUARE_ABS
unsafe def INT_LT_SUB_LADD        : thm := IT6.INT_LT_SUB_LADD
unsafe def INT_LT_SUB_RADD        : thm := IT6.INT_LT_SUB_RADD
unsafe def INT_LT_TOTAL           : thm := IT6.INT_LT_TOTAL
unsafe def INT_LT_TRANS           : thm := IT6.INT_LT_TRANS
unsafe def INT_MAX_ACI            : thm := IT6.INT_MAX_ACI
unsafe def INT_MAX_ASSOC          : thm := IT6.INT_MAX_ASSOC
unsafe def INT_MAX_LE             : thm := IT6.INT_MAX_LE
unsafe def INT_MAX_LT             : thm := IT6.INT_MAX_LT
unsafe def INT_MAX_MAX            : thm := IT6.INT_MAX_MAX
unsafe def INT_MAX_MIN            : thm := IT6.INT_MAX_MIN
unsafe def INT_MAX_SYM            : thm := IT6.INT_MAX_SYM
unsafe def INT_MIN_ACI            : thm := IT6.INT_MIN_ACI
unsafe def INT_MIN_ASSOC          : thm := IT6.INT_MIN_ASSOC
unsafe def INT_MIN_LE             : thm := IT6.INT_MIN_LE
unsafe def INT_MIN_LT             : thm := IT6.INT_MIN_LT
unsafe def INT_MIN_MAX            : thm := IT6.INT_MIN_MAX
unsafe def INT_MIN_MIN            : thm := IT6.INT_MIN_MIN
unsafe def INT_MIN_SYM            : thm := IT6.INT_MIN_SYM
unsafe def INT_MUL_2              : thm := IT6.INT_MUL_2
unsafe def INT_MUL_AC             : thm := IT6.INT_MUL_AC
unsafe def INT_MUL_ASSOC          : thm := IT6.INT_MUL_ASSOC
unsafe def INT_MUL_LID            : thm := IT6.INT_MUL_LID
unsafe def INT_MUL_LNEG           : thm := IT6.INT_MUL_LNEG
unsafe def INT_MUL_LZERO          : thm := IT6.INT_MUL_LZERO
unsafe def INT_MUL_POS_LE         : thm := IT6.INT_MUL_POS_LE
unsafe def INT_MUL_POS_LT         : thm := IT6.INT_MUL_POS_LT
unsafe def INT_MUL_RID            : thm := IT7.INT_MUL_RID
unsafe def INT_MUL_RNEG           : thm := IT7.INT_MUL_RNEG
unsafe def INT_MUL_RZERO          : thm := IT7.INT_MUL_RZERO
unsafe def INT_MUL_SYM            : thm := IT7.INT_MUL_SYM
unsafe def INT_NEG_0              : thm := IT7.INT_NEG_0
unsafe def INT_NEG_ADD            : thm := IT7.INT_NEG_ADD
unsafe def INT_NEG_EQ             : thm := IT7.INT_NEG_EQ
unsafe def INT_NEG_EQ_0           : thm := IT7.INT_NEG_EQ_0
unsafe def INT_NEG_GE0            : thm := IT7.INT_NEG_GE0
unsafe def INT_NEG_GT0            : thm := IT7.INT_NEG_GT0
unsafe def INT_NEG_LE0            : thm := IT7.INT_NEG_LE0
unsafe def INT_NEG_LMUL           : thm := IT7.INT_NEG_LMUL
unsafe def INT_NEG_LT0            : thm := IT7.INT_NEG_LT0
unsafe def INT_NEG_MINUS1         : thm := IT7.INT_NEG_MINUS1
unsafe def INT_NEG_MUL2           : thm := IT7.INT_NEG_MUL2
unsafe def INT_NEG_NEG            : thm := IT7.INT_NEG_NEG
unsafe def INT_NEG_RMUL           : thm := IT7.INT_NEG_RMUL
unsafe def INT_NEG_SUB            : thm := IT7.INT_NEG_SUB
unsafe def INT_NOT_EQ             : thm := IT7.INT_NOT_EQ
unsafe def INT_NOT_LE             : thm := IT7.INT_NOT_LE
unsafe def INT_NOT_LT             : thm := IT7.INT_NOT_LT
unsafe def INT_OF_NUM_ADD         : thm := IT7.INT_OF_NUM_ADD
unsafe def INT_OF_NUM_CLAUSES     : thm := IT7.INT_OF_NUM_CLAUSES
unsafe def INT_OF_NUM_EQ          : thm := IT7.INT_OF_NUM_EQ
unsafe def INT_OF_NUM_GE          : thm := IT7.INT_OF_NUM_GE
unsafe def INT_OF_NUM_GT          : thm := IT7.INT_OF_NUM_GT
unsafe def INT_OF_NUM_LE          : thm := IT7.INT_OF_NUM_LE
unsafe def INT_OF_NUM_LT          : thm := IT7.INT_OF_NUM_LT
unsafe def INT_OF_NUM_MAX         : thm := IT8.INT_OF_NUM_MAX
unsafe def INT_OF_NUM_MIN         : thm := IT8.INT_OF_NUM_MIN
unsafe def INT_OF_NUM_MOD         : thm := IT8.INT_OF_NUM_MOD
unsafe def INT_OF_NUM_MUL         : thm := IT8.INT_OF_NUM_MUL
unsafe def INT_OF_NUM_POW         : thm := IT8.INT_OF_NUM_POW
unsafe def INT_OF_NUM_SUB         : thm := IT8.INT_OF_NUM_SUB
unsafe def INT_OF_NUM_SUB_CASES   : thm := IT8.INT_OF_NUM_SUB_CASES
unsafe def INT_OF_NUM_SUC         : thm := IT8.INT_OF_NUM_SUC
unsafe def INT_POS                : thm := IT8.INT_POS
unsafe def INT_POS_EQ_SQUARE      : thm := IT8.INT_POS_EQ_SQUARE
unsafe def INT_POS_NZ             : thm := IT8.INT_POS_NZ
unsafe def INT_POW2_ABS           : thm := IT8.INT_POW2_ABS
unsafe def INT_POW_1              : thm := IT8.INT_POW_1
unsafe def INT_POW_1_LE           : thm := IT8.INT_POW_1_LE
unsafe def INT_POW_1_LT           : thm := IT8.INT_POW_1_LT
unsafe def INT_POW_2              : thm := IT8.INT_POW_2
unsafe def INT_POW_ADD            : thm := IT8.INT_POW_ADD
unsafe def INT_POW_EQ             : thm := IT8.INT_POW_EQ
unsafe def INT_POW_EQ_0           : thm := IT8.INT_POW_EQ_0
unsafe def INT_POW_EQ_1           : thm := IT8.INT_POW_EQ_1
unsafe def INT_POW_EQ_1_IMP       : thm := IT8.INT_POW_EQ_1_IMP
unsafe def INT_POW_EQ_ABS         : thm := IT8.INT_POW_EQ_ABS
unsafe def INT_POW_EQ_EQ          : thm := IT8.INT_POW_EQ_EQ
unsafe def INT_POW_EQ_ODD         : thm := IT8.INT_POW_EQ_ODD
unsafe def INT_POW_EQ_ODD_EQ      : thm := IT8.INT_POW_EQ_ODD_EQ
unsafe def INT_POW_LBOUND         : thm := IT8.INT_POW_LBOUND
unsafe def INT_POW_LE             : thm := IT8.INT_POW_LE
unsafe def INT_POW_LE2            : thm := IT8.INT_POW_LE2
unsafe def INT_POW_LE2_ODD        : thm := IT9.INT_POW_LE2_ODD
unsafe def INT_POW_LE2_ODD_EQ     : thm := IT9.INT_POW_LE2_ODD_EQ
unsafe def INT_POW_LE2_REV        : thm := IT9.INT_POW_LE2_REV
unsafe def INT_POW_LE_1           : thm := IT9.INT_POW_LE_1
unsafe def INT_POW_LT             : thm := IT9.INT_POW_LT
unsafe def INT_POW_LT2            : thm := IT9.INT_POW_LT2
unsafe def INT_POW_LT2_ODD        : thm := IT9.INT_POW_LT2_ODD
unsafe def INT_POW_LT2_ODD_EQ     : thm := IT9.INT_POW_LT2_ODD_EQ
unsafe def INT_POW_LT2_REV        : thm := IT9.INT_POW_LT2_REV
unsafe def INT_POW_LT_1           : thm := IT9.INT_POW_LT_1
unsafe def INT_POW_MONO           : thm := IT9.INT_POW_MONO
unsafe def INT_POW_MONO_LT        : thm := IT9.INT_POW_MONO_LT
unsafe def INT_POW_MUL            : thm := IT9.INT_POW_MUL
unsafe def INT_POW_NEG            : thm := IT9.INT_POW_NEG
unsafe def INT_POW_NZ             : thm := IT9.INT_POW_NZ
unsafe def INT_POW_ONE            : thm := IT9.INT_POW_ONE
unsafe def INT_POW_POW            : thm := IT9.INT_POW_POW
unsafe def INT_POW_ZERO           : thm := IT9.INT_POW_ZERO
unsafe def INT_RNEG_UNIQ          : thm := IT9.INT_RNEG_UNIQ
unsafe def INT_SGN                : thm := IT9.INT_SGN
unsafe def INT_SGNS_EQ            : thm := IT9.INT_SGNS_EQ
unsafe def INT_SGNS_EQ_ALT        : thm := IT9.INT_SGNS_EQ_ALT
unsafe def INT_SGN_0              : thm := IT9.INT_SGN_0
unsafe def INT_SGN_ABS            : thm := IT9.INT_SGN_ABS
unsafe def INT_SGN_ABS_ALT        : thm := IT9.INT_SGN_ABS_ALT
unsafe def INT_SGN_CASES          : thm := IT9.INT_SGN_CASES
unsafe def INT_SGN_EQ             : thm := IT10.INT_SGN_EQ
unsafe def INT_SGN_EQ_INEQ        : thm := IT10.INT_SGN_EQ_INEQ
unsafe def INT_SGN_INEQS          : thm := IT10.INT_SGN_INEQS
unsafe def INT_SGN_INT_SGN        : thm := IT10.INT_SGN_INT_SGN
unsafe def INT_SGN_MUL            : thm := IT10.INT_SGN_MUL
unsafe def INT_SGN_NEG            : thm := IT10.INT_SGN_NEG
unsafe def INT_SGN_POW            : thm := IT10.INT_SGN_POW
unsafe def INT_SGN_POW_2          : thm := IT10.INT_SGN_POW_2
unsafe def INT_SOS_EQ_0           : thm := IT10.INT_SOS_EQ_0
unsafe def INT_SUB_0              : thm := IT10.INT_SUB_0
unsafe def INT_SUB_ABS            : thm := IT10.INT_SUB_ABS
unsafe def INT_SUB_ADD            : thm := IT10.INT_SUB_ADD
unsafe def INT_SUB_ADD2           : thm := IT10.INT_SUB_ADD2
unsafe def INT_SUB_LDISTRIB       : thm := IT10.INT_SUB_LDISTRIB
unsafe def INT_SUB_LE             : thm := IT10.INT_SUB_LE
unsafe def INT_SUB_LNEG           : thm := IT10.INT_SUB_LNEG
unsafe def INT_SUB_LT             : thm := IT10.INT_SUB_LT
unsafe def INT_SUB_LZERO          : thm := IT10.INT_SUB_LZERO
unsafe def INT_SUB_NEG2           : thm := IT10.INT_SUB_NEG2
unsafe def INT_SUB_RDISTRIB       : thm := IT10.INT_SUB_RDISTRIB
unsafe def INT_SUB_REFL           : thm := IT10.INT_SUB_REFL
unsafe def INT_SUB_RNEG           : thm := IT10.INT_SUB_RNEG
unsafe def INT_SUB_RZERO          : thm := IT10.INT_SUB_RZERO
unsafe def INT_SUB_SUB            : thm := IT10.INT_SUB_SUB
unsafe def INT_SUB_SUB2           : thm := IT10.INT_SUB_SUB2
unsafe def INT_SUB_TRIANGLE       : thm := IT10.INT_SUB_TRIANGLE
-- IntWlog
unsafe def INT_WLOG_LE            : thm := IWl.INT_WLOG_LE
unsafe def INT_WLOG_LT            : thm := IWl.INT_WLOG_LT
unsafe def INT_WLOG_LE_3          : thm := IWl.INT_WLOG_LE_3
-- IntArith1 (thm fields only)
unsafe def INT_FORALL_POS         : thm := IA1.INT_FORALL_POS
unsafe def INT_EXISTS_POS         : thm := IA1.INT_EXISTS_POS
unsafe def INT_FORALL_ABS         : thm := IA1.INT_FORALL_ABS
unsafe def INT_EXISTS_ABS         : thm := IA1.INT_EXISTS_ABS
unsafe def INT_POW                : thm := IA1.INT_POW
unsafe def INT_ABS                : thm := IA1.INT_ABS
unsafe def INT_GE                 : thm := IA1.INT_GE
unsafe def INT_GT                 : thm := IA1.INT_GT
unsafe def INT_LT                 : thm := IA1.INT_LT
-- IntDivMod
unsafe def INT_SUB                : thm := IDm.INT_SUB
unsafe def INT_MAX                : thm := IDm.INT_MAX
unsafe def INT_MIN                : thm := IDm.INT_MIN
unsafe def INT_OF_NUM_EXISTS      : thm := IDm.INT_OF_NUM_EXISTS
unsafe def INT_LE_DISCRETE        : thm := IDm.INT_LE_DISCRETE
unsafe def INT_LE_TRANS_LE        : thm := IDm.INT_LE_TRANS_LE
unsafe def INT_LE_TRANS_LT        : thm := IDm.INT_LE_TRANS_LT
unsafe def INT_MUL_EQ_1           : thm := IDm.INT_MUL_EQ_1
unsafe def INT_ABS_MUL_1          : thm := IDm.INT_ABS_MUL_1
unsafe def INT_WOP                : thm := IDm.INT_WOP
unsafe def INT_ARCH               : thm := IDm.INT_ARCH
unsafe def INT_DIVMOD_EXIST_0     : thm := IDm.INT_DIVMOD_EXIST_0
unsafe def INT_DIVISION_0         : thm := IDm.INT_DIVISION_0
unsafe def INT_DIVISION           : thm := IDm.INT_DIVISION
unsafe def INT_DIVISION_SIMP      : thm := IDm.INT_DIVISION_SIMP
unsafe def INT_REM_POS            : thm := IDm.INT_REM_POS
unsafe def INT_DIV_0              : thm := IDm.INT_DIV_0
unsafe def INT_REM_0              : thm := IDm.INT_REM_0
unsafe def INT_REM_POS_EQ         : thm := IDm.INT_REM_POS_EQ
unsafe def INT_REM_DIV            : thm := IDm.INT_REM_DIV
unsafe def INT_LT_REM             : thm := IDm.INT_LT_REM
unsafe def INT_LT_REM_EQ          : thm := IDm.INT_LT_REM_EQ
-- IntDivisibility
unsafe def cong                   : thm := IDv.cong
unsafe def real_mod               : thm := IDv.real_mod
unsafe def int_divides            : thm := IDv.int_divides
unsafe def INT_DIVIDES_LE         : thm := IDv.INT_DIVIDES_LE
unsafe def int_mod                : thm := IDv.int_mod
unsafe def int_congruent          : thm := IDv.int_congruent
unsafe def INT_CONG_IMP_EQ        : thm := IDv.INT_CONG_IMP_EQ
unsafe def int_coprime            : thm := IDv.int_coprime
-- IntArith1 procedures (int.ml 674-707): the bootstrapping decision procedure.
unsafe def INT_ARITH1 : term → IO (Except String thm) := IA1.INT_ARITH1
unsafe def INT_ARITH_TAC1 : tactic := IA1.INT_ARITH_TAC1
unsafe def ASM_INT_ARITH_TAC1 : tactic := IA1.ASM_INT_ARITH_TAC1
unsafe def INTEGER_TAC1 : tactic := ITc1.INTEGER_TAC1
unsafe def INTEGER_RULE1 : term → IO (Except String thm) := ITc1.INTEGER_RULE1
-- IntDivRem1 (int.ml 1329-1763): the 47 further div/rem/congruence proofs.
unsafe def INT_DIVMOD_UNIQ        : thm := IDr1.INT_DIVMOD_UNIQ
unsafe def INT_DIV_UNIQ           : thm := IDr1.INT_DIV_UNIQ
unsafe def INT_REM_UNIQ           : thm := IDr1.INT_REM_UNIQ
unsafe def INT_DIV_LT             : thm := IDr1.INT_DIV_LT
unsafe def INT_REM_LT             : thm := IDr1.INT_REM_LT
unsafe def INT_DIV_RNEG           : thm := IDr1.INT_DIV_RNEG
unsafe def INT_REM_RNEG           : thm := IDr1.INT_REM_RNEG
unsafe def INT_REM_RABS           : thm := IDr1.INT_REM_RABS
unsafe def INT_REM_REM            : thm := IDr1.INT_REM_REM
unsafe def INT_REM_EQ             : thm := IDr1.INT_REM_EQ
unsafe def INT_DIV_ZERO           : thm := IDr1.INT_DIV_ZERO
unsafe def INT_REM_ZERO           : thm := IDr1.INT_REM_ZERO
unsafe def INT_REM_EQ_0           : thm := IDr1.INT_REM_EQ_0
unsafe def INT_MUL_DIV_EQ         : thm := IDr1.INT_MUL_DIV_EQ
unsafe def INT_CONG_LREM          : thm := IDr1.INT_CONG_LREM
unsafe def INT_CONG_RREM          : thm := IDr1.INT_CONG_RREM
unsafe def INT_REM_MOD_SELF       : thm := IDr1.INT_REM_MOD_SELF
unsafe def INT_REM_REM_MUL        : thm := IDr1.INT_REM_REM_MUL
unsafe def INT_CONG_SOLVE_BOUNDS  : thm := IDr1.INT_CONG_SOLVE_BOUNDS
unsafe def INT_NEG_REM            : thm := IDr1.INT_NEG_REM
unsafe def INT_ADD_REM            : thm := IDr1.INT_ADD_REM
unsafe def INT_SUB_REM            : thm := IDr1.INT_SUB_REM
unsafe def INT_MUL_REM            : thm := IDr1.INT_MUL_REM
unsafe def INT_POW_REM            : thm := IDr1.INT_POW_REM
unsafe def INT_OF_NUM_DIV         : thm := IDr1.INT_OF_NUM_DIV
unsafe def INT_OF_NUM_REM         : thm := IDr1.INT_OF_NUM_REM
unsafe def INT_DIV_REFL           : thm := IDr1.INT_DIV_REFL
unsafe def INT_REM_REFL           : thm := IDr1.INT_REM_REFL
unsafe def INT_DIV_LNEG           : thm := IDr1.INT_DIV_LNEG
unsafe def INT_REM_LNEG           : thm := IDr1.INT_REM_LNEG
unsafe def INT_DIV_NEG2           : thm := IDr1.INT_DIV_NEG2
unsafe def INT_REM_NEG2           : thm := IDr1.INT_REM_NEG2
unsafe def INT_DIV_1              : thm := IDr1.INT_DIV_1
unsafe def INT_REM_1              : thm := IDr1.INT_REM_1
unsafe def INT_DIV_MUL            : thm := IDr1.INT_DIV_MUL
unsafe def INT_REM_MUL            : thm := IDr1.INT_REM_MUL
unsafe def INT_DIV_LT_EQ          : thm := IDr1.INT_DIV_LT_EQ
unsafe def INT_LE_DIV_EQ          : thm := IDr1.INT_LE_DIV_EQ
unsafe def INT_DIV_LE_EQ          : thm := IDr1.INT_DIV_LE_EQ
unsafe def INT_LT_DIV_EQ          : thm := IDr1.INT_LT_DIV_EQ
unsafe def INT_DIV_LE             : thm := IDr1.INT_DIV_LE
unsafe def INT_DIV_DIV            : thm := IDr1.INT_DIV_DIV
unsafe def INT_REM_MUL_REM        : thm := IDr1.INT_REM_MUL_REM
unsafe def INT_DIV_EQ_0           : thm := IDr1.INT_DIV_EQ_0
unsafe def INT_REM_EQ_SELF        : thm := IDr1.INT_REM_EQ_SELF
unsafe def INT_REM_UNIQUE         : thm := IDr1.INT_REM_UNIQUE
unsafe def INT_DIV_REM            : thm := IDr1.INT_DIV_REM
unsafe def INT_REM_REM_LE         : thm := IDr1.INT_REM_REM_LE
unsafe def INT_LE_DIV             : thm := IDr1.INT_LE_DIV
unsafe def INT_LT_DIV             : thm := IDr1.INT_LT_DIV
unsafe def INT_REM_LE_EQ          : thm := IDr1.INT_REM_LE_EQ
unsafe def INT_REM_LE             : thm := IDr1.INT_REM_LE
unsafe def INT_REM_MUL_ADD        : thm := IDr1.INT_REM_MUL_ADD
unsafe def INT_DIV_MUL_ADD        : thm := IDr1.INT_DIV_MUL_ADD
unsafe def INT_CONG_DIV2          : thm := IDr1.INT_CONG_DIV2
unsafe def INT_REM_2_CASES        : thm := IDr1.INT_REM_2_CASES
unsafe def NOT_INT_REM_2          : thm := IDr1.NOT_INT_REM_2
unsafe def INT_REM_2_DIVIDES      : thm := IDr1.INT_REM_2_DIVIDES
unsafe def INT_REM_2_EXPAND       : thm := IDr1.INT_REM_2_EXPAND
unsafe def INT_REM_2_NEG          : thm := IDr1.INT_REM_2_NEG
unsafe def INT_DIVIDES_DIV_SELF   : thm := IDr1.INT_DIVIDES_DIV_SELF
unsafe def INT_DIV_BY_DIV         : thm := IDr1.INT_DIV_BY_DIV
unsafe def INT_DIVIDES_DIV_DIVIDES : thm := IDr1.INT_DIVIDES_DIV_DIVIDES
unsafe def INT_DIVIDES_DIVIDES_DIV : thm := IDr1.INT_DIVIDES_DIVIDES_DIV
unsafe def INT_DIVIDES_DIVIDES_DIV_EQ : thm := IDr1.INT_DIVIDES_DIVIDES_DIV_EQ
-- Reduction net, even/odd analogues and rem conversions (int.ml 1772-1928).
unsafe def INT_DIV_CONV           : ioconv := IDrc.INT_DIV_CONV
unsafe def INT_REM_CONV           : ioconv := IDrc.INT_REM_CONV
unsafe def INT_2_DIVIDES_ADD      : thm := IEo.INT_2_DIVIDES_ADD
unsafe def INT_2_DIVIDES_SUB      : thm := IEo.INT_2_DIVIDES_SUB
unsafe def INT_2_DIVIDES_MUL      : thm := IEo.INT_2_DIVIDES_MUL
unsafe def INT_2_DIVIDES_POW      : thm := IEo.INT_2_DIVIDES_POW
unsafe def INT_REM_DOWN_CONV      : ioconv := IRc.INT_REM_DOWN_CONV
unsafe def INT_POW_REM_CONV       : ioconv := IRc.INT_POW_REM_CONV
-- IntGcdLcm (int.ml 1929-2067): gcd/lcm, Bezout, and the SECOND INTEGER_TAC.
unsafe def WF_INT_MEASURE         : thm := IGl.WF_INT_MEASURE
unsafe def WF_INT_MEASURE_2       : thm := IGl.WF_INT_MEASURE_2
unsafe def INT_GCD_EXISTS         : thm := IGl.INT_GCD_EXISTS
unsafe def INT_GCD_EXISTS_POS     : thm := IGl.INT_GCD_EXISTS_POS
unsafe def int_gcd                : thm := IGl.int_gcd
unsafe def int_lcm                : thm := IGl.int_lcm
unsafe def INT_DIVIDES_LABS       : thm := IGl.INT_DIVIDES_LABS
unsafe def INT_DIVIDES_RABS       : thm := IGl.INT_DIVIDES_RABS
unsafe def INT_DIVIDES_ABS        : thm := IGl.INT_DIVIDES_ABS
unsafe def INT_LCM_POS            : thm := IGl.INT_LCM_POS
unsafe def INT_MUL_GCD_LCM        : thm := IGl.INT_MUL_GCD_LCM
unsafe def INT_MUL_LCM_GCD        : thm := IGl.INT_MUL_LCM_GCD
unsafe def INT_DIVIDES_LCM_GCD    : thm := IGl.INT_DIVIDES_LCM_GCD
unsafe def INT_LCM_DIVIDES        : thm := IGl.INT_LCM_DIVIDES
unsafe def INT_LCM                : thm := IGl.INT_LCM
-- The SECOND INTEGER_TAC/INTEGER_RULE (int.ml 2045/2064).  These REPLACE the
-- v1 versions: they additionally eliminate `gcd`/`lcm`.  Callers wanting gcd/lcm
-- goals decided use these v2 accessors (and the unnumbered `INTEGER_TAC`/
-- `INTEGER_RULE` below alias them, exactly as int.ml's later text refers to the
-- NAME `INTEGER_TAC` = v2); the v1 versions remain available as
-- `INTEGER_TAC1`/`INTEGER_RULE1` and are what the div/rem layer (int.ml
-- 1329-1763) and INTEGER_TAC2's own internal fallback consume.
unsafe def INTEGER_TAC2 : tactic := IGl.INTEGER_TAC2
unsafe def INTEGER_RULE2 : term → IO (Except String thm) := IGl.INTEGER_RULE2
unsafe def INTEGER_TAC : tactic := IGl.INTEGER_TAC2
unsafe def INTEGER_RULE : term → IO (Except String thm) := IGl.INTEGER_RULE2
-- IntConstSyntax operations (int.ml 268-281).
def is_intconst : term → Bool := HolMath.Int.is_intconst
def dest_intconst : term → Except String Rat := HolMath.Int.dest_intconst
unsafe def mk_intconst (x : Rat) : Except String term := HolMath.Int.mk_intconst IntKs x
-- IntCompareConvs (int.ml 887-936): the five relational numeral conversions.
unsafe def INT_LE_CONV : ioconv := ICv.INT_LE_CONV
unsafe def INT_LT_CONV : ioconv := ICv.INT_LT_CONV
unsafe def INT_GE_CONV : ioconv := ICv.INT_GE_CONV
unsafe def INT_GT_CONV : ioconv := ICv.INT_GT_CONV
unsafe def INT_EQ_CONV : ioconv := ICv.INT_EQ_CONV
-- IntArithConvs (int.ml 941-1079): the nine arithmetic numeral conversions.
unsafe def INT_NEG_CONV : ioconv := IAv.INT_NEG_CONV
unsafe def INT_MUL_CONV : ioconv := IAv.INT_MUL_CONV
unsafe def INT_ADD_CONV : ioconv := IAv.INT_ADD_CONV
unsafe def INT_SUB_CONV : ioconv := IAv.INT_SUB_CONV
unsafe def INT_POW_CONV : ioconv := IAv.INT_POW_CONV
unsafe def INT_ABS_CONV : ioconv := IAv.INT_ABS_CONV
unsafe def INT_MAX_CONV : ioconv := IAv.INT_MAX_CONV
unsafe def INT_MIN_CONV : ioconv := IAv.INT_MIN_CONV
unsafe def INT_SGN_CONV : ioconv := IAv.INT_SGN_CONV
-- IntPolyConvs (int.ml 1090) and IntRingConvs (int.ml 1122-1147).
unsafe def INT_POLY_CONV : ioconv := IPc.INT_POLY_CONV
unsafe def INT_RING : term → IO (Except String thm) := IRg.INT_RING
unsafe def int_ideal_cofactors : List term → term → IO (Except String (List term)) :=
  IRg.int_ideal_cofactors
unsafe def INT_INTEGRAL : thm := IRg.INT_INTEGRAL
-- IntNumOfInt (int.ml 2070-2104): the nonnegative-integer -> natural map.
unsafe def num_of_int         : thm := INoI.num_of_int
unsafe def NUM_OF_INT_OF_NUM  : thm := INoI.NUM_OF_INT_OF_NUM
unsafe def INT_OF_NUM_OF_INT  : thm := INoI.INT_OF_NUM_OF_INT
unsafe def NUM_OF_INT         : thm := INoI.NUM_OF_INT
unsafe def NUM_OF_INT_ADD     : thm := INoI.NUM_OF_INT_ADD
unsafe def NUM_OF_INT_MUL     : thm := INoI.NUM_OF_INT_MUL
unsafe def NUM_OF_INT_POW     : thm := INoI.NUM_OF_INT_POW
-- IntNumNotions (int.ml 2107-2149): natural-number divisibility notions.
unsafe def num_divides        : thm := INoN.num_divides
unsafe def num_mod            : thm := INoN.num_mod
unsafe def num_congruent      : thm := INoN.num_congruent
unsafe def num_coprime        : thm := INoN.num_coprime
unsafe def num_gcd            : thm := INoN.num_gcd
unsafe def num_lcm            : thm := INoN.num_lcm
unsafe def NUM_TO_INT_CONV    : ioconv := INoN.NUM_TO_INT_CONV
-- IntArithRule (int.ml 2153-2189): the linear decision procedure for N.
unsafe def ARITH_RULE : term → IO (Except String thm) := IAr.ARITH_RULE
unsafe def ARITH_TAC : tactic := IAr.ARITH_TAC
unsafe def ASM_ARITH_TAC : tactic := IAr.ASM_ARITH_TAC
-- IntArith2 (int.ml 2192-2323): the ENHANCED int decision procedure.  These
-- SUPERSEDE the IntArith1 versions; the unnumbered `INT_ARITH`/`INT_ARITH_TAC`/
-- `ASM_INT_ARITH_TAC` names below alias the v2 forms, exactly as int.ml's later
-- text refers to the NAME `INT_ARITH` = the enhanced one (int.ml 2190 banner
-- "replacing first one").  The v1 forms remain as `INT_ARITH1`/`INT_ARITH_TAC1`
-- /`ASM_INT_ARITH_TAC1`.
unsafe def INT_ARITH2 : term → IO (Except String thm) := IA2.INT_ARITH2
unsafe def INT_ARITH_TAC2 : tactic := IA2.INT_ARITH_TAC2
unsafe def ASM_INT_ARITH_TAC2 : tactic := IA2.ASM_INT_ARITH_TAC2
unsafe def INT_ARITH : term → IO (Except String thm) := IA2.INT_ARITH2
unsafe def INT_ARITH_TAC : tactic := IA2.INT_ARITH_TAC2
unsafe def ASM_INT_ARITH_TAC : tactic := IA2.ASM_INT_ARITH_TAC2
-- IntMiscNat (int.ml 2326-2375): four miscellaneous natural-number lemmas.
unsafe def BINARY_INDUCT       : thm := IMn.BINARY_INDUCT
unsafe def NUM_CASES_BINARY    : thm := IMn.NUM_CASES_BINARY
unsafe def num_WF_DOWN         : thm := IMn.num_WF_DOWN
unsafe def INT_REM_REM_POW_MIN : thm := IMn.INT_REM_REM_POW_MIN
-- IntNumber (int.ml 2378-2566): the natural-number divisibility layer and
-- NUMBER_TAC (int.ml 2503)/NUMBER_RULE (int.ml 2520).
unsafe def NUM_GCD                 : thm := INum.NUM_GCD
unsafe def NUM_LCM                 : thm := INum.NUM_LCM
unsafe def CONG                    : thm := INum.CONG
unsafe def CONG_LMOD               : thm := INum.CONG_LMOD
unsafe def CONG_RMOD               : thm := INum.CONG_RMOD
unsafe def CONG_DIV2               : thm := INum.CONG_DIV2
unsafe def divides                 : thm := INum.divides
unsafe def DIVIDES_LE              : thm := INum.DIVIDES_LE
unsafe def DIVIDES_LE_STRONG       : thm := INum.DIVIDES_LE_STRONG
unsafe def DIVIDES_LE_IMP          : thm := INum.DIVIDES_LE_IMP
unsafe def PROPERLY_DIVIDES_LE_IMP : thm := INum.PROPERLY_DIVIDES_LE_IMP
unsafe def DIVIDES_ANTISYM         : thm := INum.DIVIDES_ANTISYM
unsafe def DIVIDES_ONE             : thm := INum.DIVIDES_ONE
unsafe def DIV_ADD                 : thm := INum.DIV_ADD
unsafe def DIVIDES_MOD             : thm := INum.DIVIDES_MOD
unsafe def DIVIDES_DIV_MULT        : thm := INum.DIVIDES_DIV_MULT
unsafe def DIV_BY_DIV              : thm := INum.DIV_BY_DIV
unsafe def DIVIDES_DIV_DIVIDES     : thm := INum.DIVIDES_DIV_DIVIDES
unsafe def DIVIDES_DIV_SELF        : thm := INum.DIVIDES_DIV_SELF
unsafe def DIVIDES_DIVIDES_DIV     : thm := INum.DIVIDES_DIVIDES_DIV
unsafe def DIVIDES_DIVIDES_DIV_EQ  : thm := INum.DIVIDES_DIVIDES_DIV_EQ
unsafe def DIVIDES_DIVIDES_DIV_IMP : thm := INum.DIVIDES_DIVIDES_DIV_IMP
unsafe def MULT_DIV                : thm := INum.MULT_DIV
unsafe def NUMBER_TAC : tactic := INum.NUMBER_TAC
unsafe def NUMBER_RULE : term → IO (Except String thm) := INum.NUMBER_RULE
unsafe def COPRIME_LMOD            : thm := INum.COPRIME_LMOD
unsafe def COPRIME_RMOD            : thm := INum.COPRIME_RMOD
unsafe def INT_CONG_NUM_EXISTS     : thm := INum.INT_CONG_NUM_EXISTS
unsafe def GCD                     : thm := INum.GCD
unsafe def coprime                 : thm := INum.coprime
-- IntPrime (int.ml 2571-2630): the definition of `prime` and five theorems.
unsafe def prime                            : thm := IPr.prime
unsafe def ONE_OR_PRIME                     : thm := IPr.ONE_OR_PRIME
unsafe def ONE_OR_PRIME_DIVIDES_OR_COPRIME  : thm :=
  IPr.ONE_OR_PRIME_DIVIDES_OR_COPRIME
unsafe def PRIME_COPRIME_EQ_NONDIVISIBLE    : thm :=
  IPr.PRIME_COPRIME_EQ_NONDIVISIBLE
unsafe def ZERO_ONE_OR_PRIME_DIVPROD        : thm := IPr.ZERO_ONE_OR_PRIME_DIVPROD
unsafe def ZERO_ONE_OR_PRIME                : thm := IPr.ZERO_ONE_OR_PRIME
-- RealZpow (int.ml 2633-2761): `real_zpow` and its 22 theorems.
unsafe def real_zpow        : thm := RZp.real_zpow
unsafe def REAL_POW_ZPOW    : thm := RZp.REAL_POW_ZPOW
unsafe def REAL_ZPOW_NUM    : thm := RZp.REAL_ZPOW_NUM
unsafe def REAL_ZPOW_0      : thm := RZp.REAL_ZPOW_0
unsafe def REAL_ZPOW_1      : thm := RZp.REAL_ZPOW_1
unsafe def REAL_ZPOW_2      : thm := RZp.REAL_ZPOW_2
unsafe def REAL_ZPOW_ONE    : thm := RZp.REAL_ZPOW_ONE
unsafe def REAL_ZPOW_NEG    : thm := RZp.REAL_ZPOW_NEG
unsafe def REAL_ZPOW_MINUS1 : thm := RZp.REAL_ZPOW_MINUS1
unsafe def REAL_ZPOW_ZERO   : thm := RZp.REAL_ZPOW_ZERO
unsafe def REAL_ZPOW_POW    : thm := RZp.REAL_ZPOW_POW
unsafe def REAL_INV_ZPOW    : thm := RZp.REAL_INV_ZPOW
unsafe def REAL_ZPOW_INV    : thm := RZp.REAL_ZPOW_INV
unsafe def REAL_ZPOW_ZPOW   : thm := RZp.REAL_ZPOW_ZPOW
unsafe def REAL_ZPOW_MUL    : thm := RZp.REAL_ZPOW_MUL
unsafe def REAL_ZPOW_DIV    : thm := RZp.REAL_ZPOW_DIV
unsafe def REAL_ZPOW_ADD    : thm := RZp.REAL_ZPOW_ADD
unsafe def REAL_ZPOW_SUB    : thm := RZp.REAL_ZPOW_SUB
unsafe def REAL_ZPOW_LE     : thm := RZp.REAL_ZPOW_LE
unsafe def REAL_ZPOW_LT     : thm := RZp.REAL_ZPOW_LT
unsafe def REAL_ZPOW_EQ_0   : thm := RZp.REAL_ZPOW_EQ_0
unsafe def REAL_ABS_ZPOW    : thm := RZp.REAL_ABS_ZPOW
unsafe def REAL_SGN_ZPOW    : thm := RZp.REAL_SGN_ZPOW

/- ---------------------------------------------------------------------- -/
/- sets.ml (hol_lib.ml 99): basic set theory (predicates as sets).        -/
/-                                                                        -/
/- Wired in sets.ml's own order.  `setupSetsInfixes` registers the        -/
/- FOURTEEN head infixes (IN, SUBSET, PSUBSET, INTER, UNION, DIFF,        -/
/- INSERT, DELETE, HAS_SIZE and the five cardinal comparisons) and MUST   -/
/- run EXACTLY ONCE and BEFORE `setupSetsCore`, whose definition bodies   -/
/- parse `x IN s`/`s UNION t`/... as those operators (sets.ml 18-32; a    -/
/- missing infix makes `x IN s` parse as `x` applied to `IN` and `s`).    -/
/- `setupSetsCore` then introduces EMPTY/INSERT_DEF/GSPEC/SETSPEC as real -/
/- constants - the parser desugars `{a,b,c}` and `{x|P}` to them as FREE  -/
/- VARIABLES until they exist (sets.ml 74).  So: infixes, then the core   -/
/- definitions, then the rest, each memoised behind an `IO.Ref` CAF that  -/
/- runs its setup exactly once and `panic!`s on error.  Getting the order -/
/- wrong parses set terms at the wrong type.  Sets loads AFTER int.ml, so -/
/- `ensurePrioritizeNum` has restored `num` priority: the set bodies use  -/
/- no overloaded arithmetic, so they elaborate correctly under it.  Public -/
/- accessors expose each bundle with its sets.ml line range; bare re-     -/
/- exports follow.                                                        -/
/- ---------------------------------------------------------------------- -/

/-- Guard for the fourteen head infixes (sets.ml 18-32): `parse_as_infix`
    for IN/SUBSET/PSUBSET/INTER/UNION/DIFF/INSERT/DELETE/HAS_SIZE and the five
    cardinal comparisons.  An `IO` ACTION with its own once-only flag, NOT a
    memoised `Unit` CAF: a `let _ := <caf>` does NOT force a Lean CAF, so a
    `Unit` CAF here would silently never run and every set
    operator would fail to parse as an infix.  `SC` awaits this so its
    definition bodies parse `IN`/`UNION`/`INTER`/... as the registered
    operators - exactly the `ensureIntInterface`/`ensureIntDivRemInfixes`
    /`ensureRealAxOverloads` precedent. -/
initialize theSetsInfixes : IO.Ref Bool ← IO.mkRef false

/-- Force the canonical `hol_lib.ml` load prefix, through int.ml.

    sets.ml line 12 is `needs "int.ml"`, and HOL Light's `needs` loads eagerly
    and in order, so by the time any line of sets.ml runs every file beneath it
    has executed.  Our CAFs are lazy, so a Sets setup forced under the wrong
    parser/overload state parses its terms at the wrong type and fails silently
    (the bundles are private CAFs).  The order below is load-bearing and must
    not be reordered: forcing only the tail (`ensurePrioritizeNum`) makes
    `RealThms5`/`9`/`11` panic (`linear_ineqs: no contradiction`,
    `MATCH_MP_TAC: No match`), because the real bundles must be built while
    `:real` is still the schematic default, before int.ml's overloads and its
    closing `prioritize_num`. -/
unsafe def ensureHolPrefixThroughInt : IO Unit := do
  -- ind_defs.ml 256: MONO_TAC's `IMP_REFL = ITAUT `!p. p ==> p`` (hol_lib.ml 70).
  let _ ← IO.mkRef (concl indAux.2.1)
  -- metis.ml (module Metis_rules) proves its RESOLVE/IMPL_NOT lemmas at load,
  -- and thecops.ml (module Hashek) runs `new_definition `hashek = T`` at
  -- load (hol_lib.ml 76-77, before pair.ml); `Cs` and `MtRules` build them.
  -- meson.ml 122: reset_consts' `false_tm = `F`` (Meson.reset_consts uses
  -- the constant directly).
  parseLoadQuotes ["F"]
  let _ ← IO.mkRef (concl MtRules.RESOLVE_1)
  let _ ← IO.mkRef (concl Cs.hashek.hashek_def)
  let _ ← IO.mkRef (concl Qs.selectLemma)                  -- quot.ml (hol_lib.ml 78)
  -- pair.ml 184-192 (hol_lib.ml 80, before nums.ml): CURRY, UNCURRY and
  -- PASSOC are defined at load, so they are in `the_definitions` in OCaml's
  -- order.
  let _ ← IO.mkRef (concl CURRY_DEF)
  let _ ← IO.mkRef (concl letTacPths.1)                    -- pair.ml 450 (LET_TAC)
  let _ ← the_compset                                       -- compute.ml 787
  -- NUM_RING FIRST.  Its setup proofs SEARCH over the currently-registered
  -- overloads, so forcing it before the real layer registers the `real` ones
  -- keeps that search small; forcing it AFTER blows up as
  -- `NUM_INTEGRAL: solve_goal: Too deep`.  (Same note as HolTest/IntTest.lean.)
  -- arith.ml (hol_lib.ml 86) must come first: without its infixes `a + b`
  -- does not parse and this force would silently not happen.
  let _ ← IO.mkRef (concl ADD_SYM)
  ensureArithProcs                                          -- arith.ml 1713-1904
  let _ ← IO.mkRef (concl WF)                              -- wf.ml
  let _ ← IO.mkRef (concl WfInductPths.1)                  -- wf.ml 420-440 (WF_INDUCT_TAC)
  -- calc_num.ml 1473, calc_int.ml 389-406, calc_rat.ml 389-420: these reduction
  -- conversions build a net from UNANNOTATED patterns (`x + y`, `x <= y`, ...)
  -- when their file LOADS, so the patterns take the types of that moment
  -- (`num` for calc_num, `real` for calc_int/calc_rat).  Session builds them on
  -- first use, so each is built here, at its file's position (as int.ml's are
  -- in `ensurePrioritizeNum`).  Calling one on `T` builds and caches its net.
  let tTm : term := .Const "T" (.Tyapp "bool" [])
  let _ ← IO.mkRef CnN.pre_tm                              -- calc_num.ml 211-1560
  match ← numRelConvIO with                                 -- calc_num.ml 1443
  | .ok _ => pure ()
  | .error e => panic! s!"ensureHolPrefixThroughInt: NUM_REL_CONV setup: {e}"
  let _ ← NUM_RED_CONV tTm                                  -- calc_num.ml 1473
  match ← numComputeConvIO with                             -- calc_num.ml 1487
  | .ok _ => pure ()
  | .error e => panic! s!"ensureHolPrefixThroughInt: NUM_COMPUTE_CONV setup: {e}"
  let _ ← IO.mkRef (concl NmzP.2)                          -- normalizer.ml 537-565
  -- grobner.ml: NUM_RING's setup proofs search over the registered overloads,
  -- so it must be built before realax.ml adds the `real` ones (after them it
  -- fails with `NUM_INTEGRAL: solve_goal: Too deep`).
  match ← numSimplifyConvIO with
  | .ok _ => pure ()
  | .error e => panic! s!"ensureHolPrefixThroughInt: NUM_SIMPLIFY_CONV setup: {e}"
  let _ ← IO.mkRef (concl NUM_INTEGRAL)
  match ← numRingIO with
  | .ok _ => pure ()
  | .error e => panic! s!"ensureHolPrefixThroughInt: NUM_RING setup: {e}"
  -- ind_types.ml 1421-1539 (UNWIND_CONV/MATCH_CONV): its `do_list
  -- extend_basic_convs` (1528) adds the _MATCH/_FUNCTION reductions to
  -- basic_convs at load, before lists.ml; forcing MATCH_CONV builds it.
  let _ ← MATCH_CONV tTm
  match ← forallUnwindIO with                              -- ind_types.ml 1540
  | .ok _ => pure ()
  | .error e => panic! s!"ensureHolPrefixThroughInt: FORALL_UNWIND_CONV setup: {e}"
  let _ ← IO.mkRef (concl listThms1.NOT_CONS_NIL)         -- lists.ml, in file order
  let _ ← IO.mkRef (concl listThms2.ALL_APPEND)
  let _ ← IO.mkRef (concl listsMono.MONO_ALL)
  let _ ← IO.mkRef listEvalConvs                           -- lists.ml 751-876
  -- lists.ml 884: `new_type_abbrev("string",`:char list`)`.  That runs when
  -- lists.ml LOADS, so by sets.ml every `:string` annotation expands to
  -- `:char list`.  In our translation the abbreviation is installed as a side
  -- effect of the `charType` CAF, so it must be forced BEFORE sets.ml's
  -- `ISPEC `LENGTH:string->num`` (sets.ml 3623), or `:string` is unknown and
  -- the term fails to typecheck.  Forcing here reproduces lists.ml's load-time
  -- effect at the right point in the bootstrap order.
  let _ ← IO.mkRef (concl char_INDUCT)                     -- lists.ml 881-884
  let _ ← IO.mkRef charStringMachinery                     -- lists.ml 886-1020
  let _ ← IO.mkRef (concl realArithLemmas.REAL_LTE_TOTAL)  -- realarith.ml
  let _ ← IO.mkRef RaC                                      -- realarith.ml 445-449
  let _ ← IO.mkRef (concl genRealArith2Ctx.pth_abs)         -- realarith.ml ABSMAXMIN
  let _ ← REAL_INT_RED_CONV tTm                             -- calc_int.ml 389
  let _ ← REAL_INT_COMPUTE_CONV tTm                         -- calc_int.ml 403
  -- real.ml: force RT1 first, then the three bundles that must be built
  -- while `:real` is still the schematic default (RT5, RT9, RT11).  Omitting
  -- them leaves them to be forced later, under int.ml's overloads, where they
  -- panic with `linear_ineqs: no contradiction` / `MATCH_MP_TAC: No match`.
  -- real.ml, every bundle in file order.
  let _ ← IO.mkRef (concl RT1.REAL_OF_NUM_LT)
  let _ ← IO.mkRef (concl RT2.REAL_EQ_ADD_LCANCEL_0)
  let _ ← IO.mkRef (concl RT3.REAL_LE_NEGR)
  let _ ← IO.mkRef (concl RT4.REAL_ABS_ZERO)
  let _ ← IO.mkRef (concl RT5.REAL_LE_MAX)
  let _ ← IO.mkRef (concl RBc.le_pth)                      -- REAL_LE_IMP/REAL_LET_IMP
  let _ ← IO.mkRef (concl RT6.REAL_ABS_MUL)
  let _ ← IO.mkRef (concl RT7.REAL_LT_LCANCEL_IMP)
  let _ ← IO.mkRef (concl RT8.REAL_POW_LE_1)
  let _ ← IO.mkRef (concl RT9.REAL_ARCH_SIMPLE)
  let _ ← IO.mkRef (concl RT10.real_sgn)
  let _ ← IO.mkRef (concl RT11.SQRT_0)
  let _ ← IO.mkRef (concl DECIMAL)                          -- calc_rat.ml 16
  -- calc_rat.ml 490: REAL_RING / real_ideal_cofactors.  Its `REAL_INTEGRAL`
  -- sub-proof ends in REAL_ARITH_TAC (calc_rat.ml 499), and like RealThms5/9/11
  -- the setup must be built while `:real` is still the schematic default: forced later,
  -- under int.ml's overloads, it dies with `linear_ineqs: no contradiction`.
  -- That degenerated REAL_RING, and because REAL_FIELD's
  -- `core_rule t = try REAL_RING t with Failure _ -> REAL_ARITH t`
  -- (calc_rat.ml 610) can only fall back when REAL_RING *fails* - not when its
  -- setup PANICS - REAL_FIELD then diverged instead of retrying, which is what
  -- hung sets.ml 3657's `FINITE_REAL_INTERVAL`.
  -- Build the REAL_RING setup (RRing), at calc_rat.ml's position.
  let r ← IO.mkRef RRing
  let _ ← r.get
  if (← theRealRingConvs.get).isNone then panic! "ensureHolPrefixThroughInt: RRing not built"
  -- calc_rat.ml 581: REAL_FIELD.  Its SETUP builds `ltLemma` via this file's own
  -- REAL_ARITH3 and an inline MESON lemma inside `easy_nz_conv`, so like
  -- REAL_RING it must be built while `:real` is still the schematic default.
  let _ ← IO.mkRef (concl RFT.REAL_LE_TRANS_LE)            -- calc_rat.ml 563-575
  match ← realFieldIO with
  | .ok _ => pure ()
  | .error e => panic! s!"ensureHolPrefixThroughInt: REAL_FIELD setup: {e}"
  let _ ← IO.mkRef (concl RShr.REAL_SHRINK_RANGE)          -- calc_rat.ml 634-689
  let _ ← REAL_RAT_RED_CONV tTm                             -- calc_rat.ml 407
  let _ ← REAL_RAT_COMPUTE_CONV tTm                         -- calc_rat.ml 414
  let _ ← IO.mkRef (concl int_of_num)                       -- int.ml
  -- int.ml, every bundle in file order.
  let _ ← IO.mkRef IntEx
  let _ ← IO.mkRef IntTb
  let _ ← IO.mkRef IntO
  let _ ← IO.mkRef IntKs
  let _ ← IO.mkRef IT1
  let _ ← IO.mkRef IT2
  let _ ← IO.mkRef IT3
  let _ ← IO.mkRef IT4
  let _ ← IO.mkRef IT5
  let _ ← IO.mkRef IT6
  let _ ← IO.mkRef IT7
  let _ ← IO.mkRef IT8
  let _ ← IO.mkRef IT9
  let _ ← IO.mkRef IT10
  let _ ← IO.mkRef IWl
  let _ ← IO.mkRef IA1
  let _ ← IO.mkRef IDm
  let _ ← IO.mkRef ICv
  let _ ← IO.mkRef IAv
  let _ ← IO.mkRef IPc
  let _ ← IO.mkRef IRg
  let _ ← IO.mkRef IDv
  let _ ← IO.mkRef ITc1
  let _ ← IO.mkRef IDr1
  let _ ← IO.mkRef IDrc
  let _ ← IO.mkRef IEo
  let _ ← IO.mkRef IRc
  let _ ← IO.mkRef IGl
  let _ ← IO.mkRef INoI
  let _ ← IO.mkRef INoN
  let _ ← IO.mkRef IAr
  let _ ← IO.mkRef IA2
  let _ ← IO.mkRef IMn
  let _ ← IO.mkRef INum
  let _ ← IO.mkRef IPr
  let _ ← IO.mkRef RZp
  ensurePrioritizeNum                                       -- int.ml 2765, LAST
  pure ()

private unsafe def ensureSetsInfixes : IO Unit := do
  if ← theSetsInfixes.get then pure () else do
    -- Reproduce sets.ml 12's `needs "int.ml"` before registering any infix or
    -- parsing any set term.  See `ensureHolPrefixThroughInt` for the defect
    -- this prevents and why the order matters.
    ensureHolPrefixThroughInt
    HolMath.Sets.setupSetsInfixes
    theSetsInfixes.set true

/-- Once-only guard for the FIFTEENTH `parse_as_infix` of `sets.ml`:
    `CROSS 22 right` (sets.ml 2732).  Like `ensureSetsInfixes` this is an `IO`
    ACTION with its own flag, NOT a memoised `Unit` CAF: a
    `let _ := <caf>` would not force it, so `CROSS` would parse as a free
    variable / juxtaposition instead of the infix constant.  `SCross` awaits
    this (and `ensureSetsInfixes` runs first), so the `CROSS` `new_definition`
    body and every `s CROSS t` statement in that bundle parse `CROSS` as the
    registered infix. -/
initialize theSetsCrossInfix : IO.Ref Bool ← IO.mkRef false

private unsafe def ensureSetsCrossInfix : IO Unit := do
  if ← theSetsCrossInfix.get then pure () else do
    ensureSetsInfixes
    HolMath.Sets.setupSetsCrossInfix
    theSetsCrossInfix.set true

/-- Once-only guard for the FIFTEENTH and SIXTEENTH `parse_as_infix` calls of
    `sets.ml`: `UNION_OF 20 right` and `INTERSECTION_OF 20 right`
    (sets.ml 4001-4002).  Like `ensureSetsCrossInfix` this is an `IO` ACTION
    with its own flag, NOT a memoised `Unit` CAF: a
    `let _ := <caf>` would not force it, so `P UNION_OF Q` / `P INTERSECTION_OF
    Q` would parse as free variables / juxtaposition instead of the infix
    constants.  `SUO` awaits this (and `ensureSetsInfixes`/`ensureSetsCrossInfix`
    run first), so the two `UNION_OF`/`INTERSECTION_OF` `new_definition` bodies
    and every `P UNION_OF Q`/`P INTERSECTION_OF Q` statement in that bundle
    parse the symbols as the registered infixes. -/
initialize theSetsUnionOfInfix : IO.Ref Bool ← IO.mkRef false

private unsafe def ensureSetsUnionOfInfix : IO Unit := do
  if ← theSetsUnionOfInfix.get then pure () else do
    ensureSetsInfixes
    ensureSetsCrossInfix
    HolMath.Sets.setupSetsUnionOfInfix
    theSetsUnionOfInfix.set true

/-- Once-only guard for the SEVENTEENTH and EIGHTEENTH `parse_as_infix` calls
    of `sets.ml`: `has_inf 12 right` and `has_sup 12 right` (sets.ml 5030-5031),
    the LAST TWO of the file.  Like `ensureSetsUnionOfInfix` this is an `IO`
    ACTION with its own flag, NOT a memoised `Unit` CAF: a
    `let _ := <caf>` would not force it, so `s has_inf b` / `s has_sup b` would
    parse as free variables / juxtaposition instead of the infix constants.
    `SISup` awaits this (and the three earlier infix guards run first, in load
    order), so the two `has_inf`/`has_sup` `new_definition` bodies and every
    `s has_inf b`/`s has_sup b` statement in that bundle parse the symbols as
    the registered infixes.  Load order is critical here, so it is chained
    EXACTLY like the other three, forced in file order by `ensureSets`. -/
initialize theSetsHasInfSupInfix : IO.Ref Bool ← IO.mkRef false

private unsafe def ensureSetsHasInfSupInfix : IO Unit := do
  if ← theSetsHasInfSupInfix.get then pure () else do
    ensureSetsInfixes
    ensureSetsCrossInfix
    ensureSetsUnionOfInfix
    HolMath.Sets.setupSetsHasInfSupInfix
    theSetsHasInfSupInfix.set true

/-- Cache for `SetsCore` (sets.ml 34-170): `IN`, `EXTENSION`, `GSPEC`,
    `SETSPEC`, `IN_ELIM_THM`, `EMPTY`, `INSERT_DEF`, `UNIV`, the union/
    intersection/difference/insert/delete operators, `SUBSET`, `PSUBSET`,
    `DISJOINT`, `SING`, the `FINITE` inductive triple, `INFINITE`, `IMAGE`,
    `INJ`/`SURJ`/`BIJ`, `CHOICE` and `REST`.  Each `new_definition` (and the
    `new_inductive_definition` for FINITE) CREATES A CONSTANT, so NOT
    idempotent - this once-only CAF guarantees it runs once.  Forces the head
    infixes first, so `x IN s`/`s UNION t`/... in the bodies parse as
    operators and `{a,b,c}`/`{x|P}` desugar onto the freshly-real EMPTY/
    INSERT_DEF/GSPEC/SETSPEC. -/
initialize theSetsCore : IO.Ref (Option HolMath.Sets.SetsCore) ← IO.mkRef none

private unsafe def SC : HolMath.Sets.SetsCore :=
  match unsafeIO (do
    match ← theSetsCore.get with
    | some d => pure d
    | none => do
      ensureSetsInfixes
      match ← (HolMath.Sets.setupSetsCore MESON_TAC
                 new_definition new_inductive_definition).run with
      | .ok d => do theSetsCore.set (some d); pure d
      | .error e => panic! s!"setupSetsCore failed: {e}") with
  | .ok d => d | _ => panic! "Session.SC: setupSetsCore not run"

/-- Cache for `SetsProps` (sets.ml 171-308): the twenty-four basic membership
    lemmas (`NOT_IN_EMPTY`, `IN_UNION`, `IN_INTER`, `IN_IMAGE`, the
    `FORALL_IN_*`/`EXISTS_IN_*` clauses, ...) that are SET_TAC's raw material.
    Pure over `SC`; cached for reuse. -/
initialize theSetsProps : IO.Ref (Option HolMath.Sets.SetsProps) ← IO.mkRef none

private unsafe def SP : HolMath.Sets.SetsProps :=
  match unsafeIO (do
    match ← theSetsProps.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Sets.setupSetsProps SC MESON_TAC).run with
      | .ok d => do theSetsProps.set (some d); pure d
      | .error e => panic! s!"setupSetsProps failed: {e}") with
  | .ok d => d | _ => panic! "Session.SP: setupSetsProps not run"

/-- Cache for `SetsTactics` (sets.ml 309-355): `CHOICE_DEF` and the first
    SET_TAC consumers `NOT_EQUAL_SETS`, `INSERT_RESTRICT`, `UNIV_1`.  Pure over
    `SC`/`SP`; cached for reuse. -/
initialize theSetsTactics : IO.Ref (Option HolMath.Sets.SetsTactics) ← IO.mkRef none

private unsafe def STc : HolMath.Sets.SetsTactics :=
  match unsafeIO (do
    match ← theSetsTactics.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Sets.setupSetsTactics SC SP Tv MESON_TAC).run with
      | .ok d => do theSetsTactics.set (some d); pure d
      | .error e => panic! s!"setupSetsTactics failed: {e}") with
  | .ok d => d | _ => panic! "Session.STc: setupSetsTactics not run"

/-- Cache for `SetsInclusion` (sets.ml 356-475): the emptiness/universality/
    subset/psubset lemmas.  Pure over `SC`/`SP`; cached for reuse. -/
initialize theSetsInclusion : IO.Ref (Option HolMath.Sets.SetsInclusion) ← IO.mkRef none

private unsafe def SIn : HolMath.Sets.SetsInclusion :=
  match unsafeIO (do
    match ← theSetsInclusion.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Sets.setupSetsInclusion SC SP MESON_TAC).run with
      | .ok d => do theSetsInclusion.set (some d); pure d
      | .error e => panic! s!"setupSetsInclusion failed: {e}") with
  | .ok d => d | _ => panic! "Session.SIn: setupSetsInclusion not run"

/-- Cache for `SetsOperators` (sets.ml 476-855): the union/intersection/
    disjoint/difference algebra.  Pure over `SC`/`SP`; cached for reuse. -/
initialize theSetsOperators : IO.Ref (Option HolMath.Sets.SetsOperators) ← IO.mkRef none

private unsafe def SOp : HolMath.Sets.SetsOperators :=
  match unsafeIO (do
    match ← theSetsOperators.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Sets.setupSetsOperators SC SP MESON_TAC MESON).run with
      | .ok d => do theSetsOperators.set (some d); pure d
      | .error e => panic! s!"setupSetsOperators failed: {e}") with
  | .ok d => d | _ => panic! "Session.SOp: setupSetsOperators not run"

/-- Cache for `SetsInsertDelete` (sets.ml 856-950): the insert/delete algebra.
    Pure over `SC`/`SP`/`SIn`; cached for reuse. -/
initialize theSetsInsertDelete : IO.Ref (Option HolMath.Sets.SetsInsertDelete) ← IO.mkRef none

private unsafe def SID : HolMath.Sets.SetsInsertDelete :=
  match unsafeIO (do
    match ← theSetsInsertDelete.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Sets.setupSetsInsertDelete SC SP SIn MESON_TAC).run with
      | .ok d => do theSetsInsertDelete.set (some d); pure d
      | .error e => panic! s!"setupSetsInsertDelete failed: {e}") with
  | .ok d => d | _ => panic! "Session.SID: setupSetsInsertDelete not run"

/-- Cache for `SetsUnions` (sets.ml UNIONS block): the `UNIONS` clauses.  Pure
    over `SC`/`SP`; cached for reuse. -/
initialize theSetsUnions : IO.Ref (Option HolMath.Sets.SetsUnions) ← IO.mkRef none

private unsafe def SUn : HolMath.Sets.SetsUnions :=
  match unsafeIO (do
    match ← theSetsUnions.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Sets.setupSetsUnions SC SP MESON_TAC).run with
      | .ok d => do theSetsUnions.set (some d); pure d
      | .error e => panic! s!"setupSetsUnions failed: {e}") with
  | .ok d => d | _ => panic! "Session.SUn: setupSetsUnions not run"

/-- Cache for `SetsInters` (sets.ml INTERS block): the `INTERS` clauses.  Pure
    over `SC`/`SP`; cached for reuse. -/
initialize theSetsInters : IO.Ref (Option HolMath.Sets.SetsInters) ← IO.mkRef none

private unsafe def SIt : HolMath.Sets.SetsInters :=
  match unsafeIO (do
    match ← theSetsInters.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Sets.setupSetsInters SC SP MESON_TAC).run with
      | .ok d => do theSetsInters.set (some d); pure d
      | .error e => panic! s!"setupSetsInters failed: {e}") with
  | .ok d => d | _ => panic! "Session.SIt: setupSetsInters not run"

/-- Cache for `SetsImage` (sets.ml 951-1150 IMAGE block): the `IMAGE` algebra.
    Pure over `SC`/`SP`/`SIn`; threads the `I` combinator definition `I_DEF`.
    Cached for reuse. -/
initialize theSetsImage : IO.Ref (Option HolMath.Sets.SetsImage) ← IO.mkRef none

private unsafe def SIm : HolMath.Sets.SetsImage :=
  match unsafeIO (do
    match ← theSetsImage.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Sets.setupSetsImage SC SP SIn Tv I_DEF
                 MESON_TAC ASM_MESON_TAC).run with
      | .ok d => do theSetsImage.set (some d); pure d
      | .error e => panic! s!"setupSetsImage failed: {e}") with
  | .ok d => d | _ => panic! "Session.SIm: setupSetsImage not run"

/-- Cache for `SetsMisc` (sets.ml misc/GSPEC block): the `EMPTY_GSPEC`/
    `IN_GSPEC`/`SET_PAIR_THM`/saturated-image family.  Pure over the operator,
    inters, insert/delete and image bundles; cached for reuse. -/
initialize theSetsMisc : IO.Ref (Option HolMath.Sets.SetsMisc) ← IO.mkRef none

private unsafe def SMi : HolMath.Sets.SetsMisc :=
  match unsafeIO (do
    match ← theSetsMisc.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Sets.setupSetsMisc SC SP SIn SOp SIt SID SIm
                 Pr MESON_TAC).run with
      | .ok d => do theSetsMisc.set (some d); pure d
      | .error e => panic! s!"setupSetsMisc failed: {e}") with
  | .ok d => d | _ => panic! "Session.SMi: setupSetsMisc not run"

/-- Cache for `SetsInduct` (sets.ml stronger-induction block):
    `FINITE_INDUCT_STRONG`.  Pure over `SC`/`SP`; cached for reuse. -/
initialize theSetsInduct : IO.Ref (Option HolMath.Sets.SetsInduct) ← IO.mkRef none

private unsafe def SInd : HolMath.Sets.SetsInduct :=
  match unsafeIO (do
    match ← theSetsInduct.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Sets.setupSetsInduct SC SP MESON_TAC).run with
      | .ok d => do theSetsInduct.set (some d); pure d
      | .error e => panic! s!"setupSetsInduct failed: {e}") with
  | .ok d => d | _ => panic! "Session.SInd: setupSetsInduct not run"

/-- Cache for `SetsFunctions` (sets.ml 951-1382 function block): the
    injectivity/surjectivity/bijection and factoring lemmas.  Pure over
    `SC`/`SP`; cached for reuse. -/
initialize theSetsFunctions : IO.Ref (Option HolMath.Sets.SetsFunctions) ← IO.mkRef none

private unsafe def SFn : HolMath.Sets.SetsFunctions :=
  match unsafeIO (do
    match ← theSetsFunctions.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Sets.setupSetsFunctions SC SP Tv
                 MESON_TAC ASM_MESON_TAC MESON).run with
      | .ok d => do theSetsFunctions.set (some d); pure d
      | .error e => panic! s!"setupSetsFunctions failed: {e}") with
  | .ok d => d | _ => panic! "Session.SFn: setupSetsFunctions not run"

/-- Cache for `SetsFinite` (sets.ml 1383-1796): the finite-set combining
    theorems (`FINITE_EMPTY`, `FINITE_SUBSET`, `FINITE_UNION`, the `FINITE`/
    `INFINITE` IMAGE family, the transitivity-chain lemmas).  Threads the
    earlier Sets bundles plus `SInd` (`FINITE_INDUCT_STRONG`); pure over them,
    cached for reuse. -/
initialize theSetsFinite : IO.Ref (Option HolMath.Sets.SetsFinite) ← IO.mkRef none

private unsafe def SFin : HolMath.Sets.SetsFinite :=
  match unsafeIO (do
    match ← theSetsFinite.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Sets.setupSetsFinite SC SP SIn SOp SID SUn SIt SIm SMi
                 SFn SInd MESON_TAC ASM_MESON_TAC MESON
                 ASM_METIS_TAC).run with
      | .ok d => do theSetsFinite.set (some d); pure d
      | .error e => panic! s!"setupSetsFinite failed: {e}") with
  | .ok d => d | _ => panic! "Session.SFin: setupSetsFinite not run"

/-- Cache for `SetsRecursion` (sets.ml 1799-1988): the finite-set fold
    machinery `FINREC`/`ITSET`/`FINITE_RECURSION`, credited in the OCaml to
    Ching-Tsun (archive 713).  Threads the earlier Sets bundles plus `SFin`
    (`FINITE_SUBSET`/`FINITE_DELETE_IMP`), `SInd` (`FINITE_INDUCT_STRONG`) and
    `Nm` (`num_RECURSION`/`num_INDUCTION`); the `FINREC` `new_recursive_def`
    and the `ITSET` `new_definition` are injected.  Cached for reuse. -/
initialize theSetsRecursion : IO.Ref (Option HolMath.Sets.SetsRecursion) ← IO.mkRef none

private unsafe def SRec : HolMath.Sets.SetsRecursion :=
  match unsafeIO (do
    match ← theSetsRecursion.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Sets.setupSetsRecursion SC SP SID SFin SInd Nm
                 MESON_TAC ASM_MESON_TAC SELECT_CONV
                 new_recursive_definition new_definition).run with
      | .ok d => do theSetsRecursion.set (some d); pure d
      | .error e => panic! s!"setupSetsRecursion failed: {e}") with
  | .ok d => d | _ => panic! "Session.SRec: setupSetsRecursion not run"

/-- Cache for `SetsCard` (sets.ml 1991-2243): finite cardinality (`CARD`,
    `CARD_CLAUSES`, `CARD_UNION`, ...), the delete-choice induction principle
    `FINITE_INDUCT_DELETE`, the relational `HAS_SIZE` predicate with its
    rewrite form `HAS_SIZE_CLAUSES`, and the `HAS_SIZE_CONV` numeral-expansion
    conversion.  Threads the earlier Sets bundles plus `SFin`/`SInd`/`SRec`
    and the arithmetic theorems/rules/conversions; `CARD` and `HAS_SIZE` are
    injected `new_definition`s.  The `HAS_SIZE_CONV` rewrite nets are built
    once inside the builder, and this `IO.Ref` memoises the whole bundle so
    they are built at most once per process. -/
initialize theSetsCard : IO.Ref (Option HolMath.Sets.SetsCard) ← IO.mkRef none

private unsafe def SCard : HolMath.Sets.SetsCard :=
  match unsafeIO (do
    match ← theSetsCard.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Sets.setupSetsCard SC SP SIn SOp SID SUn SFin SInd
                 SRec MESON_TAC ASM_MESON_TAC
                 new_definition ADD_CLAUSES MULT_CLAUSES SUC_INJ NOT_SUC
                 SUC_SUB1 ARITH ARITH_RULE ARITH_TAC WF_INDUCT_TAC
                 num_CONV).run with
      | .ok d => do theSetsCard.set (some d); pure d
      | .error e => panic! s!"setupSetsCard failed: {e}") with
  | .ok d => d | _ => panic! "Session.SCard: setupSetsCard not run"

/-- Cache for `SetsCard2` (sets.ml 2244-2652): cardinality of unions and
    images, choosing a smaller subset of a given size, and the parity of the
    fixed-point set of an involution.  Threads the earlier Sets bundles plus
    `SCard` and the arithmetic theorems/rules/conversions. -/
initialize theSetsCard2 : IO.Ref (Option HolMath.Sets.SetsCard2) ← IO.mkRef none

private unsafe def SCard2 : HolMath.Sets.SetsCard2 :=
  match unsafeIO (do
    match ← theSetsCard2.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Sets.setupSetsCard2 SC SP SIn SOp SUn SIm SMi
                 SFin SInd SFn SCard MESON_TAC ASM_MESON_TAC MESON
                 LE_TRANS LET_TRANS LE_ANTISYM LE_REFL LT_REFL LT_LE LE_SUC
                 LE_0 LE_ADD2 LE_ADD_LCANCEL EQ_IMP_LE ADD_EQ_0
                 SUC_SUB1 num_WF EVEN_ADD EVEN_SUB ARITH
                 ARITH_RULE ARITH_TAC ASM_ARITH_TAC INDUCT_TAC).run with
      | .ok d => do theSetsCard2.set (some d); pure d
      | .error e => panic! s!"setupSetsCard2 failed: {e}") with
  | .ok d => d | _ => panic! "Session.SCard2: setupSetsCard2 not run"

/-- Cache for `SetsCross` (sets.ml 2653-2924): the cardinality-of-product
    theorems and the Cartesian product operator `CROSS` with its algebra.
    Threads the earlier Sets bundles plus `SCard`/`SCard2` and the pair
    bundle `Pr`.  The `CROSS` `new_definition` CREATES A CONSTANT (so NOT
    idempotent - the `IO.Ref` guarantees it runs once), and its infix fixity
    is registered by `ensureSetsCrossInfix`, which this accessor forces FIRST
    so the definition body and every `s CROSS t` statement parse `CROSS` as
    the registered infix. -/
initialize theSetsCross : IO.Ref (Option HolMath.Sets.SetsCross) ← IO.mkRef none

private unsafe def SCross : HolMath.Sets.SetsCross :=
  match unsafeIO (do
    match ← theSetsCross.get with
    | some d => pure d
    | none => do
      ensureSetsCrossInfix
      match ← (HolMath.Sets.setupSetsCross SC SP SIn SIm SMi SFin SInd
                 SCard SCard2 Pr MESON_TAC ASM_MESON_TAC
                 new_definition MULT_CLAUSES).run with
      | .ok d => do theSetsCross.set (some d); pure d
      | .error e => panic! s!"setupSetsCross failed: {e}") with
  | .ok d => d | _ => panic! "Session.SCross: setupSetsCross not run"

/-- Cache for `SetsFunspace` (sets.ml 2925-3324): extensional functions,
    restriction, the dependent function space / Cartesian product, the product
    of a family of maps, and the disjoint-union construction.  Threads the
    core Sets bundles plus `Pr`, `T`, `Tv` (`o_THM`) and the injected `o_DEF`.
    Its `ARB`/`EXTENSIONAL`/`RESTRICTION`/`cartesian_product`/`product_map`/
    `disjoint_union` `new_definition`s CREATE CONSTANTS (so NOT idempotent -
    the `IO.Ref` guarantees a single run). -/
initialize theSetsFunspace : IO.Ref (Option HolMath.Sets.SetsFunspace) ← IO.mkRef none

private unsafe def SFun : HolMath.Sets.SetsFunspace :=
  match unsafeIO (do
    match ← theSetsFunspace.get with
    | some d => pure d
    | none => do
      match ← (HolMath.Sets.setupSetsFunspace SC SP SIn SIm SMi Pr Tv
                 o_DEF MESON_TAC ASM_MESON_TAC new_definition).run with
      | .ok d => do theSetsFunspace.set (some d); pure d
      | .error e => panic! s!"setupSetsFunspace failed: {e}") with
  | .ok d => d | _ => panic! "Session.SFun: setupSetsFunspace not run"

/-- Cache for `SetsFunspace2` (sets.ml 3325-3548): cardinality of
    bounded-support function spaces, of type `bool`, and hence of the powerset.
    Threads the core Sets bundles plus `SFin`/`SCard`/`SCard2`/`SCross`, `Pr`,
    `T`, the MESON / `MATCH_MP` / `REWRITE_RULE` / `TAUT` helpers,
    `GEN_BETA_CONV`, `INDUCT_TAC` and the arithmetic theorems.  Pure `prove`s
    (no `new_definition`), so idempotent; the `IO.Ref` just avoids recomputing. -/
initialize theSetsFunspace2 : IO.Ref (Option HolMath.Sets.SetsFunspace2) ← IO.mkRef none

private unsafe def SFun2 : HolMath.Sets.SetsFunspace2 :=
  match unsafeIO (do
    match ← theSetsFunspace2.get with
    | some d => pure d
    | none => do
      match ← (HolMath.Sets.setupSetsFunspace2 SC SP SIn SOp SID SIm SMi
                 SFin SCard SCard2 SCross Pr MESON_TAC ASM_MESON_TAC
                 GEN_BETA_CONV INDUCT_TAC
                 EXP LE_TRANS LE_MULT_RCANCEL LE_1 ARITH).run with
      | .ok d => do theSetsFunspace2.set (some d); pure d
      | .error e => panic! s!"setupSetsFunspace2 failed: {e}") with
  | .ok d => d | _ => panic! "Session.SFun2: setupSetsFunspace2 not run"

/-- Cache for `SetsInfinite` (sets.ml 3554-3697): the infinitude of the
    numbers, of strings, and of non-trivial real intervals.  Pure `prove`s, so
    the `IO.Ref` just avoids recomputing.

    `string_INFINITE` mentions `(:string)`, so before running the proofs this
    forces the char/string layer (`char_INDUCT`) and installs the lists.ml 884
    `new_type_abbrev("string",`:char list`)` - the parser expands `string` to
    `char list` while parsing the goal, exactly as HOL Light does once lists.ml
    has loaded. -/
initialize theSetsInfinite : IO.Ref (Option HolMath.Sets.SetsInfinite) ← IO.mkRef none

private unsafe def SInf : HolMath.Sets.SetsInfinite :=
  match unsafeIO (do
    match ← theSetsInfinite.get with
    | some d => pure d
    | none => do
      -- Install the `string` type abbreviation (lists.ml 884) so the parser
      -- expands `(:string)` / `LENGTH:string->num` to `char list` forms.
      let _ ← IO.mkRef (concl char_INDUCT)
      match ← HolCore.Parser.parse_type "char list" with
      | .error e => panic! s!"SInf: string abbrev parse: {e}"
      | .ok ty => new_type_abbrev "string" ty
      match ← (HolMath.Sets.setupSetsInfinite SC SP SIn SMi SFin SCard SInd
                 MESON_TAC INDUCT_TAC
                 REAL_ARITH2 REAL_FIELD REAL_ARITH_TAC
                 Ar2.LT Ar2.LE Ar1.ADD1 Ar2.LT_SUC_LE Ar3.NOT_LT Ar3.LT_REFL
                 Ar3.LE_CASES Ar3.LE_TRANS Ar3.NOT_LE Ar3.LT_IMP_LE Ar2.LE_SUC_LT
                 listThms1.LENGTH_REPLICATE
                 RaL.REAL_NOT_LT RT3.REAL_LT_ADDR RT8.REAL_LT_DIV RaL.REAL_SUB_LT
                 RT7.REAL_LT_LDIV_EQ RT1.REAL_LT_MUL Rl.REAL_OF_NUM_EQ
                 Rl.REAL_LE_ANTISYM Rl.REAL_LE_REFL).run with
      | .ok d => do theSetsInfinite.set (some d); pure d
      | .error e => panic! s!"setupSetsInfinite failed: {e}") with
  | .ok d => d | _ => panic! "Session.SInf: setupSetsInfinite not run"

/-- Cache for `SetsList` (sets.ml 3697-3997): finite-set indexing and
    enumeration of subsets of N, the mapping between finite sets and lists
    (`set_of_list`/`list_of_set` are INTRODUCED HERE, not in Lists.lean), and
    the `pairwise` property.  Bridges to the list theory, so it threads the
    list `LENGTH`/`MEM`/`MAP` definitions and the `NOT_CONS_NIL`/`CONS_11`/
    `LENGTH_EQ_NIL`/`MEM_APPEND` theorems, the stored `list_INDUCT`/
    `list_RECURSION` and the `list_INDUCT'` behind `LIST_INDUCT_TAC`, plus the
    core Sets bundles, `SInf` (`num_FINITE`/`FINITE_NUMSEG_LT`/`num_INFINITE`),
    `Ar4`/`Wf` (`num_WOP`/`num_MAX`/`WLOG_LT`/`num_WF`, `WF_REC_EXISTS`/
    `WF_num`), `ARITH_RULE`/`TAUT`, `prove_recursive_functions_exist` and the
    `COND_ELIM_CONV`/`SELECT_CONV` conversions.  Pure `prove`s / definitions,
    so idempotent; the `IO.Ref` just avoids recomputing. -/
initialize theSetsList : IO.Ref (Option HolMath.Sets.SetsList) ← IO.mkRef none

private unsafe def SL : HolMath.Sets.SetsList :=
  match unsafeIO (do
    match ← theSetsList.get with
    | some d => pure d
    | none => do
      match ← (HolMath.Sets.setupSetsList SC SP SIn SUn SIm SID SInd SFin
                 SCard SInf Nm Ar4 Wf MESON_TAC ASM_MESON_TAC
                 INDUCT_TAC
                 list_INDUCT list_INDUCT' list_RECURSION
                 listDefs.LENGTH listDefs.MEM listDefs.MAP
                 listThms1.NOT_CONS_NIL listThms1.CONS_11
                 listThms1.LENGTH_EQ_NIL listThms1.MEM_APPEND
                 Ar2.LT Ar3.LT_IMP_LE Ar3.LE_LT Ar3.LE_ANTISYM Ar3.NOT_LT
                 Ar3.NOT_LE Ar2.LE_0 Ar3.LT_REFL Nm.SUC_INJ Nm.NOT_SUC
                 ARITH_RULE prove_recursive_functions_exist
                 COND_ELIM_CONV SELECT_CONV
                 new_recursive_definition new_definition).run with
      | .ok d => do theSetsList.set (some d); pure d
      | .error e => panic! s!"setupSetsList failed: {e}") with
  | .ok d => d | _ => panic! "Session.SL: setupSetsList not run"

/-- Cache for `SetsUnionOf` (sets.ml 3998-4364): the `UNION_OF`/
    `INTERSECTION_OF` combinators and their ARBITRARY and FINITE cases.  The
    two operators' infix fixity is registered by `ensureSetsUnionOfInfix`,
    which this accessor forces FIRST so the `new_definition` bodies and every
    `P UNION_OF Q`/`P INTERSECTION_OF Q` statement parse the symbols as
    infixes.  Threads the core Sets bundles plus `SOp`/`SUn`/`SIt`/`SIm`/`SMi`/
    `SFin`/`SCross` and `T`; pure `prove`s over them, so the `IO.Ref` just
    avoids recomputing. -/
initialize theSetsUnionOf : IO.Ref (Option HolMath.Sets.SetsUnionOf) ← IO.mkRef none

private unsafe def SUO : HolMath.Sets.SetsUnionOf :=
  match unsafeIO (do
    match ← theSetsUnionOf.get with
    | some d => pure d
    | none => do
      ensureSetsUnionOfInfix
      match ← (HolMath.Sets.setupSetsUnionOf SC SP SOp SUn SIt SIm SMi
                 SFin SCross ETA_AX MESON_TAC MESON
                 new_definition).run with
      | .ok d => do theSetsUnionOf.set (some d); pure d
      | .error e => panic! s!"setupSetsUnionOf failed: {e}") with
  | .ok d => d | _ => panic! "Session.SUO: setupSetsUnionOf not run"

/-- Cache for `SetsCardComp` (sets.ml 4365-4695): the finish of the
    set_of_list cardinality section, the classic finite
    injectivity/surjectivity/bijection theorems, `WF_FINITE`/`WF_PSUBSET`, and
    the cardinal-comparison definitions `le_c`/`lt_c`/`eq_c`/`ge_c`/`gt_c` with
    `LE_C`/`GE_C`/`COUNTABLE`.  This range registers NO new `parse_as_infix`:
    the five cardinal comparisons were declared by `ensureSetsInfixes`
    (sets.ml 28-32).  Threads the earlier Sets bundles plus `SCard2`/`SFun2`/
    `SFn`/`SL`/`SInf`, the `Ar2`/`Ar3`/`Ar9`/`Nm`/`Wf` arithmetic and
    wellfoundedness theorems, the list `ALL`/`PAIRWISE`/`ALL_MEM`/`LENGTH`, and
    `LIST_INDUCT_TAC`/`ASM_ARITH_TAC`/`ARITH_RULE`/`TAUT`.  Pure `prove`s /
    definitions, so the `IO.Ref` just avoids recomputing. -/
initialize theSetsCardComp : IO.Ref (Option HolMath.Sets.SetsCardComp) ← IO.mkRef none

private unsafe def SCC : HolMath.Sets.SetsCardComp :=
  match unsafeIO (do
    match ← theSetsCardComp.get with
    | some d => pure d
    | none => do
      match ← (HolMath.Sets.setupSetsCardComp SC SP SIn SIm SInd SFin
                 SCard SCard2 SFun2 SFn SL SInf Nm Ar2 Ar3 Ar9 Wf
                 MESON_TAC ASM_MESON_TAC
                 (HolMath.Lists.LIST_INDUCT_TAC list_INDUCT')
                 ASM_ARITH_TAC ARITH_RULE
                 listDefs.ALL listDefs.PAIRWISE listThms1.ALL_MEM
                 listDefs.LENGTH new_definition).run with
      | .ok d => do theSetsCardComp.set (some d); pure d
      | .error e => panic! s!"setupSetsCardComp failed: {e}") with
  | .ok d => d | _ => panic! "Session.SCC: setupSetsCardComp not run"

/-- Cache for `SetsSup` (sets.ml 4698-5027): the `sup`/`inf` definitions and
    their 49 surrounding `prove`s.  This range registers NO new
    `parse_as_infix`.  Threads the core Sets bundles plus the real theorems
    (`Rl`/`RaL`/`realThms2`/`realThms4`/`realThms5`/`CiT` fields) and the
    `SELECT_CONV`/`REAL_ARITH2`/`REAL_ARITH_TAC` helpers; pure `prove`s /
    definitions, so the `IO.Ref` just avoids recomputing. -/
initialize theSetsSup : IO.Ref (Option HolMath.Sets.SetsSup) ← IO.mkRef none

private unsafe def SSup : HolMath.Sets.SetsSup :=
  match unsafeIO (do
    match ← theSetsSup.get with
    | some d => pure d
    | none => do
      match ← (HolMath.Sets.setupSetsSup SC SP
                 MESON_TAC ASM_MESON_TAC REFUTE_THEN
                 INTRO_TAC SELECT_CONV
                 REAL_ARITH2 REAL_ARITH_TAC IMP_CONJ
                 SIn.MEMBER_NOT_EMPTY SP.IN_IMAGE SFin.FINITE_INSERT
                 SFin.FINITE_EMPTY SID.NOT_INSERT_EMPTY
                 SP.NOT_IN_EMPTY SP.IN_INSERT SP.IN_SING SP.FORALL_IN_INSERT
                 SP.FORALL_IN_UNION
                 SC.FINITE_RULES SInd.FINITE_INDUCT_STRONG
                 Rl.REAL_COMPLETE Rl.REAL_LE_TOTAL Rl.REAL_LE_TRANS
                 Rl.REAL_LE_ANTISYM Rl.REAL_LE_REFL
                 RaL.REAL_LTE_TRANS RaL.REAL_LET_TRANS realThms2.REAL_NOT_LE
                 RaL.REAL_NOT_LT
                 CiT.REAL_LE_NEG2 CiT.REAL_NEG_NEG Rl.real_max Rl.real_min
                 realThms5.REAL_MAX_LE realThms5.REAL_LE_MAX
                 realThms5.REAL_MIN_LE realThms5.REAL_LE_MIN
                 realThms4.REAL_BOUNDS_LE realThms4.REAL_ABS_BOUNDS
                 new_definition).run with
      | .ok d => do theSetsSup.set (some d); pure d
      | .error e => panic! s!"setupSetsSup failed: {e}") with
  | .ok d => d | _ => panic! "Session.SSup: setupSetsSup not run"

/-- Cache for `SetsHasInfSup` (sets.ml 5028-5182): the relational `has_inf`/
    `has_sup` definitions and their 12 surrounding `prove`s.  Forces
    `ensureSetsHasInfSupInfix` FIRST (the LAST TWO `parse_as_infix` of
    `sets.ml`, both `(12,"right")`) so the two `new_definition` bodies and
    every `s has_inf b`/`s has_sup b` statement parse the symbols as infixes.
    Threads `SSup` (`inf`/`sup`/`INF`/`SUP`/... ) and the Part-B tactic DSL
    (`INTRO_TAC`/`HYP_TAC`/`CLAIM_TAC`), `REFUTE_THEN`/`TRANS_TAC` and the two
    real-arith tactics. -/
initialize theSetsHasInfSup : IO.Ref (Option HolMath.Sets.SetsHasInfSup) ← IO.mkRef none

private unsafe def SISup : HolMath.Sets.SetsHasInfSup :=
  match unsafeIO (do
    match ← theSetsHasInfSup.get with
    | some d => pure d
    | none => do
      ensureSetsHasInfSupInfix
      -- Pure (Except) forms of REWRITE_RULE / MATCH_MP for HYP_TAC's `rule`
      -- argument, which must be `thm → Except String thm`.  The underlying
      -- rules are IO (they build a rewrite net); we run them via `unsafeIO`
      -- since the theorem inputs are fixed and the computation is pure.
      let rwPure : List thm → thm → Except String thm := fun thl th =>
        match unsafeIO (REWRITE_RULE thl th) with
        | .ok r => r | .error _ => .error "REWRITE_RULE_PURE: IO failure"
      let mmPure : thm → thm → Except String thm := fun th1 th2 =>
        match unsafeIO (MATCH_MP th1 th2) with
        | .ok r => r | .error _ => .error "MATCH_MP_PURE: IO failure"
      match ← (HolMath.Sets.setupSetsHasInfSup SSup
                 MESON_TAC ASM_MESON_TAC REFUTE_THEN INTRO_TAC HYP_TAC CLAIM_TAC
                 rwPure mmPure REAL_ARITH_TAC ASM_REAL_ARITH_TAC
                 SP.NOT_IN_EMPTY C.NOT_FORALL_THM Rl.REAL_LE_REFL
                 Rl.REAL_LE_TRANS RaL.REAL_NOT_LT realThms2.REAL_NOT_LE
                 new_definition).run with
      | .ok d => do theSetsHasInfSup.set (some d); pure d
      | .error e => panic! s!"setupSetsHasInfSup failed: {e}") with
  | .ok d => d | _ => panic! "Session.SISup: setupSetsHasInfSup not run"

/- ---------------------------------------------------------------------- -/
/- SET_PRESET_CONV, SET_TAC, SET_RULE (sets.ml 320-335): the linchpin      -/
/- tactic and its rule form, exposed with Session's dependency bundles     -/
/- pre-applied so callers write `SET_TAC []`/`SET_RULE tm` directly.       -/
/- ---------------------------------------------------------------------- -/

/-- `SET_PRESET_CONV` (sets.ml 321-327), the local `PRESET_CONV` of SET_TAC. -/
unsafe def SET_PRESET_CONV : IO (Except String ioconv) :=
  pure (.ok (HolMath.Sets.SET_PRESET_CONV SC SP))

/-- `SET_TAC ths` (sets.ml 320-333): rewrite with the membership lemmas, then
    MESON.  Bundles pre-applied; keeps the OCaml `List thm -> tactic` arity. -/
unsafe def SET_TAC (ths : List thm) : tactic :=
  HolMath.Sets.SET_TAC SC SP MESON_TAC ths

/-- `SET_RULE tm = prove(tm, SET_TAC[])` (sets.ml 335). -/
unsafe def SET_RULE (tm : term) : IO (Except String thm) :=
  (HolMath.Sets.SET_RULE SC SP MESON_TAC tm).run

/-- new_inductive_set's `(/\)` (sets.ml 5209), parsed once. -/
initialize theNewIndSetAnd : IO.Ref (Option term) ← IO.mkRef none

private unsafe def newIndSetAndTm : IO term := do
  match ← theNewIndSetAnd.get with
  | some t => pure t
  | none =>
    match ← HolCore.Parser.parse_term "(/\\)" with
    | .ok t => do theNewIndSetAnd.set (some t); pure t
    | .error e => throw (IO.userError s!"new_inductive_set (/\\): {e}")

/-- `new_inductive_set tm` (sets.ml 5183-5217): reduce an inductive SET
    definition to an inductive RELATION and return the `(rules, induct, cases)`
    triple.  A FUNCTION, so - like `SET_TAC`/`SET_RULE` - exposed as an accessor
    with its dependencies pre-applied: `B`, the `IN` definition (`SC.IN`, whose
    read forces `setupSetsCore` and the head infixes) and the injected
    `new_inductive_definition`.  Keeps the OCaml `term -> ...` arity. -/
unsafe def new_inductive_set (tm : term) :
    IO (Except String (thm × thm × thm)) := do
  HolMath.Sets.new_inductive_set SC.IN (← newIndSetAndTm) new_inductive_definition tm

/-- `dest_setenum` (sets.ml 3872). -/
def dest_setenum : term → Except String (List term) := HolMath.Sets.dest_setenum
/-- `is_setenum` (sets.ml 3878). -/
def is_setenum : term → Bool := HolMath.Sets.is_setenum
/-- `mk_setenum` (sets.ml 3880). -/
unsafe def mk_setenum : List term × hol_type → IO (Except String term) :=
  HolMath.Sets.mk_setenum SL.insert_atm SL.nil_atm
/-- `mk_fset` (sets.ml 3886). -/
unsafe def mk_fset : List term → IO (Except String term) :=
  HolMath.Sets.mk_fset SL.insert_atm SL.nil_atm

/-- Force the parser-critical head of the sets layer, for scratchpads/bootstrap.
    Reading `SC` forces the fourteen head infixes and the core `new_definition`s
    (EMPTY/INSERT/GSPEC/SETSPEC and the operators), so a scratchpad that has
    imported HolInit can parse `x IN s`, `{a,b,c}` and `{x | P}` with those as
    real constants/operators.  Deliberately the CHEAP head, NOT `SMi`/`SFn`/the
    proof-heavy bundles - exactly as the real.ml force in HolInit picks
    `RealThms1`, not `sqrt`, and the int.ml force picks `int_of_num`, not
    `INT_RING`: bootstrap declares the constants and fixities, it does not
    re-drive every proof.  A `let _ := SC` would NOT force a Lean CAF (defect
    class #3), so read a field via `IO.mkRef`. -/
unsafe def ensureSets : IO Unit := do
  -- Force every sets.ml bundle in file order.  HOL Light executes sets.ml top
  -- to bottom, so by the time any later proof runs every earlier definition,
  -- parser effect and theorem already exists.  Our CAFs are lazy and each
  -- takes only the bundles it cites, so a caller that reaches a late bundle
  -- first would build it in a state HOL Light never has.  Forcing in file
  -- order reproduces the eager semantics; do not reorder.
  ensureSetsInfixes                                  -- sets.ml 18-32
  let _ ← IO.mkRef (concl SC.IN)                     -- 38-170
  let _ ← IO.mkRef (concl SP.IN_UNIONS)              -- 173-308
  let _ ← IO.mkRef (concl STc.CHOICE_DEF)            -- 312-355
  let _ ← IO.mkRef (concl SIn.SUBSET_TRANS)          -- 358-459
  let _ ← IO.mkRef (concl SOp.INTER_UNIV)            -- 462-665
  let _ ← IO.mkRef (concl SID.NOT_INSERT_EMPTY)      -- 668-822
  let _ ← IO.mkRef (concl SUn.UNIONS_0)              -- 825-903
  let _ ← IO.mkRef (concl SIt.INTERS_SUBSET_STRONG)  -- 906-950
  let _ ← IO.mkRef (concl SIm.IMAGE_UNIONS)          -- 953-1056
  let _ ← IO.mkRef (concl SMi.INTER_INTERS)          -- 1059-1255
  let _ ← IO.mkRef (concl SInd.FINITE_INDUCT_STRONG) -- 1258-1272
  let _ ← IO.mkRef (concl SFn.INJECTIVE_ON_LEFT_INVERSE) -- 1275-1382
  let _ ← IO.mkRef (concl SFin.FINITE_UNION)         -- 1385-1796
  let _ ← IO.mkRef (concl SRec.ITSET)                -- 1799-1988
  let _ ← IO.mkRef (concl SCard.CARD_CLAUSES)        -- 1991-2243
  let _ ← IO.mkRef (concl SCard2.CARD_SUBSET_EQ)     -- 2246-2652
  ensureSetsCrossInfix                               -- 2732
  let _ ← IO.mkRef (concl SCross.CROSS)              -- 2734-2924
  let _ ← IO.mkRef (concl SFun.ARB)                  -- 2925-3324
  let _ ← IO.mkRef (concl SFun2.HAS_SIZE_FUNSPACE)   -- 3325-3548
  let _ ← IO.mkRef (concl SInf.num_INFINITE)         -- 3554-3697
  let _ ← IO.mkRef (concl SL.pairwise)               -- 3697-3997
  ensureSetsUnionOfInfix                              -- 4001-4002
  let _ ← IO.mkRef (concl SUO.UNION_OF)              -- 4004-4360
  let _ ← IO.mkRef (concl SCC.CARD_SET_OF_LIST_LE)   -- 4365-4695
  let _ ← IO.mkRef (concl SSup.sup)                  -- 4698-5027
  ensureSetsHasInfSupInfix                            -- 5030-5031
  let _ ← IO.mkRef (concl SISup.has_inf)             -- 5033-5182
  let _ ← newIndSetAndTm                             -- 5209
  pure ()

/- ---------------------------------------------------------------------- -/
/- sets.ml bare theorem re-exports.  In HOL Light every theorem is a       -/
/- global name; the bundle records are a translation artefact, so each     -/
/- field is re-exported bare here (checked for collisions - none, even the -/
/- short generic names IN/UNION/INTER/INSERT/DIFF/DELETE/IMAGE/SUBSET).     -/
/- ---------------------------------------------------------------------- -/
-- SetsCore (sets.ml 34-170)
unsafe def IN                : thm := SC.IN
unsafe def EXTENSION         : thm := SC.EXTENSION
unsafe def GSPEC             : thm := SC.GSPEC
unsafe def SETSPEC           : thm := SC.SETSPEC
unsafe def IN_ELIM_THM       : thm := SC.IN_ELIM_THM
unsafe def EMPTY             : thm := SC.EMPTY
unsafe def INSERT_DEF        : thm := SC.INSERT_DEF
unsafe def UNIV              : thm := SC.UNIV
unsafe def UNION             : thm := SC.UNION
unsafe def UNIONS            : thm := SC.UNIONS
unsafe def INTER             : thm := SC.INTER
unsafe def INTERS            : thm := SC.INTERS
unsafe def DIFF              : thm := SC.DIFF
unsafe def INSERT            : thm := SC.INSERT
unsafe def DELETE            : thm := SC.DELETE
unsafe def SUBSET            : thm := SC.SUBSET
unsafe def PSUBSET           : thm := SC.PSUBSET
unsafe def DISJOINT          : thm := SC.DISJOINT
unsafe def SING              : thm := SC.SING
unsafe def FINITE_RULES      : thm := SC.FINITE_RULES
unsafe def FINITE_INDUCT     : thm := SC.FINITE_INDUCT
unsafe def FINITE_CASES      : thm := SC.FINITE_CASES
unsafe def INFINITE          : thm := SC.INFINITE
unsafe def IMAGE             : thm := SC.IMAGE
unsafe def INJ               : thm := SC.INJ
unsafe def SURJ              : thm := SC.SURJ
unsafe def BIJ               : thm := SC.BIJ
unsafe def CHOICE            : thm := SC.CHOICE
unsafe def REST              : thm := SC.REST
-- SetsProps (sets.ml 171-308)
unsafe def NOT_IN_EMPTY      : thm := SP.NOT_IN_EMPTY
unsafe def IN_UNIV           : thm := SP.IN_UNIV
unsafe def IN_UNION          : thm := SP.IN_UNION
unsafe def IN_UNIONS         : thm := SP.IN_UNIONS
unsafe def IN_INTER          : thm := SP.IN_INTER
unsafe def IN_INTERS         : thm := SP.IN_INTERS
unsafe def IN_DIFF           : thm := SP.IN_DIFF
unsafe def IN_INSERT         : thm := SP.IN_INSERT
unsafe def IN_DELETE         : thm := SP.IN_DELETE
unsafe def IN_SING           : thm := SP.IN_SING
unsafe def IN_IMAGE          : thm := SP.IN_IMAGE
unsafe def IN_REST           : thm := SP.IN_REST
unsafe def FORALL_IN_INSERT  : thm := SP.FORALL_IN_INSERT
unsafe def EXISTS_IN_INSERT  : thm := SP.EXISTS_IN_INSERT
unsafe def FORALL_IN_UNION   : thm := SP.FORALL_IN_UNION
unsafe def EXISTS_IN_UNION   : thm := SP.EXISTS_IN_UNION
unsafe def FORALL_IN_IMAGE   : thm := SP.FORALL_IN_IMAGE
unsafe def EXISTS_IN_IMAGE   : thm := SP.EXISTS_IN_IMAGE
unsafe def FORALL_IN_GSPEC   : thm := SP.FORALL_IN_GSPEC
unsafe def EXISTS_IN_GSPEC   : thm := SP.EXISTS_IN_GSPEC
unsafe def UNIONS_IMAGE      : thm := SP.UNIONS_IMAGE
unsafe def INTERS_IMAGE      : thm := SP.INTERS_IMAGE
unsafe def UNIONS_GSPEC      : thm := SP.UNIONS_GSPEC
unsafe def INTERS_GSPEC      : thm := SP.INTERS_GSPEC
-- SetsTactics (sets.ml 309-355)
unsafe def CHOICE_DEF        : thm := STc.CHOICE_DEF
unsafe def NOT_EQUAL_SETS    : thm := STc.NOT_EQUAL_SETS
unsafe def INSERT_RESTRICT   : thm := STc.INSERT_RESTRICT
unsafe def UNIV_1            : thm := STc.UNIV_1
-- SetsInclusion (sets.ml 356-475)
unsafe def MEMBER_NOT_EMPTY      : thm := SIn.MEMBER_NOT_EMPTY
unsafe def UNIV_NOT_EMPTY        : thm := SIn.UNIV_NOT_EMPTY
unsafe def EMPTY_NOT_UNIV        : thm := SIn.EMPTY_NOT_UNIV
unsafe def EQ_UNIV               : thm := SIn.EQ_UNIV
unsafe def SUBSET_TRANS          : thm := SIn.SUBSET_TRANS
unsafe def SUBSET_REFL           : thm := SIn.SUBSET_REFL
unsafe def SUBSET_ANTISYM        : thm := SIn.SUBSET_ANTISYM
unsafe def SUBSET_ANTISYM_EQ     : thm := SIn.SUBSET_ANTISYM_EQ
unsafe def EMPTY_SUBSET          : thm := SIn.EMPTY_SUBSET
unsafe def SUBSET_EMPTY          : thm := SIn.SUBSET_EMPTY
unsafe def SUBSET_UNIV           : thm := SIn.SUBSET_UNIV
unsafe def UNIV_SUBSET           : thm := SIn.UNIV_SUBSET
unsafe def SING_SUBSET           : thm := SIn.SING_SUBSET
unsafe def SUBSET_RESTRICT       : thm := SIn.SUBSET_RESTRICT
unsafe def PSUBSET_TRANS         : thm := SIn.PSUBSET_TRANS
unsafe def PSUBSET_SUBSET_TRANS  : thm := SIn.PSUBSET_SUBSET_TRANS
unsafe def SUBSET_PSUBSET_TRANS  : thm := SIn.SUBSET_PSUBSET_TRANS
unsafe def PSUBSET_IRREFL        : thm := SIn.PSUBSET_IRREFL
unsafe def NOT_PSUBSET_EMPTY     : thm := SIn.NOT_PSUBSET_EMPTY
unsafe def NOT_UNIV_PSUBSET      : thm := SIn.NOT_UNIV_PSUBSET
unsafe def PSUBSET_UNIV          : thm := SIn.PSUBSET_UNIV
unsafe def PSUBSET_ALT           : thm := SIn.PSUBSET_ALT
-- SetsOperators (sets.ml 476-855)
unsafe def UNION_ASSOC             : thm := SOp.UNION_ASSOC
unsafe def UNION_IDEMPOT           : thm := SOp.UNION_IDEMPOT
unsafe def UNION_COMM              : thm := SOp.UNION_COMM
unsafe def SUBSET_UNION            : thm := SOp.SUBSET_UNION
unsafe def SUBSET_UNION_ABSORPTION : thm := SOp.SUBSET_UNION_ABSORPTION
unsafe def UNION_EMPTY             : thm := SOp.UNION_EMPTY
unsafe def UNION_UNIV              : thm := SOp.UNION_UNIV
unsafe def EMPTY_UNION             : thm := SOp.EMPTY_UNION
unsafe def UNION_SUBSET            : thm := SOp.UNION_SUBSET
unsafe def UNION_RESTRICT          : thm := SOp.UNION_RESTRICT
unsafe def FORALL_SUBSET_UNION     : thm := SOp.FORALL_SUBSET_UNION
unsafe def EXISTS_SUBSET_UNION     : thm := SOp.EXISTS_SUBSET_UNION
unsafe def FORALL_SUBSET_INSERT    : thm := SOp.FORALL_SUBSET_INSERT
unsafe def EXISTS_SUBSET_INSERT    : thm := SOp.EXISTS_SUBSET_INSERT
unsafe def INTER_ASSOC             : thm := SOp.INTER_ASSOC
unsafe def INTER_IDEMPOT           : thm := SOp.INTER_IDEMPOT
unsafe def INTER_COMM              : thm := SOp.INTER_COMM
unsafe def INTER_SUBSET            : thm := SOp.INTER_SUBSET
unsafe def SUBSET_INTER_ABSORPTION : thm := SOp.SUBSET_INTER_ABSORPTION
unsafe def INTER_EMPTY             : thm := SOp.INTER_EMPTY
unsafe def INTER_UNIV              : thm := SOp.INTER_UNIV
unsafe def SUBSET_INTER            : thm := SOp.SUBSET_INTER
unsafe def INTER_RESTRICT          : thm := SOp.INTER_RESTRICT
unsafe def UNION_OVER_INTER        : thm := SOp.UNION_OVER_INTER
unsafe def INTER_OVER_UNION        : thm := SOp.INTER_OVER_UNION
unsafe def IN_DISJOINT             : thm := SOp.IN_DISJOINT
unsafe def DISJOINT_SYM            : thm := SOp.DISJOINT_SYM
unsafe def DISJOINT_EMPTY          : thm := SOp.DISJOINT_EMPTY
unsafe def DISJOINT_EMPTY_REFL     : thm := SOp.DISJOINT_EMPTY_REFL
unsafe def DISJOINT_UNION          : thm := SOp.DISJOINT_UNION
unsafe def DISJOINT_SING           : thm := SOp.DISJOINT_SING
unsafe def DIFF_EMPTY              : thm := SOp.DIFF_EMPTY
unsafe def EMPTY_DIFF              : thm := SOp.EMPTY_DIFF
unsafe def DIFF_UNIV               : thm := SOp.DIFF_UNIV
unsafe def DIFF_DIFF               : thm := SOp.DIFF_DIFF
unsafe def DIFF_EQ_EMPTY           : thm := SOp.DIFF_EQ_EMPTY
unsafe def SUBSET_DIFF             : thm := SOp.SUBSET_DIFF
unsafe def COMPL_COMPL             : thm := SOp.COMPL_COMPL
unsafe def DIFF_RESTRICT           : thm := SOp.DIFF_RESTRICT
-- SetsInsertDelete (sets.ml 856-950)
unsafe def COMPONENT             : thm := SID.COMPONENT
unsafe def DECOMPOSITION         : thm := SID.DECOMPOSITION
unsafe def SET_CASES             : thm := SID.SET_CASES
unsafe def ABSORPTION            : thm := SID.ABSORPTION
unsafe def INSERT_INSERT         : thm := SID.INSERT_INSERT
unsafe def INSERT_COMM           : thm := SID.INSERT_COMM
unsafe def INSERT_UNIV           : thm := SID.INSERT_UNIV
unsafe def NOT_INSERT_EMPTY      : thm := SID.NOT_INSERT_EMPTY
unsafe def NOT_EMPTY_INSERT      : thm := SID.NOT_EMPTY_INSERT
unsafe def INSERT_UNION          : thm := SID.INSERT_UNION
unsafe def INSERT_UNION_EQ       : thm := SID.INSERT_UNION_EQ
unsafe def INSERT_INTER          : thm := SID.INSERT_INTER
unsafe def DISJOINT_INSERT       : thm := SID.DISJOINT_INSERT
unsafe def INSERT_SUBSET         : thm := SID.INSERT_SUBSET
unsafe def SUBSET_INSERT         : thm := SID.SUBSET_INSERT
unsafe def INSERT_DIFF           : thm := SID.INSERT_DIFF
unsafe def INSERT_AC             : thm := SID.INSERT_AC
unsafe def INTER_ACI             : thm := SID.INTER_ACI
unsafe def UNION_ACI             : thm := SID.UNION_ACI
unsafe def DELETE_NON_ELEMENT    : thm := SID.DELETE_NON_ELEMENT
unsafe def IN_DELETE_EQ          : thm := SID.IN_DELETE_EQ
unsafe def EMPTY_DELETE          : thm := SID.EMPTY_DELETE
unsafe def DELETE_DELETE         : thm := SID.DELETE_DELETE
unsafe def DELETE_COMM           : thm := SID.DELETE_COMM
unsafe def DELETE_SUBSET         : thm := SID.DELETE_SUBSET
unsafe def SUBSET_DELETE         : thm := SID.SUBSET_DELETE
unsafe def SUBSET_INSERT_DELETE  : thm := SID.SUBSET_INSERT_DELETE
unsafe def DIFF_INSERT           : thm := SID.DIFF_INSERT
unsafe def PSUBSET_INSERT_SUBSET : thm := SID.PSUBSET_INSERT_SUBSET
unsafe def DELETE_INSERT         : thm := SID.DELETE_INSERT
unsafe def INSERT_DELETE         : thm := SID.INSERT_DELETE
unsafe def DELETE_INTER          : thm := SID.DELETE_INTER
unsafe def DISJOINT_DELETE_SYM   : thm := SID.DISJOINT_DELETE_SYM
-- SetsUnions
unsafe def UNIONS_0             : thm := SUn.UNIONS_0
unsafe def UNIONS_1             : thm := SUn.UNIONS_1
unsafe def UNIONS_2             : thm := SUn.UNIONS_2
unsafe def UNIONS_INSERT        : thm := SUn.UNIONS_INSERT
unsafe def FORALL_IN_UNIONS     : thm := SUn.FORALL_IN_UNIONS
unsafe def EXISTS_IN_UNIONS     : thm := SUn.EXISTS_IN_UNIONS
unsafe def EMPTY_UNIONS         : thm := SUn.EMPTY_UNIONS
unsafe def INTER_UNIONS         : thm := SUn.INTER_UNIONS
unsafe def UNIONS_SUBSET        : thm := SUn.UNIONS_SUBSET
unsafe def SUBSET_UNIONS        : thm := SUn.SUBSET_UNIONS
unsafe def UNIONS_UNION         : thm := SUn.UNIONS_UNION
unsafe def INTERS_UNION         : thm := SUn.INTERS_UNION
unsafe def UNIONS_MONO          : thm := SUn.UNIONS_MONO
unsafe def UNIONS_MONO_IMAGE    : thm := SUn.UNIONS_MONO_IMAGE
unsafe def UNIONS_UNIV          : thm := SUn.UNIONS_UNIV
unsafe def UNIONS_INSERT_EMPTY  : thm := SUn.UNIONS_INSERT_EMPTY
unsafe def UNIONS_DELETE_EMPTY  : thm := SUn.UNIONS_DELETE_EMPTY
-- SetsInters
unsafe def INTERS_0             : thm := SIt.INTERS_0
unsafe def INTERS_1             : thm := SIt.INTERS_1
unsafe def INTERS_2             : thm := SIt.INTERS_2
unsafe def INTERS_INSERT        : thm := SIt.INTERS_INSERT
unsafe def SUBSET_INTERS        : thm := SIt.SUBSET_INTERS
unsafe def INTERS_SUBSET        : thm := SIt.INTERS_SUBSET
unsafe def INTERS_SUBSET_STRONG : thm := SIt.INTERS_SUBSET_STRONG
unsafe def INTERS_ANTIMONO      : thm := SIt.INTERS_ANTIMONO
unsafe def INTERS_EQ_UNIV       : thm := SIt.INTERS_EQ_UNIV
unsafe def INTERS_ANTIMONO_GEN  : thm := SIt.INTERS_ANTIMONO_GEN
-- SetsImage (sets.ml 951-1150)
unsafe def IMAGE_CLAUSES        : thm := SIm.IMAGE_CLAUSES
unsafe def IMAGE_UNION          : thm := SIm.IMAGE_UNION
unsafe def IMAGE_ID             : thm := SIm.IMAGE_ID
unsafe def IMAGE_I              : thm := SIm.IMAGE_I
unsafe def IMAGE_o              : thm := SIm.IMAGE_o
unsafe def IMAGE_SUBSET         : thm := SIm.IMAGE_SUBSET
unsafe def IMAGE_INTER_INJ      : thm := SIm.IMAGE_INTER_INJ
unsafe def IMAGE_DIFF_INJ       : thm := SIm.IMAGE_DIFF_INJ
unsafe def IMAGE_DIFF_INJ_ALT   : thm := SIm.IMAGE_DIFF_INJ_ALT
unsafe def IMAGE_DELETE_INJ     : thm := SIm.IMAGE_DELETE_INJ
unsafe def IMAGE_DELETE_INJ_ALT : thm := SIm.IMAGE_DELETE_INJ_ALT
unsafe def IMAGE_EQ_EMPTY       : thm := SIm.IMAGE_EQ_EMPTY
unsafe def FORALL_IN_IMAGE_2    : thm := SIm.FORALL_IN_IMAGE_2
unsafe def IMAGE_CONST          : thm := SIm.IMAGE_CONST
unsafe def SIMPLE_IMAGE         : thm := SIm.SIMPLE_IMAGE
unsafe def SIMPLE_IMAGE_GEN     : thm := SIm.SIMPLE_IMAGE_GEN
unsafe def IMAGE_UNIONS         : thm := SIm.IMAGE_UNIONS
unsafe def FUN_IN_IMAGE         : thm := SIm.FUN_IN_IMAGE
unsafe def SURJECTIVE_IMAGE_EQ  : thm := SIm.SURJECTIVE_IMAGE_EQ
unsafe def IMAGE_EQ             : thm := SIm.IMAGE_EQ
-- SetsMisc (sets.ml GSPEC/saturated-image block)
unsafe def EMPTY_GSPEC                    : thm := SMi.EMPTY_GSPEC
unsafe def UNIV_GSPEC                     : thm := SMi.UNIV_GSPEC
unsafe def SING_GSPEC                     : thm := SMi.SING_GSPEC
unsafe def SING_ALT                       : thm := SMi.SING_ALT
unsafe def IN_GSPEC                       : thm := SMi.IN_GSPEC
unsafe def IN_ELIM_PAIR_THM               : thm := SMi.IN_ELIM_PAIR_THM
unsafe def IN_ELIM_TRIPLE_THM             : thm := SMi.IN_ELIM_TRIPLE_THM
unsafe def IN_ELIM_QUAD_THM               : thm := SMi.IN_ELIM_QUAD_THM
unsafe def SET_PAIR_THM                   : thm := SMi.SET_PAIR_THM
unsafe def SET_PROVE_CASES                : thm := SMi.SET_PROVE_CASES
unsafe def UNIONS_SINGS_GEN               : thm := SMi.UNIONS_SINGS_GEN
unsafe def UNIONS_SINGS                   : thm := SMi.UNIONS_SINGS
unsafe def IMAGE_INTERS                   : thm := SMi.IMAGE_INTERS
unsafe def DIFF_INTERS                    : thm := SMi.DIFF_INTERS
unsafe def INTERS_UNIONS                  : thm := SMi.INTERS_UNIONS
unsafe def UNIONS_INTERS                  : thm := SMi.UNIONS_INTERS
unsafe def UNIONS_DIFF                    : thm := SMi.UNIONS_DIFF
unsafe def DIFF_UNIONS                    : thm := SMi.DIFF_UNIONS
unsafe def DIFF_UNIONS_NONEMPTY           : thm := SMi.DIFF_UNIONS_NONEMPTY
unsafe def INTERS_OVER_UNIONS             : thm := SMi.INTERS_OVER_UNIONS
unsafe def INTER_INTERS                   : thm := SMi.INTER_INTERS
unsafe def UNIONS_OVER_INTERS             : thm := SMi.UNIONS_OVER_INTERS
unsafe def UNIONS_EQ_INTERS               : thm := SMi.UNIONS_EQ_INTERS
unsafe def EXISTS_UNIQUE_UNIONS_INTERS    : thm := SMi.EXISTS_UNIQUE_UNIONS_INTERS
unsafe def IMAGE_INTERS_SUBSET            : thm := SMi.IMAGE_INTERS_SUBSET
unsafe def IMAGE_INTER_SUBSET             : thm := SMi.IMAGE_INTER_SUBSET
unsafe def IMAGE_INTER_SATURATED_GEN      : thm := SMi.IMAGE_INTER_SATURATED_GEN
unsafe def IMAGE_INTERS_SATURATED_GEN     : thm := SMi.IMAGE_INTERS_SATURATED_GEN
unsafe def IMAGE_INTER_SATURATED          : thm := SMi.IMAGE_INTER_SATURATED
unsafe def IMAGE_INTERS_SATURATED         : thm := SMi.IMAGE_INTERS_SATURATED
-- SetsInduct
unsafe def FINITE_INDUCT_STRONG : thm := SInd.FINITE_INDUCT_STRONG
-- SetsFunctions (sets.ml 951-1382 function block)
unsafe def INJECTIVE_ON_ALT                 : thm := SFn.INJECTIVE_ON_ALT
unsafe def INJECTIVE_ALT                     : thm := SFn.INJECTIVE_ALT
unsafe def SURJECTIVE_ON_RIGHT_INVERSE       : thm := SFn.SURJECTIVE_ON_RIGHT_INVERSE
unsafe def INJECTIVE_ON_LEFT_INVERSE         : thm := SFn.INJECTIVE_ON_LEFT_INVERSE
unsafe def BIJECTIVE_ON_LEFT_RIGHT_INVERSE   : thm := SFn.BIJECTIVE_ON_LEFT_RIGHT_INVERSE
unsafe def SURJECTIVE_RIGHT_INVERSE          : thm := SFn.SURJECTIVE_RIGHT_INVERSE
unsafe def INJECTIVE_LEFT_INVERSE            : thm := SFn.INJECTIVE_LEFT_INVERSE
unsafe def BIJECTIVE_LEFT_RIGHT_INVERSE      : thm := SFn.BIJECTIVE_LEFT_RIGHT_INVERSE
unsafe def FUNCTION_FACTORS_LEFT_GEN         : thm := SFn.FUNCTION_FACTORS_LEFT_GEN
unsafe def FUNCTION_FACTORS_LEFT             : thm := SFn.FUNCTION_FACTORS_LEFT
unsafe def FUNCTION_FACTORS_RIGHT_GEN        : thm := SFn.FUNCTION_FACTORS_RIGHT_GEN
unsafe def FUNCTION_FACTORS_RIGHT            : thm := SFn.FUNCTION_FACTORS_RIGHT
unsafe def SURJECTIVE_FORALL_THM             : thm := SFn.SURJECTIVE_FORALL_THM
unsafe def SURJECTIVE_EXISTS_THM             : thm := SFn.SURJECTIVE_EXISTS_THM
unsafe def SURJECTIVE_IMAGE_THM              : thm := SFn.SURJECTIVE_IMAGE_THM
unsafe def IMAGE_INJECTIVE_IMAGE_OF_SUBSET   : thm := SFn.IMAGE_INJECTIVE_IMAGE_OF_SUBSET
-- SetsFinite (sets.ml 1383-1796)
unsafe def FINITE_EMPTY                    : thm := SFin.FINITE_EMPTY
unsafe def FINITE_SUBSET                   : thm := SFin.FINITE_SUBSET
unsafe def FINITE_RESTRICT                 : thm := SFin.FINITE_RESTRICT
unsafe def FINITE_UNION_IMP                : thm := SFin.FINITE_UNION_IMP
unsafe def FINITE_UNION                    : thm := SFin.FINITE_UNION
unsafe def FINITE_INTER                    : thm := SFin.FINITE_INTER
unsafe def FINITE_INSERT                   : thm := SFin.FINITE_INSERT
unsafe def FINITE_SING                     : thm := SFin.FINITE_SING
unsafe def FINITE_DELETE_IMP               : thm := SFin.FINITE_DELETE_IMP
unsafe def FINITE_DELETE                   : thm := SFin.FINITE_DELETE
unsafe def FINITE_FINITE_UNIONS            : thm := SFin.FINITE_FINITE_UNIONS
unsafe def FINITE_IMAGE_EXPAND             : thm := SFin.FINITE_IMAGE_EXPAND
unsafe def FINITE_IMAGE                    : thm := SFin.FINITE_IMAGE
unsafe def FINITE_IMAGE_INJ_GENERAL        : thm := SFin.FINITE_IMAGE_INJ_GENERAL
unsafe def FINITE_FINITE_PREIMAGE_GENERAL  : thm := SFin.FINITE_FINITE_PREIMAGE_GENERAL
unsafe def FINITE_FINITE_PREIMAGE          : thm := SFin.FINITE_FINITE_PREIMAGE
unsafe def FINITE_IMAGE_INJ_EQ             : thm := SFin.FINITE_IMAGE_INJ_EQ
unsafe def FINITE_IMAGE_INJ                : thm := SFin.FINITE_IMAGE_INJ
unsafe def FINITE_IMAGE_GEN                : thm := SFin.FINITE_IMAGE_GEN
unsafe def INFINITE_IMAGE                  : thm := SFin.INFINITE_IMAGE
unsafe def INFINITE_IMAGE_INJ              : thm := SFin.INFINITE_IMAGE_INJ
unsafe def INFINITE_NONEMPTY               : thm := SFin.INFINITE_NONEMPTY
unsafe def INFINITE_DIFF_FINITE            : thm := SFin.INFINITE_DIFF_FINITE
unsafe def SUBSET_IMAGE_INJ                : thm := SFin.SUBSET_IMAGE_INJ
unsafe def SUBSET_IMAGE                    : thm := SFin.SUBSET_IMAGE
unsafe def EXISTS_SUBSET_IMAGE             : thm := SFin.EXISTS_SUBSET_IMAGE
unsafe def FORALL_SUBSET_IMAGE             : thm := SFin.FORALL_SUBSET_IMAGE
unsafe def EXISTS_SUBSET_IMAGE_INJ         : thm := SFin.EXISTS_SUBSET_IMAGE_INJ
unsafe def FORALL_SUBSET_IMAGE_INJ         : thm := SFin.FORALL_SUBSET_IMAGE_INJ
unsafe def EXISTS_FINITE_SUBSET_IMAGE_INJ  : thm := SFin.EXISTS_FINITE_SUBSET_IMAGE_INJ
unsafe def FORALL_FINITE_SUBSET_IMAGE_INJ  : thm := SFin.FORALL_FINITE_SUBSET_IMAGE_INJ
unsafe def EXISTS_FINITE_SUBSET_IMAGE      : thm := SFin.EXISTS_FINITE_SUBSET_IMAGE
unsafe def FORALL_FINITE_SUBSET_IMAGE      : thm := SFin.FORALL_FINITE_SUBSET_IMAGE
unsafe def FINITE_SUBSET_IMAGE             : thm := SFin.FINITE_SUBSET_IMAGE
unsafe def FINITE_SUBSET_IMAGE_IMP         : thm := SFin.FINITE_SUBSET_IMAGE_IMP
unsafe def FINITE_IMAGE_EQ                 : thm := SFin.FINITE_IMAGE_EQ
unsafe def FINITE_IMAGE_EQ_INJ             : thm := SFin.FINITE_IMAGE_EQ_INJ
unsafe def FINITE_DIFF                     : thm := SFin.FINITE_DIFF
unsafe def INFINITE_SUPERSET               : thm := SFin.INFINITE_SUPERSET
unsafe def FINITE_TRANSITIVITY_CHAIN       : thm := SFin.FINITE_TRANSITIVITY_CHAIN
unsafe def UNIONS_MAXIMAL_SETS             : thm := SFin.UNIONS_MAXIMAL_SETS
unsafe def FINITE_SUBSET_UNIONS            : thm := SFin.FINITE_SUBSET_UNIONS
unsafe def UNIONS_IN_CHAIN                 : thm := SFin.UNIONS_IN_CHAIN
unsafe def INTERS_IN_CHAIN                 : thm := SFin.INTERS_IN_CHAIN
unsafe def FINITE_SUBSET_UNIONS_DIRECTED_EQ : thm := SFin.FINITE_SUBSET_UNIONS_DIRECTED_EQ
unsafe def FINITE_SUBSET_UNIONS_CHAIN_EQ   : thm := SFin.FINITE_SUBSET_UNIONS_CHAIN_EQ
unsafe def FINITE_SUBSET_UNIONS_CHAIN      : thm := SFin.FINITE_SUBSET_UNIONS_CHAIN
-- SetsRecursion (sets.ml 1799-1988)
unsafe def FINREC                   : thm := SRec.FINREC
unsafe def FINREC_1_LEMMA           : thm := SRec.FINREC_1_LEMMA
unsafe def FINREC_SUC_LEMMA         : thm := SRec.FINREC_SUC_LEMMA
unsafe def FINREC_UNIQUE_LEMMA      : thm := SRec.FINREC_UNIQUE_LEMMA
unsafe def FINREC_EXISTS_LEMMA      : thm := SRec.FINREC_EXISTS_LEMMA
unsafe def FINREC_FUN_LEMMA         : thm := SRec.FINREC_FUN_LEMMA
unsafe def FINREC_FUN               : thm := SRec.FINREC_FUN
unsafe def SET_RECURSION_LEMMA      : thm := SRec.SET_RECURSION_LEMMA
unsafe def ITSET                    : thm := SRec.ITSET
unsafe def FINITE_RECURSION         : thm := SRec.FINITE_RECURSION
unsafe def FINITE_RECURSION_DELETE  : thm := SRec.FINITE_RECURSION_DELETE
unsafe def ITSET_EQ                 : thm := SRec.ITSET_EQ
-- SetsCard (sets.ml 1991-2243)
unsafe def CARD                     : thm := SCard.CARD
unsafe def CARD_CLAUSES             : thm := SCard.CARD_CLAUSES
unsafe def CARD_UNION               : thm := SCard.CARD_UNION
unsafe def CARD_DELETE              : thm := SCard.CARD_DELETE
unsafe def CARD_UNION_EQ            : thm := SCard.CARD_UNION_EQ
unsafe def CARD_DIFF                : thm := SCard.CARD_DIFF
unsafe def CARD_EQ_0                : thm := SCard.CARD_EQ_0
unsafe def CARD_SING                : thm := SCard.CARD_SING
unsafe def CARD_LE_2                : thm := SCard.CARD_LE_2
unsafe def CARD_LE_3                : thm := SCard.CARD_LE_3
unsafe def CARD_LE_4                : thm := SCard.CARD_LE_4
unsafe def FINITE_INDUCT_DELETE     : thm := SCard.FINITE_INDUCT_DELETE
unsafe def HAS_SIZE                  : thm := SCard.HAS_SIZE
unsafe def HAS_SIZE_CARD            : thm := SCard.HAS_SIZE_CARD
unsafe def HAS_SIZE_0               : thm := SCard.HAS_SIZE_0
unsafe def HAS_SIZE_SUC             : thm := SCard.HAS_SIZE_SUC
unsafe def HAS_SIZE_UNION           : thm := SCard.HAS_SIZE_UNION
unsafe def HAS_SIZE_DIFF            : thm := SCard.HAS_SIZE_DIFF
unsafe def HAS_SIZE_UNIONS          : thm := SCard.HAS_SIZE_UNIONS
unsafe def FINITE_HAS_SIZE          : thm := SCard.FINITE_HAS_SIZE
unsafe def HAS_SIZE_CLAUSES         : thm := SCard.HAS_SIZE_CLAUSES
unsafe def HAS_SIZE_CONV            : ioconv := SCard.HAS_SIZE_CONV
-- SetsCard2 (sets.ml 2244-2652)
unsafe def CARD_SUBSET_EQ           : thm := SCard2.CARD_SUBSET_EQ
unsafe def CARD_SUBSET              : thm := SCard2.CARD_SUBSET
unsafe def CARD_SUBSET_LE           : thm := SCard2.CARD_SUBSET_LE
unsafe def SUBSET_CARD_EQ           : thm := SCard2.SUBSET_CARD_EQ
unsafe def FINITE_CARD_LE_SUBSET    : thm := SCard2.FINITE_CARD_LE_SUBSET
unsafe def CARD_PSUBSET             : thm := SCard2.CARD_PSUBSET
unsafe def CARD_PSUBSET_IMP         : thm := SCard2.CARD_PSUBSET_IMP
unsafe def CARD_PSUBSET_EQ          : thm := SCard2.CARD_PSUBSET_EQ
unsafe def CARD_UNION_LE            : thm := SCard2.CARD_UNION_LE
unsafe def FINITE_CARD_LE_UNION     : thm := SCard2.FINITE_CARD_LE_UNION
unsafe def CARD_UNIONS_LE           : thm := SCard2.CARD_UNIONS_LE
unsafe def CARD_UNION_GEN           : thm := SCard2.CARD_UNION_GEN
unsafe def CARD_UNION_OVERLAP_EQ    : thm := SCard2.CARD_UNION_OVERLAP_EQ
unsafe def CARD_UNION_OVERLAP       : thm := SCard2.CARD_UNION_OVERLAP
unsafe def CARD_IMAGE_INJ           : thm := SCard2.CARD_IMAGE_INJ
unsafe def HAS_SIZE_IMAGE_INJ       : thm := SCard2.HAS_SIZE_IMAGE_INJ
unsafe def CARD_IMAGE_LE            : thm := SCard2.CARD_IMAGE_LE
unsafe def FINITE_CARD_LE_IMAGE     : thm := SCard2.FINITE_CARD_LE_IMAGE
unsafe def CARD_IMAGE_INJ_EQ        : thm := SCard2.CARD_IMAGE_INJ_EQ
unsafe def CARD_SUBSET_IMAGE        : thm := SCard2.CARD_SUBSET_IMAGE
unsafe def HAS_SIZE_IMAGE_INJ_EQ    : thm := SCard2.HAS_SIZE_IMAGE_INJ_EQ
unsafe def CARD_IMAGE_EQ_INJ        : thm := SCard2.CARD_IMAGE_EQ_INJ
unsafe def EXISTS_SMALL_SUBSET_IMAGE_INJ : thm :=
  SCard2.EXISTS_SMALL_SUBSET_IMAGE_INJ
unsafe def FORALL_SMALL_SUBSET_IMAGE_INJ : thm :=
  SCard2.FORALL_SMALL_SUBSET_IMAGE_INJ
unsafe def EXISTS_SMALL_SUBSET_IMAGE : thm := SCard2.EXISTS_SMALL_SUBSET_IMAGE
unsafe def FORALL_SMALL_SUBSET_IMAGE : thm := SCard2.FORALL_SMALL_SUBSET_IMAGE
unsafe def CARD_IMAGE_LE2           : thm := SCard2.CARD_IMAGE_LE2
unsafe def CARD_IMAGE_LT2           : thm := SCard2.CARD_IMAGE_LT2
unsafe def CHOOSE_SUBSET_STRONG     : thm := SCard2.CHOOSE_SUBSET_STRONG
unsafe def CHOOSE_SUBSET_EQ         : thm := SCard2.CHOOSE_SUBSET_EQ
unsafe def CHOOSE_SUBSET            : thm := SCard2.CHOOSE_SUBSET
unsafe def CHOOSE_SUBSET_BETWEEN    : thm := SCard2.CHOOSE_SUBSET_BETWEEN
unsafe def CARD_LE_UNIONS_CHAIN     : thm := SCard2.CARD_LE_UNIONS_CHAIN
unsafe def CARD_LE_1                : thm := SCard2.CARD_LE_1
unsafe def INVOLUTION_EVEN_NOFIXPOINTS : thm :=
  SCard2.INVOLUTION_EVEN_NOFIXPOINTS
unsafe def INVOLUTION_EVEN_FIXPOINTS : thm := SCard2.INVOLUTION_EVEN_FIXPOINTS
-- SetsCross (sets.ml 2653-2924): product cardinality and the CROSS operator.
unsafe def HAS_SIZE_PRODUCT_DEPENDENT : thm := SCross.HAS_SIZE_PRODUCT_DEPENDENT
unsafe def FINITE_PRODUCT_DEPENDENT : thm := SCross.FINITE_PRODUCT_DEPENDENT
unsafe def FINITE_PRODUCT           : thm := SCross.FINITE_PRODUCT
unsafe def CARD_PRODUCT             : thm := SCross.CARD_PRODUCT
unsafe def HAS_SIZE_PRODUCT         : thm := SCross.HAS_SIZE_PRODUCT
unsafe def CROSS                    : thm := SCross.CROSS
unsafe def IN_CROSS                 : thm := SCross.IN_CROSS
unsafe def HAS_SIZE_CROSS           : thm := SCross.HAS_SIZE_CROSS
unsafe def FINITE_CROSS             : thm := SCross.FINITE_CROSS
unsafe def CARD_CROSS               : thm := SCross.CARD_CROSS
unsafe def CROSS_EQ_EMPTY           : thm := SCross.CROSS_EQ_EMPTY
unsafe def CROSS_EMPTY              : thm := SCross.CROSS_EMPTY
unsafe def CROSS_SING               : thm := SCross.CROSS_SING
unsafe def CROSS_UNIV               : thm := SCross.CROSS_UNIV
unsafe def FINITE_CROSS_EQ          : thm := SCross.FINITE_CROSS_EQ
unsafe def INFINITE_CROSS_EQ        : thm := SCross.INFINITE_CROSS_EQ
unsafe def FINITE_CROSS_UNIV        : thm := SCross.FINITE_CROSS_UNIV
unsafe def INFINITE_CROSS_UNIV      : thm := SCross.INFINITE_CROSS_UNIV
unsafe def FINITE_UNIV_PAIR         : thm := SCross.FINITE_UNIV_PAIR
unsafe def INFINITE_UNIV_PAIR       : thm := SCross.INFINITE_UNIV_PAIR
unsafe def FORALL_IN_CROSS          : thm := SCross.FORALL_IN_CROSS
unsafe def EXISTS_IN_CROSS          : thm := SCross.EXISTS_IN_CROSS
unsafe def SUBSET_CROSS             : thm := SCross.SUBSET_CROSS
unsafe def CROSS_MONO               : thm := SCross.CROSS_MONO
unsafe def CROSS_EQ                 : thm := SCross.CROSS_EQ
unsafe def IMAGE_FST_CROSS          : thm := SCross.IMAGE_FST_CROSS
unsafe def IMAGE_SND_CROSS          : thm := SCross.IMAGE_SND_CROSS
unsafe def IMAGE_PAIRED_CROSS       : thm := SCross.IMAGE_PAIRED_CROSS
unsafe def CROSS_INTER              : thm := SCross.CROSS_INTER
unsafe def CROSS_UNION              : thm := SCross.CROSS_UNION
unsafe def CROSS_DIFF               : thm := SCross.CROSS_DIFF
unsafe def INTER_CROSS              : thm := SCross.INTER_CROSS
unsafe def CROSS_UNIONS_UNIONS      : thm := SCross.CROSS_UNIONS_UNIONS
unsafe def CROSS_UNIONS             : thm := SCross.CROSS_UNIONS
unsafe def CROSS_INTERS_INTERS      : thm := SCross.CROSS_INTERS_INTERS
unsafe def CROSS_INTERS             : thm := SCross.CROSS_INTERS
unsafe def DISJOINT_CROSS           : thm := SCross.DISJOINT_CROSS
-- SetsFunspace (sets.ml 2925-3324)
unsafe def ARB                                : thm := SFun.ARB
unsafe def EXTENSIONAL                        : thm := SFun.EXTENSIONAL
unsafe def IN_EXTENSIONAL                     : thm := SFun.IN_EXTENSIONAL
unsafe def IN_EXTENSIONAL_UNDEFINED           : thm := SFun.IN_EXTENSIONAL_UNDEFINED
unsafe def EXTENSIONAL_EMPTY                  : thm := SFun.EXTENSIONAL_EMPTY
unsafe def EXTENSIONAL_UNIV                   : thm := SFun.EXTENSIONAL_UNIV
unsafe def EXTENSIONAL_EQ                     : thm := SFun.EXTENSIONAL_EQ
unsafe def RESTRICTION                        : thm := SFun.RESTRICTION
unsafe def RESTRICTION_THM                    : thm := SFun.RESTRICTION_THM
unsafe def RESTRICTION_DEFINED                : thm := SFun.RESTRICTION_DEFINED
unsafe def RESTRICTION_UNDEFINED              : thm := SFun.RESTRICTION_UNDEFINED
unsafe def RESTRICTION_EQ                     : thm := SFun.RESTRICTION_EQ
unsafe def RESTRICTION_IN_EXTENSIONAL         : thm := SFun.RESTRICTION_IN_EXTENSIONAL
unsafe def RESTRICTION_EXTENSION              : thm := SFun.RESTRICTION_EXTENSION
unsafe def RESTRICTION_FIXPOINT               : thm := SFun.RESTRICTION_FIXPOINT
unsafe def RESTRICTION_UNIV                   : thm := SFun.RESTRICTION_UNIV
unsafe def RESTRICTION_RESTRICTION            : thm := SFun.RESTRICTION_RESTRICTION
unsafe def RESTRICTION_IDEMP                  : thm := SFun.RESTRICTION_IDEMP
unsafe def IMAGE_RESTRICTION                  : thm := SFun.IMAGE_RESTRICTION
unsafe def RESTRICTION_COMPOSE_RIGHT          : thm := SFun.RESTRICTION_COMPOSE_RIGHT
unsafe def RESTRICTION_COMPOSE_LEFT           : thm := SFun.RESTRICTION_COMPOSE_LEFT
unsafe def RESTRICTION_COMPOSE                : thm := SFun.RESTRICTION_COMPOSE
unsafe def RESTRICTION_UNIQUE                 : thm := SFun.RESTRICTION_UNIQUE
unsafe def RESTRICTION_UNIQUE_ALT             : thm := SFun.RESTRICTION_UNIQUE_ALT
unsafe def cartesian_product                  : thm := SFun.cartesian_product
unsafe def IN_CARTESIAN_PRODUCT               : thm := SFun.IN_CARTESIAN_PRODUCT
unsafe def CARTESIAN_PRODUCT                   : thm := SFun.CARTESIAN_PRODUCT
unsafe def RESTRICTION_IN_CARTESIAN_PRODUCT   : thm := SFun.RESTRICTION_IN_CARTESIAN_PRODUCT
unsafe def CARTESIAN_PRODUCT_AS_RESTRICTIONS  : thm := SFun.CARTESIAN_PRODUCT_AS_RESTRICTIONS
unsafe def CARTESIAN_PRODUCT_EQ_EMPTY         : thm := SFun.CARTESIAN_PRODUCT_EQ_EMPTY
unsafe def CARTESIAN_PRODUCT_EMPTY            : thm := SFun.CARTESIAN_PRODUCT_EMPTY
unsafe def CARTESIAN_PRODUCT_EQ_MEMBERS       : thm := SFun.CARTESIAN_PRODUCT_EQ_MEMBERS
unsafe def CARTESIAN_PRODUCT_EQ_MEMBERS_EQ    : thm := SFun.CARTESIAN_PRODUCT_EQ_MEMBERS_EQ
unsafe def SUBSET_CARTESIAN_PRODUCT           : thm := SFun.SUBSET_CARTESIAN_PRODUCT
unsafe def CARTESIAN_PRODUCT_EQ               : thm := SFun.CARTESIAN_PRODUCT_EQ
unsafe def INTER_CARTESIAN_PRODUCT            : thm := SFun.INTER_CARTESIAN_PRODUCT
unsafe def CARTESIAN_PRODUCT_UNIV             : thm := SFun.CARTESIAN_PRODUCT_UNIV
unsafe def CARTESIAN_PRODUCT_SINGS            : thm := SFun.CARTESIAN_PRODUCT_SINGS
unsafe def CARTESIAN_PRODUCT_SINGS_GEN        : thm := SFun.CARTESIAN_PRODUCT_SINGS_GEN
unsafe def IMAGE_PROJECTION_CARTESIAN_PRODUCT : thm := SFun.IMAGE_PROJECTION_CARTESIAN_PRODUCT
unsafe def FORALL_CARTESIAN_PRODUCT_ELEMENTS  : thm := SFun.FORALL_CARTESIAN_PRODUCT_ELEMENTS
unsafe def FORALL_CARTESIAN_PRODUCT_ELEMENTS_EQ : thm := SFun.FORALL_CARTESIAN_PRODUCT_ELEMENTS_EQ
unsafe def EXISTS_CARTESIAN_PRODUCT_ELEMENT   : thm := SFun.EXISTS_CARTESIAN_PRODUCT_ELEMENT
unsafe def product_map                        : thm := SFun.product_map
unsafe def PRODUCT_MAP_RESTRICTION            : thm := SFun.PRODUCT_MAP_RESTRICTION
unsafe def IMAGE_PRODUCT_MAP                  : thm := SFun.IMAGE_PRODUCT_MAP
unsafe def disjoint_union                     : thm := SFun.disjoint_union
unsafe def SUBSET_DISJOINT_UNION              : thm := SFun.SUBSET_DISJOINT_UNION
unsafe def DISJOINT_UNION_EQ                  : thm := SFun.DISJOINT_UNION_EQ
unsafe def SUBSET_DISJOINT_UNION_EXISTS       : thm := SFun.SUBSET_DISJOINT_UNION_EXISTS
unsafe def INTER_DISJOINT_UNION               : thm := SFun.INTER_DISJOINT_UNION
unsafe def UNION_DISJOINT_UNION               : thm := SFun.UNION_DISJOINT_UNION
unsafe def DISJOINT_UNION_EQ_EMPTY            : thm := SFun.DISJOINT_UNION_EQ_EMPTY
unsafe def DISJOINT_DISJOINT_UNION            : thm := SFun.DISJOINT_DISJOINT_UNION

-- SetsFunspace2 (sets.ml 3325-3548)
unsafe def HAS_SIZE_FUNSPACE          : thm := SFun2.HAS_SIZE_FUNSPACE
unsafe def CARD_FUNSPACE              : thm := SFun2.CARD_FUNSPACE
unsafe def FINITE_FUNSPACE            : thm := SFun2.FINITE_FUNSPACE
unsafe def HAS_SIZE_FUNSPACE_UNIV     : thm := SFun2.HAS_SIZE_FUNSPACE_UNIV
unsafe def CARD_FUNSPACE_UNIV         : thm := SFun2.CARD_FUNSPACE_UNIV
unsafe def FINITE_FUNSPACE_UNIV       : thm := SFun2.FINITE_FUNSPACE_UNIV
unsafe def HAS_SIZE_BOOL              : thm := SFun2.HAS_SIZE_BOOL
unsafe def CARD_BOOL                  : thm := SFun2.CARD_BOOL
unsafe def FINITE_BOOL                : thm := SFun2.FINITE_BOOL
unsafe def HAS_SIZE_POWERSET          : thm := SFun2.HAS_SIZE_POWERSET
unsafe def CARD_POWERSET              : thm := SFun2.CARD_POWERSET
unsafe def FINITE_POWERSET            : thm := SFun2.FINITE_POWERSET
unsafe def FINITE_POWERSET_EQ         : thm := SFun2.FINITE_POWERSET_EQ
unsafe def FINITE_RESTRICTED_SUBSETS  : thm := SFun2.FINITE_RESTRICTED_SUBSETS
unsafe def FINITE_UNIONS              : thm := SFun2.FINITE_UNIONS
unsafe def FINITE_CARD_LE_UNIONS      : thm := SFun2.FINITE_CARD_LE_UNIONS
unsafe def POWERSET_CLAUSES           : thm := SFun2.POWERSET_CLAUSES
unsafe def FINITE_IMAGE_INFINITE      : thm := SFun2.FINITE_IMAGE_INFINITE
unsafe def FINITE_RESTRICTED_POWERSET : thm := SFun2.FINITE_RESTRICTED_POWERSET
unsafe def FINITE_RESTRICTED_FUNSPACE : thm := SFun2.FINITE_RESTRICTED_FUNSPACE
unsafe def NUMSEG_CLAUSES_LT          : thm := SInf.NUMSEG_CLAUSES_LT
unsafe def HAS_SIZE_NUMSEG_LT         : thm := SInf.HAS_SIZE_NUMSEG_LT
unsafe def CARD_NUMSEG_LT             : thm := SInf.CARD_NUMSEG_LT
unsafe def FINITE_NUMSEG_LT           : thm := SInf.FINITE_NUMSEG_LT
unsafe def NUMSEG_CLAUSES_LE          : thm := SInf.NUMSEG_CLAUSES_LE
unsafe def HAS_SIZE_NUMSEG_LE         : thm := SInf.HAS_SIZE_NUMSEG_LE
unsafe def FINITE_NUMSEG_LE           : thm := SInf.FINITE_NUMSEG_LE
unsafe def CARD_NUMSEG_LE             : thm := SInf.CARD_NUMSEG_LE
unsafe def num_FINITE                 : thm := SInf.num_FINITE
unsafe def num_FINITE_AVOID           : thm := SInf.num_FINITE_AVOID
unsafe def num_INFINITE_EQ            : thm := SInf.num_INFINITE_EQ
unsafe def num_INFINITE               : thm := SInf.num_INFINITE
unsafe def string_INFINITE            : thm := SInf.string_INFINITE
unsafe def FINITE_REAL_INTERVAL       : thm := SInf.FINITE_REAL_INTERVAL
unsafe def real_INFINITE              : thm := SInf.real_INFINITE
-- SetsList (sets.ml 3697-3997)
unsafe def HAS_SIZE_INDEX             : thm := SL.HAS_SIZE_INDEX
unsafe def INFINITE_ENUMERATE         : thm := SL.INFINITE_ENUMERATE
unsafe def INFINITE_ENUMERATE_EQ      : thm := SL.INFINITE_ENUMERATE_EQ
unsafe def INFINITE_ENUMERATE_SUBSET  : thm := SL.INFINITE_ENUMERATE_SUBSET
unsafe def set_of_list                : thm := SL.set_of_list
unsafe def list_of_set                : thm := SL.list_of_set
unsafe def LIST_OF_SET_PROPERTIES     : thm := SL.LIST_OF_SET_PROPERTIES
unsafe def SET_OF_LIST_OF_SET         : thm := SL.SET_OF_LIST_OF_SET
unsafe def LENGTH_LIST_OF_SET         : thm := SL.LENGTH_LIST_OF_SET
unsafe def MEM_LIST_OF_SET            : thm := SL.MEM_LIST_OF_SET
unsafe def FINITE_SET_OF_LIST         : thm := SL.FINITE_SET_OF_LIST
unsafe def IN_SET_OF_LIST             : thm := SL.IN_SET_OF_LIST
unsafe def SET_OF_LIST_APPEND         : thm := SL.SET_OF_LIST_APPEND
unsafe def SET_OF_LIST_MAP            : thm := SL.SET_OF_LIST_MAP
unsafe def SET_OF_LIST_EQ_EMPTY       : thm := SL.SET_OF_LIST_EQ_EMPTY
unsafe def LIST_OF_SET_EMPTY          : thm := SL.LIST_OF_SET_EMPTY
unsafe def LIST_OF_SET_SING           : thm := SL.LIST_OF_SET_SING
unsafe def pairwise                   : thm := SL.pairwise
unsafe def PAIRWISE_EMPTY             : thm := SL.PAIRWISE_EMPTY
unsafe def PAIRWISE_SING              : thm := SL.PAIRWISE_SING
unsafe def PAIRWISE_IMP               : thm := SL.PAIRWISE_IMP
unsafe def PAIRWISE_MONO              : thm := SL.PAIRWISE_MONO
unsafe def PAIRWISE_AND               : thm := SL.PAIRWISE_AND
unsafe def PAIRWISE_INSERT            : thm := SL.PAIRWISE_INSERT
unsafe def PAIRWISE_INSERT_SYMMETRIC  : thm := SL.PAIRWISE_INSERT_SYMMETRIC
unsafe def PAIRWISE_IMAGE             : thm := SL.PAIRWISE_IMAGE
unsafe def PAIRWISE_UNION             : thm := SL.PAIRWISE_UNION
unsafe def PAIRWISE_CHAIN_UNIONS      : thm := SL.PAIRWISE_CHAIN_UNIONS
unsafe def DIFF_UNIONS_PAIRWISE_DISJOINT : thm := SL.DIFF_UNIONS_PAIRWISE_DISJOINT
unsafe def INTER_UNIONS_PAIRWISE_DISJOINT : thm := SL.INTER_UNIONS_PAIRWISE_DISJOINT
unsafe def PSUBSET_UNIONS_PAIRWISE_DISJOINT : thm := SL.PSUBSET_UNIONS_PAIRWISE_DISJOINT

-- SetsUnionOf (sets.ml 3998-4364)
unsafe def UNION_OF                        : thm := SUO.UNION_OF
unsafe def INTERSECTION_OF                 : thm := SUO.INTERSECTION_OF
unsafe def UNION_OF_INC                    : thm := SUO.UNION_OF_INC
unsafe def INTERSECTION_OF_INC             : thm := SUO.INTERSECTION_OF_INC
unsafe def UNION_OF_MONO                   : thm := SUO.UNION_OF_MONO
unsafe def INTERSECTION_OF_MONO            : thm := SUO.INTERSECTION_OF_MONO
unsafe def FORALL_UNION_OF                 : thm := SUO.FORALL_UNION_OF
unsafe def FORALL_INTERSECTION_OF          : thm := SUO.FORALL_INTERSECTION_OF
unsafe def UNION_OF_EMPTY                  : thm := SUO.UNION_OF_EMPTY
unsafe def INTERSECTION_OF_EMPTY           : thm := SUO.INTERSECTION_OF_EMPTY
unsafe def ARBITRARY                       : thm := SUO.ARBITRARY
unsafe def ARBITRARY_UNION_OF_ALT          : thm := SUO.ARBITRARY_UNION_OF_ALT
unsafe def ARBITRARY_UNION_OF_EMPTY        : thm := SUO.ARBITRARY_UNION_OF_EMPTY
unsafe def ARBITRARY_INTERSECTION_OF_EMPTY : thm := SUO.ARBITRARY_INTERSECTION_OF_EMPTY
unsafe def ARBITRARY_UNION_OF_INC          : thm := SUO.ARBITRARY_UNION_OF_INC
unsafe def ARBITRARY_INTERSECTION_OF_INC   : thm := SUO.ARBITRARY_INTERSECTION_OF_INC
unsafe def ARBITRARY_UNION_OF_COMPLEMENT   : thm := SUO.ARBITRARY_UNION_OF_COMPLEMENT
unsafe def ARBITRARY_INTERSECTION_OF_COMPLEMENT : thm := SUO.ARBITRARY_INTERSECTION_OF_COMPLEMENT
unsafe def ARBITRARY_UNION_OF_IDEMPOT      : thm := SUO.ARBITRARY_UNION_OF_IDEMPOT
unsafe def ARBITRARY_INTERSECTION_OF_IDEMPOT : thm := SUO.ARBITRARY_INTERSECTION_OF_IDEMPOT
unsafe def ARBITRARY_UNION_OF_UNIONS       : thm := SUO.ARBITRARY_UNION_OF_UNIONS
unsafe def ARBITRARY_UNION_OF_UNION        : thm := SUO.ARBITRARY_UNION_OF_UNION
unsafe def ARBITRARY_INTERSECTION_OF_INTERS : thm := SUO.ARBITRARY_INTERSECTION_OF_INTERS
unsafe def ARBITRARY_INTERSECTION_OF_INTER : thm := SUO.ARBITRARY_INTERSECTION_OF_INTER
unsafe def ARBITRARY_UNION_OF_INTER_EQ     : thm := SUO.ARBITRARY_UNION_OF_INTER_EQ
unsafe def ARBITRARY_UNION_OF_INTER        : thm := SUO.ARBITRARY_UNION_OF_INTER
unsafe def ARBITRARY_INTERSECTION_OF_UNION_EQ : thm := SUO.ARBITRARY_INTERSECTION_OF_UNION_EQ
unsafe def ARBITRARY_INTERSECTION_OF_UNION : thm := SUO.ARBITRARY_INTERSECTION_OF_UNION
unsafe def FINITE_UNION_OF_EMPTY           : thm := SUO.FINITE_UNION_OF_EMPTY
unsafe def FINITE_INTERSECTION_OF_EMPTY    : thm := SUO.FINITE_INTERSECTION_OF_EMPTY
unsafe def FINITE_UNION_OF_INC             : thm := SUO.FINITE_UNION_OF_INC
unsafe def FINITE_INTERSECTION_OF_INC      : thm := SUO.FINITE_INTERSECTION_OF_INC
unsafe def FINITE_UNION_OF_COMPLEMENT      : thm := SUO.FINITE_UNION_OF_COMPLEMENT
unsafe def FINITE_INTERSECTION_OF_COMPLEMENT : thm := SUO.FINITE_INTERSECTION_OF_COMPLEMENT
unsafe def FINITE_UNION_OF_IDEMPOT         : thm := SUO.FINITE_UNION_OF_IDEMPOT
unsafe def FINITE_INTERSECTION_OF_IDEMPOT  : thm := SUO.FINITE_INTERSECTION_OF_IDEMPOT
unsafe def FINITE_UNION_OF_UNIONS          : thm := SUO.FINITE_UNION_OF_UNIONS
unsafe def FINITE_UNION_OF_UNION           : thm := SUO.FINITE_UNION_OF_UNION
unsafe def FINITE_INTERSECTION_OF_INTERS   : thm := SUO.FINITE_INTERSECTION_OF_INTERS
unsafe def FINITE_INTERSECTION_OF_INTER    : thm := SUO.FINITE_INTERSECTION_OF_INTER
unsafe def FINITE_UNION_OF_INTER_EQ        : thm := SUO.FINITE_UNION_OF_INTER_EQ
unsafe def FINITE_UNION_OF_INTER           : thm := SUO.FINITE_UNION_OF_INTER
unsafe def FINITE_INTERSECTION_OF_UNION_EQ : thm := SUO.FINITE_INTERSECTION_OF_UNION_EQ
unsafe def FINITE_INTERSECTION_OF_UNION    : thm := SUO.FINITE_INTERSECTION_OF_UNION
-- SetsCardComp (sets.ml 4365-4695)
unsafe def CARD_SET_OF_LIST_LE          : thm := SCC.CARD_SET_OF_LIST_LE
unsafe def HAS_SIZE_SET_OF_LIST         : thm := SCC.HAS_SIZE_SET_OF_LIST
unsafe def SURJECTIVE_IFF_INJECTIVE_GEN : thm := SCC.SURJECTIVE_IFF_INJECTIVE_GEN
unsafe def SURJECTIVE_IFF_INJECTIVE     : thm := SCC.SURJECTIVE_IFF_INJECTIVE
unsafe def IMAGE_IMP_INJECTIVE_GEN      : thm := SCC.IMAGE_IMP_INJECTIVE_GEN
unsafe def IMAGE_IMP_INJECTIVE          : thm := SCC.IMAGE_IMP_INJECTIVE
unsafe def HAS_SIZE_IMAGE_INJ_RESTRICT  : thm := SCC.HAS_SIZE_IMAGE_INJ_RESTRICT
unsafe def CARD_LE_INJ                  : thm := SCC.CARD_LE_INJ
unsafe def FORALL_IN_CLAUSES            : thm := SCC.FORALL_IN_CLAUSES
unsafe def EXISTS_IN_CLAUSES            : thm := SCC.EXISTS_IN_CLAUSES
unsafe def INJECTIVE_ON_IMAGE           : thm := SCC.INJECTIVE_ON_IMAGE
unsafe def INJECTIVE_IMAGE              : thm := SCC.INJECTIVE_IMAGE
unsafe def SURJECTIVE_ON_IMAGE          : thm := SCC.SURJECTIVE_ON_IMAGE
unsafe def SURJECTIVE_IMAGE             : thm := SCC.SURJECTIVE_IMAGE
unsafe def INJECTIVE_ON_PREIMAGE        : thm := SCC.INJECTIVE_ON_PREIMAGE
unsafe def SURJECTIVE_ON_PREIMAGE       : thm := SCC.SURJECTIVE_ON_PREIMAGE
unsafe def INJECTIVE_PREIMAGE           : thm := SCC.INJECTIVE_PREIMAGE
unsafe def SURJECTIVE_PREIMAGE          : thm := SCC.SURJECTIVE_PREIMAGE
unsafe def CARD_EQ_BIJECTION            : thm := SCC.CARD_EQ_BIJECTION
unsafe def CARD_EQ_BIJECTIONS           : thm := SCC.CARD_EQ_BIJECTIONS
unsafe def CARD_EQ_BIJECTIONS_SPECIAL   : thm := SCC.CARD_EQ_BIJECTIONS_SPECIAL
unsafe def BIJECTIONS_HAS_SIZE          : thm := SCC.BIJECTIONS_HAS_SIZE
unsafe def BIJECTIONS_HAS_SIZE_EQ       : thm := SCC.BIJECTIONS_HAS_SIZE_EQ
unsafe def BIJECTIONS_CARD_EQ           : thm := SCC.BIJECTIONS_CARD_EQ
unsafe def WF_FINITE                    : thm := SCC.WF_FINITE
unsafe def WF_PSUBSET                   : thm := SCC.WF_PSUBSET
unsafe def le_c                         : thm := SCC.le_c
unsafe def lt_c                         : thm := SCC.lt_c
unsafe def eq_c                         : thm := SCC.eq_c
unsafe def ge_c                         : thm := SCC.ge_c
unsafe def gt_c                         : thm := SCC.gt_c
unsafe def LE_C                         : thm := SCC.LE_C
unsafe def GE_C                         : thm := SCC.GE_C
unsafe def COUNTABLE                    : thm := SCC.COUNTABLE
-- SetsSup (sets.ml 4698-5027)
unsafe def sup                          : thm := SSup.sup
unsafe def SUP_EQ                       : thm := SSup.SUP_EQ
unsafe def SUP                          : thm := SSup.SUP
unsafe def SUP_FINITE_LEMMA             : thm := SSup.SUP_FINITE_LEMMA
unsafe def SUP_FINITE                   : thm := SSup.SUP_FINITE
unsafe def REAL_LE_SUP_FINITE           : thm := SSup.REAL_LE_SUP_FINITE
unsafe def REAL_SUP_LE_FINITE           : thm := SSup.REAL_SUP_LE_FINITE
unsafe def REAL_LT_SUP_FINITE           : thm := SSup.REAL_LT_SUP_FINITE
unsafe def REAL_SUP_LT_FINITE           : thm := SSup.REAL_SUP_LT_FINITE
unsafe def REAL_SUP_UNIQUE              : thm := SSup.REAL_SUP_UNIQUE
unsafe def REAL_SUP_LE                  : thm := SSup.REAL_SUP_LE
unsafe def REAL_SUP_LE_SUBSET           : thm := SSup.REAL_SUP_LE_SUBSET
unsafe def REAL_SUP_BOUNDS              : thm := SSup.REAL_SUP_BOUNDS
unsafe def REAL_ABS_SUP_LE              : thm := SSup.REAL_ABS_SUP_LE
unsafe def REAL_SUP_ASCLOSE             : thm := SSup.REAL_SUP_ASCLOSE
unsafe def SUP_UNIQUE_FINITE            : thm := SSup.SUP_UNIQUE_FINITE
unsafe def SUP_INSERT_FINITE            : thm := SSup.SUP_INSERT_FINITE
unsafe def SUP_SING                     : thm := SSup.SUP_SING
unsafe def SUP_INSERT_INSERT            : thm := SSup.SUP_INSERT_INSERT
unsafe def REAL_LE_SUP                  : thm := SSup.REAL_LE_SUP
unsafe def REAL_SUP_LE_EQ               : thm := SSup.REAL_SUP_LE_EQ
unsafe def SUP_UNIQUE                    : thm := SSup.SUP_UNIQUE
unsafe def SUP_UNION                    : thm := SSup.SUP_UNION
unsafe def ELEMENT_LE_SUP               : thm := SSup.ELEMENT_LE_SUP
unsafe def SUP_APPROACH                 : thm := SSup.SUP_APPROACH
unsafe def REAL_MAX_SUP                 : thm := SSup.REAL_MAX_SUP
unsafe def inf                          : thm := SSup.inf
unsafe def INF_EQ                       : thm := SSup.INF_EQ
unsafe def INF                          : thm := SSup.INF
unsafe def INF_FINITE_LEMMA             : thm := SSup.INF_FINITE_LEMMA
unsafe def INF_FINITE                   : thm := SSup.INF_FINITE
unsafe def REAL_LE_INF_FINITE           : thm := SSup.REAL_LE_INF_FINITE
unsafe def REAL_INF_LE_FINITE           : thm := SSup.REAL_INF_LE_FINITE
unsafe def REAL_LT_INF_FINITE           : thm := SSup.REAL_LT_INF_FINITE
unsafe def REAL_INF_LT_FINITE           : thm := SSup.REAL_INF_LT_FINITE
unsafe def REAL_INF_UNIQUE              : thm := SSup.REAL_INF_UNIQUE
unsafe def REAL_LE_INF                  : thm := SSup.REAL_LE_INF
unsafe def REAL_LE_INF_SUBSET           : thm := SSup.REAL_LE_INF_SUBSET
unsafe def REAL_INF_BOUNDS              : thm := SSup.REAL_INF_BOUNDS
unsafe def REAL_ABS_INF_LE              : thm := SSup.REAL_ABS_INF_LE
unsafe def REAL_INF_ASCLOSE             : thm := SSup.REAL_INF_ASCLOSE
unsafe def INF_UNIQUE_FINITE            : thm := SSup.INF_UNIQUE_FINITE
unsafe def INF_INSERT_FINITE            : thm := SSup.INF_INSERT_FINITE
unsafe def INF_SING                     : thm := SSup.INF_SING
unsafe def INF_INSERT_INSERT            : thm := SSup.INF_INSERT_INSERT
unsafe def REAL_SUP_EQ_INF              : thm := SSup.REAL_SUP_EQ_INF
unsafe def REAL_INF_LE                  : thm := SSup.REAL_INF_LE
unsafe def REAL_LE_INF_EQ               : thm := SSup.REAL_LE_INF_EQ
unsafe def INF_UNIQUE                    : thm := SSup.INF_UNIQUE
unsafe def INF_UNION                    : thm := SSup.INF_UNION
unsafe def INF_LE_ELEMENT               : thm := SSup.INF_LE_ELEMENT
unsafe def INF_APPROACH                 : thm := SSup.INF_APPROACH
unsafe def REAL_MIN_INF                 : thm := SSup.REAL_MIN_INF
-- SetsHasInfSup (sets.ml 5028-5182)
unsafe def has_inf                      : thm := SISup.has_inf
unsafe def has_sup                      : thm := SISup.has_sup
unsafe def HAS_INF_LBOUND               : thm := SISup.HAS_INF_LBOUND
unsafe def HAS_SUP_UBOUND               : thm := SISup.HAS_SUP_UBOUND
unsafe def HAS_INF_INF                  : thm := SISup.HAS_INF_INF
unsafe def HAS_SUP_SUP                  : thm := SISup.HAS_SUP_SUP
unsafe def INF_EXISTS                   : thm := SISup.INF_EXISTS
unsafe def SUP_EXISTS                   : thm := SISup.SUP_EXISTS
unsafe def HAS_INF_APPROACH             : thm := SISup.HAS_INF_APPROACH
unsafe def HAS_SUP_APPROACH             : thm := SISup.HAS_SUP_APPROACH
unsafe def HAS_INF                      : thm := SISup.HAS_INF
unsafe def HAS_SUP                      : thm := SISup.HAS_SUP
unsafe def HAS_INF_LE                   : thm := SISup.HAS_INF_LE
unsafe def HAS_SUP_LE                   : thm := SISup.HAS_SUP_LE

/- ====================================================================== -/
/- iterate.ml wiring.  Mirrors the sets.ml block above: a once-only infix  -/
/- guard, one cache + accessor per bundle, an `ensureIterate` forcing them  -/
/- in FILE ORDER, and bare theorem re-exports.  `ensureSets` runs first     -/
/- because iterate.ml opens `needs "sets.ml"` (iterate.ml 7).               -/
/- ====================================================================== -/

/-- Install the FILE'S ONLY PARSER DECLARATION, `parse_as_infix("..",
    (15,"right"))` at iterate.ml 16, behind a once-only guard - the exact
    precedent of `ensureSetsInfixes`.  Must run BEFORE `numseg` (iterate.ml 18)
    and any term containing `..`. -/
initialize theIterateInfix : IO.Ref Bool ← IO.mkRef false

private def ensureIterateInfix : IO Unit := do
  unless (← theIterateInfix.get) do
    HolMath.Iterate.setupIterateSegmentsInfix
    theIterateInfix.set true

/-- Cache for `IterateSegments` (iterate.ml 18-165): `numseg` and the
    twenty-seven segment theorems.  Forces `ensureIterateInfix` FIRST so `..`
    parses as the infix, and enters through `ensureSets` for the sets.ml
    dependencies.  Threads the Bool/Class bundles, the decision procedures, and
    the sets/arith theorem dependencies as Session accessors. -/
initialize theIterateSegments : IO.Ref (Option HolMath.Iterate.IterateSegments) ← IO.mkRef none

private unsafe def ISeg : HolMath.Iterate.IterateSegments :=
  match unsafeIO (do
    match ← theIterateSegments.get with
    | some d => pure d
    | none => do
      ensureSets
      ensureIterateInfix
      match ← (HolMath.Iterate.setupIterateSegments
                 new_definition MESON_TAC ASM_MESON_TAC SET_TAC ARITH_RULE
                 ARITH_TAC ASM_ARITH_TAC num_INDUCTION
                 EXTENSION IN_UNION IN_INSERT IN_SING NOT_IN_EMPTY IN_INTER
                 IN_ELIM_THM IN_IMAGE SUBSET DISJOINT FINITE_RULES CARD_CLAUSES
                 HAS_SIZE FINITE_SUBSET FINITE_NUMSEG_LE FINITE_INDUCT_STRONG
                 FINITE_IMAGE CARD_EQ_BIJECTIONS
                 LE_0 LE_CASES LE_REFL LE_TRANS NOT_LE SUC_SUB1 ADD_CLAUSES
                 LE_EXISTS LEFT_IMP_EXISTS_THM ARITH MONO_EXISTS).run with
      | .ok d => do theIterateSegments.set (some d); pure d
      | .error e => panic! s!"setupIterateSegments failed: {e}") with
  | .ok d => d | _ => panic! "Session.ISeg: setupIterateSegments not run"

/-- Cache for `NumsegConvPths` (iterate.ml 176-178): the three `MESON` lemmas
    of `NUMSEG_CONV`.  Pure over `ISeg`; `ADD1` used only here. -/
initialize theNumsegConvPths : IO.Ref (Option HolMath.Iterate.NumsegConvPths) ← IO.mkRef none

private unsafe def INConv : HolMath.Iterate.NumsegConvPths :=
  match unsafeIO (do
    match ← theNumsegConvPths.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Iterate.setupNumsegConvPths MESON ISeg ADD1).run with
      | .ok d => do theNumsegConvPths.set (some d); pure d
      | .error e => panic! s!"setupNumsegConvPths failed: {e}") with
  | .ok d => d | _ => panic! "Session.INConv: setupNumsegConvPths not run"

/-- Cache for `IterateSortSeg` (iterate.ml 196-277): `TOPOLOGICAL_SORT` and
    `FINITE_INT_SEG`.  Pure over `ISeg`; `ADD_SUB` used only in
    `TOPOLOGICAL_SORT`. -/
initialize theIterateSortSeg : IO.Ref (Option HolMath.Iterate.IterateSortSeg) ← IO.mkRef none

private unsafe def ISort : HolMath.Iterate.IterateSortSeg :=
  match unsafeIO (do
    match ← theIterateSortSeg.get with
    | some d => pure d
    | none =>
      match ← (HolMath.Iterate.setupIterateSortSeg MESON_TAC ASM_MESON_TAC SET_TAC
                 SET_RULE ARITH_RULE
                 ARITH_TAC ASM_ARITH_TAC INT_ARITH_TAC ASM_INT_ARITH_TAC
                 INT_ARITH num_INDUCTION ISeg
                 HAS_SIZE_0 HAS_SIZE_SUC MEMBER_NOT_EMPTY MONO_FORALL COND_RAND
                 IMP_CONJ_ALT FINITE_SUBSET FINITE_IMAGE EMPTY_GSPEC FINITE_EMPTY
                 IMAGE_CLAUSES NOT_IN_EMPTY IN_IMAGE SUBSET IN_ELIM_THM EXTENSION
                 INT_OF_NUM_LE INT_OF_NUM_OF_INT INT_SUB_LE
                 ARITH ADD_SUB SUC_SUB1 LT_REFL).run with
      | .ok d => do theIterateSortSeg.set (some d); pure d
      | .error e => panic! s!"setupIterateSortSeg failed: {e}") with
  | .ok d => d | _ => panic! "Session.ISort: setupIterateSortSeg not run"

/-- Cache for `IterateGeneric` (iterate.ml 281-354): the four core
    `new_definition`s `neutral`/`monoidal`/`support`/`iterate` and the ten
    theorems about them.  The `iterate` body uses `ITSET` (sets.ml, `ITSET`
    accessor); `CONJ_ACI`/`o_THM`/`COND_RAND` are used only in this range.
    Enters through `ensureSets`. -/
initialize theIterateGeneric : IO.Ref (Option HolMath.Iterate.IterateGeneric) ← IO.mkRef none

private unsafe def IGen : HolMath.Iterate.IterateGeneric :=
  match unsafeIO (do
    match ← theIterateGeneric.get with
    | some d => pure d
    | none => do
      ensureSets
      match ← (HolMath.Iterate.setupIterateGeneric
                 new_definition MESON_TAC ASM_MESON_TAC
                 EXTENSION IN_ELIM_THM NOT_IN_EMPTY SUBSET FINITE_SUBSET
                 IN_INSERT IN_DELETE IN_IMAGE IN_UNION IN_INTER IN_DIFF IN_SING
                 FINITE_RULES CONJ_ACI o_THM COND_RAND).run with
      | .ok d => do theIterateGeneric.set (some d); pure d
      | .error e => panic! s!"setupIterateGeneric failed: {e}") with
  | .ok d => d | _ => panic! "Session.IGen: setupIterateGeneric not run"

/-- Cache for `IterateKey1` (iterate.ml 364-539): the first eighteen key
    lemmas, `ITERATE_SUPPORT` through `ITERATE_DELETE`.  Pure over `IGen`
    (`IterateGeneric`) plus the Sets/Theorems dependencies; forces `ensureSets`
    for the sets.ml theorems and enters after `IGen`. -/
initialize theIterateKey1 : IO.Ref (Option HolMath.Iterate.IterateKey1) ← IO.mkRef none

private unsafe def IK1 : HolMath.Iterate.IterateKey1 :=
  match unsafeIO (do
    match ← theIterateKey1.get with
    | some d => pure d
    | none => do
      ensureSets
      match ← (HolMath.Iterate.setupIterateKey1 MESON_TAC ASM_MESON_TAC SET_TAC
                 SET_RULE IGen
                 FINITE_RECURSION FINITE_INDUCT_STRONG
                 IGen.FINITE_SUPPORT FINITE_INSERT FINITE_UNION FINITE_DIFF FINITE_INTER
                 FINITE_DELETE FINITE_SUBSET SUBSET_DIFF INSERT_DELETE FINITE_RULES
                 IN_INSERT IN_UNION IN_DELETE NOT_IN_EMPTY UNION_EMPTY
                 EXTENSION FORALL_IN_INSERT NOT_INSERT_EMPTY
                 REAL_ADD_RID COND_RAND COND_ID AND_FORALL_THM IMP_CONJ
                 RIGHT_FORALL_IMP_THM).run with
      | .ok d => do theIterateKey1.set (some d); pure d
      | .error e => panic! s!"setupIterateKey1 failed: {e}") with
  | .ok d => d | _ => panic! "Session.IK1: setupIterateKey1 not run"

/-- Cache for `IterateKey2` (iterate.ml 546-703): the eleven mapping and
    congruence lemmas, `ITERATE_DELTA` through `ITERATE_OP`.  Pure over `IGen`
    and `IK1` plus the Sets/Pair/Theorems dependencies, the decision
    procedures, and `GEN_BETA_CONV` (for the paired-abstraction product
    lemma).  Enters after `IK1`. -/
initialize theIterateKey2 : IO.Ref (Option HolMath.Iterate.IterateKey2) ← IO.mkRef none

private unsafe def IK2 : HolMath.Iterate.IterateKey2 :=
  match unsafeIO (do
    match ← theIterateKey2.get with
    | some d => pure d
    | none => do
      ensureSets
      match ← (HolMath.Iterate.setupIterateKey2 MESON MESON_TAC ASM_MESON_TAC
                 SET_RULE GEN_BETA_CONV IGen IK1
                 FINITE_INDUCT_STRONG FINITE_IMAGE FINITE_IMAGE_INJ_EQ
                 FINITE_PRODUCT_DEPENDENT FINITE_INSERT IGen.FINITE_SUPPORT
                 SURJECTIVE_IFF_INJECTIVE IMAGE_CLAUSES EQ_TRANS DISJOINT CONJ_ASSOC
                 IN_INSERT IN_IMAGE IN_INTER IN_ELIM_THM NOT_IN_EMPTY EXTENSION SUBSET
                 o_THM o_DEF ETA_AX PAIR_EQ FORALL_PAIR_THM EXISTS_PAIR_THM
                 IMP_CONJ RIGHT_FORALL_IMP_THM).run with
      | .ok d => do theIterateKey2.set (some d); pure d
      | .error e => panic! s!"setupIterateKey2 failed: {e}") with
  | .ok d => d | _ => panic! "Session.IK2: setupIterateKey2 not run"

/-- Cache for `IterateKey3` (iterate.ml 713-887): the ten superset/swap/image/
    cases lemmas and the four numseg-recursion clauses closing the section.
    Pure over `IGen`, the segment bundle `ISeg`, and `IK1`/`IK2` plus the extra
    Sets/arith dependencies, the decision procedures, `ARITH_RULE`,
    `REWRITE_RULE`, `INDUCT_TAC`, `NUM_REDUCE_CONV` and `num_CONV`.  Enters
    after `IK2`. -/
initialize theIterateKey3 : IO.Ref (Option HolMath.Iterate.IterateKey3) ← IO.mkRef none

private unsafe def IK3 : HolMath.Iterate.IterateKey3 :=
  match unsafeIO (do
    match ← theIterateKey3.get with
    | some d => pure d
    | none => do
      ensureSets
      match ← (HolMath.Iterate.setupIterateKey3 MESON_TAC ASM_MESON_TAC SET_TAC
                 SET_RULE ARITH_RULE ARITH_TAC ASM_ARITH_TAC INDUCT_TAC
                 NUM_REDUCE_CONV num_CONV IGen ISeg IK1 IK2
                 FINITE_INDUCT_STRONG FINITE_UNION FINITE_RESTRICT FINITE_EMPTY FINITE_IMAGE
                 FINITE_NUMSEG_LT FINITE_NUMSEG_LE
                 NUMSEG_CLAUSES_LT NUMSEG_CLAUSES_LE IMAGE_CLAUSES EQ_TRANS
                 IN_ELIM_THM IN_IMAGE IN_INSERT IN_UNION NOT_IN_EMPTY EXTENSION SUBSET
                 UNWIND_THM2 NOT_LT LT_REFL MULT_EQ_0 ARITH o_THM o_DEF
                 IMP_CONJ RIGHT_FORALL_IMP_THM).run with
      | .ok d => do theIterateKey3.set (some d); pure d
      | .error e => panic! s!"setupIterateKey3 failed: {e}") with
  | .ok d => d | _ => panic! "Session.IK3: setupIterateKey3 not run"

/-- Cache for `IterateOrdered` (iterate.ml 896-1184): `iterato` (introduced by
    `new_specification`) and its eleven lemmas - the ordered/non-commutative
    generalisation.  Pure over `IGen`, `IK1` (`ITERATE_CLAUSES`/`SUPPORT`) and
    the segment bundle `ISeg`, plus the well-foundedness/Skolem/select theorems
    and `new_specification`/`let_CONV`/`LET_TAC`.  `new_specification` is a
    side-effecting kernel op, THREADED IN here (the
    `o prove` composition is handled inside `setupIterateOrdered`).  Enters
    after `IK3`. -/
initialize theIterateOrdered : IO.Ref (Option HolMath.Iterate.IterateOrdered) ← IO.mkRef none

private unsafe def IOrd : HolMath.Iterate.IterateOrdered :=
  match unsafeIO (do
    match ← theIterateOrdered.get with
    | some d => pure d
    | none => do
      ensureSets
      match ← (HolMath.Iterate.setupIterateOrdered new_specification
                 MESON MESON_TAC ASM_MESON_TAC SET_TAC SET_RULE ARITH_RULE ARITH_TAC
                 SELECT_RULE let_CONV LET_TAC
                 IGen IK1 ISeg
                 WF_REC WF_MEASURE MEASURE EXISTS_SWAP_FUN_THM SWAP_FORALL_THM SKOLEM_THM
                 num_WF CARD_PSUBSET PSUBSET_ALT SELECT_UNIQUE MEMBER_NOT_EMPTY CONJ_ASSOC
                 UNWIND_THM2 EMPTY_GSPEC NOT_IN_EMPTY IN_DIFF IN_SING IN_DELETE IN_ELIM_THM
                 IN_INSERT IN_UNIV FINITE_SUBSET FINITE_INSERT FINITE_DELETE FINITE_RESTRICT
                 CARD_DELETE CARD_EQ_0 COND_SWAP NOT_EXISTS_THM IMP_IMP RIGHT_IMP_FORALL_THM
                 NOT_LE CONJ_SYM UNWIND_THM1).run with
      | .ok d => do theIterateOrdered.set (some d); pure d
      | .error e => panic! s!"setupIterateOrdered failed: {e}") with
  | .ok d => d | _ => panic! "Session.IOrd: setupIterateOrdered not run"

/-- Cache for `IterateSpecial` (iterate.ml 1188-1282): the four iterated
    operations at three types - `nproduct` (:num), `iproduct`/`isum` (:int),
    `product` (:real).  Pure over `IGen` (`neutral`/`monoidal`) and `IK1`
    (`ITERATE_CLAUSES`), plus the per-type neutral/monoidal identities and the
    three decision tactics.  Enters after `IOrd` (file order). -/
initialize theIterateSpecial : IO.Ref (Option HolMath.Iterate.IterateSpecial) ← IO.mkRef none

private unsafe def ISpec : HolMath.Iterate.IterateSpecial :=
  match unsafeIO (do
    match ← theIterateSpecial.get with
    | some d => pure d
    | none => do
      ensureSets
      match ← (HolMath.Iterate.setupIterateSpecial new_definition
                 MESON_TAC ARITH_TAC INT_ARITH_TAC REAL_ARITH_TAC
                 SELECT_UNIQUE SWAP_FORALL_THM MULT_CLAUSES MULT_EQ_1
                 INT_MUL_LID INT_MUL_RID REAL_MUL_LID REAL_MUL_RID
                 INT_ADD_LID INT_ADD_RID
                 IGen IK1).run with
      | .ok d => do theIterateSpecial.set (some d); pure d
      | .error e => panic! s!"setupIterateSpecial failed: {e}") with
  | .ok d => d | _ => panic! "Session.ISpec: setupIterateSpecial not run"

/-- Guard for `prioritize_num()` (iterate.ml 1286), immediately before `nsum`
    (1288).  It restores `:num` as the default for overloaded symbols so the
    WHOLE nsum half parses bare numerals as `:num`.  In this lazy build `:num`
    is already in force (int.ml 2765's `ensurePrioritizeNum` restored it, and
    nothing re-prioritizes between there and here), so this is a
    reaffirmation - but it is one of the file's four LOAD-BEARING prioritize
    calls, reproduced at its true position for fidelity, behind a once-only
    flag (the missing-paired-side-effect hazard).  An `IO`
    action, not a `Unit` CAF: a `let _ := <caf>` would NOT force it. -/
initialize theIteratePrioritizeNum : IO.Ref Bool ← IO.mkRef false

private unsafe def ensureIteratePrioritizeNum : IO Unit := do
  unless (← theIteratePrioritizeNum.get) do
    -- `num` priority must already be restored (int.ml 2765).
    ensurePrioritizeNum
    match ← (HolMath.Int.prioritize_num prioritize_overload).run with
    | .ok () => theIteratePrioritizeNum.set true
    | .error e => panic! s!"iterate.ml 1286 prioritize_num failed: {e}"

/-- Cache for `IterateNsum1` (iterate.ml 1288-1461): the `nsum` definition,
    `NEUTRAL_ADD`/`MONOIDAL_ADD`, and the twenty-five theorems `NSUM_DEGENERATE`
    to `NSUM_SWAP`.  Forces `ensureIteratePrioritizeNum` (iterate.ml 1286)
    first, then enters after `ISpec` (file order).  Pure over `IGen`/`IK1`/
    `IK2`/`IK3` plus the arith/sets dependencies and the decision procedures. -/
initialize theIterateNsum1 : IO.Ref (Option HolMath.Iterate.IterateNsum1) ← IO.mkRef none

private unsafe def IN1 : HolMath.Iterate.IterateNsum1 :=
  match unsafeIO (do
    match ← theIterateNsum1.get with
    | some d => pure d
    | none => do
      ensureSets
      ensureIteratePrioritizeNum
      match ← (HolMath.Iterate.setupIterateNsum1 new_definition
                 MESON_TAC ASM_MESON_TAC SET_TAC ARITH_TAC ARITH_RULE
                 IGen IK1 IK2 IK3
                 SELECT_UNIQUE ADD_CLAUSES MULT_CLAUSES MULT_SYM MULT_EQ_0
                 LEFT_ADD_DISTRIB CARD_CLAUSES FINITE_RULES FINITE_INDUCT_STRONG
                 NOT_IN_EMPTY IN_INSERT IN_DELETE FINITE_DELETE LE_REFL LE_ADD2
                 LTE_ADD2 LE_0 SWAP_FORALL_THM ETA_AX MEMBER_NOT_EMPTY LT_IMP_LE
                 REAL_LT_IMP_LE IMP_CONJ RIGHT_FORALL_IMP_THM).run with
      | .ok d => do theIterateNsum1.set (some d); pure d
      | .error e => panic! s!"setupIterateNsum1 failed: {e}") with
  | .ok d => d | _ => panic! "Session.IN1: setupIterateNsum1 not run"

/-- Cache for `IterateNsum2` (iterate.ml 1462-1745): `NSUM_IMAGE` to
    `NSUM_CASES` - the image/superset/restriction lemmas, the counting lemmas,
    subset monotonicity, the transfer lemmas, and `NSUM_UNIONS_NONZERO`.  This
    bundle carries the section's heaviest structured proofs.  Pure over `IN1`
    and the `IterateKey*` generics.  Enters after `IN1`. -/
initialize theIterateNsum2 : IO.Ref (Option HolMath.Iterate.IterateNsum2) ← IO.mkRef none

private unsafe def IN2 : HolMath.Iterate.IterateNsum2 :=
  match unsafeIO (do
    match ← theIterateNsum2.get with
    | some d => pure d
    | none => do
      ensureSets
      match ← (HolMath.Iterate.setupIterateNsum2 MESON_TAC ASM_MESON_TAC SET_TAC
                 ARITH_TAC ARITH_RULE IGen IK2 IK3 IN1
                 EQ_TRANS DISJOINT FINITE_INDUCT_STRONG MULT_CLAUSES MULT_AC
                 LE_MULT_RCANCEL LE_MULT_LCANCEL LE_RDIV_EQ LE_REFL LE_TRANS
                 LT_IMP_LE MEMBER_NOT_EMPTY CARD_EQ_0 SING_SUBSET IN_DIFF
                 SUBSET_UNION LE LTE_TRANS FINITE_DIFF FINITE_INTER
                 FINITE_RESTRICT FINITE_UNIONS FINITE_SUBSET UNION_COMM UNIONS_0
                 UNIONS_INSERT IN_UNION IN_INTER IN_UNIONS IN_INSERT IN_ELIM_THM
                 FORALL_IN_IMAGE SUBSET IMP_CONJ CONJ_ASSOC).run with
      | .ok d => do theIterateNsum2.set (some d); pure d
      | .error e => panic! s!"setupIterateNsum2 failed: {e}") with
  | .ok d => d | _ => panic! "Session.IN2: setupIterateNsum2 not run"

/-- Cache for `IterateNsum3` (iterate.ml 1746-1917): closure/relation
    induction, the numeral-segment theorems, modular arithmetic, `CONG_NSUM`,
    and the trailing `extend_basic_congs` congruence registration.  Pure over
    `IN1`/`IN2`, the segment bundle `ISeg`, and `IK1`/`IK3`.  Forcing it
    performs the `extend_basic_congs (map SPEC_ALL (CONJUNCTS th))` side effect
    (iterate.ml 1917).  Enters after `IN2`. -/
initialize theIterateNsum3 : IO.Ref (Option HolMath.Iterate.IterateNsum3) ← IO.mkRef none

private unsafe def IN3 : HolMath.Iterate.IterateNsum3 :=
  match unsafeIO (do
    match ← theIterateNsum3.get with
    | some d => pure d
    | none => do
      ensureSets
      match ← (HolMath.Iterate.setupIterateNsum3 MESON_TAC ASM_MESON_TAC INDUCT_TAC
                 ARITH_TAC ARITH_RULE extend_basic_congs NUMBER_RULE
                 IK1 IK3 ISeg IN1 IN2
                 FINITE_INDUCT_STRONG ISeg.FINITE_NUMSEG ISeg.NUMSEG_SING ETA_AX MOD_ZERO
                 MOD_ADD_MOD MOD_MOD_REFL SUC_SUB1 SUB_ADD ADD_CLAUSES LT_REFL
                 NOT_LT LE_TRANS EQ_ADD_RCANCEL o_DEF ISeg.IN_NUMSEG IN_ELIM_THM
                 IMP_CONJ RIGHT_FORALL_IMP_THM).run with
      | .ok d => do theIterateNsum3.set (some d); pure d
      | .error e => panic! s!"setupIterateNsum3 failed: {e}") with
  | .ok d => d | _ => panic! "Session.IN3: setupIterateNsum3 not run"

/-- Cache for `IterateNsumCard` (iterate.ml 1920-1978): `CARD_UNIONS_IMAGE`,
    `CARD_UNIONS`, and `EXPAND_NSUM_CONV` (with its three proformas).  Pure
    over `IN1`/`IN3`.  Enters after `IN3`. -/
initialize theIterateNsumCard : IO.Ref (Option HolMath.Iterate.IterateNsumCard) ← IO.mkRef none

private unsafe def INCard : HolMath.Iterate.IterateNsumCard :=
  match unsafeIO (do
    match ← theIterateNsumCard.get with
    | some d => pure d
    | none => do
      ensureSets
      match ← (HolMath.Iterate.setupIterateNsumCard SET_TAC
                 NUM_LT_CONV NUM_LE_CONV NUM_ADD_CONV IN1 IN3
                 CARD_UNION_EQ FINITE_INDUCT_STRONG FINITE_IMAGE FINITE_UNIONS
                 FINITE_UNION IMAGE_CLAUSES IMAGE_ID INTER_UNIONS UNIONS_0
                 UNIONS_INSERT NOT_IN_EMPTY IN_INSERT CARD_CLAUSES ETA_AX
                 IMP_CONJ).run with
      | .ok d => do theIterateNsumCard.set (some d); pure d
      | .error e => panic! s!"setupIterateNsumCard failed: {e}") with
  | .ok d => d | _ => panic! "Session.INCard: setupIterateNsumCard not run"

/-- Guard for `prioritize_real()` (iterate.ml 1982), immediately before `sum`
    (1984) - THE FILE'S DEFINING HAZARD.  It makes `:real` the default for
    overloaded symbols, so from here every BARE NUMERAL parses as `:real`, not
    `:num`.  Were `sum` parsed under `:num` priority it would COLLIDE with
    `nsum` and every theorem in iterate.ml 1982-3111 would carry the wrong
    type.  Reproduced at its TRUE position in `ensureIterate`'s
    file order: AFTER the nsum bundles (last is `INCard`, iterate.ml 1978) and
    BEFORE any `sum` bundle.  This is one of the file's four LOAD-BEARING
    prioritize calls; behind a once-only flag (the
    missing-paired-side-effect hazard), it is an `IO` action so a `let _ :=`
    would NOT force it.  `prioritize_real` is idempotent, but
    it is a GLOBAL, ORDER-DEPENDENT side effect, hence the guard. -/
initialize theIterateSumPrioritizeReal : IO.Ref Bool ← IO.mkRef false

private unsafe def ensureIterateSumPrioritizeReal : IO Unit := do
  unless (← theIterateSumPrioritizeReal.get) do
    prioritize_real
    theIterateSumPrioritizeReal.set true

/-- Cache for `IterateSum1` (iterate.ml 1984-2211): the `sum` definition,
    `NEUTRAL_REAL_ADD`/`MONOIDAL_REAL_ADD`, and the core algebra/ordering/
    bounds group `SUM_DEGENERATE` to `SUM_SWAP`.  Forces
    `ensureIterateSumPrioritizeReal` (iterate.ml 1982) FIRST so bare numerals
    parse `:real`, then enters after `INCard` (file order).  Pure over
    `IGen`/`IK1`/`IK2`/`IK3` plus the real/sets dependencies and the decision
    procedures. -/
initialize theIterateSum1 : IO.Ref (Option HolMath.Iterate.IterateSum1) ← IO.mkRef none

private unsafe def IS1 : HolMath.Iterate.IterateSum1 :=
  match unsafeIO (do
    match ← theIterateSum1.get with
    | some d => pure d
    | none => do
      ensureSets
      ensureIterateSumPrioritizeReal
      match ← (HolMath.Iterate.setupIterateSum1
                 new_definition MESON_TAC ASM_MESON_TAC MESON SET_TAC SET_RULE
                 REAL_ARITH3 REAL_ARITH_TAC2 IGen IK1 IK2 IK3
                 SELECT_UNIQUE REAL_ADD_LID REAL_ADD_RID REAL_MUL_LZERO
                 REAL_MUL_RZERO REAL_MUL_SYM REAL_ENTIRE REAL_ADD_LDISTRIB
                 REAL_LE_REFL REAL_LE_ADD2 REAL_LTE_ADD2 REAL_LET_TRANS
                 REAL_LE_TRANS REAL_LE_ANTISYM REAL_ABS_NUM REAL_OF_NUM_SUC
                 REAL_EQ_SUB_LADD REAL_NEG_0 REAL_LT_IMP_LE real_sub
                 FINITE_RULES FINITE_INDUCT_STRONG FINITE_DELETE NOT_IN_EMPTY
                 IN_INSERT IN_DELETE IN_ELIM_THM MEMBER_NOT_EMPTY CARD_CLAUSES
                 ETA_AX SWAP_FORALL_THM RIGHT_FORALL_IMP_THM IMP_CONJ).run with
      | .ok d => do theIterateSum1.set (some d); pure d
      | .error e => panic! s!"setupIterateSum1 failed: {e}") with
  | .ok d => d | _ => panic! "Session.IS1: setupIterateSum1 not run"

/-- Cache for `IterateSum2` (iterate.ml 2219-2598): the second `sum` bundle -
    image/superset/count/group/subset/product/general/closure lemmas,
    `SUM_IMAGE` to `REAL_OF_NUM_SUM_GEN`.  Pure over `IGen`/`IK1`/`IK2`/`IK3`
    and `IS1`.  Enters after `IS1` (file order); no fresh prioritize needed. -/
initialize theIterateSum2 : IO.Ref (Option HolMath.Iterate.IterateSum2) ← IO.mkRef none

private unsafe def IS2 : HolMath.Iterate.IterateSum2 :=
  match unsafeIO (do
    match ← theIterateSum2.get with
    | some d => pure d
    | none => do
      ensureSets
      match ← (HolMath.Iterate.setupIterateSum2
                 MESON_TAC ASM_MESON_TAC SET_TAC SET_RULE REAL_ARITH3 REAL_ARITH_TAC2
                 IGen IK1 IK2 IK3 IS1
                 IN1.NEUTRAL_ADD FINITE_INDUCT_STRONG FINITE_IMAGE FINITE_RESTRICT
                 FINITE_DIFF FINITE_INTER FINITE_UNIONS FINITE_SUBSET IN_INSERT
                 IN_ELIM_THM IN_DIFF IN_INTER IN_UNION IN_UNIONS FORALL_IN_IMAGE
                 SING_SUBSET SUBSET SUBSET_UNION UNION_COMM UNIONS_0
                 UNIONS_INSERT DELETE EQ_TRANS DISJOINT CONJ_ASSOC IMP_CONJ
                 RIGHT_FORALL_IMP_THM LEFT_IMP_EXISTS_THM o_THM MEMBER_NOT_EMPTY
                 REAL_LE_TRANS REAL_LTE_TRANS REAL_EQ_IMP_LE REAL_LE_RMUL
                 REAL_LE_RNEG REAL_LE_REFL REAL_ADD_LID REAL_MUL_RID
                 REAL_OF_NUM_ADD REAL_OF_NUM_MUL REAL_OF_NUM_EQ REAL_DIV_LMUL
                 REAL_LT_IMP_LE HAS_SIZE HAS_SIZE_0 MULT_AC IN1.NSUM_CLAUSES
                 IN1.NSUM_SUPPORT).run with
      | .ok d => do theIterateSum2.set (some d); pure d
      | .error e => panic! s!"setupIterateSum2 failed: {e}") with
  | .ok d => d | _ => panic! "Session.IS2: setupIterateSum2 not run"

/-- Cache for `IterateSum3` (iterate.ml 2599-2778): `sum` over numseg intervals
    (`SUM_ADD_NUMSEG` to `REAL_OF_NUM_SUM_NUMSEG`) and partial summation
    (`SUM_PARTIAL_SUC` to `SUM_COMBINE_L`).  Pure over the segment bundle
    `ISeg`, `IK3` (the segment recursion clauses), and `IS1`/`IS2`.  Enters
    after `IS2` (file order); still under prioritize_real. -/
initialize theIterateSum3 : IO.Ref (Option HolMath.Iterate.IterateSum3) ← IO.mkRef none

private unsafe def IS3 : HolMath.Iterate.IterateSum3 :=
  match unsafeIO (do
    match ← theIterateSum3.get with
    | some d => pure d
    | none => do
      ensureSets
      match ← (HolMath.Iterate.setupIterateSum3
                 MESON_TAC REAL_ARITH3 REAL_ARITH_TAC2 ARITH_TAC
                 ASM_ARITH_TAC ARITH_RULE INDUCT_TAC IK3 ISeg IS1 IS2
                 ISeg.FINITE_NUMSEG ISeg.IN_NUMSEG ISeg.NUMSEG_SING
                 ISeg.NUMSEG_ADD_SPLIT ISeg.NUMSEG_OFFSET_IMAGE ISeg.NUMSEG_LREC
                 ISeg.DISJOINT_NUMSEG LE LE_TRANS NOT_LT NOT_LE LT_REFL
                 SUC_SUB1 SUB_ADD ADD_CLAUSES ADD1 ADD_SUB EQ_ADD_RCANCEL
                 o_DEF REAL_SUB_REFL REAL_MUL_RZERO REAL_NEG_SUB REAL_NEG_0
                 EXTENSION IN_INTER IN_UNION NOT_IN_EMPTY).run with
      | .ok d => do theIterateSum3.set (some d); pure d
      | .error e => panic! s!"setupIterateSum3 failed: {e}") with
  | .ok d => d | _ => panic! "Session.IS3: setupIterateSum3 not run"

/-- Cache for `IterateSum4` (iterate.ml 2779-2854): the `sum` congruences
    (`SUM_CONG`, registered via `extend_basic_congs` - a side effect, iterate.ml
    2793), `EXPAND_SUM_CONV` (a CONVERSION, tested behaviourally), and the
    `REAL_SUB_POW*` rearrangements.  Pure over `IS1`/`IS2`/`IS3`.  Enters after
    `IS3`; still under prioritize_real. -/
initialize theIterateSum4 : IO.Ref (Option HolMath.Iterate.IterateSum4) ← IO.mkRef none

private unsafe def IS4 : HolMath.Iterate.IterateSum4 :=
  match unsafeIO (do
    match ← theIterateSum4.get with
    | some d => pure d
    | none => do
      ensureSets
      match ← (HolMath.Iterate.setupIterateSum4
                 extend_basic_congs NUM_LT_CONV NUM_LE_CONV NUM_ADD_CONV
                 REAL_ARITH3 ARITH_RULE IS1 IS2 IS3
                 IN_ELIM_THM ISeg.IN_NUMSEG REAL_POW_ONE REAL_MUL_RID REAL_MUL_LID
                 REAL_MUL_LNEG REAL_NEG_SUB real_pow ADD1 LE_0 SUB_0 SUB_ADD
                 SUB_REFL).run with
      | .ok d => do theIterateSum4.set (some d); pure d
      | .error e => panic! s!"setupIterateSum4 failed: {e}") with
  | .ok d => d | _ => panic! "Session.IS4: setupIterateSum4 not run"

/-- Cache for `IterateSum5` (iterate.ml 2855-3108): real polynomial functions.
    Pure over `IS1`/`IS2`/`IS3`/`IS4` and `ISeg`.  Enters after `IS4`; still
    under prioritize_real (iterate.ml 3112's restore is a LATER range). -/
initialize theIterateSum5 : IO.Ref (Option HolMath.Iterate.IterateSum5) ← IO.mkRef none

private unsafe def IS5 : HolMath.Iterate.IterateSum5 :=
  match unsafeIO (do
    match ← theIterateSum5.get with
    | some d => pure d
    | none => do
      ensureSets
      match ← (HolMath.Iterate.setupIterateSum5
                 new_definition MESON_TAC ASM_MESON_TAC MESON SET_RULE
                 REAL_ARITH3 REAL_ARITH_TAC2 ARITH_RULE ARITH_TAC ASM_ARITH_TAC
                 INDUCT_TAC IS1 IS2 IS3 IS4 ISeg
                 ISeg.FINITE_NUMSEG FINITE_EMPTY CARD_CLAUSES FINITE_RULES
                 real_INFINITE INFINITE real_pow REAL_POW_ADD REAL_POW_1
                 REAL_MUL_RID REAL_MUL_LZERO REAL_MUL_ASSOC REAL_ADD_RID
                 REAL_ADD_LID REAL_ADD_RDISTRIB REAL_ADD_LDISTRIB REAL_MUL_SYM
                 REAL_ENTIRE REAL_SUB_0 REAL_SUB_RZERO REAL_SUB_REFL
                 REAL_SUB_LDISTRIB REAL_NEG_NEG REAL_MUL_LNEG REAL_MUL_LID
                 REAL_MUL_RZERO ARITH EQ_TRANS IMP_CONJ IMP_CONJ_ALT
                 SWAP_FORALL_THM RIGHT_FORALL_IMP_THM LE LE_0 LE_1 LE_REFL
                 NOT_FORALL_THM NOT_IMP NOT_EXISTS_THM DE_MORGAN_THM
                 LEFT_OR_DISTRIB LEFT_IMP_EXISTS_THM UNWIND_THM2 IN_SING
                 ISeg.IN_NUMSEG IN_ELIM_THM IN_ELIM_PAIR_THM FORALL_IN_GSPEC
                 UNIV_GSPEC EMPTY_GSPEC FINITE_INSERT FINITE_INDUCT_STRONG
                 FORALL_IN_INSERT COND_RAND COND_RATOR EXTENSION ETA_AX ADD1
                 ADD_CLAUSES ADD_SUB ADD_EQ_0 ARITH_EQ SUC_SUB1 ADD_SYM
                 I_DEF o_DEF FUN_EQ_THM EXISTS_REFL LEFT_FORALL_IMP_THM
                 CONTRAPOS_THM REAL_MUL_AC MEMBER_NOT_EMPTY real_sub).run with
      | .ok d => do theIterateSum5.set (some d); pure d
      | .error e => panic! s!"setupIterateSum5 failed: {e}") with
  | .ok d => d | _ => panic! "Session.IS5: setupIterateSum5 not run"

/-- Once-only guard for iterate.ml 3112, the closing `prioritize_num()`
    under the banner "Make natural numbers the default again".

    This is half of a pair with `ensureIterateSumPrioritizeReal` (iterate.ml
    1982): between those two calls a bare numeral parses `:real`; from here on
    it parses `:num` again.  Omitting this restore would silently mistype every
    later file, which no compile error would reveal.  It needs its own flag and
    its own direct call to `prioritize_num`; delegating to `ensurePrioritizeNum`
    (int.ml 2765) would be a no-op, since that guard's flag was set during the
    int/sets chain.  The real-half bundles `IS1`-`IS5` are already forced by the
    time this runs, so their theorems keep the `:real` parse they were built
    with; only the default for later parsing flips. -/
initialize theIteratePrioritizeNumRestore : IO.Ref Bool ← IO.mkRef false

private unsafe def ensureIteratePrioritizeNumRestore : IO Unit := do
  unless (← theIteratePrioritizeNumRestore.get) do
    match ← (HolMath.Int.prioritize_num prioritize_overload).run with
    | .ok () => theIteratePrioritizeNumRestore.set true
    | .error e => panic! s!"iterate.ml 3112 prioritize_num restore failed: {e}"

/-- Force every iterate.ml bundle, IN FILE ORDER, mirroring
    `ensureSets`.  HOL Light runs iterate.ml top to bottom after `needs
    "sets.ml"`, so `ensureSets` runs first, then the `..` infix, then the
    segment section, the NUMSEG_CONV lemmas, the sort/int-seg proofs, and the
    generic-iteration core.  DO NOT REORDER.  A `let _ := X` would NOT force a
    Lean CAF, so read a field via `IO.mkRef (concl ...)`.
    The three prioritize side effects are interleaved at their TRUE positions
    (1286, 1982, 3112); the last one RESTORES `:num` for every later file. -/
unsafe def ensureIterate : IO Unit := do
  ensureSets
  ensureIterateInfix                              -- iterate.ml 16
  let _ ← IO.mkRef (concl ISeg.numseg)            -- 18-165
  let _ ← IO.mkRef (concl INConv.pth_0)           -- 176-178
  let _ ← IO.mkRef (concl ISort.TOPOLOGICAL_SORT) -- 196-277
  let _ ← IO.mkRef (concl IGen.neutral)           -- 281-354
  let _ ← IO.mkRef (concl IK1.ITERATE_SUPPORT)    -- 364-539
  let _ ← IO.mkRef (concl IK2.ITERATE_DELTA)      -- 546-703
  let _ ← IO.mkRef (concl IK3.ITERATE_SUPERSET)   -- 713-887
  let _ ← IO.mkRef (concl IOrd.iterato)           -- 896-1184
  let _ ← IO.mkRef (concl ISpec.nproduct)         -- 1188-1282
  ensureIteratePrioritizeNum                      -- 1286 prioritize_num()
  let _ ← IO.mkRef (concl IN1.nsum)               -- 1288-1461
  let _ ← IO.mkRef (concl IN2.NSUM_IMAGE)         -- 1462-1745
  let _ ← IO.mkRef (concl IN3.NSUM_CLOSED)        -- 1746-1917
  let _ ← IO.mkRef (concl INCard.CARD_UNIONS_IMAGE) -- 1920-1978
  ensureIterateSumPrioritizeReal                  -- 1982 prioritize_real()
  let _ ← IO.mkRef (concl IS1.sum)                -- 1984-2211
  let _ ← IO.mkRef (concl IS2.SUM_IMAGE)          -- 2219-2598
  let _ ← IO.mkRef (concl IS3.SUM_ADD_NUMSEG)     -- 2599-2778
  let _ ← IO.mkRef (concl IS4.SUM_CONG)           -- 2779-2854
  let _ ← IO.mkRef (concl IS5.polynomial_function) -- 2855-3108
  ensureIteratePrioritizeNumRestore               -- 3112 prioritize_num()
  pure ()

/- ---------------------------------------------------------------------- -/
/- iterate.ml bare theorem re-exports (ranges 18-354).                    -/
/- ---------------------------------------------------------------------- -/
-- IterateSegments (iterate.ml 18-165)
unsafe def numseg                : thm := ISeg.numseg
unsafe def FINITE_NUMSEG         : thm := ISeg.FINITE_NUMSEG
unsafe def NUMSEG_COMBINE_R      : thm := ISeg.NUMSEG_COMBINE_R
unsafe def NUMSEG_COMBINE_L      : thm := ISeg.NUMSEG_COMBINE_L
unsafe def NUMSEG_LREC           : thm := ISeg.NUMSEG_LREC
unsafe def NUMSEG_RREC           : thm := ISeg.NUMSEG_RREC
unsafe def NUMSEG_REC            : thm := ISeg.NUMSEG_REC
unsafe def IN_NUMSEG             : thm := ISeg.IN_NUMSEG
unsafe def IN_NUMSEG_0           : thm := ISeg.IN_NUMSEG_0
unsafe def NUMSEG_SING           : thm := ISeg.NUMSEG_SING
unsafe def NUMSEG_EMPTY          : thm := ISeg.NUMSEG_EMPTY
unsafe def EMPTY_NUMSEG          : thm := ISeg.EMPTY_NUMSEG
unsafe def FINITE_SUBSET_NUMSEG  : thm := ISeg.FINITE_SUBSET_NUMSEG
unsafe def CARD_NUMSEG_LEMMA     : thm := ISeg.CARD_NUMSEG_LEMMA
unsafe def CARD_NUMSEG           : thm := ISeg.CARD_NUMSEG
unsafe def HAS_SIZE_NUMSEG       : thm := ISeg.HAS_SIZE_NUMSEG
unsafe def CARD_NUMSEG_1         : thm := ISeg.CARD_NUMSEG_1
unsafe def HAS_SIZE_NUMSEG_1     : thm := ISeg.HAS_SIZE_NUMSEG_1
unsafe def NUMSEG_CLAUSES        : thm := ISeg.NUMSEG_CLAUSES
unsafe def FINITE_INDEX_NUMSEG   : thm := ISeg.FINITE_INDEX_NUMSEG
unsafe def FINITE_INDEX_NUMBERS  : thm := ISeg.FINITE_INDEX_NUMBERS
unsafe def INTER_NUMSEG          : thm := ISeg.INTER_NUMSEG
unsafe def DISJOINT_NUMSEG       : thm := ISeg.DISJOINT_NUMSEG
unsafe def NUMSEG_ADD_SPLIT      : thm := ISeg.NUMSEG_ADD_SPLIT
unsafe def NUMSEG_OFFSET_IMAGE   : thm := ISeg.NUMSEG_OFFSET_IMAGE
unsafe def SUBSET_NUMSEG         : thm := ISeg.SUBSET_NUMSEG
unsafe def NUMSEG_LE             : thm := ISeg.NUMSEG_LE
unsafe def NUMSEG_LT             : thm := ISeg.NUMSEG_LT
-- NumsegConvPths (iterate.ml 176-178)
unsafe def NUMSEG_CONV_pth_0     : thm := INConv.pth_0
unsafe def NUMSEG_CONV_pth_1     : thm := INConv.pth_1
unsafe def NUMSEG_CONV_pth_2     : thm := INConv.pth_2
/-- `NUMSEG_CONV` (iterate.ml 175-190) fully applied: the CONVERSION evaluating
    `m..n` for specific numerals `m`, `n`, producing `|- m..n = {m,...,n}`.
    Assembled here (mirroring `EXPAND_NSUM_CONV`) from `B`, the three numeral
    conversions, and the `INConv` proformas.  The OCaml template terms
    (`ns_tm = (..)`, `m_tm = m:num`, `n_tm = n:num`, iterate.ml 178-179) are
    DERIVED from `INConv.pth_2`'s conclusion `m <= n ==> m..n = m INSERT
    (SUC m..n)` rather than re-parsed, so the head constant `nsTm` is the EXACT
    kernel constant the recursion destructures (a re-parsed `(..)` need not be
    term-equal to it, which silently fails `nst != nsTm`).  A forcing probe on
    a conversion proves nothing about its behaviour, so this is exposed for the
    test's explicit behavioural driver. -/
unsafe def NUMSEG_CONV : ioconv :=
  HolMath.Iterate.NUMSEG_CONV NUM_LT_CONV NUM_LE_CONV NUM_SUC_CONV
    INConv INConv.ns_tm INConv.m_tm INConv.n_tm
-- IterateSortSeg (iterate.ml 196-277)
unsafe def TOPOLOGICAL_SORT      : thm := ISort.TOPOLOGICAL_SORT
unsafe def FINITE_INT_SEG        : thm := ISort.FINITE_INT_SEG
-- IterateGeneric (iterate.ml 281-354)
unsafe def neutral               : thm := IGen.neutral
unsafe def monoidal              : thm := IGen.monoidal
unsafe def MONOIDAL_AC           : thm := IGen.MONOIDAL_AC
unsafe def support               : thm := IGen.support
unsafe def iterate               : thm := IGen.iterate
unsafe def IN_SUPPORT            : thm := IGen.IN_SUPPORT
unsafe def SUPPORT_SUPPORT       : thm := IGen.SUPPORT_SUPPORT
unsafe def SUPPORT_EMPTY         : thm := IGen.SUPPORT_EMPTY
unsafe def SUPPORT_SUBSET        : thm := IGen.SUPPORT_SUBSET
unsafe def FINITE_SUPPORT        : thm := IGen.FINITE_SUPPORT
unsafe def SUPPORT_CLAUSES       : thm := IGen.SUPPORT_CLAUSES
unsafe def SUPPORT_DELTA         : thm := IGen.SUPPORT_DELTA
unsafe def FINITE_SUPPORT_DELTA  : thm := IGen.FINITE_SUPPORT_DELTA
-- IterateKey1 (iterate.ml 364-539)
unsafe def ITERATE_SUPPORT          : thm := IK1.ITERATE_SUPPORT
unsafe def ITERATE_EXPAND_CASES     : thm := IK1.ITERATE_EXPAND_CASES
unsafe def ITERATE_CLAUSES_GEN      : thm := IK1.ITERATE_CLAUSES_GEN
unsafe def ITERATE_CLAUSES          : thm := IK1.ITERATE_CLAUSES
unsafe def ITERATE_UNION            : thm := IK1.ITERATE_UNION
unsafe def ITERATE_UNION_GEN        : thm := IK1.ITERATE_UNION_GEN
unsafe def ITERATE_DIFF             : thm := IK1.ITERATE_DIFF
unsafe def ITERATE_DIFF_GEN         : thm := IK1.ITERATE_DIFF_GEN
unsafe def ITERATE_INCL_EXCL        : thm := IK1.ITERATE_INCL_EXCL
unsafe def ITERATE_CLOSED           : thm := IK1.ITERATE_CLOSED
unsafe def ITERATE_RELATED          : thm := IK1.ITERATE_RELATED
unsafe def ITERATE_EQ_NEUTRAL       : thm := IK1.ITERATE_EQ_NEUTRAL
unsafe def ITERATE_SING             : thm := IK1.ITERATE_SING
unsafe def ITERATE_CLOSED_NONEMPTY  : thm := IK1.ITERATE_CLOSED_NONEMPTY
unsafe def ITERATE_RELATED_NONEMPTY : thm := IK1.ITERATE_RELATED_NONEMPTY
unsafe def ITERATE_DELETE           : thm := IK1.ITERATE_DELETE
-- IterateKey2 (iterate.ml 546-703)
unsafe def ITERATE_DELTA                : thm := IK2.ITERATE_DELTA
unsafe def ITERATE_IMAGE                : thm := IK2.ITERATE_IMAGE
unsafe def ITERATE_BIJECTION            : thm := IK2.ITERATE_BIJECTION
unsafe def ITERATE_ITERATE_PRODUCT      : thm := IK2.ITERATE_ITERATE_PRODUCT
unsafe def ITERATE_EQ                   : thm := IK2.ITERATE_EQ
unsafe def ITERATE_RESTRICT_SET         : thm := IK2.ITERATE_RESTRICT_SET
unsafe def ITERATE_EQ_GENERAL           : thm := IK2.ITERATE_EQ_GENERAL
unsafe def ITERATE_EQ_GENERAL_INVERSES  : thm := IK2.ITERATE_EQ_GENERAL_INVERSES
unsafe def ITERATE_INJECTION            : thm := IK2.ITERATE_INJECTION
unsafe def ITERATE_UNION_NONZERO        : thm := IK2.ITERATE_UNION_NONZERO
unsafe def ITERATE_OP                   : thm := IK2.ITERATE_OP
-- IterateKey3 (iterate.ml 713-887)
unsafe def ITERATE_SUPERSET             : thm := IK3.ITERATE_SUPERSET
unsafe def ITERATE_UNIV                 : thm := IK3.ITERATE_UNIV
unsafe def ITERATE_SWAP                 : thm := IK3.ITERATE_SWAP
unsafe def ITERATE_IMAGE_NONZERO        : thm := IK3.ITERATE_IMAGE_NONZERO
unsafe def ITERATE_IMAGE_GEN            : thm := IK3.ITERATE_IMAGE_GEN
unsafe def ITERATE_CASES                : thm := IK3.ITERATE_CASES
unsafe def ITERATE_OP_GEN               : thm := IK3.ITERATE_OP_GEN
unsafe def ITERATE_CLAUSES_NUMSEG       : thm := IK3.ITERATE_CLAUSES_NUMSEG
unsafe def ITERATE_CLAUSES_NUMSEG_LT    : thm := IK3.ITERATE_CLAUSES_NUMSEG_LT
unsafe def ITERATE_CLAUSES_NUMSEG_LE    : thm := IK3.ITERATE_CLAUSES_NUMSEG_LE
unsafe def ITERATE_PAIR                 : thm := IK3.ITERATE_PAIR
unsafe def ITERATE_REFLECT              : thm := IK3.ITERATE_REFLECT
-- IterateOrdered (iterate.ml 896-1184)
unsafe def iterato                      : thm := IOrd.iterato
unsafe def ITERATO_SUPPORT              : thm := IOrd.ITERATO_SUPPORT
unsafe def ITERATO_EXPAND_CASES         : thm := IOrd.ITERATO_EXPAND_CASES
unsafe def ITERATO_CLAUSES_GEN          : thm := IOrd.ITERATO_CLAUSES_GEN
unsafe def ITERATO_CLAUSES              : thm := IOrd.ITERATO_CLAUSES
unsafe def ITERATO_CLAUSES_EXISTS       : thm := IOrd.ITERATO_CLAUSES_EXISTS
unsafe def ITERATO_EQ                   : thm := IOrd.ITERATO_EQ
unsafe def ITERATO_INDUCT               : thm := IOrd.ITERATO_INDUCT
unsafe def ITERATO_CLOSED               : thm := IOrd.ITERATO_CLOSED
unsafe def ITERATO_ITERATE              : thm := IOrd.ITERATO_ITERATE
unsafe def ITERATO_CLAUSES_NUMSEG_LEFT  : thm := IOrd.ITERATO_CLAUSES_NUMSEG_LEFT
-- IterateSpecial (iterate.ml 1188-1282)
unsafe def nproduct          : thm := ISpec.nproduct
unsafe def NEUTRAL_MUL       : thm := ISpec.NEUTRAL_MUL
unsafe def MONOIDAL_MUL      : thm := ISpec.MONOIDAL_MUL
unsafe def NPRODUCT_CLAUSES  : thm := ISpec.NPRODUCT_CLAUSES
unsafe def iproduct          : thm := ISpec.iproduct
unsafe def NEUTRAL_INT_MUL   : thm := ISpec.NEUTRAL_INT_MUL
unsafe def MONOIDAL_INT_MUL  : thm := ISpec.MONOIDAL_INT_MUL
unsafe def IPRODUCT_CLAUSES  : thm := ISpec.IPRODUCT_CLAUSES
unsafe def product           : thm := ISpec.product
unsafe def NEUTRAL_REAL_MUL  : thm := ISpec.NEUTRAL_REAL_MUL
unsafe def MONOIDAL_REAL_MUL : thm := ISpec.MONOIDAL_REAL_MUL
unsafe def PRODUCT_CLAUSES   : thm := ISpec.PRODUCT_CLAUSES
unsafe def isum              : thm := ISpec.isum
unsafe def NEUTRAL_INT_ADD   : thm := ISpec.NEUTRAL_INT_ADD
unsafe def MONOIDAL_INT_ADD  : thm := ISpec.MONOIDAL_INT_ADD
unsafe def ISUM_CLAUSES      : thm := ISpec.ISUM_CLAUSES
-- IterateNsum1 (iterate.ml 1288-1461)
unsafe def nsum                 : thm := IN1.nsum
unsafe def NEUTRAL_ADD          : thm := IN1.NEUTRAL_ADD
unsafe def MONOIDAL_ADD         : thm := IN1.MONOIDAL_ADD
unsafe def NSUM_DEGENERATE      : thm := IN1.NSUM_DEGENERATE
unsafe def NSUM_CLAUSES         : thm := IN1.NSUM_CLAUSES
unsafe def NSUM_UNION           : thm := IN1.NSUM_UNION
unsafe def NSUM_DIFF            : thm := IN1.NSUM_DIFF
unsafe def NSUM_INCL_EXCL       : thm := IN1.NSUM_INCL_EXCL
unsafe def NSUM_SUPPORT         : thm := IN1.NSUM_SUPPORT
unsafe def NSUM_ADD             : thm := IN1.NSUM_ADD
unsafe def NSUM_ADD_GEN         : thm := IN1.NSUM_ADD_GEN
unsafe def NSUM_EQ_0            : thm := IN1.NSUM_EQ_0
unsafe def NSUM_0               : thm := IN1.NSUM_0
unsafe def NSUM_LMUL            : thm := IN1.NSUM_LMUL
unsafe def NSUM_RMUL            : thm := IN1.NSUM_RMUL
unsafe def NSUM_LE              : thm := IN1.NSUM_LE
unsafe def NSUM_LT              : thm := IN1.NSUM_LT
unsafe def NSUM_LT_ALL          : thm := IN1.NSUM_LT_ALL
unsafe def NSUM_EQ              : thm := IN1.NSUM_EQ
unsafe def NSUM_CONST           : thm := IN1.NSUM_CONST
unsafe def NSUM_POS_BOUND       : thm := IN1.NSUM_POS_BOUND
unsafe def NSUM_EQ_0_IFF        : thm := IN1.NSUM_EQ_0_IFF
unsafe def NSUM_POS_LT          : thm := IN1.NSUM_POS_LT
unsafe def NSUM_POS_LT_ALL      : thm := IN1.NSUM_POS_LT_ALL
unsafe def NSUM_DELETE          : thm := IN1.NSUM_DELETE
unsafe def NSUM_SING            : thm := IN1.NSUM_SING
unsafe def NSUM_DELTA           : thm := IN1.NSUM_DELTA
unsafe def NSUM_SWAP            : thm := IN1.NSUM_SWAP
-- IterateNsum2 (iterate.ml 1462-1745)
unsafe def NSUM_IMAGE               : thm := IN2.NSUM_IMAGE
unsafe def NSUM_SUPERSET            : thm := IN2.NSUM_SUPERSET
unsafe def NSUM_UNIV                : thm := IN2.NSUM_UNIV
unsafe def NSUM_UNION_RZERO         : thm := IN2.NSUM_UNION_RZERO
unsafe def NSUM_UNION_LZERO         : thm := IN2.NSUM_UNION_LZERO
unsafe def NSUM_RESTRICT            : thm := IN2.NSUM_RESTRICT
unsafe def NSUM_BOUND               : thm := IN2.NSUM_BOUND
unsafe def NSUM_BOUND_GEN           : thm := IN2.NSUM_BOUND_GEN
unsafe def NSUM_BOUND_LT            : thm := IN2.NSUM_BOUND_LT
unsafe def NSUM_BOUND_LT_ALL        : thm := IN2.NSUM_BOUND_LT_ALL
unsafe def NSUM_BOUND_LT_GEN        : thm := IN2.NSUM_BOUND_LT_GEN
unsafe def NSUM_UNION_EQ            : thm := IN2.NSUM_UNION_EQ
unsafe def NSUM_EQ_SUPERSET         : thm := IN2.NSUM_EQ_SUPERSET
unsafe def NSUM_RESTRICT_SET        : thm := IN2.NSUM_RESTRICT_SET
unsafe def NSUM_NSUM_RESTRICT       : thm := IN2.NSUM_NSUM_RESTRICT
unsafe def CARD_EQ_NSUM             : thm := IN2.CARD_EQ_NSUM
unsafe def NSUM_MULTICOUNT_GEN      : thm := IN2.NSUM_MULTICOUNT_GEN
unsafe def NSUM_MULTICOUNT          : thm := IN2.NSUM_MULTICOUNT
unsafe def NSUM_IMAGE_GEN           : thm := IN2.NSUM_IMAGE_GEN
unsafe def NSUM_GROUP               : thm := IN2.NSUM_GROUP
unsafe def NSUM_GROUP_RELATION      : thm := IN2.NSUM_GROUP_RELATION
unsafe def NSUM_SUBSET              : thm := IN2.NSUM_SUBSET
unsafe def NSUM_SUBSET_SIMPLE       : thm := IN2.NSUM_SUBSET_SIMPLE
unsafe def NSUM_LE_GEN              : thm := IN2.NSUM_LE_GEN
unsafe def NSUM_MUL_BOUND           : thm := IN2.NSUM_MUL_BOUND
unsafe def NSUM_IMAGE_NONZERO       : thm := IN2.NSUM_IMAGE_NONZERO
unsafe def NSUM_BIJECTION           : thm := IN2.NSUM_BIJECTION
unsafe def NSUM_NSUM_PRODUCT        : thm := IN2.NSUM_NSUM_PRODUCT
unsafe def NSUM_EQ_GENERAL          : thm := IN2.NSUM_EQ_GENERAL
unsafe def NSUM_EQ_GENERAL_INVERSES : thm := IN2.NSUM_EQ_GENERAL_INVERSES
unsafe def NSUM_INJECTION           : thm := IN2.NSUM_INJECTION
unsafe def NSUM_UNION_NONZERO       : thm := IN2.NSUM_UNION_NONZERO
unsafe def NSUM_UNIONS_NONZERO      : thm := IN2.NSUM_UNIONS_NONZERO
unsafe def NSUM_CASES               : thm := IN2.NSUM_CASES
-- IterateNsum3 (iterate.ml 1746-1917)
unsafe def NSUM_CLOSED              : thm := IN3.NSUM_CLOSED
unsafe def NSUM_RELATED             : thm := IN3.NSUM_RELATED
unsafe def NSUM_CLOSED_NONEMPTY     : thm := IN3.NSUM_CLOSED_NONEMPTY
unsafe def NSUM_RELATED_NONEMPTY    : thm := IN3.NSUM_RELATED_NONEMPTY
unsafe def NSUM_ADD_NUMSEG          : thm := IN3.NSUM_ADD_NUMSEG
unsafe def NSUM_LE_NUMSEG           : thm := IN3.NSUM_LE_NUMSEG
unsafe def NSUM_EQ_NUMSEG           : thm := IN3.NSUM_EQ_NUMSEG
unsafe def NSUM_CONST_NUMSEG        : thm := IN3.NSUM_CONST_NUMSEG
unsafe def NSUM_EQ_0_NUMSEG         : thm := IN3.NSUM_EQ_0_NUMSEG
unsafe def NSUM_EQ_0_IFF_NUMSEG     : thm := IN3.NSUM_EQ_0_IFF_NUMSEG
unsafe def NSUM_TRIV_NUMSEG         : thm := IN3.NSUM_TRIV_NUMSEG
unsafe def NSUM_SING_NUMSEG         : thm := IN3.NSUM_SING_NUMSEG
unsafe def NSUM_CLAUSES_NUMSEG      : thm := IN3.NSUM_CLAUSES_NUMSEG
unsafe def NSUM_CLAUSES_NUMSEG_LT   : thm := IN3.NSUM_CLAUSES_NUMSEG_LT
unsafe def NSUM_CLAUSES_NUMSEG_LE   : thm := IN3.NSUM_CLAUSES_NUMSEG_LE
unsafe def NSUM_SWAP_NUMSEG         : thm := IN3.NSUM_SWAP_NUMSEG
unsafe def NSUM_ADD_SPLIT           : thm := IN3.NSUM_ADD_SPLIT
unsafe def NSUM_OFFSET              : thm := IN3.NSUM_OFFSET
unsafe def NSUM_OFFSET_0            : thm := IN3.NSUM_OFFSET_0
unsafe def NSUM_CLAUSES_LEFT        : thm := IN3.NSUM_CLAUSES_LEFT
unsafe def NSUM_CLAUSES_RIGHT       : thm := IN3.NSUM_CLAUSES_RIGHT
unsafe def NSUM_PAIR                : thm := IN3.NSUM_PAIR
unsafe def NSUM_REFLECT             : thm := IN3.NSUM_REFLECT
unsafe def MOD_NSUM_MOD             : thm := IN3.MOD_NSUM_MOD
unsafe def MOD_NSUM_MOD_NUMSEG      : thm := IN3.MOD_NSUM_MOD_NUMSEG
unsafe def CONG_NSUM                : thm := IN3.CONG_NSUM
unsafe def NSUM_CONG                : thm := IN3.NSUM_CONG
-- IterateNsumCard (iterate.ml 1920-1978)
unsafe def CARD_UNIONS_IMAGE        : thm := INCard.CARD_UNIONS_IMAGE
unsafe def CARD_UNIONS              : thm := INCard.CARD_UNIONS
unsafe def EXPAND_NSUM_CONV_pth_0   : thm := INCard.pth_0
unsafe def EXPAND_NSUM_CONV_pth_1   : thm := INCard.pth_1
unsafe def EXPAND_NSUM_CONV_pth_2   : thm := INCard.pth_2
unsafe def EXPAND_NSUM_CONV : ioconv := INCard.EXPAND_NSUM_CONV
-- IterateSum1 (iterate.ml 1984-2211): sum + core algebra/ordering/bounds.
unsafe def sum                 : thm := IS1.sum
unsafe def NEUTRAL_REAL_ADD    : thm := IS1.NEUTRAL_REAL_ADD
unsafe def MONOIDAL_REAL_ADD   : thm := IS1.MONOIDAL_REAL_ADD
unsafe def SUM_DEGENERATE      : thm := IS1.SUM_DEGENERATE
unsafe def SUM_CLAUSES         : thm := IS1.SUM_CLAUSES
unsafe def SUM_UNION           : thm := IS1.SUM_UNION
unsafe def SUM_DIFF            : thm := IS1.SUM_DIFF
unsafe def SUM_INCL_EXCL       : thm := IS1.SUM_INCL_EXCL
unsafe def SUM_SUPPORT         : thm := IS1.SUM_SUPPORT
unsafe def SUM_ADD             : thm := IS1.SUM_ADD
unsafe def SUM_ADD_GEN         : thm := IS1.SUM_ADD_GEN
unsafe def SUM_EQ_0            : thm := IS1.SUM_EQ_0
unsafe def SUM_0               : thm := IS1.SUM_0
unsafe def SUM_LMUL            : thm := IS1.SUM_LMUL
unsafe def SUM_RMUL            : thm := IS1.SUM_RMUL
unsafe def SUM_NEG             : thm := IS1.SUM_NEG
unsafe def SUM_SUB             : thm := IS1.SUM_SUB
unsafe def SUM_LE              : thm := IS1.SUM_LE
unsafe def SUM_LT              : thm := IS1.SUM_LT
unsafe def SUM_LT_ALL          : thm := IS1.SUM_LT_ALL
unsafe def SUM_POS_LT          : thm := IS1.SUM_POS_LT
unsafe def SUM_POS_LT_ALL      : thm := IS1.SUM_POS_LT_ALL
unsafe def SUM_EQ              : thm := IS1.SUM_EQ
unsafe def SUM_ABS            : thm := IS1.SUM_ABS
unsafe def SUM_ABS_LE          : thm := IS1.SUM_ABS_LE
unsafe def SUM_CONST           : thm := IS1.SUM_CONST
unsafe def SUM_POS_LE          : thm := IS1.SUM_POS_LE
unsafe def SUM_POS_BOUND       : thm := IS1.SUM_POS_BOUND
unsafe def SUM_POS_EQ_0        : thm := IS1.SUM_POS_EQ_0
unsafe def SUM_ZERO_EXISTS     : thm := IS1.SUM_ZERO_EXISTS
unsafe def SUM_DELETE          : thm := IS1.SUM_DELETE
unsafe def SUM_DELETE_CASES    : thm := IS1.SUM_DELETE_CASES
unsafe def SUM_SING            : thm := IS1.SUM_SING
unsafe def SUM_DELTA           : thm := IS1.SUM_DELTA
unsafe def SUM_SWAP            : thm := IS1.SUM_SWAP
-- IterateSum2 (iterate.ml 2219-2598): image/count/group/subset/general.
unsafe def SUM_IMAGE               : thm := IS2.SUM_IMAGE
unsafe def SUM_SUPERSET            : thm := IS2.SUM_SUPERSET
unsafe def SUM_UNIV                : thm := IS2.SUM_UNIV
unsafe def SUM_UNION_RZERO         : thm := IS2.SUM_UNION_RZERO
unsafe def SUM_UNION_LZERO         : thm := IS2.SUM_UNION_LZERO
unsafe def SUM_RESTRICT            : thm := IS2.SUM_RESTRICT
unsafe def SUM_BOUND               : thm := IS2.SUM_BOUND
unsafe def SUM_BOUND_GEN           : thm := IS2.SUM_BOUND_GEN
unsafe def SUM_ABS_BOUND           : thm := IS2.SUM_ABS_BOUND
unsafe def SUM_BOUND_LT            : thm := IS2.SUM_BOUND_LT
unsafe def SUM_BOUND_LT_ALL        : thm := IS2.SUM_BOUND_LT_ALL
unsafe def SUM_BOUND_LT_GEN        : thm := IS2.SUM_BOUND_LT_GEN
unsafe def SUM_UNION_EQ            : thm := IS2.SUM_UNION_EQ
unsafe def SUM_EQ_SUPERSET         : thm := IS2.SUM_EQ_SUPERSET
unsafe def SUM_RESTRICT_SET        : thm := IS2.SUM_RESTRICT_SET
unsafe def SUM_SUM_RESTRICT        : thm := IS2.SUM_SUM_RESTRICT
unsafe def CARD_EQ_SUM             : thm := IS2.CARD_EQ_SUM
unsafe def SUM_MULTICOUNT_GEN      : thm := IS2.SUM_MULTICOUNT_GEN
unsafe def SUM_MULTICOUNT          : thm := IS2.SUM_MULTICOUNT
unsafe def SUM_IMAGE_GEN           : thm := IS2.SUM_IMAGE_GEN
unsafe def SUM_GROUP               : thm := IS2.SUM_GROUP
unsafe def SUM_GROUP_RELATION      : thm := IS2.SUM_GROUP_RELATION
unsafe def REAL_OF_NUM_SUM         : thm := IS2.REAL_OF_NUM_SUM
unsafe def SUM_SUBSET              : thm := IS2.SUM_SUBSET
unsafe def SUM_SUBSET_SIMPLE       : thm := IS2.SUM_SUBSET_SIMPLE
unsafe def SUM_MUL_BOUND           : thm := IS2.SUM_MUL_BOUND
unsafe def SUM_IMAGE_NONZERO       : thm := IS2.SUM_IMAGE_NONZERO
unsafe def SUM_BIJECTION           : thm := IS2.SUM_BIJECTION
unsafe def SUM_SUM_PRODUCT         : thm := IS2.SUM_SUM_PRODUCT
unsafe def SUM_EQ_GENERAL          : thm := IS2.SUM_EQ_GENERAL
unsafe def SUM_EQ_GENERAL_INVERSES : thm := IS2.SUM_EQ_GENERAL_INVERSES
unsafe def SUM_INJECTION           : thm := IS2.SUM_INJECTION
unsafe def SUM_UNION_NONZERO       : thm := IS2.SUM_UNION_NONZERO
unsafe def SUM_UNIONS_NONZERO      : thm := IS2.SUM_UNIONS_NONZERO
unsafe def SUM_CASES               : thm := IS2.SUM_CASES
unsafe def SUM_CASES_1             : thm := IS2.SUM_CASES_1
unsafe def SUM_LE_INCLUDED         : thm := IS2.SUM_LE_INCLUDED
unsafe def SUM_IMAGE_LE            : thm := IS2.SUM_IMAGE_LE
unsafe def SUM_CLOSED              : thm := IS2.SUM_CLOSED
unsafe def SUM_RELATED             : thm := IS2.SUM_RELATED
unsafe def SUM_CLOSED_NONEMPTY     : thm := IS2.SUM_CLOSED_NONEMPTY
unsafe def SUM_RELATED_NONEMPTY    : thm := IS2.SUM_RELATED_NONEMPTY
unsafe def REAL_OF_NUM_SUM_GEN     : thm := IS2.REAL_OF_NUM_SUM_GEN
-- IterateSum3 (iterate.ml 2599-2778): numseg intervals + partial summation.
unsafe def SUM_ADD_NUMSEG          : thm := IS3.SUM_ADD_NUMSEG
unsafe def SUM_SUB_NUMSEG          : thm := IS3.SUM_SUB_NUMSEG
unsafe def SUM_LE_NUMSEG           : thm := IS3.SUM_LE_NUMSEG
unsafe def SUM_EQ_NUMSEG           : thm := IS3.SUM_EQ_NUMSEG
unsafe def SUM_ABS_NUMSEG          : thm := IS3.SUM_ABS_NUMSEG
unsafe def SUM_CONST_NUMSEG        : thm := IS3.SUM_CONST_NUMSEG
unsafe def SUM_EQ_0_NUMSEG         : thm := IS3.SUM_EQ_0_NUMSEG
unsafe def SUM_TRIV_NUMSEG         : thm := IS3.SUM_TRIV_NUMSEG
unsafe def SUM_POS_LE_NUMSEG       : thm := IS3.SUM_POS_LE_NUMSEG
unsafe def SUM_POS_EQ_0_NUMSEG     : thm := IS3.SUM_POS_EQ_0_NUMSEG
unsafe def SUM_SING_NUMSEG         : thm := IS3.SUM_SING_NUMSEG
unsafe def SUM_CLAUSES_NUMSEG      : thm := IS3.SUM_CLAUSES_NUMSEG
unsafe def SUM_CLAUSES_NUMSEG_LT   : thm := IS3.SUM_CLAUSES_NUMSEG_LT
unsafe def SUM_CLAUSES_NUMSEG_LE   : thm := IS3.SUM_CLAUSES_NUMSEG_LE
unsafe def SUM_SWAP_NUMSEG         : thm := IS3.SUM_SWAP_NUMSEG
unsafe def SUM_ADD_SPLIT           : thm := IS3.SUM_ADD_SPLIT
unsafe def SUM_OFFSET              : thm := IS3.SUM_OFFSET
unsafe def SUM_OFFSET_0            : thm := IS3.SUM_OFFSET_0
unsafe def SUM_CLAUSES_LEFT        : thm := IS3.SUM_CLAUSES_LEFT
unsafe def SUM_CLAUSES_RIGHT       : thm := IS3.SUM_CLAUSES_RIGHT
unsafe def SUM_PAIR                : thm := IS3.SUM_PAIR
unsafe def SUM_REFLECT             : thm := IS3.SUM_REFLECT
unsafe def REAL_OF_NUM_SUM_NUMSEG  : thm := IS3.REAL_OF_NUM_SUM_NUMSEG
unsafe def SUM_PARTIAL_SUC         : thm := IS3.SUM_PARTIAL_SUC
unsafe def SUM_PARTIAL_PRE         : thm := IS3.SUM_PARTIAL_PRE
unsafe def SUM_DIFFS               : thm := IS3.SUM_DIFFS
unsafe def SUM_DIFFS_ALT           : thm := IS3.SUM_DIFFS_ALT
unsafe def SUM_COMBINE_R           : thm := IS3.SUM_COMBINE_R
unsafe def SUM_COMBINE_L           : thm := IS3.SUM_COMBINE_L
-- IterateSum4 (iterate.ml 2779-2854): congruences, EXPAND_SUM_CONV, REAL_SUB_POW.
unsafe def SUM_CONG                : thm := IS4.SUM_CONG
unsafe def EXPAND_SUM_CONV_pth_0   : thm := IS4.pth_0
unsafe def EXPAND_SUM_CONV_pth_1   : thm := IS4.pth_1
unsafe def EXPAND_SUM_CONV_pth_2   : thm := IS4.pth_2
unsafe def EXPAND_SUM_CONV : ioconv := IS4.EXPAND_SUM_CONV
unsafe def REAL_SUB_POW            : thm := IS4.REAL_SUB_POW
unsafe def REAL_SUB_POW_R1         : thm := IS4.REAL_SUB_POW_R1
unsafe def REAL_SUB_POW_L1         : thm := IS4.REAL_SUB_POW_L1
-- IterateSum5 (iterate.ml 2855-3108): real polynomial functions.
unsafe def REAL_SUB_POLYFUN        : thm := IS5.REAL_SUB_POLYFUN
unsafe def REAL_SUB_POLYFUN_ALT    : thm := IS5.REAL_SUB_POLYFUN_ALT
unsafe def REAL_POLYFUN_ROOTBOUND  : thm := IS5.REAL_POLYFUN_ROOTBOUND
unsafe def REAL_POLYFUN_FINITE_ROOTS : thm := IS5.REAL_POLYFUN_FINITE_ROOTS
unsafe def REAL_POLYFUN_EQ_0       : thm := IS5.REAL_POLYFUN_EQ_0
unsafe def REAL_POLYFUN_EQ_CONST   : thm := IS5.REAL_POLYFUN_EQ_CONST
unsafe def polynomial_function     : thm := IS5.polynomial_function
unsafe def POLYNOMIAL_FUNCTION_CONST : thm := IS5.POLYNOMIAL_FUNCTION_CONST
unsafe def POLYNOMIAL_FUNCTION_ID  : thm := IS5.POLYNOMIAL_FUNCTION_ID
unsafe def POLYNOMIAL_FUNCTION_I   : thm := IS5.POLYNOMIAL_FUNCTION_I
unsafe def POLYNOMIAL_FUNCTION_ADD : thm := IS5.POLYNOMIAL_FUNCTION_ADD
unsafe def POLYNOMIAL_FUNCTION_LMUL : thm := IS5.POLYNOMIAL_FUNCTION_LMUL
unsafe def POLYNOMIAL_FUNCTION_RMUL : thm := IS5.POLYNOMIAL_FUNCTION_RMUL
unsafe def POLYNOMIAL_FUNCTION_NEG : thm := IS5.POLYNOMIAL_FUNCTION_NEG
unsafe def POLYNOMIAL_FUNCTION_SUB : thm := IS5.POLYNOMIAL_FUNCTION_SUB
unsafe def POLYNOMIAL_FUNCTION_MUL : thm := IS5.POLYNOMIAL_FUNCTION_MUL
unsafe def POLYNOMIAL_FUNCTION_SUM : thm := IS5.POLYNOMIAL_FUNCTION_SUM
unsafe def POLYNOMIAL_FUNCTION_POW : thm := IS5.POLYNOMIAL_FUNCTION_POW
unsafe def POLYNOMIAL_FUNCTION_INDUCT : thm := IS5.POLYNOMIAL_FUNCTION_INDUCT
unsafe def POLYNOMIAL_FUNCTION_o   : thm := IS5.POLYNOMIAL_FUNCTION_o
unsafe def POLYNOMIAL_FUNCTION_FINITE_ROOTS : thm := IS5.POLYNOMIAL_FUNCTION_FINITE_ROOTS

/- ====================================================================== -/
/- cart.ml wiring.  Mirrors the iterate.ml block above: one cache +        -/
/- accessor per bundle and an `ensureCart` forcing them in FILE ORDER.     -/
/- `ensureIterate` runs first because cart.ml opens `needs "iterate.ml"`   -/
/- (cart.ml 7), exactly as `ensureIterate` begins with `ensureSets`.       -/
/- ====================================================================== -/

/-- Cache for `CartDimindex` (cart.ml 14-48): the `dimindex` definition and
    its eight theorems.  `dimindex` is the sole `new_definition` of the range,
    threaded in from Session (a kernel side effect, run in file order).  Enters
    through `ensureIterate` for `NUMSEG_LT` (iterate.ml) and the sets.ml
    CARD/HAS_SIZE layer.  Threads the Bool/Class bundles, the decision
    procedures, and the theorem dependencies as Session accessors. -/
initialize theCartDimindex : IO.Ref (Option HolMath.Cart.CartDimindex) ← IO.mkRef none

private unsafe def CDim : HolMath.Cart.CartDimindex :=
  match unsafeIO (do
    match ← theCartDimindex.get with
    | some d => pure d
    | none => do
      ensureIterate
      match ← (HolMath.Cart.setupCartDimindex new_definition
                 MESON_TAC SET_TAC ARITH_RULE one
                 HAS_SIZE CARD_EQ_0 CARD_CLAUSES FINITE_RULES EXTENSION
                 IN_UNIV IN_SING NOT_IN_EMPTY ARITH NUMSEG_LT).run with
      | .ok d => do theCartDimindex.set (some d); pure d
      | .error e => panic! s!"setupCartDimindex failed: {e}") with
  | .ok d => d | _ => panic! "Session.CDim: setupCartDimindex not run"

/-- Cache for `CartFiniteImage` (cart.ml 54-105): the FIRST `new_type_definition`
    in the development.  Creating the `finite_image` type operator and its
    `finite_index`/`dest_finite_image` abstraction/representation pair is a
    KERNEL side effect, so - like `one_tydef` and `int_tybij` - it lives in this
    once-only CAF and must run EXACTLY ONCE and IN FILE ORDER (after `CDim`,
    since the existence proof needs `DIMINDEX_GE_1`).  `new_type_definition` is
    passed into the pure HolMath layer as a parameter; forcing `CFImg` extends
    the type-constructor table so that `get_type_arity "finite_image"` succeeds
    afterwards.  Depends on `CDim` and threaded Sets/Iterate theorems. -/
initialize theCartFiniteImage : IO.Ref (Option HolMath.Cart.CartFiniteImage) ← IO.mkRef none

private unsafe def CFImg : HolMath.Cart.CartFiniteImage :=
  match unsafeIO (do
    match ← theCartFiniteImage.get with
    | some d => pure d
    | none => do
      ensureIterate
      match ← (HolMath.Cart.setupCartFiniteImage new_type_definition
                 MESON_TAC CDim
                 IN_NUMSEG LE_REFL EXTENSION IN_UNIV IN_IMAGE HAS_SIZE
                 HAS_SIZE_IMAGE_INJ HAS_SIZE_NUMSEG_1 CONJ_ASSOC).run with
      | .ok d => do theCartFiniteImage.set (some d); pure d
      | .error e => panic! s!"setupCartFiniteImage failed: {e}") with
  | .ok d => d | _ => panic! "Session.CFImg: setupCartFiniteImage not run"

/-- Once-only guard for the SECOND parser side effect of cart.ml:
    `parse_as_infix("$",(25,"left"))` at cart.ml 115 - vector indexing at
    precedence 25, LEFT-associative.  Like `ensureSetsInfixes` /
    `ensureIterateInfix` this is an `IO` ACTION with its own flag, NOT a
    memoised `Unit` CAF: a `let _ := <caf>` would not force
    it, so `x$i` would parse as `x` applied to `$` and `i` (juxtaposition)
    instead of the infix.  `CCart` awaits this, so the `finite_index`
    `new_definition` body (cart.ml 118, the FIRST `$` term) and every `x$i` in
    the bundle parse `$` as the registered infix.  Its TRUE file position is
    cart.ml 115, BETWEEN the `cart` type creation (112) and `finite_index`
    (117) - forced there by `ensureCart`. -/
initialize theCartDollarInfix : IO.Ref Bool ← IO.mkRef false

private def ensureCartDollarInfix : IO Unit := do
  unless (← theCartDollarInfix.get) do
    HolMath.Cart.setupCartDollarInfix
    theCartDollarInfix.set true

/-- Once-only guard for the THIRD parser side effect of cart.ml, and the ONE a
    `parse_as_infix`-only survey would MISS: `parse_as_binder "lambda"` at
    cart.ml 126 - vector abstraction.  Like `ensureCartDollarInfix` this is an
    `IO` ACTION with its own flag, NOT a memoised `Unit` CAF:
    a `let _ := <caf>` would not force it, so `lambda i. ...` would give
    "Unparsed input following term".  Same precedent as the `minimal` binder
    (`setupMinimalBinder`).  `CCart` awaits this, so the `lambda`
    `new_definition` body (cart.ml 130) and `LAMBDA_ETA`'s `lambda i. g$i`
    parse `lambda` as the binder.  Its TRUE file position is cart.ml 126,
    AFTER `$`/`finite_index`/`CART_EQ` and BEFORE the `lambda` definition -
    forced there by `ensureCart`. -/
initialize theCartLambdaBinder : IO.Ref Bool ← IO.mkRef false

private def ensureCartLambdaBinder : IO Unit := do
  unless (← theCartLambdaBinder.get) do
    HolMath.Cart.setupCartLambdaBinder
    theCartLambdaBinder.set true

/-- Cache for `CartCart` (cart.ml 111-168): the CENTRE of the file.  Creating
    the `cart` type operator (cart.ml 112, `new_type_definition`) is the KERNEL
    side effect that ACTIVATES the parser/printer `^` type infix, so - like
    `CFImg` - it lives in this once-only CAF and runs EXACTLY ONCE and IN FILE
    ORDER (after `CFImg`, since `cart`'s existence type mentions
    `(B)finite_image`).  `new_type_definition` and `new_definition` are threaded
    into the pure HolMath layer as parameters.  The `$` infix (115) and the
    `lambda` binder (126) are installed FIRST via `ensureCartDollarInfix` /
    `ensureCartLambdaBinder` so the bundle's definition bodies parse those
    symbols correctly - their TRUE file positions are interleaved inside this
    range, documented on each guard and forced in order by `ensureCart`.
    Depends on `CFImg` and threaded core rules. -/
initialize theCartCart : IO.Ref (Option HolMath.Cart.CartCart) ← IO.mkRef none

private unsafe def CCart : HolMath.Cart.CartCart :=
  match unsafeIO (do
    match ← theCartCart.get with
    | some d => pure d
    | none => do
      ensureIterate
      -- Parser side effects at their TRUE file positions (cart.ml 115, 126),
      -- installed BEFORE the bundle parses the bodies that use `$` / `lambda`.
      ensureCartDollarInfix
      ensureCartLambdaBinder
      match ← (HolMath.Cart.setupCartCart new_type_definition new_definition
                 MESON_TAC ASM_MESON_TAC SELECT_CONV CFImg
                 FUN_EQ_THM ETA_AX C.SELECT_UNIQUE).run with
      | .ok d => do theCartCart.set (some d); pure d
      | .error e => panic! s!"setupCartCart failed: {e}") with
  | .ok d => d | _ => panic! "Session.CCart: setupCartCart not run"

/-- Cache for `CartFiniteSum` (cart.ml 174-273): the THIRD `new_type_definition`
    of the file, and the FIRST applied to a LOCALLY PROVED nonemptiness theorem.
    Creating the binary type operator `finite_sum` (and its `mk_finite_sum`/
    `dest_finite_sum` abstraction/representation pair) is a KERNEL side effect,
    so - like `CFImg` and `CCart` - it lives in this once-only CAF and runs
    EXACTLY ONCE and IN FILE ORDER (after `CCart`, since `pastecart`/`fstcart`/
    `sndcart` use the `$` infix / `lambda` binder and `CART_EQ`/`LAMBDA_BETA`).
    The existence proof is built PURELY inside the HolMath layer and fed to the
    threaded `new_type_definition`; forcing `CFSum` extends the type-constructor
    table so that `get_type_arity "finite_sum"` succeeds afterwards.  Depends on
    `CDim`, `CCart`, the arithmetic layer (`ARITH_RULE`/`ASM_ARITH_TAC` from
    `IAr`), and threaded Sets/Iterate theorems. -/
initialize theCartFiniteSum : IO.Ref (Option HolMath.Cart.CartFiniteSum) ← IO.mkRef none

private unsafe def CFSum : HolMath.Cart.CartFiniteSum :=
  match unsafeIO (do
    match ← theCartFiniteSum.get with
    | some d => pure d
    | none => do
      ensureIterate
      match ← (HolMath.Cart.setupCartFiniteSum new_type_definition
                 new_definition MESON_TAC ARITH_RULE IAr.ASM_ARITH_TAC
                 CDim CCart
                 IN_NUMSEG LE_REFL EXTENSION IN_UNIV IN_IMAGE HAS_SIZE
                 HAS_SIZE_IMAGE_INJ HAS_SIZE_NUMSEG_1 ADD_SUB).run with
      | .ok d => do theCartFiniteSum.set (some d); pure d
      | .error e => panic! s!"setupCartFiniteSum failed: {e}") with
  | .ok d => d | _ => panic! "Session.CFSum: setupCartFiniteSum not run"

/-- Cache for `CartFiniteDiff` (cart.ml 279-305): the FOURTH `new_type_definition`
    of the file, applied - like `finite_sum` - to a LOCALLY PROVED nonemptiness
    theorem.  Creating the binary type operator `finite_diff` (and its
    `mk_finite_diff`/`dest_finite_diff` abstraction/representation pair) is a
    KERNEL side effect, so it lives in this once-only CAF and runs EXACTLY ONCE
    and IN FILE ORDER (after `CFSum`).  The existence proof is built PURELY
    inside the HolMath layer (closer `ARITH_TAC`, rewrite list `[IN_NUMSEG]`)
    and fed to the threaded `new_type_definition`; forcing `CFDiff` extends the
    type-constructor table so that `get_type_arity "finite_diff"` succeeds
    afterwards.  Depends on `CDim`, `ARITH_TAC` (from `IAr`), and threaded
    Sets/Iterate theorems. -/
initialize theCartFiniteDiff : IO.Ref (Option HolMath.Cart.CartFiniteDiff) ← IO.mkRef none

private unsafe def CFDiff : HolMath.Cart.CartFiniteDiff :=
  match unsafeIO (do
    match ← theCartFiniteDiff.get with
    | some d => pure d
    | none => do
      ensureIterate
      match ← (HolMath.Cart.setupCartFiniteDiff new_type_definition
                 MESON_TAC IAr.ARITH_TAC CDim
                 IN_NUMSEG EXTENSION IN_UNIV IN_IMAGE HAS_SIZE
                 HAS_SIZE_IMAGE_INJ HAS_SIZE_NUMSEG_1).run with
      | .ok d => do theCartFiniteDiff.set (some d); pure d
      | .error e => panic! s!"setupCartFiniteDiff failed: {e}") with
  | .ok d => d | _ => panic! "Session.CFDiff: setupCartFiniteDiff not run"

/-- Cache for `CartFiniteProd` (cart.ml 312-335): the FIFTH `new_type_definition`
    of the file, applied - like `finite_sum`/`finite_diff` - to a LOCALLY PROVED
    nonemptiness theorem.  Creating the binary type operator `finite_prod` (and
    its `mk_finite_prod`/`dest_finite_prod` abstraction/representation pair) is a
    KERNEL side effect, so it lives in this once-only CAF and runs EXACTLY ONCE
    and IN FILE ORDER (after `CFDiff`).  The existence proof is built PURELY
    inside the HolMath layer (closer `MESON_TAC[LE_1; DIMINDEX_GE_1; MULT_EQ_0]`,
    rewrite list `[IN_NUMSEG; LE_REFL]` - DIFFERENT from `finite_diff`'s) and fed
    to the threaded `new_type_definition`; forcing `CFProd` extends the
    type-constructor table so that `get_type_arity "finite_prod"` succeeds
    afterwards.  Depends on `CDim`, the arithmetic lemmas `LE_1`/`MULT_EQ_0`,
    and threaded Sets/Iterate theorems. -/
initialize theCartFiniteProd : IO.Ref (Option HolMath.Cart.CartFiniteProd) ← IO.mkRef none

private unsafe def CFProd : HolMath.Cart.CartFiniteProd :=
  match unsafeIO (do
    match ← theCartFiniteProd.get with
    | some d => pure d
    | none => do
      ensureIterate
      match ← (HolMath.Cart.setupCartFiniteProd new_type_definition
                 MESON_TAC CDim
                 IN_NUMSEG LE_REFL EXTENSION IN_UNIV IN_IMAGE HAS_SIZE
                 HAS_SIZE_IMAGE_INJ HAS_SIZE_NUMSEG_1 LE_1 MULT_EQ_0).run with
      | .ok d => do theCartFiniteProd.set (some d); pure d
      | .error e => panic! s!"setupCartFiniteProd failed: {e}") with
  | .ok d => d | _ => panic! "Session.CFProd: setupCartFiniteProd not run"

/-- Cache for `CartTybit` (cart.ml 338-405): the two `define_type` calls that
    create the binary "bit" type constructors `tybit0`/`tybit1`, plus their
    size/dimindex/finiteness theory.  This is what makes `:2`, `:3`, `:4` ...
    exist as types, and hence what makes `:real^3` mean anything.

    `define_type` defines an inductive type and returns a pair (INDUCT,
    RECURSION), so each of the two calls binds two names, and populates the
    `cases`/`injectivity`/`distinctness` rectype stores.  It runs exactly once
    and in file order (after `CFProd`, i.e. after all five
    `new_type_definition`s; `tybit0`'s body mentions `finite_sum`).

    Order is load-bearing even between the two `define_type` lines: `tybit1`'s
    body `mktybit1(((A,A)finite_sum,1)finite_sum)` mentions the type `1`, so
    `1` must already exist and `tybit0` (341) must precede `tybit1` (344).  We
    run `tybit0` first, then `tybit1`, then read the `cases`/`injectivity`
    theorems they populated and hand them to the pure `setupCartTybit`.  Forcing
    `CTybit` extends the type-constructor table so `get_type_arity
    "tybit0"`/`"tybit1"` succeed and `:2`/`:3`/`:4`/`:real^3` parse.  Depends on
    `CFSum`, `CDim`, threaded Sets theorems, and `MULT_2`. -/
initialize theCartTybit : IO.Ref (Option HolMath.Cart.CartTybit) ← IO.mkRef none

private unsafe def CTybit : HolMath.Cart.CartTybit :=
  match unsafeIO (do
    match ← theCartTybit.get with
    | some d => pure d
    | none => do
      ensureIterate
      -- Force `finite_sum` first (tybit0's body mentions `(A,A)finite_sum`).
      let _ ← IO.mkRef (concl CFSum.finite_sum_tybij)
      -- cart.ml 341-342: the FIRST define_type.  MUST run before line 344.
      let ⟨tybit0_INDUCT, tybit0_RECURSION⟩ ←
        (match ← define_type "tybit0 = mktybit0((A,A)finite_sum)" with
         | .ok x => pure x | .error e => panic! s!"define_type tybit0: {e}")
      -- cart.ml 344-345: the SECOND define_type.  Its body mentions the type
      -- `1`, so `1` must already exist; `tybit0` must already be defined.
      let ⟨tybit1_INDUCT, tybit1_RECURSION⟩ ←
        (match ← define_type "tybit1 = mktybit1(((A,A)finite_sum,1)finite_sum)" with
         | .ok x => pure x | .error e => panic! s!"define_type tybit1: {e}")
      -- Read the rectype theorems the two define_type calls populated.
      let cases0 ← (match ← cases "tybit0" with
        | .ok th => pure th | .error e => panic! s!"cases tybit0: {e}")
      let inj0 ← (match injectivity "tybit0" with
        | .ok th => pure th | .error e => panic! s!"injectivity tybit0: {e}")
      let cases1 ← (match ← cases "tybit1" with
        | .ok th => pure th | .error e => panic! s!"cases tybit1: {e}")
      let inj1 ← (match injectivity "tybit1" with
        | .ok th => pure th | .error e => panic! s!"injectivity tybit1: {e}")
      match ← (HolMath.Cart.setupCartTybit MESON_TAC
                 tybit0_INDUCT tybit0_RECURSION tybit1_INDUCT tybit1_RECURSION
                 cases0 inj0 cases1 inj1
                 CDim.DIMINDEX_UNIQUE CDim.HAS_SIZE_1 CDim.DIMINDEX_1
                 CFSum.DIMINDEX_HAS_SIZE_FINITE_SUM CFSum.DIMINDEX_FINITE_SUM
                 SURJECTIVE_IMAGE_EQ HAS_SIZE_IMAGE_INJ IN_UNIV HAS_SIZE
                 MULT_2).run with
      | .ok d => do theCartTybit.set (some d); pure d
      | .error e => panic! s!"setupCartTybit failed: {e}") with
  | .ok d => d | _ => panic! "Session.CTybit: setupCartTybit not run"

/-- Cache for `CartDimindexConv` (cart.ml 406-479): the `dimindex`-computing
    conversion `DIMINDEX_CONV` (with its rule `HAS_SIZE_DIMINDEX_RULE` and
    tactic `DIMINDEX_TAC`), and the payoff theorems for cases 2, 3 and 4 -
    `dimindex(:2)/(:3)/(:4) = 2/3/4` and `(:2)/(:3)/(:4) HAS_SIZE 2/3/4`.
    These are what make `:2`/`:3`/`:4` USABLE (every later `real^N` dimension
    result rests on `DIMINDEX_2/3/4`).  Pure over `CTybit`/`CDim`; enters
    through `ensureIterate` for the sets/arith layer.  `BITS_ELIM_CONV` is an
    `IO`-computed conversion, so it is forced once and threaded in.  No new
    kernel/parser side effects here - runs in file order AFTER `CTybit`. -/
initialize theCartDimindexConv : IO.Ref (Option HolMath.Cart.CartDimindexConv) ← IO.mkRef none

private unsafe def CDConv : HolMath.Cart.CartDimindexConv :=
  match unsafeIO (do
    match ← theCartDimindexConv.get with
    | some d => pure d
    | none => do
      ensureIterate
      -- Force the tybit theory first (DIMINDEX_CLAUSES / FINITE_CLAUSES live in
      -- CTybit, and :2/:3/:4 need the tybit0/tybit1 type constructors).
      let _ ← IO.mkRef (concl CTybit.DIMINDEX_CLAUSES)
      let bitsElim ← (match ← BITS_ELIM_CONV with
        | .ok c => pure c | .error e => panic! s!"BITS_ELIM_CONV: {e}")
      match ← (HolMath.Cart.setupCartDimindexConv IAr.ARITH_TAC MESON_TAC mk_numeral
                 (fun t => pure (bitsElim t))
                 NUMERAL CDim.dimindex CTybit.DIMINDEX_CLAUSES
                 CDim.UNIV_HAS_SIZE_DIMINDEX HAS_SIZE CTybit.FINITE_CLAUSES).run with
      | .ok d => do theCartDimindexConv.set (some d); pure d
      | .error e => panic! s!"setupCartDimindexConv failed: {e}") with
  | .ok d => d | _ => panic! "Session.CDConv: setupCartDimindexConv not run"

/-- `DIMINDEX_CONV` (cart.ml 409). -/
unsafe def DIMINDEX_CONV : conv := fun tm => CDConv.DIMINDEX_CONV tm
/-- `HAS_SIZE_DIMINDEX_RULE` (cart.ml 442). -/
unsafe def HAS_SIZE_DIMINDEX_RULE (ty : hol_type) : IO (Except String thm) :=
  CDConv.HAS_SIZE_DIMINDEX_RULE ty
/-- `DIMINDEX_TAC` (cart.ml 456). -/
unsafe def DIMINDEX_TAC : tactic := fun g => CDConv.DIMINDEX_TAC g

/-- Cache for `CartFinite` (cart.ml 480-548): the finiteness lemma
    `FINITE_CART` and the three whole-universe cardinality results
    (`HAS_SIZE_CART_UNIV`/`CARD_CART_UNIV`/`FINITE_CART_UNIV`).  Pure over
    `CCart`/`CFImg`; enters through `ensureIterate` for the Sets/Pair/arith
    layer, with no new kernel/parser side effects, and runs in file order after
    `CDConv`. -/
initialize theCartFinite : IO.Ref (Option HolMath.Cart.CartFinite) ← IO.mkRef none

private unsafe def CFin : HolMath.Cart.CartFinite :=
  match unsafeIO (do
    match ← theCartFinite.get with
    | some d => pure d
    | none => do
      ensureIterate
      -- Force the dimindex-conv theory first (this range rests on the `cart`
      -- type via CCart and on the finite_image layer via CFImg).
      let _ ← IO.mkRef (concl CDConv.DIMINDEX_2)
      match ← (HolMath.Cart.setupCartFinite MESON_TAC ASM_MESON_TAC
                 ARITH_RULE INDUCT_TAC CCart CFImg
                 LE_REFL LET_ANTISYM LE
                 FINITE_RULES IN_ELIM_THM EXTENSION SUBSET IN_SING IN_IMAGE
                 IN_UNIV IN_ELIM_PAIR_THM EXISTS_PAIR_THM FINITE_SUBSET
                 FINITE_IMAGE FINITE_PRODUCT SURJECTIVE_IMAGE_EQ
                 HAS_SIZE_IMAGE_INJ HAS_SIZE_FUNSPACE_UNIV HAS_SIZE
                 IMP_CONJ_ALT EQ_IMP).run with
      | .ok d => do theCartFinite.set (some d); pure d
      | .error e => panic! s!"setupCartFinite failed: {e}") with
  | .ok d => d | _ => panic! "Session.CFin: setupCartFinite not run"

/-- Cache for `CartVector` (cart.ml 551-567): the `vector` definition and the
    `IN_ELIM_PASTECART_THM` membership-elimination theorem.  `vector` is the
    FIRST cart-layer definition to reach DOWN to the lists layer - its body
    `lambda i. EL (i - 1) l` names the `EL` constant - so we force `listDefs`
    (which declares `EL`) BEFORE running the setup, mirroring HOL Light's load
    order (lists.ml at hol_lib.ml 92 precedes cart.ml at 101).  `IN_ELIM_THM`
    comes from the Sets layer (SC); the pastecart laws come from `CFSum`. -/
initialize theCartVector : IO.Ref (Option HolMath.Cart.CartVector) ← IO.mkRef none

private unsafe def CVec : HolMath.Cart.CartVector :=
  match unsafeIO (do
    match ← theCartVector.get with
    | some d => pure d
    | none => do
      ensureIterate
      -- Force the `cart`/finite_sum theory and the lists-layer `EL` constant
      -- (`listDefs` declares `EL`) BEFORE the `vector` body parses.
      let _ ← IO.mkRef (concl CFin.FINITE_CART)
      let _ ← IO.mkRef (concl listDefs.EL)
      match ← (HolMath.Cart.setupCartVector new_definition MESON_TAC
                 CFSum IN_ELIM_THM).run with
      | .ok d => do theCartVector.set (some d); pure d
      | .error e => panic! s!"setupCartVector failed: {e}") with
  | .ok d => d | _ => panic! "Session.CVec: setupCartVector not run"

/-- Once-only guard for the THIRD and LAST parser side effect of cart.ml:
    `parse_as_infix("PCROSS",(22,"right"))` at cart.ml 571 - the "pasting"
    product infix at precedence 22, RIGHT-associative.  Like
    `ensureCartDollarInfix` / `ensureCartLambdaBinder` this is an `IO` ACTION
    with its own flag, NOT a memoised `Unit` CAF: a `let _ :=
    <caf>` would not force it, so `s PCROSS t` would parse as `s` APPLIED TO
    `PCROSS` AND `t` (the three-way juxtaposition sets.ml's `x IN s` had before
    its infix existed) rather than the infix.  `CPcross` awaits this, so the
    `PCROSS` `new_definition` body (cart.ml 573, the FIRST `PCROSS` term) and
    every `s PCROSS t` in the bundle parse it as the registered infix.  Its
    TRUE file position is cart.ml 571, just before the `PCROSS` definition -
    forced there by `ensureCart`. -/
initialize theCartPcrossInfix : IO.Ref Bool ← IO.mkRef false

private def ensureCartPcrossInfix : IO Unit := do
  unless (← theCartPcrossInfix.get) do
    HolMath.Cart.setupCartPcrossInfix
    theCartPcrossInfix.set true

/-- Cache for `CartPcross` (cart.ml 573-733): the `PCROSS` "pasting" product
    and its 166-line theory - the largest section of cart.ml and the one that
    COMPLETES the file.  The `PCROSS` infix (cart.ml 571, the THIRD and LAST
    parser side effect) is installed FIRST via `ensureCartPcrossInfix` so the
    `PCROSS` `new_definition` body parses the infix, not a juxtaposition; its
    TRUE file position (571) is forced by `ensureCart` just before this bundle.
    `new_definition` is threaded into the pure HolMath layer.  Depends on
    `CFSum` (pastecart theory), `CVec` (`IN_ELIM_PASTECART_THM`), and threaded
    Sets/HAS_SIZE theorems.  The two `(CONJ_PAIR o prove)` pairs (704/715) are
    split with the threaded `CONJ_PAIR`.  No new kernel side effects - runs in
    file order AFTER `CVec`. -/
initialize theCartPcross : IO.Ref (Option HolMath.Cart.CartPcross) ← IO.mkRef none

private unsafe def CPcross : HolMath.Cart.CartPcross :=
  match unsafeIO (do
    match ← theCartPcross.get with
    | some d => pure d
    | none => do
      ensureIterate
      -- Force the cart/finite_sum/vector theory first, then install the PCROSS
      -- infix at its TRUE file position (cart.ml 571) BEFORE the bundle parses.
      let _ ← IO.mkRef (concl CVec.vector)
      ensureCartPcrossInfix
      match ← (HolMath.Cart.setupCartPcross new_definition MESON_TAC
                 SET_TAC CFSum CVec
                 FORALL_IN_GSPEC EXISTS_IN_GSPEC CONJ_ASSOC IN_ELIM_THM EXTENSION
                 IN_SING IN_UNIV IN_INTER IN_UNION IN_DIFF NOT_IN_EMPTY SUBSET
                 DISJOINT SUBSET_ANTISYM_EQ IMAGE_CLAUSES CONJ_SYM UNIONS_GSPEC
                 INTERS_GSPEC IN_ELIM_PAIR_THM FINITE_EMPTY FINITE_SUBSET
                 FINITE_IMAGE IN_IMAGE HAS_SIZE HAS_SIZE_PRODUCT
                 BIJECTIONS_HAS_SIZE_EQ EQ_IMP).run with
      | .ok d => do theCartPcross.set (some d); pure d
      | .error e => panic! s!"setupCartPcross failed: {e}") with
  | .ok d => d | _ => panic! "Session.CPcross: setupCartPcross not run"

/-- Force every cart.ml bundle, IN FILE ORDER, mirroring
    `ensureIterate`.  HOL Light runs cart.ml top to bottom after `needs
    "iterate.ml"`, so `ensureIterate` runs first, then the `dimindex` section,
    then `finite_image`, then the `cart` type with its `$` infix / `lambda`
    binder interleaved at their TRUE positions (cart.ml 115, 126).  DO NOT
    REORDER.  A `let _ := X` would NOT force a Lean CAF, so
    read a field via `IO.mkRef (concl ...)`; the parser guards are IO actions
    forced directly. -/
unsafe def ensureCart : IO Unit := do
  ensureIterate
  let _ ← IO.mkRef (concl CDim.dimindex)                  -- cart.ml 14-48
  let _ ← IO.mkRef (concl CFImg.finite_image_tybij)       -- cart.ml 54-105
  ensureCartDollarInfix                                   -- cart.ml 115
  ensureCartLambdaBinder                                  -- cart.ml 126
  let _ ← IO.mkRef (concl CCart.cart_tybij)               -- cart.ml 111-168
  let _ ← IO.mkRef (concl CFSum.finite_sum_tybij)         -- cart.ml 174-273
  let _ ← IO.mkRef (concl CFDiff.finite_diff_tybij)       -- cart.ml 279-305
  let _ ← IO.mkRef (concl CFProd.finite_prod_tybij)       -- cart.ml 312-335
  let _ ← IO.mkRef (concl CTybit.tybit0_INDUCT)           -- cart.ml 338-405
  let _ ← IO.mkRef (concl CDConv.DIMINDEX_2)              -- cart.ml 406-479
  let _ ← IO.mkRef (concl CFin.FINITE_CART)               -- cart.ml 480-548
  let _ ← IO.mkRef (concl CVec.vector)                    -- cart.ml 551-567
  ensureCartPcrossInfix                                   -- cart.ml 571
  let _ ← IO.mkRef (concl CPcross.PCROSS)                 -- cart.ml 573-733
  pure ()

/- ---------------------------------------------------------------------- -/
/- cart.ml bare theorem re-exports (ranges 14-48).                        -/
/- ---------------------------------------------------------------------- -/
-- CartDimindex (cart.ml 14-48)
unsafe def dimindex                : thm := CDim.dimindex
unsafe def DIMINDEX_NONZERO        : thm := CDim.DIMINDEX_NONZERO
unsafe def DIMINDEX_GE_1           : thm := CDim.DIMINDEX_GE_1
unsafe def DIMINDEX_UNIV           : thm := CDim.DIMINDEX_UNIV
unsafe def DIMINDEX_UNIQUE         : thm := CDim.DIMINDEX_UNIQUE
unsafe def UNIV_HAS_SIZE_DIMINDEX  : thm := CDim.UNIV_HAS_SIZE_DIMINDEX
unsafe def HAS_SIZE_1              : thm := CDim.HAS_SIZE_1
unsafe def NUMSEG_LT_DIMINDEX      : thm := CDim.NUMSEG_LT_DIMINDEX
unsafe def DIMINDEX_1              : thm := CDim.DIMINDEX_1

-- CartFiniteImage (cart.ml 54-105)
unsafe def finite_image_tybij      : thm := CFImg.finite_image_tybij
unsafe def FINITE_IMAGE_IMAGE      : thm := CFImg.FINITE_IMAGE_IMAGE
unsafe def HAS_SIZE_FINITE_IMAGE   : thm := CFImg.HAS_SIZE_FINITE_IMAGE
unsafe def CARD_FINITE_IMAGE       : thm := CFImg.CARD_FINITE_IMAGE
unsafe def FINITE_FINITE_IMAGE     : thm := CFImg.FINITE_FINITE_IMAGE
unsafe def DIMINDEX_FINITE_IMAGE   : thm := CFImg.DIMINDEX_FINITE_IMAGE
unsafe def FINITE_INDEX_WORKS      : thm := CFImg.FINITE_INDEX_WORKS
unsafe def FINITE_INDEX_INJ        : thm := CFImg.FINITE_INDEX_INJ
unsafe def FORALL_FINITE_INDEX     : thm := CFImg.FORALL_FINITE_INDEX

-- CartCart (cart.ml 111-168)
unsafe def cart_tybij              : thm := CCart.cart_tybij
unsafe def finite_index            : thm := CCart.finite_index
unsafe def CART_EQ                 : thm := CCart.CART_EQ
unsafe def lambda                  : thm := CCart.lambda
unsafe def LAMBDA_BETA             : thm := CCart.LAMBDA_BETA
unsafe def LAMBDA_UNIQUE           : thm := CCart.LAMBDA_UNIQUE
unsafe def LAMBDA_ETA              : thm := CCart.LAMBDA_ETA
unsafe def FINITE_INDEX_INRANGE    : thm := CCart.FINITE_INDEX_INRANGE
unsafe def FINITE_INDEX_INRANGE_2  : thm := CCart.FINITE_INDEX_INRANGE_2
unsafe def CART_EQ_FULL            : thm := CCart.CART_EQ_FULL

-- CartFiniteSum (cart.ml 174-273)
unsafe def finite_sum_tybij            : thm := CFSum.finite_sum_tybij
unsafe def pastecart                   : thm := CFSum.pastecart
unsafe def fstcart                     : thm := CFSum.fstcart
unsafe def sndcart                     : thm := CFSum.sndcart
unsafe def FINITE_SUM_IMAGE            : thm := CFSum.FINITE_SUM_IMAGE
unsafe def DIMINDEX_HAS_SIZE_FINITE_SUM : thm := CFSum.DIMINDEX_HAS_SIZE_FINITE_SUM
unsafe def DIMINDEX_FINITE_SUM         : thm := CFSum.DIMINDEX_FINITE_SUM
unsafe def FSTCART_PASTECART           : thm := CFSum.FSTCART_PASTECART
unsafe def SNDCART_PASTECART           : thm := CFSum.SNDCART_PASTECART
unsafe def PASTECART_FST_SND           : thm := CFSum.PASTECART_FST_SND
unsafe def PASTECART_EQ                : thm := CFSum.PASTECART_EQ
unsafe def FORALL_PASTECART            : thm := CFSum.FORALL_PASTECART
unsafe def EXISTS_PASTECART            : thm := CFSum.EXISTS_PASTECART
unsafe def PASTECART_INJ               : thm := CFSum.PASTECART_INJ
unsafe def FSTCART_COMPONENT           : thm := CFSum.FSTCART_COMPONENT
unsafe def SNDCART_COMPONENT           : thm := CFSum.SNDCART_COMPONENT
unsafe def PASTECART_COMPONENT         : thm := CFSum.PASTECART_COMPONENT

-- CartFiniteDiff (cart.ml 279-305)
unsafe def finite_diff_tybij           : thm := CFDiff.finite_diff_tybij
unsafe def FINITE_DIFF_IMAGE           : thm := CFDiff.FINITE_DIFF_IMAGE
unsafe def DIMINDEX_HAS_SIZE_FINITE_DIFF : thm := CFDiff.DIMINDEX_HAS_SIZE_FINITE_DIFF
unsafe def DIMINDEX_FINITE_DIFF        : thm := CFDiff.DIMINDEX_FINITE_DIFF

-- CartFiniteProd (cart.ml 312-335)
unsafe def finite_prod_tybij           : thm := CFProd.finite_prod_tybij
unsafe def FINITE_PROD_IMAGE           : thm := CFProd.FINITE_PROD_IMAGE
unsafe def DIMINDEX_HAS_SIZE_FINITE_PROD : thm := CFProd.DIMINDEX_HAS_SIZE_FINITE_PROD
unsafe def DIMINDEX_FINITE_PROD        : thm := CFProd.DIMINDEX_FINITE_PROD

-- CartTybit (cart.ml 338-405)
unsafe def tybit0_INDUCT               : thm := CTybit.tybit0_INDUCT
unsafe def tybit0_RECURSION            : thm := CTybit.tybit0_RECURSION
unsafe def tybit1_INDUCT               : thm := CTybit.tybit1_INDUCT
unsafe def tybit1_RECURSION            : thm := CTybit.tybit1_RECURSION
unsafe def HAS_SIZE_TYBIT0             : thm := CTybit.HAS_SIZE_TYBIT0
unsafe def HAS_SIZE_TYBIT1             : thm := CTybit.HAS_SIZE_TYBIT1
unsafe def DIMINDEX_TYBIT0             : thm := CTybit.DIMINDEX_TYBIT0
unsafe def DIMINDEX_TYBIT1             : thm := CTybit.DIMINDEX_TYBIT1
unsafe def DIMINDEX_CLAUSES            : thm := CTybit.DIMINDEX_CLAUSES
unsafe def FINITE_1                    : thm := CTybit.FINITE_1
unsafe def FINITE_TYBIT0               : thm := CTybit.FINITE_TYBIT0
unsafe def FINITE_TYBIT1               : thm := CTybit.FINITE_TYBIT1
unsafe def FINITE_CLAUSES              : thm := CTybit.FINITE_CLAUSES

-- CartDimindexConv (cart.ml 406-479)
unsafe def DIMINDEX_2                  : thm := CDConv.DIMINDEX_2
unsafe def DIMINDEX_3                  : thm := CDConv.DIMINDEX_3
unsafe def DIMINDEX_4                  : thm := CDConv.DIMINDEX_4
unsafe def HAS_SIZE_2                  : thm := CDConv.HAS_SIZE_2
unsafe def HAS_SIZE_3                  : thm := CDConv.HAS_SIZE_3
unsafe def HAS_SIZE_4                  : thm := CDConv.HAS_SIZE_4

-- CartFinite (cart.ml 480-548)
unsafe def FINITE_CART                 : thm := CFin.FINITE_CART
unsafe def HAS_SIZE_CART_UNIV          : thm := CFin.HAS_SIZE_CART_UNIV
unsafe def CARD_CART_UNIV              : thm := CFin.CARD_CART_UNIV
unsafe def FINITE_CART_UNIV            : thm := CFin.FINITE_CART_UNIV

-- CartVector (cart.ml 551-567)
unsafe def vector                      : thm := CVec.vector
unsafe def IN_ELIM_PASTECART_THM       : thm := CVec.IN_ELIM_PASTECART_THM

-- CartPcross (cart.ml 573-733)
unsafe def PCROSS                      : thm := CPcross.PCROSS
unsafe def FORALL_IN_PCROSS            : thm := CPcross.FORALL_IN_PCROSS
unsafe def EXISTS_IN_PCROSS            : thm := CPcross.EXISTS_IN_PCROSS
unsafe def PASTECART_IN_PCROSS         : thm := CPcross.PASTECART_IN_PCROSS
unsafe def PCROSS_EQ_EMPTY             : thm := CPcross.PCROSS_EQ_EMPTY
unsafe def PCROSS_EMPTY                : thm := CPcross.PCROSS_EMPTY
unsafe def PCROSS_SING                 : thm := CPcross.PCROSS_SING
unsafe def SUBSET_PCROSS               : thm := CPcross.SUBSET_PCROSS
unsafe def PCROSS_MONO                 : thm := CPcross.PCROSS_MONO
unsafe def PCROSS_EQ                   : thm := CPcross.PCROSS_EQ
unsafe def UNIV_PCROSS_UNIV            : thm := CPcross.UNIV_PCROSS_UNIV
unsafe def HAS_SIZE_PCROSS             : thm := CPcross.HAS_SIZE_PCROSS
unsafe def FINITE_PCROSS               : thm := CPcross.FINITE_PCROSS
unsafe def FINITE_PCROSS_EQ            : thm := CPcross.FINITE_PCROSS_EQ
unsafe def IMAGE_FSTCART_PCROSS        : thm := CPcross.IMAGE_FSTCART_PCROSS
unsafe def IMAGE_SNDCART_PCROSS        : thm := CPcross.IMAGE_SNDCART_PCROSS
unsafe def PCROSS_INTER                : thm := CPcross.PCROSS_INTER
unsafe def PCROSS_UNION                : thm := CPcross.PCROSS_UNION
unsafe def PCROSS_DIFF                 : thm := CPcross.PCROSS_DIFF
unsafe def INTER_PCROSS                : thm := CPcross.INTER_PCROSS
unsafe def PCROSS_UNIONS_UNIONS        : thm := CPcross.PCROSS_UNIONS_UNIONS
unsafe def PCROSS_UNIONS               : thm := CPcross.PCROSS_UNIONS
unsafe def PCROSS_INTERS_INTERS        : thm := CPcross.PCROSS_INTERS_INTERS
unsafe def PCROSS_INTERS               : thm := CPcross.PCROSS_INTERS
unsafe def DISJOINT_PCROSS             : thm := CPcross.DISJOINT_PCROSS

/- ====================================================================== -/
/- define.ml wiring.  Mirrors the cart.ml block above: one cache +         -/
/- accessor per bundle and an `ensureDefine` forcing them in FILE ORDER.   -/
/- `ensureCart` runs first because define.ml opens `needs "cart.ml"`       -/
/- (define.ml 7), exactly as `ensureCart` begins with `ensureIterate`.     -/
/- ====================================================================== -/

/-- Cache for `DefineCasewise` (define.ml 10-47): the `CASEWISE` recursive
    definition and the three theorems giving the conditions for all clauses of
    a casewise definition to hold.  `CASEWISE_DEF` (13) is the file's ONLY
    `new_recursive_definition`, taken over `list_RECURSION`; both are threaded
    into the pure HolMath layer (the `new_specification` side effect behind
    `new_recursive_definition` lives in Session's state, so this bundle carries
    no `unsafe`).  Enters through `ensureCart` because cart.ml precedes
    define.ml in `hol_lib.ml` load order.  Threads the pair theorems
    (`FORALL_PAIR_THM`/`PAIR_EQ`), the list theorems (`MEM`/`ALL_MEM` from
    `listDefs`/`listThms1`), `list_INDUCT`, and the decision procedures. -/
initialize theDefineCasewise : IO.Ref (Option HolMath.Define.DefineCasewise) ← IO.mkRef none

private unsafe def DCase : HolMath.Define.DefineCasewise :=
  match unsafeIO (do
    match ← theDefineCasewise.get with
    | some d => pure d
    | none => do
      ensureCart
      match ← (HolMath.Define.setupDefineCasewise new_recursive_definition
                 MESON_TAC ASM_MESON_TAC
                 list_RECURSION list_INDUCT
                 listDefs.MEM listThms1.ALL_MEM FORALL_PAIR_THM PAIR_EQ).run with
      | .ok d => do theDefineCasewise.set (some d); pure d
      | .error e => panic! s!"setupDefineCasewise failed: {e}") with
  | .ok d => d | _ => panic! "Session.DCase: setupDefineCasewise not run"

/-- Cache for `DefineAdmissible` (define.ml 48-78): the three core definitions
    `admissible`, `tailadmissible`, `superadmissible` and the lemma
    `MATCH_SEQPATTERN`.  The definitions are `new_definition` calls; the lemma
    is a `prove` using `_MATCH`/`_SEQPATTERN` from `pairAux`.  Enters through
    `DCase` because it follows it in define.ml file order. -/
initialize theDefineAdmissible :
    IO.Ref (Option HolMath.Define.DefineAdmissible) ← IO.mkRef none

private unsafe def DAdm : HolMath.Define.DefineAdmissible :=
  match unsafeIO (do
    match ← theDefineAdmissible.get with
    | some d => pure d
    | none => do
      let _ ← IO.mkRef (concl DCase.CASEWISE_DEF)
      match ← (HolMath.Define.setupDefineAdmissible new_definition
                 MESON_TAC pairAux.MATCH pairAux.SEQPATTERN).run with
      | .ok d => do theDefineAdmissible.set (some d); pure d
      | .error e => panic! s!"setupDefineAdmissible failed: {e}") with
  | .ok d => d | _ => panic! "Session.DAdm: setupDefineAdmissible not run"

/-- Cache for `DefineAdmissibleThms` (define.ml 79-222): the fifteen
    admissibility combinators `ADMISSIBLE_CONST` (82) through
    `ADMISSIBLE_MATCH_SEQPATTERN` (211).  Each elaborates the `admissible`
    definition; `ADMISSIBLE_NSUM`/`ADMISSIBLE_SUM`/`ADMISSIBLE_MAP` reach into
    the Iterate (`NSUM_EQ_NUMSEG` at `:num`, `SUM_EQ_NUMSEG` at `:real`) and
    Lists (`MAP_EQ`/`ALL_MEM`) layers; the pattern combinators use `pairAux`
    fields with underscores dropped.  Enters through `DAdm` because it follows
    it in define.ml file order.  `TAUT`/`MESON` are threaded in rule form for
    the `MATCH_MP_TAC(TAUT ...)` / `MATCH_MP_TAC(MESON[] ...)` steps. -/
initialize theDefineAdmissibleThms :
    IO.Ref (Option HolMath.Define.DefineAdmissibleThms) ← IO.mkRef none

private unsafe def DAdmT : HolMath.Define.DefineAdmissibleThms :=
  match unsafeIO (do
    match ← theDefineAdmissibleThms.get with
    | some d => pure d
    | none => do
      let _ ← IO.mkRef (concl DAdm.admissible)
      match ← (HolMath.Define.setupDefineAdmissibleThms MESON
                 MESON_TAC ASM_MESON_TAC
                 DAdm.admissible DAdm.MATCH_SEQPATTERN
                 pairAux.MATCH pairAux.SEQPATTERN pairAux.UNGUARDED_PATTERN
                 pairAux.GUARDED_PATTERN pairAux.GEQ_DEF
                 C.FUN_EQ_THM FORALL_PAIR_THM T.AND_FORALL_THM T.MONO_FORALL
                 IN3.NSUM_EQ_NUMSEG IS3.SUM_EQ_NUMSEG
                 listThms1.MAP_EQ listThms1.ALL_MEM).run with
      | .ok d => do theDefineAdmissibleThms.set (some d); pure d
      | .error e => panic! s!"setupDefineAdmissibleThms failed: {e}") with
  | .ok d => d | _ => panic! "Session.DAdmT: setupDefineAdmissibleThms not run"

/-- Cache for `DefineSuperadmissibleThms` (define.ml 223-356): the seven
    superadmissible generalizations `ADMISSIBLE_IMP_SUPERADMISSIBLE` (233)
    through `SUPERADMISSIBLE_MATCH_GUARDED_PATTERN` (330).  Each generalizes an
    admissibility fact into the tail-recursive `superadmissible` form `define`
    chains: the base step is proved from the three core definitions, the rest
    build on it or on `SUPERADMISSIBLE_COND`.  `SUPERADMISSIBLE_CONST` uses
    `ADMISSIBLE_CONST` (from `DAdmT`); the pattern combinators use `pairAux`
    fields with underscores dropped.  Enters through `DAdmT` because it follows
    it in define.ml file order.  `TAUT` (for the `REWRITE_TAC[TAUT ...]` step)
    and `REWRITE_RULE` (for `RULE_ASSUM_TAC(REWRITE_RULE[admissible])`) are
    threaded in rule form; `MONO_AND`/`MONO_FORALL`/`IMP_IMP`/`AND_FORALL_THM`/
    `LEFT_IMP_EXISTS_THM`/`RIGHT_IMP_FORALL_THM` from the `Theorems` bundle. -/
initialize theDefineSuperadmissibleThms :
    IO.Ref (Option HolMath.Define.DefineSuperadmissibleThms) ← IO.mkRef none

private unsafe def DSupT : HolMath.Define.DefineSuperadmissibleThms :=
  match unsafeIO (do
    match ← theDefineSuperadmissibleThms.get with
    | some d => pure d
    | none => do
      let _ ← IO.mkRef (concl DAdm.superadmissible)
      match ← (HolMath.Define.setupDefineSuperadmissibleThms
                 ASM_MESON_TAC
                 DAdm.admissible DAdm.tailadmissible DAdm.superadmissible
                 DAdm.MATCH_SEQPATTERN
                 DAdmT.ADMISSIBLE_CONST
                 pairAux.MATCH pairAux.UNGUARDED_PATTERN
                 pairAux.GUARDED_PATTERN pairAux.GEQ_DEF
                 T.LEFT_IMP_EXISTS_THM T.RIGHT_IMP_FORALL_THM
                 T.IMP_IMP T.AND_FORALL_THM T.MONO_AND T.MONO_FORALL).run with
      | .ok d => do theDefineSuperadmissibleThms.set (some d); pure d
      | .error e => panic! s!"setupDefineSuperadmissibleThms failed: {e}") with
  | .ok d => d | _ => panic! "Session.DSupT: setupDefineSuperadmissibleThms not run"

/-- Cache for `DefineWfCasewise` (define.ml 357-463): the WF/tail-recursion-
    meets-casewise theorems `WF_REC_TAIL_GENERAL'` (360), `WF_REC_CASES` (372),
    `WF_REC_CASES'` (412), `RECURSION_CASEWISE` (419),
    `RECURSION_CASEWISE_PAIRWISE` (432), `SUPERADMISSIBLE_T` (456) and
    `RECURSION_SUPERADMISSIBLE` (460).  `RECURSION_CASEWISE` and
    `RECURSION_SUPERADMISSIBLE` are the two theorems define.ml 467-953
    instantiates mechanically, so they fix what `define` can accept.  The primed
    `WF_REC_TAIL_GENERAL'` (used by `WF_REC_CASES`) is distinct from the
    pre-existing unprimed `WF_REC_TAIL_GENERAL` (`Wf.WF_REC_TAIL_GENERAL`), which
    is used only inside `WF_REC_TAIL_GENERAL'`.  Enters through `DSupT` because
    it follows it in define.ml file order. -/
initialize theDefineWfCasewise :
    IO.Ref (Option HolMath.Define.DefineWfCasewise) ← IO.mkRef none

private unsafe def DWfC : HolMath.Define.DefineWfCasewise :=
  match unsafeIO (do
    match ← theDefineWfCasewise.get with
    | some d => pure d
    | none => do
      let _ ← IO.mkRef (concl DSupT.ADMISSIBLE_IMP_SUPERADMISSIBLE)
      match ← (HolMath.Define.setupDefineWfCasewise MESON_TAC ASM_MESON_TAC
                 (HolMath.Lists.LIST_INDUCT_TAC list_INDUCT')
                 Wf.WF_REC_TAIL_GENERAL
                 DCase.CASEWISE DCase.CASEWISE_WORKS
                 DAdm.tailadmissible DAdm.superadmissible DAdm.admissible
                 listDefs.ALL listDefs.MEM listDefs.PAIRWISE listThms1.ALL_MEM
                 FORALL_PAIR_THM list_INDUCT MONO_EXISTS FUN_EQ_THM
                 T.IMP_IMP T.CONJ_ASSOC T.LEFT_IMP_EXISTS_THM
                 T.RIGHT_IMP_FORALL_THM T.RIGHT_FORALL_IMP_THM T.IMP_CONJ).run with
      | .ok d => do theDefineWfCasewise.set (some d); pure d
      | .error e => panic! s!"setupDefineWfCasewise failed: {e}") with
  | .ok d => d | _ => panic! "Session.DWfC: setupDefineWfCasewise not run"

/-- Cache for `DefineSuite` (define.ml 467-953): the one binding that
    yields `instantiate_casewise_recursion`,
    `pure_prove_recursive_function_exists` and
    `prove_general_recursive_function_exists`, with its local helpers and
    lemmas built once.  Enters through `DWfC` because it follows the 357-463
    range in define.ml file order. -/
initialize theDefineSuite : IO.Ref (Option HolMath.Define.DefineSuite) ← IO.mkRef none

private unsafe def DSuite : HolMath.Define.DefineSuite :=
  match unsafeIO (do
    match ← theDefineSuite.get with
    | some d => pure d
    | none => do
      let _ ← IO.mkRef (concl DWfC.WF_REC_TAIL_GENERAL_prime)
      match ← (HolMath.Define.setupDefineSuite MESON_TAC MESON ARITH_RULE ARITH_TAC
                 GEN_BETA_CONV FORALL_UNWIND_CONV theBasicRectypeNet.get
                 prove_recursive_functions_exist get_inductive_type_store
                 mk_small_numeral DAdmT DSupT DWfC
                 EQ_ADD_RCANCEL EQ_ADD_LCANCEL EQ_ADD_RCANCEL_0 EQ_ADD_LCANCEL_0
                 EQ_MULT_RCANCEL EQ_MULT_LCANCEL EQ_REFL
                 ADD_EQ_0 MULT_EQ_0 MULT_EQ_1 ARITH_EQ
                 EVEN_MULT EVEN_ADD ARITH EVEN
                 pairAux.UNGUARDED_PATTERN pairAux.GUARDED_PATTERN
                 pairAux.GEQ_DEF SWAP_EXISTS_THM
                 C.FUN_EQ_THM FORALL_PAIR_THM EXISTS_PAIR_THM EQ_IMP
                 AND_CLAUSES OR_CLAUSES IMP_CLAUSES EQ_CLAUSES NOT_CLAUSES FORALL_SIMP
                 listDefs.ALL listDefs.PAIRWISE CONJ_ASSOC EXISTS_REFL LET_DEF LET_END_DEF
                 Wf.WF_LEX ETA_AX Wf.WF_MEASURE_GEN Wf.WF_MEASURE Wf.WF_FALSE
                 Wf.MEASURE Wf.MEASURE_LE MONO_EXISTS).run with
      | .ok d => do theDefineSuite.set (some d); pure d
      | .error e => panic! s!"setupDefineSuite failed: {e}") with
  | .ok d => d | _ => panic! "Session.DSuite: setupDefineSuite not run"

/-- `SIMPLIFY_WELLDEFINEDNESS_CONV` (define.ml 475-526).  Reads the live
    `basic_rectype_net` on every application. -/
unsafe def SIMPLIFY_WELLDEFINEDNESS_CONV : ioconv := fun tm =>
  DSuite.SIMPLIFY_WELLDEFINEDNESS_CONV tm
/-- `EXISTS_PAT_CONV` (define.ml 531-544). -/
unsafe def EXISTS_PAT_CONV : ioconv := fun tm => DSuite.EXISTS_PAT_CONV tm
/-- `HACK_PROFORMA` (define.ml 565-579). -/
unsafe def HACK_PROFORMA (n : Int) (th : thm) : IO (Except String thm) :=
  DSuite.HACK_PROFORMA n th
/-- `EACK_PROFORMA` (define.ml 580-595). -/
unsafe def EACK_PROFORMA (n : Int) (th : thm) : IO (Except String thm) :=
  DSuite.EACK_PROFORMA n th
/-- `APPLY_PROFORMA_TAC` (define.ml 602-605). -/
unsafe def APPLY_PROFORMA_TAC (th : thm) : tactic := fun g => DSuite.APPLY_PROFORMA_TAC th g
/-- `SIMPLIFY_MATCH_WELLDEFINED_TAC` (define.ml 612-622). -/
unsafe def SIMPLIFY_MATCH_WELLDEFINED_TAC : tactic := fun g =>
  DSuite.SIMPLIFY_MATCH_WELLDEFINED_TAC g
/-- `MAIN_ADMISS_TAC` (define.ml 630-683). -/
unsafe def MAIN_ADMISS_TAC : tactic := fun g => DSuite.MAIN_ADMISS_TAC g
/-- `ADMISS_TAC` (define.ml 685-689). -/
unsafe def ADMISS_TAC : tactic := fun g => DSuite.ADMISS_TAC g
/-- `instantiate_casewise_recursion` (define.ml 698-808). -/
unsafe def instantiate_casewise_recursion : ioconv := fun tm =>
  DSuite.instantiate_casewise_recursion tm
/-- `pure_prove_recursive_function_exists` (define.ml 814-851). -/
unsafe def pure_prove_recursive_function_exists : ioconv := fun tm =>
  DSuite.pure_prove_recursive_function_exists tm
/-- `prove_general_recursive_function_exists` (define.ml 857-947).  Reads
    the live `inductive_type_store`. -/
unsafe def prove_general_recursive_function_exists : ioconv := fun tm =>
  DSuite.prove_general_recursive_function_exists tm

-- DefineSuite probe theorems for the forcing guard.
unsafe def DSUITE_eq_refl  : thm := DSuite.eq_refl
unsafe def DSUITE_elemma0  : thm := DSuite.elemma0
unsafe def DSUITE_elemma1  : thm := DSuite.elemma1
unsafe def DHACK_smw_pth0 : thm := DSuite.smw_pth0
unsafe def DHACK_smw_pth1 : thm := DSuite.smw_pth1
unsafe def DHACK_epa_pth0 : thm := DSuite.epa_pth0
unsafe def DHACK_epa_pth1 : thm := DSuite.epa_pth1
unsafe def DGUESS_pth_lexleft  : thm := DSuite.pth_lexleft
unsafe def DGUESS_pth_lexright : thm := DSuite.pth_lexright
unsafe def DGUESS_pth_measure  : thm := DSuite.pth_measure

/-- Force every define.ml bundle, IN FILE ORDER, mirroring
    `ensureCart`.  HOL Light runs define.ml top to bottom after `needs
    "cart.ml"`, so `ensureCart` runs first, then the `CASEWISE` section.  DO NOT
    REORDER.  A `let _ := X` would NOT force a Lean CAF, so
    read a field via `IO.mkRef (concl ...)`. -/
unsafe def ensureDefine : IO Unit := do
  ensureCart
  let _ ← IO.mkRef (concl DCase.CASEWISE_DEF)             -- define.ml 10-47
  let _ ← IO.mkRef (concl DAdm.admissible)                -- define.ml 48-78
  let _ ← IO.mkRef (concl DAdmT.ADMISSIBLE_CONST)         -- define.ml 79-222
  let _ ← IO.mkRef (concl DSupT.ADMISSIBLE_IMP_SUPERADMISSIBLE) -- define.ml 223-356
  let _ ← IO.mkRef (concl DWfC.WF_REC_TAIL_GENERAL_prime) -- define.ml 357-463
  let _ ← IO.mkRef (concl DSuite.eq_refl)                 -- define.ml 464-953
  pure ()

/- ---------------------------------------------------------------------- -/
/- define.ml bare theorem re-exports (ranges 10-47, 48-78, 79-222, 223-356). -/
/- ---------------------------------------------------------------------- -/
-- DefineCasewise (define.ml 10-47)
unsafe def CASEWISE_DEF                : thm := DCase.CASEWISE_DEF
unsafe def CASEWISE                    : thm := DCase.CASEWISE
unsafe def CASEWISE_CASES              : thm := DCase.CASEWISE_CASES
unsafe def CASEWISE_WORKS              : thm := DCase.CASEWISE_WORKS

-- DefineAdmissible (define.ml 48-78)
unsafe def admissible_DEF              : thm := DAdm.admissible
unsafe def tailadmissible_DEF          : thm := DAdm.tailadmissible
unsafe def superadmissible_DEF         : thm := DAdm.superadmissible
unsafe def MATCH_SEQPATTERN            : thm := DAdm.MATCH_SEQPATTERN

-- DefineAdmissibleThms (define.ml 79-222)
unsafe def ADMISSIBLE_CONST            : thm := DAdmT.ADMISSIBLE_CONST
unsafe def ADMISSIBLE_BASE             : thm := DAdmT.ADMISSIBLE_BASE
unsafe def ADMISSIBLE_COMB             : thm := DAdmT.ADMISSIBLE_COMB
unsafe def ADMISSIBLE_RAND             : thm := DAdmT.ADMISSIBLE_RAND
unsafe def ADMISSIBLE_LAMBDA           : thm := DAdmT.ADMISSIBLE_LAMBDA
unsafe def ADMISSIBLE_NEST             : thm := DAdmT.ADMISSIBLE_NEST
unsafe def ADMISSIBLE_COND             : thm := DAdmT.ADMISSIBLE_COND
unsafe def ADMISSIBLE_MATCH            : thm := DAdmT.ADMISSIBLE_MATCH
unsafe def ADMISSIBLE_SEQPATTERN       : thm := DAdmT.ADMISSIBLE_SEQPATTERN
unsafe def ADMISSIBLE_UNGUARDED_PATTERN : thm := DAdmT.ADMISSIBLE_UNGUARDED_PATTERN
unsafe def ADMISSIBLE_GUARDED_PATTERN  : thm := DAdmT.ADMISSIBLE_GUARDED_PATTERN
unsafe def ADMISSIBLE_NSUM             : thm := DAdmT.ADMISSIBLE_NSUM
unsafe def ADMISSIBLE_SUM              : thm := DAdmT.ADMISSIBLE_SUM
unsafe def ADMISSIBLE_MAP              : thm := DAdmT.ADMISSIBLE_MAP
unsafe def ADMISSIBLE_MATCH_SEQPATTERN : thm := DAdmT.ADMISSIBLE_MATCH_SEQPATTERN

-- DefineSuperadmissibleThms (define.ml 223-356)
unsafe def ADMISSIBLE_IMP_SUPERADMISSIBLE : thm := DSupT.ADMISSIBLE_IMP_SUPERADMISSIBLE
unsafe def SUPERADMISSIBLE_CONST       : thm := DSupT.SUPERADMISSIBLE_CONST
unsafe def SUPERADMISSIBLE_TAIL        : thm := DSupT.SUPERADMISSIBLE_TAIL
unsafe def SUPERADMISSIBLE_COND        : thm := DSupT.SUPERADMISSIBLE_COND
unsafe def SUPERADMISSIBLE_MATCH_SEQPATTERN : thm := DSupT.SUPERADMISSIBLE_MATCH_SEQPATTERN
unsafe def SUPERADMISSIBLE_MATCH_UNGUARDED_PATTERN : thm := DSupT.SUPERADMISSIBLE_MATCH_UNGUARDED_PATTERN
unsafe def SUPERADMISSIBLE_MATCH_GUARDED_PATTERN : thm := DSupT.SUPERADMISSIBLE_MATCH_GUARDED_PATTERN

-- DefineWfCasewise (define.ml 357-463).  NOTE: `WF_REC_TAIL_GENERAL'` (primed)
-- is re-exported as `WF_REC_TAIL_GENERAL_prime`; the UNPRIMED, pre-existing
-- `WF_REC_TAIL_GENERAL` (from `Wf`, line 2575) is a SEPARATE accessor and is
-- left untouched, so the primed/unprimed distinction is unmistakable.
unsafe def WF_REC_TAIL_GENERAL_prime   : thm := DWfC.WF_REC_TAIL_GENERAL_prime
unsafe def WF_REC_CASES                : thm := DWfC.WF_REC_CASES
unsafe def WF_REC_CASES_prime          : thm := DWfC.WF_REC_CASES_prime
unsafe def RECURSION_CASEWISE          : thm := DWfC.RECURSION_CASEWISE
unsafe def RECURSION_CASEWISE_PAIRWISE : thm := DWfC.RECURSION_CASEWISE_PAIRWISE
unsafe def SUPERADMISSIBLE_T           : thm := DWfC.SUPERADMISSIBLE_T
unsafe def RECURSION_SUPERADMISSIBLE   : thm := DWfC.RECURSION_SUPERADMISSIBLE

/- ---------------------------------------------------------------------- -/
/- define.ml 954-1028: the simple `define` function.  THE USER-FACING     -/
/- ENTRY POINT, and the LAST thing `hol_lib.ml` loads - with this, the     -/
/- HOL Light core library is complete.                                    -/
/- ---------------------------------------------------------------------- -/

/-- `define tm` (define.ml 957-1028): accept a general recursive definition,
    written as a conjunction of clauses that may use pattern matching, discharge
    the proof obligations automatically, and introduce the constant.  Calls
    `prove_general_recursive_function_exists` (define.ml 1024), then
    `new_specification` and `mk_mconst`.

    State: the OCaml's final act is `the_definitions := th3::(!the_definitions)`
    (1028).  The pure HolMath function returns the entry to prepend (`some th3`
    when it defines, `none` on a benign redefinition); this accessor performs
    the ref write.  `ensureDefine` runs first so every define.ml bundle is
    forced in file order. -/
unsafe def define (tm : term) : IO (Except String thm) := do
  ensureDefine
  let defs ← getTheDefinitions
  match ← HolMath.Define.define prove_general_recursive_function_exists
            new_specification Basics.mk_mconst defs tm with
  | .error e => return .error e
  | .ok (th, entry) => do
      -- `the_definitions := th3::(!the_definitions)` (define.ml 1028) reads the
      -- ref AFTER the definition is made: proving the recursion can itself add
      -- definitions, which must not be lost.
      match entry with
      | some th3 => theDefinitions.set (some (th3 :: (← getTheDefinitions)))
      | none => pure ()
      return .ok th

/- ---------------------------------------------------------------------- -/
/- check_axioms (hol_lib.ml 105-114): the library's FINAL integrity check. -/
/- ---------------------------------------------------------------------- -/
/-
  hol_lib.ml ends by defining this (it does not call it).  HOL Light rests on
  exactly three axioms (`INFINITY_AX`, `SELECT_AX`, `ETA_AX`); anything else in
  `the_axioms` means an axiom leaked in, most likely via `mk_thm`, which is
  `new_axiom` underneath (drule.ml 24-26).  `HolTest/AxiomsTest.lean` runs it
  over the fully bootstrapped session.

  `mem` is OCaml structural equality on `thm`, which is `equals_thm` here
  (comparing `dest_thm`, i.e. hypotheses and conclusion).
-/
unsafe def check_axioms : IO (Except String Unit) := do
  let basic_axioms := [INFINITY_AX, SELECT_AX, ETA_AX]
  let l := (← HolCore.Kernel.axioms).filter
             (fun th => !(basic_axioms.any (equals_thm th)))
  if l.isEmpty then return .ok ()
  else
    let strs ← l.mapM HolCore.Printer.string_of_thm
    return .error s!"check_axioms: [{String.intercalate ", " strs}]"


/-- `prioritize_num` (nums.ml): make `:num` the default for overloaded symbols. -/
unsafe def prioritize_num : IO Unit := do
  match ← (mk_type "num" []) with
  | .ok ty => prioritize_overload ty
  | .error e => panic! s!"prioritize_num: {e}"

/-- `prioritize_int` (int.ml): make `:int` the default for overloaded symbols.
    Forces the `int` theory first, since the type must exist. -/
unsafe def prioritize_int : IO Unit := do
  let _ ← IO.mkRef (concl INT_ADD_SYM)
  match ← (mk_type "int" []) with
  | .ok ty => prioritize_overload ty
  | .error e => panic! s!"prioritize_int: {e}"

end Session
