/- File: HolCore/OcamlOrder.lean
OCaml's evaluation order for the actions nested in a `do` statement.

OCaml evaluates the arguments of a function application, the elements of a
list or tuple and the operands of an infix operator right to left (the right
operand of `THEN` first).  So in `prove(`g`, A THEN B (MESON[..] `t`))` the
MESON call runs, and parses `t`, before A's quotations are parsed, and the
goal is parsed last.  Lean lifts the `(← e)` of a `do` statement left to
right.  Where HolLight.Syntax is open, this macro turns each statement's
nested actions into `let` binds in OCaml's order: a syntax node's children
right to left, an action after the actions nested inside it.  Nested actions
under `fun`, `if`, `match` and inner `do` blocks, and in the body of a `let`
term, are left to Lean (inner `do` blocks are rewritten in their own right;
a `let` term's value is lifted like any other child).  Statement sequences
nested in a statement (branches of `if`, `match` and `for`, and the rest of
the block after `let p := e | alt`, which Lean's parser puts inside that
statement) are rewritten in place.  Statements other
than `e`, `let`, `let ←`, reassignments and `return` are left as they are.

This matters for the type-variable counter, `genvar` and everything else
with an effect: HOL Light results depend on the order (holtranslation.md
9cz). -/

namespace HolLight.OcamlOrder


/-- Kinds whose nested actions are left to Lean's own lifting. -/
def skipKinds : List Lean.SyntaxNodeKind :=
  [`Lean.Parser.Term.do, `Lean.Parser.Term.fun, `Lean.Parser.Term.basicFun,
   `termIfThenElse, `termDepIfThenElse, `Lean.Parser.Term.match,
   `Lean.Parser.Term.byTactic, `Lean.Parser.Term.let, `Lean.Parser.Term.letrec,
   `Lean.Parser.Term.doIf, `Lean.Parser.Term.doMatch, `Lean.Parser.Term.doNested,
   -- statement sequences nested in a statement (`let p := e | alt` puts the
   -- rest of the block there): their actions belong to their own statements
   `Lean.Parser.Term.doSeqIndent, `Lean.Parser.Term.doSeqBracketed]

def elemKinds : List Lean.SyntaxNodeKind :=
  [`Lean.Parser.Term.doExpr, `Lean.Parser.Term.doLetArrow, `Lean.Parser.Term.doLet,
   `Lean.Parser.Term.doReassign, `Lean.Parser.Term.doReassignArrow,
   `Lean.Parser.Term.doReturn]

mutual
/-- Replace the nested actions of `stx` by fresh identifiers, pushing
    `let h ← e` for each in OCaml's order. -/
partial def ocamlLift (stx : Lean.Syntax) : StateT (Array Lean.Syntax) Lean.MacroM Lean.Syntax := do
  match stx with
  | .node info kind args =>
    if kind == `Lean.Parser.Term.nestedAction && args.size == 2 then
      let inner := args[1]!
      let h : Lean.Ident ← Lean.withFreshMacroScope (do
        return Lean.mkIdent (← Lean.MonadQuotation.addMacroScope `__ocl))
      if inner.isOfKind `Lean.Parser.Term.doExpr then
        let e ← ocamlLift inner[0]
        let el ← `(doElem| let $h:ident ← $(⟨e⟩):term)
        modify (·.push el.raw)
        return h.raw
      else if inner.isOfKind `Lean.Parser.Term.doNested then
        -- `(← do seq)`: the block is one action; its own statements are
        -- put in OCaml order too.
        let seq ← liftM (m := Lean.MacroM) (transformSeq inner[1])
        let el ← `(doElem| let $h:ident ← do $(⟨seq⟩):doSeq)
        modify (·.push el.raw)
        return h.raw
      else return stx
    else if kind == `Lean.Parser.Term.doNested && args.size == 2 then
      -- `let x ← do seq`: the block's statements are put in OCaml order
      return .node info kind (args.set! 1 (← liftM (m := Lean.MacroM) (transformSeq args[1]!)))
    else if kind == `Lean.Parser.Term.let then
      -- `(let x := v; body)`: OCaml's `let x = v in body` evaluates `v`
      -- first; `v`'s actions are lifted here, `body`'s are left to Lean.
      match args.findIdx? (·.isOfKind `Lean.Parser.Term.letDecl) with
      | some i => return .node info kind (args.set! i (← ocamlLift args[i]!))
      | none => return stx
    else if skipKinds.contains kind then return stx
    else
      let mut newArgs := args
      let mut i := args.size
      while i > 0 do
        i := i - 1
        newArgs := newArgs.set! i (← ocamlLift args[i]!)
      return .node info kind newArgs
  | _ => return stx

/-- A `doSeq` with each statement's nested actions made `let` binds in
    OCaml's order (unchanged if there are none, or it is not indented).
    Statement sequences nested in a statement (the branches of `if`,
    `match` and `for`, and the rest of the block after `let p := e | alt`)
    are transformed in place. -/
partial def transformSeq (s : Lean.Syntax) : Lean.MacroM Lean.Syntax := do
  unless s.isOfKind `Lean.Parser.Term.doSeqIndent do return s
  let items := s[0].getArgs
  let mut out : Array Lean.Syntax := #[]
  for item in items do
    let el := item[0]
    if elemKinds.contains el.getKind || el.isOfKind `Lean.Parser.Term.doLetElse then
      let (el', lifts) ← (ocamlLift el).run #[]
      for l in lifts do
        out := out.push (Lean.Syntax.node .none `Lean.Parser.Term.doSeqItem #[l, Lean.mkNullNode])
      out := out.push (item.setArg 0 (← transformNested el'))
    else out := out.push (item.setArg 0 (← transformNested el))
  return Lean.Syntax.node .none `Lean.Parser.Term.doSeqIndent #[Lean.mkNullNode out]

/-- `stx` with the statement sequences nested in it transformed (not those
    of inner `do` terms, which the macro reaches by itself). -/
partial def transformNested (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax := do
  match stx with
  | .node info kind args =>
    if kind == `Lean.Parser.Term.doSeqIndent then transformSeq stx
    else if kind == `Lean.Parser.Term.do then return stx
    else return .node info kind (← args.mapM transformNested)
  | _ => return stx
end

mutual
/-- Does a statement have nested actions this macro would move? -/
partial def hasLift (stx : Lean.Syntax) : Bool :=
  match stx with
  | .node _ kind args =>
    if kind == `Lean.Parser.Term.nestedAction then
      -- only the actions `ocamlLift` moves (`(← e)`, `(← do ..)`), else the
      -- macro would not change the block and would expand forever
      args.size == 2 && (args[1]!.isOfKind `Lean.Parser.Term.doExpr ||
                         args[1]!.isOfKind `Lean.Parser.Term.doNested)
    else if kind == `Lean.Parser.Term.doNested && args.size == 2 then
      args[1]![0].getArgs.any (fun item => needsWork item[0])
    else if kind == `Lean.Parser.Term.let then
      args.any (fun a => a.isOfKind `Lean.Parser.Term.letDecl && hasLift a)
    else if skipKinds.contains kind then false
    else args.any hasLift
  | _ => false

/-- Does a statement, or a statement sequence nested in it, have nested
    actions this macro would move? -/
partial def needsWork (el : Lean.Syntax) : Bool :=
  ((elemKinds.contains el.getKind || el.isOfKind `Lean.Parser.Term.doLetElse) && hasLift el)
    || nestedNeeds el

/-- Does a statement sequence nested in `stx` (not in an inner `do` term)
    need work? -/
partial def nestedNeeds (stx : Lean.Syntax) : Bool :=
  match stx with
  | .node _ kind args =>
    if kind == `Lean.Parser.Term.doSeqIndent then
      stx[0].getArgs.any (fun item => needsWork item[0])
    else if kind == `Lean.Parser.Term.do then false
    else args.any nestedNeeds
  | _ => false
end

end HolLight.OcamlOrder

namespace HolLight.Syntax

open HolLight.OcamlOrder in
scoped macro_rules
  | `(do $s:doSeq) => do
    let s := s.raw
    unless s.isOfKind `Lean.Parser.Term.doSeqIndent do Lean.Macro.throwUnsupported
    unless s[0].getArgs.any (fun item => needsWork item[0]) do
      Lean.Macro.throwUnsupported
    let seq ← transformSeq s
    `(do $(⟨seq⟩):doSeq)

end HolLight.Syntax
