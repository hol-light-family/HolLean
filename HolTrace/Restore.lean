/- File: HolTrace/Restore.lean
Replaying a HOLTrace file through the HOL Light kernel.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

This is the proof RECONSTRUCTOR.  It reads a trace in the format specified by
https://holtrace.cr.yp.to/format.html and rebuilds every type, term and theorem
it names - the theorems by applying HOL Light's primitive inference rules, one
per inference line.  Nothing in a trace is taken on trust: the file is a
RECIPE, and a trace is accepted only if the kernel both accepts every step and
produces exactly the theorems the file claims.

WHY REPLAYING IS A CHECK.  `HolCore.Kernel.thm` has a `private` constructor, so
no code outside `HolCore/Fusion.lean` can fabricate one; the only `thm` values
this module can obtain are those the ten primitive rules, `new_axiom`,
`new_basic_definition` and `new_basic_type_definition` hand back.  The
restorer's own correctness is therefore not what makes its answer meaningful -
a bug here can reject a good trace, or report the wrong theorem, but it cannot
make the kernel accept an unsound inference.  That is the whole point of
replaying a trace rather than parsing one.

WHAT IS CHECKED.  For each `t` line, `dest_thm` of the theorem the kernel just
derived must equal the hypotheses and conclusion the line states - as terms,
and in the same order, so the kernel's own `term_union` ordering of hypotheses
is checked too.  Each theorem must be preceded by an inference, and is proven
by the LAST inference before it (the format allows further inferences that
prove the same theorem differently, and allows non-inference lines in between).
`/` lines must give distinct names.  Type and term lines must satisfy the
kernel's arity, declaration and typing rules, plus the one check the kernel
does not make: that the type an `e` or `f` line DECLARES for its term is the
type that term actually has.

THE STARTING POINT.  Replay begins from a bare kernel - `bool`, `fun`, `=`,
plus the `ind` and `@` that `declarePrimitives` supplies - and every constant,
type and axiom the trace uses is created by the trace itself.  So a trace of
HOL Light's standard library is checked from nothing, independently of anything
this session has loaded.  This is upstream's `holtrace_restore_allownew`
behaviour; it is also why this module imports no `Session`. -/

import HolCore.Fusion
import HolCore.Basics
import HolCore.Printer
import HolTrace.Parse

open HolCore.Kernel HolCore.Basics

namespace HolTrace

/- ---------------------------------------------------------------------- -/
/- Configuration.                                                         -/
/- ---------------------------------------------------------------------- -/

/-- What to check while replaying. -/
structure Config where
  /-- Check each `t` line against the inference that precedes it.  Switching
      this off still runs every inference through the kernel - so the proofs
      are still checked - but stops comparing the results with the statements
      the file records.  Upstream's `holtrace_restore_skipthmchecks`. -/
  checkThms : Bool := true
  /-- Require theorem names to look like HOL Light identifiers.  Upstream's
      restorer refuses anything else, on the grounds that a name is going to be
      bound in a session. -/
  strictNames : Bool := true
  deriving Inhabited

/- ---------------------------------------------------------------------- -/
/- State.                                                                 -/
/- ---------------------------------------------------------------------- -/

/-- The restorer's state: the objects defined so far, indexed by the ID the
    format assigns them.

    Each of the four kinds of object is numbered independently from 0 upwards
    in order of definition, so "the ID" of an object is just its position here
    and the counter the format encodes references against is the array's size.
    Arrays, not lists: a trace of hol.ml defines millions of terms, and every
    reference is a random access. -/
structure State where
  /-- Types, by type ID (`a` and `b` lines). -/
  types : Array hol_type := #[]
  /-- Terms, by term ID (`c`, `d`, `e` and `f` lines). -/
  terms : Array term := #[]
  /-- Theorems, by theorem ID (`t` lines). -/
  thms : Array thm := #[]
  /-- The SECOND theorem of each `new_basic_type_definition`, by typedef ID:
      the one a later `D` line claims.  Its `A` line yields the first. -/
  typedefs : Array thm := #[]
  /-- The theorem derived by the most recent inference line, which is the one
      that proves the next `t` line. -/
  lastInf : Option thm := none
  /-- Named theorems, in order of naming (`/` lines). -/
  names : Array (String × thm) := #[]
  /-- How many inference lines have been seen.  `,` lines reference these, and
      the count is reported; the inferences themselves need not be kept. -/
  infs : Nat := 0
  /-- The ProofTrace ID counter, advanced by `,` and `;` lines. -/
  ptid : Nat := 0
  /-- Lines read, including the `HOLTrace 1` header. -/
  lines : Nat := 0
  /-- Bytes read, including each line's LF. -/
  bytes : Nat := 0
  deriving Inhabited

/-- The theorem named `name`, if the trace named one. -/
def State.find? (st : State) (name : String) : Option thm :=
  (st.names.find? (fun (n, _) => n == name)).map Prod.snd

/- ---------------------------------------------------------------------- -/
/- The restoring monad.                                                   -/
/- ---------------------------------------------------------------------- -/

/-- Replaying needs `IO`, because the kernel's type and constant tables are
    `IO.Ref`s, and needs an error channel, because a trace can be malformed in
    a hundred ways and each should name the line it was on. -/
abbrev RestoreM := ExceptT String IO

/-- Lift a pure kernel or parser result. -/
@[inline] private def ofE (r : Except String α) : RestoreM α := ExceptT.mk (pure r)

/-- Lift a kernel operation that reads the type or constant tables. -/
@[inline] private def ofIO (r : IO (Except String α)) : RestoreM α := ExceptT.mk r

/-- Read an object by ID.  `Cursor.subid` has already rejected any ID that is
    not a back reference, so this is a total restatement of that bound rather
    than a check that can fire. -/
@[inline] private def nth (a : Array α) (i : Nat) (what : String) : RestoreM α :=
  match a[i]? with
  | some x => pure x
  | none   => throw s!"{what} ID {i} is not defined yet"

/-- Record the theorem an inference line derived. -/
@[inline] private def State.infer (st : State) (th : thm) : State :=
  { st with lastInf := some th, infs := st.infs + 1 }

/-- Show a theorem for a diagnostic.  The printer works from HOL Light's
    initial fixity tables, since replay loads no library, so a conclusion using
    `/\` prints in prefix form; that is still far more use than no term at all.
    Printing must never be what fails a verification, so any error in the
    printer itself degrades to the raw constructor form. -/
private def showThm (th : thm) : IO String := do
  try HolCore.Printer.string_of_thm th
  catch _ => return s!"{repr (dest_thm th)}"

/-- Show the sequent a `t` line STATES, for the same diagnostic.

    This cannot go through `showThm`: the line's hypotheses and conclusion are
    only terms - whether they are a theorem is the very question - and they need
    not even be of type `bool`, so there is no `thm` to print and nothing that
    builds one may be used here. -/
private def showSeq (hyps : List term) (concl : term) : IO String := do
  try
    let hs ← hyps.mapM HolCore.Printer.string_of_term
    let c ← HolCore.Printer.string_of_term concl
    if hs.isEmpty then return "|- " ++ c
    return (String.intercalate ", " hs) ++ " |- " ++ c
  catch _ => return s!"{repr (hyps, concl)}"

/- ---------------------------------------------------------------------- -/
/- Primitive objects that no trace declares.                              -/
/- ---------------------------------------------------------------------- -/

/-- The type of HOL Light's choice operator, `:(A->bool)->A`. -/
private def selectTy : hol_type :=
  .Tyapp "fun" [.Tyapp "fun" [aty, bool_ty], aty]

/-- Declare the two primitive objects a trace never mentions.

    The format has a tag for every logical step, so everything a trace uses is
    either created by the trace or built into the kernel.  `bool`, `fun` and
    `=` are built into `HolCore/Fusion.lean`; the other two are not, because
    HOL Light introduces them part-way through its own library - nums.ml
    declares the type of individuals with `new_type("ind",0)` and class.ml the
    choice operator with ``new_constant("@",`:(A->bool)->A`)``.  Neither is an
    inference, so neither appears in a trace, and both must be here instead.

    This adds no axiom: `INFINITY_AX` and `SELECT_AX` are in the trace, as `X`
    lines, and are asserted by `new_axiom` when replay reaches them.  Already
    declared is not an error, so a caller may run several traces in one
    process. -/
def declarePrimitives : RestoreM Unit := ofIO do
  if (← get_type_arity "ind").toOption.isNone then
    match ← new_type "ind" 0 with
    | .error e => return .error e
    | .ok ()   => pure ()
  if (← get_const_type "@").toOption.isNone then
    match ← new_constant "@" selectTy with
    | .error e => return .error e
    | .ok ()   => pure ()
  return .ok ()

/- ---------------------------------------------------------------------- -/
/- Types.                                                                 -/
/- ---------------------------------------------------------------------- -/

/-- `a text`: the type variable named `text`. -/
def doTyvar (st : State) (c : Cursor) : RestoreM State := do
  let name ← ofE c.text
  return { st with types := st.types.push (mk_vartype name) }

/-- `b n a ... z text`: the type `text` applied to the `n` listed types.

    `mk_type` is what rejects an undeclared type constructor or the wrong
    number of arguments, so the count is not trusted here: a count larger than
    the arguments that follow runs out of line and is reported as a missing
    argument. -/
def doTyapp (st : State) (c0 : Cursor) : RestoreM State := do
  let (n, c1) ← ofE (c0.subid (-1))
  let mut c := c1
  let mut args : Array hol_type := #[]
  for _ in [0:n] do
    let (i, c') ← ofE (c.subid (st.types.size : Int))
    args := args.push (← nth st.types i "type")
    c := c'
  let name ← ofE c.text
  let ty ← ofIO (mk_type name args.toList)
  return { st with types := st.types.push ty }

/- ---------------------------------------------------------------------- -/
/- Terms.                                                                 -/
/- ---------------------------------------------------------------------- -/

/-- `c type text`: the constant `text` at type `type`.

    `mk_mconst` requires the constant to be declared and its stated type to be
    an instance of the declared generic type - so a trace cannot invent a
    constant, nor use one at a type its definition does not support. -/
def doConst (st : State) (c0 : Cursor) : RestoreM State := do
  let (i, c) ← ofE (c0.subid (st.types.size : Int))
  let ty ← nth st.types i "type"
  let name ← ofE c.text
  let tm ← ofIO (mk_mconst name ty)
  return { st with terms := st.terms.push tm }

/-- `d type text`: the variable `text` of type `type`. -/
def doVar (st : State) (c0 : Cursor) : RestoreM State := do
  let (i, c) ← ofE (c0.subid (st.types.size : Int))
  let ty ← nth st.types i "type"
  let name ← ofE c.text
  return { st with terms := st.terms.push (mk_var name ty) }

/-- `e type fterm xterm`: the application `fterm xterm`, of type `type`.

    The application itself is `mk_comb`, which checks that the argument has the
    type the function expects.  The result type the line declares is checked
    here: the kernel has no reason to look at it, but a reader must, because
    every later reference to this term is by ID and takes the stated type on
    trust. -/
def doComb (st : State) (c0 : Cursor) : RestoreM State := do
  let (tyi, c1) ← ofE (c0.subid (st.types.size : Int))
  let (fi, c2)  ← ofE (c1.subid (st.terms.size : Int))
  let (xi, c3)  ← ofE (c2.subid (st.terms.size : Int))
  ofE c3.expectEnd
  let ty ← nth st.types tyi "type"
  let f  ← nth st.terms fi "term"
  let x  ← nth st.terms xi "term"
  if type_of f != .Tyapp "fun" [type_of x, ty] then
    throw "e: the declared type is not the type of the application"
  let tm ← ofE (mk_comb f x)
  return { st with terms := st.terms.push tm }

/-- `f type vterm tterm`: the abstraction `vterm ↦ tterm`, of type `type`.

    `mk_abs` checks that `vterm` is a variable; the declared function type is
    checked here, for the same reason as on an `e` line. -/
def doAbs (st : State) (c0 : Cursor) : RestoreM State := do
  let (tyi, c1) ← ofE (c0.subid (st.types.size : Int))
  let (vi, c2)  ← ofE (c1.subid (st.terms.size : Int))
  let (bi, c3)  ← ofE (c2.subid (st.terms.size : Int))
  ofE c3.expectEnd
  let ty ← nth st.types tyi "type"
  let v  ← nth st.terms vi "term"
  let b  ← nth st.terms bi "term"
  if ty != .Tyapp "fun" [type_of v, type_of b] then
    throw "f: the declared type is not the type of the abstraction"
  let tm ← ofE (mk_abs v b)
  return { st with terms := st.terms.push tm }

/- ---------------------------------------------------------------------- -/
/- Inferences: the ten primitive rules.                                   -/
/- ---------------------------------------------------------------------- -/

/-- An inference taking one term: `R` (REFL), `B` (BETA), `U` (ASSUME) and
    `X` (new_axiom). -/
def infTerm (st : State) (c0 : Cursor) (rule : term → RestoreM thm) :
    RestoreM State := do
  let (i, c) ← ofE (c0.subid (st.terms.size : Int))
  ofE c.expectEnd
  return st.infer (← rule (← nth st.terms i "term"))

/-- An inference taking two theorems: `E` (MK_COMB), `P` (EQ_MP), `V` (TRANS)
    and `Z` (DEDUCT_ANTISYM_RULE). -/
def infThmThm (st : State) (c0 : Cursor) (rule : thm → thm → RestoreM thm) :
    RestoreM State := do
  let (i, c1) ← ofE (c0.subid (st.thms.size : Int))
  let (j, c2) ← ofE (c1.subid (st.thms.size : Int))
  ofE c2.expectEnd
  let th ← nth st.thms i "theorem"
  let tH ← nth st.thms j "theorem"
  return st.infer (← rule th tH)

/-- `F term th`: HOL Light's ABS.  The term is the variable to abstract over;
    the kernel rejects it if it is free in a hypothesis of `th`. -/
def infAbs (st : State) (c0 : Cursor) : RestoreM State := do
  let (i, c1) ← ofE (c0.subid (st.terms.size : Int))
  let (j, c2) ← ofE (c1.subid (st.thms.size : Int))
  ofE c2.expectEnd
  let v  ← nth st.terms i "term"
  let th ← nth st.thms j "theorem"
  return st.infer (← ofE (ABS v th))

/-- Read the substitution pairs that fill out an `S` or `T` line.

    The format writes each pair as `old new`, whereas HOL Light's `INST` and
    `INST_TYPE` take `[new, old]` - the pair is flipped here, once, so both
    callers agree. -/
private def substPairs (c0 : Cursor) (bound : Nat) (get : Nat → RestoreM α) :
    RestoreM (List (α × α)) := do
  let mut c := c0
  let mut acc : Array (α × α) := #[]
  while !c.atEnd do
    let (oi, c1) ← ofE (c.subid (bound : Int))
    let (ni, c2) ← ofE (c1.subid (bound : Int))
    acc := acc.push (← get ni, ← get oi)
    c := c2
  return acc.toList

/-- `S th oldterm newterm ...`: HOL Light's INST.  Zero pairs is allowed by
    the format (and does nothing). -/
def infInst (st : State) (c0 : Cursor) : RestoreM State := do
  let (i, c) ← ofE (c0.subid (st.thms.size : Int))
  let th ← nth st.thms i "theorem"
  let theta ← substPairs c st.terms.size (fun j => nth st.terms j "term")
  return st.infer (← ofE (INST theta th))

/-- `T th oldtype newtype ...`: HOL Light's INST_TYPE.

    Each `oldtype` must be a type VARIABLE.  The kernel does not insist on it -
    `type_subst` recurses into a `Tyapp` instead of looking it up, so an entry
    keyed by a composite type is silently ignored rather than wrong - and
    upstream's in-kernel `holtrace_restore` therefore accepts such a line.  It
    is refused here, as upstream's standalone verifiers refuse it: an ignored
    substitution means the file says something it does not mean, no trace a
    kernel wrote can contain one (HOL Light builds these lists with
    `type_match`, which only ever keys them by type variables), and a verifier
    should not accept a line whose stated meaning is not its effect. -/
def infInstType (st : State) (c0 : Cursor) : RestoreM State := do
  let (i, c) ← ofE (c0.subid (st.thms.size : Int))
  let th ← nth st.thms i "theorem"
  let theta ← substPairs c st.types.size (fun j => nth st.types j "type")
  if theta.any (fun (_, old) => !is_vartype old) then
    throw "T: a substitution replaces something that is not a type variable"
  return st.infer (← ofE (INST_TYPE theta th))

/- ---------------------------------------------------------------------- -/
/- Inferences: definitional extension.                                    -/
/- ---------------------------------------------------------------------- -/

/-- `C term text`: HOL Light's `new_basic_definition`.

    `term` is `v = t` with `v` a VARIABLE named `text`; the rule declares a
    constant of that name and returns `|- c = t`.  The name is in the line
    twice, so the two are checked against each other before the kernel is asked
    to create anything.  The kernel does the rest: `t` closed, and no type
    variable in `t` that is not in the type of `v`. -/
def infDef (st : State) (c0 : Cursor) : RestoreM State := do
  let (i, c) ← ofE (c0.subid (st.terms.size : Int))
  let name ← ofE c.text
  let tm ← nth st.terms i "term"
  let vname ← ofE do
    let (l, _) ← dest_eq tm
    let (n, _) ← dest_var l
    pure n
  if vname != name then
    throw s!"C: the equation defines '{vname}' but the line names '{name}'"
  return st.infer (← ofIO (new_basic_definition tm))

/-- `A reptype repterm th text`: HOL Light's `new_basic_type_definition`.

    `th` must be `|- repterm x` with `x : reptype`, witnessing that the
    predicate `repterm` is satisfied - HOL Light types are nonempty, so a type
    definition needs one.  `text` is `]abstypename]absname]repname]tyvar...]`.

    The line's `reptype` and `repterm` are redundant - both are determined by
    `th` - and are checked against it.  The type variables are redundant too:
    the kernel parameterises the new type by the type variables of the
    predicate, sorted.  Rather than recompute that list (and risk agreeing with
    a bug in the kernel rather than with the kernel), the check is made against
    the type the kernel actually built.

    Of the two theorems produced, `|- absname (repname a) = a` proves this
    line; the other is kept for a later `D` line to claim. -/
def infTypedef (st : State) (c0 : Cursor) : RestoreM State := do
  let (tyi, c1) ← ofE (c0.subid (st.types.size : Int))
  let (tmi, c2) ← ofE (c1.subid (st.terms.size : Int))
  let (thi, c3) ← ofE (c2.subid (st.thms.size : Int))
  let word ← ofE c3.text
  let reptype ← nth st.types tyi "type"
  let repterm ← nth st.terms tmi "term"
  let th ← nth st.thms thi "theorem"
  -- ]abstypename]absname]repname]tyvar0]tyvar1]...]
  let (tyname, absname, repname, tyvars) ←
    match word.splitOn "]" with
    | "" :: tyname :: absname :: repname :: rest =>
        match rest.reverse with
        | "" :: revTyvars => pure (tyname, absname, repname, revTyvars.reverse)
        | _ => throw "A: the name field must end with ']'"
    | _ => throw "A: the name field must be ]abstype]abs]rep]tyvars...]"
  -- The format requires all constant names to be distinct, counting absname
  -- and repname of every `A` line.  This one case has to be checked HERE: the
  -- kernel compares each of the two names against the constants that already
  -- exist, but not against each other, and `HolCore/Fusion.lean` discards the
  -- result of its two `new_constant` calls (`let _ <- ...`) where HOL Light's
  -- `new_constant` raises - so with absname = repname this kernel declares the
  -- name once and still mints a `Const` of that name at the OTHER type, which
  -- HOL Light refuses to do.
  if absname == repname then
    throw s!"A: absname and repname are both '{absname}'"
  if !(hyp th).isEmpty then
    throw "A: the witnessing theorem has hypotheses"
  let (p, x) ← ofE (dest_comb (concl th))
  if p != repterm then
    throw "A: repterm is not the predicate of the witnessing theorem"
  if type_of x != reptype then
    throw "A: reptype is not the type of the witness"
  let (th1, th2) ← ofIO (new_basic_type_definition tyname absname repname th)
  let built ← ofE do
    let (_, r) ← dest_eq (concl th1)
    pure (type_of r)
  if built != .Tyapp tyname (tyvars.map .Tyvar) then
    throw s!"A: the line's type variables are not the ones '{tyname}' was built with"
  return { st.infer th1 with typedefs := st.typedefs.push th2 }

/-- `D typedef`: the second theorem of an earlier `A` line,
    `|- repterm r = (repname (absname r) = r)`. -/
def infTypedefSnd (st : State) (c0 : Cursor) : RestoreM State := do
  let (i, c) ← ofE (c0.subid (st.typedefs.size : Int))
  ofE c.expectEnd
  return st.infer (← nth st.typedefs i "typedef")

/- ---------------------------------------------------------------------- -/
/- Theorems and names.                                                    -/
/- ---------------------------------------------------------------------- -/

/-- `t A ... Z conclusion`: the theorem the preceding inference proves.

    The last argument is the conclusion and the others are the hypotheses, in
    order.  The comparison is with `dest_thm`, so it is exact: same hypotheses,
    same order, same conclusion.  Hypothesis ORDER matters because the kernel
    keeps hypothesis lists sorted by `alphaorder` and merges them with
    `term_union`; a trace written by a kernel that ordered them differently
    would record a different list, and silently accepting that would mean the
    two kernels disagree about what `term_union` computes. -/
def doThm (cfg : Config) (st : State) (c0 : Cursor) : RestoreM State := do
  let some th := st.lastInf
    | throw "t: no inference precedes this theorem"
  let mut c := c0
  let mut args : Array term := #[]
  while !c.atEnd do
    let (i, c') ← ofE (c.subid (st.terms.size : Int))
    args := args.push (← nth st.terms i "term")
    c := c'
  let some concl := args.back?
    | throw "t: missing conclusion"
  if cfg.checkThms then
    let hyps := args.pop.toList
    if dest_thm th != (hyps, concl) then
      throw s!"t: the inference proves\n  {← showThm th}\n\
               but the line states\n  {← showSeq hyps concl}"
  return { st with thms := st.thms.push th }

/-- May this be a theorem name?  HOL Light identifiers: letters, digits and
    `_`, then also `'` and `.`.  Upstream's restorer refuses anything else
    rather than hand a name it could not bind to a session. -/
def nameAcceptable (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => first c && cs.all rest
  where
    first (c : Char) : Bool := c.isAlphanum || c == '_'
    rest (c : Char) : Bool := first c || c == '\'' || c == '.'

/-- `/ th text`: theorem `th` is named `text`.

    A theorem may have several names, but a name may not name two theorems, so
    a repeat is an error.  Names carry no logical content - a reader that only
    checks proofs may ignore `/` lines entirely - but they are how a caller
    asks for a particular theorem once the trace has been verified. -/
def doName (cfg : Config) (st : State) (c0 : Cursor) : RestoreM State := do
  let (i, c) ← ofE (c0.subid (st.thms.size : Int))
  let name ← ofE c.text
  if cfg.strictNames && !nameAcceptable name then
    throw s!"/: refusing unusual characters in theorem name '{name}'"
  if (st.find? name).isSome then
    throw s!"/: theorem name '{name}' is already used"
  let th ← nth st.thms i "theorem"
  return { st with names := st.names.push (name, th) }

/- ---------------------------------------------------------------------- -/
/- ProofTrace IDs.                                                        -/
/- ---------------------------------------------------------------------- -/

/-- `, newth inf ptth ptTH`: bookkeeping that lets a ProofTrace file be
    regenerated byte for byte, since ProofTrace numbers repeated proofs of the
    same theorem separately.

    It says nothing about the logic - the inference it names has already been
    checked where it appeared - so the arguments are only checked to be
    references to things that exist.  The last two are optional, being present
    only for the inputs the rule in question actually takes. -/
def doPtProof (st : State) (c0 : Cursor) : RestoreM State := do
  let (_, c1) ← ofE (c0.subid (st.thms.size : Int))
  let (_, c2) ← ofE (c1.subid (st.infs : Int))
  let c3 ← if c2.atEnd then pure c2 else Prod.snd <$> ofE (c2.subid (st.ptid : Int))
  let c4 ← if c3.atEnd then pure c3 else Prod.snd <$> ofE (c3.subid (st.ptid : Int))
  ofE c4.expectEnd
  return { st with ptid := st.ptid + 1 }

/-- `;`: advance the ProofTrace ID counter and nothing else.  ProofTrace IDs
    are mostly sequential but skip numbers on some occasions. -/
def doPtSkip (st : State) (c : Cursor) : RestoreM State := do
  ofE c.expectEnd
  return { st with ptid := st.ptid + 1 }

/- ---------------------------------------------------------------------- -/
/- The driver.                                                            -/
/- ---------------------------------------------------------------------- -/

/-- Replay one line, whose tag has already been consumed. -/
def step (cfg : Config) (st : State) (tag : Char) (c : Cursor) : RestoreM State :=
  match tag with
  -- types
  | 'a' => doTyvar st c
  | 'b' => doTyapp st c
  -- terms
  | 'c' => doConst st c
  | 'd' => doVar st c
  | 'e' => doComb st c
  | 'f' => doAbs st c
  -- theorems and names
  | 't' => doThm cfg st c
  | '/' => doName cfg st c
  -- the ten primitive inference rules
  | 'R' => infTerm st c (fun t => pure (REFL t))
  | 'B' => infTerm st c (fun t => ofE (BETA t))
  | 'U' => infTerm st c (fun t => ofE (ASSUME t))
  | 'E' => infThmThm st c (fun a b => ofE (MK_COMB a b))
  | 'P' => infThmThm st c (fun a b => ofE (EQ_MP a b))
  | 'V' => infThmThm st c (fun a b => ofE (TRANS a b))
  | 'Z' => infThmThm st c (fun a b => pure (DEDUCT_ANTISYM_RULE a b))
  | 'F' => infAbs st c
  | 'S' => infInst st c
  | 'T' => infInstType st c
  -- axioms and definitional extension
  | 'X' => infTerm st c (fun t => ofIO (new_axiom t))
  | 'C' => infDef st c
  | 'A' => infTypedef st c
  | 'D' => infTypedefSnd st c
  -- ProofTrace bookkeeping
  | ',' => doPtProof st c
  | ';' => doPtSkip st c
  | _   => throw s!"unrecognized tag '{tag}'"

/-- Does the file's first line read exactly `HOLTrace 1`? -/
private def isMagic (buf : ByteArray) (start stop : Nat) : Bool := Id.run do
  let m := magic.toUTF8
  if stop - start != m.size then return false
  let mut i := 0
  while i < m.size do
    if byteAt buf (start + i) != byteAt m i then return false
    i := i + 1
  return true

/-- Replay a whole trace, already read into memory.

    Lines are slices of `buf`, so the file is traversed once with no copying.
    Any failure is reported against the line it happened on, which is what
    makes a malformed or rejected trace diagnosable at all in a file of
    millions of lines. -/
def replay (cfg : Config) (buf : ByteArray) : RestoreM State := do
  if buf.isEmpty then throw "empty file"
  declarePrimitives
  let mut st : State := {}
  let mut pos := 0
  while pos < buf.size do
    let n := st.lines + 1
    let some stop := lineEnd buf pos
      | throw s!"line {n}: the file does not end with LF (partial final line)"
    st ← try
        ofE (checkPrintable buf pos stop)
        if stop == pos then throw "a blank line is prohibited"
        if n == 1 then
          if !isMagic buf pos stop then throw s!"the file does not start with '{magic}'"
          pure st
        else
          step cfg st (Char.ofNat (byteAt buf pos).toNat) { buf, pos := pos + 1, stop }
      catch e => throw s!"line {n}: {e}"
    st := { st with lines := n, bytes := st.bytes + (stop - pos) + 1 }
    pos := stop + 1
  return st

/-- Read a trace from a file (or from stdin, for `-`) and replay it. -/
def verifyFile (cfg : Config) (path : String) : RestoreM State := do
  let buf ←
    if path == "-" then (← IO.getStdin).readBinToEnd
    else IO.FS.readBinFile path
  replay cfg buf

/-- The one-line summary of a verified trace, in the same shape as upstream's
    `holtrace-verify-simple`, so the two can be compared directly. -/
def State.summary (st : State) : String :=
  s!"verified {st.bytes} bytes, {st.lines} lines, {st.types.size} types, " ++
  s!"{st.terms.size} terms, {st.infs} infs, {st.thms.size} thms, " ++
  s!"{st.typedefs.size} typedefs"

end HolTrace
