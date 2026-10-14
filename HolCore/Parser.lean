/- File: Parser.lean
Lexical analyzer, type and preterm parsers.
John Harrison, University of Cambridge Computer Laboratory
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Original (c) Copyright, Andrea Gabrielli, Marco Maggesi 2017-2018
Lean4 translation by Chris Walton 2026 -/

import HolCore.Lib
import HolCore.Basics
import HolCore.Fusion
import HolCore.Nets
import HolCore.Printer
import HolCore.Preterm

open HolCore.Kernel
open HolCore.Basics
open HolCore.Lib
open HolCore.Nets
open HolCore.Printer
open HolCore.System
open HolCore.Preterm

namespace HolCore.Parser

/- ---------------------------------------------------------------------- -/
/- The basic lexical classes: identifiers, strings and reserved words.    -/
/- ---------------------------------------------------------------------- -/

/-- The basic lexical classes: identifiers and reserved words. -/
inductive lexcode where
  | Ident   (s : String)
  | Resword (s : String)
  deriving BEq, Repr, Inhabited

/-- `comment_token` (parser.ml 100): the token that starts a comment running to
    the end of the line.  A ref, as in OCaml (`comment_token := Ident "--"`). -/
initialize comment_token : IO.Ref lexcode ← IO.mkRef (.Resword "//")

/- ---------------------------------------------------------------------- -/
/- Need to have this now for set enums, since "," isn't a reserved word.  -/
/- ---------------------------------------------------------------------- -/

/- ---------------------------------------------------------------------- -/
/- Basic parser combinators.                                              -/
/-                                                                        -/
/- OCaml parsers are `token list -> result * token list`, signalling      -/
/- backtracking failure via the `Noparse` exception and fatal failure via -/
/- `Failure` (raised by `fix`/`finished`). We model both with `PErr`:     -/
/-   `.noparse`  = backtrack (caught by `|||`)                            -/
/-   `.fail msg` = fatal (propagates through `|||`)                       -/
/-                                                                        -/
/- Per option (B), the parser-status tables (infixes, arities, binders,   -/
/- prefixes, interface, reserved words, abbrevs, constants) are snapshot  -/
/- once into `Ctx` and threaded purely, so the combinators stay pure.     -/
/- ---------------------------------------------------------------------- -/

/-- Parser failure: `.noparse` backtracks (caught by `|||`), `.fail`
    is fatal and propagates. -/
inductive PErr where
  | noparse
  | fail (msg : String)
  deriving Repr, Inhabited

/- Snapshot of the parser-relevant global tables. -/
/-- A pure snapshot of the parser-relevant global tables, threaded
    through the combinators. -/
structure Ctx where
  infixesTbl   : List (String × (Int × String))
  typesTbl     : List (String × Int)
  constantsTbl : List (String × hol_type)
  reswords     : List String
  commentTok   : lexcode
  bindersTbl   : List String
  prefixesTbl  : List String
  interfaceTbl : List (String × (String × hol_type))
  abbrevsTbl   : List (String × hol_type)
  userParsers  : List (String × (List lexcode → IO (Except PErr (preterm × List lexcode))))

/- Pure queries against the snapshot (mirroring the IO accessors). -/
/-- The arity of type constructor `s`; fails with "get_type_arity". -/
def Ctx.get_type_arity (c : Ctx) (s : String) : Except String Int :=
  match assoc s c.typesTbl with | .ok n => .ok n | .error _ => failwith "get_type_arity"
/-- Is `s` the name of a known constant? -/
def Ctx.can_get_const_type (c : Ctx) (s : String) : Bool :=
  (assoc s c.constantsTbl).toOption.isSome
/-- The precedence and associativity of infix `s`; fails with
    "get_infix_status". -/
def Ctx.get_infix_status (c : Ctx) (s : String) : Except String (Int × String) :=
  match assoc s c.infixesTbl with | .ok r => .ok r | .error _ => failwith "get_infix_status"
/-- Is `s` a prefix operator? -/
def Ctx.is_prefix (c : Ctx) (s : String) : Bool := mem s c.prefixesTbl
/-- Does `s` parse as a binder? -/
def Ctx.parses_as_binder (c : Ctx) (s : String) : Bool := mem s c.bindersTbl
/-- Is `s` a reserved word? -/
def Ctx.is_reserved_word (c : Ctx) (s : String) : Bool := mem s c.reswords

/- Parsers are polymorphic in the token type `τ` (so the lexer can reuse the
   same combinators over `List String`). `Parser` is the `lexcode` instance. -/
/-- A parser over token type `τ`: consumes a prefix of the token list under
    a `Ctx`, producing a result and the remaining tokens, or a `PErr`. -/
abbrev ParserT (τ α : Type) := Ctx → List τ → Except PErr (α × List τ)
/-- A parser over `lexcode` tokens. -/
abbrev Parser (α : Type) := ParserT lexcode α

/- ---------------------------------------------------------------------- -/
/- Hook to allow installation of user parsers.                            -/
/- A user parser is a raw `List lexcode → Except PErr (preterm × ...)`    -/
/- (no `Ctx`, may `.noparse`). Installed parsers are snapshot into `Ctx`. -/
/- ---------------------------------------------------------------------- -/

/-- A user parser: a raw `lexcode` parser (no `Ctx`) producing a preterm.
    IO-valued, as OCaml's user parsers read the live parser tables and may
    themselves call `parse_preterm` (Library/bitmatch.ml does). -/
abbrev UserParser := List lexcode → IO (Except PErr (preterm × List lexcode))

initialize theParserList : IO.Ref (List (String × UserParser)) ← IO.mkRef []

/-- Install a user parser at the front of the list. -/
def install_parser (dat : String × UserParser) : IO Unit :=
  theParserList.modify (dat :: ·)

/-- Delete the user parser registered under `key`. -/
def delete_parser (key : String) : IO Unit :=
  theParserList.modify fun ps =>
    (remove (fun (key', _) => key == key') ps).toOption.map Prod.snd |>.getD ps

/-- The list of currently installed user parsers. -/
def installed_parsers : IO (List (String × UserParser)) :=
  theParserList.get

/- Snapshot the live tables into a `Ctx`. -/
/-- Snapshot the live global tables into a `Ctx`. -/
def mkCtx : IO Ctx := do
  return {
    infixesTbl   := ← infixes
    typesTbl     := ← types
    constantsTbl := ← constants
    reswords     := ← reserved_words
    commentTok   := ← comment_token.get
    bindersTbl   := ← binders
    prefixesTbl  := ← prefixes
    interfaceTbl := ← the_interface.get
    abbrevsTbl   := ← type_abbrevs
    userParsers  := ← theParserList.get
  }

/- `|||`: try p1; on `.noparse` try p2 (fatal `.fail` propagates). -/
/-- Ordered choice `p1 ||| p2`: run `p1`; on `.noparse` fall back to `p2`,
    while a fatal `.fail` propagates. -/
def por (p1 p2 : ParserT τ α) : ParserT τ α := fun c inp =>
  match p1 c inp with
  | .error .noparse => p2 c inp
  | r               => r

/- `++`: sequence, pairing results. -/
/-- Sequencing `p1 ++ p2`: run `p1` then `p2`, pairing their results. -/
def pseq (p1 : ParserT τ α) (p2 : ParserT τ β) : ParserT τ (α × β) := fun c inp => do
  let (r1, rest1) ← p1 c inp
  let (r2, rest2) ← p2 c rest1
  .ok ((r1, r2), rest2)

/- `many`: zero or more. -/
/-- `many prs`: apply `prs` zero or more times, collecting the results. -/
partial def pmany (prs : ParserT τ α) : ParserT τ (List α) := fun c inp =>
  match prs c inp with
  | .ok (result, next) =>
      match pmany prs c next with
      | .ok (results, rest) => .ok (result :: results, rest)
      | .error e            => .error e
  | .error .noparse => .ok ([], inp)
  | .error e        => .error e

/- `>>`: apply a treatment function to the result. -/
/-- `prs >> f`: apply the treatment `f` to the result of `prs`. -/
def pmap (prs : ParserT τ α) (f : α → β) : ParserT τ β := fun c inp => do
  let (result, rest) ← prs c inp
  .ok (f result, rest)

/- `>>` with a possibly-failing treatment: an `.error` from `f` becomes a fatal
   `.fail` (mirroring a `failwith`/`fail()` inside an OCaml `>>` treatment). -/
/-- `prs >> f` with a failing treatment: an `.error m` from `f` becomes a
    fatal `.fail m`. -/
def pmapE (prs : ParserT τ α) (f : α → Except String β) : ParserT τ β := fun c inp => do
  let (result, rest) ← prs c inp
  match f result with
  | .ok b    => .ok (b, rest)
  | .error m => .error (.fail m)

/- `fix`: turn a backtracking failure into a fatal `"<err> expected"`. -/
/-- `fix err prs`: turn `prs`'s backtracking failure into a fatal
    `"<err> expected"`. -/
def pfix (err : String) (prs : ParserT τ α) : ParserT τ α := fun c inp =>
  match prs c inp with
  | .error .noparse => .error (.fail (err ++ " expected"))
  | r               => r

/-- `nothing`: succeed consuming nothing, returning the empty list. -/
def pnothing : ParserT τ (List α) := fun _ inp => .ok ([], inp)

/- `listof prs sep err`: nonempty separated list. -/
/-- `listof prs sep err`: a nonempty list of `prs`, separated by `sep`,
    each element after a separator fixed with `err`. -/
def plistof (prs : ParserT τ α) (sep : ParserT τ β) (err : String) : ParserT τ (List α) :=
  pmap (pseq prs (pmany (pmap (pseq sep (pfix err prs)) Prod.snd)))
       (fun (h, t) => h :: t)

/-- `elistof prs sep err`: a possibly-empty separated list. -/
def pelistof (prs : ParserT τ α) (sep : ParserT τ β) (err : String) : ParserT τ (List α) :=
  por (plistof prs sep err) pnothing

/- `leftbin`/`rightbin`: left/right-associative binary operator folds. -/

/-- `leftbin prs sep cons err`: parse `prs` separated by `sep` and fold the
    operators left-associatively with `cons`. -/
def pleftbin (prs : ParserT τ α) (sep : ParserT τ β) (cons : β → α → α → α) (err : String) :
    ParserT τ α :=
  pmap (pseq prs (pmany (pseq sep (pfix err prs))))
    (fun (x, opxs) =>
      let (ops, xs) := unzip opxs
      (itlist2 (fun op y acc => cons op acc y) (rev ops) (rev xs) x).toOption.getD x)

/-- `rightbin prs sep cons err`: parse `prs` separated by `sep` and fold the
    operators right-associatively with `cons`. -/
def prightbin (prs : ParserT τ α) (sep : ParserT τ β) (cons : β → α → α → α) (err : String) :
    ParserT τ α :=
  pmap (pseq prs (pmany (pseq sep (pfix err prs))))
    (fun (x, opxs) =>
      if opxs.isEmpty then x
      else
        let (ops, xs) := unzip opxs
        (itlist2 cons ops (x :: (xs.dropLast)) (xs.getLastD x)).toOption.getD x)

/- `possibly`: zero or one occurrence, as a list. -/
/-- `possibly prs`: zero or one occurrence of `prs`, returned as a list. -/
def ppossibly (prs : ParserT τ α) : ParserT τ (List α) := fun c inp =>
  match prs c inp with
  | .ok (x, rest)   => .ok ([x], rest)
  | .error .noparse => .ok ([], inp)
  | .error e        => .error e

/- `some p`: consume one token satisfying `p`. -/
/-- `some p`: consume one token satisfying `p`, else `.noparse`. -/
def psome (p : τ → Bool) : ParserT τ τ := fun _ inp =>
  match inp with
  | []      => .error .noparse
  | h :: t  => if p h then .ok (h, t) else .error .noparse

/- `a tok`: consume a specific token. -/
/-- `a tok`: consume exactly the token `tok`. -/
def pa [BEq τ] (tok : τ) : ParserT τ τ := psome (fun item => item == tok)

/- `atleast n prs`: at least `n` occurrences. -/
/-- `atleast n prs`: parse at least `n` occurrences of `prs`. -/
partial def patleast (n : Nat) (prs : ParserT τ α) : ParserT τ (List α) :=
  if n <= 0 then pmany prs
  else pmap (pseq prs (patleast (n - 1) prs)) (fun (h, t) => h :: t)

/- `finished`: succeed (returning 0) only if input is exhausted. -/
/-- `finished`: succeed returning `0` only if the input is exhausted,
    else the fatal "Unparsed input". -/
def pfinished : ParserT τ Nat := fun _ inp =>
  if inp.isEmpty then .ok (0, inp) else .error (.fail "Unparsed input")

/- ---------------------------------------------------------------------- -/
/- Lexical analyzer. Apart from some special bracket symbols, each         -/
/- identifier is made up of the longest string of alphanumerics or         -/
/- the longest string of symbolics.                                       -/
/-   Operates over `List String` (chars-as-strings, from `explode`),       -/
/-   producing `List lexcode`. Reuses the generic combinators.            -/
/- ---------------------------------------------------------------------- -/

/- Char classifiers (projections of `charClassifiers`):
   (isspace, issep, isbra, issymb, isalpha, isnum, isalnum). -/
private def cc_isspace : String → Bool := charClassifiers.1
private def cc_issep   : String → Bool := charClassifiers.2.1
private def cc_isbra   : String → Bool := charClassifiers.2.2.1
private def cc_issymb  : String → Bool := charClassifiers.2.2.2.1
private def cc_isnum   : String → Bool := charClassifiers.2.2.2.2.2.1
private def cc_isalnum : String → Bool := charClassifiers.2.2.2.2.2.2


/- Concatenate a nonempty (head, tail) group of char-strings. -/
private def lcollect (ht : String × List String) : String :=
  (end_itlist (· ++ ·) (ht.1 :: ht.2)).toOption.getD (ht.1)

/- reserve: promote a reserved `Ident` to a `Resword`. -/
private def lreserve (c : Ctx) (tok : lexcode) : lexcode :=
  match tok with
  | .Ident n => if c.is_reserved_word n then .Resword n else tok
  | t        => t

/- stringof p: one-or-more chars matching `p`, concatenated. -/
private def lstringof (p : String → Bool) : ParserT String String :=
  pmap (patleast 1 (psome p)) (fun l => (end_itlist (· ++ ·) l).toOption.getD "")

private def lsimple_ident : ParserT String String :=
  por (lstringof cc_isalnum) (lstringof cc_issymb)

private def lundertail : ParserT String String :=
  pmap (pseq (lstringof (fun s => s == "_")) (ppossibly lsimple_ident))
       (fun (h, t) => lcollect (h, t))

private def lident : ParserT String String :=
  pmap (pseq (por lundertail lsimple_ident) (pmany lundertail))
       (fun (h, t) => lcollect (h, t))

private def lseptok : ParserT String String := lstringof cc_issep

/- Parse an OCaml-style escape code after a backslash. -/
private def lescapecode : ParserT String String := fun _ inp =>
  let hexDigit (s : String) : Option Nat :=
    match s.toList.head? with
    | some c =>
        if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
        else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
        else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
        else none
    | none => none
  let decDigit (s : String) : Option Nat :=
    match s.toList.head? with
    | some c => if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat) else none
    | none => none
  match inp with
  | "\\" :: rst => .ok ("\\", rst)
  | "\"" :: rst => .ok ("\"", rst)
  | "'"  :: rst => .ok ("'", rst)
  | "n"  :: rst => .ok ("\n", rst)
  | "r"  :: rst => .ok ("\r", rst)
  | "t"  :: rst => .ok ("\t", rst)
  | "b"  :: rst => .ok (String.singleton (Char.ofNat 8), rst)
  | " "  :: rst => .ok (" ", rst)
  | "x" :: h :: l :: rst =>
      match hexDigit h, hexDigit l with
      | some hi, some lo => .ok (String.singleton (Char.ofNat (16 * hi + lo)), rst)
      | _, _ => .error (.fail "lex:unrecognized OCaml-style escape in string")
  | a :: b :: cc :: rst =>
      match decDigit a, decDigit b, decDigit cc with
      | some da, some db, some dc =>
          .ok (String.singleton (Char.ofNat (100 * da + 10 * db + dc)), rst)
      | _, _, _ => .error (.fail "lex:unrecognized OCaml-style escape in string")
  | _ => .error (.fail "lex:unrecognized OCaml-style escape in string")

private def lstringchar : ParserT String String :=
  por (psome (fun i => i != "\\" && i != "\""))
      (pmap (pseq (pa "\\") lescapecode) Prod.snd)

private def lstring : ParserT String String :=
  pmap (pseq (pseq (pa "\"") (pmany lstringchar)) (pa "\""))
       (fun ((_, s), _) => "\"" ++ implode s ++ "\"")

private def lrawtoken : ParserT String lexcode :=
  pmap (por (por (por lstring (psome cc_isbra)) lseptok) lident) (fun x => .Ident x)

private def lsimptoken : ParserT String lexcode :=
  pmap (pseq (pmany (psome cc_isspace)) lrawtoken)
       (fun (_, tok) => tok)   -- reserve applied below (needs Ctx)

/- simptoken with `reserve` applied (needs `Ctx`). -/
private def lsimptoken' : ParserT String lexcode := fun c inp =>
  match lsimptoken c inp with
  | .ok (tok, rest) => .ok (lreserve c tok, rest)
  | e => e

/- tokens: lex a sequence, skipping `//`-comment lines. -/
private partial def ltokens : ParserT String (List lexcode) := fun c inp =>
  match lsimptoken' c inp with
  | .ok (t, rst) =>
      if t == c.commentTok then
        -- skip to end of line, then continue
        let skipLine : ParserT String (List String) :=
          pmany (fun _ i => match i with
                            | h :: t => if h != "\n" then .ok (h, t) else .error .noparse
                            | []     => .error .noparse)
        match (pmap (pseq skipLine ltokens) Prod.snd) c rst with
        | .ok r => .ok r
        | e => e
      else
        match ltokens c rst with
        | .ok (toks, rst1) => .ok (t :: toks, rst1)
        | e => e
  | .error .noparse => .ok ([], inp)
  | .error e        => .error e

/- The lexer: run `tokens`, consume trailing space, require exhaustion.
   Takes a `Ctx` because reserved-word detection consults `is_reserved_word`. -/
/-- Lexical analyzer: split a char-string list into `lexcode` tokens, where
    each identifier is the longest run of alphanumerics or of symbolics. -/
def lex (c : Ctx) (chars : List String) : Except PErr (List lexcode) :=
  -- fst o (tokens ++ many (some isspace) ++ finished >> (fst o fst))
  -- (parser.ml 145).  The `>>` post-processing is the projection `fst o fst`,
  -- both stages total, so plain `o`; the inner `fst` runs FIRST.
  let p : ParserT String (List lexcode) :=
    pmap (pseq (pseq ltokens (pmany (psome cc_isspace))) pfinished)
         (Prod.fst o Prod.fst)
  match p c chars with
  | .ok (toks, _) => .ok toks
  | .error e      => .error e

/- ---------------------------------------------------------------------- -/
/- Parser for pretypes.                                                   -/
/- ---------------------------------------------------------------------- -/

/- Parser for pretypes. Concrete syntax:

   TYPE        :: SUMTYPE -> TYPE
                | SUMTYPE

   SUMTYPE     :: PRODTYPE + SUMTYPE
                | PRODTYPE

   PRODTYPE    :: POWTYPE # PRODTYPE
                | POWTYPE

   POWTYPE     :: APPTYPE ^ POWTYPE
                | APPTYPE

   APPTYPE     :: ATOMICTYPES type-constructor  [Provided arity matches]
                | ATOMICTYPES                   [Provided only 1 ATOMICTYPE]

   ATOMICTYPES :: type-constructor              [Provided arity zero]
                | type-variable
                | ( TYPE )
                | ( TYPE LIST )

   TYPELIST    :: TYPE , TYPELIST
                | TYPE

   Two features make this different from previous HOL type syntax:

    o Any identifier not in use as a type constant will be parsed as a
      type variable; a ' is not needed and a * is not allowed.

    o Antiquotation is not supported. -/

/- mk_prefinty: numeral → finite-type pretype (via `1`/tybit0/tybit1). -/
private partial def mk_prefinty (n : Rat) : Except String pretype :=
  let rec prefinty (n : Rat) : pretype :=
    if n == num_1 then .Ptycon "1" []
    else
      let c := if mod_num n num_2 == num_0 then "tybit0" else "tybit1"
      .Ptycon c [prefinty (quo_num n num_2)]
  if !(is_integer_num n) || decide (n < num_1) then failwith "mk_prefinty"
  else .ok (prefinty n)

/- btyop: build a binary type constructor application. -/
private def btyop (name : String) (_op : lexcode) (x y : pretype) : pretype :=
  .Ptycon name [x, y]

/- mk_apptype: from (atomic types, optional constructor). -/
private def mk_apptype : (List pretype × List String) → Except String pretype
  | ([s], [])   => .ok s
  | (tys, [c])  => .ok (.Ptycon c tys)
  | _           => failwith "Bad type construction"

/- type_atom: an identifier resolved as abbrev / finty / arity-0 const / tyvar. -/
private def type_atom : ParserT lexcode pretype := fun c inp =>
  match inp with
  | (.Ident s) :: rest =>
      let res : pretype :=
        match assoc s c.abbrevsTbl with
        | .ok ty => pretype_of_type ty
        | .error _ =>
          match num_of_string s >>= mk_prefinty with
          | .ok pt => pt
          | .error _ =>
            let arity0 := match c.get_type_arity s with | .ok n => n == 0 | .error _ => false
            if arity0 then .Ptycon s [] else .Utv s
      .ok (res, rest)
  | _ => .error .noparse

/- type_constructor: an identifier with positive type arity. -/
private def type_constructor : ParserT lexcode String := fun c inp =>
  match inp with
  | (.Ident s) :: rest =>
      let posArity := match c.get_type_arity s with | .ok n => decide (n > 0) | .error _ => false
      if posArity then .ok (s, rest) else .error .noparse
  | _ => .error .noparse

mutual
  partial def pretypeP : ParserT lexcode pretype := fun c inp =>
    prightbin sumtypeP (pa (.Resword "->")) (btyop "fun")
      "proper use of type operator (->)" c inp
  partial def sumtypeP : ParserT lexcode pretype := fun c inp =>
    prightbin prodtypeP (pa (.Ident "+")) (btyop "sum")
      "proper use of type operator (+)" c inp
  partial def prodtypeP : ParserT lexcode pretype := fun c inp =>
    prightbin carttypeP (pa (.Ident "#")) (btyop "prod")
      "proper use of type operator (#)" c inp
  partial def carttypeP : ParserT lexcode pretype := fun c inp =>
    pleftbin apptypeP (pa (.Ident "^")) (btyop "cart")
      "proper use of type operator (^)" c inp
  partial def apptypeP : ParserT lexcode pretype := fun c inp =>
    (pmapE (pseq atomictypesP
                 (por (pmap type_constructor (fun x => [x])) pnothing))
           mk_apptype) c inp
  partial def atomictypesP : ParserT lexcode (List pretype) := fun c inp =>
    (por (pmap (pseq (pseq (pa (.Resword "(")) typelistP) (pa (.Resword ")")))
               (fun ((_, tl), _) => tl))
         (pmap type_atom (fun x => [x]))) c inp
  partial def typelistP : ParserT lexcode (List pretype) := fun c inp =>
    plistof pretypeP (pa (.Ident ",")) "comma separated list for type constructor" c inp
end

/- parse_pretype (entry to the pretype grammar). -/
/-- Parse a pretype: the entry point to the pretype grammar. -/
def parse_pretype : ParserT lexcode pretype := pretypeP

/- try_user_parser: try each installed parser in turn; first non-`.noparse`
   wins. As a `ParserT`, it reads the snapshot in `Ctx` (ignoring the token
   arg beyond passing input along). -/
/-- Try each installed user parser in turn; the first non-`.noparse` result
    wins. -/
def try_user_parser : Ctx → List lexcode → IO (Except PErr (preterm × List lexcode)) :=
  fun c inp =>
  let rec try_parsers (ps : List (String × UserParser)) :
      IO (Except PErr (preterm × List lexcode)) := do
    match ps with
    | []            => return .error .noparse
    | (_, p) :: rest =>
        match ← p inp with
        | .error .noparse => try_parsers rest
        | r               => return r
  try_parsers c.userParsers

/- ---------------------------------------------------------------------- -/
/- Preterm parser layer.                                                  -/
/-                                                                        -/
/- Preterm parsing needs a genvar counter (`pgenvar`), which is stateful, -/
/- so this layer is IO-valued: `ParserM α = Ctx → List lexcode →          -/
/- IO (Except PErr (α × List lexcode))`. The pure combinators are reused  -/
/- via `liftP`, with IO variants for sequencing/choice/etc.               -/
/- ---------------------------------------------------------------------- -/

/-- An IO-valued parser over `lexcode` tokens, used by the preterm layer
    which needs the stateful `pgenvar` counter. -/
abbrev ParserM (α : Type) := Ctx → List lexcode → IO (Except PErr (α × List lexcode))

initialize theParseGenCounter : IO.Ref Nat ← IO.mkRef 0

/- A fresh pattern-variable preterm `GEN%PVAR%<n>`. -/
/-- Generate a fresh pattern-variable preterm `GEN%PVAR%<n>`. -/
def pgenvar : IO preterm := do
  let n ← theParseGenCounter.get
  theParseGenCounter.set (n + 1)
  return .Varp ("GEN%PVAR%" ++ toString n) dpty

/- Lift a pure parser into the IO layer. -/
/-- Lift a pure `ParserT lexcode` parser into the IO layer. -/
def liftP (p : ParserT lexcode α) : ParserM α := fun c inp => return (p c inp)

/- IO combinators (mirrors of the pure ones). -/
/-- Ordered choice in the IO layer (`|||`). -/
def porM (p1 p2 : ParserM α) : ParserM α := fun c inp => do
  match ← p1 c inp with
  | .error .noparse => p2 c inp
  | r               => return r

/-- Sequencing in the IO layer (`++`), pairing results. -/
def pseqM (p1 : ParserM α) (p2 : ParserM β) : ParserM (α × β) := fun c inp => do
  match ← p1 c inp with
  | .error e => return .error e
  | .ok (r1, rest1) =>
    match ← p2 c rest1 with
    | .error e => return .error e
    | .ok (r2, rest2) => return .ok ((r1, r2), rest2)

/-- `many` in the IO layer: zero or more occurrences. -/
partial def pmanyM (prs : ParserM α) : ParserM (List α) := fun c inp => do
  match ← prs c inp with
  | .ok (result, next) =>
      match ← pmanyM prs c next with
      | .ok (results, rest) => return .ok (result :: results, rest)
      | .error e            => return .error e
  | .error .noparse => return .ok ([], inp)
  | .error e        => return .error e

/-- `>>` in the IO layer: apply a treatment to the result. -/
def pmapM (prs : ParserM α) (f : α → β) : ParserM β := fun c inp => do
  match ← prs c inp with
  | .error e        => return .error e
  | .ok (result, rest) => return .ok (f result, rest)

/- map with an IO treatment (for genvar-using constructions). -/
/-- `>>` with an IO treatment (for genvar-using constructions). -/
def pmapMIO (prs : ParserM α) (f : α → IO β) : ParserM β := fun c inp => do
  match ← prs c inp with
  | .error e        => return .error e
  | .ok (result, rest) => return .ok (← f result, rest)

/- map with a failing treatment (`.error m` → fatal `.fail m`). -/
/-- `>>` with a failing treatment (`.error m` becomes a fatal `.fail m`). -/
def pmapME (prs : ParserM α) (f : α → Except String β) : ParserM β := fun c inp => do
  match ← prs c inp with
  | .error e        => return .error e
  | .ok (result, rest) =>
    match f result with
    | .ok b    => return .ok (b, rest)
    | .error m => return .error (.fail m)

/-- `fix` in the IO layer: backtracking failure becomes `"<err> expected"`. -/
def pfixM (err : String) (prs : ParserM α) : ParserM α := fun c inp => do
  match ← prs c inp with
  | .error .noparse => return .error (.fail (err ++ " expected"))
  | r               => return r

/-- `possibly` in the IO layer: zero or one occurrence, as a list. -/
def ppossiblyM (prs : ParserM α) : ParserM (List α) := fun c inp => do
  match ← prs c inp with
  | .ok (x, rest)   => return .ok ([x], rest)
  | .error .noparse => return .ok ([], inp)
  | .error e        => return .error e

/-- `nothing` in the IO layer: succeed consuming nothing. -/
def pnothingM : ParserM (List α) := fun _ inp => return .ok ([], inp)

/-- `listof` in the IO layer: a nonempty separated list. -/
def plistofM (prs : ParserM α) (sep : ParserM β) (err : String) : ParserM (List α) :=
  pmapM (pseqM prs (pmanyM (pmapM (pseqM sep (pfixM err prs)) Prod.snd)))
        (fun (h, t) => h :: t)

/-- `elistof` in the IO layer: a possibly-empty separated list. -/
def pelistofM (prs : ParserM α) (sep : ParserM β) (err : String) : ParserM (List α) :=
  porM (plistofM prs sep err) pnothingM

/-- `leftbin` in the IO layer: left-associative binary operator fold. -/
def pleftbinM (prs : ParserM α) (sep : ParserM β) (cons : β → α → α → α) (err : String) :
    ParserM α :=
  pmapM (pseqM prs (pmanyM (pseqM sep (pfixM err prs))))
    (fun (x, opxs) =>
      let (ops, xs) := unzip opxs
      (itlist2 (fun op y acc => cons op acc y) (rev ops) (rev xs) x).toOption.getD x)

/-- `rightbin` in the IO layer: right-associative binary operator fold. -/
def prightbinM (prs : ParserM α) (sep : ParserM β) (cons : β → α → α → α) (err : String) :
    ParserM α :=
  pmapM (pseqM prs (pmanyM (pseqM sep (pfixM err prs))))
    (fun (x, opxs) =>
      if opxs.isEmpty then x
      else
        let (ops, xs) := unzip opxs
        (itlist2 cons ops (x :: xs.dropLast) (xs.getLastD x)).toOption.getD x)

/- `a`/`some` in the IO layer. -/
/-- `some p` in the IO layer: consume one token satisfying `p`. -/
def psomeM (p : lexcode → Bool) : ParserM lexcode := liftP (psome p)
/-- `a tok` in the IO layer: consume exactly the token `tok`. -/
def paM (tok : lexcode) : ParserM lexcode := liftP (pa tok)

/- Ordered choice over a list of alternatives (flat `|||` fold). Tries each in
   turn; `.noparse` falls through, a fatal `.fail` propagates. -/
/-- Ordered choice over a list of alternatives (a flat `|||` fold). -/
def pfirstM : List (ParserM α) → ParserM α
  | []      => fun _ _ => return .error .noparse
  | [p]     => p
  | p :: ps => porM p (pfirstM ps)

/- ---------------------------------------------------------------------- -/
/- Preterm-building helpers.                                              -/
/- ---------------------------------------------------------------------- -/

private def pairwise (r : α → α → Bool) : List α → Bool
  | []      => true
  | h :: t  => t.all (r h) && pairwise r t

/- Free (parser-level) variables of a preterm. -/
private def pfrees (c : Ctx) : preterm → List preterm
  | .Varp v pty =>
      if v == "" && pty == dpty then []
      else if c.can_get_const_type v || (num_of_string v).toOption.isSome
              || c.interfaceTbl.any (fun (w, _) => v == w) then []
      else [.Varp v pty]
  | .Constp _ _ => []
  | .Combp p1 p2 => union (pfrees c p1) (pfrees c p2)
  | .Absp p1 p2  => subtract (pfrees c p2) (pfrees c p1)
  | .Typing p _  => pfrees c p

private def pdest_eq : preterm → Except String (preterm × preterm)
  | .Combp (.Combp (.Varp "=" _) l) r   => .ok (l, r)
  | .Combp (.Combp (.Varp "<=>" _) l) r => .ok (l, r)
  | _ => failwith "pdest_eq"

private def pmk_vbinder (n : String) (v bod : preterm) : preterm :=
  if n == "\\" then .Absp v bod
  else .Combp (.Varp n dpty) (.Absp v bod)

private def pmk_binder (n : String) (vs : List preterm) (bod : preterm) : preterm :=
  itlist (fun v b => pmk_vbinder n v b) vs bod

private def pmk_set_enum (ptms : List preterm) : preterm :=
  itlist (fun x t => .Combp (.Combp (.Varp "INSERT" dpty) x) t) ptms (.Varp "EMPTY" dpty)

private def pmk_exists (v ptm : preterm) : preterm :=
  .Combp (.Varp "?" dpty) (.Absp v ptm)

private def pmk_list (els : List preterm) : preterm :=
  itlist (fun x y => .Combp (.Combp (.Varp "CONS" dpty) x) y) els (.Varp "NIL" dpty)

private def pmk_bool (b : Bool) : preterm := if b then .Varp "T" dpty else .Varp "F" dpty

private def pmk_char (code : Nat) : preterm :=
  let lis := (List.range 8).map (fun i => pmk_bool ((code / (2 ^ i)) % 2 == 1))
  itlist (fun x y => .Combp y x) lis (.Varp "ASCII" dpty)

private def pmk_string (s : String) : preterm :=
  let ns := s.toList.map (fun c => c.toNat)
  pmk_list (ns.map pmk_char)

private def pmk_geq (s t : preterm) : preterm :=
  .Combp (.Combp (.Varp "GEQ" dpty) s) t

/- pmk_let: build a let-preterm from bindings + body. (IO for the `warn`.) -/
private def pmk_let (c : Ctx) (letbindings : List preterm) (body : preterm) :
    IO (Except String preterm) := do
  match letbindings.mapM pdest_eq with
  | .error e => return .error e
  | .ok eqs =>
    let (vars, tms) := unzip eqs
    warn (!(pairwise (fun s t => (intersect (pfrees c s) (pfrees c t)).isEmpty) vars))
         "duplicate names on left of let-binding: latest is used"
    let lend := preterm.Combp (.Varp "LET_END" dpty) body
    let abs := itlist (fun v t => preterm.Absp v t) vars lend
    let labs := preterm.Combp (.Varp "LET" dpty) abs
    return .ok (rev_itlist (fun x f => preterm.Combp f x) tms labs)

/- genvar-using helpers (IO). -/
private def pmk_setcompr (_c : Ctx) (fabs : preterm) (bvs : List preterm) (babs : preterm) :
    IO preterm := do
  let v ← pgenvar
  let bod := itlist (fun bv t => pmk_exists bv t) bvs
              (.Combp (.Combp (.Combp (.Varp "SETSPEC" dpty) v) babs) fabs)
  return .Combp (.Varp "GSPEC" dpty) (.Absp v bod)

private def pmk_setabs (c : Ctx) (fabs babs : preterm) : IO preterm := do
  let fvs := pfrees c fabs
  let bvs := pfrees c babs
  let evs := if fvs.length <= 1 || bvs.isEmpty then fvs else intersect fvs bvs
  pmk_setcompr c fabs evs babs

private def pmk_pattern (c : Ctx) (pat : preterm) (guards : List preterm) (res : preterm) :
    IO preterm := do
  let x ← pgenvar
  let y ← pgenvar
  let vs := pfrees c pat
  let bod : preterm :=
    match guards with
    | [] => .Combp (.Combp (.Varp "_UNGUARDED_PATTERN" dpty) (pmk_geq pat x)) (pmk_geq res y)
    | g :: _ =>
        .Combp (.Combp (.Combp (.Varp "_GUARDED_PATTERN" dpty) (pmk_geq pat x)) g)
               (pmk_geq res y)
  return .Absp x (.Absp y (itlist (fun v t => pmk_exists v t) vs bod))

/- ---------------------------------------------------------------------- -/
/- Leaf token parsers (pure; lifted into the IO layer where used).        -/
/- ---------------------------------------------------------------------- -/

private def any_identifier : ParserT lexcode String := fun _ inp =>
  match inp with
  | (.Ident s) :: rest => .ok (s, rest)
  | _ => .error .noparse

private def identifierP : ParserT lexcode String := fun c inp =>
  match inp with
  | (.Ident s) :: rest =>
      if (c.get_infix_status s).toOption.isSome || c.is_prefix s || c.parses_as_binder s
      then .error .noparse else .ok (s, rest)
  | _ => .error .noparse

private def binderTok : ParserT lexcode String := fun c inp =>
  match inp with
  | (.Ident s) :: rest => if c.parses_as_binder s then .ok (s, rest) else .error .noparse
  | _ => .error .noparse

private def pre_fixTok : ParserT lexcode String := fun c inp =>
  match inp with
  | (.Ident s) :: rest => if c.is_prefix s then .ok (s, rest) else .error .noparse
  | _ => .error .noparse

/- A quoted string literal token `"..."` → its unquoted contents. -/
private def stringTok : ParserT lexcode String := fun _ inp =>
  match inp with
  | (.Ident s) :: rst =>
      let cs := s.toList
      if cs.length >= 2 && cs.head? == some '"' && cs.getLast? == some '"' then
        .ok (String.ofList (cs.drop 1 |>.dropLast), rst)
      else .error .noparse
  | _ => .error .noparse

/- Build a binary-operator combination preterm from an operator token. -/
private def pmk_binop (op : lexcode) (x y : preterm) : preterm :=
  match op with
  | .Ident s => .Combp (.Combp (.Varp s dpty) x) y
  | .Resword s => .Combp (.Combp (.Varp s dpty) x) y

/- mk_precedence: parse infixes by descending precedence groups. -/
private partial def mk_precedence (infxs : List (String × (Int × String)))
    (prs : ParserM preterm) : ParserM preterm :=
  match infxs with
  | (_, (p, asc)) :: _ =>
      let (topins, rest) := infxs.partition (fun (_, pat') => pat' == (p, asc))
      let opParser : ParserM lexcode :=
        match (end_itlist por (topins.map (fun (s, _) => pa (.Ident s)))).toOption with
        | some pr => liftP pr
        | none    => fun _ _ => return .error .noparse
      let sub := mk_precedence rest prs
      let bin := if asc == "right" then prightbinM else pleftbinM
      bin sub opParser pmk_binop "term after binary operator"
  | [] => prs

/- ---------------------------------------------------------------------- -/
/- Treatments and lifted leaf parsers for the preterm grammar.            -/
/- ---------------------------------------------------------------------- -/

/- lmk_typed: attach an optional type ascription. -/
private def lmk_typed : (preterm × List pretype) → Except String preterm
  | (p, [])   => .ok p
  | (p, [ty]) => .ok (.Typing p ty)
  | _         => failwith "lmk_typed"

/- lmk_ite: build a COND preterm from the parsed `if`/`then`/`else` bodies
   (the caller unpacks the token tuple). -/
private def lmk_ite (b l rr : preterm) : preterm :=
  .Combp (.Combp (.Combp (.Varp "COND" dpty) b) l) rr

/- lmk_decimal: build a DECIMAL preterm. -/
private def lmk_decimal (l0 : String) (ropt : List String) : Except String preterm := do
  let (l, r) ←
    if ropt.isEmpty then Except.ok (l0, "1")
    else
      let r0 := ropt.headD ""
      do
        let n_l ← num_of_string l0
        let n_r ← num_of_string r0
        let n_d := (num_10) ^ (r0.length)
        let n_n := n_l * n_d + n_r
        Except.ok (string_of_num n_n, string_of_num n_d)
  .ok (.Combp (.Combp (.Varp "DECIMAL" dpty) (.Varp l dpty)) (.Varp r dpty))

/- lmk_univ: build a typed UNIV `(:ty)`. -/
private def lmk_univ (pty : pretype) : preterm :=
  .Typing (.Varp "UNIV" dpty) (.Ptycon "fun" [pty, .Ptycon "bool" []])

/- Lifted leaf parsers (IO layer). -/
private def pre_fixM : ParserM String := liftP pre_fixTok
private def binderTokM : ParserM String := liftP binderTok
private def any_identifierM : ParserM String := liftP any_identifier
private def identifierM : ParserM String := liftP identifierP
private def stringTokM : ParserM String := liftP stringTok

/- pmapMIO variant whose treatment receives the `Ctx`. -/
private def pmapMIOc (prs : ParserM α) (f : Ctx → α → IO β) : ParserM β := fun c inp => do
  match ← prs c inp with
  | .error e => return .error e
  | .ok (result, rest) => return .ok (← f c result, rest)

/- pmapMIO variant whose treatment receives the `Ctx` and may fail
   (`.error m` → fatal `.fail m`). -/
private def pmapMIOEc (prs : ParserM α) (f : Ctx → α → IO (Except String β)) : ParserM β :=
  fun c inp => do
  match ← prs c inp with
  | .error e => return .error e
  | .ok (result, rest) =>
    match ← f c result with
    | .ok b    => return .ok (b, rest)
    | .error m => return .error (.fail m)

/- pmapMEc: failing treatment that also receives the `Ctx` (`.error`→`.fail`). -/
private def pmapMEc (prs : ParserM α) (f : Ctx → α → Except String β) : ParserM β :=
  fun c inp => do
  match ← prs c inp with
  | .error e => return .error e
  | .ok (result, rest) =>
    match f c result with
    | .ok b    => return .ok (b, rest)
    | .error m => return .error (.fail m)

/- Initial preterm parsing. This uses binder and precedence/associativity/
   prefix status to guide parsing and preterm construction, but treats all
   identifiers as variables.

   PRETERM            :: APPL_PRETERM binop APPL_PRETERM
                       | APPL_PRETERM

   APPL_PRETERM       :: APPL_PRETERM : type
                       | APPL_PRETERM BINDER_PRETERM
                       | BINDER_PRETERM

   BINDER_PRETERM     :: binder VARSTRUCT_PRETERMS . PRETERM
                       | let PRETERM and ... and PRETERM in PRETERM
                       | ATOMIC_PRETERM

   VARSTRUCT_PRETERMS :: TYPED_PRETERM VARSTRUCT_PRETERMS
                       | TYPED_PRETERM

   TYPED_PRETERM      :: TYPED_PRETERM : type
                       | ATOMIC_PRETERM

   ATOMIC_PRETERM     :: ( PRETERM )
                       | if PRETERM then PRETERM else PRETERM
                       | [ PRETERM; .. ; PRETERM ]
                       | { PRETERM, .. , PRETERM }
                       | { PRETERM | PRETERM }
                       | identifier

   Note that arbitrary preterms are allowed as varstructs. This allows
   more general forms of matching and considerably regularizes the syntax. -/

/- ---------------------------------------------------------------------- -/
/- The main preterm grammar (mutually recursive).                         -/
/- `pseqM a b` yields a left-nested pair `(a,b)`; chains nest to the left.-/
/- ---------------------------------------------------------------------- -/

mutual
  partial def pretermP : ParserM preterm := fun c inp =>
    mk_precedence c.infixesTbl typed_appl_pretermP c inp

  partial def nocommapretermP : ParserM preterm := fun c inp =>
    mk_precedence (c.infixesTbl.filter (fun (s, _) => s != ",")) typed_appl_pretermP c inp

  partial def typed_appl_pretermP : ParserM preterm := fun c inp =>
    pmapME
      (pseqM appl_pretermP
             (ppossiblyM (pmapM (pseqM (paM (.Resword ":")) (liftP parse_pretype)) Prod.snd)))
      lmk_typed c inp

  partial def appl_pretermP : ParserM preterm := fun c inp =>
    porM
      (pmapM (pseqM pre_fixM appl_pretermP)
             (fun (x, y) => preterm.Combp (.Varp x dpty) y))
      (pmapM (pseqM binder_pretermP (pmanyM binder_pretermP))
             (fun (h, t) => itlist (fun x y => preterm.Combp y x) (rev t) h))
      c inp

  partial def binder_pretermP : ParserM preterm := fun c inp =>
    porM
      (porM
        -- let BND and ... and BND in PRETERM
        (pmapMIOEc
          (pseqM (pseqM (pseqM (paM (.Resword "let"))
                   (pleftbinM (pmapM pretermP (fun x => [x])) (paM (.Resword "and"))
                              (fun _ a b => a ++ b) "binding"))
                  (paM (.Resword "in"))) pretermP)
          (fun c' r => let (((_, bnds), _), ptm) := r; pmk_let c' bnds ptm))
        -- binder VARSTRUCTs . PRETERM
        (pmapM
          (pseqM (pseqM (pseqM (pseqM binderTokM typed_apretermP)
                   (pmanyM typed_apretermP)) (paM (.Resword "."))) pretermP)
          (fun ((((s, h), t), _), p) => pmk_binder s (h :: t) p)))
      atomic_pretermP
      c inp

  partial def typed_apretermP : ParserM preterm := fun c inp =>
    pmapME
      (pseqM atomic_pretermP
             (ppossiblyM (pmapM (pseqM (paM (.Resword ":")) (liftP parse_pretype)) Prod.snd)))
      lmk_typed c inp

  partial def atomic_pretermP : ParserM preterm := fun c inp =>
    pfirstM [
      try_user_parser,
      -- ( : type )   → universe
      pmapM (pseqM (pseqM (pseqM (paM (.Resword "(")) (paM (.Resword ":")))
              (liftP parse_pretype)) (paM (.Resword ")")))
            (fun (((_, _), pty), _) => lmk_univ pty),
      -- ( : type   → error: missing closing paren
      pmapME (pseqM (pseqM (paM (.Resword "(")) (paM (.Resword ":"))) (liftP parse_pretype))
             (fun _ => failwith "closing right parenthesis on universe expected"),
      -- ( :   → error: missing type
      pmapME (pseqM (paM (.Resword "(")) (paM (.Resword ":")))
             (fun _ => failwith "type in universe construction expected"),
      -- string literal
      pmapM stringTokM pmk_string,
      -- ( any_identifier )
      pmapM (pseqM (pseqM (paM (.Resword "(")) any_identifierM) (paM (.Resword ")")))
            (fun ((_, s), _) => preterm.Varp s dpty),
      -- ( PRETERM )
      pmapM (pseqM (pseqM (paM (.Resword "(")) pretermP) (paM (.Resword ")")))
            (fun ((_, p), _) => p),
      -- if P then P else P
      pmapM (pseqM (pseqM (pseqM (pseqM (pseqM (paM (.Resword "if")) pretermP)
              (paM (.Resword "then"))) pretermP) (paM (.Resword "else"))) pretermP)
            (fun (((((_, b), _), l), _), rr) => lmk_ite b l rr),
      -- if P then P else   → error
      pmapME (pseqM (pseqM (pseqM (pseqM (paM (.Resword "if")) pretermP)
               (paM (.Resword "then"))) pretermP) (paM (.Resword "else")))
             (fun _ => failwith "malformed else clause"),
      -- if P then P   → error
      pmapME (pseqM (pseqM (pseqM (paM (.Resword "if")) pretermP)
               (paM (.Resword "then"))) pretermP)
             (fun _ => failwith "missing else following then clause"),
      -- if P then   → error
      pmapME (pseqM (pseqM (paM (.Resword "if")) pretermP) (paM (.Resword "then")))
             (fun _ => failwith "malformed then clause in if-then-else statement"),
      -- if P   → error
      pmapME (pseqM (paM (.Resword "if")) pretermP)
             (fun _ => failwith "missing 'then' reserved word in if-then-else statement"),
      -- if   → error
      pmapME (paM (.Resword "if"))
             (fun _ => failwith "malformed if-then-else"),
      -- [ list ]
      pmapM (pseqM (pseqM (paM (.Resword "["))
              (pelistofM pretermP (paM (.Resword ";")) "semicolon separated list of terms"))
              (paM (.Resword "]")))
            (fun ((_, l), _) => pmk_list l),
      -- [ list   → error
      pmapME (pseqM (paM (.Resword "["))
              (pelistofM pretermP (paM (.Resword ";")) "semicolon separated list of terms"))
             (fun _ => failwith "closing square bracket of list expected"),
      -- { setenum | setabs | setcompr }
      pmapM (pseqM (paM (.Resword "{"))
              (pfirstM [
                pmapM (pseqM (pelistofM nocommapretermP (paM (.Ident ","))
                         "comma separated list of terms") (paM (.Resword "}")))
                      (fun (l, _) => pmk_set_enum l),
                pmapMIOc (pseqM (pseqM (pseqM pretermP (paM (.Resword "|"))) pretermP)
                          (paM (.Resword "}")))
                   (fun c' r => let (((l, _), rr), _) := r; pmk_setabs c' l rr),
                pmapMIOc (pseqM (pseqM (pseqM (pseqM (pseqM pretermP (paM (.Resword "|")))
                          pretermP) (paM (.Resword "|"))) pretermP) (paM (.Resword "}")))
                   (fun c' r =>
                      let (((((f, _), vs), _), b), _) := r
                      pmk_setcompr c' f (pfrees c' vs) b) ]))
            Prod.snd,
      -- {   → error
      pmapME (paM (.Resword "{")) (fun _ => failwith "malformed set {}"),
      -- match E with clauses
      pmapM (pseqM (pseqM (pseqM (paM (.Resword "match")) pretermP)
              (paM (.Resword "with"))) clausesP)
            (fun (((_, e), _), cl) => preterm.Combp (.Combp (.Varp "_MATCH" dpty) e) cl),
      -- match   → error
      pmapME (paM (.Resword "match")) (fun _ => failwith "malformed match-with statement"),
      -- function clauses
      pmapM (pseqM (paM (.Resword "function")) clausesP)
            (fun (_, cl) => preterm.Combp (.Varp "_FUNCTION" dpty) cl),
      -- function   → error
      pmapME (paM (.Resword "function"))
             (fun _ => failwith "malformed function and pattern clauses"),
      -- # identifier [. identifier]   → decimal
      pmapME (pseqM (pseqM (paM (.Ident "#")) identifierM)
               (ppossiblyM (pmapM (pseqM (paM (.Resword ".")) identifierM) Prod.snd)))
             (fun ((_, l0), ropt) => lmk_decimal l0 ropt),
      -- #   → error
      pmapME (paM (.Ident "#")) (fun _ => failwith "malformed numerical # identifier"),
      -- identifier
      pmapM identifierM (fun s => preterm.Varp s dpty)
    ] c inp

  partial def patternP : ParserM (preterm × List preterm) := fun c inp =>
    pseqM pretermP
      (ppossiblyM (pmapM (pseqM (paM (.Resword "when")) pretermP) Prod.snd)) c inp

  partial def clauseP : ParserM preterm := fun c inp =>
    pmapMIOc (pseqM patternP (pmapM (pseqM (paM (.Resword "->")) pretermP) Prod.snd))
       (fun c' ((pat, guards), res) => pmk_pattern c' pat guards res) c inp

  partial def clausesP : ParserM preterm := fun c inp =>
    pmapM
      (pmapM (pseqM (ppossiblyM (paM (.Resword "|")))
               (plistofM clauseP (paM (.Resword "|")) "pattern-match clause"))
             Prod.snd)
      (fun cls => (end_itlist (fun s t =>
                     preterm.Combp (.Combp (.Varp "_SEQPATTERN" dpty) s) t) cls).toOption.getD
                     (.Varp "" dpty))
      c inp
end

/- Top-level preterm parser: a lone non-string identifier is a plain var. -/
/-- Top-level preterm parser: a lone non-string identifier is a plain
    variable; otherwise defer to the preterm grammar. -/
def parse_preterm : ParserM preterm := fun c inp =>
  match inp with
  | [.Ident s] =>
      let isStr := s.length >= 2 && s.toList.head? == some '"' && s.toList.getLast? == some '"'
      if !isStr then return .ok (.Varp s dpty, []) else pretermP c inp
  | _ => pretermP c inp

/- ---------------------------------------------------------------------- -/
/- Type and term parsers.                                                 -/
/- ---------------------------------------------------------------------- -/

def perrMsg : PErr → String
  | .noparse  => "Noparse"
  | .fail msg => msg

/- parse_type: lex + parse a pretype + convert to a type. -/
/-- Parse a string as a type: lex, parse a pretype, convert to a type;
    fails with "Unparsed input following type" on leftover tokens. -/
def parse_type (s : String) : IO (Except String hol_type) := do
  let c ← mkCtx
  match lex c (explode s) with
  | .error e => return .error (perrMsg e)
  | .ok toks =>
    match parse_pretype c toks with
    | .error e => return .error (perrMsg e)
    | .ok (pty, l) =>
        if l.isEmpty then (type_of_pretype pty).run
        else return .error "Unparsed input following type"

/- parse_term: lex + parse a preterm + typecheck + convert to a term. -/
/-- Parse a string as a term: lex, parse a preterm, typecheck, convert to a
    term; fails with "Unparsed input following term" on leftover tokens. -/
def parse_term (s : String) : IO (Except String term) := do
  let c ← mkCtx
  match lex c (explode s) with
  | .error e => return .error (perrMsg e)
  | .ok toks =>
    match ← parse_preterm c toks with
    | .error e => return .error (perrMsg e)
    | .ok (ptm, l) =>
        if l.isEmpty then
          (do term_of_preterm (← retypecheck [] ptm)).run
        else return .error "Unparsed input following term"

end HolCore.Parser
