/- File: Printer.lean
Simplistic HOL Light prettyprinter, using the OCaml "Format" library.
John Harrison, University of Cambridge Computer Laboratory
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Original (c) Copyright, Marco Maggesi 2017
Original (c) Copyright, Andrea Gabrielli, Marco Maggesi 2017-2018
Lean4 translation by Chris Walton 2026

The OCaml "Format" library is `HolCore.System`'s translation of OCaml's
format.ml (`Fmt`), so each box below is opened with the same kind (`box`,
`hvbox` or `hbox`) as in printer.ml. -/

import HolCore.Lib
import HolCore.Basics
import HolCore.Fusion
import HolCore.System
open HolCore.Kernel
open HolCore.Basics
open HolCore.Lib
open HolCore.System

namespace HolCore.Printer

/- Character discrimination. -/
/-- The seven character classifiers `(isspace, issep, isbra, issymb,
    isalpha, isnum, isalnum)`, built from a class table. -/
def charClassifiers :
    (String → Bool) × (String → Bool) × (String → Bool) × (String → Bool) ×
    (String → Bool) × (String → Bool) × (String → Bool) :=
  let charcode (s : String) : Nat :=
    match s.toList with
    | c :: _ => c.toNat
    | []     => 0
  let spaces     := " \t\n\r"
  let separators := ",;"
  let brackets   := "()[]{}"
  let symbs      := "\\!@#$%^&*-+|\\<=>/?~.:"
  let alphas     := "'abcdefghijklmnopqrstuvwxyz_ABCDEFGHIJKLMNOPQRSTUVWXYZ"
  let nums       := "0123456789"
  let allchars   := spaces ++ separators ++ brackets ++ symbs ++ alphas ++ nums
  let csetsize   := itlist (fun c acc => Nat.max (charcode c) acc) (explode allchars) 256
  let ctable : Array Nat := Id.run do
    let mut t : Array Nat := Array.replicate (csetsize + 1) 0
    for (cls, str) in [(1, spaces), (2, separators), (4, brackets),
                        (8, symbs), (16, alphas), (32, nums)] do
      for c in explode str do
        t := t.setIfInBounds (charcode c) cls
    return t
  let classOf (c : String) : Nat := (ctable[charcode c]?).getD 0
  let isspace (c : String) : Bool := classOf c == 1
  let issep   (c : String) : Bool := classOf c == 2
  let isbra   (c : String) : Bool := classOf c == 4
  let issymb  (c : String) : Bool := classOf c == 8
  let isalpha (c : String) : Bool := classOf c == 16
  let isnum   (c : String) : Bool := classOf c == 32
  let isalnum (c : String) : Bool := classOf c >= 16
  (isspace, issep, isbra, issymb, isalpha, isnum, isalnum)

/- Reserved words. -/
private initialize theReservedWords : IO.Ref (List String) ←
IO.mkRef ["(", ")", "[", "]", "{", "}",
          ":", ";", ".", "|",
          "let", "in", "and", "if", "then", "else",
          "match", "with", "function", "->", "when",
          -- parser.ml 98: `reserve_words ["//"]`, the comment token.
          "//"]
/-- Add `ns` to the list of reserved words. -/
def reserve_words (ns : List String) : IO Unit :=
  theReservedWords.modify (fun ws => union ws ns)
/-- Remove `ns` from the list of reserved words. -/
def unreserve_words (ns : List String) : IO Unit :=
  theReservedWords.modify (fun ws => subtract ws ns)
/-- Is `n` a reserved word? -/
def is_reserved_word (n : String) : IO Bool := do
  return mem n (← theReservedWords.get)
/-- The current list of reserved words. -/
def reserved_words : IO (List String) :=
  theReservedWords.get

/- Functions to access the global tables controlling special parse status.
o List of binders;
o List of prefixes (right-associated unary functions like negation).
o List of infixes with their precedences and associations.
Note that these tables are independent of constant/variable status or
whether an identifier is symbolic.
-/
private initialize theBinders : IO.Ref (List String) ←
  IO.mkRef ([] : List String)
/-- Remove `n` from the list of binders. -/
def unparse_as_binder (n : String) : IO Unit :=
  theBinders.modify (fun bs => subtract bs [n])
/-- Add `n` to the list of binders. -/
def parse_as_binder (n : String) : IO Unit :=
  theBinders.modify (fun bs => union bs [n])
/-- Does `n` parse as a binder? -/
def parses_as_binder (n : String) : IO Bool := do
  return mem n (← theBinders.get)
/-- The current list of binders. -/
def binders : IO (List String) :=
  theBinders.get

private initialize thePrefixes : IO.Ref (List String) ←
  IO.mkRef ([] : List String)
/-- Remove `n` from the list of prefixes. -/
def unparse_as_prefix (n : String) : IO Unit :=
  thePrefixes.modify (fun ps => subtract ps [n])
/-- Add `n` to the list of prefixes. -/
def parse_as_prefix (n : String) : IO Unit :=
  thePrefixes.modify (fun ps => union ps [n])
/-- Is `n` a prefix operator? -/
def is_prefix (n : String) : IO Bool := do
  return mem n (← thePrefixes.get)
/-- The current list of prefixes. -/
def prefixes : IO (List String) :=
  thePrefixes.get

private initialize theInfixes : IO.Ref (List (String × (Int × String))) ←
  IO.mkRef ([] : List (String × (Int × String)))
private def infixCmp :
    (String × (Int × String)) → (String × (Int × String)) → Bool :=
  fun (s, (x, a)) (t, (y, b)) =>
    x < y || (x == y && compare a b == .gt) || (x == y && a == b && compare s t == .lt)
/-- Remove `n` from the list of infixes. -/
def unparse_as_infix (n : String) : IO Unit :=
  theInfixes.modify (fun l => filter (fun p => p.1 != n) l)
/-- Add the infix `nd` (name with precedence and associativity), keeping
    the list sorted by precedence then name. -/
def parse_as_infix (nd : String × (Int × String)) : IO Unit :=
  theInfixes.modify (fun l =>
    sort infixCmp (nd :: filter (fun p => p.1 != nd.1) l))
/-- The precedence and associativity of the infix `n`, if any. -/
def get_infix_status (n : String) : IO (Except String (Int × String)) := do
  return assoc n (← theInfixes.get)
/-- The current list of infixes with their precedences and associations. -/
def infixes : IO (List (String × (Int × String))) :=
  theInfixes.get

/- Interface mapping. -/
initialize the_interface : IO.Ref (List (String × (String × hol_type))) ←
  IO.mkRef ([] : List (String × (String × hol_type)))
initialize the_overload_skeletons : IO.Ref (List (String × hol_type)) ←
  IO.mkRef ([] : List (String × hol_type))

/- Now the printer.  The formatter (`Fmt`, a translation of OCaml's Format)
   lives in `HolCore.System`, opened above. -/

/- Flag determining whether interface/overloading is reversed on printing. -/
initialize reverse_interface_mapping : IO.Ref Bool ← IO.mkRef true

/- Determine binary operators that print without surrounding spaces. -/
initialize unspaced_binops : IO.Ref (List String) ← IO.mkRef [",", "..", "$"]

/- Binary operators to print at start of line when breaking. -/
initialize prebroken_binops : IO.Ref (List String) ← IO.mkRef ["==>"]

/- Force explicit indications of bound variables in set abstractions. -/
initialize print_unambiguous_comprehensions : IO.Ref Bool ← IO.mkRef false

/- Print the universal set UNIV:A->bool as "(:A)". -/
initialize typify_universal_set : IO.Ref Bool ← IO.mkRef true

/- Flag controlling whether hypotheses print. -/
initialize print_all_thm : IO.Ref Bool ← IO.mkRef true

/- Flag controlling whether types of subterms must be printed.
0: Do not print the types of subterms
1 (default) : Only print types containing invented type variables
2: Print the types of constants and variables
-/
initialize print_types_of_subterms : IO.Ref Int ← IO.mkRef 1

/- Get the name of a constant or variable. -/
/-- The name of a constant or variable (empty string otherwise). -/
def name_of (tm : term) : String :=
  match tm with
  | .Var x _ => x
  | .Const x _ => x
  | _ => ""

/- Colors -/
/- These numbers are ANSI color codes. -/
/- Const -/
initialize printer_color_const : IO.Ref (Option String) ← IO.mkRef (some "32")  -- green
/- Reserved words, excluding non-alphabets -/
initialize printer_color_resword : IO.Ref (Option String) ← IO.mkRef (some "34")  -- blue
/- Binders -/
initialize printer_color_binder : IO.Ref (Option String) ← IO.mkRef (some "35")  -- purple
/- Infixes -/
initialize printer_color_infix : IO.Ref (Option String) ← IO.mkRef none
/- Prefixes -/
initialize printer_color_prefix : IO.Ref (Option String) ← IO.mkRef none
/- Types -/
initialize printer_color_type : IO.Ref (Option String) ← IO.mkRef (some "36")  -- light blue
/- Type variables -/
initialize printer_color_typevar : IO.Ref (Option String) ← IO.mkRef (some "34")  -- blue
/- Invented type variables -/
initialize printer_color_itypevar : IO.Ref (Option String) ← IO.mkRef (some "31")  -- red

/-- Print `contents` wrapped in the ANSI color escape `colorcode`, or plainly
    when no color is given. -/
def pp_print_colored_string (colorcode : Option String) (contents : String) : Fmt Unit :=
  match colorcode with
  | some thecode => do
      -- \027 is decimal 27 (oct 33) which corresponds to
      -- "Set foreground color" in Select Graphic Rendition
      let ansicmd := "\x1b[" ++ thecode ++ "m"
      let endcmd  := "\x1b[0m"
      Fmt.printAs 0 ansicmd        -- consider ansicmd as 0-len string
      Fmt.printString contents
      Fmt.printAs 0 endcmd
  | none => Fmt.printString contents

/-- Print `s` in the constant color. -/
def pp_print_colored_const (s : String) : IO (Fmt Unit) := do
  return pp_print_colored_string (← printer_color_const.get) s
/-- Print `s` in the reserved-word color. -/
def pp_print_colored_resword (s : String) : IO (Fmt Unit) := do
  return pp_print_colored_string (← printer_color_resword.get) s
/-- Print `s` in the binder color. -/
def pp_print_colored_binder (s : String) : IO (Fmt Unit) := do
  return pp_print_colored_string (← printer_color_binder.get) s
/-- Print `s` in the infix color. -/
def pp_print_colored_infix (s : String) : IO (Fmt Unit) := do
  return pp_print_colored_string (← printer_color_infix.get) s
/-- Print `s` in the prefix color. -/
def pp_print_colored_prefix (s : String) : IO (Fmt Unit) := do
  return pp_print_colored_string (← printer_color_prefix.get) s
/-- Print type variable `s` in the invented- or ordinary-type-variable
    color, depending on whether it begins with `?`. -/
def pp_print_colored_tyvar (s : String) : IO (Fmt Unit) := do
  let isInvented := s.toList.head? == some '?'   -- invented type var?
  let color ← if isInvented then printer_color_itypevar.get else printer_color_typevar.get
  return pp_print_colored_string color s

/- Printer for types. -/
/-- Print a type, parenthesising `->`, `+`, `#`, and `^` by precedence. -/
partial def pp_print_type (ty : hol_type) : Fmt Unit :=
  Fmt.printString (sot 0 ty)
where
  soc (sep : String) (flag : Bool) (ss : List String) : String :=
    if ss == [] then ""
    else
      let s := (end_itlist (fun s1 s2 => s1 ++ sep ++ s2) ss).toOption.getD ""
      if flag then "(" ++ s ++ ")" else s
  sot (pr : Int) (ty : hol_type) : String :=
    match dest_vartype ty with
    | .ok v => v
    | .error _ =>
      match dest_finty ty with
      | .ok n => string_of_num n
      | .error _ =>
        match dest_type ty with
        | .error _ => ""
        | .ok (con, args) =>
          match con, args with
          | con, []            => con
          | "fun",  [ty1, ty2] => soc "->" (pr > 0) [sot 1 ty1, sot 0 ty2]
          | "sum",  [ty1, ty2] => soc "+"  (pr > 2) [sot 3 ty1, sot 2 ty2]
          | "prod", [ty1, ty2] => soc "#"  (pr > 4) [sot 5 ty1, sot 4 ty2]
          | "cart", [ty1, ty2] => soc "^"  (pr > 6) [sot 6 ty1, sot 7 ty2]
          | con, args          => soc "," true (args.map (sot 0)) ++ con
/-- Print a type enclosed in the quotation `` `: ... ` ``. -/
def pp_print_qtype (ty : hol_type) : Fmt Unit := do
  Fmt.printString "`:"
  pp_print_type ty
  Fmt.printString "`"

/-- Reimplementation of pp_print_type/pp_print_qtype, using prettyprinter
    to properly color strings. -/
partial def pp_print_colored_type (ty : hol_type) : IO (Fmt Unit) := sot 0 ty
where
  color_print_str (s : String) : IO (Fmt Unit) := do
    return pp_print_colored_string (← printer_color_type.get) s
  -- ss is a list of printers whose format arg is not applied yet.
  soc (sep : String) (flag : Bool) (ss : List (Fmt Unit)) : IO (Fmt Unit) := do
    if ss.isEmpty then return (pure ())
    else
      let openP  ← if flag then color_print_str "(" else pure (pure ())
      let closeP ← if flag then color_print_str ")" else pure (pure ())
      let sepP   ← color_print_str sep
      -- interleave `sepP` between the element printers (right-associated fold)
      let tuple_printer :=
        (end_itlist (fun pp pp_next => do pp; sepP; pp_next) ss).toOption.getD (pure ())
      return do openP; tuple_printer; closeP
  sot (pr : Int) (ty : hol_type) : IO (Fmt Unit) := do
    match dest_vartype ty with
    | .ok v => pp_print_colored_tyvar v
    | .error _ =>
      match dest_finty ty with
      | .ok n => color_print_str (string_of_num n)
      | .error _ =>
        match dest_type ty with
        | .error _ => return (pure ())
        | .ok (con, args) =>
          match con, args with
          | con, []            => color_print_str con
          | "fun",  [ty1, ty2] => soc "->" (pr > 0) [← sot 1 ty1, ← sot 0 ty2]
          | "sum",  [ty1, ty2] => soc "+"  (pr > 2) [← sot 3 ty1, ← sot 2 ty2]
          | "prod", [ty1, ty2] => soc "#"  (pr > 4) [← sot 5 ty1, ← sot 4 ty2]
          | "cart", [ty1, ty2] => soc "^"  (pr > 6) [← sot 6 ty1, ← sot 7 ty2]
          | con, args          => do
              let inner ← soc "," true (← args.mapM (sot 0))
              let conP  ← color_print_str con
              return do inner; conP
/-- Print a type in color, enclosed in the quotation `` `: ... ` ``. -/
def pp_print_colored_qtype (ty : hol_type) : IO (Fmt Unit) := do
  let body ← pp_print_colored_type ty
  return do
    Fmt.printString "`:"
    body
    Fmt.printString "`"

/- Allow the installation of user printers. Must fail quickly if N/A. -/
/-- A user printer: a name paired with a term printer that may decline.
    IO-valued, as OCaml's `formatter -> term -> unit` printers read the
    global printer state (e.g. `pp_print_term` on a subterm). -/
abbrev UserPrinter := String × (term → IO (Except String (Fmt Unit)))
initialize user_printers : IO.Ref (List UserPrinter) ← IO.mkRef []
initialize user_color_printers : IO.Ref (List UserPrinter) ← IO.mkRef []

/-- Install a user printer at the front of the list. -/
def install_user_printer (pr : UserPrinter) : IO Unit :=
  user_printers.modify (pr :: ·)
/-- Install a user color printer at the front of the list. -/
def install_user_color_printer (pr : UserPrinter) : IO Unit :=
  user_color_printers.modify (pr :: ·)
/-- Delete the user printer named `s`. -/
def delete_user_printer (s : String) : IO Unit := do
  -- printer.ml:276: `snd(remove ..)` raises Failure "remove" when `s` is absent
  match remove (fun (s', _) => s == s') (← user_printers.get) with
  | .error _ => throw (IO.userError "remove")
  | .ok (_, ps') => user_printers.set ps'
/-- Delete the user color printer named `s`. -/
def delete_user_color_printer (s : String) : IO Unit := do
  -- printer.ml:278: `snd(remove ..)` raises Failure "remove" when `s` is absent
  match remove (fun (s', _) => s == s') (← user_color_printers.get) with
  | .error _ => throw (IO.userError "remove")
  | .ok (_, ps') => user_color_printers.set ps'
/-- `tryfind` over IO-valued user printers: the first success wins;
    "tryfind" if all decline. -/
private def tryUserPrinters (tm : term) :
    List UserPrinter → IO (Except String (Fmt Unit))
  | [] => return failwith "tryfind"
  | (_, pr) :: rest => do
    match ← pr tm with
    | .ok f => return .ok f
    | .error _ => tryUserPrinters tm rest
/-- Try each installed user printer on `tm`, returning the first success. -/
def try_user_printer (tm : term) : IO (Except String (Fmt Unit)) := do
  tryUserPrinters tm (← user_printers.get)
/-- Try each installed user color printer on `tm`, first success wins. -/
def try_user_color_printer (tm : term) : IO (Except String (Fmt Unit)) := do
  tryUserPrinters tm (← user_color_printers.get)

/- Printer for terms. -/

/- Char classifier projections (from `charClassifiers`). -/
private def issymb  : String → Bool := charClassifiers.2.2.2.1
def isalnum : String → Bool := charClassifiers.2.2.2.2.2.2

/- Reverse the interface map (constant → surface name) when printing, if the
   `reverse_interface_mapping` flag is set. -/
/-- Map a constant name back to its surface name via the interface, when
    `reverse_interface_mapping` is set; otherwise return `s0`. -/
def reverse_interface (s0 : String) (ty0 : hol_type) : IO String := do
  if !(← reverse_interface_mapping.get) then return s0
  else
    match find (fun (_, (s', ty)) => s' == s0 && can (type_match ty ty0) [])
               (← the_interface.get) with
    | .ok (s, _) => return s
    | .error _   => return s0

/- A PURE `reverse_interface` over a SNAPSHOT of the interface state.

   `reverse_interface` above is `IO` because it reads two refs, but `DEST_BINARY`
   must stay pure (it is passed to `splitlist`).  Taking the snapshot once per
   `print_infix_app` call is equivalent to OCaml's behaviour, which re-reads the
   refs during printing but cannot see them change mid-term. -/
private def reverse_interface_of
    (iface : List (String × (String × hol_type))) (revOn : Bool)
    (s0 : String) (ty0 : hol_type) : String :=
  if !revOn then s0
  else
    match find (fun (_, (s', ty)) => s' == s0 && can (type_match ty ty0) []) iface with
    | .ok (s, _) => s
    | .error _   => s0

/- `DEST_BINARY c tm`: split an application of binary operator `c`, matching
   either literal equality of the head or interface-equal constants.

   printer.ml 294-301 compares the SURFACE names
   (`reverse_interface(dest_const …)`), not the raw name and type.  The surface
   comparison is what merges one polymorphic constant across different type
   instances (so `a,(b,c)` prints as `a,b,c`) while still distinguishing e.g.
   `=` at `:bool` (surface `<=>`) from `=` at `:num` (surface `=`).  `revIface`
   is threaded in from a snapshot to keep this pure. -/
private def DEST_BINARY (revIface : String → hol_type → String)
    (c : term) (tm : term) : Except String (term × term) :=
  (do
    let (il, r) ← dest_comb tm
    let (i, l) ← dest_comb il
    let same ←
      if i == c then pure true
      else if is_const i && is_const c then do
        let (ni, tyi) ← dest_const i
        let (nc, tyc) ← dest_const c
        pure (revIface ni tyi == revIface nc tyc)
      else pure false
    if same then pure (l, r) else failwith "DEST_BINARY"
  ).mapError (fun _ => "DEST_BINARY")

/- Right-associative infix? -/
private def ARIGHT (getInfix : String → Except String (Int × String)) (s : String) : Bool :=
  match getInfix s with
  | .ok (_, "right") => true
  | _                => false

/- Is `n` a power of 10? (`n` a non-negative integer num.) -/
private partial def powerof10 (n : Rat) : Bool :=
  if n < num_1 then false
  else if n == num_1 then true
  else powerof10 (n / num_10)

private def bool_of_term (t : term) : Except String Bool :=
  match t with
  | .Const "T" _ => .ok true
  | .Const "F" _ => .ok false
  | _            => failwith "bool_of_term"

/-- OCaml's `String.escaped`: represent special characters by escape sequences
    following OCaml's lexical conventions (`\\`, `\"`, `\n`, `\t`, `\r`, `\b`,
    and any other non-printable character as a 3-digit decimal `\DDD`). -/
def string_escaped (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++
      (if c == '\\' then "\\\\"
       else if c == '"' then "\\\""
       else if c == '\n' then "\\n"
       else if c == '\t' then "\\t"
       else if c == '\r' then "\\r"
       else if c.toNat == 8 then "\\b"
       else if c.toNat < 32 || c.toNat > 126 then
         let n := c.toNat
         "\\" ++ (toString (n / 100)) ++ (toString (n / 10 % 10)) ++ (toString (n % 10))
       else String.singleton c)) ""

/- Decode an 8-bit ASCII character term to its code. -/
private def code_of_term (t : term) : Except String Nat := do
  let (f, tms) := strip_comb t
  if !(is_const f && (← dest_const f).1 == "ASCII") || tms.length != 8 then
    failwith "code_of_term"
  else
    let bs ← (tms.reverse).mapM bool_of_term
    .ok (itlist (fun b f => if b then 1 + 2 * f else 2 * f) bs 0)

/- Destructors for pattern-match clauses. -/
private def dest_clause (tm : term) : Except String (List term) := do
  let pbod := (strip_exists (← body (← body tm))).2
  let (s, args) := strip_comb pbod
  if name_of s == "_UNGUARDED_PATTERN" && args.length == 2 then
    return [← rand (← rator (← hd args)), ← rand (← rator (← hd (← tl args)))]
  else if name_of s == "_GUARDED_PATTERN" && args.length == 3 then
    return [← rand (← rator (← hd args)), ← hd (← tl args),
            ← rand (← rator (← hd (← tl (← tl args))))]
  else failwith "dest_clause"

private partial def dest_clauses (tm : term) : Except String (List (List term)) := do
  let (s, args) := strip_comb tm
  if name_of s == "_SEQPATTERN" && args.length == 2 then
    return (← dest_clause (← hd args)) :: (← dest_clauses (← hd (← tl args)))
  else return [← dest_clause tm]

/- Split a `COND` into ((cond, then), else). -/
private def pdest_cond (tm : term) : Except String ((term × term) × term) :=
  match tm with
  | .Comb (.Comb (.Comb (.Const "COND" _) i) t) e => .ok ((i, t), e)
  | _ => failwith "pdest_cond"

/- Sequence a list of formatter actions into one. -/
private def seqFmt (ps : List (Fmt Unit)) : Fmt Unit := ps.foldl (· *> ·) (pure ())

/- The term printer, parameterized by `use_color`. Produces a deferred
   `Fmt Unit`; the `IO` layer threads reads of the color / interface / parser
   flag refs. Handlers that "decline" (OCaml `fail()`) return `.error`, so
   `print_term` can fall through to the next. -/
/-- Print a term (optionally with color), sugaring binders, sets, lists,
    conditionals, prefixes, infixes and binders with precedence-based
    parenthesisation. -/
partial def print_colored_term (use_color : Bool) (tm0 : term) : IO (Fmt Unit) :=
  print_term 0 tm0
where
  color_switch (cpp : String → IO (Fmt Unit)) (s : String) : IO (Fmt Unit) :=
    if use_color then cpp s else pure (Fmt.printString s)

  try_user_printers (tm : term) : IO (Except String (Fmt Unit)) :=
    if use_color then do
      match ← try_user_color_printer tm with
      | .ok f => return .ok f
      | .error _ => try_user_printer tm
    else try_user_printer tm

  print_numeral (tm : term) : IO (Except String (Fmt Unit)) := do
    match dest_numeral tm with
    | .ok n => return .ok (Fmt.printString (string_of_num n))
    | .error e => return .error e

  print_term (prec : Int) (tm : term) : IO (Fmt Unit) := do
    -- ----- Phase A: shape-based handlers (run before strip_comb). Each
    --    prints on success or raises Failure to fall through. -----
    match ← try_user_printers tm with
    | .ok f => return f
    | .error _ =>
    match ← print_numeral tm with
    | .ok f => return f
    | .error _ =>
    match ← print_string_or_list tm with
    | .ok f => return f
    | .error _ =>
    if is_gabs tm then print_binder prec tm else
    let (hop, args) := strip_comb tm
    let s ← reverse_interface (name_of hop) (type_of hop)
    -- ----- Phase B: name-keyed handlers. -----
    match ← firstOk [
        print_empty_set s tm args,
        print_universal_set s tm args,
        print_finite_set s tm,
        print_set_comprehension s tm,
        print_let_term s prec tm,
        print_decimal s args,
        print_match s prec args,
        print_function s prec args,
        print_cond s prec tm args,
        -- ----- Phase C: parser-status-based handlers. -----
        print_prefix_app s prec args,
        print_binder_app s prec tm args,
        print_infix_app s prec tm hop args ] with
    | .ok f => return f
    | .error _ =>
      -- ----- Phase D: leaf or generic application. -----
      if (is_const hop || is_var hop) && args.isEmpty then print_atom hop s
      else print_generic_app prec tm

  -- Try a list of handlers in order, returning the first `.ok`.
  firstOk : List (IO (Except String (Fmt Unit))) → IO (Except String (Fmt Unit))
    | [] => return failwith "firstOk"
    | h :: t => do match ← h with
                   | .ok f => return .ok f
                   | .error _ => firstOk t

  print_string_or_list (tm : term) : IO (Except String (Fmt Unit)) := do
    match dest_list tm with
    | .error e => return .error e
    | .ok tms =>
      -- string of chars?
      let asString : Except String String := do
        let (_, tyargs) ← dest_type (type_of tm)
        let (elCon, _) ← dest_type (← hd tyargs)
        if elCon != "char" then failwith "not a string"
        else
          let ccs ← tms.mapM (fun t => do
            let code ← code_of_term t
            return String.singleton (Char.ofNat code))
          return "\"" ++ string_escaped (String.intercalate "" ccs) ++ "\""
      match asString with
      | .ok s => return .ok (Fmt.printString s)
      | .error _ =>
        let body ← print_term_sequence true ";" 0 tms
        return .ok (do
          Fmt.openBox 0; Fmt.printString "["
          Fmt.openBox 0; body
          Fmt.closeBox; Fmt.printString "]"
          Fmt.closeBox)

  print_empty_set (s : String) (tm : term) (args : List term) :
      IO (Except String (Fmt Unit)) :=
    if s == "EMPTY" && is_const tm && args.isEmpty then
      return .ok (Fmt.printString "{}")
    else return failwith "print_empty_set"

  print_universal_set (s : String) (tm : term) (args : List term) :
      IO (Except String (Fmt Unit)) := do
    if s == "UNIV" && (← typify_universal_set.get) && is_const tm && args.isEmpty then
      match dest_fun_ty (type_of tm) with
      | .error e => return .error e
      | .ok (ty, _) =>
        let tp ← if use_color then pp_print_colored_type ty else pure (pp_print_type ty)
        return .ok (do Fmt.printString "(:"; tp; Fmt.printString ")")
    else return failwith "print_universal_set"

  print_finite_set (s : String) (tm : term) : IO (Except String (Fmt Unit)) := do
    if s != "INSERT" then return failwith "print_finite_set"
    else
      let (mems, oth) := splitlist (dest_binary "INSERT") tm
      if is_const oth && (dest_const oth).toOption.map Prod.fst == some "EMPTY" then
        let body ← print_term_sequence true "," 14 mems
        return .ok (do
          Fmt.openBox 0; Fmt.printString "{"; Fmt.openBox 0
          body; Fmt.closeBox; Fmt.printString "}"; Fmt.closeBox)
      else return failwith "print_finite_set"

  print_set_comprehension (s : String) (tm : term) : IO (Except String (Fmt Unit)) := do
    if s != "GSPEC" then return failwith "print_set_comprehension"
    else
      match (do
          let (evs, bod) := strip_exists (← body (← rand tm))
          let (bod1, fabs) ← dest_comb bod
          let (bod2, babs) ← dest_comb bod1
          let c ← rator bod2
          if (← dest_const c).1 != "SETSPEC" then failwith "not SETSPEC"
          else .ok (evs, fabs, babs) : Except String _) with
      | .error e => return .error e
      | .ok (evs, fabs, babs) =>
        let fabsP ← print_term 0 fabs
        let babsP ← print_term 0 babs
        let fvs := frees fabs
        let bvs := frees babs
        let ambig := !(← print_unambiguous_comprehensions.get) &&
          set_eq evs (if fvs.length <= 1 || bvs.isEmpty then fvs else intersect fvs bvs)
        let midP ←
          if ambig then pure (pure ())
          else do
            let evsP ← print_term_sequence false "," 14 evs
            pure (do evsP; Fmt.printString " | ")
        return .ok (do
          Fmt.printString "{"; fabsP; Fmt.printString " | "; midP
          babsP; Fmt.printString "}")

  print_let_term (s : String) (prec : Int) (tm : term) : IO (Except String (Fmt Unit)) := do
    if s != "LET" then return failwith "print_let_term"
    else
      match dest_let tm with
      | .error e => return .error e
      | .ok (eqs, bod) =>
        match eqs with
        | [] => return failwith "print_let_term"
        | (v0, t0) :: rest =>
          let letKw ← color_switch pp_print_colored_resword "let "
          let firstEq ← print_term 0 (safe_mk_eq v0 t0)
          let restPs ← rest.mapM (fun (v, t) => do
            let andKw ← color_switch pp_print_colored_resword "and "
            let eqP ← print_term 0 (safe_mk_eq v t)
            pure (do Fmt.printBreak 1 0; andKw; eqP))
          let inKw ← color_switch pp_print_colored_resword " in"
          let bodP ← print_term 0 bod
          return .ok (do
            (if prec == 0 then Fmt.openHvBox 0
             else do Fmt.openHvBox 1; Fmt.printString "(")
            letKw; firstEq; seqFmt restPs; inKw; Fmt.printBreak 1 0; bodP
            (if prec == 0 then pure () else Fmt.printString ")")
            Fmt.closeBox)

  print_decimal (s : String) (args : List term) : IO (Except String (Fmt Unit)) := do
    if s != "DECIMAL" then return failwith "print_decimal"
    else
      match (do
          let n_num ← dest_numeral (← hd args)
          let n_den ← dest_numeral (← hd (← tl args))
          if !(powerof10 n_den) then failwith "not power of 10"
          else
            let s_num := string_of_num (quo_num n_num n_den)
            let tailStr := explode (string_of_num (n_den + (mod_num n_num n_den)))
            let s_den := implode (← tl tailStr)
            .ok ("#" ++ s_num ++ (if n_den == num_1 then "" else ".") ++ s_den)
            : Except String String) with
      | .ok str => return .ok (Fmt.printString str)
      | .error e => return .error e

  print_match (s : String) (prec : Int) (args : List term) :
      IO (Except String (Fmt Unit)) := do
    if s != "_MATCH" || args.length != 2 then return failwith "print_match"
    else
      match (do dest_clauses (← hd (← tl args))) with
      | .error e => return .error e
      | .ok cls =>
        let scrut ← print_term 0 ((hd args).toOption.getD tm0)
        let matchKw ← color_switch pp_print_colored_resword "match "
        let withKw ← color_switch pp_print_colored_resword " with"
        let clsP ← print_clauses cls
        return .ok (do
          (if prec == 0 then pure () else Fmt.printString "(")
          Fmt.openHvBox 0; matchKw; scrut; withKw; Fmt.printBreak 1 2; clsP; Fmt.closeBox
          (if prec == 0 then pure () else Fmt.printString ")"))

  print_function (s : String) (prec : Int) (args : List term) :
      IO (Except String (Fmt Unit)) := do
    if s != "_FUNCTION" || args.length != 1 then return failwith "print_function"
    else
      match (do dest_clauses (← hd args)) with
      | .error e => return .error e
      | .ok cls =>
        let funKw ← color_switch pp_print_colored_resword "function"
        let clsP ← print_clauses cls
        return .ok (do
          (if prec == 0 then pure () else Fmt.printString "(")
          Fmt.openHvBox 0; funKw; Fmt.printBreak 1 2; clsP; Fmt.closeBox
          (if prec == 0 then pure () else Fmt.printString ")"))

  print_cond (s : String) (prec : Int) (tm : term) (args : List term) :
      IO (Except String (Fmt Unit)) := do
    if s != "COND" || args.length != 3 then return failwith "print_cond"
    else
      let (ccls, ecl) := splitlist pdest_cond tm
      let mkKw := fun kw => color_switch pp_print_colored_resword kw
      if ccls.length <= 4 then
        let a0 ← print_term 0 (args[0]?.getD tm0)
        let a1 ← print_term 0 (args[1]?.getD tm0)
        let a2 ← print_term 0 (args[2]?.getD tm0)
        let ifKw ← mkKw "if "; let thenKw ← mkKw " then "; let elseKw ← mkKw " else "
        return .ok (do
          (if prec == 0 then pure () else Fmt.printString "(")
          Fmt.openHvBox (-1)
          ifKw; a0; Fmt.printBreak 0 0; thenKw; a1; Fmt.printBreak 0 0; elseKw; a2
          Fmt.closeBox
          (if prec == 0 then pure () else Fmt.printString ")"))
      else
        match ccls with
        | [] => return failwith "print_cond"
        | (i0, t0) :: crest =>
          let ifKw ← mkKw "if "; let thenKw ← mkKw " then "
          let i0P ← print_term 0 i0
          let t0P ← print_term 0 t0
          let restPs ← crest.mapM (fun (i, t) => do
            let eifKw ← mkKw " else if "; let ethenKw ← mkKw " then "
            let iP ← print_term 0 i; let tP ← print_term 0 t
            pure (do eifKw; iP; ethenKw; tP; Fmt.printBreak 0 0))
          let elseKw ← mkKw " else "
          let eclP ← print_term 0 ecl
          return .ok (do
            (if prec == 0 then pure () else Fmt.printString "(")
            Fmt.openHvBox (-1)
            ifKw; i0P; thenKw; t0P; Fmt.printBreak 0 0; seqFmt restPs; elseKw; eclP
            Fmt.closeBox
            (if prec == 0 then pure () else Fmt.printString ")"))

  print_prefix_app (s : String) (prec : Int) (args : List term) :
      IO (Except String (Fmt Unit)) := do
    if !((← is_prefix s) && args.length == 1) then return failwith "print_prefix_app"
    else
      let arg0 := args[0]?.getD tm0
      let pfx ← color_switch pp_print_colored_prefix s
      -- decide whether to insert a separating space
      let spaceCheck : IO Bool := do
        if isalnum s then return true
        else if s == "--" then
          match dest_comb arg0 with
          | .ok (l, _) => do
              let rn ← reverse_interface (name_of l) (type_of l)
              let isNumConv := (dest_const l).toOption.map Prod.fst
              return rn == "--" ||
                (isNumConv == some "real_of_num" || isNumConv == some "int_of_num")
          | .error _ => return false
        else if s == "~" then return is_neg arg0
        else return false
      let needSpace ← spaceCheck
      let argP ← print_term 999 arg0
      return .ok (do
        (if prec == 1000 then Fmt.printString "(" else pure ())
        pfx; (if needSpace then Fmt.printString " " else pure ()); argP
        (if prec == 1000 then Fmt.printString ")" else pure ()))

  print_binder_app (s : String) (prec : Int) (tm : term) (args : List term) :
      IO (Except String (Fmt Unit)) := do
    if !((← parses_as_binder s) && args.length == 1 && is_gabs (args[0]?.getD tm0))
    then return failwith "print_binder_app"
    else return .ok (← print_binder prec tm)

  print_infix_app (s : String) (prec : Int) (tm : term) (hop : term) (args : List term) :
      IO (Except String (Fmt Unit)) := do
    let infixStatus ← get_infix_status s
    if args.length != 2 || !(infixStatus.toOption.isSome) then
      return failwith "print_infix_app"
    else
      -- Snapshot the interface state once, so `DEST_BINARY` can compare SURFACE
      -- names purely (printer.ml 294-301).
      let iface ← the_interface.get
      let revOn ← reverse_interface_mapping.get
      let revIface := reverse_interface_of iface revOn
      let bargs :=
        if ARIGHT (fun _ => infixStatus) s then   -- status already resolved for s
          let (tms, tmt) := splitlist (DEST_BINARY revIface hop) tm
          tms ++ [tmt]
        else
          let (tmt, tms) := rev_splitlist (DEST_BINARY revIface hop) tm
          tmt :: tms
      let newprec := (infixStatus.toOption.map Prod.fst).getD 0
      let unspaced ← unspaced_binops.get
      let prebroken ← prebroken_binops.get
      match bargs with
      | [] => return failwith "print_infix_app"
      | b0 :: brest =>
        let b0P ← print_term newprec b0
        let restPs ← brest.mapM (fun x => do
          let opP ← color_switch pp_print_colored_infix s
          let xP ← print_term newprec x
          pure (do
            (if mem s unspaced then pure ()
             else if mem s prebroken then Fmt.printBreak 1 0
             else Fmt.printString " ")
            opP
            (if mem s unspaced then Fmt.printBreak 0 0
             else if mem s prebroken then Fmt.printString " "
             else Fmt.printBreak 1 0)
            xP))
        return .ok (do
          (if newprec <= prec then do Fmt.openHvBox 1; Fmt.printString "("
           else Fmt.openHvBox 0)
          b0P; seqFmt restPs
          (if newprec <= prec then Fmt.printString ")" else pure ())
          Fmt.closeBox)

  print_atom (hop : term) (s : String) : IO (Fmt Unit) := do
    let isBinder ← parses_as_binder s
    let isPfx ← is_prefix s
    let isInfix := (← get_infix_status s).toOption.isSome
    let s' := if isBinder || isInfix || isPfx then "(" ++ s ++ ")" else s
    let rec hasInvented (ty : hol_type) : Bool :=
      match dest_vartype ty with
      | .ok v => (v.toList.head?.map (· == '?')).getD false
      | .error _ => ((dest_type ty).toOption.map (fun (_, args) => args.any hasInvented)).getD false
    let ptos ← print_types_of_subterms.get
    if ptos == 2 || (ptos == 1 && hasInvented (type_of hop)) then
      let nameP ← if is_const hop then color_switch pp_print_colored_const s'
                  else pure (Fmt.printString s')
      let tyP ← if use_color then pp_print_colored_type (type_of hop)
                else pure (pp_print_type (type_of hop))
      -- If s' ends in a symbolic character, juxtaposing ":" would lex as a
      -- single identifier (e.g. "&:" is one Ident), so insert a space.
      let needSpace := match s'.toList.getLast? with
                       | some c => issymb (String.singleton c)
                       | none   => false
      return (do
        Fmt.openBox 0; Fmt.printString "("; nameP
        (if needSpace then Fmt.printString " " else pure ())
        Fmt.printString ":"; tyP; Fmt.printString ")"; Fmt.closeBox)
    else
      if is_const hop then color_switch pp_print_colored_const s'
      else pure (Fmt.printString s')

  print_generic_app (prec : Int) (tm : term) : IO (Fmt Unit) := do
    -- Print `l r` by recursing on the function `l` (so an infix/binder head is
    -- re-sugared, e.g. `((o) f g) x` → `(f o g) x`) and the argument `r`.
    -- A literal space (not a breakable one) keeps an application spine on one
    -- line, avoiding the cascading-indent staircase.
    match dest_comb tm with
    | .error _ => return (pure ())
    | .ok (l, r) =>
      let lP ← print_term 999 l
      let rP ← print_term 1000 r
      let skipSpace := ((dest_const l).toOption.map Prod.fst).elim false
                        (fun n => n == "real_of_num" || n == "int_of_num")
      return (do
        Fmt.openHvBox 0
        (if prec == 1000 then Fmt.printString "(" else pure ())
        lP; (if skipSpace then pure () else Fmt.printString " "); rP
        (if prec == 1000 then Fmt.printString ")" else pure ())
        Fmt.closeBox)

  print_term_sequence (break_ : Bool) (sep : String) (prec : Int) (tms : List term) :
      IO (Fmt Unit) := do
    match tms with
    | [] => return (pure ())
    | t :: ttms =>
      let tP ← print_term prec t
      if ttms.isEmpty then return tP
      else
        let restP ← print_term_sequence break_ sep prec ttms
        return (do
          tP; Fmt.printString sep
          (if break_ then Fmt.printSpace else pure ()); restP)

  print_binder (prec : Int) (tm : term) : IO (Fmt Unit) := do
    let absf := is_gabs tm
    let (s, s') ←
      if absf then pure ("\\", "\\")
      else do
        let bt := (rator tm).toOption.getD tm0
        let sn := name_of bt
        pure (sn, ← reverse_interface sn (type_of bt))
    let rec collectvs (tm : term) : List (Bool × term) × term :=
      if absf then
        match dest_abs tm with
        | .ok (v, t) => let (vs, bod) := collectvs t; ((false, v) :: vs, bod)
        | .error _ =>
          match dest_gabs tm with
          | .ok (v, t) => let (vs, bod) := collectvs t; ((true, v) :: vs, bod)
          | .error _ => ([], tm)
      else if is_comb tm && ((rator tm).toOption.map name_of == some s) then
        match (rand tm).toOption with
        | some rtm =>
          match dest_abs rtm with
          | .ok (v, t) => let (vs, bod) := collectvs t; ((false, v) :: vs, bod)
          | .error _ =>
            match dest_gabs rtm with
            | .ok (v, t) => let (vs, bod) := collectvs t; ((true, v) :: vs, bod)
            | .error _ => ([], tm)
        | none => ([], tm)
      else ([], tm)
    let (vs, bod) := collectvs tm
    let binderKw ← color_switch pp_print_colored_binder s'
    match vs.reverse with
    | [] => return (pure ())   -- no bound vars (shouldn't happen)
    | lastV :: initRev =>
      let initVs := initRev.reverse
      let initPs ← initVs.mapM (fun (b, x) => do
        let xP ← print_term 0 x
        pure (do
          (if b then Fmt.printString "(" else pure ()); xP
          (if b then Fmt.printString ")" else pure ()); Fmt.printString " "))
      let (lb, lx) := lastV
      let lastP ← print_term 0 lx
      let bodP ← print_term 0 bod
      return (do
        (if prec == 0 then Fmt.openHvBox 4 else do Fmt.openHvBox 5; Fmt.printString "(")
        binderKw
        (if isalnum s' then Fmt.printString " " else pure ())
        seqFmt initPs
        (if lb then Fmt.printString "(" else pure ()); lastP
        (if lb then Fmt.printString ")" else pure ())
        Fmt.printString "."; Fmt.printSpace; bodP
        (if prec == 0 then pure () else Fmt.printString ")")
        Fmt.closeBox)

  print_clauses (cls : List (List term)) : IO (Fmt Unit) := do
    match cls with
    | [c] => print_clause c
    | c :: cs =>
      let cP ← print_clause c
      let csP ← print_clauses cs
      return (do cP; Fmt.printBreak 1 0; Fmt.printString "| "; csP)
    | [] => return (pure ())

  print_clause (cl : List term) : IO (Fmt Unit) := do
    match cl with
    | [p, g, r] =>
      let pP ← print_term 1 p; let gP ← print_term 1 g; let rP ← print_term 1 r
      return (do pP; Fmt.printString " when "; gP; Fmt.printString " -> "; rP)
    | [p, r] =>
      let pP ← print_term 1 p; let rP ← print_term 1 r
      return (do pP; Fmt.printString " -> "; rP)
    | _ => return (pure ())

/- Expose plain and colored term printers. -/
/-- Print a term without color. -/
def pp_print_term : term → IO (Fmt Unit) := print_colored_term false
/-- Print a term with ANSI colors. -/
def pp_print_colored_term : term → IO (Fmt Unit) := print_colored_term true

/- ---------------------------------------------------------------------- -/
/- Print term with quotes.                                                -/
/- ---------------------------------------------------------------------- -/

private def qtermFn (use_color : Bool) (tm : term) : IO (Fmt Unit) := do
  let body ← if use_color then pp_print_colored_term tm else pp_print_term tm
  return (do Fmt.printString "`"; body; Fmt.printString "`")

/-- Print a term enclosed in backquotes `` `...` ``. -/
def pp_print_qterm : term → IO (Fmt Unit) := qtermFn false
/-- Print a term in color, enclosed in backquotes `` `...` ``. -/
def pp_print_colored_qterm : term → IO (Fmt Unit) := qtermFn true

/- ---------------------------------------------------------------------- -/
/- Printer for theorems.                                                  -/
/- ---------------------------------------------------------------------- -/

private def thmFn (use_color : Bool) (th : thm) : IO (Fmt Unit) := do
  let printTm : term → IO (Fmt Unit) :=
    if use_color then pp_print_colored_term else pp_print_term
  let (asl, tm) := dest_thm th
  let aslP ←
    if !asl.isEmpty then do
      if ← print_all_thm.get then
        match asl with
        | [] => pure (pure ())
        | h :: t =>
          let hP ← printTm h
          let tPs ← t.mapM (fun x => do
            let xP ← printTm x
            pure (do Fmt.printString ","; Fmt.printSpace; xP))
          pure (do hP; seqFmt tPs; Fmt.printSpace)
      else pure (do Fmt.printString "..."; Fmt.printSpace)
    else pure (pure ())
  let tmP ← printTm tm
  return (do
    aslP
    Fmt.openHBox    -- pp_open_hbox
    Fmt.printString "|- "; tmP
    Fmt.closeBox)

/-- Print a theorem as `asl |- concl`, honoring `print_all_thm`. -/
def pp_print_thm : thm → IO (Fmt Unit) := thmFn false
/-- Print a theorem in color as `asl |- concl`. -/
def pp_print_colored_thm : thm → IO (Fmt Unit) := thmFn true

/- ---------------------------------------------------------------------- -/
/- Conversions to string.                                                 -/
/- ---------------------------------------------------------------------- -/

/- Output margin (HOL Light's default is 78). -/
initialize theMargin : IO.Ref Nat ← IO.mkRef 78
/-- Get the current output margin. -/
def get_margin : IO Nat := theMargin.get
/-- Set the output margin to `n`. -/
def set_margin (n : Nat) : IO Unit := theMargin.set n

/- Render a pure formatter action to a string at the current margin. -/
/-- Render a pure formatter for `x` to a string at the current margin. -/
def print_to_string (printer : α → Fmt Unit) (x : α) : IO String := do
  return Fmt.run (← get_margin) (printer x)

/- Render an effectful (IO) formatter action to a string. -/
/-- Render an effectful (IO) formatter for `x` to a string. -/
def print_to_string_io (printer : α → IO (Fmt Unit)) (x : α) : IO String := do
  let act ← printer x
  return Fmt.run (← get_margin) act

/-- Render a type to a string. -/
def string_of_type (ty : hol_type) : IO String := print_to_string pp_print_type ty
/-- Render a term to a string. -/
def string_of_term (tm : term) : IO String := print_to_string_io pp_print_term tm
/-- Render a theorem to a string. -/
def string_of_thm  (th : thm)  : IO String := print_to_string_io pp_print_thm th

/- ---------------------------------------------------------------------- -/
/- Print on standard output.                                              -/
/- ---------------------------------------------------------------------- -/
/- The OCaml versions print to `std_formatter`.  Here a printer renders to a
   string, so these render at the current margin and write the result to
   stdout. -/

/-- Print a type to standard output. -/
def print_type (ty : hol_type) : IO Unit := do IO.print (← string_of_type ty)
/-- Print a quoted type `` `:...` `` to standard output. -/
def print_qtype (ty : hol_type) : IO Unit := do
  IO.print (Fmt.runStd (← get_margin) (pp_print_qtype ty))
/-- Print a term to standard output. -/
def print_term (tm : term) : IO Unit := do IO.print (← string_of_term tm)
/-- Print a quoted term `` `...` `` to standard output. -/
def print_qterm (tm : term) : IO Unit := do
  IO.print (Fmt.runStd (← get_margin) (← pp_print_qterm tm))
/-- Print a theorem to standard output. -/
def print_thm (th : thm) : IO Unit := do IO.print (← string_of_thm th)
