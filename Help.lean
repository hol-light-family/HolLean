/- File: Help.lean
Simple online help system, based on old HOL88 one.
Original       John Harrison, University of Cambridge Computer Laboratory
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Lean4 translation by Chris Walton 2026

Usage, as in HOL Light (`help "REAL_LET_IMP";;`):

    #eval help("REAL_LET_IMP")        -- or: #eval help "REAL_LET_IMP"

The entries are the `.hlp` files of HOL Light's `Help` directory, shown with
the HOL Light (OCaml) syntax they were written in.

Deviations from help.ml:
- help.ml pipes each file through `sed -f doc-to-help.sed`; `docToHelp` below
  performs the same edits, command for command, so no external `sed` or script
  file is needed.
- `omit` is a Lean keyword, so the OCaml `omit` is written `«omit»`.
- `search` reads `theorems`, which `Database.lean` fills on first use rather
  than at load (filling it forces every theorem of the library). -/

import HolCore

open HolCore.Kernel HolCore.Lib HolCore.Basics

namespace Help

/- ---------------------------------------------------------------------- -/
/- HOL Light's directory (hol_loader.ml 13-14, 39-46, 93-97).             -/
/- ---------------------------------------------------------------------- -/

/-- `hol_dir`: `$HOLLIGHT_DIR`, or else the current directory. -/
initialize hol_dir : IO.Ref String ← do
  match ← IO.getEnv "HOLLIGHT_DIR" with
  | some d => IO.mkRef d
  | none => IO.mkRef (← IO.currentDir).toString

/-- Paths map initial `$/` to `!hol_dir`; `$$` gives an actual `$`. -/
def hol_expand_directory (s : String) : IO String := do
  let d ← hol_dir.get
  if s == "$" || s == "$/" then return d
  else if s == "$$" then return "$"
  else if s.length <= 2 then return s
  else if s.startsWith "$$" then return (s.drop 1).toString
  else if s.startsWith "$/" then return (System.FilePath.mk d / (s.drop 2).toString).toString
  else return s

/-- `file_on_path p s`: the first directory on path `p` containing `s`. -/
def file_on_path (p : List String) (s : String) : IO (Except String String) := do
  if (System.FilePath.mk s).isAbsolute then return .ok s
  for d0 in p do
    let d ← hol_expand_directory d0
    if ← (System.FilePath.mk d / s).pathExists then
      let cwd := (← IO.currentDir).toString
      let d' := if d == "." then cwd else d
      return .ok (System.FilePath.mk d' / s).toString
  return .error "Not_found"

/- ---------------------------------------------------------------------- -/
/- Help system.                                                           -/
/- ---------------------------------------------------------------------- -/

initialize help_path : IO.Ref (List String) ← IO.mkRef ["$/Help"]

/-- sed `s/pat/rep/` without `g`: replace the first occurrence only. -/
private def replaceFirst (s pat rep : String) : String :=
  match s.splitOn pat with
  | pre :: rest@(_ :: _) => pre ++ rep ++ pat.intercalate rest
  | _ => s

/-- sed `s/{\\em \([a-z]*\)}/*\1*/`: the first `{\em w}` with `w` all
    lower-case letters (possibly empty) becomes `*w*`. -/
private def emToStars (s : String) : String := Id.run do
  let pat := "{\\em "
  let parts := s.splitOn pat
  match parts with
  | [] | [_] => return s
  | pre :: rest =>
    -- try each occurrence in order until one matches the full pattern
    let mut acc := pre
    let mut i := 0
    for part in rest do
      if i == 0 then
        let word := part.takeWhile (fun c => 'a' ≤ c && c ≤ 'z')
        let after := (part.drop word.toString.length).toString
        if after.startsWith "}" then
          acc := acc ++ "*" ++ word.toString ++ "*" ++ (after.drop 1).toString
          i := 1
          continue
      acc := acc ++ pat ++ part
    return acc

/-- `doc-to-help.sed`: "Script to convert .hlp file into a presentable ASCII
    form.  This is essentially a copy of an old file from the HOL88
    distribution."  Each step below is one sed command, in the script's order;
    a line deleted by `d` produces no output. -/
def docToHelp (src : String) : String := Id.run do
  let spaces (s : String) : Bool := s.all (· == ' ')
  let bare (s k : String) : Bool := s.startsWith k && spaces (s.drop k.length).toString
  let mut out : Array String := #[]
  let mut inKeywords := false        -- /^\\KEYWORDS/,/^ *$/d
  let mut inLibrary := false         -- /^\\LIBRARY/,/^ *$/d
  let lines := src.splitOn "\n"
  -- A final newline does not start another line.
  let lines := if src.endsWith "\n" then lines.dropLast else lines
  for l0 in lines do
    if inKeywords then
      if spaces l0 then inKeywords := false
      continue
    if l0.startsWith "\\KEYWORDS" then
      inKeywords := true
      continue
    if inLibrary then
      if spaces l0 then inLibrary := false
      continue
    if l0.startsWith "\\LIBRARY" then
      inLibrary := true
      continue
    let mut l := l0
    l := l.replace "\\#" "#"
    l := l.replace "\\char'136" "^"
    l := l.replace "\\char'056" "."
    l := l.replace "\\char'100" "@"
    l := l.replace "{{" "<<<<<<"
    l := l.replace "}}" ">>>>>>"
    l := l.replace "{" ""
    l := l.replace "}" ""
    -- s/^{\\verb%[ ]*$/.../ and s/^%}[ ]*$/.../ can no longer match: every
    -- brace has just been removed.
    if l.startsWith "\\DOC" then continue
    if l.startsWith "\\TYPE" then
      l := ((l.drop "\\TYPE".length).dropWhile (· == ' ')).toString
    if l.startsWith "\\BLTYPE" || l.startsWith "\\ELTYPE" then continue
    if l.startsWith "\\noindent " then l := (l.drop "\\noindent ".length).toString
    let mut after : Array String := #[]
    for (key, title) in [("\\SYNOPSIS", "SYNOPSIS"), ("\\CATEGORIES", "CATEGORIES"),
        ("\\DESCRIBE", "DESCRIPTION"), ("\\FAILURE", "FAILURE CONDITIONS"),
        ("\\EXAMPLE", "EXAMPLES"), ("\\USES", "USES"), ("\\COMMENTS", "COMMENTS")] do
      if (l.splitOn key).length ≥ 2 then after := after.push ""    -- a\ (blank line)
      if bare l key then l := title
    if bare l "\\SEEALSO" then l := "SEE ALSO"
    if (l.splitOn "\\ENDDOC").length ≥ 2 then
      out := out ++ after
      continue
    l := l.replace "<<<<<<" "{"
    l := l.replace ">>>>>>" "}"
    -- These four run AFTER `{{`/`}}` are restored as braces, so they see them.
    -- Without the `g` flag each replaces only the first match on the line.
    l := replaceFirst l "\\begin{itemize}" "---------"
    l := replaceFirst l "\\end{itemize}" "---------"
    l := replaceFirst l "\\item" " *"
    l := emToStars l                       -- s/{\\em \([a-z]*\)}/*\1*/
    out := out.push l
    out := out ++ after
  return String.join (out.toList.map (· ++ "\n"))

/-- Edit distance between two strings (help.ml's `edit_distance`). -/
def edit_distance (s1 s2 : String) : Nat := Id.run do
  let a := s1.toList.toArray; let b := s2.toList.toArray
  let l1 := a.size; let l2 := b.size
  let mut m : Array (Array Nat) := Array.replicate (l1 + 1) (Array.replicate (l2 + 1) 0)
  for i in [1:l1+1] do m := m.set! i (m[i]!.set! 0 i)
  for j in [1:l2+1] do m := m.set! 0 (m[0]!.set! j j)
  for i in [1:l1+1] do
    for j in [1:l2+1] do
      let cost := if a[i-1]! == b[j-1]! then 0 else 1
      let v := min (min m[i-1]![j]! m[i]![j-1]! + 1) (m[i-1]![j-1]! + cost)
      m := m.set! i (m[i]!.set! j v)
  return m[l1]![l2]!

/-- The text `help s` prints: the help entry for `s`, or the three closest
    names. -/
def helpText (s : String) : IO String := do
  let funny_filenames : List (String × String) :=
   [("++", ".joinparsers"),
    ("|||", ".orparser"),
    (">>", ".pipeparser"),
    ("|=>", ".singlefun"),
    ("--", ".upto"),
    ("|->", ".valmod"),
    ("insert'", "insert_prime"),
    ("mem'", "mem_prime"),
    ("subtract'", "subtract_prime"),
    ("union'", "union_prime"),
    ("unions'", "unions_prime"),
    ("ALPHA", "ALPHA_UPPERCASE"),
    ("CHOOSE", "CHOOSE_UPPERCASE"),
    ("CONJUNCTS", "CONJUNCTS_UPPERCASE"),
    ("EXISTS", "EXISTS_UPPERCASE"),
    ("HYP", "HYP_UPPERCASE"),
    ("INSTANTIATE", "INSTANTIATE_UPPERCASE"),
    ("INST", "INST_UPPERCASE"),
    ("MK_BINOP", "MK_BINOP_UPPERCASE"),
    ("MK_COMB", "MK_COMB_UPPERCASE"),
    ("MK_CONJ", "MK_CONJ_UPPERCASE"),
    ("MK_DISJ", "MK_DISJ_UPPERCASE"),
    ("MK_EXISTS", "MK_EXISTS_UPPERCASE"),
    ("MK_FORALL", "MK_FORALL_UPPERCASE"),
    ("REPEAT", "REPEAT_UPPERCASE")]
  let true_path ← (← help_path.get).mapM hol_expand_directory
  let mut raw_listing : List String := []
  for a in true_path.reverse do            -- itlist: last directory first
    let entries ← (System.FilePath.mk a).readDir
    raw_listing := (entries.toList.map (fun e => (e.fileName.dropEnd 4).copy)) ++ raw_listing
  let mod_listing := funny_filenames.map Prod.fst ++
    subtract raw_listing (funny_filenames.map Prod.snd)
  let closeness (s s' : String) : String × Float :=
    (s', 2.0 * (edit_distance s.toUpper s'.toUpper).toFloat /
         (s.length + s'.length).toFloat)
  let guess (s : String) : List String :=
    let guesses := mergesort (fun x y => x.2 < y.2) (mod_listing.map (closeness s))
    (guesses.take 3).map Prod.fst
  let body ← if mem s mod_listing then do
      let fn := assocd s funny_filenames s ++ ".hlp"
      match ← file_on_path true_path fn with
      | .error e => throw (IO.userError e)
      | .ok file => pure (docToHelp (← IO.FS.readFile file))
    else
      let guesses := (guess s).map (fun s => "help \"" ++ HolCore.Printer.string_escaped s ++ "\";;\n")
      pure (String.join (["No help found for \"", HolCore.Printer.string_escaped s,
        "\"; did you mean:\n\n"] ++ guesses ++ ["\n?\n"]))
  return "-------------------------------------------------------------------\n" ++ body ++
    "--------------------------------------------------------------------\n"

/-- `help s`: print the help entry for `s`, or the three closest names. -/
def help (s : String) : IO Unit := do IO.print (← helpText s)

/- ---------------------------------------------------------------------- -/
/- Set up a theorem database, but leave contents clear for now.           -/
/- ---------------------------------------------------------------------- -/

initialize theorems : IO.Ref (List (String × thm)) ← IO.mkRef []

/-- Filled in by `Database.lean`: fills `theorems` on first use. -/
initialize theDatabaseLoader : IO.Ref (Option (IO Unit)) ← IO.mkRef none

/- ---------------------------------------------------------------------- -/
/- Some hacky term modifiers to encode searches.                          -/
/- ---------------------------------------------------------------------- -/

/-- `W mk_fun_ty ty`: `ty -> ty` (`fun` is always defined). -/
private def selfFunTy (ty : hol_type) : hol_type := .Tyapp "fun" [ty, ty]

def «omit» (t : term) : term :=
  mk_comb_unchecked (mk_var "<omit this pattern>" (selfFunTy (type_of t))) t
where mk_comb_unchecked (f x : term) : term := .Comb f x

def exactly (t : term) : term :=
  .Comb (mk_var "<match aconv>" (selfFunTy (type_of t))) t

def name (s : String) : term :=
  .Comb (mk_var "<match theorem name>" (selfFunTy aty)) (mk_var s aty)

/- ---------------------------------------------------------------------- -/
/- The main search function.                                              -/
/- ---------------------------------------------------------------------- -/

private def immediatesublist [BEq α] : List α → List α → Bool
  | [], _ => true
  | _, [] => false
  | h1 :: t1, h2 :: t2 => h1 == h2 && immediatesublist t1 t2

private def sublist [BEq α] : List α → List α → Bool
  | [], _ => true
  | _, [] => false
  | l1@(_ :: _), l2@(_ :: t2) => immediatesublist l1 l2 || sublist l1 t2

/-- `can (find_term p) tm` for an effectful `p`. -/
private partial def existsSubterm (p : term → IO Bool) (tm : term) : IO Bool := do
  if ← p tm then return true
  match tm with
  | .Comb f x => return (← existsSubterm p f) || (← existsSubterm p x)
  | .Abs _ b => existsSubterm p b
  | _ => return false

private partial def filterpred (tm : term) : (String × thm) → IO Bool :=
  match tm with
  | .Comb (.Var "<omit this pattern>" _) t => fun nth => do return !(← filterpred t nth)
  | .Comb (.Var "<match theorem name>" _) (.Var pat _) => fun (n, _) =>
      return sublist (explode pat) (explode n)
  | .Comb (.Var "<match aconv>" _) pat => fun (_, th) =>
      existsSubterm (fun t => return aconv pat t) (concl th)
  | pat => fun (_, th) =>
      existsSubterm (fun t => do return (← HolCore.Drule.term_match [] pat t).toOption.isSome) (concl th)

/-- `search pats`: the named theorems satisfying every pattern in `pats`. -/
def search (pats : List term) : IO (List (String × thm)) := do
  if (← theorems.get).isEmpty then
    if let some load := ← theDatabaseLoader.get then load
  let (triv, nontriv) := partition is_var pats
  if triv != [] then
    warn true ("Ignoring plain variables in search: " ++
      ", ".intercalate (triv.map (fun v => (dest_var v).toOption.map Prod.fst |>.getD "")))
  if nontriv == [] && triv != [] then return []
  else
    -- itlist (filter o filterpred) pats (!theorems)
    let mut ths ← theorems.get
    for p in pats.reverse do
      ths ← ths.filterM (filterpred p)
    return ths

end Help

/-- `help("NAME")` / `help "NAME"`: HOL Light's `help "NAME";;`. -/
syntax (name := helpParenCmd) "help" noWs "(" str ")" : term
@[inherit_doc helpParenCmd] syntax (name := helpStrCmd) "help" str : term
macro_rules
  | `(help($s)) => `(Help.help $s)
  | `(help $s:str) => `(Help.help $s)
