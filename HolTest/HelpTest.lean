/- File: HolTest/HelpTest.lean
Tests for Help.lean (help.ml): the `help` command, the doc-to-help.sed
conversion, and `search` with its `omit` / `exactly` / `name` modifiers.
Lean4 translation by Chris Walton 2026 -/

import Help
import HolTest.CommonTest

open HolCore.Kernel Session HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- docToHelp against doc-to-help.sed.                                     -/
/- ---------------------------------------------------------------------- -/

-- A synthetic entry using every construct the sed script handles.  The
-- expected text is the output of `sed -f hol-light/doc-to-help.sed` on it.
#eval (do
  let src := "\\DOC SYNTH\n\n\\TYPE {SYNTH : thm -> thm}\n\n\\KEYWORDS\nrule, gone.\n\n\\LIBRARY\nlib-gone\n\n\\SYNOPSIS\nBraces {x} and {{y}} and \\#, \\char'136, \\char'056, \\char'100.\n\n\\CATEGORIES\nTests.\n\n\\DESCRIBE\n\\noindent Starts here. Uses {\\em not} and {{\\em kept}}.\n\n\\begin{{itemize}}\n\\item First \\item second\n\\end{{itemize}}\n\n\\BLTYPE\ngone\n\\ELTYPE\n\n\\FAILURE\nNever.\n\n\\EXAMPLE\n{\n  # SYNTH th;;\n}\n\n\\USES\nUses.\n\n\\COMMENTS\nNone.\n\n\\SEEALSO\nOTHER.\n\n\\ENDDOC\n"
  let want := "\nSYNTH : thm -> thm\n\nSYNOPSIS\n\nBraces x and {y} and #, ^, ., @.\n\nCATEGORIES\n\nTests.\n\nDESCRIPTION\n\nStarts here. Uses \\em not and *kept*.\n\n---------\n * First \\item second\n---------\n\ngone\n\nFAILURE CONDITIONS\n\nNever.\n\nEXAMPLES\n\n\n  # SYNTH th;;\n\n\nUSES\n\nUses.\n\nCOMMENTS\n\nNone.\n\nSEE ALSO\nOTHER.\n\n"
  let got := Help.docToHelp src
  if got == want then IO.println "docToHelp = sed -f doc-to-help.sed on every rule -> OK"
  else IO.println s!"docToHelp -> MISMATCH got:\n{got}" : IO Unit)

/- ---------------------------------------------------------------------- -/
/- help.                                                                  -/
/- ---------------------------------------------------------------------- -/

#eval (do
  let t ← Help.helpText "REAL_LET_IMP"
  let ok := t.startsWith "-------------------------------------------------------------------\n" &&
    t.endsWith "--------------------------------------------------------------------\n" &&
    (t.splitOn "\nREAL_LET_IMP : thm -> thm\n").length == 2 &&
    (t.splitOn "\nSEE ALSO\nLE_IMP, REAL_ARITH, REAL_LE_IMP.\n").length == 2 &&
    (t.splitOn "\\").length == 1                    -- no markup left
  IO.println (if ok then "help \"REAL_LET_IMP\" -> OK" else s!"help REAL_LET_IMP -> MISMATCH\n{t}") : IO Unit)

-- help.ml's funny_filenames: `++` is stored as `.joinparsers.hlp`.
#eval (do
  let t ← Help.helpText "++"
  if (t.splitOn "(++) : ").length == 2 then IO.println "help \"++\" reads .joinparsers.hlp -> OK"
  else IO.println s!"help ++ -> MISMATCH\n{t}" : IO Unit)

-- An unknown name: the three closest names by relative edit distance.
#eval (do
  let t ← Help.helpText "REAL_LET_IMPP"
  let want := "-------------------------------------------------------------------\n" ++
    "No help found for \"REAL_LET_IMPP\"; did you mean:\n\n" ++
    "help \"REAL_LET_IMP\";;\nhelp \"REAL_LE_IMP\";;\nhelp \"REAL_IDEAL_CONV\";;\n\n?\n" ++
    "--------------------------------------------------------------------\n"
  IO.println (if t == want then "help on an unknown name suggests the closest -> OK"
              else s!"help unknown -> MISMATCH\n{t}") : IO Unit)

#eval (do
  let cases : List (String × String × Nat) :=
    [("", "", 0), ("abc", "", 3), ("kitten", "sitting", 3), ("REAL_LET_IMP", "REAL_LE_IMP", 1)]
  let bad := cases.filter (fun (a, b, n) => Help.edit_distance a b != n)
  IO.println (if bad.isEmpty then "edit_distance -> OK" else s!"edit_distance -> MISMATCH {bad}") : IO Unit)

/- ---------------------------------------------------------------------- -/
/- search, on a small theorem list (the full database is Database.lean).  -/
/- ---------------------------------------------------------------------- -/

#eval (do
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))
  let saved ← Help.theorems.get
  Help.theorems.set [("ADD_SYM", ADD_SYM), ("ADD_ASSOC", ADD_ASSOC),
                     ("MULT_SYM", MULT_SYM), ("ADD_0", ADD_0)]
  let names (r : List (String × thm)) := r.map Prod.fst
  let check (lbl : String) (pats : List String) (mods : List term → List term) (want : List String) :
      IO Unit := do
    let mut ts : List term := []
    for p in pats do
      match ← HolCore.Parser.parse_term p with
      | .ok t => ts := ts ++ [t]
      | .error e => IO.println s!"{lbl} -> MISMATCH parse {e}"
    let got := names (← Help.search (mods ts))
    IO.println (if got == want then s!"search {lbl} -> OK" else s!"search {lbl} -> MISMATCH got {got}")
  check "pattern `x + y`" ["x + y"] id ["ADD_SYM", "ADD_ASSOC", "ADD_0"]
  check "pattern `x * y`" ["x * y"] id ["MULT_SYM"]
  check "two patterns (both required)" ["x + y", "0"] id ["ADD_0"]
  check "omit" ["x + y", "0"] (fun ts => [ts[0]!, Help.«omit» ts[1]!]) ["ADD_SYM", "ADD_ASSOC"]
  check "exactly" ["m + n"] (fun ts => ts.map Help.exactly) ["ADD_SYM", "ADD_ASSOC"]
  let byName := names (← Help.search [Help.name "ADD"])
  IO.println (if byName == ["ADD_SYM", "ADD_ASSOC", "ADD_0"] then "search name \"ADD\" -> OK"
              else s!"search name -> MISMATCH got {byName}")
  let plain := names (← Help.search [mk_var "x" bool_ty])
  IO.println (if plain.isEmpty then "search of only plain variables returns [] -> OK"
              else s!"search plain vars -> MISMATCH got {plain}")
  Help.theorems.set saved : IO Unit)
