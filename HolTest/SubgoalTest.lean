/- File: HolTest/SubgoalTest.lean
Tests for the interactive subgoal package (tactics.ml): `g`, `e`, `b`, `r`,
`er`, `p`, `top_thm`, `flush_goalstack`, `set_goal`, and the goal printers
including `print_goal_hyp_max_boxes`.  Expected output is the transcript in
the corresponding hol-light/Help file (without the `val it : goalstack = `
prefix that the OCaml toplevel adds).  The CASE_REWRITE_TAC.hlp example at
the end is checked against HOL Light's own output instead (see there).
Lean4 translation by Chris Walton 2026 -/

import HolTest.CommonTest

open HolCore.Kernel Session HolTest.CommonTest

/-- The goalstack as `#eval` displays it (hol.ml's installed printer). -/
private unsafe def shown (l : HolCore.Tactics.goalstack) : IO String :=
  HolCore.Printer.print_to_string_io HolCore.Tactics.pp_print_goalstack l

private unsafe def expect (lbl : String) (act : IO HolCore.Tactics.goalstack) (want : String) : IO Unit := do
  try
    let got ← shown (← act)
    IO.println (if got == want then s!"{lbl} -> OK" else s!"{lbl} -> MISMATCH got:\n{got}")
  catch e => IO.println s!"{lbl} -> MISMATCH failed: {e}"

private unsafe def expectFail (lbl : String) (act : IO α) (needle : String) : IO Unit := do
  try
    let _ ← act
    IO.println s!"{lbl} -> MISMATCH wrongly succeeded"
  catch e =>
    let m := toString e
    IO.println (if (m.splitOn needle).length ≥ 2 then s!"{lbl} -> OK (correctly rejected)"
                else s!"{lbl} -> MISMATCH wrong message: {m}")

-- Help/g.hlp, e.hlp, b.hlp.
#eval (do
  let _ ← (IO.mkRef (concl listDefs.HD) : IO (IO.Ref term))
  let t := [[ (HD[1;2;3] = 1) /\ (TL[1;2;3] = [2;3]) ]]
  expect "g (g.hlp)" (g t)
    "1 subgoal (1 total)\n\n`HD [1; 2; 3] = 1 /\\ TL [1; 2; 3] = [2; 3]`\n"
  expect "e CONJ_TAC (e.hlp)" (e CONJ_TAC)
    "2 subgoals (2 total)\n\n`TL [1; 2; 3] = [2; 3]`\n\n`HD [1; 2; 3] = 1`\n"
  expect "b (b.hlp)" b
    "1 subgoal (1 total)\n\n`HD [1; 2; 3] = 1 /\\ TL [1; 2; 3] = [2; 3]`\n"
  expectFail "b at the bottom of the stack" b "Can't back up any more"
  let _ ← e CONJ_TAC
  expect "e (REWRITE_TAC[HD]) (e.hlp)" (e (REWRITE_TAC [listDefs.HD]))
    "1 subgoal (1 total)\n\n`TL [1; 2; 3] = [2; 3]`\n"
  expect "e (REWRITE_TAC[TL]) (e.hlp)" (e (REWRITE_TAC [listDefs.TL])) "No subgoals\n"
  match ← (try some <$> top_thm catch _ => pure none) with
  | some th => stmtOK "top_thm after No subgoals" th "HD[1;2;3] = 1 /\\ TL[1;2;3] = [2;3]"
  | none => IO.println "top_thm -> MISMATCH failed"
  : IO Unit)

-- Help/r.hlp.
#eval (do
  let _ ← (IO.mkRef (concl listDefs.HD) : IO (IO.Ref term))
  let _ ← g ([[ (HD[1;2;3] = 1) /\ (TL[1;2;3] = [2;3]) /\ (HD (TL[1;2;3]) = 2) ]])
  expect "e (REPEAT CONJ_TAC) (r.hlp)" (e (REPEAT CONJ_TAC))
    ("3 subgoals (3 total)\n\n`HD (TL [1; 2; 3]) = 2`\n\n`TL [1; 2; 3] = [2; 3]`\n\n" ++
     "`HD [1; 2; 3] = 1`\n")
  expect "r 1 (r.hlp)" (r 1) "1 subgoal (3 total)\n\n`TL [1; 2; 3] = [2; 3]`\n"
  expect "r 1 again (r.hlp)" (r 1) "1 subgoal (3 total)\n\n`HD (TL [1; 2; 3]) = 2`\n"
  let before := (← p).length
  flush_goalstack
  let after := (← p).length
  IO.println (if before > 1 && after == 1 then "flush_goalstack keeps only the newest state -> OK"
              else s!"flush_goalstack -> MISMATCH {before} -> {after}")
  : IO Unit)

-- Help/er.hlp: `er ALL_TAC` rotates one subgoal, and one `b` undoes it all.
-- `ARITH_TAC` is int.ml's; force the library through int.ml in load order
-- first (as HolInit does), or the real layers would be built after it.
#eval (do
  ensureHolPrefixThroughInt
  let _ ← g ([[ x + 1 = 1 + x /\ 1 + 1 = 2 ]])
  expect "e CONJ_TAC (er.hlp)" (e CONJ_TAC)
    "2 subgoals (2 total)\n\n`1 + 1 = 2`\n\n`x + 1 = 1 + x`\n"
  expect "er ALL_TAC (er.hlp)" (er ALL_TAC) "1 subgoal (2 total)\n\n`1 + 1 = 2`\n"
  expect "e ARITH_TAC (er.hlp)" (e ARITH_TAC) "1 subgoal (1 total)\n\n`x + 1 = 1 + x`\n"
  expect "e (REWRITE_TAC[ADD_SYM]) (er.hlp)" (e (REWRITE_TAC [ADD_SYM])) "No subgoals\n"
  let _ ← g ([[ x + 1 = 1 + x /\ 1 + 1 = 2 ]])
  let _ ← e CONJ_TAC
  let _ ← er ALL_TAC
  expect "one b undoes er" b "2 subgoals (2 total)\n\n`1 + 1 = 2`\n\n`x + 1 = 1 + x`\n"
  : IO Unit)

-- Help/print_goal_hyp_max_boxes.hlp.
#eval (do
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))
  let _ ← g ([[ 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 10 ==> 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 = 20 ]])
  -- The goal is too long for one line: HOL Light breaks before `==>`,
  -- indented one column (under the term, after the backquote).  The .hlp
  -- shows no indent there, unlike every other such transcript
  -- (LIST_INDUCT_TAC.hlp, MAP_FIRST.hlp, METIS_TAC.hlp), so it was trimmed.
  expect "g long implication breaks before ==>" p
    ("1 subgoal (1 total)\n\n`1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 10\n" ++
     " ==> 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 = 20`\n")
  let concl2 := "\n`2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 = 20`\n"
  expect "e STRIP_TAC (print_goal_hyp_max_boxes.hlp)" (e STRIP_TAC)
    ("1 subgoal (1 total)\n\n  0 [`1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 10`]\n" ++ concl2)
  HolCore.Tactics.print_goal_hyp_max_boxes.set (some 5)
  expect "print_goal_hyp_max_boxes := Some 5" p
    ("1 subgoal (1 total)\n\n  0 [`. = 10`]\n" ++ concl2)
  HolCore.Tactics.print_goal_hyp_max_boxes.set none
  expect "print_goal_hyp_max_boxes := None" p
    ("1 subgoal (1 total)\n\n  0 [`1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 10`]\n" ++ concl2)
  : IO Unit)

-- set_goal: assumptions become labelled-"" hypotheses, printed as `rev asl`
-- numbered from 0 (tactics.ml `print_hyps fmt 0 (rev asl)`); a non-boolean
-- assumption or goal fails (ASSUME / mk_goalstate).
#eval (do
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))
  expect "set_goal with assumptions" (set_goal [ [[ p:bool ]], [[ q:bool ]] ] ([[ p /\ q ]]))
    "1 subgoal (1 total)\n\n  0 [`q`]\n  1 [`p`]\n\n`p /\\ q`\n"
  expectFail "set_goal non-boolean assumption" (set_goal [ [[ 1 ]] ] ([[ T ]])) "ASSUME"
  expectFail "g non-boolean goal" (g ([[ 1 ]])) "mk_goalstate: Non-boolean goal"
  : IO Unit)

-- Help/LIST_INDUCT_TAC.hlp: three multi-line goals, verbatim.  The .hlp
-- predates `set_verbose_symbols`, so print with the terse symbols for this
-- check (and restore them after).
#eval (do
  let _ ← (IO.mkRef (concl listDefs.MAP) : IO (IO.Ref term))
  HolCore.Bool.unset_verbose_symbols
  try
    let _ ← g ([[ !l f:A->B g:B->C. MAP (g o f) l = MAP g (MAP f l) ]])
    expect "e (MATCH_MP_TAC list_INDUCT) (LIST_INDUCT_TAC.hlp)" (e (MATCH_MP_TAC list_INDUCT))
      ("1 subgoal (1 total)\n\n" ++
       "`(!f g. MAP (g o f) [] = MAP g (MAP f [])) /\\\n" ++
       " (!a0 a1.\n" ++
       "      (!f g. MAP (g o f) a1 = MAP g (MAP f a1))\n" ++
       "      ==> (!f g. MAP (g o f) (CONS a0 a1) = MAP g (MAP f (CONS a0 a1))))`\n")
    expect "e (REWRITE_TAC[MAP]) (LIST_INDUCT_TAC.hlp)" (e (REWRITE_TAC [listDefs.MAP]))
      ("1 subgoal (1 total)\n\n" ++
       "`!a0 a1.\n" ++
       "     (!f g. MAP (g o f) a1 = MAP g (MAP f a1))\n" ++
       "     ==> (!f g.\n" ++
       "              CONS ((g o f) a0) (MAP (g o f) a1) =\n" ++
       "              CONS (g (f a0)) (MAP g (MAP f a1)))`\n")
    -- The .hlp (written in 2010) breaks after `=` here, but OCaml 5's Format -
    -- which HolCore.System reproduces exactly - keeps the equation on one line:
    -- its box ends at column 76, within the margin of 78 (the closing `))`` is
    -- outside the box).  OCaml 4.14 gives the same.  Recorded as OCaml 5 prints.
    expect "e (MAP_EVERY X_GEN_TAC [k; l]) (LIST_INDUCT_TAC.hlp, OCaml 5 layout)"
      (e (MAP_EVERY X_GEN_TAC [ [[ k:A ]], [[ l:A list ]] ]))
      ("1 subgoal (1 total)\n\n" ++
       "`(!f g. MAP (g o f) l = MAP g (MAP f l))\n" ++
       " ==> (!f g.\n" ++
       "          CONS ((g o f) k) (MAP (g o f) l) = CONS (g (f k)) (MAP g (MAP f l)))`\n")
  finally
    let _ ← HolCore.Bool.set_verbose_symbols
  : IO Unit)

-- Help/CASE_REWRITE_TAC.hlp, with the help file's typographic quotes
-- replaced by backquotes.  Expected output printed by HOL Light (the help
-- file's own transcript is from an older printer: `!a b c.`, other indents).
-- Forcing REAL_DIV_REFL first builds real.ml's layer, so the overloading of
-- `<` and `/` is in place when the quotation is parsed.
#eval (do
  let _ ← (IO.mkRef (concl REAL_DIV_REFL) : IO (IO.Ref term))
  expect "g (CASE_REWRITE_TAC.hlp)" (g [[ !a b c. a < b ==> (a - b) / (a - b) * c = c ]])
    "1 subgoal (1 total)\n\n`forall a b c. a < b ==> (a - b) / (a - b) * c = c`\n"
  expect "e (CASE_REWRITE_TAC REAL_DIV_REFL) (CASE_REWRITE_TAC.hlp)"
    (e (CASE_REWRITE_TAC REAL_DIV_REFL))
    ("1 subgoal (1 total)\n\n`forall a b c.\n     a < b\n" ++
     "     ==> (~(a - b = &0) ==> &1 * c = c) /\\\n" ++
     "         (a - b = &0 ==> (a - b) / (a - b) * c = c)`\n")
  : IO Unit)
