/- File: HolTest/RecordsTest.lean
Runtime test suite: Library/records.ml (HolLibrary/Records.lean, wired by
SessionLibrary/Records.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/records.ml"`; tools/recordsdiff/rdump.ml), which also
compares the whole run with HOL Light structurally.  Invented type
variables are renumbered in order of appearance. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel Session SessionLibrary.Components SessionLibrary.Records HolTest.CommonTest

#eval ensureRecords

/-- Strip spaces and newlines, and renumber invented type variables `?N`. -/
private def squash (s : String) : String := Id.run do
  let s := (s.replace "\n" "").replace " " ""
  let mut out := ""
  let mut seen : List String := []
  let mut i := 0
  let cs := s.toList.toArray
  while i < cs.size do
    if cs[i]! == '?' then
      let mut j := i + 1
      while j < cs.size && cs[j]!.isDigit do j := j + 1
      let n := String.ofList (cs.extract i j).toList
      let k := match seen.idxOf? n with
        | some k => k
        | none => seen.length
      if k == seen.length then seen := seen ++ [n]
      out := out ++ s!"?{k}"
      i := j
    else
      out := out.push cs[i]!
      i := i + 1
  return out

private unsafe def check (lbl : String) (got expected : String) : IO Unit :=
  if squash got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

private unsafe def str (t : thm) : IO String := HolCore.Printer.string_of_thm t

/-- `parse_record_specification`, printed as rdump.ml prints it. -/
private unsafe def parseCheck (s expected : String) : IO Unit := do
  let got ← match ← parse_record_specification s with
    | .error e => pure s!"FAIL {e}"
    | .ok (n, fs) => do
      let mut r := n
      for (f, y) in fs do r := r ++ s!" {f}:{← HolCore.Printer.string_of_type y}"
      pure r
  check s!"parse_record_specification {s}" got expected
#eval parseCheck "point = { xc: num; yc: num }" "point xc:num yc:num"
#eval parseCheck "r = { a: num }" "r a:num"
#eval parseCheck "r { a: num }" "FAIL Noparse"
#eval parseCheck "r = { a: num } x" "FAIL Stuff after record spec"
#eval parseCheck "r = { a: num; }" "FAIL ';' or '}' expected"
#eval parseCheck "r = { a: nosuchtype }" "r a:nosuchtype"
#eval parseCheck "r = { }" "FAIL Noparse"

/-- The `define_record_type` sequence of rdump.ml: definition, benign
    redefinition, redefinition with different fields, a polymorphic record. -/
private unsafe def drt (s expected : String) : IO (Option (thm × thm × thm)) := do
  match ← define_record_type s with
  | .error e => check s!"define_record_type {s}" s!"FAIL {e}" expected; pure none
  | .ok r => check s!"define_record_type {s}" "OK" expected; pure (some r)

#eval (do
  let _ ← drt "point = { xc: num; yc: num }" "OK"
  let _ ← drt "point = { xc: num; zc: num }" "FAIL define_record_type: type point already defined with different fields"
  let _ ← drt "pair = { fst_c: A; snd_c: B }" "OK"
  pure () : IO Unit)

#eval (do
  match ← define_record_type "point = { xc: num; yc: num }" with
  | .ok (_, _, cth) => check "point components" (← str cth) "|- ((forall a0 a1. read xc (point_RECORD a0 a1) = a0) /\\ (forall a0' a0 a1. write xc a0' (point_RECORD a0 a1) = point_RECORD a0' a1)) /\\ (forall a0 a1. read yc (point_RECORD a0 a1) = a1) /\\ (forall a1' a0 a1. write yc a1' (point_RECORD a0 a1) = point_RECORD a0 a1')"
  | .error e => IO.println s!"point components -> MISMATCH {e}"
  match ← define_record_type "pair = { fst_c: A; snd_c: B }" with
  | .ok (_, _, cth) => check "pair components" (← str cth) "|- ((forall a0 a1. read fst_c (pair_RECORD a0 a1) = a0) /\\ (forall a0' a0 a1. write fst_c a0' (pair_RECORD a0 a1) = pair_RECORD a0' a1)) /\\ (forall a0 a1. read snd_c (pair_RECORD a0 a1) = a1) /\\ (forall a1' a0 a1. write snd_c a1' (pair_RECORD a0 a1) = pair_RECORD a0 a1')"
  | .error e => IO.println s!"pair components -> MISMATCH {e}" : IO Unit)

/- define_auto_record_type and the record_..._thms functions. -/
#eval (do
  match ← define_auto_record_type "state = { pc: num; regs: num list; flag: bool }" with
  | .error e => IO.println s!"define_auto_record_type -> MISMATCH {e}"
  | .ok (ith, _, cth) => do
    check "state induction" (← str ith) "|- forall P. (forall a0 a1 a2. P (state_RECORD a0 a1 a2)) ==> (forall x. P x)"
    let lst (lbl : String) (r : IO (Except String (List thm))) (expected : List String) : IO Unit := do
      match ← r with
      | .error e => IO.println s!"{lbl} -> MISMATCH {e}"
      | .ok l =>
        if l.length != expected.length then
          IO.println s!"{lbl} -> MISMATCH {l.length} theorems"
        else
          for (t, e, i) in (l.zip expected).zipIdx.map (fun ((t, e), i) => (t, e, i)) do
            check s!"{lbl} {i}" (← str t) e
    lst "record_read_write_thms" (record_read_write_thms (ith, cth))
      ["|- forall y s. read pc (write pc y s) = y",
       "|- forall y s. read regs (write regs y s) = y",
       "|- forall y s. read flag (write flag y s) <=> y"]
    lst "record_strongly_valid_component_thms" (record_strongly_valid_component_thms (ith, cth))
      ["|- strongly_valid_component pc",
       "|- strongly_valid_component regs",
       "|- strongly_valid_component flag"]
    lst "record_valid_component_thms" (record_valid_component_thms (ith, cth))
      ["|- valid_component pc",
       "|- valid_component regs",
       "|- valid_component flag"]
    lst "record_extensionally_valid_component_thms" (record_extensionally_valid_component_thms (ith, cth))
      ["|- extensionally_valid_component pc",
       "|- extensionally_valid_component regs",
       "|- extensionally_valid_component flag"]
    lst "record_weakly_valid_component_thms" (record_weakly_valid_component_thms (ith, cth))
      ["|- weakly_valid_component pc",
       "|- weakly_valid_component regs",
       "|- weakly_valid_component flag"]
    lst "record_orthogonality_thms" (record_orthogonality_thms (ith, cth))
      ["|- orthogonal_components pc regs",
       "|- orthogonal_components pc flag",
       "|- orthogonal_components regs pc",
       "|- orthogonal_components regs flag",
       "|- orthogonal_components flag pc",
       "|- orthogonal_components flag regs"]
  : IO Unit)

/- The theorem lists after the run above, as counts (HOL Light's order is
   checked by tools/recordsdiff). -/
