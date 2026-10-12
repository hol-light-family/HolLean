/- File: HolTest/UnitRecordsTest.lean
Runtime test suite: HOL Light's own UnitTests/records.ml (Library/components.ml
and Library/records.ml), translated assertion by assertion, in file order.  A
command that must merely succeed becomes an assertion that it succeeds.
Every assertion passes in real HOL Light (run against /tmp/hol4).
Part of the Lean4 translation of HOL Light by Chris Walton 2026. -/

import HolTest.CommonTest
import SessionLibrary.Records

open HolCore.Kernel HolTest.CommonTest

namespace HolTest.UnitRecordsTest
open Session SessionLibrary.Records HolLight.Syntax

private def ok (lbl : String) (b : Bool) : IO Unit :=
  IO.println (if b then s!"records {lbl} -> OK" else s!"records {lbl} -> MISMATCH")

private def get (lbl : String) (r : Except String α) : IO α := do
  match r with
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{lbl}: {e}")

#eval (do
  ensureRecords
  -- 9-11
  let (point_INDUCT, point_RECURSION, point_COMPONENTS) ← get "define_auto_record_type test_point"
    (← define_auto_record_type "test_point = { xcoord: num; ycoord: num }")
  ok "define_auto_record_type test_point" true
  -- 19
  ok "length (get_record_components point_COMPONENTS) = 2"
    ((← get "get_record_components" (get_record_components point_COMPONENTS)).length == 2)
  -- 22-23
  let rw_thms ← get "record_read_write_thms"
    (← record_read_write_thms (point_INDUCT, point_COMPONENTS))
  ok "length rw_thms = 2" (rw_thms.length == 2)
  -- 26-28
  let sv_thms ← get "record_strongly_valid_component_thms"
    (← record_strongly_valid_component_thms (point_INDUCT, point_COMPONENTS))
  ok "length sv_thms = 2" (sv_thms.length == 2)
  -- 31-32
  let orth_thms ← get "record_orthogonality_thms"
    (← record_orthogonality_thms (point_INDUCT, point_COMPONENTS))
  ok "length orth_thms = 2" (orth_thms.length == 2)
  -- 35-45
  let _ ← get "XCOORD_READ_WRITE" (← (HolLight.prove
    r"!x s:test_point. read xcoord (write xcoord x s) = x"
    (GEN_TAC THEN MATCH_MP_TAC point_INDUCT THEN REWRITE_TAC [point_COMPONENTS])).run)
  ok "XCOORD_READ_WRITE" true
  let _ ← get "YCOORD_INTACT" (← (HolLight.prove
    r"!x s:test_point. read ycoord (write xcoord x s) = read ycoord s"
    (GEN_TAC THEN MATCH_MP_TAC point_INDUCT THEN REWRITE_TAC [point_COMPONENTS])).run)
  ok "YCOORD_INTACT" true
  -- 48-54
  let (triple_INDUCT, _triple_RECURSION, triple_COMPONENTS) ← get "define_auto_record_type test_triple"
    (← define_auto_record_type "test_triple = { first: num; second: bool; third: num }")
  ok "length (get_record_components triple_COMPONENTS) = 3"
    ((← get "get_record_components" (get_record_components triple_COMPONENTS)).length == 3)
  ok "length (record_orthogonality_thms triple) = 6"
    ((← get "record_orthogonality_thms" (← record_orthogonality_thms
        (triple_INDUCT, triple_COMPONENTS))).length == 6)
  -- 62-67: benign redefinition returns the same theorems
  let (point2_INDUCT, point2_RECURSION, point2_COMPONENTS) ← get "define_record_type test_point again"
    (← define_record_type "test_point = { xcoord: num; ycoord: num }")
  ok "concl point2_INDUCT = concl point_INDUCT" (concl point2_INDUCT == concl point_INDUCT)
  ok "concl point2_RECURSION = concl point_RECURSION"
    (concl point2_RECURSION == concl point_RECURSION)
  ok "concl point2_COMPONENTS = concl point_COMPONENTS"
    (concl point2_COMPONENTS == concl point_COMPONENTS)
  -- 74-79: redefinition with different fields fails with the dedicated message
  match ← define_record_type "test_point = { xcoord: bool; ycoord: num }" with
  | .ok _ => ok "redefinition with different fields fails" false
  | .error msg =>
    ok "redefinition with different fields fails with the dedicated message"
      (msg == "define_record_type: type test_point already defined with different fields")
  : IO Unit)

end HolTest.UnitRecordsTest
