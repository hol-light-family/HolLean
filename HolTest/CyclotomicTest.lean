/- File: HolTest/CyclotomicTest.lean
Runtime test suite: Library/cyclotomic.ml (HolLibrary/Cyclotomic.lean, wired by
SessionLibrary/Cyclotomic.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/cyclotomic.ml"`, then `string_of_thm`, newlines joined).
tools/cyclotomicdiff/check.sh compares every theorem structurally and as
printed, and the constants and definitions after loading.  Theorems that
print with `?NNN` invented type variables are omitted here. -/

import HolTest.CommonTest
import SessionLibrary.Cyclotomic

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.Cyclotomic.ensureCyclotomic

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def check (lbl : String) (r : IO (Except String thm)) (expected : String) :
    IO Unit := do
  let got ← match ← r with
    | .ok th => pure (squash (← HolCore.Printer.string_of_thm th))
    | .error e => pure s!"FAIL {e}"
  if got == squash expected || got == expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

private unsafe def thm' (lbl : String) (th : thm) (expected : String) : IO Unit :=
  check lbl (pure (.ok th)) expected

namespace T
open Session SessionLibrary.Cyclotomic HolLight.Syntax

#eval thm' "CYCLOTOMIC_GALOIS_GROUP_MODMUL" CYCLOTOMIC_GALOIS_GROUP_MODMUL
  "|- forall h k l z n.        field l /\\        z IN ring_carrier l /\\        ring_order l z = n /\\        ~(n = 0) /\\        subfield_generated l (z INSERT IMAGE h (ring_carrier k)) = l        ==> (exists e.                 group_monomorphism (galois_group (k,l) h,modmul_group n) e /\\                 (forall f.                      f IN group_carrier (galois_group (k,l) h)                      ==> f z = ring_pow l z (e f)))"
#eval thm' "CYCLOTOMIC_GALOIS_GROUP_MODMUL_ISOMORPHISM" CYCLOTOMIC_GALOIS_GROUP_MODMUL_ISOMORPHISM
  "|- forall h k l z n.        field_extension (k,l) h /\\        z IN ring_carrier l /\\        ring_order l z = n /\\        ~(n = 0) /\\        subfield_generated l (z INSERT IMAGE h (ring_carrier k)) = l        ==> ((exists e.                  group_isomorphism (galois_group (k,l) h,modmul_group n) e /\\                  (forall f.                       f IN group_carrier (galois_group (k,l) h)                       ==> f z = ring_pow l z (e f))) <=>             extension_degree (k,l) h = phi n)"

end T
