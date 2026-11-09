/- File: HolTest/NormalBasisTest.lean
Runtime test suite: Library/normal_basis.ml (HolLibrary/NormalBasis.lean, wired by
SessionLibrary/NormalBasis.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/normal_basis.ml"`, then `string_of_thm`, newlines joined).
tools/normalbasisdiff/check.sh compares every theorem structurally and as
printed, and the constants and definitions after loading.  Theorems that
print with `?NNN` invented type variables are omitted here. -/

import HolTest.CommonTest
import SessionLibrary.NormalBasis

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.NormalBasis.ensureNormalBasis

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
open Session SessionLibrary.NormalBasis HolLight.Syntax

#eval thm' "NORMAL_BASIS_INDEPENDENT" NORMAL_BASIS_INDEPENDENT
  "|- forall h k l x.        finite_extension (k,l) h /\\        galois_extension (k,l) h /\\        x IN ring_carrier l /\\        (forall c.             (forall f.                  f IN group_carrier (galois_group (k,l) h)                  ==> c f IN ring_carrier k) /\\             ring_sum l (group_carrier (galois_group (k,l) h))             (\\f. ring_mul l (h (c f)) (f x)) =             ring_0 l             ==> (forall f.                      f IN group_carrier (galois_group (k,l) h)                      ==> c f = ring_0 k))        ==> (forall f g.                 f IN group_carrier (galois_group (k,l) h) /\\                 g IN group_carrier (galois_group (k,l) h) /\\                 f x = g x                 ==> f = g) /\\            ring_basis (k,l) h            (IMAGE (\\f. f x) (group_carrier (galois_group (k,l) h))) /\\            (forall y.                 y IN ring_carrier l                 ==> (exists c.                          (forall f.                               f IN group_carrier (galois_group (k,l) h)                               ==> c f IN ring_carrier k) /\\                          y =                          ring_sum l (group_carrier (galois_group (k,l) h))                          (\\f. ring_mul l (h (c f)) (f x))))"
#eval thm' "NORMAL_BASIS_DET_INDEPENDENT" NORMAL_BASIS_DET_INDEPENDENT
  "|- forall h k l x.        finite_extension (k,l) h /\\        x IN ring_carrier l /\\        ~(ring_det l (group_carrier (galois_group (k,l) h))          (\\f g. (inverse f o g) x) =          ring_0 l)        ==> (forall c.                 (forall f.                      f IN group_carrier (galois_group (k,l) h)                      ==> c f IN ring_carrier k) /\\                 ring_sum l (group_carrier (galois_group (k,l) h))                 (\\f. ring_mul l (h (c f)) (f x)) =                 ring_0 l                 ==> (forall f.                          f IN group_carrier (galois_group (k,l) h)                          ==> c f = ring_0 k))"
#eval thm' "NORMAL_BASIS_DETERMINANT" NORMAL_BASIS_DETERMINANT
  "|- forall h k l x.        finite_extension (k,l) h /\\        galois_extension (k,l) h /\\        x IN ring_carrier l        ==> ((forall c.                  (forall f.                       f IN group_carrier (galois_group (k,l) h)                       ==> c f IN ring_carrier k) /\\                  ring_sum l (group_carrier (galois_group (k,l) h))                  (\\f. ring_mul l (h (c f)) (f x)) =                  ring_0 l                  ==> (forall f.                           f IN group_carrier (galois_group (k,l) h)                           ==> c f = ring_0 k)) <=>             ~(ring_det l (group_carrier (galois_group (k,l) h))               (\\f g. (inverse f o g) x) =               ring_0 l))"
#eval thm' "NORMAL_BASIS_CYCLIC" NORMAL_BASIS_CYCLIC
  "|- forall h k l.        finite_extension (k,l) h /\\        galois_extension (k,l) h /\\        cyclic_group (galois_group (k,l) h)        ==> (exists x.                 x IN ring_carrier l /\\                 (forall y.                      y IN ring_carrier l                      ==> (exists c.                               (forall f.                                    f IN group_carrier (galois_group (k,l) h)                                    ==> c f IN ring_carrier k) /\\                               y =                               ring_sum l                               (group_carrier (galois_group (k,l) h))                               (\\f. ring_mul l (h (c f)) (f x)))) /\\                 (forall c.                      (forall f.                           f IN group_carrier (galois_group (k,l) h)                           ==> c f IN ring_carrier k) /\\                      ring_sum l (group_carrier (galois_group (k,l) h))                      (\\f. ring_mul l (h (c f)) (f x)) =                      ring_0 l                      ==> (forall f.                               f IN group_carrier (galois_group (k,l) h)                               ==> c f = ring_0 k)))"
#eval thm' "NORMAL_BASIS_INFINITE" NORMAL_BASIS_INFINITE
  "|- forall h k l.        finite_extension (k,l) h /\\        galois_extension (k,l) h /\\        INFINITE (ring_carrier k)        ==> (exists x.                 x IN ring_carrier l /\\                 (forall y.                      y IN ring_carrier l                      ==> (exists c.                               (forall f.                                    f IN group_carrier (galois_group (k,l) h)                                    ==> c f IN ring_carrier k) /\\                               y =                               ring_sum l                               (group_carrier (galois_group (k,l) h))                               (\\f. ring_mul l (h (c f)) (f x)))) /\\                 (forall c.                      (forall f.                           f IN group_carrier (galois_group (k,l) h)                           ==> c f IN ring_carrier k) /\\                      ring_sum l (group_carrier (galois_group (k,l) h))                      (\\f. ring_mul l (h (c f)) (f x)) =                      ring_0 l                      ==> (forall f.                               f IN group_carrier (galois_group (k,l) h)                               ==> c f = ring_0 k)))"
#eval thm' "NORMAL_BASIS_THEOREM" NORMAL_BASIS_THEOREM
  "|- forall h k l.        finite_extension (k,l) h /\\ galois_extension (k,l) h        ==> (exists x.                 x IN ring_carrier l /\\                 (forall y.                      y IN ring_carrier l                      ==> (exists c.                               (forall f.                                    f IN group_carrier (galois_group (k,l) h)                                    ==> c f IN ring_carrier k) /\\                               y =                               ring_sum l                               (group_carrier (galois_group (k,l) h))                               (\\f. ring_mul l (h (c f)) (f x)))) /\\                 (forall c.                      (forall f.                           f IN group_carrier (galois_group (k,l) h)                           ==> c f IN ring_carrier k) /\\                      ring_sum l (group_carrier (galois_group (k,l) h))                      (\\f. ring_mul l (h (c f)) (f x)) =                      ring_0 l                      ==> (forall f.                               f IN group_carrier (galois_group (k,l) h)                               ==> c f = ring_0 k)))"
#eval thm' "NORMAL_BASIS_RING_BASIS" NORMAL_BASIS_RING_BASIS
  "|- forall h k l.        finite_extension (k,l) h /\\ galois_extension (k,l) h        ==> (exists x.                 x IN ring_carrier l /\\                 ring_basis (k,l) h                 (IMAGE (\\f. f x) (group_carrier (galois_group (k,l) h))) /\\                 (forall f g.                      f IN group_carrier (galois_group (k,l) h) /\\                      g IN group_carrier (galois_group (k,l) h) /\\                      f x = g x                      ==> f = g))"
#eval thm' "NORMAL_BASIS_FREE_BASIS" NORMAL_BASIS_FREE_BASIS
  "|- forall h k l.        finite_extension (k,l) h /\\ galois_extension (k,l) h        ==> (exists x.                 x IN ring_carrier l /\\                 (forall n e.                      BIJ e {i | i < n} (group_carrier (galois_group (k,l) h))                      ==> free_basis (k,l) h n (\\i. e i x)))"
#eval thm' "FINITE_FIELD_NORMAL_BASIS" FINITE_FIELD_NORMAL_BASIS
  "|- forall h k l.        field_extension (k,l) h /\\ FINITE (ring_carrier l)        ==> (exists x.                 x IN ring_carrier l /\\                 free_basis (k,l) h (extension_degree (k,l) h)                 (\\i. ring_pow l x (CARD (ring_carrier k) EXP i)))"

end T
