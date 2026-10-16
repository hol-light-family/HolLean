/- File: HolTest/MatroidsTest.lean
Runtime test suite: Library/matroids.ml (HolLibrary/Matroids.lean, wired by
SessionLibrary/Matroids.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/matroids.ml"`, then `string_of_thm`, newlines joined).
tools/matroidsdiff/check.sh compares every theorem structurally and as
printed, and the constants and definitions after loading.  Theorems that
print with `?NNN` invented type variables are omitted here. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.Matroids.ensureMatroids

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
open Session SessionLibrary.Matroids HolLight.Syntax

#eval thm' "matroid_tybij" matroid_tybij
  "|- (forall a. matroid (dest_matroid a) = a) /\\    (forall r.         (forall s. s SUBSET FST r ==> SND r s SUBSET FST r) /\\         (forall s. s SUBSET FST r ==> s SUBSET SND r s) /\\         (forall s t. s SUBSET t /\\ t SUBSET FST r ==> SND r s SUBSET SND r t) /\\         (forall s. s SUBSET FST r ==> SND r (SND r s) = SND r s) /\\         (forall s x.              s SUBSET FST r /\\ x IN SND r s              ==> (exists s'. FINITE s' /\\ s' SUBSET s /\\ x IN SND r s')) /\\         (forall s x y.              s SUBSET FST r /\\              x IN FST r /\\              y IN SND r (x INSERT s) /\\              ~(y IN SND r s)              ==> x IN SND r (y INSERT s)) <=>         dest_matroid (matroid r) = r)"
#eval thm' "MATROID_SPAN_EQ_SET" MATROID_SPAN_EQ_SET
  "|- forall m s.        s SUBSET matroid_set m        ==> (matroid_span m s = matroid_set m <=>             matroid_set m SUBSET matroid_span m s)"
#eval thm' "matroid_spanning" matroid_spanning
  "|- forall s m.        matroid_spanning m s <=>        s SUBSET matroid_set m /\\ matroid_span m s = matroid_set m"
#eval thm' "MATROID_INDEPENDENT_FINITARY" MATROID_INDEPENDENT_FINITARY
  "|- forall m s.        matroid_independent m s <=>        s SUBSET matroid_set m /\\        (forall t. FINITE t /\\ t SUBSET s ==> matroid_independent m t)"
#eval thm' "MATROID_INDEPENDENT_EXTENDS_TO_BASIS" MATROID_INDEPENDENT_EXTENDS_TO_BASIS
  "|- forall m s.        matroid_independent m s        ==> (exists b. s SUBSET b /\\ matroid_basis m b)"
#eval thm' "MATROID_INDEPENDENT_SPANNING_FINITE" MATROID_INDEPENDENT_SPANNING_FINITE
  "|- forall m s t.        matroid_independent m s /\\ matroid_spanning m t /\\ FINITE t        ==> FINITE s"
#eval thm' "MATROID_SPAN_EQ_SELF" MATROID_SPAN_EQ_SELF
  "|- forall m s.        s SUBSET matroid_set m        ==> (matroid_span m s = s <=> matroid_subspace m s)"
#eval thm' "MATROID_STEINITZ_EXCHANGE_FINITE" MATROID_STEINITZ_EXCHANGE_FINITE
  "|- forall m s t.        FINITE t /\\        t SUBSET matroid_set m /\\        matroid_independent m s /\\        s SUBSET matroid_span m t        ==> (exists t'.                 t' HAS_SIZE CARD t /\\                 s SUBSET t' /\\                 t' SUBSET s UNION t /\\                 matroid_span m t' = matroid_span m t)"
#eval thm' "MATROID_FINITE_DIMENSIONAL_CONTAINS_BASIS" MATROID_FINITE_DIMENSIONAL_CONTAINS_BASIS
  "|- forall m s.        matroid_finite_dimensional m /\\ matroid_spanning m s        ==> (exists b. FINITE b /\\ b SUBSET s /\\ matroid_basis m b)"
#eval thm' "MATROID_DIM_ALT" MATROID_DIM_ALT
  "|- forall m s.        s SUBSET matroid_set m        ==> matroid_dim m s =            (@n.                 exists b.                     b SUBSET s /\\                     matroid_independent m b /\\                     s SUBSET matroid_span m b /\\                     b HAS_SIZE n)"
#eval thm' "MATROID_DIM_LE" MATROID_DIM_LE
  "|- forall m s b n.        FINITE b /\\        CARD b <= n /\\        b SUBSET matroid_set m /\\        s SUBSET matroid_span m b        ==> matroid_dim m s <= n"
#eval thm' "MATROID_DIM_GE_FINITE_CARD_EQ" MATROID_DIM_GE_FINITE_CARD_EQ
  "|- forall m s.        s SUBSET matroid_set m /\\ FINITE s /\\ CARD s <= matroid_dim m s <=>        matroid_finite_dim m s /\\ matroid_independent m s"
#eval thm' "MATROID_LOWDIM_EXPAND_DIMENSION" MATROID_LOWDIM_EXPAND_DIMENSION
  "|- forall m s n.        matroid_finite_dim m s /\\        matroid_dim m s <= n /\\        (matroid_finite_dimensional m ==> n <= matroid_dimension m)        ==> (exists t.                 matroid_finite_dim m t /\\                 matroid_dim m t = n /\\                 matroid_span m s SUBSET matroid_span m t)"

end T
