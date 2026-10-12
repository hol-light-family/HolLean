/- File: HolTest/NetsTest.lean
Runtime test suite: term nets (nets.ml).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set.

Term nets are a DISCRIMINATION structure: `lookup` must return exactly the
entries whose patterns are matchable to the query term.  A wrong label or a
wrong lookup edge silently changes WHICH rewrites fire, so the tests below
assert the retrieved SET, not merely that a lookup succeeds.  `lookup` is an
OVER-approximation by design - the caller's `term_match` rejects the residue -
so an all-variable pattern is expected to come back alongside a specific one. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/-- Report a retrieved tip set against its expectation, order-insensitively. -/
private def netSaid (lbl : String) (got exp : List Nat) : IO Unit :=
  let g := mergesort Nat.ble got
  let e := mergesort Nat.ble exp
  if g == e then IO.println s!"{lbl} -> OK {g}"
  else IO.println s!"{lbl} -> DIFFERS got {g} expected {e}"

/- ---------------------------------------------------------------------- -/
/- Round trip, and discrimination between distinct head constants.         -/
/- ---------------------------------------------------------------------- -/

#eval (do
  (do match ← HolCore.Nets.enter [] ([[ (a:bool) /\ b ]], 1) HolCore.Nets.empty_net with
      | .error e => IO.println s!"nets enter ERR: {e}"
      | .ok n1 => do
        netSaid "nets: single entry retrievable"
          (HolCore.Nets.lookup ([[ (a:bool) /\ b ]]) n1) [1]
        -- a different head constant must retrieve nothing
        netSaid "nets: unmatched head retrieves nothing"
          (HolCore.Nets.lookup ([[ ~(p:bool) ]]) n1) []))

#eval (do
  (do match ← HolCore.Nets.enter [] ([[ (a:bool) /\ b ]], 1) HolCore.Nets.empty_net with
      | .error e => IO.println s!"nets enter ERR: {e}"
      | .ok n1 =>
        match ← HolCore.Nets.enter [] ([[ (x:bool) \/ y ]], 2) n1 with
        | .error e => IO.println s!"nets enter2 ERR: {e}"
        | .ok n2 => do
          netSaid "nets: discriminates /\\ from \\/"
            (HolCore.Nets.lookup ([[ (p:bool) /\ q ]]) n2) [1]
          netSaid "nets: discriminates \\/ from /\\"
            (HolCore.Nets.lookup ([[ (p:bool) \/ q ]]) n2) [2]))

/- ---------------------------------------------------------------------- -/
/- An all-variable pattern is matchable to ANY conjunction, so it must come -/
/- back alongside a more specific entry (nets.ml `lookup` follows both the   -/
/- constant edge and the variable edge).                                    -/
/- ---------------------------------------------------------------------- -/

#eval (do
  (do match ← HolCore.Nets.enter [] ([[ T /\ F ]], 1) HolCore.Nets.empty_net with
      | .error e => IO.println s!"nets enter ERR: {e}"
      | .ok n1 =>
        match ← HolCore.Nets.enter [] ([[ (a:bool) /\ b ]], 2) n1 with
        | .error e => IO.println s!"nets enter2 ERR: {e}"
        | .ok n2 =>
          netSaid "nets: general pattern retrieved with specific one"
            (HolCore.Nets.lookup ([[ T /\ F ]]) n2) [1, 2]))

-- Help/lookup.hlp: `T /\ t`, `u /\ T` and `t /\ t` are ALL matchable to
-- `T /\ T`, so all three tips are retrieved.
#eval (do
  (do match ← HolCore.Nets.enter [] ([[ T /\ (t:bool) ]], 1) HolCore.Nets.empty_net with
      | .error e => IO.println s!"nets enter ERR: {e}"
      | .ok n1 =>
        match ← HolCore.Nets.enter [] ([[ (u:bool) /\ T ]], 2) n1 with
        | .error e => IO.println s!"nets enter2 ERR: {e}"
        | .ok n2 =>
          match ← HolCore.Nets.enter [] ([[ (t:bool) /\ t ]], 3) n2 with
          | .error e => IO.println s!"nets enter3 ERR: {e}"
          | .ok n3 =>
            netSaid "nets: Help/lookup.hlp three matchable patterns"
              (HolCore.Nets.lookup ([[ T /\ T ]]) n3) [1, 2, 3]))

/- ---------------------------------------------------------------------- -/
/- `merge_nets` unions the tip sets (nets.ml `merge_nets`).                -/
/- ---------------------------------------------------------------------- -/

#eval (do
  (do match ← HolCore.Nets.enter [] ([[ (a:bool) /\ b ]], 1) HolCore.Nets.empty_net with
      | .error e => IO.println s!"nets merge enter ERR: {e}"
      | .ok n1 =>
        match ← HolCore.Nets.enter [] ([[ (a:bool) /\ b ]], 2) HolCore.Nets.empty_net with
        | .error e => IO.println s!"nets merge enter2 ERR: {e}"
        | .ok n2 =>
          netSaid "nets: merge_nets unions tips"
            (HolCore.Nets.lookup ([[ (p:bool) /\ q ]]) (HolCore.Nets.merge_nets n1 n2))
            [1, 2]))

-- Merging nets whose patterns have DIFFERENT heads must keep both edges.
#eval (do
  (do match ← HolCore.Nets.enter [] ([[ (a:bool) /\ b ]], 1) HolCore.Nets.empty_net with
      | .error e => IO.println s!"nets merge2 enter ERR: {e}"
      | .ok n1 =>
        match ← HolCore.Nets.enter [] ([[ (x:bool) \/ y ]], 2) HolCore.Nets.empty_net with
        | .error e => IO.println s!"nets merge2 enter2 ERR: {e}"
        | .ok n2 => do
          let m := HolCore.Nets.merge_nets n1 n2
          netSaid "nets: merge keeps /\\ edge"
            (HolCore.Nets.lookup ([[ (p:bool) /\ q ]]) m) [1]
          netSaid "nets: merge keeps \\/ edge"
            (HolCore.Nets.lookup ([[ (p:bool) \/ q ]]) m) [2]))
