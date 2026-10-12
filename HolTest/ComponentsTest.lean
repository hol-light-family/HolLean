/- File: HolTest/ComponentsTest.lean
Runtime test suite: Library/components.ml (HolLibrary/Components.lean, wired
by SessionLibrary/Components.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/components.ml"`, then `string_of_thm`).  The whole file is
also compared with HOL Light by tools/componentsdiff/check.sh: all 38
theorems structurally, the theorem lists, the parse of `:>`, and the types,
constants and definitions.

Loading components.ml (`ensureComponents`) runs the whole file; a proof that
failed would `panic!`, which the `make verify` PANIC gate catches. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel Session SessionLibrary.Components HolTest.CommonTest

#eval ensureComponents

/-- Strip spaces and newlines, so line breaking does not matter, and
    renumber invented type variables `?N` in order of appearance: the
    counter that makes them differs between the two systems. -/
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

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/- ---------------------------------------------------------------------- -/
/- Theorem statements (components.ml), as HOL Light prints them.          -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "components.ml component_tybij" component_tybij
  "|- (forall a. component (dest_component a) = a) /\\ (forall r. dest_component (component r) = r)"
#eval thmCheck "components.ml COMPONENT_EQ" COMPONENT_EQ
  "|- forall (c1:(?143107,?143106)component) (c2:(?143107,?143106)component). (c1:(?143107,?143106)component) = (c2:(?143107,?143106)component) <=> (read:(?143107,?143106)component->?143107->?143106) (c1:(?143107,?143106)component) = (read:(?143107,?143106)component->?143107->?143106) (c2:(?143107,?143106)component) /\\ (write:(?143107,?143106)component->?143106->?143107->?143107) (c1:(?143107,?143106)component) = (write:(?143107,?143106)component->?143106->?143107->?143107) (c2:(?143107,?143106)component)"
#eval thmCheck "components.ml READ_ENTIRETY" READ_ENTIRETY
  "|- (read:(?143135,?143135)component->?143135->?143135) (entirety:(?143135,?143135)component) = (I:?143135->?143135) /\\ (forall (s:?143147). (read:(?143147,?143147)component->?143147->?143147) (entirety:(?143147,?143147)component) (s:?143147) = (s:?143147))"
#eval thmCheck "components.ml WRITE_ENTIRETY" WRITE_ENTIRETY
  "|- (forall (y:?143163). (write:(?143163,?143163)component->?143163->?143163->?143163) (entirety:(?143163,?143163)component) (y:?143163) = (\\(s:?143163). (y:?143163))) /\\ (forall (s:?143181) (y:?143181). (write:(?143181,?143181)component->?143181->?143181->?143181) (entirety:(?143181,?143181)component) (y:?143181) (s:?143181) = (y:?143181))"
#eval thmCheck "components.ml component_compose" component_compose
  "|- forall c2 c1. c1 :> c2 = component (read c2 o read c1,(\\v s. write c1 (write c2 v (read c1 s)) s))"
#eval thmCheck "components.ml COMPONENT_COMPOSE_ASSOC" COMPONENT_COMPOSE_ASSOC
  "|- forall (sc1:(?143281,?143271)component) (sc2:(?143271,?143270)component) (sc3:(?143270,?143277)component). (sc1:(?143281,?143271)component) :> (sc2:(?143271,?143270)component) :> (sc3:(?143270,?143277)component) = ((sc1:(?143281,?143271)component) :> (sc2:(?143271,?143270)component)) :> (sc3:(?143270,?143277)component)"
#eval thmCheck "components.ml COMPOSE_ENTIRETY" COMPOSE_ENTIRETY
  "|- (forall (c:(?143373,?143375)component). (c:(?143373,?143375)component) :> (entirety:(?143375,?143375)component) = (c:(?143373,?143375)component)) /\\ (forall (c:(?143388,?143387)component). (entirety:(?143388,?143388)component) :> (c:(?143388,?143387)component) = (c:(?143388,?143387)component))"
#eval thmCheck "components.ml READ_WRITE_COMPONENT_COMPOSE" READ_WRITE_COMPONENT_COMPOSE
  "|- forall (sc1:(?143470,?143433)component) (sc2:(?143433,?143430)component). (forall (y:?143433) (s:?143470). (read:(?143470,?143433)component->?143470->?143433) (sc1:(?143470,?143433)component) ((write:(?143470,?143433)component->?143433->?143470->?143470) (sc1:(?143470,?143433)component) (y:?143433) (s:?143470)) = (y:?143433)) /\\ (forall (y:?143430) (s:?143433). (read:(?143433,?143430)component->?143433->?143430) (sc2:(?143433,?143430)component) ((write:(?143433,?143430)component->?143430->?143433->?143433) (sc2:(?143433,?143430)component) (y:?143430) (s:?143433)) = (y:?143430)) ==> (forall (y:?143430) (s:?143470). (read:(?143470,?143430)component->?143470->?143430) ((sc1:(?143470,?143433)component) :> (sc2:(?143433,?143430)component)) ((write:(?143470,?143430)component->?143430->?143470->?143470) ((sc1:(?143470,?143433)component) :> (sc2:(?143433,?143430)component)) (y:?143430) (s:?143470)) = (y:?143430))"
#eval thmCheck "components.ml weak_read_over_write" weak_read_over_write
  "|- forall c. weak_read_over_write c <=> (exists f. forall y s. read c (write c y s) = f y)"
#eval thmCheck "components.ml valid_component" valid_component
  "|- (valid_component:(?143596,?143593)component->bool) (c:(?143596,?143593)component) <=> (forall (y:?143593) (s:?143596). (read:(?143596,?143593)component->?143596->?143593) (c:(?143596,?143593)component) ((write:(?143596,?143593)component->?143593->?143596->?143596) (c:(?143596,?143593)component) (y:?143593) (s:?143596)) = (y:?143593)) /\\ (forall (y:?143593) (z:?143593) (s:?143596). (write:(?143596,?143593)component->?143593->?143596->?143596) (c:(?143596,?143593)component) (z:?143593) ((write:(?143596,?143593)component->?143593->?143596->?143596) (c:(?143596,?143593)component) (y:?143593) (s:?143596)) = (write:(?143596,?143593)component->?143593->?143596->?143596) (c:(?143596,?143593)component) (z:?143593) (s:?143596))"
#eval thmCheck "components.ml VALID_COMPONENT_COMPOSE" VALID_COMPONENT_COMPOSE
  "|- forall (c1:(?143649,?143652)component) (c2:(?143652,?143653)component). (valid_component:(?143649,?143652)component->bool) (c1:(?143649,?143652)component) /\\ (valid_component:(?143652,?143653)component->bool) (c2:(?143652,?143653)component) ==> (valid_component:(?143649,?143653)component->bool) ((c1:(?143649,?143652)component) :> (c2:(?143652,?143653)component))"
#eval thmCheck "components.ml EXTENSIONALLY_VALID_COMPONENT_ENTIRETY" EXTENSIONALLY_VALID_COMPONENT_ENTIRETY
  "|- (extensionally_valid_component:(?143967,?143967)component->bool) (entirety:(?143967,?143967)component)"
#eval thmCheck "components.ml orthogonal_components" orthogonal_components
  "|- (orthogonal_components:(?143987,?143991)component->(?143987,?143996)component->bool) (sc1:(?143987,?143991)component) (sc2:(?143987,?143996)component) <=> (forall (y:?143991) (z:?143996) (s:?143987). (write:(?143987,?143991)component->?143991->?143987->?143987) (sc1:(?143987,?143991)component) (y:?143991) ((write:(?143987,?143996)component->?143996->?143987->?143987) (sc2:(?143987,?143996)component) (z:?143996) (s:?143987)) = (write:(?143987,?143996)component->?143996->?143987->?143987) (sc2:(?143987,?143996)component) (z:?143996) ((write:(?143987,?143991)component->?143991->?143987->?143987) (sc1:(?143987,?143991)component) (y:?143991) (s:?143987))) /\\ (forall (y:?143991) (s:?143987). (read:(?143987,?143996)component->?143987->?143996) (sc2:(?143987,?143996)component) ((write:(?143987,?143991)component->?143991->?143987->?143987) (sc1:(?143987,?143991)component) (y:?143991) (s:?143987)) = (read:(?143987,?143996)component->?143987->?143996) (sc2:(?143987,?143996)component) (s:?143987)) /\\ (forall (z:?143996) (s:?143987). (read:(?143987,?143991)component->?143987->?143991) (sc1:(?143987,?143991)component) ((write:(?143987,?143996)component->?143996->?143987->?143987) (sc2:(?143987,?143996)component) (z:?143996) (s:?143987)) = (read:(?143987,?143991)component->?143987->?143991) (sc1:(?143987,?143991)component) (s:?143987))"
#eval thmCheck "components.ml ORTHOGONAL_COMPONENTS_SYM" ORTHOGONAL_COMPONENTS_SYM
  "|- forall (sc1:(?144074,?144073)component) (sc2:(?144074,?144075)component). (orthogonal_components:(?144074,?144073)component->(?144074,?144075)component->bool) (sc1:(?144074,?144073)component) (sc2:(?144074,?144075)component) <=> (orthogonal_components:(?144074,?144075)component->(?144074,?144073)component->bool) (sc2:(?144074,?144075)component) (sc1:(?144074,?144073)component)"

/- ---------------------------------------------------------------------- -/
/- The theorem lists (components.ml 17-50) after loading: one theorem in   -/
/- each list the file extends, none in the others.                         -/
/- ---------------------------------------------------------------------- -/
private unsafe def listCheck (lbl : String) (r : IO.Ref (List thm)) (expected : List thm) :
    IO Unit := do
  if (← r.get) == expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got {(← r.get).length} theorems"

#eval listCheck "component_read_write_thms" component_read_write_thms [READ_WRITE_ENTIRETY]
#eval listCheck "valid_component_thms" valid_component_thms [VALID_COMPONENT_ENTIRETY]
#eval listCheck "weakly_valid_component_thms" weakly_valid_component_thms
  [WEAKLY_VALID_COMPONENT_ENTIRETY]
#eval listCheck "strongly_valid_component_thms" strongly_valid_component_thms
  [STRONGLY_VALID_COMPONENT_ENTIRETY]
#eval listCheck "extensionally_valid_component_thms" extensionally_valid_component_thms
  [EXTENSIONALLY_VALID_COMPONENT_ENTIRETY]
#eval listCheck "component_alias_thms" component_alias_thms []
#eval listCheck "component_orthogonality_thms" component_orthogonality_thms []
