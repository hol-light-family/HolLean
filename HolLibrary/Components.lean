/- ========================================================================= -/
/- General theory of state components (lenses).                              -/
/-                                                                           -/
/- This gives a hierarchical way of describing state using ":>" to compose,  -/
/- analogous to record components. The components are essentially just pairs -/
/- of reader and writer function, wrapped in a special type only for brevity -/
/- when stating component types explicitly. This idea is often called a      -/
/- "lens", (e.g. https://medium.com/javascript-scene/lenses-b85976cb0534).   -/
/-                                                                           -/
/- Ported from s2n-bignum (common/components.ml).                            -/
/- ========================================================================= -/
/- File: HolLibrary/Components.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/components.ml`, in the style of
  HolLibrary/Prime.lean: pure, the proofs translated by hand, one `let` per
  OCaml `let`, in file order.  See HolLibrary/Prime.lean for the conventions
  and HolMath/Base.lean for the tactic surface.

  Side effects come in through `ComponentsDeps` and run where the OCaml runs
  them: the type definition (58), the definitions, `parse_as_infix` for `:>`
  (118), and the `add_..._thms` calls that extend the theorem lists, whose
  references live in SessionLibrary/Components.lean.
-/

import HolMath

open HolCore HolCore.Lib
open HolCore.Kernel hiding ASSUME INST
open HolCore.Equal (ioconv lhs lhand)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolLight HolLight.Syntax

namespace HolLibrary.Components

/- ------------------------------------------------------------------------- -/
/- What components.ml uses from the core library (supplied by Session).      -/
/- ------------------------------------------------------------------------- -/

/-- The side effects, decision procedure and theorems components.ml uses. -/
structure ComponentsDeps where
  -- definitions
  new_definition : String → ExceptT String IO thm
  new_type_definition : String → String × String → thm → ExceptT String IO thm
  define : String → ExceptT String IO thm
  parse_as_infix : String × (Int × String) → IO Unit
  -- the theorem lists of components.ml 17-50
  add_component_read_write_thms : List thm → IO Unit
  add_valid_component_thms : List thm → IO Unit
  add_weakly_valid_component_thms : List thm → IO Unit
  add_strongly_valid_component_thms : List thm → IO Unit
  add_extensionally_valid_component_thms : List thm → IO Unit
  -- decision procedures
  MESON_TAC : List thm → tactic
  -- theorems
  (FUN_EQ_THM I_DEF I_THM PAIR PAIR_EQ o_DEF : thm)

/-- Everything components.ml 58-276 proves or defines. -/
structure Components where
  component_tybij : thm
  COMPONENT_INJ : thm
  FORALL_COMPONENT : thm
  EXISTS_COMPONENT : thm
  read_def : thm
  write_def : thm
  read : thm
  write : thm
  COMPONENT_EQ : thm
  entirety : thm
  READ_ENTIRETY : thm
  WRITE_ENTIRETY : thm
  READ_WRITE_ENTIRETY : thm
  component_compose : thm
  COMPONENT_COMPOSE_ASSOC : thm
  READ_COMPONENT_COMPOSE : thm
  WRITE_COMPONENT_COMPOSE : thm
  COMPOSE_ENTIRETY : thm
  READ_WRITE_COMPONENT_COMPOSE : thm
  read_over_write : thm
  write_over_write : thm
  write_over_read : thm
  weak_read_over_write : thm
  valid_component : thm
  VALID_COMPONENT_COMPOSE : thm
  VALID_COMPONENT_ENTIRETY : thm
  weakly_valid_component : thm
  VALID_IMP_WEAKLY_VALID_COMPONENT : thm
  WEAKLY_VALID_COMPONENT_ENTIRETY : thm
  strongly_valid_component : thm
  STRONGLY_VALID_IMP_VALID_COMPONENT : thm
  STRONGLY_VALID_COMPONENT_COMPOSE : thm
  STRONGLY_VALID_COMPONENT_ENTIRETY : thm
  extensionally_valid_component : thm
  STRONGLY_VALID_IMP_EXTENSIONALLY_VALID_COMPONENT : thm
  EXTENSIONALLY_VALID_COMPONENT_ENTIRETY : thm
  orthogonal_components : thm
  ORTHOGONAL_COMPONENTS_SYM : thm
  deriving Inhabited

@[nospecialize]
def setupComponents [HolBase] (D : ComponentsDeps) : ExceptT String IO Components := do
  let { new_definition, new_type_definition, define, MESON_TAC, .. } := D
  let { FUN_EQ_THM, I_DEF, I_THM, PAIR, PAIR_EQ, o_DEF, .. } := D

  /- ----------------------------------------------------------------------- -/
  /- Set up a type ":(S,V)component" for a component of type ":V" in a        -/
  /- larger state space ":S", which is really just a reader function S->V      -/
  /- and a writer function V->S->S updating the corresponding field.           -/
  /- ----------------------------------------------------------------------- -/

  let component_tybij ← do
    let th ← prove r"?rw:(S->V)#(V->S->S). T" (REWRITE_TAC [])
    REWRITE_RULE []
     (← new_type_definition "component" ("component", "dest_component") th)

  let COMPONENT_INJ ← prove
   r"!rw rw'. component rw = component rw' <=> rw = rw'"
   (MESON_TAC [component_tybij])

  let FORALL_COMPONENT ← prove
   r"(!c:(S,V)component. P c) <=> !r w. P(component(r,w))"
   (MESON_TAC [component_tybij, PAIR])

  let EXISTS_COMPONENT ← prove
   r"(?c:(S,V)component. P c) <=> ?r w. P(component(r,w))"
   (MESON_TAC [component_tybij, PAIR])

  let read_def ← new_definition
   r"read (c:(S,V)component) = FST(dest_component c)"

  let write_def ← new_definition
   r"write (c:(S,V)component) = SND(dest_component c)"

  let read ← prove
   r"!(r:S->V) w. read(component(r,w)) = r"
   (REWRITE_TAC [read_def, component_tybij])

  let write ← prove
   r"!(r:S->V) w. write(component(r,w)) = w"
   (REWRITE_TAC [write_def, component_tybij])

  let COMPONENT_EQ ← prove
   r"!c1 c2. c1 = c2 <=> read c1 = read c2 /\ write c1 = write c2"
   (REWRITE_TAC [COMPONENT_INJ, FORALL_COMPONENT, read, write, PAIR_EQ])

  /- ----------------------------------------------------------------------- -/
  /- A sort of identity for state components, corresponding to the full state. -/
  /- ----------------------------------------------------------------------- -/

  let entirety ← new_definition
   r"entirety = component((\s:S. s),(\x:S s:S. x))"

  let READ_ENTIRETY ← prove
   r"read entirety = I /\ (!s. read entirety s = s)"
   (REWRITE_TAC [read, entirety, I_THM, FUN_EQ_THM])

  let WRITE_ENTIRETY ← prove
   r"(!y. write entirety y = \s. y) /\ (!s y. write entirety y s = y)"
   (REWRITE_TAC [write, entirety, I_THM, FUN_EQ_THM])

  let READ_WRITE_ENTIRETY ← prove
   r"!y s. read entirety (write entirety y s) = y"
   (REWRITE_TAC [WRITE_ENTIRETY, READ_ENTIRETY, I_DEF])

  D.add_component_read_write_thms [READ_WRITE_ENTIRETY]

  /- ----------------------------------------------------------------------- -/
  /- Composition operation on state components.                                -/
  /- ----------------------------------------------------------------------- -/

  D.parse_as_infix (":>", (28, "right"))

  let component_compose ← new_definition
   r"(c1:(S,T)component) :> (c2:(T,U)component) =
        component((read c2 o read c1),
                  (\v s. write c1 (write c2 v (read c1 s)) s))"

  let COMPONENT_COMPOSE_ASSOC ← prove
   r"!sc1 sc2 sc3. sc1 :> (sc2 :> sc3) = (sc1 :> sc2) :> sc3"
   (REWRITE_TAC [FORALL_COMPONENT, component_compose, read, write, o_DEF])

  let READ_COMPONENT_COMPOSE ← prove
   r"!sc1 sc2 s. read (sc1 :> sc2) s = read sc2 (read sc1 s)"
   (REWRITE_TAC [FORALL_COMPONENT, read, component_compose, read, write, o_DEF])

  let WRITE_COMPONENT_COMPOSE ← prove
   r"!sc1 sc2 s x. write (sc1 :> sc2) x s =
                 write sc1 (write sc2 x (read sc1 s)) s"
   (REWRITE_TAC [FORALL_COMPONENT, read, write, component_compose])

  let COMPOSE_ENTIRETY ← prove
   r"(!c. c :> entirety = c) /\ (!c. entirety :> c = c)"
   (REWRITE_TAC [FORALL_COMPONENT, component_compose, entirety, FUN_EQ_THM,
                 read, write, COMPONENT_EQ, o_DEF])

  let READ_WRITE_COMPONENT_COMPOSE ← prove
   r"!sc1 sc2.
        (!y s. read sc1 (write sc1 y s) = y) /\
        (!y s. read sc2 (write sc2 y s) = y)
        ==> !y s. read (sc1 :> sc2) (write (sc1 :> sc2) y s) = y"
   (SIMP_TAC [READ_COMPONENT_COMPOSE, WRITE_COMPONENT_COMPOSE])

  /- ----------------------------------------------------------------------- -/
  /- Individual read-versus-write properties                                   -/
  /- ----------------------------------------------------------------------- -/

  let read_over_write ← new_definition
   r"read_over_write (c:(S,A)component) <=>
        !y s. read c (write c y s) = y"

  let write_over_write ← new_definition
   r"write_over_write (c:(S,A)component) <=>
        !y z s. write c z (write c y s) = write c z s"

  let write_over_read ← new_definition
   r"write_over_read (c:(S,A)component) <=>
     !s. write c (read c s) s = s"

  let weak_read_over_write ← new_definition
   r"weak_read_over_write (c:(S,A)component) <=>
        ?f. !y s. read c (write c y s) = f y"

  /- ----------------------------------------------------------------------- -/
  /- Valid state components.                                                   -/
  /- ----------------------------------------------------------------------- -/

  let valid_component ← define
   r"valid_component c <=>
        (!y s. read c (write c y s) = y) /\
        (!y z s. write c z (write c y s) = write c z s)"

  let VALID_COMPONENT_COMPOSE ← prove
   r"!c1 c2. valid_component c1 /\ valid_component c2
           ==> valid_component(c1 :> c2)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [valid_component] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [WRITE_COMPONENT_COMPOSE, READ_COMPONENT_COMPOSE])

  let VALID_COMPONENT_ENTIRETY ← prove
   r"valid_component entirety"
   (REWRITE_TAC [valid_component, WRITE_ENTIRETY, READ_ENTIRETY, I_DEF])

  D.add_valid_component_thms [VALID_COMPONENT_ENTIRETY]

  /- ----------------------------------------------------------------------- -/
  /- A slightly weaker version where writes may be modified (e.g. truncated).  -/
  /- ----------------------------------------------------------------------- -/

  let weakly_valid_component ← define
   r"weakly_valid_component c <=>
        (?f. !y s. read c (write c y s) = f y) /\
        (!y z s. write c z (write c y s) = write c z s)"

  let VALID_IMP_WEAKLY_VALID_COMPONENT ← prove
   r"!c:(S,V)component. valid_component c ==> weakly_valid_component c"
   (REWRITE_TAC [valid_component, weakly_valid_component] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    EXISTS_TAC (← q r"\x:V. x") THEN ASM_REWRITE_TAC [])

  let WEAKLY_VALID_COMPONENT_ENTIRETY ← prove
   r"weakly_valid_component entirety"
   (SIMP_TAC [VALID_IMP_WEAKLY_VALID_COMPONENT, VALID_COMPONENT_ENTIRETY])

  D.add_weakly_valid_component_thms [WEAKLY_VALID_COMPONENT_ENTIRETY]

  /- ----------------------------------------------------------------------- -/
  /- A stronger notion more in line with our expectations.                     -/
  /- ----------------------------------------------------------------------- -/

  let strongly_valid_component ← define
   r"strongly_valid_component c <=>
        (!y s. read c (write c y s) = y) /\
        (!s. write c (read c s) s = s) /\
        (!y z s. write c z (write c y s) = write c z s)"

  let STRONGLY_VALID_IMP_VALID_COMPONENT ← prove
   r"!c:(S,V)component. strongly_valid_component c ==> valid_component c"
   (SIMP_TAC [valid_component, strongly_valid_component])

  let STRONGLY_VALID_COMPONENT_COMPOSE ← prove
   r"!c1 c2. strongly_valid_component c1 /\ strongly_valid_component c2
           ==> strongly_valid_component(c1 :> c2)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [strongly_valid_component] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [WRITE_COMPONENT_COMPOSE, READ_COMPONENT_COMPOSE])

  let STRONGLY_VALID_COMPONENT_ENTIRETY ← prove
   r"strongly_valid_component entirety"
   (REWRITE_TAC [strongly_valid_component, READ_ENTIRETY, WRITE_ENTIRETY])

  D.add_strongly_valid_component_thms [STRONGLY_VALID_COMPONENT_ENTIRETY]

  /- ----------------------------------------------------------------------- -/
  /- And likewise a version of that allowing write truncation.                 -/
  /- ----------------------------------------------------------------------- -/

  let extensionally_valid_component ← define
   r"extensionally_valid_component (c:(S,A)component) <=>
        (?f. !y s. read c (write c y s) = f y) /\
        (!s. write c (read c s) s = s) /\
        (!y z s. write c z (write c y s) = write c z s)"

  let STRONGLY_VALID_IMP_EXTENSIONALLY_VALID_COMPONENT ← prove
   r"!c:(S,V)component.
        strongly_valid_component c ==> extensionally_valid_component c"
   (REWRITE_TAC [extensionally_valid_component, strongly_valid_component] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    EXISTS_TAC (← q r"\x:V. x") THEN ASM_REWRITE_TAC [])

  let EXTENSIONALLY_VALID_COMPONENT_ENTIRETY ← prove
   r"extensionally_valid_component entirety"
   (SIMP_TAC [STRONGLY_VALID_COMPONENT_ENTIRETY,
              STRONGLY_VALID_IMP_EXTENSIONALLY_VALID_COMPONENT])

  D.add_extensionally_valid_component_thms
    [EXTENSIONALLY_VALID_COMPONENT_ENTIRETY]

  /- ----------------------------------------------------------------------- -/
  /- General independence/orthogonality of state components.                   -/
  /- ----------------------------------------------------------------------- -/

  let orthogonal_components ← define
   r"orthogonal_components sc1 sc2 <=>
        (!y z s. write sc1 y (write sc2 z s) =
                 write sc2 z (write sc1 y s)) /\
        (!y s. read sc2 (write sc1 y s) = read sc2 s) /\
        (!z s. read sc1 (write sc2 z s) = read sc1 s)"

  let ORTHOGONAL_COMPONENTS_SYM ← prove
   r"!sc1 sc2. orthogonal_components sc1 sc2 <=> orthogonal_components sc2 sc1"
   (REWRITE_TAC [orthogonal_components] THEN MESON_TAC [])

  return {
    component_tybij, COMPONENT_INJ, FORALL_COMPONENT, EXISTS_COMPONENT,
    read_def, write_def, read, write, COMPONENT_EQ,
    entirety, READ_ENTIRETY, WRITE_ENTIRETY, READ_WRITE_ENTIRETY,
    component_compose, COMPONENT_COMPOSE_ASSOC, READ_COMPONENT_COMPOSE,
    WRITE_COMPONENT_COMPOSE, COMPOSE_ENTIRETY, READ_WRITE_COMPONENT_COMPOSE,
    read_over_write, write_over_write, write_over_read, weak_read_over_write,
    valid_component, VALID_COMPONENT_COMPOSE, VALID_COMPONENT_ENTIRETY,
    weakly_valid_component, VALID_IMP_WEAKLY_VALID_COMPONENT,
    WEAKLY_VALID_COMPONENT_ENTIRETY,
    strongly_valid_component, STRONGLY_VALID_IMP_VALID_COMPONENT,
    STRONGLY_VALID_COMPONENT_COMPOSE, STRONGLY_VALID_COMPONENT_ENTIRETY,
    extensionally_valid_component,
    STRONGLY_VALID_IMP_EXTENSIONALLY_VALID_COMPONENT,
    EXTENSIONALLY_VALID_COMPONENT_ENTIRETY,
    orthogonal_components, ORTHOGONAL_COMPONENTS_SYM }

end HolLibrary.Components
