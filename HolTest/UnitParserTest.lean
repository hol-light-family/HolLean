/- File: HolTest/UnitParserTest.lean
Runtime test suite: HOL Light's own UnitTests/parser_tests.ml, translated
assertion by assertion, in file order.  Each OCaml `assert` becomes one
`-> OK` / `-> MISMATCH` line.  Every assertion passes in real HOL Light.
Part of the Lean4 translation of HOL Light by Chris Walton 2026. -/

/- ========================================================================= -/
/-                   HOL Light parser and typechecker tests                  -/
/-                                                                           -/
/-  Checks that quotations are parsed and typechecked into the expected      -/
/-  terms, exercising the preterm typing pass in preterm.ml (variable versus -/
/-  constant resolution, varstructs, type annotations, interface mapping).   -/
/- ========================================================================= -/

import HolTest.CommonTest

open HolCore.Kernel HolTest.CommonTest

namespace HolTest.UnitParserTest
open Session
open HolCore.Basics (bndvar)
open HolCore.Equal (lhand)

private def ok (lbl : String) (b : Bool) : IO Unit :=
  IO.println (if b then s!"{lbl} -> OK" else s!"{lbl} -> MISMATCH")

private def pt (s : String) : IO term := do
  match ← HolCore.Parser.parse_term s with
  | .ok t => pure t
  | .error e => throw (IO.userError s!"parse `{s}`: {e}")

/-- Run an assertion; an exception is a MISMATCH. -/
private def run (lbl : String) (act : IO Bool) : IO Unit := do
  try ok lbl (← act) catch e => IO.println s!"{lbl} -> MISMATCH {e}"

private def get (r : Except String α) : IO α := IO.ofExcept r

/- ------------------------------------------------------------------------- -/
/- A binder may shadow a constant of the same name, even when type-annotated -/
/- or part of a tuple varstruct (see varstruct_consts and the Absp branch in -/
/- preterm.ml). Without the fix the first quotation below raises             -/
/- "shadow_test_const has type bool, it cannot be used with type num".       -/
/- ------------------------------------------------------------------------- -/

#eval (do
  ensureHolPrefixThroughInt
  -- a constant of type bool
  run "new_definition shadow_test_const = T" (do
    let _ ← get (← new_definition (← pt "shadow_test_const = T")); pure true)
  -- An annotated binder shadows the constant: the bound variable has the
  -- annotated type, not the constant's bool type.
  run "annotated binder has the annotated type" (do
    let tm ← pt "forall (shadow_test_const:num). shadow_test_const > 0"
    let v ← get (bndvar (← get (rand tm)))
    pure (is_var v && type_of v == (← get (← HolCore.Parser.parse_type "num"))))
  -- Tuple varstructs are handled too.
  run "tuple varstruct" (do
    pure (aconv (← pt "\\(shadow_test_const:num,y:num). shadow_test_const + y")
                (← pt "\\(a:num,b:num). a + b")))
  -- A free occurrence of the same name still resolves to the constant.
  run "free occurrence is the constant" (do
    pure (is_const (← get (lhand
      (← pt "shadow_test_const /\\ (?(shadow_test_const:num). shadow_test_const > 0)")))))
  : IO Unit)

/- The same holds for an interface or overloaded name such as "gcd" or "sum",  -/
/- which is not itself a constant but is still parsed as one.                  -/

#eval (do
  ensureHolPrefixThroughInt
  let _ ← get (← new_definition (← pt "shadow_test_num (n:num) = n + 1"))
  let _ ← get (← make_overloadable "shadow_test_op"
                   (← get (← HolCore.Parser.parse_type "A->A")))
  let _ ← get (← overload_interface "shadow_test_op" (← pt "shadow_test_num"))
  run "\\shadow_test_op. T is an abstraction" (do pure (is_abs (← pt "\\shadow_test_op. T")))
  run "annotated overloaded binder" (do
    pure (aconv (← pt "\\(shadow_test_op:num). shadow_test_op + 1") (← pt "\\(x:num). x + 1")))
  run "tuple overloaded binder" (do
    pure (aconv (← pt "\\(shadow_test_op:num,y:num). shadow_test_op + y")
                (← pt "\\(a:num,b:num). a + b")))
  run "free overloaded name is the constant" (do
    let tm ← pt "shadow_test_op (x:num) = (\\shadow_test_op. shadow_test_op) x"
    pure (is_const (← get (rator (← get (lhand tm))))))
  -- With the flag off, such a binder is a degenerate generalized abstraction.
  HolCore.Preterm.ignore_constant_varstruct.set false
  run "flag off: degenerate generalized abstractions" (do
    pure (!(is_abs (← pt "\\shadow_test_const. T")) &&
          !(is_abs (← pt "\\shadow_test_op. T"))))
  HolCore.Preterm.ignore_constant_varstruct.set true
  : IO Unit)

end HolTest.UnitParserTest
