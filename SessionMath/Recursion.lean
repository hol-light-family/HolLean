/- File: SessionMath/Recursion.lean
recursion.ml: primitive recursive definitions over the stored recursion
theorems (`new_recursive_definition` and `theRecursiveDefinitions`).
-/
import SessionMath.Nums
import HolMath.Recursion

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Simp HolCore.Theorems HolCore.Classic

namespace Session

initialize theRecursiveDefinitions : IO.Ref (List thm) ← IO.mkRef []

/-- `prove_canon_recursive_functions_exist ax tm`. -/
def prove_canon_recursive_functions_exist (ax : thm) (tm : term) :
    IO (Except String thm) :=
  HolMath.Recursion.prove_canon_recursive_functions_exist ax tm

/-- `prove_raw_recursive_functions_exist ax tm`. -/
def prove_raw_recursive_functions_exist (ax : thm) (tm : term) :
    IO (Except String thm) :=
  HolMath.Recursion.prove_raw_recursive_functions_exist ax tm

/-- `prove_recursive_functions_exist ax tm`. -/
def prove_recursive_functions_exist (ax : thm) (tm : term) :
    IO (Except String thm) :=
  HolMath.Recursion.prove_recursive_functions_exist T.BETA_THM ax tm

def new_recursive_definition (ax : thm) (tm : term) : IO (Except String thm) := do
  let existing ← theRecursiveDefinitions.get
  match ← HolMath.Recursion.new_recursive_definition_core T.BETA_THM
             new_specification existing ax tm with
  | .error e => return .error e
  | .ok (th, entry) => do
      match entry with
      | some t => theRecursiveDefinitions.set (t :: existing)
      | none => pure ()
      return .ok th

end Session
