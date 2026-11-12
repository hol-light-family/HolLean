/- ========================================================================= -/
/- Helpers for the ANT/ translation: OCaml's `check`, `can` and `find_term` -/
/- with predicates that can fail.                                          -/
/- ========================================================================= -/
/- File: HolANT/Prelude.lean

  Lean4 translation by Chris Walton 2026

  The ANT/ proofs pick assumptions with predicates written in OCaml, such as
  `check (fun th -> is_eq(concl th) && rand(concl th) = `x:A`)`.  In OCaml a
  predicate's own failure (`rand` of a variable) is an exception that
  `check` passes on and its caller (FIRST_X_ASSUM, ...) treats as "no", and
  a quotation in it is parsed each time it runs.  So the translated
  predicates are `ExceptT String IO Bool` computations, and these are the
  lib.ml functions over them.  Not part of HOL Light; no ANT/ file has a
  counterpart.
-/

import HolMath

open HolCore HolCore.Lib HolCore.Basics HolCore.Kernel

namespace HolANT.Prelude

/-- lib.ml's `check p x`: `x` if `p x`, else failure "check"; a failure of
    `p` itself passes through. -/
def checkM {α : Type} (p : α → ExceptT String IO Bool) (x : α) : ExceptT String IO α := do
  if ← p x then pure x else throw "check"

/-- lib.ml's `can f x`: whether `f x` succeeds. -/
def canM {α β : Type} (f : α → ExceptT String IO β) (x : α) : ExceptT String IO Bool :=
  tryCatch (do let _ ← f x; pure true) (fun _ => pure false)

/-- basics.ml's `find_term p tm`, for a predicate that can fail:
    `if p tm then tm else if is_abs tm then find_term p (body tm) else if
    is_comb tm then let l,r = dest_comb tm in try find_term p l with
    Failure _ -> find_term p r else failwith "find_term"`. -/
partial def find_termM (p : term → ExceptT String IO Bool) (tm : term) : ExceptT String IO term := do
  if ← p tm then pure tm
  else if is_abs tm then find_termM p (← liftExcept (body tm))
  else if is_comb tm then
    let (l, r) ← liftExcept (dest_comb tm)
    tryCatch (find_termM p l) (fun _ => find_termM p r)
  else throw "find_term"

/-- lib.ml's `filter p l` for a predicate that can fail: `let t' = filter
    p t in if p h then h::t' else t'` (the tail first). -/
def filterM {α : Type} (p : α → ExceptT String IO Bool) : List α → ExceptT String IO (List α)
  | [] => pure []
  | h :: t => do
    let t' ← filterM p t
    if ← p h then pure (h :: t') else pure t'

/-- lib.ml's `funpow n f x` for a rule that can fail. -/
def funpowM {α : Type} : Nat → (α → ExceptT String IO α) → α → ExceptT String IO α
  | 0, _, x => pure x
  | n + 1, f, x => do funpowM n f (← f x)

/-- tactics.ml's NO_TAC. -/
def NO_TAC : HolCore.Tactics.tactic := HolCore.Tactics.NO_TAC

end HolANT.Prelude
