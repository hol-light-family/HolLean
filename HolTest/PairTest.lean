/- File: HolTest/PairTest.lean
Runtime test suite: pair.ml - pairing theory and syntax sugar
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- Tests: pair.ml - pairing theory and syntax sugar.                      -/
/- ---------------------------------------------------------------------- -/


-- ========================================================================
-- pair.ml : pairing theory.  Forcing any Pair theorem forces `Session.Pr`,
-- which runs the `prod` type definition, all pairing definitions, and the
-- ~33 `setupPair` proofs.  A failure would surface as a panic here.
-- Gated by TestFlags.runPair.
-- ========================================================================
#eval (do
  IO.println s!"FST -> {← HolCore.Printer.string_of_thm Session.FST}")

#eval (do
  IO.println s!"SND -> {← HolCore.Printer.string_of_thm Session.SND}")

#eval (do
  IO.println s!"PAIR -> {← HolCore.Printer.string_of_thm Session.PAIR}")

#eval (do
  IO.println s!"PAIR_EQ -> {← HolCore.Printer.string_of_thm Session.PAIR_EQ}")

#eval (do
  IO.println s!"pair_INDUCT -> {← HolCore.Printer.string_of_thm Session.pair_INDUCT}")

#eval (do
  IO.println s!"FORALL_PAIR_THM -> {← HolCore.Printer.string_of_thm Session.FORALL_PAIR_THM}")
-- Prove `FST(a,b) = a` and `SND(a,b) = b` from the basic rewrites.

#eval (do
  match ← prove ([[ FST ((a:A),(b:B)) = a ]]) (Session.REWRITE_TAC []) with
  | .ok th => IO.println s!"FST(a,b)=a -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"FST(a,b)=a ERR: {e}")

#eval (do
  match ← prove ([[ SND ((a:A),(b:B)) = b ]]) (Session.REWRITE_TAC []) with
  | .ok th => IO.println s!"SND(a,b)=b -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"SND(a,b)=b ERR: {e}")


-- GEN_BETA_CONV on a paired-abstraction redex (prod is in the store by now).
#eval (do
  match ← Session.GEN_BETA_CONV ([[ (\(a:A,b:B). (f:A->B->C) a b) (u,v) ]]) with
  | .ok th => IO.println s!"GEN_BETA_CONV uncurry -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"GEN_BETA_CONV uncurry ERR: {e}")

#eval (do
  match ← Session.GEN_BETA_CONV ([[ (\(x:A,y:B). x) (p,q) ]]) with
  | .ok th => IO.println s!"GEN_BETA_CONV fst -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"GEN_BETA_CONV fst ERR: {e}")
-- Depairing new_definition: CURRY/UNCURRY/PASSOC (forces curryDefs).

#eval (do
  IO.println s!"CURRY_DEF -> {← HolCore.Printer.string_of_thm Session.CURRY_DEF}")

#eval (do
  IO.println s!"UNCURRY_DEF -> {← HolCore.Printer.string_of_thm Session.UNCURRY_DEF}")

#eval (do
  IO.println s!"PASSOC_DEF -> {← HolCore.Printer.string_of_thm Session.PASSOC_DEF}")
-- let_CONV: expand a let-term.

#eval (do
  match ← Session.let_CONV ([[ let x = a in (f:A->bool) x ]]) with
  | .ok th => IO.println s!"let_CONV -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"let_CONV ERR: {e}")
-- let_CONV over a paired let with a literal pair argument.

#eval (do
  match ← Session.let_CONV ([[ let (x,y) = (a,b) in (g:A->B->bool) x y ]]) with
  | .ok th => IO.println s!"let_CONV paired -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"let_CONV paired ERR: {e}")
-- LET_TAC: abbreviate the let, then discharge with the assumption.

#eval (do
  match ← prove ([[ (let x = a in (f:A->bool) x) <=> f a ]])
            (THEN Session.LET_TAC (Session.ASM_REWRITE_TAC [])) with
  | .ok th => IO.println s!"LET_TAC -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"LET_TAC (msg): {e}")
-- SUBLET_CONV: apply a conversion to the RHS of a toplevel let.

#eval (do
  match ← Session.SUBLET_CONV (fun t => pure (.ok (REFL t)))
            ([[ let x = a in (f:A->bool) x ]]) with
  | .ok th => IO.println s!"SUBLET_CONV -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"SUBLET_CONV (msg): {e}")
-- Syntax ops: is_pair / dest_pair / mk_pair.

#eval (do
  let ab := [[ ((a:A),(b:B)) ]]
  IO.println s!"is_pair (a,b) = {Session.is_pair ab}"
  match Session.dest_pair ab with
  | .ok (l, r) => IO.println s!"dest_pair (a,b) = ({← HolCore.Printer.string_of_term l}, {← HolCore.Printer.string_of_term r})"
  | .error e => IO.println s!"dest_pair ERR: {e}"
  match ← Session.mk_pair ([[ (u:A) ]], [[ (v:B) ]]) with
  | .ok pr => IO.println s!"mk_pair (u,v) = {← HolCore.Printer.string_of_term pr}"
  | .error e => IO.println s!"mk_pair ERR: {e}")
-- The pairing theorems used in real proofs.

#eval (do
  match ← prove ([[ !p:A#B. p = (FST p, SND p) ]])
            (THEN Session.GEN_TAC (Session.REWRITE_TAC [])) with
  | .ok th => IO.println s!"p=(FST p,SND p) -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"p=(FST p,SND p) (msg): {e}")

#eval (do
  match ← prove ([[ ((a:A),(b:B)) = (a,b) <=> T ]]) (Session.REWRITE_TAC []) with
  | .ok th => IO.println s!"PAIR_EQ use -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"PAIR_EQ use (msg): {e}")
-- CURRY/UNCURRY round-trip via the definitions.

#eval (do
  match ← prove ([[ !f:A->B->C. !x y. UNCURRY f (x,y) = f x y ]])
            (Session.REWRITE_TAC [Session.UNCURRY_DEF]) with
  | .ok th => IO.println s!"UNCURRY use -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"UNCURRY use (msg): {e}")

/- ---------------------------------------------------------------------- -/
/- Every remaining theorem this layer establishes, printed as `|- ...`.   -/
/- Forcing any one of them runs the whole layer, so these also serve as   -/
/- a check that no proof in it regressed.                                 -/
/- ---------------------------------------------------------------------- -/

-- Remaining statements from the pair.ml definitions (one `#eval` each, so a
-- failure points at the individual theorem).
#eval LET_END_DEF
#eval GABS_DEF
#eval GEQ_DEF
#eval mk_pair_def
#eval prod_tybij
#eval COMMA_DEF
#eval FST_DEF
#eval SND_DEF
