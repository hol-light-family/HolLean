/- File: HolTest/ArithTest.lean
Runtime test suite: arith.ml - natural number arithmetic
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- Tests: arith.ml - natural number arithmetic.                           -/
/- ---------------------------------------------------------------------- -/

/- ---------------------------------------------------------------------- -/
/- arith.ml : natural number arithmetic.                                  -/
/- A representative sample of theorems from EVERY bundle ArithThms1..9,   -/
/- the DIV/MOD characterisation theorems, and each of the three           -/
/- conversions (MOD_DOWN_CONV, NUM_CANCEL_CONV, BITS_ELIM_CONV) APPLIED to-/
/- a concrete term so it actually runs.  Gated by TestFlags.runArith.     -/
/- NOTE: conversion input terms are parsed with `parse_term` at the point -/
/- of use, because they mention constants (DIV, MOD, ...) introduced by   -/
/- definitions; a hoisted `[[ ]]` quotation parses eagerly and a name     -/
/- parses as a VARIABLE before its defining constant exists.              -/
/- ---------------------------------------------------------------------- -/

-- A representative sample of theorems from every bundle, printed as `|- ...`.
-- Each theorem this layer establishes, printed as `|- ...`.
#eval ADD_CLAUSES
#eval ADD_SYM
#eval BIT0_THM
#eval ADD1
#eval MULT_CLAUSES
#eval EXP_ADD
#eval LE_SUC
#eval MAX
#eval LE_REFL
#eval LE_TRANS
#eval NOT_LE
#eval LT_NZ
#eval LE_EXISTS
#eval num_WF
#eval num_WOP
#eval LE_INDUCT
#eval EVEN_ADD
#eval ODD_EXISTS
#eval SUB_ADD
#eval FACT_MONO
#eval LT_EXP
#eval LE_EXP
#eval EXP_MONO_LE
#eval EQ_EXP
#eval DIVISION
#eval DIVMOD_UNIQ
#eval DIV_MULT
#eval MOD_MULT
#eval DIV_MOD
#eval MOD_REFL
#eval EVEN_MOD
#eval MOD_MULT_ADD
#eval DIV_ADD_MOD
#eval DIV_EXP
#eval MOD_EXP
#eval FORALL_MOD_THM
#eval PRE_ELIM_THM
#eval SUB_ELIM_THM
#eval DIVMOD_ELIM_THM
#eval minimal
#eval MINIMAL
#eval MINIMAL_UNIQUE
#eval TRANSITIVE_STEPWISE_LT
#eval TRANSITIVE_STEPWISE_LE
#eval DEPENDENT_CHOICE_FIXED
#eval DEPENDENT_CHOICE

-- The DIV/MOD characterisation theorems specifically.
-- Each theorem this layer establishes, printed as `|- ...`.
#eval DIVISION_0
#eval DIVISION
#eval DIVISION_SIMP
#eval DIVMOD_UNIQ
#eval DIV_UNIQ
#eval MOD_UNIQ
#eval DIV_MULT
#eval MOD_MULT
#eval MOD_LT
#eval DIV_LT
#eval DIV_DIV
#eval DIV_MOD
#eval MOD_MULT_MOD

-- MOD_DOWN_CONV applied to a concrete term: combine nested MODs into one.
#eval (do
  match ← HolCore.Parser.parse_term "(x MOD n + y MOD n) MOD n" with
  | .error e => IO.println s!"MOD_DOWN_CONV parse ERR: {e}"
  | .ok tm =>
    match ← Session.MOD_DOWN_CONV tm with
    | .ok th => IO.println s!"MOD_DOWN_CONV -> {← HolCore.Printer.string_of_thm th}"
    | .error e => IO.println s!"MOD_DOWN_CONV ERR: {e}")

-- NUM_CANCEL_CONV applied to a concrete equation: cancel common summands.
#eval (do
  match ← HolCore.Parser.parse_term "a + b + c = c + d + a" with
  | .error e => IO.println s!"NUM_CANCEL_CONV parse ERR: {e}"
  | .ok tm =>
    match ← Session.NUM_CANCEL_CONV tm with
    | .ok th => IO.println s!"NUM_CANCEL_CONV -> {← HolCore.Printer.string_of_thm th}"
    | .error e => IO.println s!"NUM_CANCEL_CONV ERR: {e}")

-- BITS_ELIM_CONV applied to a concrete term: expose bit structure that is NOT
-- part of a well-formed numeral (a bare `BIT0 (BIT1 _0)` rather than a numeral).
#eval (do
  match ← Session.BITS_ELIM_CONV with
  | .error e => IO.println s!"BITS_ELIM_CONV build ERR: {e}"
  | .ok conv =>
    match ← HolCore.Parser.parse_term "BIT0(BIT1 _0) = x" with
    | .error e => IO.println s!"BITS_ELIM_CONV parse ERR: {e}"
    | .ok tm =>
      match conv tm with
      | .ok th => IO.println s!"BITS_ELIM_CONV -> {← HolCore.Printer.string_of_thm th}"
      | .error e => IO.println s!"BITS_ELIM_CONV ERR: {e}")

/- ---------------------------------------------------------------------- -/
/- arith.ml: paths the sampled-theorem tests above do not reach.          -/
/- Every ArithThms bundle IS forced by those tests (so all 262 proofs run -/
/- and a broken proof would panic), but these specific code paths were    -/
/- unexercised.  Gated by TestFlags.runArith.                             -/
/- ---------------------------------------------------------------------- -/

#eval (do
  match ← Session.LE_IMP Session.LE_ADD with
  | .ok th => IO.println s!"LE_IMP LE_ADD -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"LE_IMP ERR: {e}")

#eval (do
  match ← Session.LE_IMP Session.LE_ADDR with
  | .ok th => IO.println s!"LE_IMP LE_ADDR -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"LE_IMP LE_ADDR ERR: {e}")
-- The `minimal` BINDER SYNTAX was never parsed by any test - only the
-- theorem was printed.  `setupMinimalBinder` runs inside Ar9, so force that
-- bundle first; otherwise `parse_as_binder "minimal"` has not happened yet
-- and the parse fails with "Unparsed input following term".

#eval (do
  IO.println s!"(force Ar9: {← HolCore.Printer.string_of_thm Session.MINIMAL})"
  match ← HolCore.Parser.parse_term "minimal n. 3 < n" with
  | .ok t => IO.println s!"minimal binder parses -> {← HolCore.Printer.string_of_term t}"
  | .error e => IO.println s!"minimal binder ERR: {e}")
-- BITS_ELIM_CONV negative case: a WELL-FORMED numeral must be left alone
-- (the `is_numeral` guard).  The existing test only feeds it raw BIT0/BIT1.

#eval (do
  match ← Session.BITS_ELIM_CONV with
  | .error e => IO.println s!"BITS_ELIM factory ERR: {e}"
  | .ok cnv =>
    match ← HolCore.Parser.parse_term "12 = x" with
    | .error e => IO.println s!"parse ERR: {e}"
    | .ok t =>
      match cnv t with
      | .ok th => IO.println s!"BITS_ELIM leaves numerals alone -> {← HolCore.Printer.string_of_thm th}"
      | .error e => IO.println s!"BITS_ELIM numeral (msg): {e}")
-- NUM_CANCEL_CONV with NOTHING to cancel (the existing test only covers the
-- cancelling case).

#eval (do
  match ← HolCore.Parser.parse_term "a + b = c + d" with
  | .error e => IO.println s!"parse ERR: {e}"
  | .ok t =>
    match ← Session.NUM_CANCEL_CONV t with
    | .ok th => IO.println s!"NUM_CANCEL nothing-to-cancel -> {← HolCore.Printer.string_of_thm th}"
    | .error e => IO.println s!"NUM_CANCEL nothing-to-cancel (msg): {e}")


-- The arithmetic theorems USED to prove new goals, rather than only printed.
#eval (do
  match ← HolCore.Parser.parse_term "!m n. m + n = 0 ==> m = 0" with
  | .error e => IO.println s!"parse ERR: {e}"
  | .ok g =>
    match ← Session.prove g (Session.MESON_TAC [Session.ADD_EQ_0]) with
    | .ok th => IO.println s!"proof using ADD_EQ_0 -> {← HolCore.Printer.string_of_thm th}"
    | .error e => IO.println s!"proof using ADD_EQ_0 (msg): {e}")
-- An induction proof over the arithmetic just defined.

#eval (do
  match ← HolCore.Parser.parse_term "!n. 0 + n = n + 0" with
  | .error e => IO.println s!"parse ERR: {e}"
  | .ok g =>
    match ← Session.prove g (THEN Session.INDUCT_TAC
                               (Session.ASM_REWRITE_TAC [Session.ADD_CLAUSES])) with
    | .ok th => IO.println s!"induction over ADD -> {← HolCore.Printer.string_of_thm th}"
    | .error e => IO.println s!"induction over ADD (msg): {e}")
-- A DIV/MOD goal discharged from the characterisation theorem.

#eval (do
  match ← HolCore.Parser.parse_term "!m. ~(m = 0) ==> m MOD m = 0" with
  | .error e => IO.println s!"parse ERR: {e}"
  | .ok g =>
    match ← Session.prove g (Session.MESON_TAC [Session.MOD_REFL]) with
    | .ok th => IO.println s!"proof using MOD_REFL -> {← HolCore.Printer.string_of_thm th}"
    | .error e => IO.println s!"proof using MOD_REFL (msg): {e}")

/- ---------------------------------------------------------------------- -/
/- Every remaining theorem this layer establishes, printed as `|- ...`.   -/
/- Forcing any one of them runs the whole layer, so these also serve as   -/
/- a check that no proof in it regressed.                                 -/
/- ---------------------------------------------------------------------- -/

-- Remaining statements from arith.ml part 1 (one `#eval` each, so a
-- failure points at the individual theorem).
#eval ADD_0
#eval ADD_SUC
#eval ADD_ASSOC
#eval ADD_AC
#eval EQ_ADD_LCANCEL
#eval EQ_ADD_RCANCEL
#eval EQ_ADD_LCANCEL_0
#eval EQ_ADD_RCANCEL_0
#eval BIT1_THM
#eval ONE

-- Remaining statements from arith.ml part 2 (one `#eval` each, so a
-- failure points at the individual theorem).
#eval MULT
#eval MULT_0
#eval MULT_SUC
#eval MULT_SYM
#eval LEFT_ADD_DISTRIB
#eval RIGHT_ADD_DISTRIB
#eval MULT_ASSOC
#eval MULT_AC
#eval MULT_EQ_0
#eval EQ_MULT_LCANCEL
#eval EQ_MULT_RCANCEL
#eval MULT_2
#eval MULT_EQ_1
#eval EXP
#eval EXP_EQ_0
#eval EXP_EQ_1
#eval EXP_ZERO
#eval EXP_ONE
#eval EXP_1
#eval EXP_2
#eval MULT_EXP
#eval EXP_MULT
#eval EXP_EXP
#eval Session.LE   -- qualified: `LE` also names a Lean typeclass
#eval Session.LT   -- qualified: `LT` also names a Lean typeclass
#eval GE
#eval GT
#eval MIN
#eval LE_SUC_LT
#eval LT_SUC_LE
#eval LT_SUC
#eval LE_0

-- Remaining statements from arith.ml part 3 (one `#eval` each, so a
-- failure points at the individual theorem).
#eval LT_REFL
#eval LT_IMP_NE
#eval LE_ANTISYM
#eval LT_ANTISYM
#eval LET_ANTISYM
#eval LTE_ANTISYM
#eval LT_TRANS
#eval LET_TRANS
#eval LTE_TRANS
#eval LE_CASES
#eval LT_CASES
#eval LET_CASES
#eval LTE_CASES
#eval LE_LT
#eval LT_LE
#eval NOT_LT
#eval LT_IMP_LE
#eval EQ_IMP_LE
#eval LE_1

-- Remaining statements from arith.ml part 4 (one `#eval` each, so a
-- failure points at the individual theorem).
#eval LT_EXISTS
#eval LT_ADD
#eval LT_ADDR
#eval LE_ADD_LCANCEL
#eval LE_ADD_RCANCEL
#eval LT_ADD_LCANCEL
#eval LT_ADD_RCANCEL
#eval LE_ADD2
#eval LET_ADD2
#eval LTE_ADD2
#eval LT_ADD2
#eval LT_MULT
#eval LE_MULT2
#eval LT_LMULT
#eval LE_MULT_LCANCEL
#eval LE_MULT_RCANCEL
#eval LT_MULT_LCANCEL
#eval LT_MULT_RCANCEL
#eval LT_MULT2
#eval LE_SQUARE_REFL
#eval LT_POW2_REFL
#eval WLOG_LE
#eval WLOG_LT
#eval WLOG_LE_3
#eval num_MAX
#eval num_INDUCTION_DOWN

-- Remaining statements from arith.ml part 5 (one `#eval` each, so a
-- failure points at the individual theorem).
#eval EVEN
#eval ODD
#eval NOT_EVEN
#eval NOT_ODD
#eval EVEN_OR_ODD
#eval EVEN_AND_ODD
#eval EVEN_MULT
#eval EVEN_EXP
#eval ODD_ADD
#eval ODD_MULT
#eval ODD_EXP
#eval EVEN_DOUBLE
#eval ODD_DOUBLE
#eval EVEN_EXISTS_LEMMA
#eval EVEN_EXISTS
#eval EVEN_ODD_DECOMPOSITION
#eval SUB
#eval SUB_0
#eval SUB_PRESUC
#eval SUB_SUC
#eval SUB_REFL
#eval ADD_SUB
#eval ADD_SUB2
#eval SUB_EQ_0
#eval ADD_SUBR2
#eval ADD_SUBR
#eval SUB_ADD_LCANCEL
#eval SUB_ADD_RCANCEL
#eval LEFT_SUB_DISTRIB
#eval RIGHT_SUB_DISTRIB
#eval SUC_SUB1
#eval EVEN_SUB
#eval ODD_SUB
#eval FACT
#eval FACT_LT
#eval FACT_LE
#eval FACT_NZ

-- Remaining statements from arith.ml part 6 (one `#eval` each, so a
-- failure points at the individual theorem).
#eval EXP_LT_0
#eval EXP_MONO_LE_IMP
#eval EXP_MONO_LT_IMP
#eval EXP_MONO_LT
#eval EXP_MONO_EQ

-- Remaining statements from arith.ml part 7 (one `#eval` each, so a
-- failure points at the individual theorem).
#eval DIVMOD_EXIST
#eval DIVMOD_EXIST_0
#eval DIV_ZERO
#eval MOD_ZERO
#eval EQ_DIVMOD
#eval MOD_LT_EQ
#eval MOD_LT_EQ_LT
#eval DIVMOD_UNIQ_LEMMA
#eval DIV_0
#eval MOD_0
#eval MOD_EQ_SELF
#eval MOD_CASES
#eval MOD_ADD_CASES
#eval MOD_EQ
#eval DIV_LE
#eval DIV_MUL_LE
#eval MOD_LE_TWICE
#eval DIV_1
#eval MOD_1
#eval MOD_MOD
#eval MOD_MOD_REFL
#eval MOD_MOD_LE
#eval MOD_EVEN_2
#eval DIV_MULT2
#eval MOD_MULT2
#eval MOD_EXISTS
#eval LE_RDIV_EQ
#eval RDIV_LT_EQ
#eval LE_LDIV_EQ
#eval LDIV_LT_EQ
#eval LE_LDIV
#eval DIV_MONO
#eval DIV_MONO_LT
#eval DIV_EQ_0
#eval MOD_DIV_EQ_0
#eval MOD_EQ_0
#eval DIV_EQ_SELF

-- Remaining statements from arith.ml part 8 (one `#eval` each, so a
-- failure points at the individual theorem).
#eval ODD_MOD
#eval MOD_2_CASES
#eval EVEN_MOD_EVEN
#eval ODD_MOD_EVEN
#eval HALF_DOUBLE
#eval DOUBLE_HALF
#eval MOD_MULT_RMOD
#eval MOD_MULT_LMOD
#eval MOD_MULT_MOD2
#eval MOD_EXP_MOD
#eval DIV_MULT_ADD
#eval MOD_ADD_MOD
#eval MOD_ADD_EQ_EQ
#eval DIV_ADD_EQ_EQ
#eval DIV_ADD_EQ
#eval MOD_ADD_EQ
#eval DIV_REFL
#eval MOD_LE
#eval DIV_MONO2
#eval DIV_LE_EXCLUSION
#eval DIV_EQ_EXCLUSION
#eval MULT_DIV_LE
#eval MOD_MOD_EXP_MIN
#eval FORALL_LT_MOD_THM
#eval EXISTS_LT_MOD_THM
#eval EXISTS_MOD_THM

-- Remaining statements from arith.ml part 9 (one `#eval` each, so a
-- failure points at the individual theorem).
#eval LE_MINIMAL
#eval MINIMAL_LE
#eval MINIMAL_UBOUND
#eval MINIMAL_LBOUND
#eval MINIMAL_MONO
#eval TRANSITIVE_STEPWISE_LT_EQ
#eval TRANSITIVE_STEPWISE_LE_EQ
