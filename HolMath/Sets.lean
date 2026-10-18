/- File: Sets.lean
Very basic set theory (using predicates as sets).

Original       John Harrison, University of Cambridge Computer Laboratory
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2016
Original (c) Copyright, Marco Maggesi 2012-2017
Original (c) Copyright, Andrea Gabrielli 2012-2017
Lean4 translation by Chris Walton 2026

A set of `:A` is just a predicate `A->bool`: `x IN s` unfolds to `s x` and
extensionality is function extensionality.
-/

import HolMath.Int
import HolMath.Base

namespace HolMath.Sets

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax

/- ---------------------------------------------------------------------- -/
/- Infix symbols for set operations.  (sets.ml 15-32)                     -/
/- ---------------------------------------------------------------------- -/

/-- Register the fourteen infix operators declared at the head of `sets.ml`
    (sets.ml 18-32): IN, SUBSET, PSUBSET, INTER, UNION, DIFF, INSERT, DELETE,
    HAS_SIZE and the five cardinal comparisons.  Must run once, before any term
    using these symbols is parsed. -/
def setupSetsInfixes : IO Unit := do
  -- sets.ml 18-25: the eight core set operators.
  HolCore.Printer.parse_as_infix ("IN", (11, "right"))
  HolCore.Printer.parse_as_infix ("SUBSET", (12, "right"))
  HolCore.Printer.parse_as_infix ("PSUBSET", (12, "right"))
  HolCore.Printer.parse_as_infix ("INTER", (20, "right"))
  HolCore.Printer.parse_as_infix ("UNION", (16, "right"))
  HolCore.Printer.parse_as_infix ("DIFF", (18, "left"))
  HolCore.Printer.parse_as_infix ("INSERT", (21, "right"))
  HolCore.Printer.parse_as_infix ("DELETE", (21, "left"))
  -- sets.ml 27-32: HAS_SIZE and the five cardinal comparisons.
  HolCore.Printer.parse_as_infix ("HAS_SIZE", (12, "right"))
  HolCore.Printer.parse_as_infix ("<=_c", (12, "right"))
  HolCore.Printer.parse_as_infix ("<_c", (12, "right"))
  HolCore.Printer.parse_as_infix (">=_c", (12, "right"))
  HolCore.Printer.parse_as_infix (">_c", (12, "right"))
  HolCore.Printer.parse_as_infix ("=_c", (12, "right"))

/- ---------------------------------------------------------------------- -/
/- Set membership and the core set definitions.  (sets.ml 34-170)         -/
/- ---------------------------------------------------------------------- -/

/-- The core definitions and few proofs of sets.ml 34-170: `IN`, `EXTENSION`,
    `GSPEC`, `SETSPEC`, `IN_ELIM_THM`, `EMPTY`, `INSERT_DEF`, `UNIV`, `UNION`,
    `UNIONS`, `INTER`, `INTERS`, `DIFF`, `INSERT`, `DELETE`, `SUBSET`,
    `PSUBSET`, `DISJOINT`, `SING`, the `FINITE` inductive triple, `INFINITE`,
    `IMAGE`, `INJ`, `SURJ`, `BIJ`, `CHOICE` and `REST`.

    The parser desugars `{a,b,c}` into an `INSERT`/`EMPTY` chain and `{x | P}`
    into `GSPEC (\v. ... SETSPEC v ...)` as free variables, so these constants
    must be introduced before any definition whose body uses that syntax.  The
    textual order of `sets.ml` is already a valid order, so this stage follows
    it verbatim.  The layer stays pure, threading `new_definition` and
    `new_inductive_definition` in as parameters (the mutable side effect lives
    in Session.lean).

    Takes `MESON_TAC` (for `IN_ELIM_THM`), `new_definition` and
    `new_inductive_definition` (for the `FINITE` triple). -/
structure SetsCore where
  /-- `IN` (sets.ml 38): `!P:A->bool. !x. x IN P <=> P x`. -/
  IN : thm
  /-- `EXTENSION` (sets.ml 45): `!s t. (s = t) <=> !x:A. x IN s <=> x IN t`. -/
  EXTENSION : thm
  /-- `GSPEC` (sets.ml 53): `GSPEC (p:A->bool) = p`. -/
  GSPEC : thm
  /-- `SETSPEC` (sets.ml 56): `SETSPEC (v:A) P t <=> P /\ (v = t)`. -/
  SETSPEC : thm
  /-- `IN_ELIM_THM` (sets.ml 63): the FIVE-conjunct set-comprehension
      membership rewrite. -/
  IN_ELIM_THM : thm
  /-- `EMPTY` (sets.ml 77): `EMPTY = (\x:A. F)`. -/
  EMPTY : thm
  /-- `INSERT_DEF` (sets.ml 80): `x INSERT s = \y:A. y IN s \/ (y = x)`. -/
  INSERT_DEF : thm
  /-- `UNIV` (sets.ml 87): `UNIV = (\x:A. T)`. -/
  UNIV : thm
  /-- `UNION` (sets.ml 90): `s UNION t = {x:A | x IN s \/ x IN t}`. -/
  UNION : thm
  /-- `UNIONS` (sets.ml 93): `UNIONS s = {x:A | ?u. u IN s /\ x IN u}`. -/
  UNIONS : thm
  /-- `INTER` (sets.ml 96): `s INTER t = {x:A | x IN s /\ x IN t}`. -/
  INTER : thm
  /-- `INTERS` (sets.ml 99): `INTERS s = {x:A | !u. u IN s ==> x IN u}`. -/
  INTERS : thm
  /-- `DIFF` (sets.ml 102): `s DIFF t = {x:A | x IN s /\ ~(x IN t)}`. -/
  DIFF : thm
  /-- `INSERT` (sets.ml 105): a PROVE, NOT a definition -
      `x INSERT s = {y:A | y IN s \/ (y = x)}`. -/
  INSERT : thm
  /-- `DELETE` (sets.ml 109): `s DELETE x = {y:A | y IN s /\ ~(y = x)}`. -/
  DELETE : thm
  /-- `SUBSET` (sets.ml 116): `s SUBSET t <=> !x:A. x IN s ==> x IN t`. -/
  SUBSET : thm
  /-- `PSUBSET` (sets.ml 119):
      `(s:A->bool) PSUBSET t <=> s SUBSET t /\ ~(s = t)`. -/
  PSUBSET : thm
  /-- `DISJOINT` (sets.ml 122):
      `DISJOINT (s:A->bool) t <=> (s INTER t = EMPTY)`. -/
  DISJOINT : thm
  /-- `SING` (sets.ml 125): `SING s = ?x:A. s = {x}`. -/
  SING : thm
  /-- `FINITE_RULES` (sets.ml 132): the rule theorem of the `FINITE`
      inductive definition. -/
  FINITE_RULES : thm
  /-- `FINITE_INDUCT` (sets.ml 132): the induction theorem of `FINITE`. -/
  FINITE_INDUCT : thm
  /-- `FINITE_CASES` (sets.ml 132): the cases theorem of `FINITE`. -/
  FINITE_CASES : thm
  /-- `INFINITE` (sets.ml 137): `INFINITE (s:A->bool) <=> ~(FINITE s)`. -/
  INFINITE : thm
  /-- `IMAGE` (sets.ml 144):
      `IMAGE (f:A->B) s = { y | ?x. x IN s /\ (y = f x)}`. -/
  IMAGE : thm
  /-- `INJ` (sets.ml 147): the injectivity predicate. -/
  INJ : thm
  /-- `SURJ` (sets.ml 152): the surjectivity predicate. -/
  SURJ : thm
  /-- `BIJ` (sets.ml 157): `BIJ (f:A->B) s t <=> INJ f s t /\ SURJ f s t`. -/
  BIJ : thm
  /-- `CHOICE` (sets.ml 164): `CHOICE s = @x:A. x IN s`. -/
  CHOICE : thm
  /-- `REST` (sets.ml 167): `REST (s:A->bool) = s DELETE (CHOICE s)`. -/
  REST : thm
  deriving Inhabited

/-- The core definitions of sets.ml 34-170, in file order; that order is
    the one the parser needs (see `SetsCore`). -/
@[nospecialize]
def setupSetsCore [HolBase]
    (MESON_TAC : List thm → tactic)
    (new_definition' : term → IO (Except String thm))
    (new_inductive_definition' : term → IO (Except String (thm × thm × thm))) :
    ExceptT String IO SetsCore := do
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let new_inductive_definition (s : String) :
      ExceptT String IO (thm × thm × thm) := do
    new_inductive_definition' (← q s)
  let { FUN_EQ_THM, .. } := HolBase.C

  /- Set membership. -/

  let IN ← new_definition
   r"!P:A->bool. !x. x IN P <=> P x"

  /- Axiom of extensionality in this framework. -/

  let EXTENSION ← prove
   r"!s t. (s = t) <=> !x:A. x IN s <=> x IN t"
   (REWRITE_TAC [IN, FUN_EQ_THM])

  /- General specification. -/

  let GSPEC ← new_definition
   r"GSPEC (p:A->bool) = p"

  let SETSPEC ← new_definition
   r"SETSPEC (v:A) P t <=> P /\ (v = t)"

  /- Rewrite rule for eliminating set-comprehension membership assertions. -/

  let IN_ELIM_THM ← prove
   r"(!P x:A. x IN GSPEC (\v. P (SETSPEC v)) <=> P (\p t. p /\ (x = t))) /\
   (!p x:A. x IN GSPEC (\v. ?y. SETSPEC v (p y) y) <=> p x) /\
   (!P x:A. GSPEC (\v. P (SETSPEC v)) x <=> P (\p t. p /\ (x = t))) /\
   (!p x:A. GSPEC (\v. ?y. SETSPEC v (p y) y) x <=> p x) /\
   (!p x:A. x IN (\y. p y) <=> p x)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [IN, GSPEC] THEN
    TRY (AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM]) THEN
    REWRITE_TAC [SETSPEC] THEN MESON_TAC [])

  /- These two definitions are needed first, for the parsing of enumerations. -/

  let EMPTY ← new_definition
   r"EMPTY = (\x:A. F)"

  let INSERT_DEF ← new_definition
   r"x INSERT s = \y:A. y IN s \/ (y = x)"

  /- The other basic operations. -/

  let UNIV ← new_definition
   r"UNIV = (\x:A. T)"

  let UNION ← new_definition
   r"s UNION t = {x:A | x IN s \/ x IN t}"

  let UNIONS ← new_definition
   r"UNIONS s = {x:A | ?u. u IN s /\ x IN u}"

  let INTER ← new_definition
   r"s INTER t = {x:A | x IN s /\ x IN t}"

  let INTERS ← new_definition
   r"INTERS s = {x:A | !u. u IN s ==> x IN u}"

  let DIFF ← new_definition
   r"s DIFF t =  {x:A | x IN s /\ ~(x IN t)}"

  let INSERT ← prove
   r"x INSERT s = {y:A | y IN s \/ (y = x)}"
   (REWRITE_TAC [EXTENSION, INSERT_DEF, IN_ELIM_THM])

  let DELETE ← new_definition
   r"s DELETE x = {y:A | y IN s /\ ~(y = x)}"

  /- Other basic predicates. -/

  let SUBSET ← new_definition
   r"s SUBSET t <=> !x:A. x IN s ==> x IN t"

  let PSUBSET ← new_definition
   r"(s:A->bool) PSUBSET t <=> s SUBSET t /\ ~(s = t)"

  let DISJOINT ← new_definition
   r"DISJOINT (s:A->bool) t <=> (s INTER t = EMPTY)"

  let SING ← new_definition
   r"SING s = ?x:A. s = {x}"

  /- Finiteness. -/

  let (FINITE_RULES, FINITE_INDUCT, FINITE_CASES) ←
    new_inductive_definition
     r"FINITE (EMPTY:A->bool) /\
     !(x:A) s. FINITE s ==> FINITE (x INSERT s)"

  let INFINITE ← new_definition
   r"INFINITE (s:A->bool) <=> ~(FINITE s)"

  /- Stuff concerned with functions. -/

  let IMAGE ← new_definition
   r"IMAGE (f:A->B) s = { y | ?x. x IN s /\ (y = f x)}"

  let INJ ← new_definition
   r"INJ (f:A->B) s t <=>
     (!x. x IN s ==> (f x) IN t) /\
     (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))"

  let SURJ ← new_definition
   r"SURJ (f:A->B) s t <=>
     (!x. x IN s ==> (f x) IN t) /\
     (!x. (x IN t) ==> ?y. y IN s /\ (f y = x))"

  let BIJ ← new_definition
   r"BIJ (f:A->B) s t <=> INJ f s t /\ SURJ f s t"

  /- Another funny thing. -/

  let CHOICE ← new_definition
   r"CHOICE s = @x:A. x IN s"

  let REST ← new_definition
   r"REST (s:A->bool) = s DELETE (CHOICE s)"

  return {
    IN, EXTENSION, GSPEC, SETSPEC, IN_ELIM_THM, EMPTY, INSERT_DEF, UNIV, UNION,
    UNIONS, INTER, INTERS, DIFF, INSERT, DELETE, SUBSET, PSUBSET, DISJOINT,
    SING, FINITE_RULES, FINITE_INDUCT, FINITE_CASES, INFINITE, IMAGE, INJ,
    SURJ, BIJ, CHOICE, REST }

/- ---------------------------------------------------------------------- -/
/- Basic membership properties.  (sets.ml 171-308)                        -/
/- ---------------------------------------------------------------------- -/

/-- The twenty-four "basic membership properties" of sets.ml 171-308.  These
    are SET_TAC's raw material: SET_TAC (sets.ml 320) rewrites with a fixed
    list of membership lemmas before handing the goal to MESON, and twelve of
    the twenty-five it uses live here (`NOT_IN_EMPTY`, `IN_UNIV`, `IN_UNION`,
    `IN_INTER`, `IN_DIFF`, `IN_INSERT`, `IN_DELETE`, `IN_REST`, `IN_INTERS`,
    `IN_UNIONS`, `IN_IMAGE`, plus the GSPEC/IMAGE forms `UNIONS_IMAGE`,
    `INTERS_IMAGE`, `UNIONS_GSPEC`, `INTERS_GSPEC`).  Ordinary proofs over the
    `SetsCore` constants (`S`), using `T` (for `CONJ_SYM`/`DISJ_SYM`) and
    `MESON_TAC`. -/
structure SetsProps where
  /-- `NOT_IN_EMPTY` (sets.ml 174): `!x:A. ~(x IN EMPTY)`. -/
  NOT_IN_EMPTY : thm
  /-- `IN_UNIV` (sets.ml 178): `!x:A. x IN UNIV`. -/
  IN_UNIV : thm
  /-- `IN_UNION` (sets.ml 182):
      `!s t (x:A). x IN (s UNION t) <=> x IN s \/ x IN t`. -/
  IN_UNION : thm
  /-- `IN_UNIONS` (sets.ml 186):
      `!s (x:A). x IN (UNIONS s) <=> ?t. t IN s /\ x IN t`. -/
  IN_UNIONS : thm
  /-- `IN_INTER` (sets.ml 190):
      `!s t (x:A). x IN (s INTER t) <=> x IN s /\ x IN t`. -/
  IN_INTER : thm
  /-- `IN_INTERS` (sets.ml 194):
      `!s (x:A). x IN (INTERS s) <=> !t. t IN s ==> x IN t`. -/
  IN_INTERS : thm
  /-- `IN_DIFF` (sets.ml 198):
      `!(s:A->bool) t x. x IN (s DIFF t) <=> x IN s /\ ~(x IN t)`. -/
  IN_DIFF : thm
  /-- `IN_INSERT` (sets.ml 202):
      `!x:A. !y s. x IN (y INSERT s) <=> (x = y) \/ x IN s`. -/
  IN_INSERT : thm
  /-- `IN_DELETE` (sets.ml 206):
      `!s. !x:A. !y. x IN (s DELETE y) <=> x IN s /\ ~(x = y)`. -/
  IN_DELETE : thm
  /-- `IN_SING` (sets.ml 210): `!x y. x IN {y:A} <=> (x = y)`. -/
  IN_SING : thm
  /-- `IN_IMAGE` (sets.ml 214):
      `!y:B. !s f. (y IN (IMAGE f s)) <=> ?x:A. (y = f x) /\ x IN s`. -/
  IN_IMAGE : thm
  /-- `IN_REST` (sets.ml 218):
      `!x:A. !s. x IN (REST s) <=> x IN s /\ ~(x = CHOICE s)`. -/
  IN_REST : thm
  /-- `FORALL_IN_INSERT` (sets.ml 222):
      `!P a s. (!x:A. x IN (a INSERT s) ==> P x) <=>
               P a /\ (!x. x IN s ==> P x)`. -/
  FORALL_IN_INSERT : thm
  /-- `EXISTS_IN_INSERT` (sets.ml 226):
      `!P a s. (?x:A. x IN (a INSERT s) /\ P x) <=>
               P a \/ ?x. x IN s /\ P x`. -/
  EXISTS_IN_INSERT : thm
  /-- `FORALL_IN_UNION` (sets.ml 230):
      `!P s t:A->bool. (!x. x IN s UNION t ==> P x) <=>
       (!x. x IN s ==> P x) /\ (!x. x IN t ==> P x)`. -/
  FORALL_IN_UNION : thm
  /-- `EXISTS_IN_UNION` (sets.ml 236):
      `!P s t:A->bool. (?x. x IN s UNION t /\ P x) <=>
       (?x. x IN s /\ P x) \/ (?x. x IN t /\ P x)`. -/
  EXISTS_IN_UNION : thm
  /-- `FORALL_IN_IMAGE` (sets.ml 242):
      `!(f:A->B) s. (!y. y IN IMAGE f s ==> P y) <=>
                    (!x. x IN s ==> P(f x))`. -/
  FORALL_IN_IMAGE : thm
  /-- `EXISTS_IN_IMAGE` (sets.ml 246):
      `!(f:A->B) s. (?y. y IN IMAGE f s /\ P y) <=> ?x. x IN s /\ P(f x)`. -/
  EXISTS_IN_IMAGE : thm
  /-- `FORALL_IN_GSPEC` (sets.ml 250): the FOUR-conjunct `!`-over-`{f .. | ..}`
      rewrite (arities 1..4). -/
  FORALL_IN_GSPEC : thm
  /-- `EXISTS_IN_GSPEC` (sets.ml 263): the FOUR-conjunct `?`-over-`{f .. | ..}`
      rewrite (arities 1..4). -/
  EXISTS_IN_GSPEC : thm
  /-- `UNIONS_IMAGE` (sets.ml 276):
      `!(f:A->B->bool) s. UNIONS (IMAGE f s) = {y | ?x. x IN s /\ y IN f x}`. -/
  UNIONS_IMAGE : thm
  /-- `INTERS_IMAGE` (sets.ml 281):
      `!(f:A->B->bool) s.
         INTERS (IMAGE f s) = {y | !x. x IN s ==> y IN f x}`. -/
  INTERS_IMAGE : thm
  /-- `UNIONS_GSPEC` (sets.ml 286): the THREE-conjunct `UNIONS {f .. | ..}`
      rewrite (arities 1..3). -/
  UNIONS_GSPEC : thm
  /-- `INTERS_GSPEC` (sets.ml 297): the THREE-conjunct `INTERS {f .. | ..}`
      rewrite (arities 1..3). -/
  INTERS_GSPEC : thm
  /-- SET_TAC's local `PRESET_CONV` (sets.ml 321-327), built once as OCaml
      builds it, when sets.ml reaches SET_TAC. -/
  PRESET_CONV : ioconv
  deriving Inhabited

@[nospecialize]
def setupSetsProps [HolBase] (S : SetsCore)
    (MESON_TAC : List thm → tactic) :
    ExceptT String IO SetsProps := do
  let { CONJ_SYM, DISJ_SYM, .. } := HolBase.T
  let { IN, EXTENSION, GSPEC, IN_ELIM_THM, EMPTY, UNIV, UNION, UNIONS, INTER,
        INTERS, DIFF, INSERT, DELETE, IMAGE, REST, .. } := S

  let NOT_IN_EMPTY ← prove
   r"!x:A. ~(x IN EMPTY)"
   (REWRITE_TAC [IN, EMPTY])

  let IN_UNIV ← prove
   r"!x:A. x IN UNIV"
   (REWRITE_TAC [UNIV, IN])

  let IN_UNION ← prove
   r"!s t (x:A). x IN (s UNION t) <=> x IN s \/ x IN t"
   (REWRITE_TAC [IN_ELIM_THM, UNION])

  let IN_UNIONS ← prove
   r"!s (x:A). x IN (UNIONS s) <=> ?t. t IN s /\ x IN t"
   (REWRITE_TAC [IN_ELIM_THM, UNIONS])

  let IN_INTER ← prove
   r"!s t (x:A). x IN (s INTER t) <=> x IN s /\ x IN t"
   (REWRITE_TAC [IN_ELIM_THM, INTER])

  let IN_INTERS ← prove
   r"!s (x:A). x IN (INTERS s) <=> !t. t IN s ==> x IN t"
   (REWRITE_TAC [IN_ELIM_THM, INTERS])

  let IN_DIFF ← prove
   r"!(s:A->bool) t x. x IN (s DIFF t) <=> x IN s /\ ~(x IN t)"
   (REWRITE_TAC [IN_ELIM_THM, DIFF])

  let IN_INSERT ← prove
   r"!x:A. !y s. x IN (y INSERT s) <=> (x = y) \/ x IN s"
   (ONCE_REWRITE_TAC [DISJ_SYM] THEN REWRITE_TAC [IN_ELIM_THM, INSERT])

  let IN_DELETE ← prove
   r"!s. !x:A. !y. x IN (s DELETE y) <=> x IN s /\ ~(x = y)"
   (REWRITE_TAC [IN_ELIM_THM, DELETE])

  let IN_SING ← prove
   r"!x y. x IN {y:A} <=> (x = y)"
   (REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY])

  let IN_IMAGE ← prove
   r"!y:B. !s f. (y IN (IMAGE f s)) <=> ?x:A. (y = f x) /\ x IN s"
   (ONCE_REWRITE_TAC [CONJ_SYM] THEN REWRITE_TAC [IN_ELIM_THM, IMAGE])

  let IN_REST ← prove
   r"!x:A. !s. x IN (REST s) <=> x IN s /\ ~(x = CHOICE s)"
   (REWRITE_TAC [REST, IN_DELETE])

  let FORALL_IN_INSERT ← prove
   r"!P a s. (!x:A. x IN (a INSERT s) ==> P x) <=> P a /\ (!x. x IN s ==> P x)"
   (REWRITE_TAC [IN_INSERT] THEN MESON_TAC [])

  let EXISTS_IN_INSERT ← prove
   r"!P a s. (?x:A. x IN (a INSERT s) /\ P x) <=> P a \/ ?x. x IN s /\ P x"
   (REWRITE_TAC [IN_INSERT] THEN MESON_TAC [])

  let FORALL_IN_UNION ← prove
   r"!P s t:A->bool.
        (!x. x IN s UNION t ==> P x) <=>
        (!x. x IN s ==> P x) /\ (!x. x IN t ==> P x)"
   (REWRITE_TAC [IN_UNION] THEN MESON_TAC [])

  let EXISTS_IN_UNION ← prove
   r"!P s t:A->bool.
        (?x. x IN s UNION t /\ P x) <=>
        (?x. x IN s /\ P x) \/ (?x. x IN t /\ P x)"
   (REWRITE_TAC [IN_UNION] THEN MESON_TAC [])

  let FORALL_IN_IMAGE ← prove
   r"!(f:A->B) s. (!y. y IN IMAGE f s ==> P y) <=> (!x. x IN s ==> P(f x))"
   (REWRITE_TAC [IN_IMAGE] THEN MESON_TAC [])

  let EXISTS_IN_IMAGE ← prove
   r"!(f:A->B) s. (?y. y IN IMAGE f s /\ P y) <=> ?x. x IN s /\ P(f x)"
   (REWRITE_TAC [IN_IMAGE] THEN MESON_TAC [])

  let FORALL_IN_GSPEC ← prove
   r"(!P Q (f:A->B). (!z. z IN {f x | P x} ==> Q z) <=> (!x. P x ==> Q(f x))) /\
   (!P Q (f:A->B->C).
        (!z. z IN {f x y | P x y} ==> Q z) <=>
        (!x y. P x y ==> Q(f x y))) /\
   (!P Q (f:A->B->C->D).
        (!z. z IN {f w x y | P w x y} ==> Q z) <=>
        (!w x y. P w x y ==> Q(f w x y))) /\
   (!P Q (f:A->B->C->D->E).
        (!z. z IN {f v w x y | P v w x y} ==> Q z) <=>
        (!v w x y. P v w x y ==> Q(f v w x y)))"
   (REWRITE_TAC [GSPEC, IN_ELIM_THM] THEN MESON_TAC [])

  let EXISTS_IN_GSPEC ← prove
   r"(!P Q (f:A->B). (?z. z IN {f x | P x} /\ Q z) <=> (?x. P x /\ Q(f x))) /\
   (!P Q (f:A->B->C).
        (?z. z IN {f x y | P x y} /\ Q z) <=>
        (?x y. P x y /\ Q(f x y))) /\
   (!P Q (f:A->B->C->D).
        (?z. z IN {f w x y | P w x y} /\ Q z) <=>
        (?w x y. P w x y /\ Q(f w x y))) /\
   (!P Q (f:A->B->C->D->E).
        (?z. z IN {f v w x y | P v w x y} /\ Q z) <=>
        (?v w x y. P v w x y /\ Q(f v w x y)))"
   (REWRITE_TAC [GSPEC, IN_ELIM_THM] THEN MESON_TAC [])

  let UNIONS_IMAGE ← prove
   r"!(f:A->B->bool) s. UNIONS (IMAGE f s) = {y | ?x. x IN s /\ y IN f x}"
   (REPEAT GEN_TAC THEN  GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC [IN_UNIONS, IN_IMAGE, IN_ELIM_THM] THEN MESON_TAC [])

  let INTERS_IMAGE ← prove
   r"!(f:A->B->bool) s. INTERS (IMAGE f s) = {y | !x. x IN s ==> y IN f x}"
   (REPEAT GEN_TAC THEN  GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC [IN_INTERS, IN_IMAGE, IN_ELIM_THM] THEN MESON_TAC [])

  let UNIONS_GSPEC ← prove
   r"(!P (f:A->B->bool).
        UNIONS {f x | P x} = {a | ?x. P x /\ a IN (f x)}) /\
   (!P (f:A->B->C->bool).
        UNIONS {f x y | P x y} = {a | ?x y. P x y /\ a IN (f x y)}) /\
   (!P (f:A->B->C->D->bool).
        UNIONS {f x y z | P x y z} =
        {a | ?x y z. P x y z /\ a IN (f x y z)})"
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC [IN_UNIONS, IN_ELIM_THM] THEN MESON_TAC [])

  let INTERS_GSPEC ← prove
   r"(!P (f:A->B->bool).
        INTERS {f x | P x} = {a | !x. P x ==> a IN (f x)}) /\
   (!P (f:A->B->C->bool).
        INTERS {f x y | P x y} = {a | !x y. P x y ==> a IN (f x y)}) /\
   (!P (f:A->B->C->D->bool).
        INTERS {f x y z | P x y z} =
        {a | !x y z. P x y z ==> a IN (f x y z)})"
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC [IN_INTERS, IN_ELIM_THM] THEN MESON_TAC [])

  /- SET_TAC's `PRESET_CONV` (sets.ml 321-327). -/
  let { SUBSET, PSUBSET, DISJOINT, SING, BIJ, INJ, SURJ, .. } := S
  let PRESET_CONV :=
    (← REWRITE_CONV_NET [INTERS_IMAGE, INTERS_GSPEC, UNIONS_IMAGE, UNIONS_GSPEC]) THENC
    (← REWRITE_CONV_NET [EXTENSION, SUBSET, PSUBSET, DISJOINT, SING,
                         BIJ, INJ, SURJ]) THENC
    (← REWRITE_CONV_NET [NOT_IN_EMPTY, IN_UNIV, IN_UNION, IN_INTER, IN_DIFF, IN_INSERT,
                         IN_DELETE, IN_REST, IN_INTERS, IN_UNIONS, IN_IMAGE,
                         IN_ELIM_THM, IN])

  return {
    NOT_IN_EMPTY, IN_UNIV, IN_UNION, IN_UNIONS, IN_INTER, IN_INTERS, IN_DIFF,
    IN_INSERT, IN_DELETE, IN_SING, IN_IMAGE, IN_REST, FORALL_IN_INSERT,
    EXISTS_IN_INSERT, FORALL_IN_UNION, EXISTS_IN_UNION, FORALL_IN_IMAGE,
    EXISTS_IN_IMAGE, FORALL_IN_GSPEC, EXISTS_IN_GSPEC, UNIONS_IMAGE,
    INTERS_IMAGE, UNIONS_GSPEC, INTERS_GSPEC, PRESET_CONV }

/- ---------------------------------------------------------------------- -/
/- Tactic to automate some routine set theory by reduction to FOL.        -/
/- (sets.ml 317-335)                                                      -/
/- ---------------------------------------------------------------------- -/

/-- SET_TAC's local `PRESET_CONV` (sets.ml 321-327), built once in
    `setupSetsProps`. -/
def SET_PRESET_CONV (_S : SetsCore) (P : SetsProps) : ioconv := P.PRESET_CONV

/-- `SET_TAC` (sets.ml 317).  OCaml's `CONV_RULE PRESET_CONV th = TRUTH` is
    structural equality on theorems, so it is `compare ... == .eq`.  OCaml
    runs the filter when `SET_TAC ths` is built; here it runs when the tactic
    is applied.  `CONV_RULE` prints nothing, so the difference is not
    visible. -/
def SET_TAC [HolBase] (S : SetsCore) (P : SetsProps)
    (MESON_TAC : List thm → tactic) (ths : List thm) : tactic :=
  let PRESET_CONV := SET_PRESET_CONV S P
  tactic_of do
    let kept ← ths.filterM (fun th => do
      pure (compare (← CONV_RULE PRESET_CONV th) HolBase.B.TRUTH == .eq))
    pure
     (MAP_EVERY MP_TAC ths THEN POP_ASSUM_LIST (K ALL_TAC : List thm → tactic) THEN
      REPEAT (COND_CASES_TAC THEN POP_ASSUM MP_TAC) THEN
      CONV_TAC PRESET_CONV THEN MAP_EVERY MP_TAC kept THEN
      REWRITE_TAC [S.IN] THEN MESON_TAC [])

/-- `SET_RULE tm = prove(tm,SET_TAC[])` (sets.ml 335). -/
def SET_RULE [HolBase] (S : SetsCore) (P : SetsProps)
    (MESON_TAC : List thm → tactic) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (HolCore.Tactics.prove HolBase.B tm (SET_TAC S P MESON_TAC []))

/-- The stage-3 theorems: `CHOICE_DEF` (sets.ml 312) and the first three
    `SET_TAC` consumers, `NOT_EQUAL_SETS` (341), `INSERT_RESTRICT` (346) and
    `UNIV_1` (353). -/
structure SetsTactics where
  /-- `CHOICE_DEF` (sets.ml 312):
      `!s:A->bool. ~(s = EMPTY) ==> (CHOICE s) IN s`. -/
  CHOICE_DEF : thm
  /-- `NOT_EQUAL_SETS` (sets.ml 341):
      `!s:A->bool. !t. ~(s = t) <=> ?x. x IN t <=> ~(x IN s)`.  A bare
      `SET_TAC[]`. -/
  NOT_EQUAL_SETS : thm
  /-- `INSERT_RESTRICT` (sets.ml 345):
      `!P s a:A. {x | x IN a INSERT s /\ P x} =
       if P a then a INSERT {x | x IN s /\ P x} else {x | x IN s /\ P x}`.
      Proved with `ASM SET_TAC[]`. -/
  INSERT_RESTRICT : thm
  /-- `UNIV_1` (sets.ml 351): `(:1) = {one}`.  `SET_TAC[one]`. -/
  UNIV_1 : thm
  deriving Inhabited

@[nospecialize]
def setupSetsTactics [HolBase] (S : SetsCore)
    (P : SetsProps) (Tr : HolCore.Trivia.TriviaThms)
    (MESON_TAC : List thm → tactic) :
    ExceptT String IO SetsTactics := do
  let SET_TAC := SET_TAC S P MESON_TAC
  let { NOT_FORALL_THM, EXISTS_THM, .. } := HolBase.C
  let { one, .. } := Tr
  let { EXTENSION, CHOICE, .. } := S
  let { NOT_IN_EMPTY, .. } := P

  /- Basic property of the choice function. -/

  let CHOICE_DEF ← prove
   r"!s:A->bool. ~(s = EMPTY) ==> (CHOICE s) IN s"
   (REWRITE_TAC [CHOICE, EXTENSION, NOT_IN_EMPTY, NOT_FORALL_THM, EXISTS_THM])

  /- Misc. theorems. -/

  let NOT_EQUAL_SETS ← prove
   r"!s:A->bool. !t. ~(s = t) <=> ?x. x IN t <=> ~(x IN s)"
   (SET_TAC [])

  let INSERT_RESTRICT ← prove
   r"!P s a:A.
        {x | x IN a INSERT s /\ P x} =
        if P a then a INSERT {x | x IN s /\ P x} else {x | x IN s /\ P x}"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM SET_TAC [])

  let UNIV_1 ← prove
   r"(:1) = {one}"
   (SET_TAC [one])

  return {
    CHOICE_DEF, NOT_EQUAL_SETS, INSERT_RESTRICT, UNIV_1 }

/- ---------------------------------------------------------------------- -/
/- The empty set, the universal set, inclusion, proper subset.            -/
/-   (sets.ml 356-459)                                                    -/
/- ---------------------------------------------------------------------- -/

/-- The empty-set, universal-set, set-inclusion and proper-subset theorems
    of sets.ml 356-459.  TWENTY-ONE theorems.  Nineteen are a bare
    `SET_TAC[]`; the two exceptions are `SUBSET_RESTRICT` (a single
    `SIMP_TAC[SUBSET; IN_ELIM_THM]`, sets.ml 421) and `PSUBSET_ALT`
    (`REWRITE_TAC[PSUBSET] THEN SET_TAC[]`, sets.ml 457).  No `ASM SET_TAC`,
    no THENL anywhere in this range. -/
structure SetsInclusion where
  /-- `MEMBER_NOT_EMPTY` (sets.ml 359):
      `!s:A->bool. (?x. x IN s) <=> ~(s = EMPTY)`.  Bare `SET_TAC[]`. -/
  MEMBER_NOT_EMPTY : thm
  /-- `UNIV_NOT_EMPTY` (sets.ml 367): `~(UNIV:A->bool = EMPTY)`.  `SET_TAC[]`. -/
  UNIV_NOT_EMPTY : thm
  /-- `EMPTY_NOT_UNIV` (sets.ml 371): `~(EMPTY:A->bool = UNIV)`.  `SET_TAC[]`. -/
  EMPTY_NOT_UNIV : thm
  /-- `EQ_UNIV` (sets.ml 375): `(!x:A. x IN s) <=> (s = UNIV)`.  `SET_TAC[]`.
      `s` is FREE in the OCaml goal string - kept free. -/
  EQ_UNIV : thm
  /-- `SUBSET_TRANS` (sets.ml 383):
      `!(s:A->bool) t u. s SUBSET t /\ t SUBSET u ==> s SUBSET u`.  `SET_TAC[]`. -/
  SUBSET_TRANS : thm
  /-- `SUBSET_REFL` (sets.ml 387): `!s:A->bool. s SUBSET s`.  `SET_TAC[]`. -/
  SUBSET_REFL : thm
  /-- `SUBSET_ANTISYM` (sets.ml 391):
      `!(s:A->bool) t. s SUBSET t /\ t SUBSET s ==> s = t`.  `SET_TAC[]`. -/
  SUBSET_ANTISYM : thm
  /-- `SUBSET_ANTISYM_EQ` (sets.ml 395):
      `!(s:A->bool) t. s SUBSET t /\ t SUBSET s <=> s = t`.  `SET_TAC[]`. -/
  SUBSET_ANTISYM_EQ : thm
  /-- `EMPTY_SUBSET` (sets.ml 399): `!s:A->bool. EMPTY SUBSET s`.  `SET_TAC[]`. -/
  EMPTY_SUBSET : thm
  /-- `SUBSET_EMPTY` (sets.ml 403):
      `!s:A->bool. s SUBSET EMPTY <=> (s = EMPTY)`.  `SET_TAC[]`. -/
  SUBSET_EMPTY : thm
  /-- `SUBSET_UNIV` (sets.ml 407): `!s:A->bool. s SUBSET UNIV`.  `SET_TAC[]`. -/
  SUBSET_UNIV : thm
  /-- `UNIV_SUBSET` (sets.ml 411):
      `!s:A->bool. UNIV SUBSET s <=> (s = UNIV)`.  `SET_TAC[]`. -/
  UNIV_SUBSET : thm
  /-- `SING_SUBSET` (sets.ml 415):
      `!s x:A. {x} SUBSET s <=> x IN s`.  `SET_TAC[]`. -/
  SING_SUBSET : thm
  /-- `SUBSET_RESTRICT` (sets.ml 419):
      `!s P. {x:A | x IN s /\ P x} SUBSET s`.  A single
      `SIMP_TAC[SUBSET; IN_ELIM_THM]` - NOT `SET_TAC`. -/
  SUBSET_RESTRICT : thm
  /-- `PSUBSET_TRANS` (sets.ml 427):
      `!(s:A->bool) t u. s PSUBSET t /\ t PSUBSET u ==> s PSUBSET u`.
      `SET_TAC[]`. -/
  PSUBSET_TRANS : thm
  /-- `PSUBSET_SUBSET_TRANS` (sets.ml 431):
      `!(s:A->bool) t u. s PSUBSET t /\ t SUBSET u ==> s PSUBSET u`.
      `SET_TAC[]`. -/
  PSUBSET_SUBSET_TRANS : thm
  /-- `SUBSET_PSUBSET_TRANS` (sets.ml 435):
      `!(s:A->bool) t u. s SUBSET t /\ t PSUBSET u ==> s PSUBSET u`.
      `SET_TAC[]`. -/
  SUBSET_PSUBSET_TRANS : thm
  /-- `PSUBSET_IRREFL` (sets.ml 439): `!s:A->bool. ~(s PSUBSET s)`.
      `SET_TAC[]`. -/
  PSUBSET_IRREFL : thm
  /-- `NOT_PSUBSET_EMPTY` (sets.ml 443): `!s:A->bool. ~(s PSUBSET EMPTY)`.
      `SET_TAC[]`. -/
  NOT_PSUBSET_EMPTY : thm
  /-- `NOT_UNIV_PSUBSET` (sets.ml 447): `!s:A->bool. ~(UNIV PSUBSET s)`.
      `SET_TAC[]`. -/
  NOT_UNIV_PSUBSET : thm
  /-- `PSUBSET_UNIV` (sets.ml 451):
      `!s:A->bool. s PSUBSET UNIV <=> ?x. ~(x IN s)`.  `SET_TAC[]`. -/
  PSUBSET_UNIV : thm
  /-- `PSUBSET_ALT` (sets.ml 455):
      `!s t:A->bool. s PSUBSET t <=> s SUBSET t /\ (?a. a IN t /\ ~(a IN s))`.
      `REWRITE_TAC[PSUBSET] THEN SET_TAC[]`. -/
  PSUBSET_ALT : thm
  deriving Inhabited

@[nospecialize]
def setupSetsInclusion [HolBase] (S : SetsCore) (P : SetsProps)
    (MESON_TAC : List thm → tactic) :
    ExceptT String IO SetsInclusion := do
  let SET_TAC := SET_TAC S P MESON_TAC
  let { IN_ELIM_THM, SUBSET, PSUBSET, .. } := S

  /- The empty set. -/

  let MEMBER_NOT_EMPTY ← prove
   r"!s:A->bool. (?x. x IN s) <=> ~(s = EMPTY)"
   (SET_TAC [])

  /- The universal set. -/

  let UNIV_NOT_EMPTY ← prove
   r"~(UNIV:A->bool = EMPTY)"
   (SET_TAC [])

  let EMPTY_NOT_UNIV ← prove
   r"~(EMPTY:A->bool = UNIV)"
   (SET_TAC [])

  let EQ_UNIV ← prove
   r"(!x:A. x IN s) <=> (s = UNIV)"
   (SET_TAC [])

  /- Set inclusion. -/

  let SUBSET_TRANS ← prove
   r"!(s:A->bool) t u. s SUBSET t /\ t SUBSET u ==> s SUBSET u"
   (SET_TAC [])

  let SUBSET_REFL ← prove
   r"!s:A->bool. s SUBSET s"
   (SET_TAC [])

  let SUBSET_ANTISYM ← prove
   r"!(s:A->bool) t. s SUBSET t /\ t SUBSET s ==> s = t"
   (SET_TAC [])

  let SUBSET_ANTISYM_EQ ← prove
   r"!(s:A->bool) t. s SUBSET t /\ t SUBSET s <=> s = t"
   (SET_TAC [])

  let EMPTY_SUBSET ← prove
   r"!s:A->bool. EMPTY SUBSET s"
   (SET_TAC [])

  let SUBSET_EMPTY ← prove
   r"!s:A->bool. s SUBSET EMPTY <=> (s = EMPTY)"
   (SET_TAC [])

  let SUBSET_UNIV ← prove
   r"!s:A->bool. s SUBSET UNIV"
   (SET_TAC [])

  let UNIV_SUBSET ← prove
   r"!s:A->bool. UNIV SUBSET s <=> (s = UNIV)"
   (SET_TAC [])

  let SING_SUBSET ← prove
   r"!s x:A. {x} SUBSET s <=> x IN s"
   (SET_TAC [])

  let SUBSET_RESTRICT ← prove
   r"!s P. {x:A | x IN s /\ P x} SUBSET s"
   (SIMP_TAC [SUBSET, IN_ELIM_THM])

  /- Proper subset. -/

  let PSUBSET_TRANS ← prove
   r"!(s:A->bool) t u. s PSUBSET t /\ t PSUBSET u ==> s PSUBSET u"
   (SET_TAC [])

  let PSUBSET_SUBSET_TRANS ← prove
   r"!(s:A->bool) t u. s PSUBSET t /\ t SUBSET u ==> s PSUBSET u"
   (SET_TAC [])

  let SUBSET_PSUBSET_TRANS ← prove
   r"!(s:A->bool) t u. s SUBSET t /\ t PSUBSET u ==> s PSUBSET u"
   (SET_TAC [])

  let PSUBSET_IRREFL ← prove
   r"!s:A->bool. ~(s PSUBSET s)"
   (SET_TAC [])

  let NOT_PSUBSET_EMPTY ← prove
   r"!s:A->bool. ~(s PSUBSET EMPTY)"
   (SET_TAC [])

  let NOT_UNIV_PSUBSET ← prove
   r"!s:A->bool. ~(UNIV PSUBSET s)"
   (SET_TAC [])

  let PSUBSET_UNIV ← prove
   r"!s:A->bool. s PSUBSET UNIV <=> ?x. ~(x IN s)"
   (SET_TAC [])

  let PSUBSET_ALT ← prove
   r"!s t:A->bool. s PSUBSET t <=> s SUBSET t /\ (?a. a IN t /\ ~(a IN s))"
   (REWRITE_TAC [PSUBSET] THEN SET_TAC [])

  return {
    MEMBER_NOT_EMPTY, UNIV_NOT_EMPTY, EMPTY_NOT_UNIV, EQ_UNIV, SUBSET_TRANS,
    SUBSET_REFL, SUBSET_ANTISYM, SUBSET_ANTISYM_EQ, EMPTY_SUBSET, SUBSET_EMPTY,
    SUBSET_UNIV, UNIV_SUBSET, SING_SUBSET, SUBSET_RESTRICT, PSUBSET_TRANS,
    PSUBSET_SUBSET_TRANS, SUBSET_PSUBSET_TRANS, PSUBSET_IRREFL,
    NOT_PSUBSET_EMPTY, NOT_UNIV_PSUBSET, PSUBSET_UNIV, PSUBSET_ALT }

/- ---------------------------------------------------------------------- -/
/- Union, intersection, distributivity, disjointness, difference.        -/
/-   (sets.ml 460-618)                                                    -/
/- ---------------------------------------------------------------------- -/

/-- The union, intersection, distributivity, disjoint-set and set-difference
    theorems of sets.ml 462-665.  THIRTY-NINE theorems.  Thirty-five are a
    bare `SET_TAC[]`; the four exceptions all sit in the union block:
    `FORALL_SUBSET_UNION` (sets.ml 508), `EXISTS_SUBSET_UNION` (523),
    `FORALL_SUBSET_INSERT` (529) and `EXISTS_SUBSET_INSERT` (536).  Two of
    those (`FORALL_SUBSET_UNION`) use the `ASM SET_TAC` variant. -/
structure SetsOperators where
  /-- `UNION_ASSOC` (sets.ml 463):
      `!(s:A->bool) t u. (s UNION t) UNION u = s UNION (t UNION u)`.
      Bare `SET_TAC[]`. -/
  UNION_ASSOC : thm
  /-- `UNION_IDEMPOT` (sets.ml 467): `!s:A->bool. s UNION s = s`.  `SET_TAC[]`. -/
  UNION_IDEMPOT : thm
  /-- `UNION_COMM` (sets.ml 471):
      `!(s:A->bool) t. s UNION t = t UNION s`.  `SET_TAC[]`. -/
  UNION_COMM : thm
  /-- `SUBSET_UNION` (sets.ml 475): the pair
      `(!s t. s SUBSET (s UNION t)) /\ (!s t. s SUBSET (t UNION s))`.
      `SET_TAC[]`. -/
  SUBSET_UNION : thm
  /-- `SUBSET_UNION_ABSORPTION` (sets.ml 480):
      `!s t. s SUBSET t <=> (s UNION t = t)`.  `SET_TAC[]`. -/
  SUBSET_UNION_ABSORPTION : thm
  /-- `UNION_EMPTY` (sets.ml 484): the pair
      `(!s. EMPTY UNION s = s) /\ (!s. s UNION EMPTY = s)`.  `SET_TAC[]`. -/
  UNION_EMPTY : thm
  /-- `UNION_UNIV` (sets.ml 489): the pair
      `(!s. UNIV UNION s = UNIV) /\ (!s. s UNION UNIV = UNIV)`.  `SET_TAC[]`. -/
  UNION_UNIV : thm
  /-- `EMPTY_UNION` (sets.ml 494):
      `!s t. (s UNION t = EMPTY) <=> (s = EMPTY) /\ (t = EMPTY)`.
      `SET_TAC[]`. -/
  EMPTY_UNION : thm
  /-- `UNION_SUBSET` (sets.ml 498):
      `!s t u. (s UNION t) SUBSET u <=> s SUBSET u /\ t SUBSET u`.
      `SET_TAC[]`. -/
  UNION_SUBSET : thm
  /-- `UNION_RESTRICT` (sets.ml 502): the restriction of `{x | x IN s /\ P x}`
      distributes over `UNION`.  `SET_TAC[]`. -/
  UNION_RESTRICT : thm
  /-- `FORALL_SUBSET_UNION` (sets.ml 508): quantifying subsets of `t UNION u`.
      `REPEAT GEN_TAC THEN EQ_TAC THENL [..;..]`, both branches ending in
      `ASM SET_TAC[]`. -/
  FORALL_SUBSET_UNION : thm
  /-- `EXISTS_SUBSET_UNION` (sets.ml 519): the existential dual of
      `FORALL_SUBSET_UNION`, via a MESON rewrite and `FORALL_SUBSET_UNION`. -/
  EXISTS_SUBSET_UNION : thm
  /-- `FORALL_SUBSET_INSERT` (sets.ml 526): quantifying subsets of
      `a INSERT t`, reduced to `FORALL_SUBSET_UNION` via
      `a INSERT s = {a} UNION s`. -/
  FORALL_SUBSET_INSERT : thm
  /-- `EXISTS_SUBSET_INSERT` (sets.ml 535): the existential dual of
      `FORALL_SUBSET_INSERT`. -/
  EXISTS_SUBSET_INSERT : thm
  /-- `INTER_ASSOC` (sets.ml 545):
      `!(s:A->bool) t u. (s INTER t) INTER u = s INTER (t INTER u)`.
      `SET_TAC[]`. -/
  INTER_ASSOC : thm
  /-- `INTER_IDEMPOT` (sets.ml 549): `!s:A->bool. s INTER s = s`.  `SET_TAC[]`. -/
  INTER_IDEMPOT : thm
  /-- `INTER_COMM` (sets.ml 553):
      `!(s:A->bool) t. s INTER t = t INTER s`.  `SET_TAC[]`. -/
  INTER_COMM : thm
  /-- `INTER_SUBSET` (sets.ml 557): the pair
      `(!s t. (s INTER t) SUBSET s) /\ (!s t. (t INTER s) SUBSET s)`.
      `SET_TAC[]`. -/
  INTER_SUBSET : thm
  /-- `SUBSET_INTER_ABSORPTION` (sets.ml 562):
      `!s t. s SUBSET t <=> (s INTER t = s)`.  `SET_TAC[]`. -/
  SUBSET_INTER_ABSORPTION : thm
  /-- `INTER_EMPTY` (sets.ml 566): the pair
      `(!s. EMPTY INTER s = EMPTY) /\ (!s. s INTER EMPTY = EMPTY)`.
      `SET_TAC[]`. -/
  INTER_EMPTY : thm
  /-- `INTER_UNIV` (sets.ml 571): the pair
      `(!s. UNIV INTER s = s) /\ (!s. s INTER UNIV = s)`.  `SET_TAC[]`. -/
  INTER_UNIV : thm
  /-- `SUBSET_INTER` (sets.ml 576):
      `!s t u. s SUBSET (t INTER u) <=> s SUBSET t /\ s SUBSET u`.
      `SET_TAC[]`. -/
  SUBSET_INTER : thm
  /-- `INTER_RESTRICT` (sets.ml 580): the restriction of `{x | x IN s /\ P x}`
      distributes over `INTER`.  `SET_TAC[]`. -/
  INTER_RESTRICT : thm
  /-- `UNION_OVER_INTER` (sets.ml 590):
      `!s t u. s INTER (t UNION u) = (s INTER t) UNION (s INTER u)`.
      `SET_TAC[]`. -/
  UNION_OVER_INTER : thm
  /-- `INTER_OVER_UNION` (sets.ml 594):
      `!s t u. s UNION (t INTER u) = (s UNION t) INTER (s UNION u)`.
      `SET_TAC[]`. -/
  INTER_OVER_UNION : thm
  /-- `IN_DISJOINT` (sets.ml 602):
      `!s t. DISJOINT s t <=> ~(?x. x IN s /\ x IN t)`.  `SET_TAC[]`. -/
  IN_DISJOINT : thm
  /-- `DISJOINT_SYM` (sets.ml 606):
      `!s t. DISJOINT s t <=> DISJOINT t s`.  `SET_TAC[]`. -/
  DISJOINT_SYM : thm
  /-- `DISJOINT_EMPTY` (sets.ml 610):
      `!s:A->bool. DISJOINT EMPTY s /\ DISJOINT s EMPTY`.  `SET_TAC[]`. -/
  DISJOINT_EMPTY : thm
  /-- `DISJOINT_EMPTY_REFL` (sets.ml 614):
      `!s:A->bool. (s = EMPTY) <=> (DISJOINT s s)`.  `SET_TAC[]`. -/
  DISJOINT_EMPTY_REFL : thm
  /-- `DISJOINT_UNION` (sets.ml 618):
      `!s t u. DISJOINT (s UNION t) u <=> DISJOINT s u /\ DISJOINT t u`.
      `SET_TAC[]`. -/
  DISJOINT_UNION : thm
  /-- `DISJOINT_SING` (sets.ml 622): the pair
      `(!s a. DISJOINT s {a} <=> ~(a IN s)) /\
       (!s a. DISJOINT {a} s <=> ~(a IN s))`.  `SET_TAC[]`. -/
  DISJOINT_SING : thm
  /-- `DIFF_EMPTY` (sets.ml 631): `!s:A->bool. s DIFF EMPTY = s`.  `SET_TAC[]`. -/
  DIFF_EMPTY : thm
  /-- `EMPTY_DIFF` (sets.ml 635):
      `!s:A->bool. EMPTY DIFF s = EMPTY`.  `SET_TAC[]`. -/
  EMPTY_DIFF : thm
  /-- `DIFF_UNIV` (sets.ml 639):
      `!s:A->bool. s DIFF UNIV = EMPTY`.  `SET_TAC[]`. -/
  DIFF_UNIV : thm
  /-- `DIFF_DIFF` (sets.ml 643):
      `!s t. (s DIFF t) DIFF t = s DIFF t`.  `SET_TAC[]`. -/
  DIFF_DIFF : thm
  /-- `DIFF_EQ_EMPTY` (sets.ml 647):
      `!s:A->bool. s DIFF s = EMPTY`.  `SET_TAC[]`. -/
  DIFF_EQ_EMPTY : thm
  /-- `SUBSET_DIFF` (sets.ml 651): `!s t. (s DIFF t) SUBSET s`.  `SET_TAC[]`. -/
  SUBSET_DIFF : thm
  /-- `COMPL_COMPL` (sets.ml 655):
      `!s. (:A) DIFF ((:A) DIFF s) = s`.  `SET_TAC[]`. -/
  COMPL_COMPL : thm
  /-- `DIFF_RESTRICT` (sets.ml 659): the restriction of `{x | x IN s /\ P x}`
      distributes over `DIFF`.  `SET_TAC[]`. -/
  DIFF_RESTRICT : thm
  deriving Inhabited

@[nospecialize]
def setupSetsOperators [HolBase] (S : SetsCore) (P : SetsProps)
    (MESON_TAC : List thm → tactic)
    (MESON' : List thm → term → IO (Except String thm)) :
    ExceptT String IO SetsOperators := do
  let SET_TAC := SET_TAC S P MESON_TAC
  let SET_RULE := SET_RULE S P MESON_TAC
  let MESON (ths : List thm) (t : term) : ExceptT String IO thm := MESON' ths t
  let { EQ_IMP, .. } := HolBase.T

  /- Union. -/

  let UNION_ASSOC ← prove
   r"!(s:A->bool) t u. (s UNION t) UNION u = s UNION (t UNION u)"
   (SET_TAC [])

  let UNION_IDEMPOT ← prove
   r"!s:A->bool. s UNION s = s"
   (SET_TAC [])

  let UNION_COMM ← prove
   r"!(s:A->bool) t. s UNION t = t UNION s"
   (SET_TAC [])

  let SUBSET_UNION ← prove
   r"(!s:A->bool. !t. s SUBSET (s UNION t)) /\
   (!s:A->bool. !t. s SUBSET (t UNION s))"
   (SET_TAC [])

  let SUBSET_UNION_ABSORPTION ← prove
   r"!s:A->bool. !t. s SUBSET t <=> (s UNION t = t)"
   (SET_TAC [])

  let UNION_EMPTY ← prove
   r"(!s:A->bool. EMPTY UNION s = s) /\
   (!s:A->bool. s UNION EMPTY = s)"
   (SET_TAC [])

  let UNION_UNIV ← prove
   r"(!s:A->bool. UNIV UNION s = UNIV) /\
   (!s:A->bool. s UNION UNIV = UNIV)"
   (SET_TAC [])

  let EMPTY_UNION ← prove
   r"!s:A->bool. !t. (s UNION t = EMPTY) <=> (s = EMPTY) /\ (t = EMPTY)"
   (SET_TAC [])

  let UNION_SUBSET ← prove
   r"!s t u:A->bool. (s UNION t) SUBSET u <=> s SUBSET u /\ t SUBSET u"
   (SET_TAC [])

  let UNION_RESTRICT ← prove
   r"!P s t:A->bool.
        {x | x IN (s UNION t) /\ P x} =
        {x | x IN s /\ P x} UNION {x | x IN t /\ P x}"
   (SET_TAC [])

  let FORALL_SUBSET_UNION ← prove
   r"!t u:A->bool.
        (!s. s SUBSET t UNION u ==> P s) <=>
        (!t' u'. t' SUBSET t /\ u' SUBSET u ==> P(t' UNION u'))"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC [],
      DISCH_TAC THEN X_GEN_TAC (← q r"s:A->bool") THEN DISCH_TAC THEN
      FIRST_ASSUM (MP_TAC o SPECL [← q r"s INTER t:A->bool", ← q r"s INTER u:A->bool"]) THEN
      ANTS_TAC THENL [ALL_TAC, MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC] THEN
      ASM SET_TAC []])

  let EXISTS_SUBSET_UNION ← prove
   r"!t u:A->bool.
        (?s. s SUBSET t UNION u /\ P s) <=>
        (?t' u'. t' SUBSET t /\ u' SUBSET u /\ P(t' UNION u'))"
   (REWRITE_TAC [← MESON [] (← q r"(?x. P x /\ Q x) <=> ~(!x. P x ==> ~Q x)")] THEN
    REWRITE_TAC [FORALL_SUBSET_UNION] THEN MESON_TAC [])

  -- The two SET_RULEs run (and print) right to left, as in OCaml.
  let FORALL_SUBSET_INSERT ← prove
   r"!a:A t. (!s. s SUBSET a INSERT t ==> P s) <=>
           (!s. s SUBSET t ==> P s /\ P (a INSERT s))"
   (← do
    let r2 ← SET_RULE (← q r"s SUBSET {a} <=> s = {} \/ s = {a}")
    let r1 ← SET_RULE (← q r"a INSERT s = {a} UNION s")
    pure
     (REPEAT GEN_TAC THEN
      ONCE_REWRITE_TAC [r1] THEN
      REWRITE_TAC [FORALL_SUBSET_UNION, r2] THEN
      MESON_TAC [UNION_EMPTY]))

  let EXISTS_SUBSET_INSERT ← prove
   r"!a:A t. (?s. s SUBSET a INSERT t /\ P s) <=>
           (?s. s SUBSET t /\ (P s \/ P (a INSERT s)))"
   (REWRITE_TAC [← MESON [] (← q r"(?x. P x /\ Q x) <=> ~(!x. P x ==> ~Q x)")] THEN
    REWRITE_TAC [FORALL_SUBSET_INSERT] THEN MESON_TAC [])

  /- Intersection. -/

  let INTER_ASSOC ← prove
   r"!(s:A->bool) t u. (s INTER t) INTER u = s INTER (t INTER u)"
   (SET_TAC [])

  let INTER_IDEMPOT ← prove
   r"!s:A->bool. s INTER s = s"
   (SET_TAC [])

  let INTER_COMM ← prove
   r"!(s:A->bool) t. s INTER t = t INTER s"
   (SET_TAC [])

  let INTER_SUBSET ← prove
   r"(!s:A->bool. !t. (s INTER t) SUBSET s) /\
   (!s:A->bool. !t. (t INTER s) SUBSET s)"
   (SET_TAC [])

  let SUBSET_INTER_ABSORPTION ← prove
   r"!s:A->bool. !t. s SUBSET t <=> (s INTER t = s)"
   (SET_TAC [])

  let INTER_EMPTY ← prove
   r"(!s:A->bool. EMPTY INTER s = EMPTY) /\
   (!s:A->bool. s INTER EMPTY = EMPTY)"
   (SET_TAC [])

  let INTER_UNIV ← prove
   r"(!s:A->bool. UNIV INTER s = s) /\
   (!s:A->bool. s INTER UNIV = s)"
   (SET_TAC [])

  let SUBSET_INTER ← prove
   r"!s t u:A->bool. s SUBSET (t INTER u) <=> s SUBSET t /\ s SUBSET u"
   (SET_TAC [])

  let INTER_RESTRICT ← prove
   r"!P s (t:A->bool).
        {x | x IN (s INTER t) /\ P x} =
        {x | x IN s /\ P x} INTER {x | x IN t /\ P x}"
   (SET_TAC [])

  /- Distributivity. -/

  let UNION_OVER_INTER ← prove
   r"!s:A->bool. !t u. s INTER (t UNION u) = (s INTER t) UNION (s INTER u)"
   (SET_TAC [])

  let INTER_OVER_UNION ← prove
   r"!s:A->bool. !t u. s UNION (t INTER u) = (s UNION t) INTER (s UNION u)"
   (SET_TAC [])

  /- Disjoint sets. -/

  let IN_DISJOINT ← prove
   r"!s:A->bool. !t. DISJOINT s t <=> ~(?x. x IN s /\ x IN t)"
   (SET_TAC [])

  let DISJOINT_SYM ← prove
   r"!s:A->bool. !t. DISJOINT s t <=> DISJOINT t s"
   (SET_TAC [])

  let DISJOINT_EMPTY ← prove
   r"!s:A->bool. DISJOINT EMPTY s /\ DISJOINT s EMPTY"
   (SET_TAC [])

  let DISJOINT_EMPTY_REFL ← prove
   r"!s:A->bool. (s = EMPTY) <=> (DISJOINT s s)"
   (SET_TAC [])

  let DISJOINT_UNION ← prove
   r"!s:A->bool. !t u. DISJOINT (s UNION t) u <=> DISJOINT s u /\ DISJOINT t u"
   (SET_TAC [])

  let DISJOINT_SING ← prove
   r"(!s a:A. DISJOINT s {a} <=> ~(a IN s)) /\
   (!s a:A. DISJOINT {a} s <=> ~(a IN s))"
   (SET_TAC [])

  /- Set difference. -/

  let DIFF_EMPTY ← prove
   r"!s:A->bool. s DIFF EMPTY = s"
   (SET_TAC [])

  let EMPTY_DIFF ← prove
   r"!s:A->bool. EMPTY DIFF s = EMPTY"
   (SET_TAC [])

  let DIFF_UNIV ← prove
   r"!s:A->bool. s DIFF UNIV = EMPTY"
   (SET_TAC [])

  let DIFF_DIFF ← prove
   r"!s:A->bool. !t. (s DIFF t) DIFF t = s DIFF t"
   (SET_TAC [])

  let DIFF_EQ_EMPTY ← prove
   r"!s:A->bool. s DIFF s = EMPTY"
   (SET_TAC [])

  let SUBSET_DIFF ← prove
   r"!s t:A->bool. (s DIFF t) SUBSET s"
   (SET_TAC [])

  let COMPL_COMPL ← prove
   r"!s. (:A) DIFF ((:A) DIFF s) = s"
   (SET_TAC [])

  let DIFF_RESTRICT ← prove
   r"!P s (t:A->bool).
        {x | x IN (s DIFF t) /\ P x} =
        {x | x IN s /\ P x} DIFF {x | x IN t /\ P x}"
   (SET_TAC [])

  return {
    UNION_ASSOC, UNION_IDEMPOT, UNION_COMM, SUBSET_UNION,
    SUBSET_UNION_ABSORPTION, UNION_EMPTY, UNION_UNIV, EMPTY_UNION,
    UNION_SUBSET, UNION_RESTRICT, FORALL_SUBSET_UNION, EXISTS_SUBSET_UNION,
    FORALL_SUBSET_INSERT, EXISTS_SUBSET_INSERT, INTER_ASSOC, INTER_IDEMPOT,
    INTER_COMM, INTER_SUBSET, SUBSET_INTER_ABSORPTION, INTER_EMPTY, INTER_UNIV,
    SUBSET_INTER, INTER_RESTRICT, UNION_OVER_INTER, INTER_OVER_UNION,
    IN_DISJOINT, DISJOINT_SYM, DISJOINT_EMPTY, DISJOINT_EMPTY_REFL,
    DISJOINT_UNION, DISJOINT_SING, DIFF_EMPTY, EMPTY_DIFF, DIFF_UNIV,
    DIFF_DIFF, DIFF_EQ_EMPTY, SUBSET_DIFF, COMPL_COMPL, DIFF_RESTRICT }

/- ---------------------------------------------------------------------- -/
/- Insertion and deletion.  (sets.ml 666-822)                             -/
/- ---------------------------------------------------------------------- -/

/-- The insertion and deletion theorems of sets.ml 666-822.  THIRTY-FOUR
    theorems - the largest single operator section in the file.  This is the
    section that makes reasoning about set ENUMERATIONS work: HOL Light's
    parser desugars `{a,b,c}` into an `INSERT` chain ending in `EMPTY`
    (parser.ml 304-305, mirrored in `HolCore.Parser.pmk_set_enum`), so the
    `INSERT`/`IN_INSERT`/`NOT_INSERT_EMPTY` family below is exactly what lets
    those enumeration terms be reasoned about.  Twenty-six are a bare
    `SET_TAC[]`; the eight structured ones are `DECOMPOSITION` (677),
    `SET_CASES` (683), `INSERT_UNION` (712), `INSERT_INTER` (722),
    `INSERT_DIFF` (745), `INSERT_AC` (758), `DELETE_INSERT` (804) and none use
    the `ASM SET_TAC` variant.  There are ZERO `THENL` anywhere in this
    section - every structured proof is a straight left-associative `THEN`
    chain. -/
structure SetsInsertDelete where
  /-- `COMPONENT` (sets.ml 669): `!x:A. !s. x IN (x INSERT s)`.  `SET_TAC[]`. -/
  COMPONENT : thm
  /-- `DECOMPOSITION` (sets.ml 673):
      `!s:A->bool. !x. x IN s <=> ?t. (s = x INSERT t) /\ ~(x IN t)`. -/
  DECOMPOSITION : thm
  /-- `SET_CASES` (sets.ml 679):
      `!s:A->bool. (s = EMPTY) \/ ?x:A. ?t. (s = x INSERT t) /\ ~(x IN t)`. -/
  SET_CASES : thm
  /-- `ABSORPTION` (sets.ml 683):
      `!x:A. !s. x IN s <=> (x INSERT s = s)`.  `SET_TAC[]`. -/
  ABSORPTION : thm
  /-- `INSERT_INSERT` (sets.ml 687):
      `!x:A. !s. x INSERT (x INSERT s) = x INSERT s`.  `SET_TAC[]`. -/
  INSERT_INSERT : thm
  /-- `INSERT_COMM` (sets.ml 691):
      `!x:A. !y s. x INSERT (y INSERT s) = y INSERT (x INSERT s)`.
      `SET_TAC[]`. -/
  INSERT_COMM : thm
  /-- `INSERT_UNIV` (sets.ml 695): `!x:A. x INSERT UNIV = UNIV`.  `SET_TAC[]`. -/
  INSERT_UNIV : thm
  /-- `NOT_INSERT_EMPTY` (sets.ml 699):
      `!x:A. !s. ~(x INSERT s = EMPTY)`.  `SET_TAC[]`. -/
  NOT_INSERT_EMPTY : thm
  /-- `NOT_EMPTY_INSERT` (sets.ml 703):
      `!x:A. !s. ~(EMPTY = x INSERT s)`.  `SET_TAC[]`. -/
  NOT_EMPTY_INSERT : thm
  /-- `INSERT_UNION` (sets.ml 707):
      `(x INSERT s) UNION t = if x IN t then s UNION t
       else x INSERT (s UNION t)`.  `COND_CASES_TAC` proof. -/
  INSERT_UNION : thm
  /-- `INSERT_UNION_EQ` (sets.ml 713):
      `!x:A. !s t. (x INSERT s) UNION t = x INSERT (s UNION t)`.  `SET_TAC[]`. -/
  INSERT_UNION_EQ : thm
  /-- `INSERT_INTER` (sets.ml 717):
      `(x INSERT s) INTER t = if x IN t then x INSERT (s INTER t)
       else s INTER t`.  `COND_CASES_TAC` proof. -/
  INSERT_INTER : thm
  /-- `DISJOINT_INSERT` (sets.ml 723):
      `DISJOINT (x INSERT s) t <=> (DISJOINT s t) /\ ~(x IN t)`.  `SET_TAC[]`. -/
  DISJOINT_INSERT : thm
  /-- `INSERT_SUBSET` (sets.ml 727):
      `!x:A. !s t. (x INSERT s) SUBSET t <=> (x IN t /\ s SUBSET t)`.
      `SET_TAC[]`. -/
  INSERT_SUBSET : thm
  /-- `SUBSET_INSERT` (sets.ml 731):
      `!x:A. !s. ~(x IN s) ==> !t. s SUBSET (x INSERT t) <=> s SUBSET t`.
      `SET_TAC[]`. -/
  SUBSET_INSERT : thm
  /-- `INSERT_DIFF` (sets.ml 735):
      `(x INSERT s) DIFF t = if x IN t then s DIFF t
       else x INSERT (s DIFF t)`.  `COND_CASES_TAC` proof. -/
  INSERT_DIFF : thm
  /-- `INSERT_AC` (sets.ml 741): the two-conjunct insert AC theorem.
      `REWRITE_TAC[INSERT_COMM; INSERT_INSERT]`. -/
  INSERT_AC : thm
  /-- `INTER_ACI` (sets.ml 746): the five-conjunct intersection ACI theorem.
      `SET_TAC[]`. -/
  INTER_ACI : thm
  /-- `UNION_ACI` (sets.ml 754): the five-conjunct union ACI theorem.
      `SET_TAC[]`. -/
  UNION_ACI : thm
  /-- `DELETE_NON_ELEMENT` (sets.ml 762):
      `!x:A. !s. ~(x IN s) <=> (s DELETE x = s)`.  `SET_TAC[]`. -/
  DELETE_NON_ELEMENT : thm
  /-- `IN_DELETE_EQ` (sets.ml 766):
      `(x IN s <=> x' IN s) <=> (x IN (s DELETE x') <=> x' IN (s DELETE x))`.
      `SET_TAC[]`. -/
  IN_DELETE_EQ : thm
  /-- `EMPTY_DELETE` (sets.ml 771): `!x:A. EMPTY DELETE x = EMPTY`.
      `SET_TAC[]`. -/
  EMPTY_DELETE : thm
  /-- `DELETE_DELETE` (sets.ml 775):
      `!x:A. !s. (s DELETE x) DELETE x = s DELETE x`.  `SET_TAC[]`. -/
  DELETE_DELETE : thm
  /-- `DELETE_COMM` (sets.ml 779):
      `!x:A. !y. !s. (s DELETE x) DELETE y = (s DELETE y) DELETE x`.
      `SET_TAC[]`. -/
  DELETE_COMM : thm
  /-- `DELETE_SUBSET` (sets.ml 783): `!x:A. !s. (s DELETE x) SUBSET s`.
      `SET_TAC[]`. -/
  DELETE_SUBSET : thm
  /-- `SUBSET_DELETE` (sets.ml 787):
      `!x:A. !s t. s SUBSET (t DELETE x) <=> ~(x IN s) /\ (s SUBSET t)`.
      `SET_TAC[]`. -/
  SUBSET_DELETE : thm
  /-- `SUBSET_INSERT_DELETE` (sets.ml 791):
      `!x:A. !s t. s SUBSET (x INSERT t) <=> ((s DELETE x) SUBSET t)`.
      `SET_TAC[]`. -/
  SUBSET_INSERT_DELETE : thm
  /-- `DIFF_INSERT` (sets.ml 795):
      `!s t. !x:A. s DIFF (x INSERT t) = (s DELETE x) DIFF t`.  `SET_TAC[]`. -/
  DIFF_INSERT : thm
  /-- `PSUBSET_INSERT_SUBSET` (sets.ml 799):
      `!s t. s PSUBSET t <=> ?x:A. ~(x IN s) /\ (x INSERT s) SUBSET t`.
      `SET_TAC[]`. -/
  PSUBSET_INSERT_SUBSET : thm
  /-- `DELETE_INSERT` (sets.ml 803):
      `(x INSERT s) DELETE y = if x = y then s DELETE y
       else x INSERT (s DELETE y)`.  `COND_CASES_TAC` proof. -/
  DELETE_INSERT : thm
  /-- `INSERT_DELETE` (sets.ml 810):
      `!x:A. !s. x IN s ==> (x INSERT (s DELETE x) = s)`.  `SET_TAC[]`. -/
  INSERT_DELETE : thm
  /-- `DELETE_INTER` (sets.ml 814):
      `!s t. !x:A. (s DELETE x) INTER t = (s INTER t) DELETE x`.  `SET_TAC[]`. -/
  DELETE_INTER : thm
  /-- `DISJOINT_DELETE_SYM` (sets.ml 818):
      `!s t. !x:A. DISJOINT (s DELETE x) t = DISJOINT (t DELETE x) s`.
      `SET_TAC[]`. -/
  DISJOINT_DELETE_SYM : thm
  deriving Inhabited

@[nospecialize]
def setupSetsInsertDelete [HolBase] (S : SetsCore) (P : SetsProps)
    (SIn : SetsInclusion) (MESON_TAC : List thm → tactic) :
    ExceptT String IO SetsInsertDelete := do
  let SET_TAC := SET_TAC S P MESON_TAC
  let { IN_INSERT, .. } := P
  let { MEMBER_NOT_EMPTY, .. } := SIn

  let COMPONENT ← prove
   r"!x:A. !s. x IN (x INSERT s)"
   (SET_TAC [])

  let DECOMPOSITION ← prove
   r"!s:A->bool. !x. x IN s <=> ?t. (s = x INSERT t) /\ ~(x IN t)"
   (REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [IN_INSERT] THEN EXISTS_TAC (← q r"s DELETE x:A") THEN
    POP_ASSUM MP_TAC THEN SET_TAC [])

  let SET_CASES ← prove
   r"!s:A->bool. (s = EMPTY) \/ ?x:A. ?t. (s = x INSERT t) /\ ~(x IN t)"
   (MESON_TAC [MEMBER_NOT_EMPTY, DECOMPOSITION])

  let ABSORPTION ← prove
   r"!x:A. !s. x IN s <=> (x INSERT s = s)"
   (SET_TAC [])

  let INSERT_INSERT ← prove
   r"!x:A. !s. x INSERT (x INSERT s) = x INSERT s"
   (SET_TAC [])

  let INSERT_COMM ← prove
   r"!x:A. !y s. x INSERT (y INSERT s) = y INSERT (x INSERT s)"
   (SET_TAC [])

  let INSERT_UNIV ← prove
   r"!x:A. x INSERT UNIV = UNIV"
   (SET_TAC [])

  let NOT_INSERT_EMPTY ← prove
   r"!x:A. !s. ~(x INSERT s = EMPTY)"
   (SET_TAC [])

  let NOT_EMPTY_INSERT ← prove
   r"!x:A. !s. ~(EMPTY = x INSERT s)"
   (SET_TAC [])

  let INSERT_UNION ← prove
   r"!x:A. !s t. (x INSERT s) UNION t =
               if x IN t then s UNION t else x INSERT (s UNION t)"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    POP_ASSUM MP_TAC THEN SET_TAC [])

  let INSERT_UNION_EQ ← prove
   r"!x:A. !s t. (x INSERT s) UNION t = x INSERT (s UNION t)"
   (SET_TAC [])

  let INSERT_INTER ← prove
   r"!x:A. !s t. (x INSERT s) INTER t =
               if x IN t then x INSERT (s INTER t) else s INTER t"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    POP_ASSUM MP_TAC THEN SET_TAC [])

  let DISJOINT_INSERT ← prove
   r"!(x:A) s t. DISJOINT (x INSERT s) t <=> (DISJOINT s t) /\ ~(x IN t)"
   (SET_TAC [])

  let INSERT_SUBSET ← prove
   r"!x:A. !s t. (x INSERT s) SUBSET t <=> (x IN t /\ s SUBSET t)"
   (SET_TAC [])

  let SUBSET_INSERT ← prove
   r"!x:A. !s. ~(x IN s) ==> !t. s SUBSET (x INSERT t) <=> s SUBSET t"
   (SET_TAC [])

  let INSERT_DIFF ← prove
   r"!s t. !x:A. (x INSERT s) DIFF t =
               if x IN t then s DIFF t else x INSERT (s DIFF t)"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    POP_ASSUM MP_TAC THEN SET_TAC [])

  let INSERT_AC ← prove
   r"(x:A) INSERT (y INSERT s) = y INSERT (x INSERT s) /\
   x INSERT (x INSERT s) = x INSERT s"
   (REWRITE_TAC [INSERT_COMM, INSERT_INSERT])

  let INTER_ACI ← prove
   r"((p:A->bool) INTER q = q INTER p) /\
   ((p INTER q) INTER r = p INTER q INTER r) /\
   (p INTER q INTER r = q INTER p INTER r) /\
   (p INTER p = p) /\
   (p INTER p INTER q = p INTER q)"
   (SET_TAC [])

  let UNION_ACI ← prove
   r"((p:A->bool) UNION q = q UNION p) /\
   ((p UNION q) UNION r = p UNION q UNION r) /\
   (p UNION q UNION r = q UNION p UNION r) /\
   (p UNION p = p) /\
   (p UNION p UNION q = p UNION q)"
   (SET_TAC [])

  let DELETE_NON_ELEMENT ← prove
   r"!x:A. !s. ~(x IN s) <=> (s DELETE x = s)"
   (SET_TAC [])

  let IN_DELETE_EQ ← prove
   r"!s x. !x':A.
     (x IN s <=> x' IN s) <=> (x IN (s DELETE x') <=> x' IN (s DELETE x))"
   (SET_TAC [])

  let EMPTY_DELETE ← prove
   r"!x:A. EMPTY DELETE x = EMPTY"
   (SET_TAC [])

  let DELETE_DELETE ← prove
   r"!x:A. !s. (s DELETE x) DELETE x = s DELETE x"
   (SET_TAC [])

  let DELETE_COMM ← prove
   r"!x:A. !y. !s. (s DELETE x) DELETE y = (s DELETE y) DELETE x"
   (SET_TAC [])

  let DELETE_SUBSET ← prove
   r"!x:A. !s. (s DELETE x) SUBSET s"
   (SET_TAC [])

  let SUBSET_DELETE ← prove
   r"!x:A. !s t. s SUBSET (t DELETE x) <=> ~(x IN s) /\ (s SUBSET t)"
   (SET_TAC [])

  let SUBSET_INSERT_DELETE ← prove
   r"!x:A. !s t. s SUBSET (x INSERT t) <=> ((s DELETE x) SUBSET t)"
   (SET_TAC [])

  let DIFF_INSERT ← prove
   r"!s t. !x:A. s DIFF (x INSERT t) = (s DELETE x) DIFF t"
   (SET_TAC [])

  let PSUBSET_INSERT_SUBSET ← prove
   r"!s t. s PSUBSET t <=> ?x:A. ~(x IN s) /\ (x INSERT s) SUBSET t"
   (SET_TAC [])

  let DELETE_INSERT ← prove
   r"!x:A. !y s.
      (x INSERT s) DELETE y =
        if x = y then s DELETE y else x INSERT (s DELETE y)"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    POP_ASSUM MP_TAC THEN SET_TAC [])

  let INSERT_DELETE ← prove
   r"!x:A. !s. x IN s ==> (x INSERT (s DELETE x) = s)"
   (SET_TAC [])

  let DELETE_INTER ← prove
   r"!s t. !x:A. (s DELETE x) INTER t = (s INTER t) DELETE x"
   (SET_TAC [])

  let DISJOINT_DELETE_SYM ← prove
   r"!s t. !x:A. DISJOINT (s DELETE x) t = DISJOINT (t DELETE x) s"
   (SET_TAC [])


  return {
    COMPONENT, DECOMPOSITION, SET_CASES, ABSORPTION, INSERT_INSERT,
    INSERT_COMM, INSERT_UNIV, NOT_INSERT_EMPTY, NOT_EMPTY_INSERT, INSERT_UNION,
    INSERT_UNION_EQ, INSERT_INTER, DISJOINT_INSERT, INSERT_SUBSET,
    SUBSET_INSERT, INSERT_DIFF, INSERT_AC, INTER_ACI, UNION_ACI,
    DELETE_NON_ELEMENT, IN_DELETE_EQ, EMPTY_DELETE, DELETE_DELETE, DELETE_COMM,
    DELETE_SUBSET, SUBSET_DELETE, SUBSET_INSERT_DELETE, DIFF_INSERT,
    PSUBSET_INSERT_SUBSET, DELETE_INSERT, INSERT_DELETE, DELETE_INTER,
    DISJOINT_DELETE_SYM }

/- ---------------------------------------------------------------------- -/
/- Multiple union.  (sets.ml 823-903)                                     -/
/- ---------------------------------------------------------------------- -/

/-- The multiple-union (`UNIONS`) theorems of sets.ml 833-903.  EIGHTEEN
    theorems.  Thirteen are a bare `SET_TAC[]`; the five structured ones -
    `INTER_UNIONS` (867), `UNIONS_UNIV` (895), `UNIONS_INSERT_EMPTY` (899) and
    `UNIONS_DELETE_EMPTY` (903) - each open by pushing extensionality with
    `ONCE_REWRITE_TAC[EXTENSION]` (or plain `REWRITE_TAC` for `UNIONS_UNIV`),
    then rewrite membership, then finish with `MESON_TAC`.  ZERO `THENL`. -/
structure SetsUnions where
  /-- `UNIONS_0` (sets.ml 826): `UNIONS {}:A->bool = {}`.  `SET_TAC[]`. -/
  UNIONS_0 : thm
  /-- `UNIONS_1` (sets.ml 830): `!s:A->bool. UNIONS {s} = s`.  `SET_TAC[]`. -/
  UNIONS_1 : thm
  /-- `UNIONS_2` (sets.ml 834):
      `!s (t:A->bool). UNIONS {s,t} = s UNION t`.  `SET_TAC[]`. -/
  UNIONS_2 : thm
  /-- `UNIONS_INSERT` (sets.ml 838):
      `!(s:A->bool) u. UNIONS (s INSERT u) = s UNION (UNIONS u)`.  `SET_TAC[]`. -/
  UNIONS_INSERT : thm
  /-- `FORALL_IN_UNIONS` (sets.ml 842):
      `!P s. (!x:A. x IN UNIONS s ==> P x) <=>
       !t x. t IN s /\ x IN t ==> P x`.  `SET_TAC[]`. -/
  FORALL_IN_UNIONS : thm
  /-- `EXISTS_IN_UNIONS` (sets.ml 846):
      `!P s. (?x:A. x IN UNIONS s /\ P x) <=>
       (?t x. t IN s /\ x IN t /\ P x)`.  `SET_TAC[]`. -/
  EXISTS_IN_UNIONS : thm
  /-- `EMPTY_UNIONS` (sets.ml 850):
      `!s. (UNIONS s = {}) <=> !t:A->bool. t IN s ==> t = {}`.  `SET_TAC[]`. -/
  EMPTY_UNIONS : thm
  /-- `INTER_UNIONS` (sets.ml 854): the two-conjunct distribution of `INTER`
      over `UNIONS {x INTER t | x IN s}`.
      `ONCE_REWRITE_TAC[EXTENSION] THEN
       REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_INTER] THEN MESON_TAC[IN_INTER]`. -/
  INTER_UNIONS : thm
  /-- `UNIONS_SUBSET` (sets.ml 861):
      `!f (t:A->bool). UNIONS f SUBSET t <=> !s. s IN f ==> s SUBSET t`.
      `SET_TAC[]`. -/
  UNIONS_SUBSET : thm
  /-- `SUBSET_UNIONS` (sets.ml 865):
      `!(f:(A->bool)->bool) g. f SUBSET g ==> UNIONS f SUBSET UNIONS g`.
      `SET_TAC[]`. -/
  SUBSET_UNIONS : thm
  /-- `UNIONS_UNION` (sets.ml 869):
      `!s t:(A->bool)->bool. UNIONS(s UNION t) = (UNIONS s) UNION (UNIONS t)`.
      `SET_TAC[]`. -/
  UNIONS_UNION : thm
  /-- `INTERS_UNION` (sets.ml 873):
      `!s t:(A->bool)->bool. INTERS (s UNION t) = INTERS s INTER INTERS t`.
      `SET_TAC[]`. -/
  INTERS_UNION : thm
  /-- `UNIONS_MONO` (sets.ml 877):
      `!s t:(A->bool)->bool.
       (!x. x IN s ==> ?y. y IN t /\ x SUBSET y) ==> UNIONS s SUBSET UNIONS t`.
      `SET_TAC[]`. -/
  UNIONS_MONO : thm
  /-- `UNIONS_MONO_IMAGE` (sets.ml 882):
      `!(f:A->B->bool) g s. (!x. x IN s ==> f x SUBSET g x)
       ==> UNIONS(IMAGE f s) SUBSET UNIONS(IMAGE g s)`.  `SET_TAC[]`. -/
  UNIONS_MONO_IMAGE : thm
  /-- `UNIONS_UNIV` (sets.ml 888): `UNIONS (:A->bool) = (:A)`.
      `REWRITE_TAC[EXTENSION; IN_UNIONS; IN_UNIV] THEN MESON_TAC[IN_SING]`. -/
  UNIONS_UNIV : thm
  /-- `UNIONS_INSERT_EMPTY` (sets.ml 893):
      `!s:(A->bool)->bool. UNIONS({} INSERT s) = UNIONS s`.
      `ONCE_REWRITE_TAC[EXTENSION] THEN REWRITE_TAC[IN_UNIONS; IN_INSERT] THEN
       MESON_TAC[NOT_IN_EMPTY]`. -/
  UNIONS_INSERT_EMPTY : thm
  /-- `UNIONS_DELETE_EMPTY` (sets.ml 898):
      `!s:(A->bool)->bool. UNIONS(s DELETE {}) = UNIONS s`.
      `ONCE_REWRITE_TAC[EXTENSION] THEN REWRITE_TAC[IN_UNIONS; IN_DELETE] THEN
       MESON_TAC[NOT_IN_EMPTY]`. -/
  UNIONS_DELETE_EMPTY : thm
  deriving Inhabited

@[nospecialize]
def setupSetsUnions [HolBase] (S : SetsCore) (P : SetsProps)
    (MESON_TAC : List thm → tactic) :
    ExceptT String IO SetsUnions := do
  let SET_TAC := SET_TAC S P MESON_TAC
  let { EXTENSION, IN_ELIM_THM, .. } := S
  let { NOT_IN_EMPTY, IN_UNIV, IN_UNIONS, IN_INTER, IN_INSERT, IN_DELETE,
        IN_SING, .. } := P

  let UNIONS_0 ← prove
   r"UNIONS {}:A->bool = {}"
   (SET_TAC [])

  let UNIONS_1 ← prove
   r"!s:A->bool. UNIONS {s} = s"
   (SET_TAC [])

  let UNIONS_2 ← prove
   r"!s (t:A->bool). UNIONS {s,t} = s UNION t"
   (SET_TAC [])

  let UNIONS_INSERT ← prove
   r"!(s:A->bool) u. UNIONS (s INSERT u) = s UNION (UNIONS u)"
   (SET_TAC [])

  let FORALL_IN_UNIONS ← prove
   r"!P s. (!x:A. x IN UNIONS s ==> P x) <=> !t x. t IN s /\ x IN t ==> P x"
   (SET_TAC [])

  let EXISTS_IN_UNIONS ← prove
   r"!P s. (?x:A. x IN UNIONS s /\ P x) <=> (?t x. t IN s /\ x IN t /\ P x)"
   (SET_TAC [])

  let EMPTY_UNIONS ← prove
   r"!s. (UNIONS s = {}) <=> !t:A->bool. t IN s ==> t = {}"
   (SET_TAC [])

  let INTER_UNIONS ← prove
   r"(!s (t:A->bool). UNIONS s INTER t = UNIONS {x INTER t | x IN s}) /\
   (!s (t:A->bool). t INTER UNIONS s = UNIONS {t INTER x | x IN s})"
   (ONCE_REWRITE_TAC [EXTENSION] THEN
    REWRITE_TAC [IN_UNIONS, IN_ELIM_THM, IN_INTER] THEN
    MESON_TAC [IN_INTER])

  let UNIONS_SUBSET ← prove
   r"!f (t:A->bool). UNIONS f SUBSET t <=> !s. s IN f ==> s SUBSET t"
   (SET_TAC [])

  let SUBSET_UNIONS ← prove
   r"!(f:(A->bool)->bool) g. f SUBSET g ==> UNIONS f SUBSET UNIONS g"
   (SET_TAC [])

  let UNIONS_UNION ← prove
   r"!s t:(A->bool)->bool. UNIONS(s UNION t) = (UNIONS s) UNION (UNIONS t)"
   (SET_TAC [])

  let INTERS_UNION ← prove
   r"!s t:(A->bool)->bool. INTERS (s UNION t) = INTERS s INTER INTERS t"
   (SET_TAC [])

  let UNIONS_MONO ← prove
   r"!s t:(A->bool)->bool.
    (!x. x IN s ==> ?y. y IN t /\ x SUBSET y) ==> UNIONS s SUBSET UNIONS t"
   (SET_TAC [])

  let UNIONS_MONO_IMAGE ← prove
   r"!(f:A->B->bool) g s.
        (!x. x IN s ==> f x SUBSET g x)
        ==> UNIONS(IMAGE f s) SUBSET UNIONS(IMAGE g s)"
   (SET_TAC [])

  let UNIONS_UNIV ← prove
   r"UNIONS (:A->bool) = (:A)"
   (REWRITE_TAC [EXTENSION, IN_UNIONS, IN_UNIV] THEN
    MESON_TAC [IN_SING])

  let UNIONS_INSERT_EMPTY ← prove
   r"!s:(A->bool)->bool. UNIONS({} INSERT s) = UNIONS s"
   (ONCE_REWRITE_TAC [EXTENSION] THEN
    REWRITE_TAC [IN_UNIONS, IN_INSERT] THEN MESON_TAC [NOT_IN_EMPTY])

  let UNIONS_DELETE_EMPTY ← prove
   r"!s:(A->bool)->bool. UNIONS(s DELETE {}) = UNIONS s"
   (ONCE_REWRITE_TAC [EXTENSION] THEN
    REWRITE_TAC [IN_UNIONS, IN_DELETE] THEN MESON_TAC [NOT_IN_EMPTY])


  return {
    UNIONS_0, UNIONS_1, UNIONS_2, UNIONS_INSERT, FORALL_IN_UNIONS,
    EXISTS_IN_UNIONS, EMPTY_UNIONS, INTER_UNIONS, UNIONS_SUBSET, SUBSET_UNIONS,
    UNIONS_UNION, INTERS_UNION, UNIONS_MONO, UNIONS_MONO_IMAGE, UNIONS_UNIV,
    UNIONS_INSERT_EMPTY, UNIONS_DELETE_EMPTY }

/- ---------------------------------------------------------------------- -/
/- Multiple intersection.  (sets.ml 904-950)                              -/
/- ---------------------------------------------------------------------- -/

/-- The multiple-intersection (`INTERS`) theorems of sets.ml 906-950.  TEN
    theorems, EVERY one a bare `SET_TAC[]`.  No structured proofs, no `THENL`,
    no `ASM SET_TAC`. -/
structure SetsInters where
  /-- `INTERS_0` (sets.ml 907): `INTERS {} = (:A)`.  `SET_TAC[]`. -/
  INTERS_0 : thm
  /-- `INTERS_1` (sets.ml 911): `!s:A->bool. INTERS {s} = s`.  `SET_TAC[]`. -/
  INTERS_1 : thm
  /-- `INTERS_2` (sets.ml 915):
      `!s (t:A->bool). INTERS {s,t} = s INTER t`.  `SET_TAC[]`. -/
  INTERS_2 : thm
  /-- `INTERS_INSERT` (sets.ml 919):
      `!(s:A->bool) u. INTERS (s INSERT u) = s INTER (INTERS u)`.  `SET_TAC[]`. -/
  INTERS_INSERT : thm
  /-- `SUBSET_INTERS` (sets.ml 923):
      `!(s:A->bool) f. s SUBSET INTERS f <=> (!t. t IN f ==> s SUBSET t)`.
      `SET_TAC[]`. -/
  SUBSET_INTERS : thm
  /-- `INTERS_SUBSET` (sets.ml 927):
      `!u s:A->bool. ~(u = {}) /\ (!t. t IN u ==> t SUBSET s)
       ==> INTERS u SUBSET s`.  `SET_TAC[]`. -/
  INTERS_SUBSET : thm
  /-- `INTERS_SUBSET_STRONG` (sets.ml 932):
      `!u s:A->bool. (?t. t IN u /\ t SUBSET s) ==> INTERS u SUBSET s`.
      `SET_TAC[]`. -/
  INTERS_SUBSET_STRONG : thm
  /-- `INTERS_ANTIMONO` (sets.ml 936):
      `!(f:(A->bool)->bool) g. g SUBSET f ==> INTERS f SUBSET INTERS g`.
      `SET_TAC[]`. -/
  INTERS_ANTIMONO : thm
  /-- `INTERS_EQ_UNIV` (sets.ml 940):
      `!f. INTERS f = (:A) <=> !s. s IN f ==> s = (:A)`.  `SET_TAC[]`. -/
  INTERS_EQ_UNIV : thm
  /-- `INTERS_ANTIMONO_GEN` (sets.ml 944):
      `!s (t:(A->bool)->bool). (!y. y IN t ==> ?x. x IN s /\ x SUBSET y)
       ==> INTERS s SUBSET INTERS t`.  `SET_TAC[]`. -/
  INTERS_ANTIMONO_GEN : thm
  deriving Inhabited

@[nospecialize]
def setupSetsInters [HolBase] (S : SetsCore) (P : SetsProps)
    (MESON_TAC : List thm → tactic) :
    ExceptT String IO SetsInters := do
  let SET_TAC := SET_TAC S P MESON_TAC

  let INTERS_0 ← prove
   r"INTERS {} = (:A)"
   (SET_TAC [])

  let INTERS_1 ← prove
   r"!s:A->bool. INTERS {s} = s"
   (SET_TAC [])

  let INTERS_2 ← prove
   r"!s (t:A->bool). INTERS {s,t} = s INTER t"
   (SET_TAC [])

  let INTERS_INSERT ← prove
   r"!(s:A->bool) u. INTERS (s INSERT u) = s INTER (INTERS u)"
   (SET_TAC [])

  let SUBSET_INTERS ← prove
   r"!(s:A->bool) f. s SUBSET INTERS f <=> (!t. t IN f ==> s SUBSET t)"
   (SET_TAC [])

  let INTERS_SUBSET ← prove
   r"!u s:A->bool.
    ~(u = {}) /\ (!t. t IN u ==> t SUBSET s) ==> INTERS u SUBSET s"
   (SET_TAC [])

  let INTERS_SUBSET_STRONG ← prove
   r"!u s:A->bool. (?t. t IN u /\ t SUBSET s) ==> INTERS u SUBSET s"
   (SET_TAC [])

  let INTERS_ANTIMONO ← prove
   r"!(f:(A->bool)->bool) g. g SUBSET f ==> INTERS f SUBSET INTERS g"
   (SET_TAC [])

  let INTERS_EQ_UNIV ← prove
   r"!f. INTERS f = (:A) <=> !s. s IN f ==> s = (:A)"
   (SET_TAC [])

  let INTERS_ANTIMONO_GEN ← prove
   r"!s (t:(A->bool)->bool).
        (!y. y IN t ==> ?x. x IN s /\ x SUBSET y)
        ==> INTERS s SUBSET INTERS t"
   (SET_TAC [])


  return {
    INTERS_0, INTERS_1, INTERS_2, INTERS_INSERT, SUBSET_INTERS, INTERS_SUBSET,
    INTERS_SUBSET_STRONG, INTERS_ANTIMONO, INTERS_EQ_UNIV, INTERS_ANTIMONO_GEN }

/- ---------------------------------------------------------------------- -/
/- Image under a function.  (sets.ml 951-1056)                            -/
/- ---------------------------------------------------------------------- -/

/-- The `IMAGE` theorems of sets.ml 953-1056.  TWENTY-ONE theorems.  Nine are
    a bare `SET_TAC[]` (`IMAGE_DIFF_INJ`, `IMAGE_DIFF_INJ_ALT`,
    `IMAGE_DELETE_INJ`, `IMAGE_DELETE_INJ_ALT`, `FORALL_IN_IMAGE_2`,
    `SIMPLE_IMAGE_GEN`, `FUN_IN_IMAGE`, `SURJECTIVE_IMAGE_EQ`, `IMAGE_EQ`);
    the other twelve are `REWRITE_TAC`/`MESON_TAC` reductions.  Two are single
    tactics (`IMAGE_ID`, `IMAGE_I`).  `IMAGE_CONST` uses `COND_CASES_TAC` and
    `ASM_MESON_TAC[MEMBER_NOT_EMPTY]`; `IMAGE_UNIONS` is a five-step rewrite
    chain.  ZERO `THENL` in the whole range. -/
structure SetsImage where
  /-- `IMAGE_CLAUSES` (sets.ml 954): the pair
      `IMAGE f {} = {}` and `IMAGE f (x INSERT s) = f x INSERT IMAGE f s`. -/
  IMAGE_CLAUSES : thm
  /-- `IMAGE_UNION` (sets.ml 960):
      `!(f:A->B) s t. IMAGE f (s UNION t) = IMAGE f s UNION IMAGE f t`. -/
  IMAGE_UNION : thm
  /-- `IMAGE_ID` (sets.ml 964): `!s:A->bool. IMAGE (\x. x) s = s`. -/
  IMAGE_ID : thm
  /-- `IMAGE_I` (sets.ml 968): `!s:A->bool. IMAGE I s = s`. -/
  IMAGE_I : thm
  /-- `IMAGE_o` (sets.ml 972):
      `!(f:B->C) (g:A->B) s. IMAGE (f o g) s = IMAGE f (IMAGE g s)`. -/
  IMAGE_o : thm
  /-- `IMAGE_SUBSET` (sets.ml 976):
      `!(f:A->B) s t. s SUBSET t ==> IMAGE f s SUBSET IMAGE f t`. -/
  IMAGE_SUBSET : thm
  /-- `IMAGE_INTER_INJ` (sets.ml 980): injective image over `INTER`. -/
  IMAGE_INTER_INJ : thm
  /-- `IMAGE_DIFF_INJ` (sets.ml 986): injective image over `DIFF`.
      `SET_TAC[]`. -/
  IMAGE_DIFF_INJ : thm
  /-- `IMAGE_DIFF_INJ_ALT` (sets.ml 992): alt form.  `SET_TAC[]`. -/
  IMAGE_DIFF_INJ_ALT : thm
  /-- `IMAGE_DELETE_INJ` (sets.ml 998): injective image over `DELETE`.
      `SET_TAC[]`. -/
  IMAGE_DELETE_INJ : thm
  /-- `IMAGE_DELETE_INJ_ALT` (sets.ml 1004): alt form.  `SET_TAC[]`. -/
  IMAGE_DELETE_INJ_ALT : thm
  /-- `IMAGE_EQ_EMPTY` (sets.ml 1010):
      `!(f:A->B) s. IMAGE f s = {} <=> s = {}`. -/
  IMAGE_EQ_EMPTY : thm
  /-- `FORALL_IN_IMAGE_2` (sets.ml 1014): pointwise `!`-over-image.
      `SET_TAC[]`. -/
  FORALL_IN_IMAGE_2 : thm
  /-- `IMAGE_CONST` (sets.ml 1019):
      `!(s:A->bool) (c:B). IMAGE (\x. c) s = if s = {} then {} else {c}`. -/
  IMAGE_CONST : thm
  /-- `SIMPLE_IMAGE` (sets.ml 1026):
      `!(f:A->B) s. {f x | x IN s} = IMAGE f s`. -/
  SIMPLE_IMAGE : thm
  /-- `SIMPLE_IMAGE_GEN` (sets.ml 1030):
      `!(f:A->B) P. {f x | P x} = IMAGE f {x | P x}`.  `SET_TAC[]`. -/
  SIMPLE_IMAGE_GEN : thm
  /-- `IMAGE_UNIONS` (sets.ml 1034):
      `!(f:A->B) s. IMAGE f (UNIONS s) = UNIONS (IMAGE (IMAGE f) s)`. -/
  IMAGE_UNIONS : thm
  /-- `FUN_IN_IMAGE` (sets.ml 1042):
      `!(f:A->B) s x. x IN s ==> f x IN IMAGE f s`.  `SET_TAC[]`. -/
  FUN_IN_IMAGE : thm
  /-- `SURJECTIVE_IMAGE_EQ` (sets.ml 1046): surjective image equals the
      codomain.  `SET_TAC[]`. -/
  SURJECTIVE_IMAGE_EQ : thm
  /-- `IMAGE_EQ` (sets.ml 1052):
      `!(f:A->B) g s. (!x. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE g s`.
      `SET_TAC[]`. -/
  IMAGE_EQ : thm
  deriving Inhabited

@[nospecialize]
def setupSetsImage [HolBase] (S : SetsCore) (P : SetsProps)
    (SIn : SetsInclusion) (Tr : HolCore.Trivia.TriviaThms) (I_DEF : thm)
    (MESON_TAC : List thm → tactic) (ASM_MESON_TAC : List thm → tactic) :
    ExceptT String IO SetsImage := do
  let SET_TAC := SET_TAC S P MESON_TAC
  let { EXTENSION, IN_ELIM_THM, SUBSET, IMAGE, .. } := S
  let { NOT_IN_EMPTY, IN_UNION, IN_UNIONS, IN_INTER, IN_INSERT, IN_SING,
        IN_IMAGE, .. } := P
  let { MEMBER_NOT_EMPTY, .. } := SIn
  let { CONJ_ASSOC, UNWIND_THM1, UNWIND_THM2, SWAP_EXISTS_THM,
        LEFT_AND_EXISTS_THM, .. } := HolBase.T
  let { o_THM, .. } := Tr

  let IMAGE_CLAUSES ← prove
   r"(IMAGE (f:A->B) {} = {}) /\
   (IMAGE f (x INSERT s) = (f x) INSERT (IMAGE f s))"
   (REWRITE_TAC [IMAGE, IN_ELIM_THM, NOT_IN_EMPTY, IN_INSERT, EXTENSION] THEN
    MESON_TAC [])

  let IMAGE_UNION ← prove
   r"!(f:A->B) s t. IMAGE f (s UNION t) = (IMAGE f s) UNION (IMAGE f t)"
   (REWRITE_TAC [EXTENSION, IN_IMAGE, IN_UNION] THEN MESON_TAC [])

  let IMAGE_ID ← prove
   r"!s:A->bool. IMAGE (\x. x) s = s"
   (REWRITE_TAC [EXTENSION, IN_IMAGE, UNWIND_THM1])

  let IMAGE_I ← prove
   r"!s:A->bool. IMAGE I s = s"
   (REWRITE_TAC [I_DEF, IMAGE_ID])

  let IMAGE_o ← prove
   r"!(f:B->C) (g:A->B) s. IMAGE (f o g) s = IMAGE f (IMAGE g s)"
   (REWRITE_TAC [EXTENSION, IN_IMAGE, o_THM] THEN MESON_TAC [])

  let IMAGE_SUBSET ← prove
   r"!(f:A->B) s t. s SUBSET t ==> (IMAGE f s) SUBSET (IMAGE f t)"
   (REWRITE_TAC [SUBSET, IN_IMAGE] THEN MESON_TAC [])

  let IMAGE_INTER_INJ ← prove
   r"!(f:A->B) s t.
        (!x y. f(x) = f(y) ==> x = y)
        ==> (IMAGE f (s INTER t) = (IMAGE f s) INTER (IMAGE f t))"
   (REWRITE_TAC [EXTENSION, IN_IMAGE, IN_INTER] THEN MESON_TAC [])

  let IMAGE_DIFF_INJ ← prove
   r"!f:A->B s t.
        (!x y. x IN s /\ y IN t /\ f x = f y ==> x = y)
        ==> IMAGE f (s DIFF t) = IMAGE f s DIFF IMAGE f t"
   (SET_TAC [])

  let IMAGE_DIFF_INJ_ALT ← prove
   r"!f:A->B s t.
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\ t SUBSET s
        ==> IMAGE f (s DIFF t) = IMAGE f s DIFF IMAGE f t"
   (SET_TAC [])

  let IMAGE_DELETE_INJ ← prove
   r"!f:A->B s a.
        (!x. x IN s /\ f x = f a ==> x = a)
        ==> IMAGE f (s DELETE a) = IMAGE f s DELETE f a"
   (SET_TAC [])

  let IMAGE_DELETE_INJ_ALT ← prove
   r"!f:A->B s a.
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\ a IN s
        ==> IMAGE f (s DELETE a) = IMAGE f s DELETE f a"
   (SET_TAC [])

  let IMAGE_EQ_EMPTY ← prove
   r"!(f:A->B) s. (IMAGE f s = {}) <=> (s = {})"
   (REWRITE_TAC [EXTENSION, NOT_IN_EMPTY, IN_IMAGE] THEN MESON_TAC [])

  let FORALL_IN_IMAGE_2 ← prove
   r"!(f:A->B) P s. (!x y. x IN IMAGE f s /\ y IN IMAGE f s ==> P x y) <=>
                 (!x y. x IN s /\ y IN s ==> P (f x) (f y))"
   (SET_TAC [])

  let IMAGE_CONST ← prove
   r"!(s:A->bool) (c:B). IMAGE (\x. c) s = if s = {} then {} else {c}"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [IMAGE_CLAUSES] THEN
    REWRITE_TAC [EXTENSION, IN_IMAGE, IN_SING] THEN
    ASM_MESON_TAC [MEMBER_NOT_EMPTY])

  let SIMPLE_IMAGE ← prove
   r"!(f:A->B) s. {f x | x IN s} = IMAGE f s"
   (REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_IMAGE] THEN MESON_TAC [])

  let SIMPLE_IMAGE_GEN ← prove
   r"!(f:A->B) P. {f x | P x} = IMAGE f {x | P x}"
   (SET_TAC [])

  let IMAGE_UNIONS ← prove
   r"!(f:A->B) s. IMAGE f (UNIONS s) = UNIONS (IMAGE (IMAGE f) s)"
   (ONCE_REWRITE_TAC [EXTENSION] THEN REWRITE_TAC [IN_UNIONS, IN_IMAGE] THEN
    REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
    REWRITE_TAC [← GSYM CONJ_ASSOC, UNWIND_THM2, IN_IMAGE] THEN
    MESON_TAC [])

  let FUN_IN_IMAGE ← prove
   r"!(f:A->B) s x. x IN s ==> f(x) IN IMAGE f s"
   (SET_TAC [])

  let SURJECTIVE_IMAGE_EQ ← prove
   r"!(f:A->B) s t.
        (!y. y IN t ==> ?x. f x = y) /\ (!x. (f x) IN t <=> x IN s)
        ==> IMAGE f s = t"
   (SET_TAC [])

  let IMAGE_EQ ← prove
   r"!(f:A->B) g s. (!x. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE g s"
   (SET_TAC [])


  return {
    IMAGE_CLAUSES, IMAGE_UNION, IMAGE_ID, IMAGE_I, IMAGE_o, IMAGE_SUBSET,
    IMAGE_INTER_INJ, IMAGE_DIFF_INJ, IMAGE_DIFF_INJ_ALT, IMAGE_DELETE_INJ,
    IMAGE_DELETE_INJ_ALT, IMAGE_EQ_EMPTY, FORALL_IN_IMAGE_2, IMAGE_CONST,
    SIMPLE_IMAGE, SIMPLE_IMAGE_GEN, IMAGE_UNIONS, FUN_IN_IMAGE,
    SURJECTIVE_IMAGE_EQ, IMAGE_EQ }

/- ---------------------------------------------------------------------- -/
/- Misc lemmas.  (sets.ml 1057-1255)                                      -/
/- ---------------------------------------------------------------------- -/

/-- The "misc lemmas" of sets.ml 1059-1255 (the 197-line block).
    THIRTY theorems.  Many are a bare `SET_TAC[]` or a `REWRITE_TAC[...] THEN
    SET_TAC[]`; a handful are genuine `REWRITE_TAC`/`MESON_TAC` reductions,
    and `IMAGE_INTERS_SATURATED_GEN` is a substantial structured proof with a
    LOCAL `lemma`, TWO `THENL`s and several `MATCH_MP_TAC` steps. -/
structure SetsMisc where
  /-- `EMPTY_GSPEC` (sets.ml 1060): `{x:A | F} = {}`.  `SET_TAC[]`. -/
  EMPTY_GSPEC : thm
  /-- `UNIV_GSPEC` (sets.ml 1064): `{x | T} = (:A)`.  `SET_TAC[]`. -/
  UNIV_GSPEC : thm
  /-- `SING_GSPEC` (sets.ml 1068): the two `{x | x = a}` / `{x | a = x}`
      forms.  `SET_TAC[]`. -/
  SING_GSPEC : thm
  /-- `SING_ALT` (sets.ml 1073):
      `!s:A->bool. (?x. s = {x}) <=> ?!x. x IN s`.  `SET_TAC[]`. -/
  SING_ALT : thm
  /-- `IN_GSPEC` (sets.ml 1077): `!s:A->bool. {x | x IN s} = s`.
      `SET_TAC[]`. -/
  IN_GSPEC : thm
  /-- `IN_ELIM_PAIR_THM` (sets.ml 1081):
      `!(P:A->B->bool) a b. (a,b) IN {(x,y) | P x y} <=> P a b`.
      `REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[PAIR_EQ]`. -/
  IN_ELIM_PAIR_THM : thm
  /-- `IN_ELIM_TRIPLE_THM` (sets.ml 1085): the two triple forms. -/
  IN_ELIM_TRIPLE_THM : thm
  /-- `IN_ELIM_QUAD_THM` (sets.ml 1090): the three quad forms. -/
  IN_ELIM_QUAD_THM : thm
  /-- `SET_PAIR_THM` (sets.ml 1099):
      `!(P:A#B->bool). {p | P p} = {(a,b) | P(a,b)}`.  A single
      `REWRITE_TAC`. -/
  SET_PAIR_THM : thm
  /-- `SET_PROVE_CASES` (sets.ml 1103): empty/insert case split.
      `MESON_TAC[SET_CASES]`. -/
  SET_PROVE_CASES : thm
  /-- `UNIONS_SINGS_GEN` (sets.ml 1109):
      `!P:A->bool. UNIONS {{x} | P x} = {x | P x}`.
      `REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]`. -/
  UNIONS_SINGS_GEN : thm
  /-- `UNIONS_SINGS` (sets.ml 1113):
      `!s:A->bool. UNIONS {{x} | x IN s} = s`.
      `REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]`. -/
  UNIONS_SINGS : thm
  /-- `IMAGE_INTERS` (sets.ml 1117): injective image over `INTERS`.
      `REWRITE_TAC[INTERS_IMAGE] THEN SET_TAC[]`. -/
  IMAGE_INTERS : thm
  /-- `DIFF_INTERS` (sets.ml 1124):
      `!(u:A->bool) s. u DIFF INTERS s = UNIONS {u DIFF t | t IN s}`.
      `REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]`. -/
  DIFF_INTERS : thm
  /-- `INTERS_UNIONS` (sets.ml 1128):
      `!s. INTERS s = UNIV DIFF (UNIONS {(:A) DIFF t | t IN s})`.
      `REWRITE_TAC[GSYM DIFF_INTERS] THEN SET_TAC[]`. -/
  INTERS_UNIONS : thm
  /-- `UNIONS_INTERS` (sets.ml 1132):
      `!s. UNIONS s = UNIV DIFF (INTERS {(:A) DIFF t | t IN s})`.  A
      `GEN_REWRITE_TAC I [EXTENSION]` reduction. -/
  UNIONS_INTERS : thm
  /-- `UNIONS_DIFF` (sets.ml 1138):
      `!s t:A->bool. UNIONS s DIFF t = UNIONS {x DIFF t | x IN s}`.
      `REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]`. -/
  UNIONS_DIFF : thm
  /-- `DIFF_UNIONS` (sets.ml 1142):
      `!(u:A->bool) s. u DIFF UNIONS s = u INTER INTERS {u DIFF t | t IN s}`.
      `REWRITE_TAC[INTERS_GSPEC] THEN SET_TAC[]`. -/
  DIFF_UNIONS : thm
  /-- `DIFF_UNIONS_NONEMPTY` (sets.ml 1146): nonempty form.
      `REWRITE_TAC[INTERS_GSPEC] THEN SET_TAC[]`. -/
  DIFF_UNIONS_NONEMPTY : thm
  /-- `INTERS_OVER_UNIONS` (sets.ml 1150): the interchange law.  A
      `GEN_REWRITE_TAC I [EXTENSION]` reduction ending in `RIGHT_IMP_EXISTS_THM;
      SKOLEM_THM` and `MESON_TAC[]`. -/
  INTERS_OVER_UNIONS : thm
  /-- `INTER_INTERS` (sets.ml 1160): the two `s INTER INTERS f` forms.
      `REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[...] THEN
      ASM SET_TAC[]`. -/
  INTER_INTERS : thm
  /-- `UNIONS_OVER_INTERS` (sets.ml 1171): the dual interchange law.  A
      `GEN_REWRITE_TAC I [EXTENSION]` reduction using `TAUT`, the negation
      pushers and `GSYM SKOLEM_THM`. -/
  UNIONS_OVER_INTERS : thm
  /-- `UNIONS_EQ_INTERS` (sets.ml 1182):
      `!f:(A->bool)->bool. UNIONS f = INTERS f <=> ?s. f = {s}`.  An inline
      `SET_RULE` rewrite then `SET_TAC[]`. -/
  UNIONS_EQ_INTERS : thm
  /-- `EXISTS_UNIQUE_UNIONS_INTERS` (sets.ml 1188):
      `!P. (?!s:A->bool. P s) <=> UNIONS {s | P s} = INTERS {s | P s}`.
      `REWRITE_TAC[UNIONS_EQ_INTERS] THEN SET_TAC[]`. -/
  EXISTS_UNIQUE_UNIONS_INTERS : thm
  /-- `IMAGE_INTERS_SUBSET` (sets.ml 1192):
      `!(f:A->B) g. IMAGE f (INTERS g) SUBSET INTERS (IMAGE (IMAGE f) g)`.
      `REWRITE_TAC[INTERS_IMAGE] THEN SET_TAC[]`. -/
  IMAGE_INTERS_SUBSET : thm
  /-- `IMAGE_INTER_SUBSET` (sets.ml 1196):
      `!(f:A->B) s t. IMAGE f (s INTER t) SUBSET IMAGE f s INTER IMAGE f t`.
      `SET_TAC[]`. -/
  IMAGE_INTER_SUBSET : thm
  /-- `IMAGE_INTER_SATURATED_GEN` (sets.ml 1200): saturated image over
      `INTER`.  `SET_TAC[]`. -/
  IMAGE_INTER_SATURATED_GEN : thm
  /-- `IMAGE_INTERS_SATURATED_GEN` (sets.ml 1207): saturated image over
      `INTERS`.  The one substantial structured proof of this block, with a
      LOCAL `lemma` and TWO `THENL`s. -/
  IMAGE_INTERS_SATURATED_GEN : thm
  /-- `IMAGE_INTER_SATURATED` (sets.ml 1241): unconditioned form.
      `SET_TAC[]`. -/
  IMAGE_INTER_SATURATED : thm
  /-- `IMAGE_INTERS_SATURATED` (sets.ml 1247): unconditioned form.
      `REPEAT STRIP_TAC THEN MATCH_MP_TAC IMAGE_INTERS_SATURATED_GEN THEN
      MAP_EVERY EXISTS_TAC [..] THEN ASM_REWRITE_TAC[IN_UNIV; SUBSET_UNIV]`. -/
  IMAGE_INTERS_SATURATED : thm
  deriving Inhabited

@[nospecialize]
def setupSetsMisc [HolBase] (S : SetsCore) (P : SetsProps)
    (SIn : SetsInclusion) (O : SetsOperators) (IT : SetsInters)
    (ID : SetsInsertDelete) (Im : SetsImage) (Pr : HolMath.Pair.PairThms)
    (MESON_TAC : List thm → tactic) :
    ExceptT String IO SetsMisc := do
  let SET_TAC := SET_TAC S P MESON_TAC
  let SET_RULE := SET_RULE S P MESON_TAC
  let { EXTENSION, IN_ELIM_THM, .. } := S
  let { NOT_IN_EMPTY, IN_UNIV, IN_UNIONS, IN_INTERS, IN_DIFF, IN_IMAGE,
        FORALL_IN_INSERT, UNIONS_IMAGE, INTERS_IMAGE, UNIONS_GSPEC,
        INTERS_GSPEC, .. } := P
  let { SUBSET_UNIV, .. } := SIn
  let { INTER_UNIV, .. } := O
  let { INTERS_0, INTERS_1, INTERS_INSERT, .. } := IT
  let { SET_CASES, NOT_INSERT_EMPTY, .. } := ID
  let { IMAGE_CLAUSES, SIMPLE_IMAGE, .. } := Im
  let { PAIR_EQ, FORALL_PAIR_THM, .. } := Pr
  let { CONJ_ASSOC, IMP_CONJ, FORALL_UNWIND_THM2, SWAP_FORALL_THM,
        AND_FORALL_THM, LEFT_IMP_EXISTS_THM, .. } := HolBase.T
  let { NOT_IMP, NOT_EXISTS_THM, NOT_FORALL_THM, RIGHT_IMP_EXISTS_THM,
        SKOLEM_THM, .. } := HolBase.C

  let EMPTY_GSPEC ← prove
   r"{x:A | F} = {}"
   (SET_TAC [])

  let UNIV_GSPEC ← prove
   r"{x | T} = (:A)"
   (SET_TAC [])

  let SING_GSPEC ← prove
   r"(!a:A. {x | x = a} = {a}) /\
   (!a:A. {x | a = x} = {a})"
   (SET_TAC [])

  let SING_ALT ← prove
   r"!s:A->bool. (?x. s = {x}) <=> ?!x. x IN s"
   (SET_TAC [])

  let IN_GSPEC ← prove
   r"!s:A->bool. {x | x IN s} = s"
   (SET_TAC [])

  let IN_ELIM_PAIR_THM ← prove
   r"!(P:A->B->bool) a b. (a,b) IN {(x,y) | P x y} <=> P a b"
   (REWRITE_TAC [IN_ELIM_THM] THEN MESON_TAC [PAIR_EQ])

  let IN_ELIM_TRIPLE_THM ← prove
   r"(!(P:A->B->C->bool) a b c. (a,b,c) IN {(x,y,z) | P x y z} <=> P a b c) /\
   (!(P:A->B->C->bool) a b c. ((a,b),c) IN {((x,y),z) | P x y z} <=> P a b c)"
   (REWRITE_TAC [IN_ELIM_THM, PAIR_EQ] THEN MESON_TAC [])

  let IN_ELIM_QUAD_THM ← prove
   r"(!(P:A->B->C->D->bool) a b c d.
        (a,b,c,d) IN {w,x,y,z | P w x y z} <=> P a b c d) /\
   (!(P:A->B->C->D->bool) a b c d.
        ((a,b),(c,d)) IN {(w,x),(y,z) | P w x y z} <=> P a b c d) /\
   (!(P:A->B->C->D->bool) a b c d.
        (((a,b),c),d) IN {(((w,x),y),z) | P w x y z} <=> P a b c d)"
   (REWRITE_TAC [IN_ELIM_THM, PAIR_EQ] THEN MESON_TAC [])

  let SET_PAIR_THM ← prove
   r"!(P:A#B->bool). {p | P p} = {(a,b) | P(a,b)}"
   (REWRITE_TAC [EXTENSION, FORALL_PAIR_THM, IN_ELIM_THM, IN_ELIM_PAIR_THM])

  let SET_PROVE_CASES ← prove
   r"!P:(A->bool)->bool.
       P {} /\ (!a s. ~(a IN s) ==> P(a INSERT s))
       ==> !s. P s"
   (MESON_TAC [SET_CASES])

  let UNIONS_SINGS_GEN ← prove
   r"!P:A->bool. UNIONS {{x} | P x} = {x | P x}"
   (REWRITE_TAC [UNIONS_GSPEC] THEN SET_TAC [])

  let UNIONS_SINGS ← prove
   r"!s:A->bool. UNIONS {{x} | x IN s} = s"
   (REWRITE_TAC [UNIONS_GSPEC] THEN SET_TAC [])

  let IMAGE_INTERS ← prove
   r"!(f:A->B) s.
        ~(s = {}) /\
        (!x y. x IN UNIONS s /\ y IN UNIONS s /\ f x = f y ==> x = y)
        ==> IMAGE f (INTERS s) = INTERS(IMAGE (IMAGE f) s)"
   (REWRITE_TAC [INTERS_IMAGE] THEN SET_TAC [])

  let DIFF_INTERS ← prove
   r"!(u:A->bool) s. u DIFF INTERS s = UNIONS {u DIFF t | t IN s}"
   (REWRITE_TAC [UNIONS_GSPEC] THEN SET_TAC [])

  let INTERS_UNIONS ← prove
   r"!s. INTERS s = UNIV DIFF (UNIONS {(:A) DIFF t | t IN s})"
   (REWRITE_TAC [← GSYM DIFF_INTERS] THEN SET_TAC [])

  let UNIONS_INTERS ← prove
   r"!s. UNIONS s = UNIV DIFF (INTERS {(:A) DIFF t | t IN s})"
   (GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC [IN_UNIONS, IN_UNIV, IN_DIFF, INTERS_GSPEC, IN_ELIM_THM] THEN
    MESON_TAC [])

  let UNIONS_DIFF ← prove
   r"!s t:A->bool. UNIONS s DIFF t = UNIONS {x DIFF t | x IN s}"
   (REWRITE_TAC [UNIONS_GSPEC] THEN SET_TAC [])

  let DIFF_UNIONS ← prove
   r"!(u:A->bool) s. u DIFF UNIONS s = u INTER INTERS {u DIFF t | t IN s}"
   (REWRITE_TAC [INTERS_GSPEC] THEN SET_TAC [])

  let DIFF_UNIONS_NONEMPTY ← prove
   r"!(u:A->bool) s. ~(s = {}) ==> u DIFF UNIONS s = INTERS {u DIFF t | t IN s}"
   (REWRITE_TAC [INTERS_GSPEC] THEN SET_TAC [])

  let INTERS_OVER_UNIONS ← prove
   r"!f:A->(B->bool)->bool s.
        INTERS { UNIONS(f x) | x IN s} =
        UNIONS { INTERS {g x | x IN s} |g| !x. x IN s ==> g x IN f x}"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC [SIMPLE_IMAGE, INTERS_IMAGE, UNIONS_IMAGE, UNIONS_GSPEC] THEN
    REWRITE_TAC [IN_UNIONS, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"b:B") THEN REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN
    MESON_TAC [])

  let INTER_INTERS ← prove
   r"(!f s:A->bool.
        s INTER INTERS f =
        if f = {} then s else INTERS {s INTER t | t IN f}) /\
   (!f s:A->bool.
        INTERS f INTER s =
        if f = {} then s else INTERS {t INTER s | t IN f})"
   (REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [INTERS_0, INTER_UNIV, INTERS_GSPEC] THEN
    ASM SET_TAC [])

  let UNIONS_OVER_INTERS ← prove
   r"!f:A->(B->bool)->bool s.
        UNIONS { INTERS(f x) | x IN s} =
        INTERS { UNIONS {g x | x IN s} |g| !x. x IN s ==> g x IN f x}"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC [SIMPLE_IMAGE, INTERS_IMAGE, UNIONS_IMAGE, INTERS_GSPEC] THEN
    REWRITE_TAC [IN_INTERS, IN_ELIM_THM] THEN
    GEN_TAC THEN ONCE_REWRITE_TAC [← TAUT (← q r"(p <=> q) <=> (~p <=> ~q)")] THEN
    REWRITE_TAC [NOT_FORALL_THM, NOT_IMP, NOT_EXISTS_THM] THEN
    REWRITE_TAC [AND_FORALL_THM, ← GSYM SKOLEM_THM] THEN MESON_TAC [])

  let UNIONS_EQ_INTERS ← prove
   r"!f:(A->bool)->bool. UNIONS f = INTERS f <=> ?s. f = {s}"
   (REWRITE_TAC [← SET_RULE
     (← q r"(?s. f = {s}) <=> ~(f = {}) /\ !s t. s IN f /\ t IN f ==> s = t")] THEN
    SET_TAC [])

  let EXISTS_UNIQUE_UNIONS_INTERS ← prove
   r"!P. (?!s:A->bool. P s) <=> UNIONS {s | P s} = INTERS {s | P s}"
   (REWRITE_TAC [UNIONS_EQ_INTERS] THEN SET_TAC [])

  let IMAGE_INTERS_SUBSET ← prove
   r"!(f:A->B) g. IMAGE f (INTERS g) SUBSET INTERS (IMAGE (IMAGE f) g)"
   (REWRITE_TAC [INTERS_IMAGE] THEN SET_TAC [])

  let IMAGE_INTER_SUBSET ← prove
   r"!(f:A->B) s t. IMAGE f (s INTER t) SUBSET IMAGE f s INTER IMAGE f t"
   (SET_TAC [])

  let IMAGE_INTER_SATURATED_GEN ← prove
   r"!f:A->B s t u.
        {x | x IN u /\ f(x) IN IMAGE f s} SUBSET s /\ t SUBSET u \/
        {x | x IN u /\ f(x) IN IMAGE f t} SUBSET t /\ s SUBSET u
        ==> IMAGE f (s INTER t) = IMAGE f s INTER IMAGE f t"
   (SET_TAC [])

  -- The local lemma is proved first; then the tactic's three SET_RULEs run
  -- (and print) right to left, as in OCaml.
  let IMAGE_INTERS_SATURATED_GEN ← prove
   r"!f:A->B g s u.
        ~(g = {}) /\
        (!t. t IN g ==> t SUBSET u) /\
        (!t. t IN g DELETE s ==> {x | x IN u /\ f(x) IN IMAGE f t} SUBSET t)
        ==> IMAGE f (INTERS g) = INTERS (IMAGE (IMAGE f) g)"
   (← do
    let lemma ← prove
     r"~(g = {}) /\
       (!t. t IN g ==> t SUBSET u /\ {x | x IN u /\ f(x) IN IMAGE f t} SUBSET t)
       ==> IMAGE f (INTERS g) = INTERS (IMAGE (IMAGE f) g)"
     (ONCE_REWRITE_TAC [EXTENSION] THEN
      REWRITE_TAC [INTERS_IMAGE, IN_INTERS, IN_IMAGE] THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM, IN_ELIM_THM, NOT_IN_EMPTY] THEN
      ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
      REWRITE_TAC [IMP_CONJ, FORALL_UNWIND_THM2] THEN SET_TAC [])
    let r3 ← SET_RULE
     (← q r"IMAGE f (s INTER t) = IMAGE f s INTER IMAGE f t /\
      IMAGE f t = u ==> IMAGE f (s INTER t) = IMAGE f s INTER u")
    let r2 ← SET_RULE (← q r"x IN s ==> s = x INSERT (s DELETE x)")
    let r1 ← SET_RULE (← q r"~(s IN g) ==> g DELETE s = g")
    pure
     (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"(s:A->bool) IN g") THEN
      ASM_SIMP_TAC [r1] THENL
       [ALL_TAC, MESON_TAC [lemma]] THEN
      REWRITE_TAC [CONJ_ASSOC] THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      FIRST_X_ASSUM (SUBST1_TAC o MATCH_MP r2) THEN
      REWRITE_TAC [FORALL_IN_INSERT, NOT_INSERT_EMPTY] THEN
      STRIP_TAC THEN ASM_CASES_TAC (← q r"g DELETE (s:A->bool) = {}") THEN
      ASM_REWRITE_TAC [IMAGE_CLAUSES, INTERS_0, INTERS_1] THEN
      REWRITE_TAC [IMAGE_CLAUSES, INTERS_INSERT] THEN
      MATCH_MP_TAC r3 THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_INTER_SATURATED_GEN THEN
        EXISTS_TAC (← q r"u:A->bool") THEN ASM SET_TAC [],
        MATCH_MP_TAC lemma THEN ASM SET_TAC []]))

  let IMAGE_INTER_SATURATED ← prove
   r"!f:A->B s t.
        {x | f(x) IN IMAGE f s} SUBSET s \/ {x | f(x) IN IMAGE f t} SUBSET t
         ==> IMAGE f (s INTER t) = IMAGE f s INTER IMAGE f t"
   (SET_TAC [])

  let IMAGE_INTERS_SATURATED ← prove
   r"!f:A->B g s.
        ~(g = {}) /\ (!t. t IN g DELETE s ==> {x | f(x) IN IMAGE f t} SUBSET t)
        ==> IMAGE f (INTERS g) = INTERS (IMAGE (IMAGE f) g)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC IMAGE_INTERS_SATURATED_GEN THEN
    MAP_EVERY EXISTS_TAC [← q r"s:A->bool", ← q r"(:A)"] THEN
    ASM_REWRITE_TAC [IN_UNIV, SUBSET_UNIV])


  return {
    EMPTY_GSPEC, UNIV_GSPEC, SING_GSPEC, SING_ALT, IN_GSPEC, IN_ELIM_PAIR_THM,
    IN_ELIM_TRIPLE_THM, IN_ELIM_QUAD_THM, SET_PAIR_THM, SET_PROVE_CASES,
    UNIONS_SINGS_GEN, UNIONS_SINGS, IMAGE_INTERS, DIFF_INTERS, INTERS_UNIONS,
    UNIONS_INTERS, UNIONS_DIFF, DIFF_UNIONS, DIFF_UNIONS_NONEMPTY,
    INTERS_OVER_UNIONS, INTER_INTERS, UNIONS_OVER_INTERS, UNIONS_EQ_INTERS,
    EXISTS_UNIQUE_UNIONS_INTERS, IMAGE_INTERS_SUBSET, IMAGE_INTER_SUBSET,
    IMAGE_INTER_SATURATED_GEN, IMAGE_INTERS_SATURATED_GEN,
    IMAGE_INTER_SATURATED, IMAGE_INTERS_SATURATED }

/- ---------------------------------------------------------------------- -/
/- Stronger form of induction is sometimes handy.  (sets.ml 1258-1272)    -/
/- ---------------------------------------------------------------------- -/

/-- The stronger finite-set induction principle of sets.ml 1258-1272 - "a
    stronger form of induction is sometimes handy" (OCaml banner).  ONE
    theorem, `FINITE_INDUCT_STRONG`:

      `!P:(A->bool)->bool.
            P {} /\ (!x s. P s /\ ~(x IN s) /\ FINITE s ==> P(x INSERT s))
            ==> !s. FINITE s ==> P s`

    Its extra strength over `FINITE_INDUCT` is that the insertion step may
    ASSUME `~(x IN s)` and `FINITE s`, not just `P s`.  It is derived from
    `FINITE_INDUCT` by strengthening the goal to carry `FINITE s` alongside
    `P s`. -/
structure SetsInduct where
  /-- `FINITE_INDUCT_STRONG` (sets.ml 1259). -/
  FINITE_INDUCT_STRONG : thm
  deriving Inhabited

@[nospecialize]
def setupSetsInduct [HolBase] (S : SetsCore) (P : SetsProps)
    (MESON_TAC : List thm → tactic) :
    ExceptT String IO SetsInduct := do
  let SET_TAC := SET_TAC S P MESON_TAC
  let { FINITE_RULES, FINITE_INDUCT, .. } := S

  let FINITE_INDUCT_STRONG ← prove
   r"!P:(A->bool)->bool.
        P {} /\ (!x s. P s /\ ~(x IN s) /\ FINITE s ==> P(x INSERT s))
        ==> !s. FINITE s ==> P s"
   (GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"!s:A->bool. FINITE s ==> FINITE s /\ P s") MP_TAC THENL
     [ALL_TAC, MESON_TAC []] THEN
    MATCH_MP_TAC FINITE_INDUCT THEN ASM_SIMP_TAC [FINITE_RULES] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"x:A IN s") THENL
     [SUBGOAL_THEN (← q r"x:A INSERT s = s") (fun th => ASM_REWRITE_TAC [th]) THEN
      UNDISCH_TAC (← q r"x:A IN s") THEN SET_TAC [],
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []])

  return {
    FINITE_INDUCT_STRONG }

/- ---------------------------------------------------------------------- -/
/- Useful general properties of functions.  (sets.ml 1273-1382)           -/
/- ---------------------------------------------------------------------- -/

/-- The "useful general properties of functions" of sets.ml 1275-1382 - the
    INJ/SURJ/BIJ left/right-inverse theory and the function-factoring lemmas.
    SEVENTEEN theorems.  None uses `SET_TAC` except `IMAGE_INJECTIVE_IMAGE_OF_
    SUBSET` (which uses `SET_TAC[]` inside a `SUBGOAL_THEN`); the rest are
    `REWRITE_TAC`/`MESON_TAC` reductions, several building a local `MESON[]`
    lemma or specialising an earlier theorem with `ISPECL`/`REWRITE_RULE`. -/
structure SetsFunctions where
  /-- `INJECTIVE_ON_ALT` (sets.ml 1276): `MESON_TAC[]`. -/
  INJECTIVE_ON_ALT : thm
  /-- `INJECTIVE_ALT` (sets.ml 1282): `MESON_TAC[]`. -/
  INJECTIVE_ALT : thm
  /-- `SURJECTIVE_ON_RIGHT_INVERSE` (sets.ml 1286):
      `REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]`.  `s` is FREE. -/
  SURJECTIVE_ON_RIGHT_INVERSE : thm
  /-- `INJECTIVE_ON_LEFT_INVERSE` (sets.ml 1292): built with a local
      `MESON[]` lemma then `REWRITE_TAC[lemma; GSYM SKOLEM_THM] THEN
      MESON_TAC[]`. -/
  INJECTIVE_ON_LEFT_INVERSE : thm
  /-- `BIJECTIVE_ON_LEFT_RIGHT_INVERSE` (sets.ml 1300): a structured proof
      ending in `AP_TERM_TAC THEN ABS_TAC THEN EQ_TAC THEN ASM_MESON_TAC[]`. -/
  BIJECTIVE_ON_LEFT_RIGHT_INVERSE : thm
  /-- `SURJECTIVE_RIGHT_INVERSE` (sets.ml 1313):
      `MESON_TAC[SURJECTIVE_ON_RIGHT_INVERSE; IN_UNIV]`. -/
  SURJECTIVE_RIGHT_INVERSE : thm
  /-- `INJECTIVE_LEFT_INVERSE` (sets.ml 1317): a `REWRITE_RULE[IN_UNIV]`
      specialisation (via `ISPECL`) of `INJECTIVE_ON_LEFT_INVERSE`. -/
  INJECTIVE_LEFT_INVERSE : thm
  /-- `BIJECTIVE_LEFT_RIGHT_INVERSE` (sets.ml 1323):
      `GEN_TAC THEN MP_TAC(ISPECL [..] BIJECTIVE_ON_LEFT_RIGHT_INVERSE) THEN
      REWRITE_TAC[IN_UNIV]`. -/
  BIJECTIVE_LEFT_RIGHT_INVERSE : thm
  /-- `FUNCTION_FACTORS_LEFT_GEN` (sets.ml 1331): `ONCE_REWRITE_TAC[MESON[]..]
      THEN REWRITE_TAC[GSYM SKOLEM_THM] THEN MESON_TAC[]`. -/
  FUNCTION_FACTORS_LEFT_GEN : thm
  /-- `FUNCTION_FACTORS_LEFT` (sets.ml 1339): a `REWRITE_TAC` using `o_THM`,
      `FUN_EQ_THM` and a `REWRITE_RULE`d `ISPEC` of
      `FUNCTION_FACTORS_LEFT_GEN`. -/
  FUNCTION_FACTORS_LEFT : thm
  /-- `FUNCTION_FACTORS_RIGHT_GEN` (sets.ml 1344):
      `REWRITE_TAC[GSYM SKOLEM_THM] THEN MESON_TAC[]`. -/
  FUNCTION_FACTORS_RIGHT_GEN : thm
  /-- `FUNCTION_FACTORS_RIGHT` (sets.ml 1350):
      `REWRITE_TAC[FUN_EQ_THM; o_THM; GSYM SKOLEM_THM] THEN MESON_TAC[]`. -/
  FUNCTION_FACTORS_RIGHT : thm
  /-- `SURJECTIVE_FORALL_THM` (sets.ml 1354): `EQ_TAC THENL [MESON_TAC[];
      ALL_TAC] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
      MESON_TAC[]`. -/
  SURJECTIVE_FORALL_THM : thm
  /-- `SURJECTIVE_EXISTS_THM` (sets.ml 1359): `EQ_TAC THENL [MESON_TAC[];
      ALL_TAC] THEN DISCH_THEN(MP_TAC o SPEC ..) THEN MESON_TAC[]`. -/
  SURJECTIVE_EXISTS_THM : thm
  /-- `SURJECTIVE_IMAGE_THM` (sets.ml 1364): `REWRITE_TAC[EXTENSION; IN_IMAGE;
      IN_ELIM_THM] THEN EQ_TAC THENL [ALL_TAC; DISCH_THEN(MP_TAC o SPEC ..)]
      THEN MESON_TAC[]`. -/
  SURJECTIVE_IMAGE_THM : thm
  /-- `IMAGE_INJECTIVE_IMAGE_OF_SUBSET` (sets.ml 1370): a `SUBGOAL_THEN ...
      STRIP_ASSUME_TAC THENL [..; ..]` proof; the first branch is
      `REWRITE_TAC[GSYM SURJECTIVE_ON_RIGHT_INVERSE] THEN SET_TAC[]`. -/
  IMAGE_INJECTIVE_IMAGE_OF_SUBSET : thm
  deriving Inhabited

@[nospecialize]
def setupSetsFunctions [HolBase] (S : SetsCore) (P : SetsProps)
    (Tr : HolCore.Trivia.TriviaThms)
    (MESON_TAC : List thm → tactic) (ASM_MESON_TAC : List thm → tactic)
    (MESON' : List thm → term → IO (Except String thm)) :
    ExceptT String IO SetsFunctions := do
  let SET_TAC := SET_TAC S P MESON_TAC
  let MESON (ths : List thm) (t : term) : ExceptT String IO thm := MESON' ths t
  let { EXTENSION, IN_ELIM_THM, .. } := S
  let { IN_UNIV, IN_IMAGE, .. } := P
  let { RIGHT_AND_EXISTS_THM, .. } := HolBase.T
  let { FUN_EQ_THM, RIGHT_IMP_EXISTS_THM, SKOLEM_THM, .. } := HolBase.C
  let { o_THM, .. } := Tr

  let INJECTIVE_ON_ALT ← prove
   r"!P f:A->B.
        (!x y. P x /\ P y /\ f x = f y ==> x = y) <=>
        (!x y. P x /\ P y ==> (f x = f y <=> x = y))"
   (MESON_TAC [])

  let INJECTIVE_ALT ← prove
   r"!f:A->B. (!x y. f x = f y ==> x = y) <=> (!x y. f x = f y <=> x = y)"
   (MESON_TAC [])

  let SURJECTIVE_ON_RIGHT_INVERSE ← prove
   r"!(f:A->B) t.
        (!y. y IN t ==> ?x. x IN s /\ (f(x) = y)) <=>
        (?g. !y. y IN t ==> g(y) IN s /\ (f(g(y)) = y))"
   (REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM])

  let INJECTIVE_ON_LEFT_INVERSE ← prove
   r"!(f:A->B) s. (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)) <=>
         (?g. !x. x IN s ==> (g(f(x)) = x))"
   (← do
    let lemma ← MESON []
     (← q r"(!x. x IN s ==> (g(f(x)) = x)) <=>
      (!y x. x IN s /\ (y = (f:A->B) x) ==> (g y = x))")
    pure (REWRITE_TAC [lemma, ← GSYM SKOLEM_THM] THEN MESON_TAC []))

  let BIJECTIVE_ON_LEFT_RIGHT_INVERSE ← prove
   r"!(f:A->B) s t.
        (!x. x IN s ==> f(x) IN t)
        ==> ((!x y. x IN s /\ y IN s /\ f(x) = f(y) ==> x = y) /\
             (!y. y IN t ==> ?x. x IN s /\ f x = y) <=>
            ?g. (!y. y IN t ==> g(y) IN s) /\
                (!y. y IN t ==> (f(g(y)) = y)) /\
                (!x. x IN s ==> (g(f(x)) = x)))"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [INJECTIVE_ON_LEFT_INVERSE, SURJECTIVE_ON_RIGHT_INVERSE] THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM] THEN AP_TERM_TAC THEN ABS_TAC THEN
    EQ_TAC THEN ASM_MESON_TAC [])

  let SURJECTIVE_RIGHT_INVERSE ← prove
   r"!f:A->B. (!y. ?x. f(x) = y) <=> (?g. !y. f(g(y)) = y)"
   (MESON_TAC [SURJECTIVE_ON_RIGHT_INVERSE, IN_UNIV])

  let INJECTIVE_LEFT_INVERSE ← prove
   r"!f:A->B. (!x y. f x = f y ==> x = y) <=> (?g. !x. g(f(x)) = x)"
   (← do
    let th ← REWRITE_RULE [IN_UNIV]
     (← ISPECL [← q r"f:A->B", ← q r"UNIV:A->bool"] INJECTIVE_ON_LEFT_INVERSE)
    pure (REWRITE_TAC [th]))

  let BIJECTIVE_LEFT_RIGHT_INVERSE ← prove
   r"!f:A->B.
       (!x y. f(x) = f(y) ==> x = y) /\ (!y. ?x. f x = y) <=>
       ?g. (!y. f(g(y)) = y) /\ (!x. g(f(x)) = x)"
   (GEN_TAC THEN
    MP_TAC (← ISPECL [← q r"f:A->B", ← q r"(:A)", ← q r"(:B)"] BIJECTIVE_ON_LEFT_RIGHT_INVERSE) THEN
    REWRITE_TAC [IN_UNIV])

  let FUNCTION_FACTORS_LEFT_GEN ← prove
   r"!P (f:A->B) (g:A->C).
        (!x y. P x /\ P y /\ g x = g y ==> f x = f y) <=>
        (?h. !x. P x ==> f(x) = h(g x))"
   (ONCE_REWRITE_TAC [← MESON []
     (← q r"(!x. P x ==> f(x) = g(k x)) <=> (!y x. P x /\ y = k x ==> f x = g y)")] THEN
    REWRITE_TAC [← GSYM SKOLEM_THM] THEN MESON_TAC [])

  let FUNCTION_FACTORS_LEFT ← prove
   r"!(f:A->B) (g:A->C). (!x y. g x = g y ==> f x = f y) <=> ?h. f = h o g"
   (REWRITE_TAC [FUN_EQ_THM, o_THM,
     ← GSYM (← REWRITE_RULE [] (← ISPEC (← q r"\x. T") FUNCTION_FACTORS_LEFT_GEN))])

  let FUNCTION_FACTORS_RIGHT_GEN ← prove
   r"!P (f:A->C) (g:B->C).
        (!x. P x ==> ?y. g(y) = f(x)) <=>
        (?h. !x. P x ==> f(x) = g(h x))"
   (REWRITE_TAC [← GSYM SKOLEM_THM] THEN MESON_TAC [])

  let FUNCTION_FACTORS_RIGHT ← prove
   r"!(f:A->C) (g:B->C). (!x. ?y. g(y) = f(x)) <=> ?h. f = g o h"
   (REWRITE_TAC [FUN_EQ_THM, o_THM, ← GSYM SKOLEM_THM] THEN MESON_TAC [])

  let SURJECTIVE_FORALL_THM ← prove
   r"!f:A->B. (!y. ?x. f x = y) <=> (!P. (!x. P(f x)) <=> (!y. P y))"
   (GEN_TAC THEN EQ_TAC THENL [MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN (fun th => tactic_of do pure (ONCE_REWRITE_TAC [← GSYM th])) THEN
    MESON_TAC [])

  let SURJECTIVE_EXISTS_THM ← prove
   r"!f:A->B. (!y. ?x. f x = y) <=> (!P. (?x. P(f x)) <=> (?y. P y))"
   (GEN_TAC THEN EQ_TAC THENL [MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"\y:B. !x:A. ~(f x = y)")) THEN MESON_TAC [])

  let SURJECTIVE_IMAGE_THM ← prove
   r"!f:A->B. (!y. ?x. f x = y) <=> (!P. IMAGE f {x | P(f x)} = {x | P x})"
   (GEN_TAC THEN REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN
    EQ_TAC THENL [ALL_TAC, DISCH_THEN (MP_TAC o SPEC (← q r"\y:B. T"))] THEN
    MESON_TAC [])

  let IMAGE_INJECTIVE_IMAGE_OF_SUBSET ← prove
   r"!f:A->B s.
     ?t. t SUBSET s /\
         IMAGE f s = IMAGE f t /\
         (!x y. x IN t /\ y IN t /\ f x = f y ==> x = y)"
   (REPEAT GEN_TAC THEN
    SUBGOAL_THEN
     (← q r"?g. !y. y IN IMAGE (f:A->B) s ==> g(y) IN s /\ f(g(y)) = y")
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC [← GSYM SURJECTIVE_ON_RIGHT_INVERSE] THEN SET_TAC [],
      EXISTS_TAC (← q r"IMAGE (g:B->A) (IMAGE (f:A->B) s)") THEN ASM SET_TAC []])

  return {
    INJECTIVE_ON_ALT, INJECTIVE_ALT, SURJECTIVE_ON_RIGHT_INVERSE,
    INJECTIVE_ON_LEFT_INVERSE, BIJECTIVE_ON_LEFT_RIGHT_INVERSE,
    SURJECTIVE_RIGHT_INVERSE, INJECTIVE_LEFT_INVERSE,
    BIJECTIVE_LEFT_RIGHT_INVERSE, FUNCTION_FACTORS_LEFT_GEN,
    FUNCTION_FACTORS_LEFT, FUNCTION_FACTORS_RIGHT_GEN, FUNCTION_FACTORS_RIGHT,
    SURJECTIVE_FORALL_THM, SURJECTIVE_EXISTS_THM, SURJECTIVE_IMAGE_THM,
    IMAGE_INJECTIVE_IMAGE_OF_SUBSET }

/- ---------------------------------------------------------------------- -/
/- Basic combining theorems for finite sets.  (sets.ml 1383-1796)         -/
/- ---------------------------------------------------------------------- -/

/-- The "basic combining theorems for finite sets" of sets.ml 1383-1796 -
    FORTY-SEVEN theorems built on the `FINITE` inductive definition of
    sets.ml 132 (`S.FINITE_RULES`/`S.FINITE_INDUCT`/`S.FINITE_CASES`) and the
    stronger induction `SInd.FINITE_INDUCT_STRONG` of sets.ml 1258.  SIX
    theorems drive `FINITE_INDUCT` directly (FINITE_SUBSET, FINITE_UNION_IMP,
    FINITE_FINITE_UNIONS, FINITE_IMAGE_EXPAND, UNIONS_IN_CHAIN,
    INTERS_IN_CHAIN) and TWO drive `FINITE_INDUCT_STRONG`
    (FINITE_TRANSITIVITY_CHAIN, FINITE_SUBSET_UNIONS_DIRECTED_EQ); the rest are
    `MESON_TAC`/`REWRITE_TAC` reductions or structured `EQ_TAC`/`SUBGOAL_THEN`
    scripts resting on those eight inductions.  Unlike most earlier blocks
    almost NONE is a bare `SET_TAC[]` - `SET_TAC` cannot see `FINITE`, so the
    inductive skeleton is explicit. -/
structure SetsFinite where
  /-- `FINITE_EMPTY` (sets.ml 1386): `FINITE ({}:A->bool)`.
      `REWRITE_TAC[FINITE_RULES]`. -/
  FINITE_EMPTY : thm
  /-- `FINITE_SUBSET` (sets.ml 1390): a subset of a finite set is finite.  A
      structured `MATCH_MP_TAC FINITE_INDUCT` proof. -/
  FINITE_SUBSET : thm
  /-- `FINITE_RESTRICT` (sets.ml 1409):
      `MESON_TAC[SUBSET_RESTRICT; FINITE_SUBSET]`. -/
  FINITE_RESTRICT : thm
  /-- `FINITE_UNION_IMP` (sets.ml 1413): `MATCH_MP_TAC FINITE_INDUCT`. -/
  FINITE_UNION_IMP : thm
  /-- `FINITE_UNION` (sets.ml 1422): `EQ_TAC THENL [..; MATCH_ACCEPT_TAC
      FINITE_UNION_IMP]`. -/
  FINITE_UNION : thm
  /-- `FINITE_INTER` (sets.ml 1429):
      `MESON_TAC[INTER_SUBSET; FINITE_SUBSET]`. -/
  FINITE_INTER : thm
  /-- `FINITE_INSERT` (sets.ml 1433): `EQ_TAC THEN DISCH_TAC THENL [..; ..]`. -/
  FINITE_INSERT : thm
  /-- `FINITE_SING` (sets.ml 1441):
      `REWRITE_TAC[FINITE_INSERT; FINITE_RULES]`. -/
  FINITE_SING : thm
  /-- `FINITE_DELETE_IMP` (sets.ml 1445):
      `REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN ...`. -/
  FINITE_DELETE_IMP : thm
  /-- `FINITE_DELETE` (sets.ml 1450): `EQ_TAC THEN REWRITE_TAC[..] THEN
      ASM_CASES_TAC` with a `GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)`. -/
  FINITE_DELETE : thm
  /-- `FINITE_FINITE_UNIONS` (sets.ml 1460): `MATCH_MP_TAC FINITE_INDUCT`. -/
  FINITE_FINITE_UNIONS : thm
  /-- `FINITE_IMAGE_EXPAND` (sets.ml 1467): `MATCH_MP_TAC FINITE_INDUCT` with
      a `SUBGOAL_THEN` set-equation. -/
  FINITE_IMAGE_EXPAND : thm
  /-- `FINITE_IMAGE` (sets.ml 1479):
      `REWRITE_TAC[IMAGE; FINITE_IMAGE_EXPAND]`. -/
  FINITE_IMAGE : thm
  /-- `FINITE_IMAGE_INJ_GENERAL` (sets.ml 1483): `GEN_REWRITE_RULE I
      [INJECTIVE_ON_LEFT_INVERSE]` then `MATCH_MP_TAC FINITE_SUBSET`. -/
  FINITE_IMAGE_INJ_GENERAL : thm
  /-- `FINITE_FINITE_PREIMAGE_GENERAL` (sets.ml 1494): a `SUBGOAL_THEN`
      set-equation to a `UNIONS(IMAGE ...)`. -/
  FINITE_FINITE_PREIMAGE_GENERAL : thm
  /-- `FINITE_FINITE_PREIMAGE` (sets.ml 1508): `MP_TAC(ISPECL [..]
      FINITE_FINITE_PREIMAGE_GENERAL) THEN REWRITE_TAC[IN_UNIV]`. -/
  FINITE_FINITE_PREIMAGE : thm
  /-- `FINITE_IMAGE_INJ_EQ` (sets.ml 1517): `EQ_TAC THEN ASM_SIMP_TAC
      [FINITE_IMAGE]` then a `MATCH_MP FINITE_IMAGE_INJ_GENERAL`. -/
  FINITE_IMAGE_INJ_EQ : thm
  /-- `FINITE_IMAGE_INJ` (sets.ml 1526): `MP_TAC(SPECL [..]
      FINITE_IMAGE_INJ_GENERAL) THEN REWRITE_TAC[IN_UNIV]`. -/
  FINITE_IMAGE_INJ : thm
  /-- `FINITE_IMAGE_GEN` (sets.ml 1534): `GEN_REWRITE_RULE I
      [FUNCTION_FACTORS_LEFT_GEN]` then a `SUBGOAL_THEN`. -/
  FINITE_IMAGE_GEN : thm
  /-- `INFINITE_IMAGE` (sets.ml 1545): `INJECTIVE_ON_LEFT_INVERSE` then
      `REWRITE_TAC[INFINITE; CONTRAPOS_THM]`. -/
  INFINITE_IMAGE : thm
  /-- `INFINITE_IMAGE_INJ` (sets.ml 1555): `MESON_TAC[INFINITE_IMAGE]`. -/
  INFINITE_IMAGE_INJ : thm
  /-- `INFINITE_NONEMPTY` (sets.ml 1560):
      `MESON_TAC[INFINITE; FINITE_RULES]`. -/
  INFINITE_NONEMPTY : thm
  /-- `INFINITE_DIFF_FINITE` (sets.ml 1564): `MATCH_MP_TAC(TAUT ...) THEN
      REWRITE_TAC[INFINITE]` then `MATCH_MP_TAC FINITE_SUBSET`. -/
  INFINITE_DIFF_FINITE : thm
  /-- `SUBSET_IMAGE_INJ` (sets.ml 1573): `EQ_TAC THENL [..; MESON_TAC
      [IMAGE_SUBSET]]` with a `MATCH_MP (SET_RULE ...)`. -/
  SUBSET_IMAGE_INJ : thm
  /-- `SUBSET_IMAGE` (sets.ml 1586): `EQ_TAC THENL [..; MESON_TAC
      [IMAGE_SUBSET]] THEN REWRITE_TAC[SUBSET_IMAGE_INJ] THEN
      MATCH_MP_TAC MONO_EXISTS`. -/
  SUBSET_IMAGE : thm
  /-- `EXISTS_SUBSET_IMAGE` (sets.ml 1591):
      `REWRITE_TAC[SUBSET_IMAGE] THEN MESON_TAC[]`. -/
  EXISTS_SUBSET_IMAGE : thm
  /-- `FORALL_SUBSET_IMAGE` (sets.ml 1596):
      `REWRITE_TAC[SUBSET_IMAGE] THEN MESON_TAC[]`. -/
  FORALL_SUBSET_IMAGE : thm
  /-- `EXISTS_SUBSET_IMAGE_INJ` (sets.ml 1602):
      `REWRITE_TAC[SUBSET_IMAGE_INJ] THEN MESON_TAC[]`. -/
  EXISTS_SUBSET_IMAGE_INJ : thm
  /-- `FORALL_SUBSET_IMAGE_INJ` (sets.ml 1610): `ONCE_REWRITE_TAC[MESON[]
      ...] THEN REWRITE_TAC[NOT_IMP; EXISTS_SUBSET_IMAGE_INJ; GSYM
      CONJ_ASSOC]`. -/
  FORALL_SUBSET_IMAGE_INJ : thm
  /-- `EXISTS_FINITE_SUBSET_IMAGE_INJ` (sets.ml 1620):
      `ONCE_REWRITE_TAC[TAUT ...] THEN ... AP_TERM_TAC THEN ABS_TAC THEN
      MESON_TAC[FINITE_IMAGE_INJ_EQ]`. -/
  EXISTS_FINITE_SUBSET_IMAGE_INJ : thm
  /-- `FORALL_FINITE_SUBSET_IMAGE_INJ` (sets.ml 1630): `ONCE_REWRITE_TAC
      [MESON[] ...] THEN REWRITE_TAC[NOT_IMP; EXISTS_FINITE_SUBSET_IMAGE_INJ;
      GSYM CONJ_ASSOC]`. -/
  FORALL_FINITE_SUBSET_IMAGE_INJ : thm
  /-- `EXISTS_FINITE_SUBSET_IMAGE` (sets.ml 1640): `EQ_TAC THENL [..; ..]`. -/
  EXISTS_FINITE_SUBSET_IMAGE : thm
  /-- `FORALL_FINITE_SUBSET_IMAGE` (sets.ml 1648): `ONCE_REWRITE_TAC[MESON[]
      ...] THEN REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC;
      EXISTS_FINITE_SUBSET_IMAGE]`. -/
  FORALL_FINITE_SUBSET_IMAGE : thm
  /-- `FINITE_SUBSET_IMAGE` (sets.ml 1656): `EQ_TAC THENL [..; ASM_MESON_TAC
      ..] THEN SPEC_TAC(..) THEN REWRITE_TAC[FORALL_FINITE_SUBSET_IMAGE]`. -/
  FINITE_SUBSET_IMAGE : thm
  /-- `FINITE_SUBSET_IMAGE_IMP` (sets.ml 1665):
      `MESON_TAC[SUBSET_REFL; FINITE_SUBSET_IMAGE]`. -/
  FINITE_SUBSET_IMAGE_IMP : thm
  /-- `FINITE_IMAGE_EQ` (sets.ml 1671):
      `MESON_TAC[FINITE_SUBSET_IMAGE; FINITE_IMAGE; SUBSET_REFL]`. -/
  FINITE_IMAGE_EQ : thm
  /-- `FINITE_IMAGE_EQ_INJ` (sets.ml 1676): `EQ_TAC THENL [..; MESON_TAC
      [FINITE_IMAGE]]` then `MP_TAC(ISPECL [..] SUBSET_IMAGE_INJ)`,
      `MATCH_MP_TAC MONO_EXISTS`, `ASM_METIS_TAC[FINITE_IMAGE_INJ_EQ]`. -/
  FINITE_IMAGE_EQ_INJ : thm
  /-- `FINITE_DIFF` (sets.ml 1687):
      `MESON_TAC[FINITE_SUBSET; SUBSET_DIFF]`. -/
  FINITE_DIFF : thm
  /-- `INFINITE_SUPERSET` (sets.ml 1691):
      `REWRITE_TAC[INFINITE] THEN MESON_TAC[FINITE_SUBSET]`. -/
  INFINITE_SUPERSET : thm
  /-- `FINITE_TRANSITIVITY_CHAIN` (sets.ml 1695):
      `MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC[NOT_IN_EMPTY]
      THEN SET_TAC[]`. -/
  FINITE_TRANSITIVITY_CHAIN : thm
  /-- `UNIONS_MAXIMAL_SETS` (sets.ml 1706): a substantial structured proof -
      `SIMP_TAC[GSYM SUBSET_ANTISYM_EQ; ..]`, `MATCH_MP_TAC UNIONS_MONO`,
      `MP_TAC(ISPECL [..] FINITE_TRANSITIVITY_CHAIN)` and a `CONJ_TAC` split
      of width FOUR. -/
  UNIONS_MAXIMAL_SETS : thm
  /-- `FINITE_SUBSET_UNIONS` (sets.ml 1720): `GEN_REWRITE_RULE I [SUBSET]`,
      `GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [..]`, then `SKOLEM_THM`
      and `IMAGE (u:A->A->bool) s`. -/
  FINITE_SUBSET_UNIONS : thm
  /-- `UNIONS_IN_CHAIN` (sets.ml 1733): `MATCH_MP_TAC FINITE_INDUCT` with a
      `MATCH_MP_TAC(MESON[] ...)` set-lemma. -/
  UNIONS_IN_CHAIN : thm
  /-- `INTERS_IN_CHAIN` (sets.ml 1751): `MATCH_MP_TAC FINITE_INDUCT` with a
      `MATCH_MP_TAC(MESON[] ...)` set-lemma (the `INTERS` dual). -/
  INTERS_IN_CHAIN : thm
  /-- `FINITE_SUBSET_UNIONS_DIRECTED_EQ` (sets.ml 1769):
      `MATCH_MP_TAC FINITE_INDUCT_STRONG THEN SIMP_TAC[INSERT_SUBSET] THEN
      ASM SET_TAC[]`. -/
  FINITE_SUBSET_UNIONS_DIRECTED_EQ : thm
  /-- `FINITE_SUBSET_UNIONS_CHAIN_EQ` (sets.ml 1789, `time prove`):
      `MATCH_MP_TAC FINITE_SUBSET_UNIONS_DIRECTED_EQ THEN
      ASM_MESON_TAC[SUBSET_REFL]`. -/
  FINITE_SUBSET_UNIONS_CHAIN_EQ : thm
  /-- `FINITE_SUBSET_UNIONS_CHAIN` (sets.ml 1789):
      `MESON_TAC[FINITE_SUBSET_UNIONS_CHAIN_EQ]`. -/
  FINITE_SUBSET_UNIONS_CHAIN : thm
  deriving Inhabited

@[nospecialize]
def setupSetsFinite [HolBase] (S : SetsCore) (P : SetsProps)
    (SIn : SetsInclusion) (O : SetsOperators) (ID : SetsInsertDelete)
    (Un : SetsUnions) (IT : SetsInters) (Im : SetsImage) (Mi : SetsMisc)
    (Fn : SetsFunctions)
    (SInd : SetsInduct)
    (MESON_TAC : List thm → tactic) (ASM_MESON_TAC : List thm → tactic)
    (MESON' : List thm → term → IO (Except String thm))
    (ASM_METIS_TAC : List thm → tactic) :
    ExceptT String IO SetsFinite := do
  let SET_TAC := SET_TAC S P MESON_TAC
  let SET_RULE := SET_RULE S P MESON_TAC
  let MESON (ths : List thm) (t : term) : ExceptT String IO thm := MESON' ths t
  let { EXTENSION, IN_ELIM_THM, SUBSET, PSUBSET, FINITE_RULES, FINITE_INDUCT,
        INFINITE, IMAGE, .. } := S
  let { NOT_IN_EMPTY, IN_UNIV, IN_UNION, IN_UNIONS, IN_INSERT,
        FORALL_IN_INSERT, FORALL_IN_IMAGE, EXISTS_IN_IMAGE, FORALL_IN_GSPEC,
        EXISTS_IN_GSPEC, UNIONS_IMAGE, .. } := P
  let { SUBSET_REFL, SUBSET_ANTISYM_EQ, SUBSET_EMPTY, SUBSET_RESTRICT,
        PSUBSET_TRANS, SUBSET_PSUBSET_TRANS, .. } := SIn
  let { UNION_EMPTY, INTER_SUBSET, INTER_UNIV, SUBSET_DIFF, .. } := O
  let { NOT_INSERT_EMPTY, INSERT_SUBSET, .. } := ID
  let { UNIONS_0, UNIONS_INSERT, SUBSET_UNIONS, UNIONS_MONO, .. } := Un
  let { INTERS_0, INTERS_INSERT, .. } := IT
  let { IMAGE_SUBSET, .. } := Im
  let { EMPTY_GSPEC, .. } := Mi
  let { SURJECTIVE_ON_RIGHT_INVERSE, INJECTIVE_ON_LEFT_INVERSE,
        FUNCTION_FACTORS_LEFT_GEN, .. } := Fn
  let { FINITE_INDUCT_STRONG, .. } := SInd
  let { CONJ_ASSOC, IMP_CONJ, IMP_IMP, IMP_CONJ_ALT, EQ_IMP, SWAP_FORALL_THM,
        FORALL_AND_THM, RIGHT_FORALL_IMP_THM, LEFT_IMP_EXISTS_THM, MONO_EXISTS, .. } := HolBase.T
  let { NOT_IMP, CONTRAPOS_THM, RIGHT_IMP_EXISTS_THM, SKOLEM_THM, .. } := HolBase.C

  let FINITE_EMPTY ← prove
   r"FINITE ({}:A->bool)"
   (REWRITE_TAC [FINITE_RULES])

  let FINITE_SUBSET ← prove
   r"!(s:A->bool) t. FINITE t /\ s SUBSET t ==> FINITE s"
   (ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    REWRITE_TAC [IMP_CONJ] THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT THEN CONJ_TAC THENL
     [MESON_TAC [SUBSET_EMPTY, FINITE_RULES], ALL_TAC] THEN
    X_GEN_TAC (← q r"x:A") THEN X_GEN_TAC (← q r"u:A->bool") THEN DISCH_TAC THEN
    X_GEN_TAC (← q r"t:A->bool") THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"FINITE((x:A) INSERT (t DELETE x))") ASSUME_TAC THENL
     [MATCH_MP_TAC (← CONJUNCT2 FINITE_RULES) THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC (← q r"t SUBSET (x:A INSERT u)") THEN SET_TAC [],
      ASM_CASES_TAC (← q r"x:A IN t") THENL
       [SUBGOAL_THEN (← q r"x:A INSERT (t DELETE x) = t") SUBST_ALL_TAC THENL
         [UNDISCH_TAC (← q r"x:A IN t") THEN SET_TAC [], ASM_REWRITE_TAC []],
        FIRST_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC (← q r"t SUBSET x:A INSERT u") THEN
        UNDISCH_TAC (← q r"~(x:A IN t)") THEN SET_TAC []]])

  let FINITE_RESTRICT ← prove
   r"!s:A->bool P. FINITE s ==> FINITE {x | x IN s /\ P x}"
   (MESON_TAC [SUBSET_RESTRICT, FINITE_SUBSET])

  let FINITE_UNION_IMP ← prove
   r"!(s:A->bool) t. FINITE s /\ FINITE t ==> FINITE (s UNION t)"
   (REWRITE_TAC [IMP_CONJ] THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT THEN REWRITE_TAC [UNION_EMPTY] THEN
    SUBGOAL_THEN (← q r"!x s t. (x:A INSERT s) UNION t = x INSERT (s UNION t)")
    (fun th => REWRITE_TAC [th]) THENL
     [SET_TAC [],
      MESON_TAC [FINITE_RULES]])

  let FINITE_UNION ← prove
   r"!(s:A->bool) t. FINITE(s UNION t) <=> FINITE(s) /\ FINITE(t)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC (← q r"(s:A->bool) UNION t") THEN ASM_REWRITE_TAC [] THEN SET_TAC [],
      MATCH_ACCEPT_TAC FINITE_UNION_IMP])

  let FINITE_INTER ← prove
   r"!(s:A->bool) t. FINITE s \/ FINITE t ==> FINITE (s INTER t)"
   (MESON_TAC [INTER_SUBSET, FINITE_SUBSET])

  let FINITE_INSERT ← prove
   r"!(s:A->bool) x. FINITE (x INSERT s) <=> FINITE s"
   (REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC (← q r"x:A INSERT s") THEN ASM_REWRITE_TAC [] THEN SET_TAC [],
      MATCH_MP_TAC (← CONJUNCT2 FINITE_RULES) THEN
      ASM_REWRITE_TAC []])

  let FINITE_SING ← prove
   r"!a:A. FINITE {a}"
   (REWRITE_TAC [FINITE_INSERT, FINITE_RULES])

  let FINITE_DELETE_IMP ← prove
   r"!(s:A->bool) x. FINITE s ==> FINITE (s DELETE x)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    ASM_REWRITE_TAC [] THEN ASM SET_TAC [])

  let FINITE_DELETE ← prove
   r"!(s:A->bool) x. FINITE (s DELETE x) <=> FINITE s"
   (REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC [FINITE_DELETE_IMP] THEN
    ASM_CASES_TAC (← q r"x:A IN s") THENL
     [SUBGOAL_THEN (← q r"s = x INSERT (s DELETE x:A)")
      (fun th => GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THEN
      REWRITE_TAC [FINITE_INSERT] THEN POP_ASSUM MP_TAC THEN SET_TAC [],
      SUBGOAL_THEN (← q r"s DELETE x:A = s") (fun th => REWRITE_TAC [th]) THEN
      POP_ASSUM MP_TAC THEN SET_TAC []])

  let FINITE_FINITE_UNIONS ← prove
   r"!s:(A->bool)->bool.
        FINITE(s) ==> (FINITE(UNIONS s) <=> (!t. t IN s ==> FINITE(t)))"
   (MATCH_MP_TAC FINITE_INDUCT THEN
    REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY, UNIONS_0, UNIONS_INSERT] THEN
    REWRITE_TAC [FINITE_UNION, FINITE_RULES] THEN MESON_TAC [])

  let FINITE_IMAGE_EXPAND ← prove
   r"!(f:A->B) s. FINITE s ==> FINITE {y | ?x. x IN s /\ (y = f x)}"
   (GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT THEN
    REWRITE_TAC [NOT_IN_EMPTY, ← REWRITE_RULE [] EMPTY_GSPEC, FINITE_RULES] THEN
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN (← q r"{y | ?z. z IN (x INSERT s) /\ (y = (f:A->B) z)} =
                {y | ?z. z IN s /\ (y = f z)} UNION {(f x)}")
    (fun th => REWRITE_TAC [th]) THENL
     [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_INSERT, IN_UNION, NOT_IN_EMPTY] THEN
      MESON_TAC [],
      REWRITE_TAC [FINITE_UNION, FINITE_INSERT, FINITE_RULES]])

  let FINITE_IMAGE ← prove
   r"!(f:A->B) s. FINITE s ==> FINITE (IMAGE f s)"
   (REWRITE_TAC [IMAGE, FINITE_IMAGE_EXPAND])

  let FINITE_IMAGE_INJ_GENERAL ← prove
   r"!(f:A->B) A s.
        (!x y. x IN s /\ y IN s /\ f(x) = f(y) ==> x = y) /\
        FINITE A
        ==> FINITE {x | x IN s /\ f(x) IN A}"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [INJECTIVE_ON_LEFT_INVERSE]) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"g:B->A")) THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"IMAGE (g:B->A) A") THEN
    ASM_SIMP_TAC [FINITE_IMAGE] THEN ASM SET_TAC [])

  let FINITE_FINITE_PREIMAGE_GENERAL ← prove
   r"!f:A->B s t.
        FINITE t /\
        (!y. y IN t ==> FINITE {x | x IN s /\ f(x) = y})
        ==> FINITE {x | x IN s /\ f(x) IN t}"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"{x | x IN s /\ (f:A->B)(x) IN t} =
      UNIONS (IMAGE (\a. {x | x IN s /\ f x = a}) t)")
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM, IN_UNIONS] THEN
      REWRITE_TAC [EXISTS_IN_IMAGE] THEN SET_TAC [],
      ASM_SIMP_TAC [FINITE_FINITE_UNIONS, FINITE_IMAGE, FORALL_IN_IMAGE]])

  let FINITE_FINITE_PREIMAGE ← prove
   r"!f:A->B t.
        FINITE t /\
        (!y. y IN t ==> FINITE {x | f(x) = y})
        ==> FINITE {x | f(x) IN t}"
   (REPEAT GEN_TAC THEN MP_TAC
     (← ISPECL [← q r"f:A->B", ← q r"(:A)", ← q r"t:B->bool"] FINITE_FINITE_PREIMAGE_GENERAL) THEN
    REWRITE_TAC [IN_UNIV])

  let FINITE_IMAGE_INJ_EQ ← prove
   r"!(f:A->B) s.
        (!x y. x IN s /\ y IN s /\ f(x) = f(y) ==> x = y)
        ==> (FINITE(IMAGE f s) <=> FINITE s)"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC [FINITE_IMAGE] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [IMP_IMP] THEN
    DISCH_THEN (MP_TAC o MATCH_MP FINITE_IMAGE_INJ_GENERAL) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC [])

  let FINITE_IMAGE_INJ ← prove
   r"!(f:A->B) A.
        (!x y. f(x) = f(y) ==> x = y) /\ FINITE A
        ==> FINITE {x | f(x) IN A}"
   (REPEAT GEN_TAC THEN
    MP_TAC (← SPECL [← q r"f:A->B", ← q r"A:B->bool", ← q r"UNIV:A->bool"]
      FINITE_IMAGE_INJ_GENERAL) THEN REWRITE_TAC [IN_UNIV])

  let FINITE_IMAGE_GEN ← prove
   r"!(f:A->B) (g:A->C) s t.
        IMAGE f s SUBSET t /\ FINITE t /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> g x = g y)
        ==> FINITE(IMAGE g s)"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [FUNCTION_FACTORS_LEFT_GEN]) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"h:B->C")) THEN
    SUBGOAL_THEN (← q r"IMAGE g s = IMAGE (h:B->C) (IMAGE (f:A->B) s)") SUBST1_TAC THENL
     [ASM SET_TAC [], ASM_MESON_TAC [FINITE_IMAGE, FINITE_SUBSET]])

  let INFINITE_IMAGE ← prove
   r"!f:A->B s.
        INFINITE s /\ (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> INFINITE (IMAGE f s)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [IMP_CONJ_ALT, INJECTIVE_ON_LEFT_INVERSE] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"g:B->A")) THEN
    REWRITE_TAC [INFINITE, CONTRAPOS_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"s = IMAGE (g:B->A) (IMAGE f s)") SUBST1_TAC THENL
     [ASM SET_TAC [], MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC []])

  let INFINITE_IMAGE_INJ ← prove
   r"!f:A->B. (!x y. (f x = f y) ==> (x = y))
            ==> !s. INFINITE s ==> INFINITE(IMAGE f s)"
   (MESON_TAC [INFINITE_IMAGE])

  let INFINITE_NONEMPTY ← prove
   r"!s:A->bool. INFINITE(s) ==> ~(s = EMPTY)"
   (MESON_TAC [INFINITE, FINITE_RULES])

  let INFINITE_DIFF_FINITE ← prove
   r"!s:A->bool t. INFINITE(s) /\ FINITE(t) ==> INFINITE(s DIFF t)"
   (REPEAT GEN_TAC THEN
    MATCH_MP_TAC (← TAUT (← q r"(b /\ ~c ==> ~a) ==> a /\ b ==> c")) THEN
    REWRITE_TAC [INFINITE] THEN STRIP_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC (← q r"(t:A->bool) UNION (s DIFF t)") THEN
    ASM_REWRITE_TAC [FINITE_UNION] THEN SET_TAC [])

  let SUBSET_IMAGE_INJ ← prove
   r"!f:A->B s t.
        s SUBSET (IMAGE f t) <=>
        ?u. u SUBSET t /\
            (!x y. x IN u /\ y IN u ==> (f x = f y <=> x = y)) /\
            s = IMAGE f u"
   (REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC, MESON_TAC [IMAGE_SUBSET]] THEN
    DISCH_TAC THEN FIRST_ASSUM (MP_TAC o MATCH_MP (← SET_RULE
     (← q r"s SUBSET IMAGE f t ==> !x. x IN s ==> ?y. y IN t /\ f y = x"))) THEN
    REWRITE_TAC [SURJECTIVE_ON_RIGHT_INVERSE] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"g:B->A")) THEN
    EXISTS_TAC (← q r"IMAGE (g:B->A) s") THEN ASM SET_TAC [])

  let SUBSET_IMAGE ← prove
   r"!f:A->B s t. s SUBSET (IMAGE f t) <=> ?u. u SUBSET t /\ (s = IMAGE f u)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC, MESON_TAC [IMAGE_SUBSET]] THEN
    REWRITE_TAC [SUBSET_IMAGE_INJ] THEN MATCH_MP_TAC MONO_EXISTS THEN SET_TAC [])

  let EXISTS_SUBSET_IMAGE ← prove
   r"!P (f:A->B) s.
    (?t. t SUBSET IMAGE f s /\ P t) <=> (?t. t SUBSET s /\ P (IMAGE f t))"
   (REWRITE_TAC [SUBSET_IMAGE] THEN MESON_TAC [])

  let FORALL_SUBSET_IMAGE ← prove
   r"!P (f:A->B) s.
        (!t. t SUBSET IMAGE f s ==> P t) <=>
        (!t. t SUBSET s ==> P(IMAGE f t))"
   (REWRITE_TAC [SUBSET_IMAGE] THEN MESON_TAC [])

  let EXISTS_SUBSET_IMAGE_INJ ← prove
   r"!P (f:A->B) s.
    (?t. t SUBSET IMAGE f s /\ P t) <=>
    (?t. t SUBSET s /\
         (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y)) /\
         P (IMAGE f t))"
   (REWRITE_TAC [SUBSET_IMAGE_INJ] THEN MESON_TAC [])

  let FORALL_SUBSET_IMAGE_INJ ← prove
   r"!P (f:A->B) s.
        (!t. t SUBSET IMAGE f s ==> P t) <=>
        (!t. t SUBSET s /\
             (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y))
             ==> P(IMAGE f t))"
   (REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC [← MESON [] (← q r"(!t. p t) <=> ~(?t. ~p t)")] THEN
    REWRITE_TAC [NOT_IMP, EXISTS_SUBSET_IMAGE_INJ, ← GSYM CONJ_ASSOC])

  let EXISTS_FINITE_SUBSET_IMAGE_INJ ← prove
   r"!P (f:A->B) s.
    (?t. FINITE t /\ t SUBSET IMAGE f s /\ P t) <=>
    (?t. FINITE t /\ t SUBSET s /\
         (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y)) /\
         P (IMAGE f t))"
   (ONCE_REWRITE_TAC [← TAUT (← q r"p /\ q /\ r <=> q /\ p /\ r")] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [EXISTS_SUBSET_IMAGE_INJ] THEN
    AP_TERM_TAC THEN ABS_TAC THEN MESON_TAC [FINITE_IMAGE_INJ_EQ])

  let FORALL_FINITE_SUBSET_IMAGE_INJ ← prove
   r"!P (f:A->B) s.
        (!t. FINITE t /\ t SUBSET IMAGE f s ==> P t) <=>
        (!t. FINITE t /\ t SUBSET s /\
             (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y))
             ==> P(IMAGE f t))"
   (REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC [← MESON [] (← q r"(!t. p t) <=> ~(?t. ~p t)")] THEN
    REWRITE_TAC [NOT_IMP, EXISTS_FINITE_SUBSET_IMAGE_INJ, ← GSYM CONJ_ASSOC])

  let EXISTS_FINITE_SUBSET_IMAGE ← prove
   r"!P (f:A->B) s.
    (?t. FINITE t /\ t SUBSET IMAGE f s /\ P t) <=>
    (?t. FINITE t /\ t SUBSET s /\ P (IMAGE f t))"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [REWRITE_TAC [EXISTS_FINITE_SUBSET_IMAGE_INJ] THEN MESON_TAC [],
      MESON_TAC [FINITE_IMAGE, IMAGE_SUBSET]])

  let FORALL_FINITE_SUBSET_IMAGE ← prove
   r"!P (f:A->B) s.
        (!t. FINITE t /\ t SUBSET IMAGE f s ==> P t) <=>
        (!t. FINITE t /\ t SUBSET s ==> P(IMAGE f t))"
   (REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC [← MESON [] (← q r"(!x. P x) <=> ~(?x. ~P x)")] THEN
    REWRITE_TAC [NOT_IMP, ← GSYM CONJ_ASSOC, EXISTS_FINITE_SUBSET_IMAGE])

  let FINITE_SUBSET_IMAGE ← prove
   r"!f:A->B s t.
        FINITE(t) /\ t SUBSET (IMAGE f s) <=>
        ?s'. FINITE s' /\ s' SUBSET s /\ (t = IMAGE f s')"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [ALL_TAC, ASM_MESON_TAC [FINITE_IMAGE, IMAGE_SUBSET]] THEN
    SPEC_TAC (← q r"t:B->bool", ← q r"t:B->bool") THEN
    REWRITE_TAC [FORALL_FINITE_SUBSET_IMAGE] THEN MESON_TAC [])

  let FINITE_SUBSET_IMAGE_IMP ← prove
   r"!f:A->B s t.
        FINITE(t) /\ t SUBSET (IMAGE f s)
        ==> ?s'. FINITE s' /\ s' SUBSET s /\ t SUBSET (IMAGE f s')"
   (MESON_TAC [SUBSET_REFL, FINITE_SUBSET_IMAGE])

  let FINITE_IMAGE_EQ ← prove
   r"!(f:A->B) s. FINITE(IMAGE f s) <=>
                ?t. FINITE t /\ t SUBSET s /\ IMAGE f s = IMAGE f t"
   (MESON_TAC [FINITE_SUBSET_IMAGE, FINITE_IMAGE, SUBSET_REFL])

  let FINITE_IMAGE_EQ_INJ ← prove
   r"!(f:A->B) s. FINITE(IMAGE f s) <=>
                ?t. FINITE t /\ t SUBSET s /\ IMAGE f s = IMAGE f t /\
                    (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y))"
   (REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC, MESON_TAC [FINITE_IMAGE]] THEN
    DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"f:A->B", ← q r"IMAGE (f:A->B) s", ← q r"s:A->bool"]
          SUBSET_IMAGE_INJ) THEN
    REWRITE_TAC [SUBSET_REFL] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM_METIS_TAC [FINITE_IMAGE_INJ_EQ])

  let FINITE_DIFF ← prove
   r"!s t:A->bool. FINITE s ==> FINITE(s DIFF t)"
   (MESON_TAC [FINITE_SUBSET, SUBSET_DIFF])

  let INFINITE_SUPERSET ← prove
   r"!s t:A->bool. INFINITE s /\ s SUBSET t ==> INFINITE t"
   (REWRITE_TAC [INFINITE] THEN MESON_TAC [FINITE_SUBSET])

  let FINITE_TRANSITIVITY_CHAIN ← prove
   r"!R s:A->bool.
        FINITE s /\
        (!x. ~(R x x)) /\
        (!x y z. R x y /\ R y z ==> R x z) /\
        (!x. x IN s ==> ?y. y IN s /\ R x y)
        ==> s = {}"
   (GEN_TAC THEN ONCE_REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC [NOT_IN_EMPTY] THEN
    SET_TAC [])

  let UNIONS_MAXIMAL_SETS ← prove
   r"!f. FINITE f
       ==> UNIONS {t:A->bool | t IN f /\ !u. u IN f ==> ~(t PSUBSET u)} =
           UNIONS f"
   (SIMP_TAC [← GSYM SUBSET_ANTISYM_EQ, SUBSET_UNIONS, SUBSET_RESTRICT] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC UNIONS_MONO THEN
    X_GEN_TAC (← q r"s:A->bool") THEN DISCH_TAC THEN REWRITE_TAC [EXISTS_IN_GSPEC] THEN
    GEN_REWRITE_TAC I [← TAUT (← q r"p <=> ~ ~ p")] THEN DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"\t u:A->bool. s SUBSET t /\ t PSUBSET u",
      ← q r"{t:A->bool | t IN f /\ s SUBSET t}"] FINITE_TRANSITIVITY_CHAIN) THEN
    ASM_SIMP_TAC [NOT_IMP, FINITE_RESTRICT, FORALL_IN_GSPEC, EXISTS_IN_GSPEC] THEN
    REPEAT CONJ_TAC THENL [SET_TAC [], SET_TAC [], ALL_TAC, ASM SET_TAC []] THEN
    ASM_MESON_TAC [PSUBSET_TRANS, SUBSET_PSUBSET_TRANS, PSUBSET])

  let FINITE_SUBSET_UNIONS ← prove
   r"!f s:A->bool.
        FINITE s /\ s SUBSET UNIONS f
        ==> ?f'. FINITE f' /\ f' SUBSET f /\ s SUBSET UNIONS f'"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [IN_UNIONS, RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"u:A->A->bool") THEN DISCH_TAC THEN
    EXISTS_TAC (← q r"IMAGE (u:A->A->bool) s") THEN
    ASM_SIMP_TAC [FINITE_IMAGE, UNIONS_IMAGE] THEN ASM SET_TAC [])

  let UNIONS_IN_CHAIN ← prove
   r"!f:(A->bool)->bool.
        FINITE f /\ ~(f = {}) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> UNIONS f IN f"
   (← do
    let m1 ← MESON []
     (← q r"s UNION t = s \/ s UNION t = t
      ==> t IN f ==> s UNION t = s \/ s UNION t IN f")
    let t1 ← TAUT (← q r"p ==> q /\ r <=> (p ==> q) /\ (p ==> r)")
    pure
     (REWRITE_TAC [IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT THEN
      REWRITE_TAC [RIGHT_FORALL_IMP_THM, FORALL_IN_INSERT, UNIONS_INSERT] THEN
      REWRITE_TAC [FORALL_AND_THM, t1, NOT_INSERT_EMPTY] THEN
      MAP_EVERY X_GEN_TAC [← q r"s:A->bool", ← q r"f:(A->bool)->bool"] THEN
      ASM_CASES_TAC (← q r"f:(A->bool)->bool = {}") THEN
      ASM_REWRITE_TAC [UNIONS_0, IN_INSERT, UNION_EMPTY] THEN
      DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC m1 THEN
      ASM SET_TAC []))

  let INTERS_IN_CHAIN ← prove
   r"!f:(A->bool)->bool.
        FINITE f /\ ~(f = {}) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> INTERS f IN f"
   (← do
    let m1 ← MESON []
     (← q r"s INTER t = s \/ s INTER t = t
      ==> t IN f ==> s INTER t = s \/ s INTER t IN f")
    let t1 ← TAUT (← q r"p ==> q /\ r <=> (p ==> q) /\ (p ==> r)")
    pure
     (REWRITE_TAC [IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT THEN
      REWRITE_TAC [RIGHT_FORALL_IMP_THM, FORALL_IN_INSERT, INTERS_INSERT] THEN
      REWRITE_TAC [FORALL_AND_THM, t1, NOT_INSERT_EMPTY] THEN
      MAP_EVERY X_GEN_TAC [← q r"s:A->bool", ← q r"f:(A->bool)->bool"] THEN
      ASM_CASES_TAC (← q r"f:(A->bool)->bool = {}") THEN
      ASM_REWRITE_TAC [INTERS_0, IN_INSERT, INTER_UNIV] THEN
      DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC m1 THEN
      ASM SET_TAC []))

  let FINITE_SUBSET_UNIONS_DIRECTED_EQ ← prove
   r"!f s:A->bool.
        ~(f = {}) /\
        (!t u. t IN f /\ u IN f
               ==> ?v. v IN f /\ t SUBSET v /\ u SUBSET v) /\
        FINITE s
        ==> (s SUBSET UNIONS f <=> ?t. t IN f /\ s SUBSET t)"
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    GEN_TAC THEN REPEAT DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [INSERT_SUBSET] THEN ASM SET_TAC [])

  -- `time prove`.
  let FINITE_SUBSET_UNIONS_CHAIN_EQ ← ExceptT.mk <| time (fun (_ : Unit) => (prove
   r"!f s:A->bool.
        ~(f = {}) /\
        (!t u. t IN f /\ u IN f ==> t SUBSET u \/ u SUBSET t) /\
        FINITE s
        ==> (s SUBSET UNIONS f <=> ?t. t IN f /\ s SUBSET t)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET_UNIONS_DIRECTED_EQ THEN
    ASM_MESON_TAC [SUBSET_REFL])).run) ()

  let FINITE_SUBSET_UNIONS_CHAIN ← prove
   r"!f s:A->bool.
        FINITE s /\ s SUBSET UNIONS f /\ ~(f = {}) /\
        (!t u. t IN f /\ u IN f ==> t SUBSET u \/ u SUBSET t)
        ==> ?t. t IN f /\ s SUBSET t"
   (MESON_TAC [FINITE_SUBSET_UNIONS_CHAIN_EQ])


  return {
    FINITE_EMPTY, FINITE_SUBSET, FINITE_RESTRICT, FINITE_UNION_IMP,
    FINITE_UNION, FINITE_INTER, FINITE_INSERT, FINITE_SING, FINITE_DELETE_IMP,
    FINITE_DELETE, FINITE_FINITE_UNIONS, FINITE_IMAGE_EXPAND, FINITE_IMAGE,
    FINITE_IMAGE_INJ_GENERAL, FINITE_FINITE_PREIMAGE_GENERAL,
    FINITE_FINITE_PREIMAGE, FINITE_IMAGE_INJ_EQ, FINITE_IMAGE_INJ,
    FINITE_IMAGE_GEN, INFINITE_IMAGE, INFINITE_IMAGE_INJ, INFINITE_NONEMPTY,
    INFINITE_DIFF_FINITE, SUBSET_IMAGE_INJ, SUBSET_IMAGE, EXISTS_SUBSET_IMAGE,
    FORALL_SUBSET_IMAGE, EXISTS_SUBSET_IMAGE_INJ, FORALL_SUBSET_IMAGE_INJ,
    EXISTS_FINITE_SUBSET_IMAGE_INJ, FORALL_FINITE_SUBSET_IMAGE_INJ,
    EXISTS_FINITE_SUBSET_IMAGE, FORALL_FINITE_SUBSET_IMAGE,
    FINITE_SUBSET_IMAGE, FINITE_SUBSET_IMAGE_IMP, FINITE_IMAGE_EQ,
    FINITE_IMAGE_EQ_INJ, FINITE_DIFF, INFINITE_SUPERSET,
    FINITE_TRANSITIVITY_CHAIN, UNIONS_MAXIMAL_SETS, FINITE_SUBSET_UNIONS,
    UNIONS_IN_CHAIN, INTERS_IN_CHAIN, FINITE_SUBSET_UNIONS_DIRECTED_EQ,
    FINITE_SUBSET_UNIONS_CHAIN_EQ, FINITE_SUBSET_UNIONS_CHAIN }

/- ---------------------------------------------------------------------- -/
/- Recursion over finite sets; based on Ching-Tsun's code (archive 713).  -/
/-   (sets.ml 1797-1988)                                                  -/
/- ---------------------------------------------------------------------- -/

/-- The recursion-over-finite-sets block of sets.ml 1799-1988, credited in
    the OCaml verbatim to "Ching-Tsun's code (archive 713)".  The auxiliary
    relation `FINREC f b s a n` (a `new_recursive_definition` over `num`) says
    `a` is the result of folding `f` over the `n`-element set `s` from base
    `b`; the machinery below shows that when `f` COMMUTES
    (`f x (f y s) = f y (f x s)` for `x <> y`) the fold is UNIQUE and
    ORDER-INDEPENDENT, so it defines a genuine function.  `ITSET f s b` is that
    function (a `new_definition` selecting the unique `g`), and
    `FINITE_RECURSION` is its defining clauses - the set-theoretic analogue of
    `list_RECURSION`'s fold.

    Homes: `FINITE_INDUCT_STRONG` = `SInd`; `FINITE_SUBSET`/`FINITE_DELETE_IMP`
    = `SFin`; `FINITE_RULES` = `S`; `NOT_IN_EMPTY`/`IN_INSERT`/`IN_DELETE` =
    `P`/`SID`; `ABSORPTION` = `SID`; `SELECT_UNIQUE`/`SELECT_CONV` = `C`;
    `LEFT_IMP_EXISTS_THM` = `T`.  `FINREC` needs `num_RECURSION`
    (`Nm.num_RECURSION`) via the injected `new_recursive_definition`; `ITSET`
    is an injected `new_definition`.  `INDUCT_TAC` uses `Nm.num_INDUCTION`.
    The OCaml `MP_TAC o SPEC t`, `ANTE_RES_THEN`, `CONJUNCTS_THEN` and the
    `MATCH_MP lem th` inside a `FIRST_ASSUM` become explicit `thm_tactic`
    closures that bind the `Except`-returning `B.SPEC`/`B.CONJUNCT1`/
    `MATCH_MP` before handing on. -/
structure SetsRecursion where
  /-- `FINREC` (sets.ml 1800): the `num`-indexed fold relation, defined by
      `new_recursive_definition num_RECURSION` with a `0` and a `SUC n`
      clause. -/
  FINREC : thm
  /-- `FINREC_1_LEMMA` (sets.ml 1807): `FINREC f b s a (SUC 0) <=> ?x. s = {x}
      /\ a = f x b`.  `REWRITE_TAC[FINREC] THEN REPEAT GEN_TAC THEN AP_TERM_TAC
      THEN ABS_TAC THEN SET_TAC[]`. -/
  FINREC_1_LEMMA : thm
  /-- `FINREC_SUC_LEMMA` (sets.ml 1812): from a `(SUC n)`-fold, deleting any
      member gives an `n`-fold.  A local set-lemma `lem` then
      `INDUCT_TAC THENL [..; ..]` (width 2), with the step branch built from
      `GEN_REWRITE_TAC LAND_CONV [FINREC]`, `X_CHOOSE_THEN`, `ANTE_RES_THEN
      (MP_TAC o SPEC x)` and an inner `CONJ_TAC THENL [..; ..]`. -/
  FINREC_SUC_LEMMA : thm
  /-- `FINREC_UNIQUE_LEMMA` (sets.ml 1843): the fold result and length are
      unique.  `INDUCT_TAC THEN INDUCT_TAC THENL [..;..;..;..]` (width 4); the
      three base branches are `REWRITE_TAC[FINREC] THEN MESON_TAC[NOT_IN_EMPTY]`
      and the step branch uses `IMP_RES_THEN ASSUME_TAC FINREC_SUC_LEMMA` and a
      `DISCH_THEN(fun th -> MP_TAC(CONJUNCT1 th) THEN MP_TAC th)`. -/
  FINREC_UNIQUE_LEMMA : thm
  /-- `FINREC_EXISTS_LEMMA` (sets.ml 1859): every finite set has SOME fold.  A
      local `lem`, then `MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REPEAT STRIP_TAC
      THENL [..; ..]` (width 2); the step supplies `MATCH_MP lem th` inside a
      `FIRST_ASSUM`. -/
  FINREC_EXISTS_LEMMA : thm
  /-- `FINREC_FUN_LEMMA` (sets.ml 1869): a general existence+uniqueness to a
      function extractor.  `EXISTS_TAC` the choice term, then `EQ_TAC THENL
      [MATCH_MP_TAC SELECT_UNIQUE ..; .. CONV_TAC SELECT_CONV ..]` (width 2). -/
  FINREC_FUN_LEMMA : thm
  /-- `FINREC_FUN` (sets.ml 1880): under commutativity there is `g` with
      `g {} = b` and `g (INSERT)` deleting.  Chains `FINREC_UNIQUE_LEMMA`,
      `FINREC_EXISTS_LEMMA` and `FINREC_FUN_LEMMA`, then a `CONJ_TAC THENL`
      (width 2) with an inner `INDUCT_TAC THENL` (width 2) and a
      `SUBGOAL_THEN .. SUBST1_TAC THENL` (width 2) resting on
      `FINITE_SUBSET`. -/
  FINREC_FUN : thm
  /-- `SET_RECURSION_LEMMA` (sets.ml 1917): recasts `FINREC_FUN` in `INSERT`
      form with the `if x IN s` guard.  `COND_CASES_TAC THEN ASM_REWRITE_TAC[]
      THEN DISCH_TAC THENL [.. GSYM ABSORPTION ..; .. SUBGOAL_THEN ..]`
      (width 2). -/
  SET_RECURSION_LEMMA : thm
  /-- `ITSET` (sets.ml 1936): the iterated-set function, `new_definition`
      selecting (by `@g`) the unique `g` characterised by
      `SET_RECURSION_LEMMA`. -/
  ITSET : thm
  /-- `FINITE_RECURSION` (sets.ml 1943): `ITSET`'s defining clauses.
      `REWRITE_TAC[ITSET] THEN CONV_TAC SELECT_CONV THEN MATCH_MP_TAC
      SET_RECURSION_LEMMA THEN ASM_REWRITE_TAC[]`. -/
  FINITE_RECURSION : thm
  /-- `FINITE_RECURSION_DELETE` (sets.ml 1955): the delete-form recursion.
      `MATCH_MP FINITE_RECURSION`, then `ASM_CASES_TAC x IN s THENL [..; ..]`
      (width 2) using `FINITE_DELETE_IMP`. -/
  FINITE_RECURSION_DELETE : thm
  /-- `ITSET_EQ` (sets.ml 1974): `ITSET` respects pointwise-equal commuting
      functions.  `ONCE_REWRITE_TAC[T.IMP_CONJ] THEN REWRITE_TAC
      [RIGHT_FORALL_IMP_THM] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
      SIMP_TAC[FINITE_RECURSION; NOT_IN_EMPTY; IN_INSERT] THEN ..`. -/
  ITSET_EQ : thm
  deriving Inhabited

@[nospecialize]
def setupSetsRecursion [HolBase] (S : SetsCore) (P : SetsProps)
    (SID : SetsInsertDelete) (SFin : SetsFinite) (SInd : SetsInduct)
    (Nm : HolMath.Nums.NumsThms)
    (MESON_TAC : List thm → tactic) (ASM_MESON_TAC : List thm → tactic)
    (SELECT_CONV' : term → Except String thm)
    (new_recursive_definition' : thm → term → IO (Except String thm))
    (new_definition' : term → IO (Except String thm)) :
    ExceptT String IO SetsRecursion := do
  let SET_TAC := SET_TAC S P MESON_TAC
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let new_recursive_definition (ax : thm) (s : String) : ExceptT String IO thm := do
    new_recursive_definition' ax (← q s)
  let SELECT_CONV : ioconv := fun t => pure (SELECT_CONV' t)
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC Nm.num_INDUCTION
  let { FINITE_RULES, .. } := S
  let { NOT_IN_EMPTY, IN_INSERT, IN_DELETE, .. } := P
  let { ABSORPTION, .. } := SID
  let { FINITE_SUBSET, FINITE_DELETE_IMP, .. } := SFin
  let { FINITE_INDUCT_STRONG, .. } := SInd
  let { num_RECURSION, .. } := Nm
  let { IMP_CONJ, RIGHT_IMP_FORALL_THM, RIGHT_FORALL_IMP_THM,
        LEFT_IMP_EXISTS_THM, .. } := HolBase.T
  let { SELECT_UNIQUE, .. } := HolBase.C

  let FINREC ← new_recursive_definition num_RECURSION
   r"(FINREC (f:A->B->B) b s a 0 <=> (s = {}) /\ (a = b)) /\
   (FINREC (f:A->B->B) b s a (SUC n) <=>
                ?x c. x IN s /\
                      FINREC f b (s DELETE x) c n  /\
                      (a = f x c))"

  let FINREC_1_LEMMA ← prove
   r"!(f:A->B->B) b s a. FINREC f b s a (SUC 0) <=> ?x. s = {x} /\ a = f x b"
   (REWRITE_TAC [FINREC] THEN
    REPEAT GEN_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN SET_TAC [])

  let FINREC_SUC_LEMMA ← prove
   r"!(f:A->B->B) b.
         (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
         ==> !n s z.
                FINREC f b s z (SUC n)
                ==> !x. x IN s ==> ?w. FINREC f b (s DELETE x) w n /\
                                       (z = f x w)"
   (← do
    let lem ← prove r"s DELETE (x:A) DELETE y = s DELETE y DELETE x" (SET_TAC [])
    pure
     (REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
       [REWRITE_TAC [FINREC_1_LEMMA] THEN REWRITE_TAC [FINREC] THEN
        REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
        ASM_REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
        DISCH_THEN SUBST1_TAC THEN EXISTS_TAC (← q r"b:B") THEN
        ASM_REWRITE_TAC [] THEN SET_TAC [],
        REPEAT GEN_TAC THEN
        GEN_REWRITE_TAC LAND_CONV [FINREC] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"y:A") MP_TAC) THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"c:B") STRIP_ASSUME_TAC) THEN
        X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN
        ASM_CASES_TAC (← q r"x:A = y") THEN ASM_REWRITE_TAC [] THENL
         [EXISTS_TAC (← q r"c:B") THEN ASM_REWRITE_TAC [],
          UNDISCH_TAC (← q r"FINREC (f:A->B->B) b (s DELETE y) c (SUC n)") THEN
          DISCH_THEN (ANTE_RES_THEN (MP_TAC o SPEC (← q r"x:A"))) THEN
          ASM_REWRITE_TAC [IN_DELETE] THEN
          DISCH_THEN (X_CHOOSE_THEN (← q r"v:B") STRIP_ASSUME_TAC) THEN
          EXISTS_TAC (← q r"(f:A->B->B) y v") THEN ASM_REWRITE_TAC [FINREC] THEN
          CONJ_TAC THENL
           [MAP_EVERY EXISTS_TAC [← q r"y:A", ← q r"v:B"] THEN
            ONCE_REWRITE_TAC [lem] THEN ASM_REWRITE_TAC [IN_DELETE],
            FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []]]]))

  let FINREC_UNIQUE_LEMMA ← prove
   r"!(f:A->B->B) b.
         (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
         ==> !n1 n2 s a1 a2.
                FINREC f b s a1 n1 /\ FINREC f b s a2 n2
                ==> (a1 = a2) /\ (n1 = n2)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    INDUCT_TAC THEN INDUCT_TAC THENL
     [REWRITE_TAC [FINREC] THEN MESON_TAC [NOT_IN_EMPTY],
      REWRITE_TAC [FINREC] THEN MESON_TAC [NOT_IN_EMPTY],
      REWRITE_TAC [FINREC] THEN MESON_TAC [NOT_IN_EMPTY],
      IMP_RES_THEN ASSUME_TAC FINREC_SUC_LEMMA THEN REPEAT GEN_TAC THEN
      DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← CONJUNCT1 th) THEN MP_TAC th)) THEN
      DISCH_THEN (CONJUNCTS_THEN (ANTE_RES_THEN ASSUME_TAC)) THEN
      REWRITE_TAC [FINREC] THEN STRIP_TAC THEN ASM_MESON_TAC []])

  let FINREC_EXISTS_LEMMA ← prove
   r"!(f:A->B->B) b s. FINITE s ==> ?a n. FINREC f b s a n"
   (← do
    let lem ← prove r"~(x IN s ) ==> ((x:A INSERT s) DELETE x = s)" (SET_TAC [])
    pure
     (GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
      REPEAT STRIP_TAC THENL
       [MAP_EVERY EXISTS_TAC [← q r"b:B", ← q r"0"] THEN REWRITE_TAC [FINREC],
        MAP_EVERY EXISTS_TAC [← q r"(f:A->B->B) x a", ← q r"SUC n"] THEN
        REWRITE_TAC [FINREC] THEN MAP_EVERY EXISTS_TAC [← q r"x:A", ← q r"a:B"] THEN
        FIRST_ASSUM (fun th => tactic_of do pure (
          ASM_REWRITE_TAC [← MATCH_MP lem th, IN_INSERT]))]))

  let FINREC_FUN_LEMMA ← prove
   r"!P (R:A->B->C->bool).
       (!s. P s ==> ?a n. R s a n) /\
       (!n1 n2 s a1 a2. R s a1 n1 /\ R s a2 n2 ==> (a1 = a2) /\ (n1 = n2))
       ==> ?f. !s a. P s ==> ((?n. R s a n) <=> (f s = a))"
   (REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"\s:A. @a:B. ?n:C. R s a n") THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN EQ_TAC THENL
     [STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC [],
      DISCH_THEN (SUBST1_TAC o SYM) THEN CONV_TAC SELECT_CONV THEN
      ASM_MESON_TAC []])

  let FINREC_FUN ← prove
   r"!(f:A->B->B) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> ?g. (g {} = b) /\
                !s x. FINITE s /\ x IN s
                      ==> (g s = f x (g (s DELETE x)))"
   (REPEAT STRIP_TAC THEN IMP_RES_THEN MP_TAC FINREC_UNIQUE_LEMMA THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"b:B")) THEN DISCH_THEN
     (MP_TAC o CONJ (← SPECL [← q r"f:A->B->B", ← q r"b:B"] FINREC_EXISTS_LEMMA)) THEN
    DISCH_THEN (MP_TAC o MATCH_MP FINREC_FUN_LEMMA) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"g:(A->bool)->B")) THEN
    EXISTS_TAC (← q r"g:(A->bool)->B") THEN CONJ_TAC THENL
     [SUBGOAL_THEN (← q r"FINITE(EMPTY:A->bool)")
      (ANTE_RES_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC I [← GSYM th]))) THENL
       [REWRITE_TAC [FINITE_RULES],
        EXISTS_TAC (← q r"0") THEN REWRITE_TAC [FINREC]],
      REPEAT STRIP_TAC THEN
      ANTE_RES_THEN MP_TAC (← ASSUME (← q r"FINITE(s:A->bool)")) THEN
      DISCH_THEN (ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC [] THEN
      FIRST_ASSUM (MP_TAC o SPEC (← q r"(g:(A->bool)->B) s")) THEN
      REWRITE_TAC [] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      INDUCT_TAC THENL
       [ASM_REWRITE_TAC [FINREC] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"x:A IN s") THEN
        ASM_REWRITE_TAC [NOT_IN_EMPTY],
        IMP_RES_THEN ASSUME_TAC FINREC_SUC_LEMMA THEN
        DISCH_THEN (ANTE_RES_THEN (MP_TAC o SPEC (← q r"x:A"))) THEN
        ASM_REWRITE_TAC [] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"w:B") (CONJUNCTS_THEN ASSUME_TAC)) THEN
        SUBGOAL_THEN (← q r"(g (s DELETE x:A) = w:B)") SUBST1_TAC THENL
         [SUBGOAL_THEN (← q r"FINITE(s DELETE x:A)") MP_TAC THENL
           [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"s:A->bool") THEN
            ASM_REWRITE_TAC [] THEN SET_TAC [],
            DISCH_THEN (ANTE_RES_THEN (MP_TAC o GSYM)) THEN
            DISCH_THEN (fun th => REWRITE_TAC [th]) THEN
            EXISTS_TAC (← q r"n:num") THEN ASM_REWRITE_TAC []],
          ASM_REWRITE_TAC []]]])

  let SET_RECURSION_LEMMA ← prove
   r"!(f:A->B->B) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> ?g. (g {} = b) /\
                !x s. FINITE s
                      ==> (g (x INSERT s) =
                                if x IN s then g s else f x (g s))"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"b:B") o MATCH_MP FINREC_FUN) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"g:(A->bool)->B") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"g:(A->bool)->B") THEN ASM_REWRITE_TAC [] THEN
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    DISCH_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC [← GSYM ABSORPTION] THEN ASM_REWRITE_TAC [],
      SUBGOAL_THEN (← q r"FINITE(x:A INSERT s) /\ x IN (x INSERT s)") MP_TAC THENL
       [REWRITE_TAC [IN_INSERT] THEN ASM_MESON_TAC [FINITE_RULES],
        DISCH_THEN (ANTE_RES_THEN SUBST1_TAC) THEN
        REPEAT AP_TERM_TAC THEN UNDISCH_TAC (← q r"~(x:A IN s)") THEN SET_TAC []]])

  let ITSET ← new_definition
   r"ITSET (f:A->B->B) s b =
        (@g. (g {} = b) /\
             !x s. FINITE s
                   ==> (g (x INSERT s) = if x IN s then g s else f x (g s)))
        s"

  let FINITE_RECURSION ← prove
   r"!(f:A->B->B) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> (ITSET f {} b = b) /\
            !x s. FINITE s
                  ==> (ITSET f (x INSERT s) b =
                       if x IN s then ITSET f s b
                                 else f x (ITSET f s b))"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [ITSET] THEN
    CONV_TAC SELECT_CONV THEN MATCH_MP_TAC SET_RECURSION_LEMMA THEN
    ASM_REWRITE_TAC [])

  let FINITE_RECURSION_DELETE ← prove
   r"!(f:A->B->B) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> (ITSET f {} b = b) /\
            !x s. FINITE s
                  ==> (ITSET f s b =
                       if x IN s then f x (ITSET f (s DELETE x) b)
                                 else ITSET f (s DELETE x) b)"
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP FINITE_RECURSION) THEN
    DISCH_THEN (STRIP_ASSUME_TAC o SPEC (← q r"b:B")) THEN ASM_REWRITE_TAC [] THEN
    REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"x:A IN s") THEN ASM_REWRITE_TAC [] THENL
     [DISCH_THEN (MP_TAC o MATCH_MP FINITE_DELETE_IMP) THEN
      DISCH_THEN (ANTE_RES_THEN MP_TAC o SPEC (← q r"x:A")) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"x:A")) THEN
      REWRITE_TAC [IN_DELETE] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC (← q r"x:A IN s") THEN SET_TAC [],
      DISCH_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC (← q r"~(x:A IN s)") THEN SET_TAC []])

  let ITSET_EQ ← prove
   r"!s (f:A->B->B) g b.
        FINITE(s) /\ (!x. x IN s ==> (f x = g x)) /\
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s))) /\
        (!x y s. ~(x = y) ==> (g x (g y s) = g y (g x s)))
        ==> (ITSET f s b = ITSET g s b)"
   (ONCE_REWRITE_TAC [IMP_CONJ] THEN
    REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [FINITE_RECURSION, NOT_IN_EMPTY, IN_INSERT] THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
    FIRST_ASSUM (MATCH_MP_TAC o REWRITE_RULE [RIGHT_IMP_FORALL_THM]) THEN
    ASM_MESON_TAC [])


  return {
    FINREC, FINREC_1_LEMMA, FINREC_SUC_LEMMA, FINREC_UNIQUE_LEMMA,
    FINREC_EXISTS_LEMMA, FINREC_FUN_LEMMA, FINREC_FUN, SET_RECURSION_LEMMA,
    ITSET, FINITE_RECURSION, FINITE_RECURSION_DELETE, ITSET_EQ }

/- ---------------------------------------------------------------------- -/
/- Cardinality, HAS_SIZE, and the HAS_SIZE numeral expansion.             -/
/- (sets.ml 1989-2243)                                                    -/
/- ---------------------------------------------------------------------- -/

/-- `let rec EXISTS_HAS_SIZE_AND_CONV tm = ...` inside HAS_SIZE_CONV
    (sets.ml 2221). -/
partial def existsHasSizeAndConv [HolBase] (num_CONV qconv_0 qconv_1 : ioconv) :
    ioconv := fun tm =>
  (qconv_0 ORELSEC
   (BINDER_CONV (LAND_CONV (RAND_CONV num_CONV)) THENC
    qconv_1 THENC
    BINDER_CONV (existsHasSizeAndConv num_CONV qconv_0 qconv_1))) tm

/-- `let rec NOT_IN_INSERT_CONV tm = ...` inside HAS_SIZE_CONV
    (sets.ml 2226). -/
partial def notInInsertConv [HolBase] (rconv_0 rconv_1 : ioconv) : ioconv :=
  fun tm =>
  ((rconv_0 THENC notInInsertConv rconv_0 rconv_1) ORELSEC
   (rconv_1 THENC RAND_CONV (notInInsertConv rconv_0 rconv_1)) ORELSEC
   ALL_CONV) tm

/-- The `CARD`/`HAS_SIZE` bundle (sets.ml 1991-2243): finite cardinality,
    its basic clauses, the delete-choice induction principle, the relational
    `HAS_SIZE` predicate with its rewrite form, and the `HAS_SIZE_CONV`
    numeral expansion (returned as an `ioconv`, not a theorem). -/
structure SetsCard where
  /-- `CARD` (sets.ml 1992): `CARD s = ITSET (\x n. SUC n) s 0`, an injected
      `new_definition`. -/
  CARD : thm
  /-- `CARD_CLAUSES` (sets.ml 1995): `CARD {} = 0` and the `INSERT` step.
      `MP_TAC(ISPECL [..] FINITE_RECURSION) THEN REWRITE_TAC[CARD]`. -/
  CARD_CLAUSES : thm
  /-- `CARD_UNION` (sets.ml 2003): cardinality is additive on disjoint finite
      sets.  A `TAUT`/`RIGHT_FORALL_IMP_THM` reshuffle, `FINITE_INDUCT_STRONG`,
      then THREE `THENL`s of width 2 (`SUBGOAL_THEN .. SUBST1_TAC`,
      `SUBGOAL_THEN .. STRIP_ASSUME_TAC`, `SUBGOAL_THEN ~(x IN ..)
      ASSUME_TAC`). -/
  CARD_UNION : thm
  /-- `CARD_DELETE` (sets.ml 2029).  `COND_CASES_TAC THENL [..; ..]` (width 2);
      branch 1 uses `GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th]`. -/
  CARD_DELETE : thm
  /-- `CARD_UNION_EQ` (sets.ml 2039): `MESON_TAC[CARD_UNION; FINITE_SUBSET;
      SUBSET_UNION]`. -/
  CARD_UNION_EQ : thm
  /-- `CARD_DIFF` (sets.ml 2045): `MATCH_MP_TAC(ARITH_RULE ..) THEN
      MATCH_MP_TAC CARD_UNION_EQ THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[]`. -/
  CARD_DIFF : thm
  /-- `CARD_EQ_0` (sets.ml 2051): `FINITE_INDUCT_STRONG` then
      `SIMP_TAC[CARD_CLAUSES; NOT_INSERT_EMPTY; NOT_SUC]`. -/
  CARD_EQ_0 : thm
  /-- `CARD_SING` (sets.ml 2056): `CARD {a} = 1`. -/
  CARD_SING : thm
  /-- `CARD_LE_2` (sets.ml 2060): `CARD{a,b} <= 2`. -/
  CARD_LE_2 : thm
  /-- `CARD_LE_3` (sets.ml 2066): `CARD{a,b,c} <= 3`. -/
  CARD_LE_3 : thm
  /-- `CARD_LE_4` (sets.ml 2072): `CARD{a,b,c,d} <= 4`. -/
  CARD_LE_4 : thm
  /-- `FINITE_INDUCT_DELETE` (sets.ml 2082): induction choosing the deleted
      element.  `WF_INDUCT_TAC \`CARD(s:A->bool)\``, no top-level `THENL`. -/
  FINITE_INDUCT_DELETE : thm
  /-- `HAS_SIZE` (sets.ml 2100): `s HAS_SIZE n <=> FINITE s /\ CARD s = n`, an
      injected `new_definition`. -/
  HAS_SIZE : thm
  /-- `HAS_SIZE_CARD` (sets.ml 2103): `SIMP_TAC[HAS_SIZE]`. -/
  HAS_SIZE_CARD : thm
  /-- `HAS_SIZE_0` (sets.ml 2107): `s HAS_SIZE 0 <=> s = {}`. -/
  HAS_SIZE_0 : thm
  /-- `HAS_SIZE_SUC` (sets.ml 2121): the delete characterisation of `SUC n`. -/
  HAS_SIZE_SUC : thm
  /-- `HAS_SIZE_UNION` (sets.ml 2144): `SIMP_TAC[HAS_SIZE; FINITE_UNION;
      DISJOINT; CARD_UNION]`. -/
  HAS_SIZE_UNION : thm
  /-- `HAS_SIZE_DIFF` (sets.ml 2150): `SIMP_TAC[HAS_SIZE; FINITE_DIFF;
      CARD_DIFF]`. -/
  HAS_SIZE_DIFF : thm
  /-- `HAS_SIZE_UNIONS` (sets.ml 2156): a disjoint union of `n`-sized sets has
      size `m*n`.  `GEN_REWRITE_TAC (funpow 4 BINDER_CONV o funpow 2 LAND_CONV)
      [HAS_SIZE]`, `FINITE_INDUCT_STRONG`, `CONJ_TAC THENL [..; ALL_TAC]`. -/
  HAS_SIZE_UNIONS : thm
  /-- `FINITE_HAS_SIZE` (sets.ml 2184): `REWRITE_TAC[HAS_SIZE]`. -/
  FINITE_HAS_SIZE : thm
  /-- `HAS_SIZE_CLAUSES` (sets.ml 2192): the rewrite form.  A local
      `lemma = SET_RULE ..`, then `EQ_TAC THENL [..; ..]` (width 2). -/
  HAS_SIZE_CLAUSES : thm
  /-- `HAS_SIZE_CONV` (sets.ml 2206): a CONVERSION producing the explicit
      expansion of `s HAS_SIZE n` for a NUMERAL n.  Machinery, not a theorem;
      returned as an `ioconv`. -/
  HAS_SIZE_CONV : ioconv
  deriving Inhabited

@[nospecialize]
def setupSetsCard [HolBase] (S : SetsCore)
    (P : SetsProps) (SIn : SetsInclusion) (SOp : SetsOperators)
    (SID : SetsInsertDelete) (SUn : SetsUnions)
    (SFin : SetsFinite) (SInd : SetsInduct) (SRec : SetsRecursion)
    (MESON_TAC : List thm → tactic) (ASM_MESON_TAC : List thm → tactic)
    (new_definition' : term → IO (Except String thm))
    (ADD_CLAUSES MULT_CLAUSES SUC_INJ NOT_SUC SUC_SUB1 ARITH : thm)
    (ARITH_RULE' : term → IO (Except String thm))
    (ARITH_TAC : tactic)
    (WF_INDUCT_TAC : term → tactic)
    (num_CONV : ioconv) :
    ExceptT String IO SetsCard := do
  let SET_TAC := SET_TAC S P MESON_TAC
  let SET_RULE := SET_RULE S P MESON_TAC
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let ARITH_RULE (t : term) : ExceptT String IO thm := ARITH_RULE' t
  let { EXTENSION, IN_ELIM_THM, DISJOINT, FINITE_RULES, .. } := S
  let { NOT_IN_EMPTY, IN_UNION, IN_INTER, IN_INSERT, IN_DELETE, .. } := P
  let { MEMBER_NOT_EMPTY, .. } := SIn
  let { SUBSET_UNION, UNION_EMPTY, INTER_EMPTY, .. } := SOp
  let { NOT_INSERT_EMPTY, .. } := SID
  let { EMPTY_UNIONS, .. } := SUn
  let { FINITE_EMPTY, FINITE_SUBSET, FINITE_UNION_IMP, FINITE_UNION,
        FINITE_INSERT, FINITE_DELETE, FINITE_DIFF, .. } := SFin
  let { FINITE_INDUCT_STRONG, .. } := SInd
  let { FINITE_RECURSION, .. } := SRec
  let { CONJ_ASSOC, IMP_CONJ, RIGHT_FORALL_IMP_THM, LEFT_IMP_EXISTS_THM, .. } := HolBase.T
  let { NOT_FORALL_THM, .. } := HolBase.C

  /- Cardinality. -/

  let CARD ← new_definition
   r"CARD (s:A->bool) = ITSET (\x n. SUC n) s 0"

  let CARD_CLAUSES ← prove
   r"(CARD ({}:A->bool) = 0) /\
   (!(x:A) s. FINITE s ==>
                 (CARD (x INSERT s) =
                      if x IN s then CARD s else SUC(CARD s)))"
   (MP_TAC (← ISPECL [← q r"\(x:A) n. SUC n", ← q r"0"] FINITE_RECURSION) THEN
    REWRITE_TAC [CARD])

  let CARD_UNION ← prove
   r"!(s:A->bool) t. FINITE(s) /\ FINITE(t) /\ (s INTER t = EMPTY)
         ==> (CARD (s UNION t) = CARD s + CARD t)"
   (REWRITE_TAC [← TAUT (← q r"a /\ b /\ c ==> d <=> a ==> b /\ c ==> d")] THEN
    REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [UNION_EMPTY, CARD_CLAUSES, INTER_EMPTY, ADD_CLAUSES] THEN
    X_GEN_TAC (← q r"x:A") THEN X_GEN_TAC (← q r"s:A->bool") THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"(x:A INSERT s) UNION t = x INSERT (s UNION t)")
    SUBST1_TAC THENL [SET_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"FINITE ((s:A->bool) UNION t) /\ FINITE s")
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC FINITE_UNION_IMP THEN
      ASM_REWRITE_TAC [], ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"x:A", ← q r"s:A->bool"] (← CONJUNCT2 CARD_CLAUSES)) THEN
    MP_TAC (← ISPECL [← q r"x:A", ← q r"s:A->bool UNION t"] (← CONJUNCT2 CARD_CLAUSES)) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"~(x:A IN (s UNION t))") ASSUME_TAC THENL
     [ASM_REWRITE_TAC [IN_UNION] THEN
      UNDISCH_TAC (← q r"(x:A INSERT s) INTER t = EMPTY") THEN
      REWRITE_TAC [EXTENSION, IN_INSERT, IN_INTER, NOT_IN_EMPTY] THEN
      MESON_TAC [],
      ASM_REWRITE_TAC [SUC_INJ, ADD_CLAUSES] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC (← q r"x:A INSERT s INTER t = EMPTY") THEN SET_TAC []])

  let CARD_DELETE ← prove
   r"!x:A s. FINITE(s)
           ==> (CARD(s DELETE x) = if x IN s then CARD(s) - 1 else CARD(s))"
   (REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
     [SUBGOAL_THEN (← q r"s = x:A INSERT (s DELETE x)")
       (fun th => GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th])
      THENL [UNDISCH_TAC (← q r"x:A IN s") THEN SET_TAC [], ALL_TAC] THEN
      ASM_SIMP_TAC [CARD_CLAUSES, FINITE_DELETE, IN_DELETE, SUC_SUB1],
      AP_TERM_TAC THEN UNDISCH_TAC (← q r"~(x:A IN s)") THEN SET_TAC []])

  let CARD_UNION_EQ ← prove
   r"!s t u:A->bool.
        FINITE u /\ s INTER t = {} /\ s UNION t = u
        ==> (CARD s + CARD t = CARD u)"
   (MESON_TAC [CARD_UNION, FINITE_SUBSET, SUBSET_UNION])

  let CARD_DIFF ← prove
   r"!s t:A->bool. FINITE s /\ t SUBSET s ==> CARD(s DIFF t) = CARD s - CARD t"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (← ARITH_RULE (← q r"a + b:num = c ==> a = c - b")) THEN
    MATCH_MP_TAC CARD_UNION_EQ THEN ASM_SIMP_TAC [] THEN ASM SET_TAC [])

  let CARD_EQ_0 ← prove
   r"!s:A->bool. FINITE s ==> ((CARD s = 0) <=> (s = {}))"
   (MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [CARD_CLAUSES, NOT_INSERT_EMPTY, NOT_SUC])

  let CARD_SING ← prove
   r"!a:A. CARD {a} = 1"
   (SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY, NOT_IN_EMPTY, ARITH])

  let CARD_LE_2 ← prove
   r"!a (b:A). CARD{a,b} <= 2"
   (SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY,
              IN_INSERT, NOT_IN_EMPTY] THEN
    REPEAT (GEN_TAC ORELSE COND_CASES_TAC) THEN ARITH_TAC)

  let CARD_LE_3 ← prove
   r"!a b (c:A). CARD{a,b,c} <= 3"
   (SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY,
              IN_INSERT, NOT_IN_EMPTY] THEN
    REPEAT (GEN_TAC ORELSE COND_CASES_TAC) THEN ARITH_TAC)

  let CARD_LE_4 ← prove
   r"!a b c (d:A). CARD{a,b,c,d} <= 4"
   (SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY,
              IN_INSERT, NOT_IN_EMPTY] THEN
    REPEAT (GEN_TAC ORELSE COND_CASES_TAC) THEN ARITH_TAC)

  /- A stronger still form of induction where we get to choose the element. -/

  let FINITE_INDUCT_DELETE ← prove
   r"!P. P {} /\
       (!s. FINITE s /\ ~(s = {}) ==> ?x. x IN s /\ (P(s DELETE x) ==> P s))
       ==> !s:A->bool. FINITE s ==> P s"
   (GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN WF_INDUCT_TAC (← q r"CARD(s:A->bool)") THEN
    ASM_CASES_TAC (← q r"s:A->bool = {}") THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    UNDISCH_TAC
     (← q r"!s. FINITE s /\ ~(s = {}) ==> ?x:A. x IN s /\ (P(s DELETE x) ==> P s)") THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"s:A->bool")) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"x:A") (CONJUNCTS_THEN2 ASSUME_TAC MATCH_MP_TAC)) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"s DELETE (x:A)")) THEN
    ASM_SIMP_TAC [FINITE_DELETE, CARD_DELETE, CARD_EQ_0,
                  ← ARITH_RULE (← q r"n - 1 < n <=> ~(n = 0)")])

  /- Relational form is often more useful. -/

  let HAS_SIZE ← new_definition
   r"(s:A->bool) HAS_SIZE n <=> FINITE s /\ CARD s = n"

  let HAS_SIZE_CARD ← prove
   r"!(s:A->bool) n. s HAS_SIZE n ==> CARD s = n"
   (SIMP_TAC [HAS_SIZE])

  let HAS_SIZE_0 ← prove
   r"!(s:A->bool). s HAS_SIZE 0 <=> (s = {})"
   (REPEAT GEN_TAC THEN REWRITE_TAC [HAS_SIZE] THEN
    EQ_TAC THEN DISCH_TAC THEN
    ASM_REWRITE_TAC [FINITE_RULES, CARD_CLAUSES] THEN
    FIRST_ASSUM (MP_TAC o CONJUNCT2) THEN
    FIRST_ASSUM (MP_TAC o CONJUNCT1) THEN
    SPEC_TAC (← q r"s:A->bool", ← q r"s:A->bool") THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [NOT_INSERT_EMPTY] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do pure (
      REWRITE_TAC [← MATCH_MP (← CONJUNCT2 CARD_CLAUSES) th])) THEN
    ASM_REWRITE_TAC [NOT_SUC])

  let HAS_SIZE_SUC ← prove
   r"!(s:A->bool) n. s HAS_SIZE (SUC n) <=>
                   ~(s = {}) /\ !a. a IN s ==> (s DELETE a) HAS_SIZE n"
   (REPEAT GEN_TAC THEN REWRITE_TAC [HAS_SIZE] THEN
    ASM_CASES_TAC (← q r"s:A->bool = {}") THEN
    ASM_REWRITE_TAC [CARD_CLAUSES, FINITE_RULES, NOT_IN_EMPTY, NOT_SUC] THEN
    REWRITE_TAC [FINITE_DELETE] THEN
    ASM_CASES_TAC (← q r"FINITE(s:A->bool)") THEN
    ASM_REWRITE_TAC [NOT_FORALL_THM, MEMBER_NOT_EMPTY] THEN
    EQ_TAC THEN REPEAT STRIP_TAC THENL
     [MP_TAC (← ISPECL [← q r"a:A", ← q r"s DELETE a:A"] (← CONJUNCT2 CARD_CLAUSES)) THEN
      ASM_REWRITE_TAC [FINITE_DELETE, IN_DELETE] THEN
      SUBGOAL_THEN (← q r"a INSERT (s DELETE a:A) = s") SUBST1_TAC THENL
       [UNDISCH_TAC (← q r"a:A IN s") THEN SET_TAC [],
        ASM_REWRITE_TAC [SUC_INJ] THEN MESON_TAC []],
      FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY]) THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"a:A")) THEN
      MP_TAC (← ISPECL [← q r"a:A", ← q r"s DELETE a:A"] (← CONJUNCT2 CARD_CLAUSES)) THEN
      ASM_REWRITE_TAC [FINITE_DELETE, IN_DELETE] THEN
      SUBGOAL_THEN (← q r"a INSERT (s DELETE a:A) = s") SUBST1_TAC THENL
       [UNDISCH_TAC (← q r"a:A IN s") THEN SET_TAC [],
        ASM_MESON_TAC []]])

  let HAS_SIZE_UNION ← prove
   r"!(s:A->bool) t m n.
        s HAS_SIZE m /\ t HAS_SIZE n /\ DISJOINT s t
        ==> (s UNION t) HAS_SIZE (m + n)"
   (SIMP_TAC [HAS_SIZE, FINITE_UNION, DISJOINT, CARD_UNION])

  let HAS_SIZE_DIFF ← prove
   r"!(s:A->bool) t m n.
        s HAS_SIZE m /\ t HAS_SIZE n /\ t SUBSET s
        ==> (s DIFF t) HAS_SIZE (m - n)"
   (SIMP_TAC [HAS_SIZE, FINITE_DIFF, CARD_DIFF])

  -- The two SET_RULEs run (and print) right to left, as in OCaml.
  let HAS_SIZE_UNIONS ← prove
   r"!s t:A->B->bool m n.
        s HAS_SIZE m /\
        (!x. x IN s ==> t(x) HAS_SIZE n) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (t x) (t y))
        ==> UNIONS {t(x) | x IN s} HAS_SIZE (m * n)"
   (← do
    let r2 ← SET_RULE
     (← q r"DISJOINT a (UNIONS s) <=> !x. x IN s ==> DISJOINT a x")
    let a1 ← ARITH_RULE (← q r"SUC a * b = b + a * b")
    let r1 ← SET_RULE
     (← q r"UNIONS {t y | y IN x INSERT s} = t x UNION UNIONS {t y | y IN s}")
    pure
     (GEN_REWRITE_TAC (funpow 4 BINDER_CONV o funpow 2 LAND_CONV) [HAS_SIZE] THEN
      REWRITE_TAC [← GSYM CONJ_ASSOC] THEN
      ONCE_REWRITE_TAC [IMP_CONJ] THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
      MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
       [REPEAT GEN_TAC THEN REWRITE_TAC [CARD_CLAUSES] THEN
        DISCH_THEN (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC : thm → tactic)) THEN
        REWRITE_TAC [MULT_CLAUSES, HAS_SIZE_0, EMPTY_UNIONS] THEN
        REWRITE_TAC [IN_ELIM_THM, NOT_IN_EMPTY],
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"s:A->bool"] THEN STRIP_TAC THEN
      MAP_EVERY X_GEN_TAC [← q r"t:A->B->bool", ← q r"m:num", ← q r"n:num"] THEN
      ASM_SIMP_TAC [CARD_CLAUSES] THEN
      DISCH_THEN (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) STRIP_ASSUME_TAC) THEN
      REWRITE_TAC [r1] THEN
      REWRITE_TAC [a1] THEN
      MATCH_MP_TAC HAS_SIZE_UNION THEN ASM_SIMP_TAC [IN_INSERT] THEN
      REWRITE_TAC [r2] THEN
      ASM_SIMP_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
      ASM_MESON_TAC [IN_INSERT]))

  let FINITE_HAS_SIZE ← prove
   r"!s:A->bool. FINITE s <=> s HAS_SIZE CARD s"
   (REWRITE_TAC [HAS_SIZE])

  /- This is often more useful as a rewrite. -/

  let HAS_SIZE_CLAUSES ← prove
   r"(s HAS_SIZE 0 <=> s = {}) /\
   (s HAS_SIZE (SUC n) <=>
        ?(a:A) t. t HAS_SIZE n /\ ~(a IN t) /\ (s = a INSERT t))"
   (← do
    let lemma ← SET_RULE (← q r"a IN s ==> (s = a INSERT (s DELETE a))")
    pure
     (REWRITE_TAC [HAS_SIZE_0] THEN REPEAT STRIP_TAC THEN EQ_TAC THENL
       [REWRITE_TAC [HAS_SIZE_SUC, ← GSYM MEMBER_NOT_EMPTY] THEN
        MESON_TAC [lemma, IN_DELETE],
        SIMP_TAC [LEFT_IMP_EXISTS_THM, HAS_SIZE, CARD_CLAUSES, FINITE_INSERT]]))

  /- Produce an explicit expansion for "s HAS_SIZE n" for numeral n. -/

  let HAS_SIZE_CONV ← do
    let pth ← prove
     r"(~((a:A) IN {}) /\ P <=> P) /\
       (~(a IN {b}) /\ P <=> ~(a = b) /\ P) /\
       (~(a IN (b INSERT cs)) /\ P <=> ~(a = b) /\ ~(a IN cs) /\ P)"
     (SET_TAC [])
    let qth ← prove
     r"((?s. s HAS_SIZE 0 /\ P s) <=> P {}) /\
       ((?s. s HAS_SIZE (SUC n) /\ P s) <=>
        (?(a:A) s. s HAS_SIZE n /\ ~(a IN s) /\ P(a INSERT s)))"
     (REWRITE_TAC [HAS_SIZE_CLAUSES] THEN MESON_TAC [])
    let qconv_0 ← GEN_REWRITE_CONV_NET I [← CONJUNCT1 qth]
    let qconv_1 ← GEN_REWRITE_CONV_NET I [← CONJUNCT2 qth]
    let rconv_0 ← GEN_REWRITE_CONV_NET I [← CONJUNCT1 pth]
    let rconv_1 ← GEN_REWRITE_CONV_NET I [← CONJUNCT2 pth]
    let EXISTS_HAS_SIZE_AND_CONV := existsHasSizeAndConv num_CONV qconv_0 qconv_1
    let NOT_IN_INSERT_CONV := notInInsertConv rconv_0 rconv_1
    let HAS_SIZE_CONV :=
      (← GEN_REWRITE_CONV_NET I [← CONJUNCT1 HAS_SIZE_CLAUSES]) ORELSEC
      (RAND_CONV num_CONV THENC
       (← GEN_REWRITE_CONV_NET I [← CONJUNCT2 HAS_SIZE_CLAUSES]) THENC
       BINDER_CONV EXISTS_HAS_SIZE_AND_CONV)
    pure (fun tm => ExceptT.run do
      let th ← HAS_SIZE_CONV tm
      let tm' ← rand (concl th)
      let (evs, _bod) := HolCore.Basics.strip_exists tm'
      if evs.isEmpty then pure th else
      let th' ← funpow evs.length BINDER_CONV NOT_IN_INSERT_CONV tm'
      HolLight.TRANS th th' : ioconv)

  return {
    CARD, CARD_CLAUSES, CARD_UNION, CARD_DELETE, CARD_UNION_EQ, CARD_DIFF,
    CARD_EQ_0, CARD_SING, CARD_LE_2, CARD_LE_3, CARD_LE_4,
    FINITE_INDUCT_DELETE, HAS_SIZE, HAS_SIZE_CARD, HAS_SIZE_0, HAS_SIZE_SUC,
    HAS_SIZE_UNION, HAS_SIZE_DIFF, HAS_SIZE_UNIONS, FINITE_HAS_SIZE,
    HAS_SIZE_CLAUSES, HAS_SIZE_CONV }

/- ---------------------------------------------------------------------- -/
/- Various useful lemmas about cardinalities of unions etc.               -/
/- (sets.ml 2244-2652)                                                    -/
/- ---------------------------------------------------------------------- -/

/-- Cardinality lemmas for unions and images, the "choose a smaller subset"
    principle, and the parity of an involution's fixed points (sets.ml
    2244-2652).  Depends on the Stage-1 `SetsCard` bundle `SCard` (`CARD`,
    `CARD_UNION`, `CARD_DELETE`, `CARD_DIFF`, `CARD_EQ_0`, `CARD_CLAUSES`,
    `HAS_SIZE`, `HAS_SIZE_0`, `HAS_SIZE_SUC`, `HAS_SIZE_UNION`,
    `HAS_SIZE_CONV`). -/
structure SetsCard2 where
  /-- `CARD_SUBSET_EQ` (sets.ml 2247): `FINITE b /\ a SUBSET b /\
      CARD a = CARD b ==> a = b`.  `CARD_UNION` on `a`,`b DIFF a`, then TWO
      width-2 `SUBGOAL_THEN` `THENL`s and a `MP_TAC` one. -/
  CARD_SUBSET_EQ : thm
  /-- `CARD_SUBSET` (sets.ml 2268): `a SUBSET b /\ FINITE b ==>
      CARD a <= CARD b`.  Two width-2 `SUBGOAL_THEN` `THENL`s; the second
      has an inner `REPEAT CONJ_TAC THENL [..;..;..]` of width 3. -/
  CARD_SUBSET : thm
  /-- `CARD_SUBSET_LE` (sets.ml 2284): `MESON[CARD_SUBSET; CARD_SUBSET_EQ;
      LE_ANTISYM]`. -/
  CARD_SUBSET_LE : thm
  /-- `SUBSET_CARD_EQ` (sets.ml 2288): `MESON[CARD_SUBSET_EQ; LE_ANTISYM;
      CARD_SUBSET]`. -/
  SUBSET_CARD_EQ : thm
  /-- `FINITE_CARD_LE_SUBSET` (sets.ml 2292): `MESON[FINITE_SUBSET;
      CARD_SUBSET; LE_TRANS]`. -/
  FINITE_CARD_LE_SUBSET : thm
  /-- `CARD_PSUBSET` (sets.ml 2298): `a PSUBSET b /\ FINITE b ==>
      CARD a < CARD b`.  `SET_RULE` rewrite, `LET_TRANS`, no top-level
      `THENL`. -/
  CARD_PSUBSET : thm
  /-- `CARD_PSUBSET_IMP` (sets.ml 2309): `REWRITE_TAC[PSUBSET] THEN
      MESON_TAC[]`. -/
  CARD_PSUBSET_IMP : thm
  /-- `CARD_PSUBSET_EQ` (sets.ml 2313): `MESON[CARD_PSUBSET_IMP; CARD_PSUBSET;
      LT_REFL]`. -/
  CARD_PSUBSET_EQ : thm
  /-- `CARD_UNION_LE` (sets.ml 2317): `CARD(s UNION t) <= CARD s + CARD t`.
      `LE_TRANS`, `ONCE_REWRITE_TAC[SET_RULE ..]`, `CARD_UNION`.  No
      top-level `THENL`. -/
  CARD_UNION_LE : thm
  /-- `FINITE_CARD_LE_UNION` (sets.ml 2327): `MESON[FINITE_UNION;
      CARD_UNION_LE; LE_ADD2; LE_TRANS]`. -/
  FINITE_CARD_LE_UNION : thm
  /-- `CARD_UNIONS_LE` (sets.ml 2334): `CARD(UNIONS {t x | x IN s}) <= m*n`.
      `GEN_REWRITE_TAC (funpow 4 BINDER_CONV o funpow 2 LAND_CONV) [HAS_SIZE]`,
      `FINITE_INDUCT_STRONG`, ONE `CONJ_TAC THENL [..;..]` of width 2. -/
  CARD_UNIONS_LE : thm
  /-- `CARD_UNION_GEN` (sets.ml 2358): `CARD(s UNION t) =
      (CARD s + CARD t) - CARD(s INTER t)`.  No top-level `THENL`. -/
  CARD_UNION_GEN : thm
  /-- `CARD_UNION_OVERLAP_EQ` (sets.ml 2369): `CARD(s UNION t) =
      CARD s + CARD t <=> s INTER t = {}`.  No top-level `THENL`. -/
  CARD_UNION_OVERLAP_EQ : thm
  /-- `CARD_UNION_OVERLAP` (sets.ml 2378): `SIMP_TAC[GSYM
      CARD_UNION_OVERLAP_EQ] THEN ARITH_TAC`. -/
  CARD_UNION_OVERLAP : thm
  /-- `CARD_IMAGE_INJ` (sets.ml 2388): `CARD(IMAGE f s) = CARD s` for injective
      `f`.  `TAUT` reshuffle, `FINITE_INDUCT_STRONG`, then a
      `COND_CASES_TAC THEN ASM_MESON_TAC[IN_INSERT]`. -/
  CARD_IMAGE_INJ : thm
  /-- `HAS_SIZE_IMAGE_INJ` (sets.ml 2399): `SIMP_TAC[HAS_SIZE; FINITE_IMAGE]
      THEN MESON_TAC[CARD_IMAGE_INJ]`. -/
  HAS_SIZE_IMAGE_INJ : thm
  /-- `CARD_IMAGE_LE` (sets.ml 2405): `CARD(IMAGE f s) <= CARD s`.
      `FINITE_INDUCT_STRONG`, `COND_CASES_TAC`, `ARITH_TAC`. -/
  CARD_IMAGE_LE : thm
  /-- `FINITE_CARD_LE_IMAGE` (sets.ml 2412): `MESON[CARD_IMAGE_LE; LE_TRANS;
      FINITE_IMAGE]`. -/
  FINITE_CARD_LE_IMAGE : thm
  /-- `CARD_IMAGE_INJ_EQ` (sets.ml 2417): a "unique preimage" characterisation.
      ONE width-2 `SUBGOAL_THEN .. SUBST1_TAC THENL [..;..]`. -/
  CARD_IMAGE_INJ_EQ : thm
  /-- `CARD_SUBSET_IMAGE` (sets.ml 2428): `MESON[LE_TRANS; FINITE_IMAGE;
      CARD_IMAGE_LE; CARD_SUBSET]`. -/
  CARD_SUBSET_IMAGE : thm
  /-- `HAS_SIZE_IMAGE_INJ_EQ` (sets.ml 2432): `(IMAGE f s) HAS_SIZE n <=>
      s HAS_SIZE n` for injective `f`.  A `TAUT` split via `CONJ_TAC THENL
      [..;..]` (width 2). -/
  HAS_SIZE_IMAGE_INJ_EQ : thm
  /-- `CARD_IMAGE_EQ_INJ` (sets.ml 2445): `CARD(IMAGE f s) = CARD s <=>`
      injectivity.  `EQ_TAC THENL [..;..]`, then a `SUBGOAL_THEN .. SUBST1_TAC
      THENL [ASM SET_TAC[]; REWRITE_TAC[]]` (width 2). -/
  CARD_IMAGE_EQ_INJ : thm
  /-- `EXISTS_SMALL_SUBSET_IMAGE_INJ` (sets.ml 2464): reindex a small subset of
      `IMAGE f s` by an injective-on subset of `s`.  A `TAUT` reshuffle,
      `EXISTS_SUBSET_IMAGE_INJ`, `AP_TERM_TAC THEN ABS_TAC`, `MESON`. -/
  EXISTS_SMALL_SUBSET_IMAGE_INJ : thm
  /-- `FORALL_SMALL_SUBSET_IMAGE_INJ` (sets.ml 2478): the `!`-dual, via
      `(!t. p) <=> ~(?t. ~p)` and `EXISTS_SMALL_SUBSET_IMAGE_INJ`. -/
  FORALL_SMALL_SUBSET_IMAGE_INJ : thm
  /-- `EXISTS_SMALL_SUBSET_IMAGE` (sets.ml 2488): the non-injective form.
      `EQ_TAC THENL [..;..]` (width 2). -/
  EXISTS_SMALL_SUBSET_IMAGE : thm
  /-- `FORALL_SMALL_SUBSET_IMAGE` (sets.ml 2497): the `!`-dual. -/
  FORALL_SMALL_SUBSET_IMAGE : thm
  /-- `CARD_IMAGE_LE2` (sets.ml 2505): `CARD(IMAGE f s) <= CARD(IMAGE g s)`
      when `g x = g y ==> f x = f y`.  `FUNCTION_FACTORS_LEFT_GEN`,
      `TRANS_TAC LE_TRANS`, `IMAGE_o`. -/
  CARD_IMAGE_LE2 : thm
  /-- `CARD_IMAGE_LT2` (sets.ml 2516): the strict version.  ONE width-2
      `SUBGOAL_THEN .. SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC]`. -/
  CARD_IMAGE_LT2 : thm
  /-- `CHOOSE_SUBSET_STRONG` (sets.ml 2533): `(FINITE s ==> n <= CARD s) ==>
      ?t. t SUBSET s /\ t HAS_SIZE n`.  `INDUCT_TAC THEN .. THENL [..;ALL_TAC]`,
      `SET_PROVE_CASES`, then `COND_CASES_TAC`.  Width-2 top `THENL`. -/
  CHOOSE_SUBSET_STRONG : thm
  /-- `CHOOSE_SUBSET_EQ` (sets.ml 2552): `(FINITE s ==> n <= CARD s) <=>
      (?t. t SUBSET s /\ t HAS_SIZE n)`.  `EQ_TAC`, `TRANS_TAC LE_TRANS`. -/
  CHOOSE_SUBSET_EQ : thm
  /-- `CHOOSE_SUBSET` (sets.ml 2560): `MESON[CHOOSE_SUBSET_STRONG]`. -/
  CHOOSE_SUBSET : thm
  /-- `CHOOSE_SUBSET_BETWEEN` (sets.ml 2564): interpolate a size-`n` set between
      `s` and `u`.  `CHOOSE_SUBSET_STRONG` on `n - CARD s`,`u DIFF s`;
      `ANTS_TAC THENL [..;..]`, inner `SUBGOAL_THEN .. SUBST1_TAC THENL
      [..;..]`. -/
  CHOOSE_SUBSET_BETWEEN : thm
  /-- `CARD_LE_UNIONS_CHAIN` (sets.ml 2585): a chain of `<= n`-sized sets has
      union `<= n`.  `GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM]`, `CHOOSE_SUBSET_EQ`,
      `MONO_EXISTS`, `FINITE_SUBSET_UNIONS_CHAIN`.  No top-level `THENL`. -/
  CARD_LE_UNIONS_CHAIN : thm
  /-- `CARD_LE_1` (sets.ml 2603): `FINITE s /\ CARD s <= 1 <=> ?a. s SUBSET {a}`.
      `CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN SET_TAC[]`. -/
  CARD_LE_1 : thm
  /-- `INVOLUTION_EVEN_NOFIXPOINTS` (sets.ml 2613): a fixed-point-free involution
      on a finite set forces `EVEN(CARD s)`.  `ABBREV_TAC`, `num_WF`,
      `SET_PROVE_CASES`, nested `ASM_CASES_TAC`; the final `CONJ_TAC THENL
      [ASM_ARITH_TAC; ASM SET_TAC[]]` is width 2. -/
  INVOLUTION_EVEN_NOFIXPOINTS : thm
  /-- `INVOLUTION_EVEN_FIXPOINTS` (sets.ml 2638): for an involution the parity
      of the fixed-point set matches the parity of `CARD s`.  `TRANS_TAC
      EQ_TRANS`, `CONJ_TAC THENL [ALL_TAC; ..]` (width 2),
      `INVOLUTION_EVEN_NOFIXPOINTS`. -/
  INVOLUTION_EVEN_FIXPOINTS : thm
  deriving Inhabited

@[nospecialize]
def setupSetsCard2 [HolBase] (S : SetsCore)
    (P : SetsProps) (SIn : SetsInclusion) (SOp : SetsOperators)
    (SUn : SetsUnions) (SImg : SetsImage)
    (SMi : SetsMisc) (SFin : SetsFinite) (SInd : SetsInduct)
    (SFn : SetsFunctions) (SCard : SetsCard)
    (MESON_TAC : List thm → tactic) (ASM_MESON_TAC : List thm → tactic)
    (MESON' : List thm → term → IO (Except String thm))
    (LE_TRANS LET_TRANS LE_ANTISYM LE_REFL LT_REFL LT_LE LE_SUC LE_0
     LE_ADD2 LE_ADD_LCANCEL EQ_IMP_LE ADD_EQ_0 SUC_SUB1
     num_WF EVEN_ADD EVEN_SUB ARITH : thm)
    (ARITH_RULE' : term → IO (Except String thm))
    (ARITH_TAC : tactic)
    (ASM_ARITH_TAC : tactic)
    (INDUCT_TAC : tactic) :
    ExceptT String IO SetsCard2 := do
  let SET_TAC := SET_TAC S P MESON_TAC
  let SET_RULE := SET_RULE S P MESON_TAC
  let MESON (ths : List thm) (t : term) : ExceptT String IO thm := MESON' ths t
  let ARITH_RULE (t : term) : ExceptT String IO thm := ARITH_RULE' t
  let { EXTENSION, PSUBSET, FINITE_RULES, .. } := S
  let { NOT_IN_EMPTY, IN_INSERT, IN_IMAGE, FORALL_IN_INSERT, FORALL_IN_IMAGE, .. } := P
  let { MEMBER_NOT_EMPTY, EMPTY_SUBSET, .. } := SIn
  let { INTER_SUBSET, SUBSET_DIFF, .. } := SOp
  let { UNIONS_0, .. } := SUn
  let { IMAGE_CLAUSES, IMAGE_o, IMAGE_SUBSET, .. } := SImg
  let { SET_PROVE_CASES, .. } := SMi
  let { FINITE_EMPTY, FINITE_SUBSET, FINITE_RESTRICT, FINITE_UNION,
        FINITE_INTER, FINITE_INSERT, FINITE_DELETE, FINITE_FINITE_UNIONS,
        FINITE_IMAGE, FINITE_IMAGE_INJ_EQ, EXISTS_SUBSET_IMAGE_INJ,
        FINITE_DIFF, FINITE_SUBSET_UNIONS_CHAIN, .. } := SFin
  let { FINITE_INDUCT_STRONG, .. } := SInd
  let { FUNCTION_FACTORS_LEFT_GEN, .. } := SFn
  let { CARD_CLAUSES, CARD_UNION, CARD_DELETE, CARD_DIFF, CARD_EQ_0, HAS_SIZE,
        HAS_SIZE_0, HAS_SIZE_SUC, HAS_SIZE_UNION, HAS_SIZE_CONV, .. } := SCard
  let { EQ_TRANS, CONJ_ASSOC, IMP_CONJ, LEFT_OR_DISTRIB, SWAP_EXISTS_THM,
        RIGHT_AND_EXISTS_THM, RIGHT_FORALL_IMP_THM, MONO_EXISTS, .. } := HolBase.T
  let { NOT_IMP, CONTRAPOS_THM, NOT_FORALL_THM, .. } := HolBase.C

  let CARD_SUBSET_EQ ← prove
   r"!(a:A->bool) b. FINITE b /\ a SUBSET b /\ (CARD a = CARD b) ==> (a = b)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"a:A->bool", ← q r"b DIFF (a:A->bool)"] CARD_UNION) THEN
    SUBGOAL_THEN (← q r"FINITE(a:A->bool)") ASSUME_TAC THENL
     [ASM_MESON_TAC [FINITE_SUBSET], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"FINITE(b:A->bool DIFF a)") ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"b:A->bool") THEN
      ASM_REWRITE_TAC [] THEN SET_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"a:A->bool INTER (b DIFF a) = EMPTY") ASSUME_TAC THENL
     [SET_TAC [], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"a UNION (b:A->bool DIFF a) = b") ASSUME_TAC THENL
     [UNDISCH_TAC (← q r"a:A->bool SUBSET b") THEN SET_TAC [], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"(a = a + b) <=> (b = 0)")] THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"b:A->bool DIFF a = EMPTY") MP_TAC THENL
     [REWRITE_TAC [← GSYM HAS_SIZE_0] THEN
      ASM_REWRITE_TAC [HAS_SIZE],
      UNDISCH_TAC (← q r"a:A->bool SUBSET b") THEN SET_TAC []])

  let CARD_SUBSET ← prove
   r"!(a:A->bool) b. a SUBSET b /\ FINITE(b) ==> CARD(a) <= CARD(b)"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"b:A->bool = a UNION (b DIFF a)") SUBST1_TAC THENL
     [UNDISCH_TAC (← q r"a:A->bool SUBSET b") THEN SET_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"CARD (a UNION b DIFF a) = CARD(a:A->bool) + CARD(b DIFF a)")
    SUBST1_TAC THENL
     [MATCH_MP_TAC CARD_UNION THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"b:A->bool") THEN
        ASM_REWRITE_TAC [],
        MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"b:A->bool") THEN
        ASM_REWRITE_TAC [] THEN SET_TAC [],
        SET_TAC []],
      ARITH_TAC])

  let CARD_SUBSET_LE ← prove
   r"!(a:A->bool) b. FINITE b /\ a SUBSET b /\ CARD b <= CARD a ==> a = b"
   (MESON_TAC [CARD_SUBSET, CARD_SUBSET_EQ, LE_ANTISYM])

  let SUBSET_CARD_EQ ← prove
   r"!s t:A->bool. FINITE t /\ s SUBSET t ==> (CARD s = CARD t <=> s = t)"
   (MESON_TAC [CARD_SUBSET_EQ, LE_ANTISYM, CARD_SUBSET])

  let FINITE_CARD_LE_SUBSET ← prove
   r"!s (t:A->bool) n.
        s SUBSET t /\ FINITE t /\ CARD t <= n
        ==> FINITE s /\ CARD s <= n"
   (MESON_TAC [FINITE_SUBSET, CARD_SUBSET, LE_TRANS])

  let CARD_PSUBSET ← prove
   r"!(a:A->bool) b. a PSUBSET b /\ FINITE(b) ==> CARD(a) < CARD(b)"
   (← do
    let a1 ← ARITH_RULE (← q r"n - 1 < n <=> ~(n = 0)")
    let s1 ← SET_RULE
     (← q r"a PSUBSET b <=> ?x. x IN b /\ ~(x IN a) /\ a SUBSET (b DELETE x)")
    pure
     (REPEAT GEN_TAC THEN REWRITE_TAC [s1] THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"x:A") STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC (← q r"CARD(b DELETE (x:A))") THEN
      ASM_SIMP_TAC [CARD_SUBSET, FINITE_DELETE] THEN
      ASM_SIMP_TAC [CARD_DELETE, a1] THEN
      ASM_MESON_TAC [CARD_EQ_0, MEMBER_NOT_EMPTY]))

  let CARD_PSUBSET_IMP ← prove
   r"!a b:A->bool. a SUBSET b /\ ~(CARD a = CARD b) ==> a PSUBSET b"
   (REWRITE_TAC [PSUBSET] THEN MESON_TAC [])

  let CARD_PSUBSET_EQ ← prove
   r"!a b:A->bool. FINITE b /\ a SUBSET b ==> (a PSUBSET b <=> CARD a < CARD b)"
   (MESON_TAC [CARD_PSUBSET_IMP, CARD_PSUBSET, LT_REFL])

  let CARD_UNION_LE ← prove
   r"!s t:A->bool.
        FINITE s /\ FINITE t ==> CARD(s UNION t) <= CARD(s) + CARD(t)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC (← q r"CARD(s:A->bool) + CARD(t DIFF s)") THEN
    ASM_SIMP_TAC [LE_ADD_LCANCEL, CARD_SUBSET, SUBSET_DIFF, FINITE_DIFF] THEN
    MATCH_MP_TAC EQ_IMP_LE THEN
    ONCE_REWRITE_TAC [← SET_RULE (← q r"s UNION t = s UNION (t DIFF s)")] THEN
    MATCH_MP_TAC CARD_UNION THEN ASM_SIMP_TAC [FINITE_DIFF] THEN SET_TAC [])

  let FINITE_CARD_LE_UNION ← prove
   r"!s (t:A->bool) m n.
        (FINITE s /\ CARD s <= m) /\
        (FINITE t /\ CARD t <= n)
        ==> FINITE(s UNION t) /\ CARD(s UNION t) <= m + n"
   (MESON_TAC [FINITE_UNION, CARD_UNION_LE, LE_ADD2, LE_TRANS])

  -- The three SET_RULEs run (and print) right to left, as in OCaml.
  let CARD_UNIONS_LE ← prove
   r"!s t:A->B->bool m n.
        s HAS_SIZE m /\ (!x. x IN s ==> FINITE(t x) /\ CARD(t x) <= n)
        ==> CARD(UNIONS {t(x) | x IN s}) <= m * n"
   (← do
    let a1 ← ARITH_RULE (← q r"a <= n /\ b <= x * n ==> a + b <= SUC x * n")
    let r3 ← SET_RULE (← q r"{t x | x IN s} = IMAGE t s")
    let r2 ← SET_RULE
     (← q r"UNIONS {t x | x IN a INSERT s} = t(a) UNION UNIONS {t x | x IN s}")
    let r1 ← SET_RULE (← q r"UNIONS {t x | x IN {}} = {}")
    pure
     (GEN_REWRITE_TAC (funpow 4 BINDER_CONV o funpow 2 LAND_CONV) [HAS_SIZE] THEN
      REWRITE_TAC [← GSYM CONJ_ASSOC] THEN
      ONCE_REWRITE_TAC [IMP_CONJ] THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
      MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THEN
      REWRITE_TAC [r1, CARD_CLAUSES, LE_0] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
      ASM_SIMP_TAC [CARD_CLAUSES, FINITE_RULES] THEN
      DISCH_THEN (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC) THEN
      REWRITE_TAC [r2] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC
       (← q r"CARD((t:A->B->bool) x) + CARD(UNIONS {(t:A->B->bool) y | y IN s})") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CARD_UNION_LE THEN ASM_SIMP_TAC [IN_INSERT] THEN
        REWRITE_TAC [r3] THEN
        ASM_SIMP_TAC [FINITE_FINITE_UNIONS, FINITE_IMAGE, FORALL_IN_IMAGE,
                      IN_INSERT],
        MATCH_MP_TAC a1 THEN
        ASM_SIMP_TAC [IN_INSERT]]))

  -- The two SET_RULEs run (and print) right to left, as in OCaml.
  let CARD_UNION_GEN ← prove
   r"!s t:A->bool.
        FINITE s /\ FINITE t
        ==> CARD(s UNION t) = (CARD(s) + CARD(t)) - CARD(s INTER t)"
   (← do
    let r2 ← SET_RULE (← q r"t DIFF (s INTER t) = t DIFF s")
    let a1 ← ARITH_RULE (← q r"x:num <= y ==> (a + y) - x = a + (y - x)")
    let r1 ← SET_RULE (← q r"s UNION t = s UNION (t DIFF s)")
    pure
     (REPEAT STRIP_TAC THEN
      ONCE_REWRITE_TAC [r1] THEN
      ASM_SIMP_TAC [a1, CARD_SUBSET, INTER_SUBSET, ← GSYM CARD_DIFF] THEN
      REWRITE_TAC [r2] THEN
      MATCH_MP_TAC CARD_UNION THEN ASM_SIMP_TAC [FINITE_DIFF] THEN SET_TAC []))

  let CARD_UNION_OVERLAP_EQ ← prove
   r"!s t:A->bool.
        FINITE s /\ FINITE t
        ==> (CARD(s UNION t) = CARD s + CARD t <=> s INTER t = {})"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC [CARD_UNION_GEN] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"a - b = a <=> b = 0 \/ a = 0")] THEN
    ASM_SIMP_TAC [ADD_EQ_0, CARD_EQ_0, FINITE_INTER] THEN SET_TAC [])

  let CARD_UNION_OVERLAP ← prove
   r"!s t:A->bool.
        FINITE s /\ FINITE t /\ CARD(s UNION t) < CARD(s) + CARD(t)
        ==> ~(s INTER t = {})"
   (SIMP_TAC [← GSYM CARD_UNION_OVERLAP_EQ] THEN ARITH_TAC)

  /- Cardinality of image under maps, injective or general. -/

  let CARD_IMAGE_INJ ← prove
   r"!(f:A->B) s. (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\
                FINITE s ==> (CARD (IMAGE f s) = CARD s)"
   (GEN_TAC THEN
    REWRITE_TAC [← TAUT (← q r"a /\ b ==> c <=> b ==> a ==> c")] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [NOT_IN_EMPTY, IMAGE_CLAUSES] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [CARD_CLAUSES, FINITE_IMAGE, IN_IMAGE] THEN
    COND_CASES_TAC THEN ASM_MESON_TAC [IN_INSERT])

  let HAS_SIZE_IMAGE_INJ ← prove
   r"!(f:A->B) s n.
        (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\ s HAS_SIZE n
        ==> (IMAGE f s) HAS_SIZE n"
   (SIMP_TAC [HAS_SIZE, FINITE_IMAGE] THEN MESON_TAC [CARD_IMAGE_INJ])

  let CARD_IMAGE_LE ← prove
   r"!(f:A->B) s. FINITE s ==> CARD(IMAGE f s) <= CARD s"
   (GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [IMAGE_CLAUSES, CARD_CLAUSES, FINITE_IMAGE, LE_REFL] THEN
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    DISCH_THEN (MP_TAC o CONJUNCT1) THEN ARITH_TAC)

  let FINITE_CARD_LE_IMAGE ← prove
   r"!(f:A->B) s n.
        FINITE s /\ CARD s <= n ==> FINITE(IMAGE f s) /\ CARD(IMAGE f s) <= n"
   (MESON_TAC [CARD_IMAGE_LE, LE_TRANS, FINITE_IMAGE])

  let CARD_IMAGE_INJ_EQ ← prove
   r"!f:A->B s t.
        FINITE s /\
        (!x. x IN s ==> f(x) IN t) /\
        (!y. y IN t ==> ?!x. x IN s /\ f(x) = y)
        ==> CARD t = CARD s"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"t = IMAGE (f:A->B) s") SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_IMAGE] THEN ASM_MESON_TAC [],
      MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_MESON_TAC []])

  let CARD_SUBSET_IMAGE ← prove
   r"!(f:A->B) s t. FINITE t /\ s SUBSET IMAGE f t ==> CARD s <= CARD t"
   (MESON_TAC [LE_TRANS, FINITE_IMAGE, CARD_IMAGE_LE, CARD_SUBSET])

  let HAS_SIZE_IMAGE_INJ_EQ ← prove
   r"!(f:A->B) s n.
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> ((IMAGE f s) HAS_SIZE n <=> s HAS_SIZE n)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [HAS_SIZE] THEN
    MATCH_MP_TAC (← TAUT
     (← q r"(a' <=> a) /\ (a ==> (b' <=> b)) ==> (a' /\ b' <=> a /\ b)")) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE_INJ_EQ,
      DISCH_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC CARD_IMAGE_INJ] THEN
    ASM_REWRITE_TAC [])

  let CARD_IMAGE_EQ_INJ ← prove
   r"!f:A->B s.
        FINITE s
        ==> (CARD(IMAGE f s) = CARD s <=>
             !x y. x IN s /\ y IN s /\ f x = f y ==> x = y)"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [DISCH_TAC, ASM_MESON_TAC [CARD_IMAGE_INJ]] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"y:A"] THEN STRIP_TAC THEN
    ASM_CASES_TAC (← q r"x:A = y") THEN ASM_REWRITE_TAC [] THEN
    UNDISCH_TAC (← q r"CARD(IMAGE (f:A->B) s) = CARD s") THEN
    SUBGOAL_THEN (← q r"IMAGE  (f:A->B) s = IMAGE f (s DELETE y)") SUBST1_TAC THENL
     [ASM SET_TAC [], REWRITE_TAC []] THEN
    MATCH_MP_TAC (← ARITH_RULE (← q r"!n. m <= n /\ n < p ==> ~(m:num = p)")) THEN
    EXISTS_TAC (← q r"CARD(s DELETE (y:A))") THEN
    ASM_SIMP_TAC [CARD_IMAGE_LE, FINITE_DELETE] THEN
    ASM_SIMP_TAC [CARD_DELETE, CARD_EQ_0,
                  ← ARITH_RULE (← q r"n - 1 < n <=> ~(n = 0)")] THEN
    ASM SET_TAC [])

  let EXISTS_SMALL_SUBSET_IMAGE_INJ ← prove
   r"!P (f:A->B) s n.
    (?t. FINITE t /\ CARD t < n /\ t SUBSET IMAGE f s /\ P t) <=>
    (?t. FINITE t /\ CARD t < n /\ t SUBSET s /\
         (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y)) /\
         P (IMAGE f t))"
   (ONCE_REWRITE_TAC [← TAUT (← q r"p /\ q /\ r /\ s <=> r /\ s /\ p /\ q")] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [EXISTS_SUBSET_IMAGE_INJ] THEN
    REWRITE_TAC [CONJ_ASSOC] THEN AP_TERM_TAC THEN ABS_TAC THEN
    MATCH_MP_TAC (← TAUT
     (← q r"(p ==> (q <=> s)) /\ (p /\ s ==> (r <=> t))
      ==> ((p /\ q) /\ r <=> (p /\ s) /\ t)")) THEN
    MESON_TAC [CARD_IMAGE_INJ, FINITE_IMAGE_INJ_EQ])

  let FORALL_SMALL_SUBSET_IMAGE_INJ ← prove
   r"!P (f:A->B) s n.
    (!t. FINITE t /\ CARD t < n /\ t SUBSET IMAGE f s ==> P t) <=>
    (!t. FINITE t /\ CARD t < n /\ t SUBSET s /\
         (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y))
         ==> P (IMAGE f t))"
   (REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC [← MESON [] (← q r"(!t. p t) <=> ~(?t. ~p t)")] THEN
    REWRITE_TAC [NOT_IMP, EXISTS_SMALL_SUBSET_IMAGE_INJ, ← GSYM CONJ_ASSOC])

  let EXISTS_SMALL_SUBSET_IMAGE ← prove
   r"!P (f:A->B) s n.
    (?t. FINITE t /\ CARD t < n /\ t SUBSET IMAGE f s /\ P t) <=>
    (?t. FINITE t /\ CARD t < n /\ t SUBSET s /\
         P (IMAGE f t))"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [REWRITE_TAC [EXISTS_SMALL_SUBSET_IMAGE_INJ] THEN MESON_TAC [],
      MESON_TAC [FINITE_IMAGE, CARD_IMAGE_LE, LET_TRANS, IMAGE_SUBSET]])

  let FORALL_SMALL_SUBSET_IMAGE ← prove
   r"!P (f:A->B) s n.
    (!t. FINITE t /\ CARD t < n /\ t SUBSET IMAGE f s ==> P t) <=>
    (!t. FINITE t /\ CARD t < n /\ t SUBSET s ==> P (IMAGE f t))"
   (REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC [← MESON [] (← q r"(!t. p t) <=> ~(?t. ~p t)")] THEN
    REWRITE_TAC [NOT_IMP, EXISTS_SMALL_SUBSET_IMAGE, ← GSYM CONJ_ASSOC])

  let CARD_IMAGE_LE2 ← prove
   r"!(f:A->B) (g:A->C) s.
        FINITE s /\
        (!x y. x IN s /\ y IN s /\ g x = g y ==> f x = f y)
        ==> CARD(IMAGE f s) <= CARD(IMAGE g s)"
   (REPEAT STRIP_TAC THEN FIRST_X_ASSUM (X_CHOOSE_TAC (← q r"h:C->B") o
      GEN_REWRITE_RULE I [FUNCTION_FACTORS_LEFT_GEN]) THEN
    TRANS_TAC LE_TRANS (← q r"CARD(IMAGE ((h:C->B) o (g:A->C)) s)") THEN
    ASM_SIMP_TAC [IMAGE_o, CARD_IMAGE_LE, FINITE_IMAGE] THEN
    MATCH_MP_TAC EQ_IMP_LE THEN AP_TERM_TAC THEN ASM SET_TAC [])

  let CARD_IMAGE_LT2 ← prove
   r"!(f:A->B) (g:A->C) s.
        FINITE s /\
        (!x y. x IN s /\ y IN s /\ g x = g y ==> f x = f y) /\
        ~(!x y. x IN s /\ y IN s /\ f x = f y ==> g x = g y)
        ==> CARD(IMAGE f s) < CARD(IMAGE g s)"
   (REPEAT STRIP_TAC THEN FIRST_X_ASSUM (X_CHOOSE_TAC (← q r"h:C->B") o
      GEN_REWRITE_RULE I [FUNCTION_FACTORS_LEFT_GEN]) THEN
    SUBGOAL_THEN (← q r"IMAGE f s = IMAGE (h:C->B) (IMAGE (g:A->C) s)") SUBST1_TAC THENL
     [ASM SET_TAC [], ALL_TAC] THEN
    ASM_SIMP_TAC [LT_LE, CARD_IMAGE_LE, FINITE_IMAGE, CARD_IMAGE_EQ_INJ] THEN
    ASM SET_TAC [])

  /- Choosing a smaller subset of a given size. -/

  let CHOOSE_SUBSET_STRONG ← prove
   r"!n s:A->bool.
        (FINITE s ==> n <= CARD s) ==> ?t. t SUBSET s /\ t HAS_SIZE n"
   (INDUCT_TAC THEN REWRITE_TAC [HAS_SIZE_0, HAS_SIZE_SUC] THENL
     [MESON_TAC [EMPTY_SUBSET], ALL_TAC] THEN
    MATCH_MP_TAC SET_PROVE_CASES THEN
    REWRITE_TAC [FINITE_EMPTY, CARD_CLAUSES, ← ARITH_RULE (← q r"~(SUC n <= 0)")] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:A", ← q r"s:A->bool"] THEN DISCH_TAC THEN
    ASM_SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, LE_SUC] THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"s:A->bool")) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"t:A->bool") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"(a:A) INSERT t") THEN
    REPEAT (CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC]) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [HAS_SIZE]) THEN
    ASM_SIMP_TAC [HAS_SIZE, CARD_DELETE, FINITE_INSERT, FINITE_DELETE,
                  CARD_CLAUSES] THEN
    GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [SUC_SUB1] THEN
    ASM SET_TAC [])

  let CHOOSE_SUBSET_EQ ← prove
   r"!n s:A->bool.
     (FINITE s ==> n <= CARD s) <=> (?t. t SUBSET s /\ t HAS_SIZE n)"
   (REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC [CHOOSE_SUBSET_STRONG] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"t:A->bool") STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
    TRANS_TAC LE_TRANS (← q r"CARD(t:A->bool)") THEN
    ASM_MESON_TAC [CARD_SUBSET, HAS_SIZE, LE_REFL])

  let CHOOSE_SUBSET ← prove
   r"!s:A->bool. FINITE s ==> !n. n <= CARD s ==> ?t. t SUBSET s /\ t HAS_SIZE n"
   (MESON_TAC [CHOOSE_SUBSET_STRONG])

  let CHOOSE_SUBSET_BETWEEN ← prove
   r"!n s u:A->bool.
        s SUBSET u /\ FINITE s /\ CARD s <= n /\ (FINITE u ==> n <= CARD u)
        ==> ?t. s SUBSET t /\ t SUBSET u /\ t HAS_SIZE n"
   (← do
    let s1 ← SET_RULE (← q r"u SUBSET (u DIFF s) UNION s")
    let t1 ← TAUT (← q r"~p ==> p ==> q")
    let a1 ← ARITH_RULE (← q r"n:num <= m ==> n - x <= m - x")
    pure
     (REPEAT STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"n - CARD(s:A->bool)", ← q r"u DIFF s:A->bool"]
            CHOOSE_SUBSET_STRONG) THEN
      ANTS_TAC THENL
       [ASM_CASES_TAC (← q r"FINITE(u:A->bool)") THEN
        ASM_SIMP_TAC [CARD_DIFF, a1] THEN
        MATCH_MP_TAC t1 THEN
        ASM_MESON_TAC [FINITE_UNION, FINITE_SUBSET, s1],
        DISCH_THEN (X_CHOOSE_THEN (← q r"t:A->bool") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q r"s UNION t:A->bool") THEN
        REPEAT (CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC]) THEN
        SUBGOAL_THEN (← q r"n:num = CARD(s) + (n - CARD(s:A->bool))") SUBST1_TAC THENL
         [ASM_ARITH_TAC,
          MATCH_MP_TAC HAS_SIZE_UNION] THEN
          ASM_REWRITE_TAC [] THEN ASM_REWRITE_TAC [HAS_SIZE] THEN ASM SET_TAC []]))

  let CARD_LE_UNIONS_CHAIN ← prove
   r"!(f:(A->bool)->bool) n.
        (!t u. t IN f /\ u IN f ==> t SUBSET u \/ u SUBSET t) /\
        (!t. t IN f ==> FINITE t /\ CARD t <= n)
        ==> FINITE(UNIONS f) /\ CARD(UNIONS f) <= n"
   (← do
    let a1 ← ARITH_RULE (← q r"~(x <= n) <=> SUC n <= x")
    let t1 ← TAUT (← q r"~(p /\ q) <=> p ==> ~q")
    pure
     (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"f:(A->bool)->bool = {}") THEN
      ASM_REWRITE_TAC [UNIONS_0, FINITE_EMPTY, CARD_CLAUSES, LE_0] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      GEN_REWRITE_TAC I [← GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC [NOT_FORALL_THM, NOT_IMP, t1] THEN
      REWRITE_TAC [a1] THEN
      REWRITE_TAC [CHOOSE_SUBSET_EQ] THEN REWRITE_TAC [RIGHT_AND_EXISTS_THM] THEN
      ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"s:A->bool") THEN
      REWRITE_TAC [HAS_SIZE] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC FINITE_SUBSET_UNIONS_CHAIN THEN
      ASM_REWRITE_TAC []))

  let CARD_LE_1 ← prove
   r"!s:A->bool. FINITE s /\ CARD s <= 1 <=> ?a. s SUBSET {a}"
   (GEN_TAC THEN REWRITE_TAC [← ARITH_RULE (← q r"c <= 1 <=> c = 0 \/ c = 1")] THEN
    REWRITE_TAC [LEFT_OR_DISTRIB, ← GSYM HAS_SIZE] THEN
    CONV_TAC (ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN SET_TAC [])

  /- Lemmas about the parity of the set of fixed points of an involution. -/

  let INVOLUTION_EVEN_NOFIXPOINTS ← prove
   r"!f (s:A->bool).
        FINITE s /\ (!x. x IN s ==> f x IN s /\ ~(f x = x) /\ f(f x) = x)
        ==> EVEN(CARD s)"
   (← do
    let a2 ← ARITH_RULE (← q r"n <= 2 <=> n = 0 \/ n = 1 \/ n = 2")
    let a1 ← ARITH_RULE (← q r"SUC n = 1 <=> n = 0")
    let t1 ← TAUT (← q r"p ==> q /\ r ==> s <=> (q /\ p) /\ r ==> s")
    pure
      (REPEAT GEN_TAC THEN ABBREV_TAC (← q r"n = CARD(s:A->bool)") THEN
       POP_ASSUM MP_TAC THEN
       REWRITE_TAC [t1] THEN
       MAP_EVERY (fun t => SPEC_TAC (t, t)) [← q r"s:A->bool", ← q r"n:num"] THEN
       MATCH_MP_TAC num_WF THEN X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN
       ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [ARITH] THEN
       MATCH_MP_TAC SET_PROVE_CASES THEN ASM_REWRITE_TAC [CARD_CLAUSES] THEN
       MAP_EVERY X_GEN_TAC [← q r"a:A", ← q r"s:A->bool"] THEN
       SIMP_TAC [FINITE_INSERT, IMP_CONJ, CARD_CLAUSES, FORALL_IN_INSERT] THEN
       REWRITE_TAC [IN_INSERT] THEN ASM_CASES_TAC (← q r"f(a:A) = a") THEN
       ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"n = 1") THEN
       ASM_SIMP_TAC [a1, CARD_EQ_0, NOT_IN_EMPTY] THEN
       REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q r"n - 2")) THEN
       ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
       DISCH_THEN (MP_TAC o SPEC (← q r"s DELETE (f:A->A) a")) THEN
       ASM_SIMP_TAC [FINITE_DELETE, CARD_DELETE, EVEN_SUB, ARITH] THEN
       ASM_REWRITE_TAC [a2] THEN
       ASM_CASES_TAC (← q r"n = 2") THEN ASM_REWRITE_TAC [ARITH] THEN
       DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
        [ASM_ARITH_TAC, ASM SET_TAC []]))

  let INVOLUTION_EVEN_FIXPOINTS ← prove
   r"!f (s:A->bool).
        FINITE s /\ (!x. x IN s ==> f x IN s /\ f(f x) = x)
        ==> (EVEN(CARD {x | x IN s /\ f x = x}) <=> EVEN(CARD s))"
   (← do
    let t1 ← TAUT (← q r"(p <=> (p <=> q)) <=> q")
    let s1 ← SET_RULE
     (← q r"{x | x IN s /\ P x} INTER {x | x IN s /\ ~P x} = {}")
    pure
     (REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS
      (← q r"EVEN(CARD({x:A | x IN s /\ f x = x} UNION {x | x IN s /\ ~(f x = x)}))") THEN
      CONJ_TAC THENL [ALL_TAC, AP_TERM_TAC THEN AP_TERM_TAC THEN SET_TAC []] THEN
      ASM_SIMP_TAC [EVEN_ADD, CARD_UNION, FINITE_RESTRICT, s1] THEN
      REWRITE_TAC [t1] THEN
      MATCH_MP_TAC INVOLUTION_EVEN_NOFIXPOINTS THEN
      EXISTS_TAC (← q r"f:A->A") THEN ASM_SIMP_TAC [FINITE_RESTRICT] THEN
      ASM SET_TAC []))


  return {
    CARD_SUBSET_EQ, CARD_SUBSET, CARD_SUBSET_LE, SUBSET_CARD_EQ,
    FINITE_CARD_LE_SUBSET, CARD_PSUBSET, CARD_PSUBSET_IMP, CARD_PSUBSET_EQ,
    CARD_UNION_LE, FINITE_CARD_LE_UNION, CARD_UNIONS_LE, CARD_UNION_GEN,
    CARD_UNION_OVERLAP_EQ, CARD_UNION_OVERLAP, CARD_IMAGE_INJ,
    HAS_SIZE_IMAGE_INJ, CARD_IMAGE_LE, FINITE_CARD_LE_IMAGE, CARD_IMAGE_INJ_EQ,
    CARD_SUBSET_IMAGE, HAS_SIZE_IMAGE_INJ_EQ, CARD_IMAGE_EQ_INJ,
    EXISTS_SMALL_SUBSET_IMAGE_INJ, FORALL_SMALL_SUBSET_IMAGE_INJ,
    EXISTS_SMALL_SUBSET_IMAGE, FORALL_SMALL_SUBSET_IMAGE, CARD_IMAGE_LE2,
    CARD_IMAGE_LT2, CHOOSE_SUBSET_STRONG, CHOOSE_SUBSET_EQ, CHOOSE_SUBSET,
    CHOOSE_SUBSET_BETWEEN, CARD_LE_UNIONS_CHAIN, CARD_LE_1,
    INVOLUTION_EVEN_NOFIXPOINTS, INVOLUTION_EVEN_FIXPOINTS }

/- ---------------------------------------------------------------------- -/
/- Cardinality of products, then the CROSS operator.  (sets.ml 2653-2924) -/
/- ---------------------------------------------------------------------- -/

/-- `parse_as_infix("CROSS",(22,"right"))` (sets.ml 2732).  Session runs it
    once, before `setupSetsCross`. -/
def setupSetsCrossInfix : IO Unit :=
  HolCore.Printer.parse_as_infix ("CROSS", (22, "right"))

/-- The cardinality-of-product theorems (sets.ml 2655-2728) and the Cartesian
    product operator `CROSS` with its algebra (sets.ml 2731-2924). -/
structure SetsCross where
  /-- `HAS_SIZE_PRODUCT_DEPENDENT` (sets.ml 2656): `s HAS_SIZE m /\
      (!x. x IN s ==> t(x) HAS_SIZE n) ==> {x,y | x IN s /\ y IN t(x)}
      HAS_SIZE (m*n)`.  `GEN_REWRITE_TAC (funpow 4 BINDER_CONV o funpow 2
      LAND_CONV) [HAS_SIZE]`, `FINITE_INDUCT_STRONG`, one width-2 `CONJ_TAC
      THENL [..;ALL_TAC]`. -/
  HAS_SIZE_PRODUCT_DEPENDENT : thm
  /-- `FINITE_PRODUCT_DEPENDENT` (sets.ml 2684): `FINITE s /\
      (!x. x IN s ==> FINITE(t x)) ==> FINITE {f x y | x IN s /\ y IN t x}`.
      `FINITE_SUBSET`, `FINITE_INDUCT_STRONG`; two width-2 `CONJ_TAC`/
      `SUBGOAL_THEN` `THENL`s. -/
  FINITE_PRODUCT_DEPENDENT : thm
  /-- `FINITE_PRODUCT` (sets.ml 2711): `SIMP_TAC[FINITE_PRODUCT_DEPENDENT]`. -/
  FINITE_PRODUCT : thm
  /-- `CARD_PRODUCT` (sets.ml 2715): `CARD {x,y | x IN s /\ y IN t} =
      CARD s * CARD t`.  `MP_TAC(SPECL [..] HAS_SIZE_PRODUCT_DEPENDENT)`. -/
  CARD_PRODUCT : thm
  /-- `HAS_SIZE_PRODUCT` (sets.ml 2723): `SIMP_TAC[HAS_SIZE; CARD_PRODUCT;
      FINITE_PRODUCT]`. -/
  HAS_SIZE_PRODUCT : thm
  /-- `CROSS` (sets.ml 2734, `new_definition`): `(s:A->bool) CROSS (t:B->bool)
      = {x,y | x IN s /\ y IN t}`.  Introduces the `CROSS` constant. -/
  CROSS : thm
  /-- `IN_CROSS` (sets.ml 2737): `(x,y) IN (s CROSS t) <=> x IN s /\ y IN t`. -/
  IN_CROSS : thm
  /-- `HAS_SIZE_CROSS` (sets.ml 2741): `REWRITE_TAC[CROSS; HAS_SIZE_PRODUCT]`. -/
  HAS_SIZE_CROSS : thm
  /-- `FINITE_CROSS` (sets.ml 2746): `SIMP_TAC[CROSS; FINITE_PRODUCT]`. -/
  FINITE_CROSS : thm
  /-- `CARD_CROSS` (sets.ml 2750): `SIMP_TAC[CROSS; CARD_PRODUCT]`. -/
  CARD_CROSS : thm
  /-- `CROSS_EQ_EMPTY` (sets.ml 2754): `s CROSS t = {} <=> s = {} \/ t = {}`. -/
  CROSS_EQ_EMPTY : thm
  /-- `CROSS_EMPTY` (sets.ml 2759): `REWRITE_TAC[CROSS_EQ_EMPTY]`. -/
  CROSS_EMPTY : thm
  /-- `CROSS_SING` (sets.ml 2763): `{x} CROSS {y} = {(x,y)}`. -/
  CROSS_SING : thm
  /-- `CROSS_UNIV` (sets.ml 2767): `(:A) CROSS (:B) = (:A#B)`. -/
  CROSS_UNIV : thm
  /-- `FINITE_CROSS_EQ` (sets.ml 2771): `FINITE(s CROSS t) <=> s = {} \/
      t = {} \/ FINITE s /\ FINITE t`.  A width-2 `THENL` picking `FST`/`SND`
      `FINITE_IMAGE`, then `MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT]
      FINITE_SUBSET)`. -/
  FINITE_CROSS_EQ : thm
  /-- `INFINITE_CROSS_EQ` (sets.ml 2786): `REWRITE_TAC[INFINITE;
      FINITE_CROSS_EQ] THEN MESON_TAC[FINITE_EMPTY]`. -/
  INFINITE_CROSS_EQ : thm
  /-- `FINITE_CROSS_UNIV` (sets.ml 2792): `FINITE(:A#B) <=> FINITE(:A) /\
      FINITE(:B)`. -/
  FINITE_CROSS_UNIV : thm
  /-- `INFINITE_CROSS_UNIV` (sets.ml 2796): `INFINITE(:A#B) <=> INFINITE(:A) \/
      INFINITE(:B)`. -/
  INFINITE_CROSS_UNIV : thm
  /-- `FINITE_UNIV_PAIR` (sets.ml 2801): `FINITE(:A#A) <=> FINITE(:A)`. -/
  FINITE_UNIV_PAIR : thm
  /-- `INFINITE_UNIV_PAIR` (sets.ml 2805): `INFINITE(:A#A) <=> INFINITE(:A)`. -/
  INFINITE_UNIV_PAIR : thm
  /-- `FORALL_IN_CROSS` (sets.ml 2809): `(!z. z IN s CROSS t ==> P z) <=>
      (!x y. x IN s /\ y IN t ==> P(x,y))`. -/
  FORALL_IN_CROSS : thm
  /-- `EXISTS_IN_CROSS` (sets.ml 2814): `(?z. z IN s CROSS t /\ P z) <=>
      (?x y. x IN s /\ y IN t /\ P(x,y))`. -/
  EXISTS_IN_CROSS : thm
  /-- `SUBSET_CROSS` (sets.ml 2819): `s CROSS t SUBSET s' CROSS t' <=>
      s = {} \/ t = {} \/ s SUBSET s' /\ t SUBSET t'`. -/
  SUBSET_CROSS : thm
  /-- `CROSS_MONO` (sets.ml 2826): `SIMP_TAC[SUBSET_CROSS]`. -/
  CROSS_MONO : thm
  /-- `CROSS_EQ` (sets.ml 2830): `s CROSS t = s' CROSS t' <=> ...`.
      `REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET_CROSS] THEN SET_TAC[]`. -/
  CROSS_EQ : thm
  /-- `IMAGE_FST_CROSS` (sets.ml 2836): `IMAGE FST (s CROSS t) =
      if t = {} then {} else s`.  `COND_CASES_TAC`, `EXISTS_IN_CROSS`. -/
  IMAGE_FST_CROSS : thm
  /-- `IMAGE_SND_CROSS` (sets.ml 2844): `IMAGE SND (s CROSS t) =
      if s = {} then {} else t`. -/
  IMAGE_SND_CROSS : thm
  /-- `IMAGE_PAIRED_CROSS` (sets.ml 2852): `IMAGE (\(x,y). f x,g y) (s CROSS t)
      = (IMAGE f s) CROSS (IMAGE g t)`. -/
  IMAGE_PAIRED_CROSS : thm
  /-- `CROSS_INTER` (sets.ml 2859): distributivity of `CROSS` over `INTER`
      (both sides).  `REPEAT STRIP_TAC THEN CONV_TAC TAUT`. -/
  CROSS_INTER : thm
  /-- `CROSS_UNION` (sets.ml 2867): distributivity over `UNION` (both
      sides). -/
  CROSS_UNION : thm
  /-- `CROSS_DIFF` (sets.ml 2875): distributivity over `DIFF` (both sides). -/
  CROSS_DIFF : thm
  /-- `INTER_CROSS` (sets.ml 2883): `(s CROSS t) INTER (s' CROSS t') =
      (s INTER s') CROSS (t INTER t')`. -/
  INTER_CROSS : thm
  /-- `CROSS_UNIONS_UNIONS` (sets.ml 2889, `fst` of `CONJ_PAIR o prove`):
      `(UNIONS f) CROSS (UNIONS g) = UNIONS {s CROSS t | s IN f /\ t IN g}`. -/
  CROSS_UNIONS_UNIONS : thm
  /-- `CROSS_UNIONS` (sets.ml 2889, `snd` of `CONJ_PAIR o prove`): the two
      single-`UNIONS` distributivities of `CROSS` over `UNIONS`. -/
  CROSS_UNIONS : thm
  /-- `CROSS_INTERS_INTERS` (sets.ml 2901, `fst` of `CONJ_PAIR o prove`):
      `(INTERS f) CROSS (INTERS g) = ...` (with the empty-family guards). -/
  CROSS_INTERS_INTERS : thm
  /-- `CROSS_INTERS` (sets.ml 2901, `snd` of `CONJ_PAIR o prove`): the two
      single-`INTERS` distributivities of `CROSS` over `INTERS`. -/
  CROSS_INTERS : thm
  /-- `DISJOINT_CROSS` (sets.ml 2918): `DISJOINT (s CROSS t) (s' CROSS t') <=>
      DISJOINT s s' \/ DISJOINT t t'`. -/
  DISJOINT_CROSS : thm
  deriving Inhabited

@[nospecialize]
def setupSetsCross [HolBase] (S : SetsCore)
    (P : SetsProps) (SIn : SetsInclusion)
    (SImg : SetsImage) (SMi : SetsMisc) (SFin : SetsFinite)
    (SInd : SetsInduct)
    (SCard : SetsCard) (SCard2 : SetsCard2) (Pr : HolMath.Pair.PairThms)
    (MESON_TAC : List thm → tactic) (ASM_MESON_TAC : List thm → tactic)
    (new_definition' : term → IO (Except String thm))
    (MULT_CLAUSES : thm) :
    ExceptT String IO SetsCross := do
  let SET_TAC := SET_TAC S P MESON_TAC
  let SET_RULE := SET_RULE S P MESON_TAC
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let { EXTENSION, IN_ELIM_THM, SUBSET, DISJOINT, FINITE_RULES, INFINITE, .. } := S
  let { NOT_IN_EMPTY, IN_UNIV, IN_UNION, IN_INTER, IN_DIFF, IN_INSERT, IN_SING,
        IN_IMAGE, FORALL_IN_GSPEC, UNIONS_GSPEC, INTERS_GSPEC, .. } := P
  let { UNIV_NOT_EMPTY, SUBSET_ANTISYM_EQ, .. } := SIn
  let { IMAGE_CLAUSES, .. } := SImg
  let { IN_ELIM_PAIR_THM, .. } := SMi
  let { FINITE_EMPTY, FINITE_SUBSET, FINITE_UNION, FINITE_IMAGE, .. } := SFin
  let { FINITE_INDUCT_STRONG, .. } := SInd
  let { CARD_CLAUSES, HAS_SIZE, HAS_SIZE_0, HAS_SIZE_UNION, .. } := SCard
  let { HAS_SIZE_IMAGE_INJ, .. } := SCard2
  let { PAIR_EQ, FST, SND, FORALL_PAIR_THM, EXISTS_PAIR_THM, .. } := Pr
  let { CONJ_ASSOC, CONJ_SYM, IMP_CONJ, IMP_CONJ_ALT, EXISTS_REFL,
        FORALL_AND_THM, RIGHT_FORALL_IMP_THM, LEFT_FORALL_IMP_THM, .. } := HolBase.T

  /- Cardinality of product. -/

  let HAS_SIZE_PRODUCT_DEPENDENT ← prove
   r"!s m t n.
         s HAS_SIZE m /\ (!x. x IN s ==> t(x) HAS_SIZE n)
         ==> {(x:A,y:B) | x IN s /\ y IN t(x)} HAS_SIZE (m * n)"
   (← do
    let s1 ← SET_RULE
      (← q r"{(x,y) | (x = a \/ x IN s) /\ y IN t(x)} =
       {(x,y) | x IN s /\ y IN t(x)} UNION
       IMAGE (\y. (a,y)) (t a)")
    let t1 ← TAUT (← q r"a \/ b ==> c <=> (a ==> c) /\ (b ==> c)")
    pure
      (GEN_REWRITE_TAC (funpow 4 BINDER_CONV o funpow 2 LAND_CONV) [HAS_SIZE] THEN
       REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
       MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
       SIMP_TAC [CARD_CLAUSES, NOT_IN_EMPTY, IN_INSERT] THEN CONJ_TAC THENL
        [GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
         REWRITE_TAC [MULT_CLAUSES, HAS_SIZE_0] THEN SET_TAC [],
         ALL_TAC] THEN
       MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"s:A->bool"] THEN STRIP_TAC THEN
       X_GEN_TAC (← q r"m:num") THEN DISCH_THEN (ASSUME_TAC o SYM) THEN
       MAP_EVERY X_GEN_TAC [← q r"t:A->B->bool", ← q r"n:num"] THEN
       REWRITE_TAC [t1] THEN
       SIMP_TAC [FORALL_AND_THM, LEFT_FORALL_IMP_THM, EXISTS_REFL] THEN
       STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q r"CARD(s:A->bool)")) THEN
       ASM_REWRITE_TAC [MULT_CLAUSES] THEN DISCH_TAC THEN
       REWRITE_TAC [s1] THEN
       MATCH_MP_TAC HAS_SIZE_UNION THEN
       ASM_SIMP_TAC [HAS_SIZE_IMAGE_INJ, PAIR_EQ] THEN
       REWRITE_TAC [DISJOINT, IN_IMAGE, IN_ELIM_THM, IN_INTER, EXTENSION,
                    NOT_IN_EMPTY, EXISTS_PAIR_THM, PAIR_EQ] THEN
       REPEAT STRIP_TAC THEN ASM_MESON_TAC [PAIR_EQ]))

  let FINITE_PRODUCT_DEPENDENT ← prove
   r"!f:A->B->C s t.
        FINITE s /\ (!x. x IN s ==> FINITE(t x))
        ==> FINITE {f x y | x IN s /\ y IN (t x)}"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC (← q r"IMAGE (\(x,y). (f:A->B->C) x y) {x,y | x IN s /\ y IN t x}") THEN
    REWRITE_TAC [SUBSET, IN_IMAGE, EXISTS_PAIR_THM, IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC [FORALL_IN_GSPEC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC FINITE_IMAGE, MESON_TAC []] THEN
    MAP_EVERY UNDISCH_TAC
     [← q r"!x:A. x IN s ==> FINITE(t x :B->bool)", ← q r"FINITE(s:A->bool)"] THEN
    MAP_EVERY (fun t => SPEC_TAC (t, t)) [← q r"t:A->B->bool", ← q r"s:A->bool"] THEN
    REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
     [GEN_TAC THEN SUBGOAL_THEN (← q r"{(x:A,y:B) | x IN {} /\ y IN (t x)} = {}")
       (fun th => REWRITE_TAC [th, FINITE_RULES]) THEN
      REWRITE_TAC [EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY],
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:A", ← q r"s:A->bool"] THEN STRIP_TAC THEN
    X_GEN_TAC (← q r"t:A->B->bool") THEN
    SUBGOAL_THEN
     (← q r"{(x:A,y:B) | x IN (a INSERT s) /\ y IN (t x)} =
      IMAGE (\y. a,y) (t a) UNION {(x,y) | x IN s /\ y IN (t x)}")
     (fun th => ASM_SIMP_TAC [IN_INSERT, FINITE_IMAGE, FINITE_UNION, th]) THEN
    REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM, IN_INSERT, IN_UNION] THEN
    MESON_TAC [])

  let FINITE_PRODUCT ← prove
   r"!s t. FINITE s /\ FINITE t ==> FINITE {(x:A,y:B) | x IN s /\ y IN t}"
   (SIMP_TAC [FINITE_PRODUCT_DEPENDENT])

  let CARD_PRODUCT ← prove
   r"!s t. FINITE s /\ FINITE t
         ==> (CARD {(x:A,y:B) | x IN s /\ y IN t} = CARD s * CARD t)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"s:A->bool", ← q r"CARD(s:A->bool)", ← q r"\x:A. t:B->bool",
                     ← q r"CARD(t:B->bool)"] HAS_SIZE_PRODUCT_DEPENDENT) THEN
    ASM_SIMP_TAC [HAS_SIZE])

  let HAS_SIZE_PRODUCT ← prove
   r"!s m t n. s HAS_SIZE m /\ t HAS_SIZE n
             ==> {(x:A,y:B) | x IN s /\ y IN t} HAS_SIZE (m * n)"
   (SIMP_TAC [HAS_SIZE, CARD_PRODUCT, FINITE_PRODUCT])

  /- Actually introduce a Cartesian product operation. -/

  let CROSS ← new_definition
   r"(s:A->bool) CROSS (t:B->bool) = {x,y | x IN s /\ y IN t}"

  let IN_CROSS ← prove
   r"!(x:A) (y:B) s t. (x,y) IN (s CROSS t) <=> x IN s /\ y IN t"
   (REWRITE_TAC [CROSS, IN_ELIM_PAIR_THM])

  let HAS_SIZE_CROSS ← prove
   r"!(s:A->bool) (t:B->bool) m n.
        s HAS_SIZE m /\ t HAS_SIZE n ==> (s CROSS t) HAS_SIZE (m * n)"
   (REWRITE_TAC [CROSS, HAS_SIZE_PRODUCT])

  let FINITE_CROSS ← prove
   r"!(s:A->bool) (t:B->bool). FINITE s /\ FINITE t ==> FINITE(s CROSS t)"
   (SIMP_TAC [CROSS, FINITE_PRODUCT])

  let CARD_CROSS ← prove
   r"!(s:A->bool) (t:B->bool). FINITE s /\ FINITE t ==> CARD(s CROSS t) = CARD s * CARD t"
   (SIMP_TAC [CROSS, CARD_PRODUCT])

  let CROSS_EQ_EMPTY ← prove
   r"!(s:A->bool) (t:B->bool). s CROSS t = {} <=> s = {} \/ t = {}"
   (REWRITE_TAC [EXTENSION, FORALL_PAIR_THM, IN_CROSS, NOT_IN_EMPTY] THEN
    MESON_TAC [])

  let CROSS_EMPTY ← prove
   r"(!s:A->bool. s CROSS {} = {}) /\ (!t:B->bool. {} CROSS t = {})"
   (REWRITE_TAC [CROSS_EQ_EMPTY])

  let CROSS_SING ← prove
   r"!x:A y:B. {x} CROSS {y} = {(x,y)}"
   (REWRITE_TAC [EXTENSION, FORALL_PAIR_THM, IN_SING, IN_CROSS, PAIR_EQ])

  let CROSS_UNIV ← prove
   r"(:A) CROSS (:B) = (:A#B)"
   (REWRITE_TAC [CROSS, EXTENSION, IN_ELIM_PAIR_THM, FORALL_PAIR_THM, IN_UNIV])

  let FINITE_CROSS_EQ ← prove
   r"!s:A->bool t:B->bool.
        FINITE(s CROSS t) <=> s = {} \/ t = {} \/ FINITE s /\ FINITE t"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"s:A->bool = {}") THEN
    ASM_REWRITE_TAC [CROSS_EMPTY, FINITE_EMPTY] THEN
    ASM_CASES_TAC (← q r"t:B->bool = {}") THEN
    ASM_REWRITE_TAC [CROSS_EMPTY, FINITE_EMPTY] THEN
    EQ_TAC THEN REWRITE_TAC [FINITE_CROSS] THEN REPEAT STRIP_TAC THENL
     [FIRST_ASSUM (MP_TAC o MATCH_MP (← ISPEC (← q r"FST:A#B->A") FINITE_IMAGE)),
      FIRST_ASSUM (MP_TAC o MATCH_MP (← ISPEC (← q r"SND:A#B->B") FINITE_IMAGE))] THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] FINITE_SUBSET) THEN
    REWRITE_TAC [SUBSET, IN_IMAGE, EXISTS_PAIR_THM, IN_CROSS] THEN
    ASM SET_TAC [])

  let INFINITE_CROSS_EQ ← prove
   r"!(s:A->bool) (t:B->bool).
        INFINITE(s CROSS t) <=>
        ~(s = {}) /\ INFINITE t \/ INFINITE s /\ ~(t = {})"
   (REWRITE_TAC [INFINITE, FINITE_CROSS_EQ] THEN MESON_TAC [FINITE_EMPTY])

  let FINITE_CROSS_UNIV ← prove
   r"FINITE(:A#B) <=> FINITE(:A) /\ FINITE(:B)"
   (REWRITE_TAC [← GSYM CROSS_UNIV, FINITE_CROSS_EQ, UNIV_NOT_EMPTY])

  let INFINITE_CROSS_UNIV ← prove
   r"INFINITE(:A#B) <=> INFINITE(:A) \/ INFINITE(:B)"
   (REWRITE_TAC [← GSYM CROSS_UNIV, INFINITE_CROSS_EQ, UNIV_NOT_EMPTY] THEN
    MESON_TAC [])

  let FINITE_UNIV_PAIR ← prove
   r"FINITE(:A#A) <=> FINITE(:A)"
   (REWRITE_TAC [FINITE_CROSS_UNIV])

  let INFINITE_UNIV_PAIR ← prove
   r"INFINITE(:A#A) <=> INFINITE(:A)"
   (REWRITE_TAC [INFINITE_CROSS_UNIV])

  let FORALL_IN_CROSS ← prove
   r"!P s t. (!z:A#B. z IN s CROSS t ==> P z) <=>
           (!x y. x IN s /\ y IN t ==> P(x,y))"
   (REWRITE_TAC [FORALL_PAIR_THM, IN_CROSS])

  let EXISTS_IN_CROSS ← prove
   r"!P s t. (?z:A#B. z IN s CROSS t /\ P z) <=>
           (?x y. x IN s /\ y IN t /\ P(x,y))"
   (REWRITE_TAC [EXISTS_PAIR_THM, ← GSYM CONJ_ASSOC, IN_CROSS])

  let SUBSET_CROSS ← prove
   r"!(s:A->bool) (t:B->bool) s' t'.
        s CROSS t SUBSET s' CROSS t' <=>
        s = {} \/ t = {} \/ s SUBSET s' /\ t SUBSET t'"
   (SIMP_TAC [CROSS, EXTENSION, IN_ELIM_PAIR_THM, SUBSET,
     FORALL_PAIR_THM, IN_CROSS, NOT_IN_EMPTY] THEN MESON_TAC [])

  let CROSS_MONO ← prove
   r"!(s:A->bool) (t:B->bool) s' t'. s SUBSET s' /\ t SUBSET t' ==> s CROSS t SUBSET s' CROSS t'"
   (SIMP_TAC [SUBSET_CROSS])

  let CROSS_EQ ← prove
   r"!s s':A->bool t t':B->bool.
        s CROSS t = s' CROSS t' <=>
        (s = {} \/ t = {}) /\ (s' = {} \/ t' = {}) \/ s = s' /\ t = t'"
   (REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ, SUBSET_CROSS] THEN SET_TAC [])

  let IMAGE_FST_CROSS ← prove
   r"!s:A->bool t:B->bool.
        IMAGE FST (s CROSS t) = if t = {} then {} else s"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [CROSS_EMPTY, IMAGE_CLAUSES] THEN
    REWRITE_TAC [EXTENSION, IN_IMAGE] THEN ONCE_REWRITE_TAC [CONJ_SYM] THEN
    REWRITE_TAC [EXISTS_IN_CROSS, FST] THEN ASM SET_TAC [])

  let IMAGE_SND_CROSS ← prove
   r"!s:A->bool t:B->bool.
        IMAGE SND (s CROSS t) = if s = {} then {} else t"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [CROSS_EMPTY, IMAGE_CLAUSES] THEN
    REWRITE_TAC [EXTENSION, IN_IMAGE] THEN ONCE_REWRITE_TAC [CONJ_SYM] THEN
    REWRITE_TAC [EXISTS_IN_CROSS, SND] THEN ASM SET_TAC [])

  let IMAGE_PAIRED_CROSS ← prove
   r"!(f:A->B) (g:C->D) s t.
         IMAGE (\(x,y). f x,g y) (s CROSS t) = (IMAGE f s) CROSS (IMAGE g t)"
   (REWRITE_TAC [EXTENSION, IN_IMAGE, EXISTS_PAIR_THM, IN_CROSS, FORALL_PAIR_THM,
                 PAIR_EQ] THEN
    MESON_TAC [])

  let CROSS_INTER ← prove
   r"(!(s:A->bool) (t:B->bool) u.
        s CROSS (t INTER u) = (s CROSS t) INTER (s CROSS u)) /\
   (!(s:A->bool) t (u:B->bool).
        (s INTER t) CROSS u = (s CROSS u) INTER (t CROSS u))"
   (REWRITE_TAC [EXTENSION, FORALL_PAIR_THM, IN_INTER, IN_CROSS] THEN
    REPEAT STRIP_TAC THEN CONV_TAC (fun t => (TAUT t).run))

  let CROSS_UNION ← prove
   r"(!(s:A->bool) (t:B->bool) u.
        s CROSS (t UNION u) = (s CROSS t) UNION (s CROSS u)) /\
   (!(s:A->bool) t (u:B->bool).
        (s UNION t) CROSS u = (s CROSS u) UNION (t CROSS u))"
   (REWRITE_TAC [EXTENSION, FORALL_PAIR_THM, IN_UNION, IN_CROSS] THEN
    REPEAT STRIP_TAC THEN CONV_TAC (fun t => (TAUT t).run))

  let CROSS_DIFF ← prove
   r"(!(s:A->bool) (t:B->bool) u.
        s CROSS (t DIFF u) = (s CROSS t) DIFF (s CROSS u)) /\
   (!(s:A->bool) t (u:B->bool).
        (s DIFF t) CROSS u = (s CROSS u) DIFF (t CROSS u))"
   (REWRITE_TAC [EXTENSION, FORALL_PAIR_THM, IN_DIFF, IN_CROSS] THEN
    REPEAT STRIP_TAC THEN CONV_TAC (fun t => (TAUT t).run))

  let INTER_CROSS ← prove
   r"!(s:A->bool) s' (t:B->bool) t'.
      (s CROSS t) INTER (s' CROSS t') = (s INTER s') CROSS (t INTER t')"
   (REWRITE_TAC [EXTENSION, IN_INTER, FORALL_PAIR_THM, IN_CROSS] THEN
    CONV_TAC (fun t => (TAUT t).run))

  let (CROSS_UNIONS_UNIONS, CROSS_UNIONS) ← CONJ_PAIR (← prove
   r"(!(f:(A->bool)->bool) (g:(B->bool)->bool).
        (UNIONS f) CROSS (UNIONS g) =
        UNIONS {s CROSS t | s IN f /\ t IN g}) /\
   (!(s:A->bool) (f:(A->bool)->bool).
        s CROSS (UNIONS f) = UNIONS {s CROSS t | t IN f}) /\
   (!(f:(A->bool)->bool) (t:B->bool).
        (UNIONS f) CROSS t = UNIONS {s CROSS t | s IN f})"
   (REWRITE_TAC [UNIONS_GSPEC, EXTENSION, FORALL_PAIR_THM, IN_ELIM_THM,
                 IN_CROSS] THEN
    SET_TAC []))

  let (CROSS_INTERS_INTERS, CROSS_INTERS) ← CONJ_PAIR (← prove
   r"(!(f:(A->bool)->bool) (g:(B->bool)->bool).
        (INTERS f) CROSS (INTERS g) =
        if f = {} then INTERS {UNIV CROSS t | t IN g}
        else if g = {} then INTERS {s CROSS UNIV | s IN f}
        else INTERS {s CROSS t | s IN f /\ t IN g}) /\
   (!(s:A->bool) (f:(A->bool)->bool).
        s CROSS (INTERS f) =
        if f = {} then s CROSS UNIV else INTERS {s CROSS t | t IN f}) /\
   (!(f:(A->bool)->bool) (t:B->bool).
        (INTERS f) CROSS t =
        if f = {} then UNIV CROSS t else INTERS {s CROSS t | s IN f})"
   (REPEAT STRIP_TAC THEN REPEAT (COND_CASES_TAC THEN REWRITE_TAC []) THEN
    ASM_REWRITE_TAC [INTERS_GSPEC, EXTENSION, FORALL_PAIR_THM, IN_ELIM_THM,
                     IN_CROSS, NOT_IN_EMPTY] THEN
    ASM SET_TAC []))

  let DISJOINT_CROSS ← prove
   r"!s:A->bool t:B->bool s' t'.
        DISJOINT (s CROSS t) (s' CROSS t') <=>
        DISJOINT s s' \/ DISJOINT t t'"
   (REWRITE_TAC [DISJOINT, INTER_CROSS, CROSS_EQ_EMPTY])

  return {
    HAS_SIZE_PRODUCT_DEPENDENT, FINITE_PRODUCT_DEPENDENT, FINITE_PRODUCT,
    CARD_PRODUCT, HAS_SIZE_PRODUCT, CROSS, IN_CROSS, HAS_SIZE_CROSS,
    FINITE_CROSS, CARD_CROSS, CROSS_EQ_EMPTY, CROSS_EMPTY, CROSS_SING,
    CROSS_UNIV, FINITE_CROSS_EQ, INFINITE_CROSS_EQ, FINITE_CROSS_UNIV,
    INFINITE_CROSS_UNIV, FINITE_UNIV_PAIR, INFINITE_UNIV_PAIR, FORALL_IN_CROSS,
    EXISTS_IN_CROSS, SUBSET_CROSS, CROSS_MONO, CROSS_EQ, IMAGE_FST_CROSS,
    IMAGE_SND_CROSS, IMAGE_PAIRED_CROSS, CROSS_INTER, CROSS_UNION, CROSS_DIFF,
    INTER_CROSS, CROSS_UNIONS_UNIONS, CROSS_UNIONS, CROSS_INTERS_INTERS,
    CROSS_INTERS, DISJOINT_CROSS }

/- ---------------------------------------------------------------------- -/
/- Extensional functions, restriction, and the dependent function space.   -/
/- (sets.ml 2925-3324)                                                    -/
/- ---------------------------------------------------------------------- -/

/-- Extensional functions (fixed to `ARB` off the domain), restriction of a
    function to an extensional one, the general Cartesian product / dependent
    function space, the product of a family of maps, and the disjoint-union
    construction (sets.ml 2925-3324).  Depends on the core Sets bundles plus
    `Pr` (`PairThms`, for `FORALL_PAIR_THM`/`PAIR_EQ`), `T` (`LEFT_IMP_EXISTS_THM`),
    `Tr` (`o_THM`), the injected combinator definition `o_DEF`, `C.SKOLEM_THM`,
    and the MESON/`new_definition` helpers. -/
structure SetsFunspace where
  /-- `ARB` (sets.ml 2929, `new_definition`): `ARB = (@x:A. F)`, the fixed
      "undefined" value used off an extensional function's domain. -/
  ARB : thm
  /-- `EXTENSIONAL` (sets.ml 2931, `new_definition`): `EXTENSIONAL s =
      {f | !x. ~(x IN s) ==> f x = ARB}`. -/
  EXTENSIONAL : thm
  /-- `IN_EXTENSIONAL` (sets.ml 2936): `REWRITE_TAC[EXTENSIONAL; IN_ELIM_THM]`. -/
  IN_EXTENSIONAL : thm
  /-- `IN_EXTENSIONAL_UNDEFINED` (sets.ml 2940): `SIMP_TAC[IN_EXTENSIONAL]`. -/
  IN_EXTENSIONAL_UNDEFINED : thm
  /-- `EXTENSIONAL_EMPTY` (sets.ml 2944): two `REWRITE_TAC`s, no `THENL`. -/
  EXTENSIONAL_EMPTY : thm
  /-- `EXTENSIONAL_UNIV` (sets.ml 2949): `REWRITE_TAC[EXTENSIONAL; IN_UNIV;
      IN_ELIM_THM]`. -/
  EXTENSIONAL_UNIV : thm
  /-- `EXTENSIONAL_EQ` (sets.ml 2953): extensional functions agreeing on the
      domain are equal.  ONE width-2 `ASM_CASES_TAC THENL
      [ASM_SIMP_TAC[]; ASM_MESON_TAC[IN_EXTENSIONAL_UNDEFINED]]`. -/
  EXTENSIONAL_EQ : thm
  /-- `RESTRICTION` (sets.ml 2967, `new_definition`): `RESTRICTION s f x =
      if x IN s then f x else ARB`. -/
  RESTRICTION : thm
  /-- `RESTRICTION_THM` (sets.ml 2968): `REWRITE_TAC[FUN_EQ_THM; RESTRICTION]`. -/
  RESTRICTION_THM : thm
  /-- `RESTRICTION_DEFINED` (sets.ml 2972): `SIMP_TAC[RESTRICTION]`. -/
  RESTRICTION_DEFINED : thm
  /-- `RESTRICTION_UNDEFINED` (sets.ml 2976): `SIMP_TAC[RESTRICTION]`. -/
  RESTRICTION_UNDEFINED : thm
  /-- `RESTRICTION_EQ` (sets.ml 2980): `SIMP_TAC[RESTRICTION_DEFINED]`. -/
  RESTRICTION_EQ : thm
  /-- `RESTRICTION_IN_EXTENSIONAL` (sets.ml 2984): `SIMP_TAC[IN_EXTENSIONAL;
      RESTRICTION]`. -/
  RESTRICTION_IN_EXTENSIONAL : thm
  /-- `RESTRICTION_EXTENSION` (sets.ml 2988): `REWRITE_TAC[RESTRICTION;
      FUN_EQ_THM] THEN MESON_TAC[]`. -/
  RESTRICTION_EXTENSION : thm
  /-- `RESTRICTION_FIXPOINT` (sets.ml 2993): `REWRITE_TAC[IN_EXTENSIONAL;
      FUN_EQ_THM; RESTRICTION] THEN MESON_TAC[]`. -/
  RESTRICTION_FIXPOINT : thm
  /-- `RESTRICTION_UNIV` (sets.ml 2997): `REWRITE_TAC[FUN_EQ_THM; RESTRICTION;
      IN_UNIV]`. -/
  RESTRICTION_UNIV : thm
  /-- `RESTRICTION_RESTRICTION` (sets.ml 3001): `REWRITE_TAC[FUN_EQ_THM;
      RESTRICTION] THEN SET_TAC[]`. -/
  RESTRICTION_RESTRICTION : thm
  /-- `RESTRICTION_IDEMP` (sets.ml 3006): `REWRITE_TAC[RESTRICTION_FIXPOINT;
      RESTRICTION_IN_EXTENSIONAL]`. -/
  RESTRICTION_IDEMP : thm
  /-- `IMAGE_RESTRICTION` (sets.ml 3010): `REWRITE_TAC[EXTENSION; IN_IMAGE;
      RESTRICTION] THEN SET_TAC[]`. -/
  IMAGE_RESTRICTION : thm
  /-- `RESTRICTION_COMPOSE_RIGHT` (sets.ml 3014): `REWRITE_TAC[FUN_EQ_THM;
      o_DEF; RESTRICTION] THEN SIMP_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      SET_TAC[]`.  `o` inside `o_DEF` REWRITE only. -/
  RESTRICTION_COMPOSE_RIGHT : thm
  /-- `RESTRICTION_COMPOSE_LEFT` (sets.ml 3021): same shape as
      `RESTRICTION_COMPOSE_RIGHT`. -/
  RESTRICTION_COMPOSE_LEFT : thm
  /-- `RESTRICTION_COMPOSE` (sets.ml 3029): `SIMP_TAC[RESTRICTION_COMPOSE_LEFT;
      RESTRICTION_COMPOSE_RIGHT]`. -/
  RESTRICTION_COMPOSE : thm
  /-- `RESTRICTION_UNIQUE` (sets.ml 3036): `REWRITE_TAC[FUN_EQ_THM; RESTRICTION;
      EXTENSIONAL; IN_ELIM_THM] THEN MESON_TAC[]`. -/
  RESTRICTION_UNIQUE : thm
  /-- `RESTRICTION_UNIQUE_ALT` (sets.ml 3042): same shape as
      `RESTRICTION_UNIQUE`. -/
  RESTRICTION_UNIQUE_ALT : thm
  /-- `cartesian_product` (sets.ml 3055, `new_definition`): the dependent
      function space `{f | EXTENSIONAL k f /\ !i. i IN k ==> f i IN s i}`. -/
  cartesian_product : thm
  /-- `IN_CARTESIAN_PRODUCT` (sets.ml 3056): `REWRITE_TAC[cartesian_product;
      IN_ELIM_THM]`. -/
  IN_CARTESIAN_PRODUCT : thm
  /-- `CARTESIAN_PRODUCT` (sets.ml 3062): the "conditional membership" form.
      `GEN_REWRITE_TAC I [EXTENSION]`, `REWRITE_TAC`, `MESON_TAC[IN_SING]`.
      No top-level `THENL`.  `I` = id (ZERO). -/
  CARTESIAN_PRODUCT : thm
  /-- `RESTRICTION_IN_CARTESIAN_PRODUCT` (sets.ml 3069): `REWRITE_TAC[...] THEN
      SET_TAC[]`. -/
  RESTRICTION_IN_CARTESIAN_PRODUCT : thm
  /-- `CARTESIAN_PRODUCT_AS_RESTRICTIONS` (sets.ml 3076): the product as a set
      of restrictions.  `GSYM SUBSET_ANTISYM_EQ`, `FORALL_IN_GSPEC`, `X_GEN_TAC`,
      `EXISTS_TAC`, `ASM_MESON_TAC`.  No top-level `THENL`. -/
  CARTESIAN_PRODUCT_AS_RESTRICTIONS : thm
  /-- `CARTESIAN_PRODUCT_EQ_EMPTY` (sets.ml 3088): empty iff some fibre is empty.
      `GEN_REWRITE_TAC LAND_CONV [EXTENSION]`, a `SET_RULE` rewrite, `SKOLEM_THM`,
      `EQ_TAC THEN DISCH_TAC` (a common tail applied to BOTH branches, so the
      `EQ_TAC` split has NO `THENL`), `FIRST_X_ASSUM(MP_TAC o SPEC ...)`. -/
  CARTESIAN_PRODUCT_EQ_EMPTY : thm
  /-- `CARTESIAN_PRODUCT_EMPTY` (sets.ml 3100): `cartesian_product {} s =
      {(\i. ARB)}`.  Three `REWRITE_TAC`s, no `THENL`. -/
  CARTESIAN_PRODUCT_EMPTY : thm
  /-- `CARTESIAN_PRODUCT_EQ_MEMBERS` (sets.ml 3105): members agreeing on `k`
      are equal.  `MATCH_MP_TAC EXTENSIONAL_EQ`, `EXISTS_TAC`, `[IN]` rewrite.
      No top-level `THENL`. -/
  CARTESIAN_PRODUCT_EQ_MEMBERS : thm
  /-- `CARTESIAN_PRODUCT_EQ_MEMBERS_EQ` (sets.ml 3114):
      `MESON[CARTESIAN_PRODUCT_EQ_MEMBERS]`. -/
  CARTESIAN_PRODUCT_EQ_MEMBERS_EQ : thm
  /-- `SUBSET_CARTESIAN_PRODUCT` (sets.ml 3121): a subset characterisation.
      ONE width-2 top-level `EQ_TAC THENL [ALL_TAC; MESON_TAC[]]`, then a
      `FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [...])`, a `SET_RULE`
      rewrite and `SKOLEM_THM`.  `RAND_CONV` = one level. -/
  SUBSET_CARTESIAN_PRODUCT : thm
  /-- `CARTESIAN_PRODUCT_EQ` (sets.ml 3141): equality of two products.  ONE
      width-2 top-level `ASM_REWRITE_TAC[] THENL [ASM_SIMP_TAC[...]; ...]`, the
      second branch a chain ending in `ASM SET_TAC[]`. -/
  CARTESIAN_PRODUCT_EQ : thm
  /-- `INTER_CARTESIAN_PRODUCT` (sets.ml 3157): `REWRITE_TAC[...] THEN
      SET_TAC[]`. -/
  INTER_CARTESIAN_PRODUCT : thm
  /-- `CARTESIAN_PRODUCT_UNIV` (sets.ml 3164): two `REWRITE_TAC`s, no `THENL`. -/
  CARTESIAN_PRODUCT_UNIV : thm
  /-- `CARTESIAN_PRODUCT_SINGS` (sets.ml 3169): `REWRITE_TAC`s then `MESON_TAC[]`.
      No `THENL`. -/
  CARTESIAN_PRODUCT_SINGS : thm
  /-- `CARTESIAN_PRODUCT_SINGS_GEN` (sets.ml 3175): `REWRITE_TAC`s then
      `MESON_TAC[]`.  No `THENL`. -/
  CARTESIAN_PRODUCT_SINGS_GEN : thm
  /-- `IMAGE_PROJECTION_CARTESIAN_PRODUCT` (sets.ml 3181): the image of a
      coordinate projection.  `ASM_CASES_TAC`, `GSYM SUBSET_ANTISYM_EQ`,
      `FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [...])`, `SET_RULE`,
      `SKOLEM_THM`, `EXISTS_TAC`, `ASM_MESON_TAC[IN_SING]`.  No top-level
      `THENL` (the `ASM_CASES_TAC` split shares a common tail). -/
  IMAGE_PROJECTION_CARTESIAN_PRODUCT : thm
  /-- `FORALL_CARTESIAN_PRODUCT_ELEMENTS` (sets.ml 3202): a `!`-over-elements
      characterisation.  ONE width-2 top-level `EQ_TAC THENL [DISCH_TAC;
      MESON_TAC[]]`, then `SET_RULE`/`SKOLEM_THM` and a
      `FIRST_X_ASSUM(MP_TAC o SPECL [..])`. -/
  FORALL_CARTESIAN_PRODUCT_ELEMENTS : thm
  /-- `FORALL_CARTESIAN_PRODUCT_ELEMENTS_EQ` (sets.ml 3222):
      `SIMP_TAC[FORALL_CARTESIAN_PRODUCT_ELEMENTS]`. -/
  FORALL_CARTESIAN_PRODUCT_ELEMENTS_EQ : thm
  /-- `EXISTS_CARTESIAN_PRODUCT_ELEMENT` (sets.ml 3229):
      `REWRITE_TAC[CARTESIAN_PRODUCT_AS_RESTRICTIONS; EXISTS_IN_GSPEC] THEN
      SIMP_TAC[RESTRICTION] THEN MESON_TAC[]`. -/
  EXISTS_CARTESIAN_PRODUCT_ELEMENT : thm
  /-- `product_map` (sets.ml 3242, `new_definition`): `product_map k f =
      \x. RESTRICTION k (\i. f i (x i))`. -/
  product_map : thm
  /-- `PRODUCT_MAP_RESTRICTION` (sets.ml 3244): `SIMP_TAC[product_map;
      RESTRICTION; o_THM; FUN_EQ_THM]`. -/
  PRODUCT_MAP_RESTRICTION : thm
  /-- `IMAGE_PRODUCT_MAP` (sets.ml 3249): image of a product map is the product
      of the images.  `CARTESIAN_PRODUCT_AS_RESTRICTIONS`,
      `ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN]`, `GSYM IMAGE_o`,
      `GEN_REWRITE_TAC I [EXTENSION]`, `X_GEN_TAC`, `EQ_TAC THEN STRIP_TAC`
      (common tail, so NO top-level `THENL`), then `ASM SET_TAC[]`.  `I` = id
      (ZERO). -/
  IMAGE_PRODUCT_MAP : thm
  /-- `disjoint_union` (sets.ml 3267, `new_definition`): `disjoint_union k s =
      {(i,x) | i IN k /\ x IN s i}`. -/
  disjoint_union : thm
  /-- `SUBSET_DISJOINT_UNION` (sets.ml 3269): `REWRITE_TAC[SUBSET;
      disjoint_union; FORALL_IN_GSPEC] THEN REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
      SET_TAC[]`. -/
  SUBSET_DISJOINT_UNION : thm
  /-- `DISJOINT_UNION_EQ` (sets.ml 3276): `REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ;
      SUBSET_DISJOINT_UNION] THEN SET_TAC[]`. -/
  DISJOINT_UNION_EQ : thm
  /-- `SUBSET_DISJOINT_UNION_EXISTS` (sets.ml 3283): a subset of a disjoint
      union is itself a disjoint union.  ONE width-2 top-level `EQ_TAC THENL
      [DISCH_TAC; MESON_TAC[SUBSET_DISJOINT_UNION]]`, then `EXISTS_TAC`,
      `POP_ASSUM MP_TAC`, `SET_TAC[]`. -/
  SUBSET_DISJOINT_UNION_EXISTS : thm
  /-- `INTER_DISJOINT_UNION` (sets.ml 3294): `REWRITE_TAC[...] THEN
      MESON_TAC[PAIR_EQ]`. -/
  INTER_DISJOINT_UNION : thm
  /-- `UNION_DISJOINT_UNION` (sets.ml 3302): `REWRITE_TAC[...] THEN
      MESON_TAC[PAIR_EQ]`. -/
  UNION_DISJOINT_UNION : thm
  /-- `DISJOINT_UNION_EQ_EMPTY` (sets.ml 3310): `REWRITE_TAC[...] THEN
      SET_TAC[]`. -/
  DISJOINT_UNION_EQ_EMPTY : thm
  /-- `DISJOINT_DISJOINT_UNION` (sets.ml 3317): `REWRITE_TAC[DISJOINT;
      INTER_DISJOINT_UNION; DISJOINT_UNION_EQ_EMPTY]`. -/
  DISJOINT_DISJOINT_UNION : thm
  deriving Inhabited

@[nospecialize]
def setupSetsFunspace [HolBase] (S : SetsCore)
    (P : SetsProps) (SIn : SetsInclusion) (SImg : SetsImage) (SMi : SetsMisc)
    (Pr : HolMath.Pair.PairThms) (Tr : HolCore.Trivia.TriviaThms) (o_DEF : thm)
    (MESON_TAC : List thm → tactic) (ASM_MESON_TAC : List thm → tactic)
    (new_definition' : term → IO (Except String thm)) :
    ExceptT String IO SetsFunspace := do
  let SET_TAC := SET_TAC S P MESON_TAC
  let SET_RULE := SET_RULE S P MESON_TAC
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let { IN, EXTENSION, IN_ELIM_THM, SUBSET, DISJOINT, .. } := S
  let { NOT_IN_EMPTY, IN_UNIV, IN_UNION, IN_INTER, IN_SING, IN_IMAGE,
        FORALL_IN_IMAGE, FORALL_IN_GSPEC, EXISTS_IN_GSPEC, .. } := P
  let { SUBSET_ANTISYM_EQ, EMPTY_SUBSET, .. } := SIn
  let { IMAGE_CLAUSES, IMAGE_o, SIMPLE_IMAGE_GEN, .. } := SImg
  let { IN_ELIM_PAIR_THM, .. } := SMi
  let { PAIR_EQ, FORALL_PAIR_THM, .. } := Pr
  let { o_THM, .. } := Tr
  let { LEFT_IMP_EXISTS_THM, .. } := HolBase.T
  let { FUN_EQ_THM, NOT_EXISTS_THM, SKOLEM_THM, .. } := HolBase.C

  /- "Extensional" functions, mapping to a fixed value ARB outside the domain.
     Even though these are still total, they're a conveniently better model
     of the partial function space (e.g. the space has the right cardinality). -/

  let ARB ← new_definition
   r"ARB = (@x:A. F)"

  let EXTENSIONAL ← new_definition
   r"EXTENSIONAL s = {f:A->B | !x. ~(x IN s) ==> f x = ARB}"

  let IN_EXTENSIONAL ← prove
   r"!s f:A->B. f IN EXTENSIONAL s <=> (!x. ~(x IN s) ==> f x = ARB)"
   (REWRITE_TAC [EXTENSIONAL, IN_ELIM_THM])

  let IN_EXTENSIONAL_UNDEFINED ← prove
   r"!s f:A->B x. f IN EXTENSIONAL s /\ ~(x IN s) ==> f x = ARB"
   (SIMP_TAC [IN_EXTENSIONAL])

  let EXTENSIONAL_EMPTY ← prove
   r"EXTENSIONAL {} = {\x:A. ARB:B}"
   (REWRITE_TAC [EXTENSION, IN_EXTENSIONAL, IN_SING, NOT_IN_EMPTY] THEN
    REWRITE_TAC [FUN_EQ_THM])

  let EXTENSIONAL_UNIV ← prove
   r"!f:A->B. EXTENSIONAL (:A) f"
   (REWRITE_TAC [EXTENSIONAL, IN_UNIV, IN_ELIM_THM])

  let EXTENSIONAL_EQ ← prove
   r"!s f g:A->B.
     f IN EXTENSIONAL s /\ g IN EXTENSIONAL s /\ (!x. x IN s ==> f x = g x)
     ==> f = g"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
    ASM_CASES_TAC (← q r"x:A IN s") THENL
    [ASM_SIMP_TAC [], ASM_MESON_TAC [IN_EXTENSIONAL_UNDEFINED]])

  /- Restriction of a function to an EXTENSIONAL one on a subset. -/

  let RESTRICTION ← new_definition
   r"RESTRICTION s (f:A->B) x = if x IN s then f x else ARB"

  let RESTRICTION_THM ← prove
   r"!s (f:A->B). RESTRICTION s f = \x. if x IN s then f x else ARB"
   (REWRITE_TAC [FUN_EQ_THM, RESTRICTION])

  let RESTRICTION_DEFINED ← prove
   r"!s f:A->B x. x IN s ==> RESTRICTION s f x = f x"
   (SIMP_TAC [RESTRICTION])

  let RESTRICTION_UNDEFINED ← prove
   r"!s f:A->B x. ~(x IN s) ==> RESTRICTION s f x = ARB"
   (SIMP_TAC [RESTRICTION])

  let RESTRICTION_EQ ← prove
   r"!s f:A->B x y. x IN s /\ f x = y ==> RESTRICTION s f x = y"
   (SIMP_TAC [RESTRICTION_DEFINED])

  let RESTRICTION_IN_EXTENSIONAL ← prove
   r"!s f:A->B. RESTRICTION s f IN EXTENSIONAL s"
   (SIMP_TAC [IN_EXTENSIONAL, RESTRICTION])

  let RESTRICTION_EXTENSION ← prove
   r"!s f g:A->B. RESTRICTION s f = RESTRICTION s g <=>
                (!x. x IN s ==> f x = g x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [RESTRICTION, FUN_EQ_THM] THEN MESON_TAC [])

  let RESTRICTION_FIXPOINT ← prove
   r"!s f:A->B. RESTRICTION s f = f <=> f IN EXTENSIONAL s"
   (REWRITE_TAC [IN_EXTENSIONAL, FUN_EQ_THM, RESTRICTION] THEN MESON_TAC [])

  let RESTRICTION_UNIV ← prove
   r"!f:A->B. RESTRICTION UNIV f = f"
   (REWRITE_TAC [FUN_EQ_THM, RESTRICTION, IN_UNIV])

  let RESTRICTION_RESTRICTION ← prove
   r"!s t f:A->B.
        s SUBSET t ==> RESTRICTION s (RESTRICTION t f) = RESTRICTION s f"
   (REWRITE_TAC [FUN_EQ_THM, RESTRICTION] THEN SET_TAC [])

  let RESTRICTION_IDEMP ← prove
   r"!s f:A->B. RESTRICTION s (RESTRICTION s f) = RESTRICTION s f"
   (REWRITE_TAC [RESTRICTION_FIXPOINT, RESTRICTION_IN_EXTENSIONAL])

  let IMAGE_RESTRICTION ← prove
   r"!f:A->B s t. s SUBSET t ==> IMAGE (RESTRICTION t f) s = IMAGE f s"
   (REWRITE_TAC [EXTENSION, IN_IMAGE, RESTRICTION] THEN SET_TAC [])

  let RESTRICTION_COMPOSE_RIGHT ← prove
   r"!f:A->B g:B->C s.
        RESTRICTION s (g o RESTRICTION s f) =
        RESTRICTION s (g o f)"
   (REWRITE_TAC [FUN_EQ_THM, o_DEF, RESTRICTION] THEN
    SIMP_TAC [SUBSET, FORALL_IN_IMAGE] THEN SET_TAC [])

  let RESTRICTION_COMPOSE_LEFT ← prove
   r"!f:A->B g:B->C s t.
        IMAGE f s SUBSET t
        ==> RESTRICTION s (RESTRICTION t g o f) =
            RESTRICTION s (g o f)"
   (REWRITE_TAC [FUN_EQ_THM, o_DEF, RESTRICTION] THEN
    SIMP_TAC [SUBSET, FORALL_IN_IMAGE] THEN SET_TAC [])

  let RESTRICTION_COMPOSE ← prove
   r"!f:A->B g:B->C s t.
        IMAGE f s SUBSET t
        ==> RESTRICTION s (RESTRICTION t g o RESTRICTION s f) =
            RESTRICTION s (g o f)"
   (SIMP_TAC [RESTRICTION_COMPOSE_LEFT, RESTRICTION_COMPOSE_RIGHT])

  let RESTRICTION_UNIQUE ← prove
   r"!s (f:A->B) g.
        RESTRICTION s f = g <=> EXTENSIONAL s g /\ !x. x IN s ==> f x = g x"
   (REWRITE_TAC [FUN_EQ_THM, RESTRICTION, EXTENSIONAL, IN_ELIM_THM] THEN
    MESON_TAC [])

  let RESTRICTION_UNIQUE_ALT ← prove
   r"!s (f:A->B) g.
        f = RESTRICTION s g <=> EXTENSIONAL s f /\ !x. x IN s ==> f x = g x"
   (REWRITE_TAC [FUN_EQ_THM, RESTRICTION, EXTENSIONAL, IN_ELIM_THM] THEN
    MESON_TAC [])

  /- General Cartesian product / dependent function space. -/

  let cartesian_product ← new_definition
   r"cartesian_product k s =
        {f:K->A | EXTENSIONAL k f /\ !i. i IN k ==> f i IN s i}"

  let IN_CARTESIAN_PRODUCT ← prove
   r"!k s (x:K->A).
        x IN cartesian_product k s <=>
        EXTENSIONAL k x /\ (!i. i IN k ==> x i IN s i)"
   (REWRITE_TAC [cartesian_product, IN_ELIM_THM])

  let CARTESIAN_PRODUCT ← prove
   r"!k s. cartesian_product k s =
         {f:K->A | !i. f i IN (if i IN k then s i else {ARB})}"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC [cartesian_product, IN_ELIM_THM, EXTENSIONAL] THEN
    MESON_TAC [IN_SING])

  let RESTRICTION_IN_CARTESIAN_PRODUCT ← prove
   r"!k s (f:K->A).
        RESTRICTION k f IN cartesian_product k s <=>
        !i. i IN k ==> (f i) IN (s i)"
   (REWRITE_TAC [RESTRICTION, cartesian_product, EXTENSIONAL, IN_ELIM_THM] THEN
    SET_TAC [])

  let CARTESIAN_PRODUCT_AS_RESTRICTIONS ← prove
   r"!k (s:K->A->bool).
      cartesian_product k s =
      {RESTRICTION k f |f| !i. i IN k ==> f i IN s i}"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ, SUBSET, FORALL_IN_GSPEC] THEN
    REWRITE_TAC [RESTRICTION_IN_CARTESIAN_PRODUCT] THEN
    X_GEN_TAC (← q r"x:K->A") THEN
    REWRITE_TAC [cartesian_product, IN_ELIM_THM, EXTENSIONAL] THEN
    STRIP_TAC THEN EXISTS_TAC (← q r"x:K->A") THEN
    ASM_REWRITE_TAC [FUN_EQ_THM, RESTRICTION] THEN ASM_MESON_TAC [])

  let CARTESIAN_PRODUCT_EQ_EMPTY ← prove
   r"!k s:K->A->bool.
        cartesian_product k s = {} <=> ?i. i IN k /\ s i = {}"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
    REWRITE_TAC [← SET_RULE
     (← q r"(?i. i IN k /\ s i = {}) <=> ~(!i. ?a. i IN k ==> a IN s i)")] THEN
    REWRITE_TAC [SKOLEM_THM, NOT_EXISTS_THM, cartesian_product] THEN
    REWRITE_TAC [IN_ELIM_THM, NOT_IN_EMPTY] THEN EQ_TAC THEN
    DISCH_TAC THEN X_GEN_TAC (← q r"f:K->A") THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"\i. if i IN k then (f:K->A) i else ARB")) THEN
    REWRITE_TAC [EXTENSIONAL, IN_ELIM_THM] THEN SIMP_TAC [])

  let CARTESIAN_PRODUCT_EMPTY ← prove
   r"!(s:K->A->bool). cartesian_product {} s = {(\i. ARB)}"
   (REWRITE_TAC [CARTESIAN_PRODUCT, NOT_IN_EMPTY, EXTENSION] THEN
    REWRITE_TAC [IN_ELIM_THM, IN_SING] THEN REWRITE_TAC [FUN_EQ_THM])

  let CARTESIAN_PRODUCT_EQ_MEMBERS ← prove
   r"!k s x y:K->A.
        x IN cartesian_product k s /\ y IN cartesian_product k s /\
        (!i. i IN k ==> x i = y i)
        ==> x = y"
   (REWRITE_TAC [cartesian_product, IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC EXTENSIONAL_EQ THEN
    EXISTS_TAC (← q r"k:K->bool") THEN ASM_REWRITE_TAC [IN])

  let CARTESIAN_PRODUCT_EQ_MEMBERS_EQ ← prove
   r"!k s x y:K->A.
        x IN cartesian_product k s /\
        y IN cartesian_product k s
        ==> (x = y <=> !i. i IN k ==> x i = y i)"
   (MESON_TAC [CARTESIAN_PRODUCT_EQ_MEMBERS])

  let SUBSET_CARTESIAN_PRODUCT ← prove
   r"!k s t:K->A->bool.
        cartesian_product k s SUBSET cartesian_product k t <=>
        cartesian_product k s = {} \/ !i. i IN k ==> s i SUBSET t i"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"cartesian_product k (s:K->A->bool) = {}") THEN
    ASM_REWRITE_TAC [EMPTY_SUBSET] THEN
    REWRITE_TAC [SUBSET, cartesian_product, IN_ELIM_THM] THEN
    EQ_TAC THENL [ALL_TAC, MESON_TAC []] THEN FIRST_X_ASSUM (MP_TAC o
      GEN_REWRITE_RULE RAND_CONV [CARTESIAN_PRODUCT_EQ_EMPTY]) THEN
    REWRITE_TAC [← SET_RULE
     (← q r"~(?i. i IN k /\ s i = {}) <=> (!i. ?a. i IN k ==> a IN s i)")] THEN
    REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"z:K->A") THEN DISCH_TAC THEN DISCH_TAC THEN
    X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC
     (← q r"(\j. if j IN k then if j = i then x else z j else ARB):K->A")) THEN
    REWRITE_TAC [EXTENSIONAL, IN_ELIM_THM] THEN SIMP_TAC [] THEN
    ASM_MESON_TAC [])

  let CARTESIAN_PRODUCT_EQ ← prove
   r"!k s t:K->A->bool.
        cartesian_product k s = cartesian_product k t <=>
        cartesian_product k s = {} /\ cartesian_product k t = {} \/
        !i. i IN k ==> s i = t i"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"!i. i IN k ==> (s:K->A->bool) i = t i") THEN
    ASM_REWRITE_TAC [] THENL
     [ASM_SIMP_TAC [cartesian_product, EXTENSION, IN_ELIM_THM],
      ASM_CASES_TAC (← q r"cartesian_product k (t:K->A->bool) = {}") THEN
      ASM_REWRITE_TAC [] THEN
      ASM_CASES_TAC (← q r"cartesian_product k (s:K->A->bool) = {}") THEN
      ASM_REWRITE_TAC [] THEN
      ASM_REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ, SUBSET_CARTESIAN_PRODUCT] THEN
      ASM SET_TAC []])

  let INTER_CARTESIAN_PRODUCT ← prove
   r"!k s t:K->A->bool.
        (cartesian_product k s) INTER (cartesian_product k t) =
        cartesian_product k (\i. s i INTER t i)"
   (REWRITE_TAC [EXTENSION, cartesian_product, IN_INTER, IN_ELIM_THM] THEN
    SET_TAC [])

  let CARTESIAN_PRODUCT_UNIV ← prove
   r"cartesian_product (:K) (\i. (:A)) = (:K->A)"
   (REWRITE_TAC [EXTENSION, IN_UNIV, cartesian_product, IN_ELIM_THM] THEN
    REWRITE_TAC [EXTENSIONAL_UNIV])

  let CARTESIAN_PRODUCT_SINGS ← prove
   r"!k x:K->A. EXTENSIONAL k x ==> cartesian_product k (\i. {x i}) = {x}"
   (REWRITE_TAC [cartesian_product, IN_SING] THEN
    REWRITE_TAC [EXTENSION, EXTENSIONAL, IN_ELIM_THM, IN_SING] THEN
    REWRITE_TAC [FUN_EQ_THM] THEN MESON_TAC [])

  let CARTESIAN_PRODUCT_SINGS_GEN ← prove
   r"!k (x:K->A). cartesian_product k (\i. {x i}) = {RESTRICTION k x}"
   (REWRITE_TAC [cartesian_product, IN_SING] THEN
    REWRITE_TAC [EXTENSION, EXTENSIONAL, IN_ELIM_THM, IN_SING] THEN
    REWRITE_TAC [FUN_EQ_THM, RESTRICTION] THEN MESON_TAC [])

  let IMAGE_PROJECTION_CARTESIAN_PRODUCT ← prove
   r"!k s:K->A->bool i.
        IMAGE (\x. x i) (cartesian_product k s) =
        if cartesian_product k s = {} then {}
        else if i IN k then s i else {ARB}"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"cartesian_product k (s:K->A->bool) = {}") THEN
    ASM_REWRITE_TAC [IMAGE_CLAUSES] THEN
    REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ, SUBSET, FORALL_IN_IMAGE] THEN
    SIMP_TAC [CARTESIAN_PRODUCT, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o
      GEN_REWRITE_RULE RAND_CONV [CARTESIAN_PRODUCT_EQ_EMPTY]) THEN
    REWRITE_TAC [← SET_RULE
     (← q r"~(?i. i IN k /\ s i = {}) <=> (!i. ?a. i IN k ==> a IN s i)")] THEN
    REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"z:K->A") THEN DISCH_TAC THEN
    REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN
    EXISTS_TAC
     (← q r"\j. if j = i then x else if j IN k then (z:K->A) j else ARB") THEN
    ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [IN_SING])

  let FORALL_CARTESIAN_PRODUCT_ELEMENTS ← prove
   r"!P k s:K->A->bool.
        (!z i. z IN cartesian_product k s /\ i IN k ==> P i (z i)) <=>
        cartesian_product k s = {} \/
        (!i x. i IN k /\ x IN s i ==> P i x)"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"cartesian_product k (s:K->A->bool) = {}") THEN
    ASM_REWRITE_TAC [NOT_IN_EMPTY] THEN
    REWRITE_TAC [cartesian_product, IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_TAC, MESON_TAC []] THEN
    FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV
     [CARTESIAN_PRODUCT_EQ_EMPTY]) THEN
    REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM, ← SET_RULE
       (← q r"~(?i. i IN k /\ s i = {}) <=> (!i. ?x. i IN k ==> x IN s i)")] THEN
    X_GEN_TAC (← q r"z:K->A") THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [← q r"i:K", ← q r"x:A"] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL
     [← q r"\j. if j = i then x else if j IN k then (z:K->A) j else ARB", ← q r"i:K"]) THEN
    ASM_REWRITE_TAC [EXTENSIONAL, IN_ELIM_THM] THEN ASM_MESON_TAC [])

  let FORALL_CARTESIAN_PRODUCT_ELEMENTS_EQ ← prove
   r"!P k (s:K->A->bool).
        ~(cartesian_product k s = {})
        ==> ((!i x. i IN k /\ x IN s i ==> P i x) <=>
             !z i. z IN cartesian_product k s /\ i IN k ==> P i (z i))"
   (SIMP_TAC [FORALL_CARTESIAN_PRODUCT_ELEMENTS])

  let EXISTS_CARTESIAN_PRODUCT_ELEMENT ← prove
   r"!P k s:K->A->bool.
        (?z. z IN cartesian_product k s /\ (!i. i IN k ==> P i (z i))) <=>
        (!i. i IN k ==> ?x. x IN (s i) /\ P i x)"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [CARTESIAN_PRODUCT_AS_RESTRICTIONS, EXISTS_IN_GSPEC] THEN
    SIMP_TAC [RESTRICTION] THEN MESON_TAC [])

  /- Product of a family of maps. -/

  let product_map ← new_definition
   r"product_map k (f:K->A->B) = \x. RESTRICTION k (\i. f i (x i))"

  let PRODUCT_MAP_RESTRICTION ← prove
   r"!(f:K->A->B) k x.
        product_map k f (RESTRICTION k x) = RESTRICTION k (\i. f i (x i))"
   (SIMP_TAC [product_map, RESTRICTION, o_THM, FUN_EQ_THM])

  let IMAGE_PRODUCT_MAP ← prove
   r"!(f:K->A->B) k s.
        IMAGE (product_map k f) (cartesian_product k s) =
        cartesian_product k (\i. IMAGE (f i) (s i))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [CARTESIAN_PRODUCT_AS_RESTRICTIONS] THEN
    ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC [product_map, ← GSYM IMAGE_o, o_DEF] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC (← q r"g:K->B") THEN
    REWRITE_TAC [IN_IMAGE, RESTRICTION, IN_ELIM_THM] THEN
    EQ_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [RESTRICTION_EXTENSION] THEN
    ASM SET_TAC [])

  /- Disjoint union construction for a family of sets. -/

  let disjoint_union ← new_definition
   r"disjoint_union (k:K->bool) (s:K->A->bool) = { (i,x) | i IN k /\ x IN s i}"

  let SUBSET_DISJOINT_UNION ← prove
   r"!k (s:K->A->bool) t.
        disjoint_union k s SUBSET disjoint_union k t <=>
        !i. i IN k ==> s i SUBSET t i"
   (REWRITE_TAC [SUBSET, disjoint_union, FORALL_IN_GSPEC] THEN
    REWRITE_TAC [IN_ELIM_PAIR_THM] THEN SET_TAC [])

  let DISJOINT_UNION_EQ ← prove
   r"!k (s:K->A->bool) t.
        disjoint_union k s = disjoint_union k t <=>
        !i. i IN k ==> s i = t i"
   (REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ, SUBSET_DISJOINT_UNION] THEN
    SET_TAC [])

  let SUBSET_DISJOINT_UNION_EXISTS ← prove
   r"!k (s:K->A->bool) u.
        u SUBSET disjoint_union k s <=>
        ?t. u = disjoint_union k t /\ !i. i IN k ==> t i SUBSET s i"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC, MESON_TAC [SUBSET_DISJOINT_UNION]] THEN
    EXISTS_TAC (← q r"\i. {x | (i,x) IN (u:K#A->bool)}") THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [SUBSET, EXTENSION] THEN
    REWRITE_TAC [disjoint_union, FORALL_PAIR_THM, IN_ELIM_PAIR_THM] THEN
    SET_TAC [])

  let INTER_DISJOINT_UNION ← prove
   r"!k s t:K->A->bool.
        (disjoint_union k s) INTER (disjoint_union k t) =
        disjoint_union k (\i. s i INTER t i)"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [EXTENSION, disjoint_union, IN_INTER, IN_ELIM_THM] THEN
    MESON_TAC [PAIR_EQ])

  let UNION_DISJOINT_UNION ← prove
   r"!k s t:K->A->bool.
        (disjoint_union k s) UNION (disjoint_union k t) =
        disjoint_union k (\i. s i UNION t i)"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [EXTENSION, disjoint_union, IN_UNION, IN_ELIM_THM] THEN
    MESON_TAC [PAIR_EQ])

  let DISJOINT_UNION_EQ_EMPTY ← prove
   r"!k s:K->A->bool.
        disjoint_union k s = {} <=> !i. i IN k ==> s i = {}"
   (REWRITE_TAC [EXTENSION, FORALL_PAIR_THM, disjoint_union, IN_ELIM_PAIR_THM,
                 NOT_IN_EMPTY] THEN
    SET_TAC [])

  let DISJOINT_DISJOINT_UNION ← prove
   r"!k s t:K->A->bool.
        DISJOINT (disjoint_union k s) (disjoint_union k t) =
        !i. i IN k ==> DISJOINT (s i) (t i)"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [DISJOINT, INTER_DISJOINT_UNION, DISJOINT_UNION_EQ_EMPTY])

  return {
    ARB, EXTENSIONAL, IN_EXTENSIONAL, IN_EXTENSIONAL_UNDEFINED,
    EXTENSIONAL_EMPTY, EXTENSIONAL_UNIV, EXTENSIONAL_EQ, RESTRICTION,
    RESTRICTION_THM, RESTRICTION_DEFINED, RESTRICTION_UNDEFINED,
    RESTRICTION_EQ, RESTRICTION_IN_EXTENSIONAL, RESTRICTION_EXTENSION,
    RESTRICTION_FIXPOINT, RESTRICTION_UNIV, RESTRICTION_RESTRICTION,
    RESTRICTION_IDEMP, IMAGE_RESTRICTION, RESTRICTION_COMPOSE_RIGHT,
    RESTRICTION_COMPOSE_LEFT, RESTRICTION_COMPOSE, RESTRICTION_UNIQUE,
    RESTRICTION_UNIQUE_ALT, cartesian_product, IN_CARTESIAN_PRODUCT,
    CARTESIAN_PRODUCT, RESTRICTION_IN_CARTESIAN_PRODUCT,
    CARTESIAN_PRODUCT_AS_RESTRICTIONS, CARTESIAN_PRODUCT_EQ_EMPTY,
    CARTESIAN_PRODUCT_EMPTY, CARTESIAN_PRODUCT_EQ_MEMBERS,
    CARTESIAN_PRODUCT_EQ_MEMBERS_EQ, SUBSET_CARTESIAN_PRODUCT,
    CARTESIAN_PRODUCT_EQ, INTER_CARTESIAN_PRODUCT, CARTESIAN_PRODUCT_UNIV,
    CARTESIAN_PRODUCT_SINGS, CARTESIAN_PRODUCT_SINGS_GEN,
    IMAGE_PROJECTION_CARTESIAN_PRODUCT, FORALL_CARTESIAN_PRODUCT_ELEMENTS,
    FORALL_CARTESIAN_PRODUCT_ELEMENTS_EQ, EXISTS_CARTESIAN_PRODUCT_ELEMENT,
    product_map, PRODUCT_MAP_RESTRICTION, IMAGE_PRODUCT_MAP, disjoint_union,
    SUBSET_DISJOINT_UNION, DISJOINT_UNION_EQ, SUBSET_DISJOINT_UNION_EXISTS,
    INTER_DISJOINT_UNION, UNION_DISJOINT_UNION, DISJOINT_UNION_EQ_EMPTY,
    DISJOINT_DISJOINT_UNION }

/- ---------------------------------------------------------------------- -/
/- Cardinality of functions with bounded domain (support) and range;      -/
/- of bool; of the powerset.  (sets.ml 3325-3553)                         -/
/- ---------------------------------------------------------------------- -/

/-- The cardinality theorems for function spaces, the type `bool`, and hence
    the powerset, of sets.ml 3325-3548 (TWENTY theorems).  Built on the
    dependent-function-space material of the preceding bundle plus the
    `HAS_SIZE`/`CARD` reasoning of `SCard`/`SCard2`, `HAS_SIZE_PRODUCT`
    (`SCross`) and the `FINITE` lemmas of `SFin`.  The payoff is
    `HAS_SIZE_POWERSET`/`CARD_POWERSET`/`FINITE_POWERSET`: a powerset is a
    funspace into `bool`, so its size is `2 EXP n`.  `HAS_SIZE_FUNSPACE`
    inducts over the domain and reduces the successor step to
    `HAS_SIZE_IMAGE_INJ`/`HAS_SIZE_PRODUCT`. -/
structure SetsFunspace2 where
  /-- `HAS_SIZE_FUNSPACE` (sets.ml 3328): the set of bounded-support functions
      `{f | (!x. x IN s ==> f x IN t) /\ (!x. ~(x IN s) ==> f x = d)}` has size
      `n EXP m` when `s HAS_SIZE m` and `t HAS_SIZE n`.  `INDUCT_TAC` over the
      domain size; THREE top-level width-2 `THENL`s (after
      `REWRITE_TAC[HAS_SIZE_CLAUSES]`; after the `SUBGOAL_THEN ... SUBST1_TAC`;
      after the final `CONJ_TAC`) plus a NESTED width-2 `EQ_TAC THENL` inside
      the first `SUBST1_TAC` branch.  `CONV_TAC HAS_SIZE_CONV` (bare, ZERO
      depth); `CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV)`;
      `ONCE_REWRITE_RULE[CONJ_SYM] UNWIND_THM1`; `MP_TAC o SPEC` explicit
      thm_tactics; `DISCH_THEN(X_CHOOSE_THEN .. (X_CHOOSE_THEN ..
      STRIP_ASSUME_TAC))`. -/
  HAS_SIZE_FUNSPACE : thm
  /-- `CARD_FUNSPACE` (sets.ml 3372): `MESON[HAS_SIZE_FUNSPACE; HAS_SIZE]`. -/
  CARD_FUNSPACE : thm
  /-- `FINITE_FUNSPACE` (sets.ml 3379): `MESON[HAS_SIZE_FUNSPACE; HAS_SIZE]`. -/
  FINITE_FUNSPACE : thm
  /-- `HAS_SIZE_FUNSPACE_UNIV` (sets.ml 3385): `REPEAT GEN_TAC THEN
      DISCH_THEN(MP_TAC o MATCH_MP HAS_SIZE_FUNSPACE) THEN
      REWRITE_TAC[IN_UNIV; UNIV_GSPEC]`.  `MP_TAC o MATCH_MP` explicit
      thm_tactic.  No top-level `THENL`. -/
  HAS_SIZE_FUNSPACE_UNIV : thm
  /-- `CARD_FUNSPACE_UNIV` (sets.ml 3391):
      `MESON[HAS_SIZE_FUNSPACE_UNIV; HAS_SIZE]`. -/
  CARD_FUNSPACE_UNIV : thm
  /-- `FINITE_FUNSPACE_UNIV` (sets.ml 3395):
      `MESON[HAS_SIZE_FUNSPACE_UNIV; HAS_SIZE]`. -/
  FINITE_FUNSPACE_UNIV : thm
  /-- `HAS_SIZE_BOOL` (sets.ml 3403): `(:bool) HAS_SIZE 2`.  ONE width-2
      top-level `SUBGOAL_THEN (:bool) = {F,T} SUBST1_TAC THENL
      [REWRITE_TAC[..] THEN CONV_TAC TAUT; SIMP_TAC[..]]`.  `CONV_TAC TAUT`. -/
  HAS_SIZE_BOOL : thm
  /-- `CARD_BOOL` (sets.ml 3410): `MESON[HAS_SIZE_BOOL; HAS_SIZE]`. -/
  CARD_BOOL : thm
  /-- `FINITE_BOOL` (sets.ml 3414): `MESON[HAS_SIZE_BOOL; HAS_SIZE]`. -/
  FINITE_BOOL : thm
  /-- `HAS_SIZE_POWERSET` (sets.ml 3422): `{t | t SUBSET s} HAS_SIZE 2 EXP n`.
      ONE width-2 top-level `SUBGOAL_THEN {t|t SUBSET s} = {funspace} SUBST1_TAC
      THENL [REWRITE_TAC[..]; MATCH_MP_TAC HAS_SIZE_FUNSPACE THEN .. THEN
      CONV_TAC HAS_SIZE_CONV THEN MAP_EVERY EXISTS_TAC [`T`;`F`] THEN .. THEN
      CONV_TAC TAUT]`.  `CONV_TAC HAS_SIZE_CONV` (bare, ZERO). -/
  HAS_SIZE_POWERSET : thm
  /-- `CARD_POWERSET` (sets.ml 3434): `MESON[HAS_SIZE_POWERSET; HAS_SIZE]`. -/
  CARD_POWERSET : thm
  /-- `FINITE_POWERSET` (sets.ml 3438): `MESON[HAS_SIZE_POWERSET; HAS_SIZE]`. -/
  FINITE_POWERSET : thm
  /-- `FINITE_POWERSET_EQ` (sets.ml 3442): `FINITE {t | t SUBSET s} <=>
      FINITE s`.  `GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[FINITE_POWERSET] THEN
      DISCH_TAC THEN SUBGOAL_THEN FINITE(IMAGE (\x. {x}) s) MP_TAC THENL
      [b1; b2]`.  ONE width-2 top-level `THENL` (the `SUBGOAL_THEN`);
      b1 uses `MATCH_MP (REWRITE_RULE[T.IMP_CONJ] FINITE_SUBSET)` via
      `FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP ..)`; b2 uses
      `MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN
      SET_TAC[]`. -/
  FINITE_POWERSET_EQ : thm
  /-- `FINITE_RESTRICTED_SUBSETS` (sets.ml 3452): `REPEAT STRIP_TAC THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{t | t SUBSET s}` THEN
      ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[]`.  No top-level `THENL`. -/
  FINITE_RESTRICTED_SUBSETS : thm
  /-- `FINITE_UNIONS` (sets.ml 3458): `FINITE(UNIONS s) <=> FINITE s /\
      (!t. t IN s ==> FINITE t)`.  `GEN_TAC THEN ASM_CASES_TAC FINITE s THEN
      ASM_SIMP_TAC[FINITE_FINITE_UNIONS] THEN
      DISCH_THEN(MP_TAC o MATCH_MP FINITE_POWERSET) THEN POP_ASSUM MP_TAC THEN
      REWRITE_TAC[CONTRAPOS_THM] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN SET_TAC[]`.
      No top-level `THENL`; `MP_TAC o MATCH_MP` explicit thm_tactic;
      `REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET` bound first. -/
  FINITE_UNIONS : thm
  /-- `FINITE_CARD_LE_UNIONS` (sets.ml 3467): `REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[FINITE_UNIONS; FORALL_IN_GSPEC; FINITE_IMAGE;
      SIMPLE_IMAGE] THEN TRANS_TAC LE_TRANS `CARD s * n` THEN
      ASM_REWRITE_TAC[GSYM SIMPLE_IMAGE; LE_MULT_RCANCEL] THEN
      MATCH_MP_TAC CARD_UNIONS_LE THEN ASM_REWRITE_TAC[HAS_SIZE]`.  No
      top-level `THENL`. -/
  FINITE_CARD_LE_UNIONS : thm
  /-- `POWERSET_CLAUSES` (sets.ml 3479): the empty and INSERT recursion of the
      powerset.  TWO top-level width-2 `THENL`s, each `[ALL_TAC; <closer>]`
      with a common tail after: `CONJ_TAC THENL [ALL_TAC; SET_TAC[]]` (bare
      SET_TAC) and `ASM_CASES_TAC (a IN s) THENL [ALL_TAC; ASM SET_TAC[]]`
      (ASM SET_TAC).  `ONCE_REWRITE_TAC[SUBSET]`; `DISJ2_TAC`; `EXISTS_TAC
      `s DELETE a``. -/
  POWERSET_CLAUSES : thm
  /-- `FINITE_IMAGE_INFINITE` (sets.ml 3495): an infinite set with finite image
      has an infinite fibre.  ONE width-2 top-level `SUBGOAL_THEN s = UNIONS{..}
      SUBST1_TAC THENL [REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]; ALL_TAC]`
      with a common tail after.  `GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM]`
      (`I` = id, ZERO); an inline `TAUT `~(p /\ q) <=> p ==> ~q``. -/
  FINITE_IMAGE_INFINITE : thm
  /-- `FINITE_RESTRICTED_POWERSET` (sets.ml 3507): `FINITE {t | t SUBSET s /\
      t HAS_SIZE n} <=> FINITE s \/ n = 0`.  Nested `THENL`s: the top-level
      `ASM_CASES_TAC (n = 0) ... THENL [b1; b2]` (width 2); b2 nests
      `ASM_CASES_TAC FINITE s ... THENL [b2a; b2b]` (width 2); b2b nests a
      `SUBGOAL_THEN FINITE s MP_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]]` (width 2,
      common tail) and a `CONJ_TAC THENL [b2b1; b2b2]` (width 2).  `GEN_REWRITE_TAC
      I [SUBSET]` (ZERO); `CHOOSE_SUBSET_BETWEEN`; two inline `SET_RULE`s. -/
  FINITE_RESTRICTED_POWERSET : thm
  /-- `FINITE_RESTRICTED_FUNSPACE` (sets.ml 3531): the funspace of maps agreeing
      with `k` off a finite set is finite.  ONE top-level width-2
      `CONJ_TAC THENL [ALL_TAC; <closer>] THEN <tail>`: branch 1 is `ALL_TAC`,
      branch 2 closes the second goal with `ASM SET_TAC[]`, and the tail applies
      to the surviving goal 1.  `GEN_REWRITE_TAC I [SUBSET]` (ZERO); the witness
      IMAGE uses a paired select `@y. (x,y) IN u`; `GSYM CONJ_ASSOC`,
      `UNWIND_THM1`, `UNWIND_THM2`. -/
  FINITE_RESTRICTED_FUNSPACE : thm
  deriving Inhabited

@[nospecialize]
def setupSetsFunspace2 [HolBase] (S : SetsCore)
    (P : SetsProps) (SIn : SetsInclusion) (SOp : SetsOperators)
    (SID : SetsInsertDelete)
    (SImg : SetsImage) (SMi : SetsMisc) (SFin : SetsFinite)
    (SCard : SetsCard) (SCard2 : SetsCard2) (SCross : SetsCross)
    (Pr : HolMath.Pair.PairThms)
    (MESON_TAC : List thm → tactic) (ASM_MESON_TAC : List thm → tactic)
    (GEN_BETA_CONV : ioconv)
    (INDUCT_TAC : tactic)
    (EXP LE_TRANS LE_MULT_RCANCEL LE_1 ARITH : thm) :
    ExceptT String IO SetsFunspace2 := do
  let SET_TAC := SET_TAC S P MESON_TAC
  let SET_RULE := SET_RULE S P MESON_TAC
  let { IN, EXTENSION, IN_ELIM_THM, SUBSET, INFINITE, .. } := S
  let { NOT_IN_EMPTY, IN_UNIV, IN_UNION, IN_INSERT, IN_SING, IN_IMAGE,
        FORALL_IN_IMAGE, FORALL_IN_GSPEC, UNIONS_GSPEC, .. } := P
  let { SUBSET_ANTISYM, SUBSET_EMPTY, SING_SUBSET, .. } := SIn
  let { UNION_SUBSET, .. } := SOp
  let { SUBSET_INSERT_DELETE, .. } := SID
  let { SIMPLE_IMAGE, .. } := SImg
  let { UNIV_GSPEC, SING_GSPEC, .. } := SMi
  let { FINITE_EMPTY, FINITE_SUBSET, FINITE_RESTRICT, FINITE_INSERT,
        FINITE_SING, FINITE_FINITE_UNIONS, FINITE_IMAGE, FINITE_IMAGE_INJ_EQ, .. } := SFin
  let { CARD_CLAUSES, CARD_SING, HAS_SIZE, HAS_SIZE_0, HAS_SIZE_CLAUSES,
        HAS_SIZE_CONV, .. } := SCard
  let { CARD_UNIONS_LE, HAS_SIZE_IMAGE_INJ, CHOOSE_SUBSET_BETWEEN, .. } := SCard2
  let { HAS_SIZE_PRODUCT, IN_CROSS, FINITE_CROSS, .. } := SCross
  let { PAIR_EQ, FORALL_PAIR_THM, EXISTS_PAIR_THM, .. } := Pr
  let { CONJ_ASSOC, CONJ_SYM, IMP_CONJ, IMP_CONJ_ALT, EQ_IMP, UNWIND_THM1,
        UNWIND_THM2, LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM, .. } := HolBase.T
  let { FUN_EQ_THM, CONTRAPOS_THM, NOT_EXISTS_THM, .. } := HolBase.C

  let HAS_SIZE_FUNSPACE ← prove
   r"!d n t:B->bool m s:A->bool.
        s HAS_SIZE m /\ t HAS_SIZE n
        ==> {f | (!x. x IN s ==> f(x) IN t) /\ (!x. ~(x IN s) ==> (f x = d))}
            HAS_SIZE (n EXP m)"
   (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC [HAS_SIZE_CLAUSES] THENL
     [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [NOT_IN_EMPTY, EXP] THEN
      CONV_TAC HAS_SIZE_CONV THEN EXISTS_TAC (← q r"(\x. d):A->B") THEN
      REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_SING] THEN REWRITE_TAC [FUN_EQ_THM],
      REWRITE_TAC [LEFT_IMP_EXISTS_THM, LEFT_AND_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC [← q r"s0:A->bool", ← q r"a:A", ← q r"s:A->bool"] THEN
    STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q r"s:A->bool")) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"{f:A->B | (!x. x IN a INSERT s ==> f x IN t) /\
                (!x. ~(x IN a INSERT s) ==> (f x = d))} =
      IMAGE (\(b,g) x. if x = a then b else g(x))
            {b,g | b IN t /\
                   g IN {f | (!x. x IN s ==> f x IN t) /\
                             (!x. ~(x IN s) ==> (f x = d))}}")
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_IMAGE, FORALL_PAIR_THM, IN_ELIM_THM,
                   EXISTS_PAIR_THM] THEN
      REWRITE_TAC [PAIR_EQ, CONJ_ASSOC, ← ONCE_REWRITE_RULE [CONJ_SYM]
       UNWIND_THM1] THEN
      X_GEN_TAC (← q r"f:A->B") THEN REWRITE_TAC [IN_INSERT] THEN EQ_TAC THENL
       [STRIP_TAC THEN MAP_EVERY EXISTS_TAC
         [← q r"(f:A->B) a", ← q r"\x. if x IN s then (f:A->B) x else d"] THEN
        REWRITE_TAC [FUN_EQ_THM] THEN ASM_MESON_TAC [],
        DISCH_THEN (X_CHOOSE_THEN (← q r"b:B") (X_CHOOSE_THEN (← q r"g:A->B")
          STRIP_ASSUME_TAC)) THEN
        ASM_REWRITE_TAC [] THEN ASM_MESON_TAC []],
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_SIMP_TAC [EXP, HAS_SIZE_PRODUCT] THEN
    REWRITE_TAC [FORALL_PAIR_THM, IN_ELIM_THM, PAIR_EQ, CONJ_ASSOC] THEN
    REWRITE_TAC [← ONCE_REWRITE_RULE [CONJ_SYM] UNWIND_THM1] THEN
    CONV_TAC (ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC [FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o SPEC (← q r"a:A")) THEN REWRITE_TAC [],
      X_GEN_TAC (← q r"x:A") THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:A")) THEN
      ASM_MESON_TAC []])

  let CARD_FUNSPACE ← prove
   r"!s t. FINITE s /\ FINITE t
         ==> (CARD {f:A->B | (!x. x IN s ==> f(x) IN t) /\
                             (!x. ~(x IN s) ==> (f x = d))} =
             (CARD t) EXP (CARD s))"
   (MESON_TAC [HAS_SIZE_FUNSPACE, HAS_SIZE])

  let FINITE_FUNSPACE ← prove
   r"!s t. FINITE s /\ FINITE t
         ==> FINITE {f:A->B | (!x. x IN s ==> f(x) IN t) /\
                              (!x. ~(x IN s) ==> (f x = d))}"
   (MESON_TAC [HAS_SIZE_FUNSPACE, HAS_SIZE])

  let HAS_SIZE_FUNSPACE_UNIV ← prove
   r"!m n. (:A) HAS_SIZE m /\ (:B) HAS_SIZE n ==> (:A->B) HAS_SIZE (n EXP m)"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (MP_TAC o MATCH_MP HAS_SIZE_FUNSPACE) THEN
    REWRITE_TAC [IN_UNIV, UNIV_GSPEC])

  let CARD_FUNSPACE_UNIV ← prove
   r"FINITE(:A) /\ FINITE(:B) ==> CARD(:A->B) = CARD(:B) EXP CARD(:A)"
   (MESON_TAC [HAS_SIZE_FUNSPACE_UNIV, HAS_SIZE])

  let FINITE_FUNSPACE_UNIV ← prove
   r"FINITE(:A) /\ FINITE(:B) ==> FINITE(:A->B)"
   (MESON_TAC [HAS_SIZE_FUNSPACE_UNIV, HAS_SIZE])

  /- Cardinality of type bool. -/

  let HAS_SIZE_BOOL ← prove
   r"(:bool) HAS_SIZE 2"
   (SUBGOAL_THEN (← q r"(:bool) = {F,T}") SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_UNIV, IN_INSERT] THEN CONV_TAC (fun t => (TAUT t).run),
      SIMP_TAC [HAS_SIZE, CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY, ARITH,
                IN_SING, NOT_IN_EMPTY]])

  let CARD_BOOL ← prove
   r"CARD(:bool) = 2"
   (MESON_TAC [HAS_SIZE_BOOL, HAS_SIZE])

  let FINITE_BOOL ← prove
   r"FINITE(:bool)"
   (MESON_TAC [HAS_SIZE_BOOL, HAS_SIZE])

  /- Hence cardinality of powerset. -/

  let HAS_SIZE_POWERSET ← prove
   r"!(s:A->bool) n. s HAS_SIZE n ==> {t | t SUBSET s} HAS_SIZE (2 EXP n)"
   (REPEAT STRIP_TAC THEN SUBGOAL_THEN
     (← q r"{t | t SUBSET s} =
      {f | (!x:A. x IN s ==> f(x) IN UNIV) /\ (!x. ~(x IN s) ==> (f x = F))}")
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_UNIV, SUBSET, IN, CONTRAPOS_THM],
      MATCH_MP_TAC HAS_SIZE_FUNSPACE THEN ASM_REWRITE_TAC [] THEN
      CONV_TAC HAS_SIZE_CONV THEN MAP_EVERY EXISTS_TAC [← q r"T", ← q r"F"] THEN
      REWRITE_TAC [EXTENSION, IN_UNIV, IN_INSERT, NOT_IN_EMPTY] THEN
      CONV_TAC (fun t => (TAUT t).run)])

  let CARD_POWERSET ← prove
   r"!s:A->bool. FINITE s ==> (CARD {t | t SUBSET s} = 2 EXP (CARD s))"
   (MESON_TAC [HAS_SIZE_POWERSET, HAS_SIZE])

  let FINITE_POWERSET ← prove
   r"!s:A->bool. FINITE s ==> FINITE {t | t SUBSET s}"
   (MESON_TAC [HAS_SIZE_POWERSET, HAS_SIZE])

  let FINITE_POWERSET_EQ ← prove
   r"!s:A->bool. FINITE {t | t SUBSET s} <=> FINITE s"
   (GEN_TAC THEN EQ_TAC THEN REWRITE_TAC [FINITE_POWERSET] THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"FINITE(IMAGE (\x:A. {x}) s)") MP_TAC THENL
     [FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
          FINITE_SUBSET)) THEN
      SIMP_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM, IN_SING],
      MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN
      SET_TAC []])

  let FINITE_RESTRICTED_SUBSETS ← prove
   r"!P s:A->bool. FINITE s ==> FINITE {t | t SUBSET s /\ P t}"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC (← q r"{t:A->bool | t SUBSET s}") THEN
    ASM_SIMP_TAC [FINITE_POWERSET] THEN SET_TAC [])

  let FINITE_UNIONS ← prove
   r"!s:(A->bool)->bool.
        FINITE(UNIONS s) <=> FINITE s /\ (!t. t IN s ==> FINITE t)"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"FINITE(s:(A->bool)->bool)") THEN
    ASM_SIMP_TAC [FINITE_FINITE_UNIONS] THEN
    DISCH_THEN (MP_TAC o MATCH_MP FINITE_POWERSET) THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [CONTRAPOS_THM] THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] FINITE_SUBSET) THEN SET_TAC [])

  let FINITE_CARD_LE_UNIONS ← prove
   r"!s (t:A->B->bool) m n.
        (!x. x IN s ==> FINITE(t x) /\ CARD(t x) <= n) /\
        FINITE s /\ CARD s <= m
        ==> FINITE(UNIONS {t x | x IN s}) /\
            CARD(UNIONS {t x | x IN s}) <= m * n"
   (REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [FINITE_UNIONS, FORALL_IN_GSPEC, FINITE_IMAGE, SIMPLE_IMAGE] THEN
    TRANS_TAC LE_TRANS (← q r"CARD(s:A->bool) * n") THEN
    ASM_REWRITE_TAC [← GSYM SIMPLE_IMAGE, LE_MULT_RCANCEL] THEN
    MATCH_MP_TAC CARD_UNIONS_LE THEN ASM_REWRITE_TAC [HAS_SIZE])

  let POWERSET_CLAUSES ← prove
   r"{s:A->bool | s SUBSET {}} = {{}} /\
   (!a:A t. {s | s SUBSET (a INSERT t)} =
            {s | s SUBSET t} UNION IMAGE (\s. a INSERT s) {s | s SUBSET t})"
   (REWRITE_TAC [SUBSET_INSERT_DELETE, SUBSET_EMPTY, SING_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:A", ← q r"t:A->bool"] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC [UNION_SUBSET] THEN
    ONCE_REWRITE_TAC [SUBSET] THEN
    REWRITE_TAC [FORALL_IN_IMAGE, FORALL_IN_GSPEC] THEN
    REWRITE_TAC [IN_ELIM_THM, IN_UNION, IN_IMAGE] THEN
    CONJ_TAC THENL [ALL_TAC, SET_TAC []] THEN
    X_GEN_TAC (← q r"s:A->bool") THEN
    ASM_CASES_TAC (← q r"(a:A) IN s") THENL [ALL_TAC, ASM SET_TAC []] THEN
    STRIP_TAC THEN DISJ2_TAC THEN EXISTS_TAC (← q r"s DELETE (a:A)") THEN
    ASM SET_TAC [])

  let FINITE_IMAGE_INFINITE ← prove
   r"!f:A->B s.
        INFINITE s /\ FINITE(IMAGE f s)
        ==> ?a. a IN s /\ INFINITE {x | x IN s /\ f x = f a}"
   (REPEAT GEN_TAC THEN REWRITE_TAC [IMP_CONJ_ALT] THEN DISCH_TAC THEN
    GEN_REWRITE_TAC I [← GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC [NOT_EXISTS_THM, INFINITE, ← TAUT (← q r"~(p /\ q) <=> p ==> ~q")] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN (← q r"s = UNIONS {{x | x IN s /\ (f:A->B) x = y} |y| y IN IMAGE f s}")
    SUBST1_TAC THENL [REWRITE_TAC [UNIONS_GSPEC] THEN SET_TAC [], ALL_TAC] THEN
    ASM_SIMP_TAC [FINITE_UNIONS, SIMPLE_IMAGE, FINITE_IMAGE, FORALL_IN_IMAGE])

  -- The three SET_RULEs run (and print) right to left, as in OCaml.
  let FINITE_RESTRICTED_POWERSET ← prove
   r"!(s:A->bool) n.
        FINITE {t | t SUBSET s /\ t HAS_SIZE n} <=>
        FINITE s \/ n = 0"
   (← do
    let r3 ← SET_RULE (← q r"P /\ x IN t <=> {x} SUBSET t /\ P")
    let r2 ← SET_RULE (← q r"{x | P x /\ Q x} = {x | x IN {y | P y} /\ Q x}")
    let r1 ← SET_RULE (← q r"t SUBSET s /\ t = {} <=> t = {}")
    pure
     (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [] THENL
       [REWRITE_TAC [HAS_SIZE_0, r1] THEN
        REWRITE_TAC [SING_GSPEC, FINITE_SING],
        ASM_CASES_TAC (← q r"FINITE(s:A->bool)") THEN ASM_REWRITE_TAC [] THENL
         [ONCE_REWRITE_TAC [r2] THEN
          ASM_SIMP_TAC [FINITE_RESTRICT, FINITE_POWERSET],
          DISCH_TAC THEN SUBGOAL_THEN (← q r"FINITE(s:A->bool)")
          MP_TAC THENL [ALL_TAC, ASM_REWRITE_TAC []] THEN
          MATCH_MP_TAC FINITE_SUBSET THEN
          EXISTS_TAC (← q r"UNIONS {t:A->bool | t SUBSET s /\ t HAS_SIZE n}") THEN
          CONJ_TAC THENL
           [ASM_SIMP_TAC [FINITE_UNIONS, FORALL_IN_GSPEC] THEN SIMP_TAC [HAS_SIZE],
            GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN
            REWRITE_TAC [UNIONS_GSPEC, IN_ELIM_THM] THEN
            ONCE_REWRITE_TAC [r3] THEN
            MATCH_MP_TAC CHOOSE_SUBSET_BETWEEN THEN
            ASM_REWRITE_TAC [SING_SUBSET, FINITE_SING, CARD_SING] THEN
            ASM_SIMP_TAC [LE_1]]]]))

  let FINITE_RESTRICTED_FUNSPACE ← prove
   r"!s:A->bool t:B->bool k.
        FINITE s /\ FINITE t
        ==> FINITE {f | IMAGE f s SUBSET t /\ {x | ~(f x = k x)} SUBSET s}"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     (← q r"IMAGE (\u:(A#B)->bool x. if ?y. (x,y) IN u then @y. (x,y) IN u else k x)
            {u | u SUBSET (s CROSS t)}") THEN
    ASM_SIMP_TAC [FINITE_POWERSET, FINITE_CROSS, FINITE_IMAGE] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC [FORALL_IN_GSPEC] THEN
    X_GEN_TAC (← q r"f:A->B") THEN STRIP_TAC THEN
    REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN
    EXISTS_TAC (← q r"IMAGE (\x. x,(f:A->B) x) {x | ~(f x = k x)}") THEN
    ASM_SIMP_TAC [FINITE_IMAGE] THEN CONJ_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM, IN_CROSS] THEN
      ASM SET_TAC []] THEN
    REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"x:A") THEN
    REWRITE_TAC [IN_IMAGE, IN_ELIM_THM, PAIR_EQ] THEN
    REWRITE_TAC [← GSYM CONJ_ASSOC, UNWIND_THM1, UNWIND_THM2] THEN
    ASM_CASES_TAC (← q r"(f:A->B) x = k x") THEN ASM_REWRITE_TAC [])

  return {
    HAS_SIZE_FUNSPACE, CARD_FUNSPACE, FINITE_FUNSPACE, HAS_SIZE_FUNSPACE_UNIV,
    CARD_FUNSPACE_UNIV, FINITE_FUNSPACE_UNIV, HAS_SIZE_BOOL, CARD_BOOL,
    FINITE_BOOL, HAS_SIZE_POWERSET, CARD_POWERSET, FINITE_POWERSET,
    FINITE_POWERSET_EQ, FINITE_RESTRICTED_SUBSETS, FINITE_UNIONS,
    FINITE_CARD_LE_UNIONS, POWERSET_CLAUSES, FINITE_IMAGE_INFINITE,
    FINITE_RESTRICTED_POWERSET, FINITE_RESTRICTED_FUNSPACE }

/- ---------------------------------------------------------------------- -/
/- The infinitude results.  (sets.ml 3554-3696)                           -/
/- ---------------------------------------------------------------------- -/

/-- The infinitude theorems of sets.ml 3554-3697.  Built on the num-segment
    HAS_SIZE reasoning of `SCard`, the `FINITE`/`FINITE_IMAGE_INJ_EQ` lemmas of
    `SFin`, `FINITE_INDUCT_STRONG` (`SInd`), the list `LENGTH`/`LENGTH_REPLICATE`
    of lists.ml and the real linear/field arithmetic (`REAL_ARITH`/`REAL_FIELD`/
    `REAL_ARITH_TAC`). -/
structure SetsInfinite where
  /-- `NUMSEG_CLAUSES_LT` (sets.ml 3557): `{i | i < 0} = {} /\ (!k. {i | i < SUC
      k} = k INSERT {i | i < k})`.  `REWRITE_TAC[LT] THEN SET_TAC[]`.  No
      top-level `THENL`. -/
  NUMSEG_CLAUSES_LT : thm
  /-- `HAS_SIZE_NUMSEG_LT` (sets.ml 3562): `{m | m < n} HAS_SIZE n`.
      `REWRITE_TAC[HAS_SIZE] THEN INDUCT_TAC THEN ASM_SIMP_TAC[..]`.  No
      top-level `THENL`. -/
  HAS_SIZE_NUMSEG_LT : thm
  /-- `CARD_NUMSEG_LT` (sets.ml 3568): `CARD {m | m < n} = n`.
      `REWRITE_TAC[REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_LT]`.  No `THENL`. -/
  CARD_NUMSEG_LT : thm
  /-- `FINITE_NUMSEG_LT` (sets.ml 3572): `FINITE {m | m < n}`.
      `REWRITE_TAC[REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_LT]`.  No `THENL`. -/
  FINITE_NUMSEG_LT : thm
  /-- `NUMSEG_CLAUSES_LE` (sets.ml 3576): `{i | i <= 0} = {0} /\ (!k. {i | i <=
      SUC k} = SUC k INSERT {i | i <= k})`.  `REWRITE_TAC[LE] THEN SET_TAC[]`.
      No top-level `THENL`. -/
  NUMSEG_CLAUSES_LE : thm
  /-- `HAS_SIZE_NUMSEG_LE` (sets.ml 3581): `{m | m <= n} HAS_SIZE (n + 1)`.
      `REWRITE_TAC[GSYM LT_SUC_LE; HAS_SIZE_NUMSEG_LT; ADD1]`.  No `THENL`. -/
  HAS_SIZE_NUMSEG_LE : thm
  /-- `FINITE_NUMSEG_LE` (sets.ml 3585): `FINITE {m | m <= n}`.
      `REWRITE_TAC[REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_LE]`.  No `THENL`. -/
  FINITE_NUMSEG_LE : thm
  /-- `CARD_NUMSEG_LE` (sets.ml 3589): `CARD {m | m <= n} = n + 1`.
      `REWRITE_TAC[REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_LE]`.  No `THENL`. -/
  CARD_NUMSEG_LE : thm
  /-- `num_FINITE` (sets.ml 3593): `FINITE s <=> ?a. !x. x IN s ==> x <= a`.
      `GEN_TAC THEN EQ_TAC THENL [b1; b2]` - ONE width-2 top-level `THENL`.
      b1: `SPEC_TAC` then `MATCH_MP_TAC FINITE_INDUCT_STRONG` then `MESON_TAC`;
      b2: `DISCH_THEN(X_CHOOSE_TAC ..)` then `MATCH_MP_TAC FINITE_SUBSET` with
      `EXISTS_TAC {m | m <= n}`. -/
  num_FINITE : thm
  /-- `num_FINITE_AVOID` (sets.ml 3603): `FINITE s ==> ?a. ~(a IN s)`.
      `MESON_TAC[num_FINITE; LT; NOT_LT]`.  No `THENL`. -/
  num_FINITE_AVOID : thm
  /-- `num_INFINITE_EQ` (sets.ml 3607): `INFINITE s <=> !N. ?n. N <= n /\ n IN
      s`.  `GEN_TAC THEN REWRITE_TAC[INFINITE; num_FINITE] THEN MESON_TAC[..]`.
      No `THENL`. -/
  num_INFINITE_EQ : thm
  /-- `num_INFINITE` (sets.ml 3612): `INFINITE(:num)`.
      `REWRITE_TAC[INFINITE] THEN MESON_TAC[num_FINITE_AVOID; IN_UNIV]`.  No
      `THENL`. -/
  num_INFINITE : thm
  /-- `string_INFINITE` (sets.ml 3620): `INFINITE(:string)`.  `MP_TAC
      num_INFINITE THEN REWRITE_TAC[INFINITE; CONTRAPOS_THM] THEN
      DISCH_THEN(MP_TAC o ISPEC `LENGTH:string->num` o MATCH_MP FINITE_IMAGE)
      THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[..] THEN
      MESON_TAC[LENGTH_REPLICATE]`.  No top-level `THENL`; the `o` chain
      `MP_TAC o ISPEC .. o MATCH_MP FINITE_IMAGE` is an explicit thm_tactic. -/
  string_INFINITE : thm
  /-- `FINITE_REAL_INTERVAL` (sets.ml 3631): the eight interval finiteness
      clauses.  TWO top-level `THENL`s: `SUBGOAL_THEN .. ASSUME_TAC THENL
      [big; ALL_TAC]` (width 2), then after `ASM_REWRITE_TAC[] THEN REPEAT
      CONJ_TAC THEN REPEAT GEN_TAC` a `THENL` with SEVEN branches (width 7 -
      one conjunct was already discharged by the SUBGOAL) with a common tail
      after.  `big` uses two `ASM_CASES_TAC`, `MP_TAC o MATCH_MP (REWRITE_RULE
      [T.IMP_CONJ] FINITE_SUBSET)`, `MP_TAC o SPEC`, `MP_TAC num_INFINITE`,
      `CONV_TAC SYM_CONV`, `MATCH_MP_TAC FINITE_IMAGE_INJ_EQ` and inline
      `REAL_ARITH`/`REAL_FIELD`; branches 1-4 close with `REAL_ARITH_TAC`,
      5-6 only rewrite, 7 does an `ASM_CASES_TAC` split. -/
  FINITE_REAL_INTERVAL : thm
  /-- `real_INFINITE` (sets.ml 3689): `INFINITE(:real)`.
      `REWRITE_TAC[INFINITE] THEN DISCH_THEN(MP_TAC o SPEC `{x | &0 <= x}` o
      MATCH_MP(REWRITE_RULE[T.IMP_CONJ] FINITE_SUBSET)) THEN
      REWRITE_TAC[FINITE_REAL_INTERVAL; SUBSET_UNIV]`.  No top-level `THENL`;
      the `o` chain is an explicit thm_tactic. -/
  real_INFINITE : thm
  deriving Inhabited

@[nospecialize]
def setupSetsInfinite [HolBase] (S : SetsCore)
    (P : SetsProps) (SIn : SetsInclusion) (SMi : SetsMisc)
    (SFin : SetsFinite) (SCard : SetsCard) (SInd : SetsInduct)
    (MESON_TAC : List thm → tactic)
    (INDUCT_TAC : tactic)
    (REAL_ARITH' : term → IO (Except String thm))
    (REAL_FIELD' : term → IO (Except String thm))
    (REAL_ARITH_TAC : tactic)
    (LT LE_thm ADD1 LT_SUC_LE NOT_LT LT_REFL : thm)
    (LE_CASES LE_TRANS NOT_LE LT_IMP_LE LE_SUC_LT : thm)
    (LENGTH_REPLICATE : thm)
    (REAL_NOT_LT REAL_LT_ADDR REAL_LT_DIV REAL_SUB_LT REAL_LT_LDIV_EQ
     REAL_LT_MUL REAL_OF_NUM_EQ REAL_LE_ANTISYM REAL_LE_REFL : thm) :
    ExceptT String IO SetsInfinite := do
  let SET_TAC := SET_TAC S P MESON_TAC
  let SET_RULE := SET_RULE S P MESON_TAC
  let REAL_ARITH (t : term) : ExceptT String IO thm := REAL_ARITH' t
  let REAL_FIELD (t : term) : ExceptT String IO thm := REAL_FIELD' t
  let LE := LE_thm
  let { EXTENSION, IN_ELIM_THM, SUBSET, INFINITE, .. } := S
  let { NOT_IN_EMPTY, IN_UNIV, IN_INSERT, IN_IMAGE, FORALL_IN_IMAGE, .. } := P
  let { SUBSET_UNIV, .. } := SIn
  let { EMPTY_GSPEC, SING_GSPEC, .. } := SMi
  let { FINITE_EMPTY, FINITE_SUBSET, FINITE_UNION, FINITE_INSERT, FINITE_SING,
        FINITE_IMAGE, FINITE_IMAGE_INJ_EQ, .. } := SFin
  let { CARD_CLAUSES, HAS_SIZE, .. } := SCard
  let { FINITE_INDUCT_STRONG, .. } := SInd
  let { IMP_CONJ, EQ_IMP, .. } := HolBase.T
  let { NOT_IMP, CONTRAPOS_THM, .. } := HolBase.C

  /- Set of numbers is infinite. -/

  let NUMSEG_CLAUSES_LT ← prove
   r"{i | i < 0} = {} /\
   (!k. {i | i < SUC k} = k INSERT {i | i < k})"
   (REWRITE_TAC [LT] THEN SET_TAC [])

  let HAS_SIZE_NUMSEG_LT ← prove
   r"!n. {m | m < n} HAS_SIZE n"
   (REWRITE_TAC [HAS_SIZE] THEN INDUCT_TAC THEN
    ASM_SIMP_TAC [NUMSEG_CLAUSES_LT, FINITE_EMPTY, CARD_CLAUSES, FINITE_INSERT,
                  IN_ELIM_THM, LT_REFL])

  let CARD_NUMSEG_LT ← prove
   r"!n. CARD {m | m < n} = n"
   (REWRITE_TAC [← REWRITE_RULE [HAS_SIZE] HAS_SIZE_NUMSEG_LT])

  let FINITE_NUMSEG_LT ← prove
   r"!n:num. FINITE {m | m < n}"
   (REWRITE_TAC [← REWRITE_RULE [HAS_SIZE] HAS_SIZE_NUMSEG_LT])

  let NUMSEG_CLAUSES_LE ← prove
   r"{i | i <= 0} = {0} /\
   (!k. {i | i <= SUC k} = SUC k INSERT {i | i <= k})"
   (REWRITE_TAC [LE] THEN SET_TAC [])

  let HAS_SIZE_NUMSEG_LE ← prove
   r"!n. {m | m <= n} HAS_SIZE (n + 1)"
   (REWRITE_TAC [← GSYM LT_SUC_LE, HAS_SIZE_NUMSEG_LT, ADD1])

  let FINITE_NUMSEG_LE ← prove
   r"!n. FINITE {m | m <= n}"
   (REWRITE_TAC [← REWRITE_RULE [HAS_SIZE] HAS_SIZE_NUMSEG_LE])

  let CARD_NUMSEG_LE ← prove
   r"!n. CARD {m | m <= n} = n + 1"
   (REWRITE_TAC [← REWRITE_RULE [HAS_SIZE] HAS_SIZE_NUMSEG_LE])

  let num_FINITE ← prove
   r"!s:num->bool. FINITE s <=> ?a. !x. x IN s ==> x <= a"
   (GEN_TAC THEN EQ_TAC THENL
     [SPEC_TAC (← q r"s:num->bool", ← q r"s:num->bool") THEN
      MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
      REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN MESON_TAC [LE_CASES, LE_TRANS],
      DISCH_THEN (X_CHOOSE_TAC (← q r"n:num")) THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC (← q r"{m:num | m <= n}") THEN REWRITE_TAC [FINITE_NUMSEG_LE] THEN
      ASM_SIMP_TAC [SUBSET, IN_ELIM_THM]])

  let num_FINITE_AVOID ← prove
   r"!s:num->bool. FINITE(s) ==> ?a. ~(a IN s)"
   (MESON_TAC [num_FINITE, LT, NOT_LT])

  let num_INFINITE_EQ ← prove
   r"!s:num->bool. INFINITE s <=> !N. ?n. N <= n /\ n IN s"
   (GEN_TAC THEN REWRITE_TAC [INFINITE, num_FINITE] THEN
    MESON_TAC [NOT_LE, LT_IMP_LE, LE_SUC_LT])

  let num_INFINITE ← prove
   r"INFINITE(:num)"
   (REWRITE_TAC [INFINITE] THEN MESON_TAC [num_FINITE_AVOID, IN_UNIV])

  /- Set of strings is infinite. -/

  let string_INFINITE ← prove
   r"INFINITE(:string)"
   (MP_TAC num_INFINITE THEN REWRITE_TAC [INFINITE, CONTRAPOS_THM] THEN
    DISCH_THEN (MP_TAC o ISPEC (← q r"LENGTH:string->num") o MATCH_MP FINITE_IMAGE) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, IN_UNIV, IN_IMAGE] THEN MESON_TAC [LENGTH_REPLICATE])

  /- Non-trivial intervals of reals are infinite. -/

  -- The rules run (and print) right to left, as in OCaml: the SET_RULE,
  -- then the REAL_ARITHs of the case list, then REAL_FIELD and the
  -- REAL_ARITHs of the subgoal's proof.
  let FINITE_REAL_INTERVAL ← prove
   r"(!a. ~FINITE {x:real | a < x}) /\
   (!a. ~FINITE {x:real | a <= x}) /\
   (!b. ~FINITE {x:real | x < b}) /\
   (!b. ~FINITE {x:real | x <= b}) /\
   (!a b. FINITE {x:real | a < x /\ x < b} <=> b <= a) /\
   (!a b. FINITE {x:real | a <= x /\ x < b} <=> b <= a) /\
   (!a b. FINITE {x:real | a < x /\ x <= b} <=> b <= a) /\
   (!a b. FINITE {x:real | a <= x /\ x <= b} <=> b <= a)"
   (← do
    let sr ← SET_RULE (← q r"{x | p x \/ q x} = {x | p x} UNION {x | q x}")
    let c7 ← REAL_ARITH
     (← q r"~(b:real = a) ==>
        (a <= x /\ x <= b <=> (a < x /\ x < b) \/ ~(b <= a) /\ x = a \/
        ~(b <= a) /\ x = b)")
    let c6 ← REAL_ARITH
     (← q r"a:real < x /\ x <= b <=> (a < x /\ x < b) \/ ~(b <= a) /\ x = b")
    let c5 ← REAL_ARITH
     (← q r"a:real <= x /\ x < b <=> (a < x /\ x < b) \/ ~(b <= a) /\ x = a")
    let rf ← REAL_FIELD
     (← q r"a < b ==> (a + (b - a) / (&n + &2) = a + (b - a) / (&m + &2) <=>
                 &n:real = &m)")
    let a5 ← REAL_ARITH (← q r"&0:real < &n + &1")
    let a4 ← REAL_ARITH (← q r"x:real < x * (n + &2) <=> &0 < x * (n + &1)")
    let a3 ← REAL_ARITH (← q r"&0:real < &n + &2")
    let a2 ← REAL_ARITH (← q r"a + x / y < b <=> x / y < b - a")
    let a1 ← REAL_ARITH (← q r"~(a:real < b) ==> ~(a < x /\ x < b)")
    pure
     (SUBGOAL_THEN (← q r"!a b. FINITE {x:real | a < x /\ x < b} <=> b <= a")
      ASSUME_TAC THENL
       [REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM REAL_NOT_LT] THEN
        ASM_CASES_TAC (← q r"a:real < b") THEN
        ASM_SIMP_TAC [a1] THEN
        REWRITE_TAC [EMPTY_GSPEC, FINITE_EMPTY] THEN
        DISCH_THEN (MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ] FINITE_SUBSET)) THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"IMAGE (\n. a + (b - a) / (&n + &2)) (:num)")) THEN
        REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_UNIV, IN_ELIM_THM] THEN
        SIMP_TAC [REAL_LT_ADDR, a2] THEN
        ASM_SIMP_TAC [REAL_LT_DIV, REAL_SUB_LT, REAL_LT_LDIV_EQ, NOT_IMP, a3] THEN
        REWRITE_TAC [a4] THEN
        ASM_SIMP_TAC [REAL_SUB_LT, REAL_LT_MUL, a5] THEN
        MP_TAC num_INFINITE THEN REWRITE_TAC [INFINITE] THEN
        MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN
        ASM_SIMP_TAC [REAL_OF_NUM_EQ, rf],
        ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
       [DISCH_THEN (MP_TAC o SPEC (← q r"{x:real | a < x /\ x < a + &1}") o
            MATCH_MP (← REWRITE_RULE [IMP_CONJ] FINITE_SUBSET)) THEN
        ASM_REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN REAL_ARITH_TAC,
        DISCH_THEN (MP_TAC o SPEC (← q r"{x:real | a < x /\ x < a + &1}") o
            MATCH_MP (← REWRITE_RULE [IMP_CONJ] FINITE_SUBSET)) THEN
        ASM_REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN REAL_ARITH_TAC,
        DISCH_THEN (MP_TAC o SPEC (← q r"{x:real | b - &1 < x /\ x < b}") o
            MATCH_MP (← REWRITE_RULE [IMP_CONJ] FINITE_SUBSET)) THEN
        ASM_REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN REAL_ARITH_TAC,
        DISCH_THEN (MP_TAC o SPEC (← q r"{x:real | b - &1 < x /\ x < b}") o
            MATCH_MP (← REWRITE_RULE [IMP_CONJ] FINITE_SUBSET)) THEN
        ASM_REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN REAL_ARITH_TAC,
        REWRITE_TAC [c5],
        REWRITE_TAC [c6],
        ASM_CASES_TAC (← q r"b:real = a") THEN
        ASM_SIMP_TAC [REAL_LE_ANTISYM, REAL_LE_REFL, SING_GSPEC, FINITE_SING] THEN
        ASM_SIMP_TAC [c7]] THEN
      ASM_REWRITE_TAC [FINITE_UNION, sr] THEN
      ASM_CASES_TAC (← q r"b:real <= a") THEN
      ASM_REWRITE_TAC [EMPTY_GSPEC, FINITE_EMPTY]))

  let real_INFINITE ← prove
   r"INFINITE(:real)"
   (REWRITE_TAC [INFINITE] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"{x:real | &0 <= x}") o
          MATCH_MP (← REWRITE_RULE [IMP_CONJ] FINITE_SUBSET)) THEN
    REWRITE_TAC [FINITE_REAL_INTERVAL, SUBSET_UNIV])

  return {
    NUMSEG_CLAUSES_LT, HAS_SIZE_NUMSEG_LT, CARD_NUMSEG_LT, FINITE_NUMSEG_LT,
    NUMSEG_CLAUSES_LE, HAS_SIZE_NUMSEG_LE, FINITE_NUMSEG_LE, CARD_NUMSEG_LE,
    num_FINITE, num_FINITE_AVOID, num_INFINITE_EQ, num_INFINITE,
    string_INFINITE, FINITE_REAL_INTERVAL, real_INFINITE }

/- ---------------------------------------------------------------------- -/
/- Finite-set indexing, set/list mappings, the pairwise property.         -/
/- (sets.ml 3697-3997)                                                    -/
/- ---------------------------------------------------------------------- -/

/- Mappings from finite set enumerations to lists (no "setification"). -/

/-- `dest_setenum` (sets.ml 3872). -/
def dest_setenum (tm : term) : Except String (List term) :=
  let (l, n) := splitlist (dest_binary "INSERT") tm
  if is_const n && (dest_const n).toOption.map Prod.fst == some "EMPTY" then .ok l
  else failwith "dest_setenum: not a finite set enumeration"

/-- `is_setenum = can dest_setenum` (sets.ml 3878). -/
def is_setenum (tm : term) : Bool := (dest_setenum tm).isOk

/-- `mk_setenum` (sets.ml 3880).  `insert_atm` and `nil_atm` are the parsed
    constants `(INSERT):A->(A->bool)->(A->bool)` and `(EMPTY):A->bool`
    (`SetsList.insert_atm`/`nil_atm`), instantiated at the element type. -/
def mk_setenum (insert_atm nil_atm : term) (lty : List term × hol_type) :
    IO (Except String term) := ExceptT.run do
  let (l, ty) := lty
  let aty := mk_vartype "A"
  let insert_tm := inst [(ty, aty)] insert_atm
  let nil_tm := inst [(ty, aty)] nil_atm
  liftExcept (itlist (fun x acc => do (← mk_binop insert_tm x) (← acc)) l (.ok nil_tm))

/-- `mk_fset l = mk_setenum(l,type_of(hd l))` (sets.ml 3886). -/
def mk_fset (insert_atm nil_atm : term) (l : List term) : IO (Except String term) := do
  match l with
  | [] => return failwith "hd"
  | h :: _ => mk_setenum insert_atm nil_atm (l, type_of h)

/-- The theorems of sets.ml 3697-3997, in three OCaml sections:

    * 3699-3786  indexing of finite sets and enumeration of subsets of N in
      order (`HAS_SIZE_INDEX`, `INFINITE_ENUMERATE`, `INFINITE_ENUMERATE_EQ`,
      `INFINITE_ENUMERATE_SUBSET`);
    * 3789-3868  the mapping between finite sets and lists.  `set_of_list`
      (`new_recursive_definition list_RECURSION`) and `list_of_set`
      (`new_definition`) ARE INTRODUCED HERE - they are NOT in Lists.lean - and
      the twelve theorems built on them;
    * 3893-3997  the `pairwise` relation (`new_definition`) and its seventeen
      theorems over sets and lists.

    The term utilities of sets.ml 3869-3886 (`dest_setenum`, `is_setenum`,
    `mk_setenum`, `mk_fset`) produce no theorem; they are defined before this
    bundle, as plain functions. -/
structure SetsList where
  /-- `mk_setenum`'s `(INSERT):A->(A->bool)->(A->bool)` (sets.ml 3881). -/
  insert_atm : term
  /-- `mk_setenum`'s `(EMPTY):A->bool` (sets.ml 3882). -/
  nil_atm : term
  /-- `HAS_SIZE_INDEX` (sets.ml 3700): `s HAS_SIZE n ==> ?f. (!m. m<n ==> f m IN
      s) /\ (!x. x IN s ==> ?!m. m<n /\ f m = x)`.  ONE top-level `CONJ_TAC
      THENL [b1; ALL_TAC]` (width 2); uses `CONJUNCTS_THEN2`, `COND_CASES_TAC`,
      `CONV_TAC(ONCE_DEPTH_CONV COND_ELIM_CONV)`, `ASM_CASES_TAC`. -/
  HAS_SIZE_INDEX : thm
  /-- `INFINITE_ENUMERATE` (sets.ml 3722): `INFINITE s ==> ?r:num->num. (!m n.
      m<n ==> r m < r n) /\ IMAGE r (:num) = s`.  Six top-level `THENL`s (all
      width 2), `prove_recursive_functions_exist num_RECURSION`, `num_WOP`,
      `num_MAX`, `num_WF`, inline `TAUT`/`ARITH_RULE`. -/
  INFINITE_ENUMERATE : thm
  /-- `INFINITE_ENUMERATE_EQ` (sets.ml 3758): the `<=>` form of
      `INFINITE_ENUMERATE`.  `MATCH_MP_TAC INFINITE_IMAGE`, `WLOG_LT`; the
      `STRIP_ASSUME_TAC o GSYM` runs `GSYM` first.  No top-level `THENL`. -/
  INFINITE_ENUMERATE_EQ : thm
  /-- `INFINITE_ENUMERATE_SUBSET` (sets.ml 3767): `INFINITE s <=> ?f:num->A.
      (!x. f x IN s) /\ (!x y. f x = f y ==> x = y)`.  `EQ_TAC..STRIP_TAC
      THENL [b1; b2]` (width 2); b1 has an inner width-2 `SUBGOAL_THEN`, uses
      `MATCH_MP_TAC(MATCH_MP WF_REC_EXISTS WF_num)` and a `MP_TAC o SPEC o
      MATCH_MP(REWRITE_RULE[T.IMP_CONJ] INFINITE_DIFF_FINITE)` chain (MATCH_MP
      first). -/
  INFINITE_ENUMERATE_SUBSET : thm
  /-- `set_of_list` (sets.ml 3790): `new_recursive_definition list_RECURSION`
      giving `set_of_list [] = {}` and `set_of_list (CONS h t) = h INSERT
      set_of_list t`.  DEFINED HERE, not in Lists.lean. -/
  set_of_list : thm
  /-- `list_of_set` (sets.ml 3794): `new_definition` `list_of_set s = @l.
      set_of_list l = s /\ LENGTH l = CARD s`.  DEFINED HERE, not in
      Lists.lean. -/
  list_of_set : thm
  /-- `LIST_OF_SET_PROPERTIES` (sets.ml 3797): `FINITE s ==> set_of_list
      (list_of_set s) = s /\ LENGTH (list_of_set s) = CARD s`.  ONE top-level
      `THENL` width 2 after `CONV_TAC(BINDER_CONV(RAND_CONV SELECT_CONV))` and
      `MATCH_MP_TAC FINITE_INDUCT_STRONG`. -/
  LIST_OF_SET_PROPERTIES : thm
  /-- `SET_OF_LIST_OF_SET` (sets.ml 3811): `FINITE s ==> set_of_list
      (list_of_set s) = s`.  `MESON_TAC[LIST_OF_SET_PROPERTIES]`. -/
  SET_OF_LIST_OF_SET : thm
  /-- `LENGTH_LIST_OF_SET` (sets.ml 3815): `FINITE s ==> LENGTH (list_of_set s)
      = CARD s`.  `MESON_TAC[LIST_OF_SET_PROPERTIES]`. -/
  LENGTH_LIST_OF_SET : thm
  /-- `MEM_LIST_OF_SET` (sets.ml 3819): `FINITE s ==> !x. MEM x (list_of_set s)
      <=> x IN s`.  `DISCH_THEN(MP_TAC o MATCH_MP SET_OF_LIST_OF_SET)` then
      `DISCH_THEN(fun th -> GEN_REWRITE_TAC (BINDER_CONV o funpow 2 RAND_CONV)
      [GSYM th])`, `SPEC_TAC`, `LIST_INDUCT_TAC`.  No top-level `THENL`. -/
  MEM_LIST_OF_SET : thm
  /-- `FINITE_SET_OF_LIST` (sets.ml 3828): `FINITE (set_of_list l)`.
      `LIST_INDUCT_TAC THEN ASM_SIMP_TAC[set_of_list; FINITE_RULES]`. -/
  FINITE_SET_OF_LIST : thm
  /-- `IN_SET_OF_LIST` (sets.ml 3832): `x IN set_of_list l <=> MEM x l`.
      `GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[..] THEN ASM_MESON_TAC[]`. -/
  IN_SET_OF_LIST : thm
  /-- `SET_OF_LIST_APPEND` (sets.ml 3838): `set_of_list (APPEND l1 l2) =
      set_of_list l1 UNION set_of_list l2`.  One-liner `REWRITE_TAC[EXTENSION;
      IN_SET_OF_LIST; IN_UNION; MEM_APPEND]`. -/
  SET_OF_LIST_APPEND : thm
  /-- `SET_OF_LIST_MAP` (sets.ml 3843): `set_of_list (MAP f l) = IMAGE f
      (set_of_list l)`.  `GEN_TAC THEN LIST_INDUCT_TAC THEN
      ASM_REWRITE_TAC[set_of_list; MAP; IMAGE_CLAUSES]`. -/
  SET_OF_LIST_MAP : thm
  /-- `SET_OF_LIST_EQ_EMPTY` (sets.ml 3848): `set_of_list l = {} <=> l = []`.
      `LIST_INDUCT_TAC THEN REWRITE_TAC[..]`. -/
  SET_OF_LIST_EQ_EMPTY : thm
  /-- `LIST_OF_SET_EMPTY` (sets.ml 3853): `list_of_set {} = []`.
      `REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN SIMP_TAC[LENGTH_LIST_OF_SET;
      FINITE_EMPTY; CARD_CLAUSES]`. -/
  LIST_OF_SET_EMPTY : thm
  /-- `LIST_OF_SET_SING` (sets.ml 3858): `list_of_set {a} = [a]`.
      `MATCH_MP_TAC SELECT_UNIQUE` then `MATCH_MP_TAC list_INDUCT`, an inner
      `LIST_INDUCT_TAC`, `DISCH_THEN(K ALL_TAC)`, closing `SET_TAC[]`.  No
      top-level `THENL`. -/
  LIST_OF_SET_SING : thm
  /-- `pairwise` (sets.ml 3894): `new_definition` `pairwise r s <=> !x y. x IN s
      /\ y IN s /\ ~(x=y) ==> r x y`. -/
  pairwise : thm
  /-- `PAIRWISE_EMPTY` (sets.ml 3897): `pairwise r {} <=> T`.
      `REWRITE_TAC[pairwise; NOT_IN_EMPTY] THEN MESON_TAC[]`. -/
  PAIRWISE_EMPTY : thm
  /-- `PAIRWISE_SING` (sets.ml 3901): `pairwise r {x} <=> T`.
      `REWRITE_TAC[pairwise; IN_SING] THEN MESON_TAC[]`. -/
  PAIRWISE_SING : thm
  /-- `PAIRWISE_IMP` (sets.ml 3905): `pairwise P s /\ (!x y. ... ==> Q x y) ==>
      pairwise Q s`.  `REWRITE_TAC[pairwise] THEN SET_TAC[]`. -/
  PAIRWISE_IMP : thm
  /-- `PAIRWISE_MONO` (sets.ml 3912): `pairwise r s /\ t SUBSET s ==> pairwise r
      t`.  `REWRITE_TAC[pairwise] THEN SET_TAC[]`. -/
  PAIRWISE_MONO : thm
  /-- `PAIRWISE_AND` (sets.ml 3916): `pairwise R s /\ pairwise R' s <=> pairwise
      (\x y. R x y /\ R' x y) s`.  `REWRITE_TAC[pairwise] THEN SET_TAC[]`. -/
  PAIRWISE_AND : thm
  /-- `PAIRWISE_INSERT` (sets.ml 3921): `pairwise r (x INSERT s) <=> (!y. y IN s
      /\ ~(y=x) ==> r x y /\ r y x) /\ pairwise r s`.
      `REWRITE_TAC[pairwise; IN_INSERT] THEN MESON_TAC[]`. -/
  PAIRWISE_INSERT : thm
  /-- `PAIRWISE_INSERT_SYMMETRIC` (sets.ml 3928): symmetric-relation variant of
      `PAIRWISE_INSERT`.  `REWRITE_TAC[PAIRWISE_INSERT] THEN MESON_TAC[]`. -/
  PAIRWISE_INSERT_SYMMETRIC : thm
  /-- `PAIRWISE_IMAGE` (sets.ml 3935): `pairwise r (IMAGE f s) <=> pairwise (\x
      y. ~(f x = f y) ==> r (f x) (f y)) s`.  `REWRITE_TAC[pairwise; IN_IMAGE]
      THEN MESON_TAC[]`. -/
  PAIRWISE_IMAGE : thm
  /-- `PAIRWISE_UNION` (sets.ml 3941): `pairwise R (s UNION t) <=> pairwise R s
      /\ pairwise R t /\ (!x y. x IN s DIFF t /\ y IN t DIFF s ==> R x y /\ R y
      x)`.  `REWRITE_TAC[pairwise] THEN SET_TAC[]`. -/
  PAIRWISE_UNION : thm
  /-- `PAIRWISE_CHAIN_UNIONS` (sets.ml 3947): a chain of `pairwise R` sets has
      `pairwise R (UNIONS c)`.  `REWRITE_TAC[pairwise] THEN SET_TAC[]`. -/
  PAIRWISE_CHAIN_UNIONS : thm
  /-- `DIFF_UNIONS_PAIRWISE_DISJOINT` (sets.ml 3954): for `pairwise DISJOINT s`
      and `t SUBSET s`, `UNIONS s DIFF UNIONS t = UNIONS (s DIFF t)`.
      `MATCH_MP_TAC(SET_RULE ...) THEN CONJ_TAC THENL [b1; b2]` (width 2). -/
  DIFF_UNIONS_PAIRWISE_DISJOINT : thm
  /-- `INTER_UNIONS_PAIRWISE_DISJOINT` (sets.ml 3968): for `pairwise DISJOINT (s
      UNION t)`, `UNIONS s INTER UNIONS t = UNIONS (s INTER t)`.  TWO top-level
      `THENL`s (`EQ_TAC` width 2, then an inner `ASM_CASES_TAC` width 2). -/
  INTER_UNIONS_PAIRWISE_DISJOINT : thm
  /-- `PSUBSET_UNIONS_PAIRWISE_DISJOINT` (sets.ml 3983): for `pairwise DISJOINT
      v` and `u PSUBSET (v DELETE {})`, `UNIONS u PSUBSET UNIONS v`.
      `CONJ_TAC THENL [b1; ALL_TAC]` (width 2), `W(MP_TAC o PART_MATCH (lhand o
      rand) DIFF_UNIONS_PAIRWISE_DISJOINT o lhand o rand o snd)`, `ANTS_TAC
      THENL [b1; b2]` (width 2). -/
  PSUBSET_UNIONS_PAIRWISE_DISJOINT : thm
  deriving Inhabited

@[nospecialize]
def setupSetsList [HolBase] (S : SetsCore)
    (P : SetsProps) (SIn : SetsInclusion) (SUn : SetsUnions) (SIm : SetsImage)
    (SID : SetsInsertDelete)
    (SInd : SetsInduct) (SFin : SetsFinite) (SCard : SetsCard)
    (SInf : SetsInfinite) (Nm : HolMath.Nums.NumsThms)
    (Ar4 : HolMath.Arith.ArithThms4) (Wf : HolMath.Wf.WfThms)
    (MESON_TAC : List thm → tactic) (ASM_MESON_TAC : List thm → tactic)
    (INDUCT_TAC : tactic)
    (list_INDUCT list_INDUCT' list_RECURSION : thm)
    (LENGTH MEM MAP : thm)
    (NOT_CONS_NIL CONS_11 LENGTH_EQ_NIL MEM_APPEND : thm)
    (LT LT_IMP_LE LE_LT LE_ANTISYM NOT_LT NOT_LE LE_0 LT_REFL : thm)
    (SUC_INJ NOT_SUC : thm)
    (ARITH_RULE' : term → IO (Except String thm))
    (prove_recursive_functions_exist' : thm → term → IO (Except String thm))
    (COND_ELIM_CONV : ioconv)
    (SELECT_CONV' : term → Except String thm)
    (new_recursive_definition' : thm → term → IO (Except String thm))
    (new_definition' : term → IO (Except String thm)) :
    ExceptT String IO SetsList := do
  let SET_TAC := SET_TAC S P MESON_TAC
  let SET_RULE := SET_RULE S P MESON_TAC
  let ARITH_RULE (t : term) : ExceptT String IO thm := ARITH_RULE' t
  let prove_recursive_functions_exist (ax : thm) (t : term) : ExceptT String IO thm :=
    prove_recursive_functions_exist' ax t
  let SELECT_CONV : ioconv := fun t => pure (SELECT_CONV' t)
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let new_recursive_definition (ax : thm) (s : String) : ExceptT String IO thm := do
    new_recursive_definition' ax (← q s)
  let LIST_INDUCT_TAC := HolMath.Lists.LIST_INDUCT_TAC list_INDUCT'
  let { num_RECURSION, .. } := Nm
  let { num_MAX, num_WF, num_WOP, WLOG_LT, .. } := Ar4
  let { WF_num, WF_REC_EXISTS, .. } := Wf
  let { EXTENSION, IN_ELIM_THM, SUBSET, DISJOINT, FINITE_RULES, INFINITE, .. } := S
  let { NOT_IN_EMPTY, IN_UNIV, IN_UNION, IN_UNIONS, IN_INTER, IN_DIFF,
        IN_INSERT, IN_DELETE, IN_SING, IN_IMAGE, FORALL_IN_IMAGE,
        FORALL_IN_GSPEC, UNIONS_IMAGE, .. } := P
  let { SUBSET_ANTISYM_EQ, PSUBSET_ALT, .. } := SIn
  let { EMPTY_UNIONS, INTER_UNIONS, UNIONS_UNION, .. } := SUn
  let { IMAGE_CLAUSES, SIMPLE_IMAGE, .. } := SIm
  let { NOT_INSERT_EMPTY, .. } := SID
  let { FINITE_INDUCT_STRONG, .. } := SInd
  let { FINITE_EMPTY, FINITE_IMAGE, INFINITE_IMAGE, INFINITE_IMAGE_INJ,
        INFINITE_NONEMPTY, INFINITE_DIFF_FINITE, INFINITE_SUPERSET, .. } := SFin
  let { CARD_CLAUSES, HAS_SIZE_0, HAS_SIZE_SUC, .. } := SCard
  let { FINITE_NUMSEG_LT, num_FINITE, num_INFINITE, .. } := SInf
  let { IMP_CONJ, SWAP_FORALL_THM, FORALL_AND_THM, RIGHT_AND_EXISTS_THM,
        LEFT_IMP_EXISTS_THM, MONO_EXISTS, .. } := HolBase.T
  let { SELECT_UNIQUE, NOT_FORALL_THM, SKOLEM_THM, .. } := HolBase.C

  /- Indexing of finite sets and enumeration of subsets of N in order. -/

  let HAS_SIZE_INDEX ← prove
   r"!s n. s HAS_SIZE n
         ==> ?f:num->A. (!m. m < n ==> f(m) IN s) /\
                        (!x. x IN s ==> ?!m. m < n /\ (f m = x))"
   (ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN INDUCT_TAC THEN
    SIMP_TAC [HAS_SIZE_0, HAS_SIZE_SUC, LT, NOT_IN_EMPTY] THEN
    X_GEN_TAC (← q r"s:A->bool") THEN REWRITE_TAC [EXTENSION, NOT_IN_EMPTY] THEN
    REWRITE_TAC [NOT_FORALL_THM] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"a:A")) (MP_TAC o SPEC (← q r"a:A"))) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"s DELETE (a:A)")) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"f:num->A") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"\m:num. if m < n then f(m) else a:A") THEN CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC [] THEN COND_CASES_TAC THEN
      ASM_MESON_TAC [IN_DELETE], ALL_TAC] THEN
    X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:A")) THEN
    ASM_REWRITE_TAC [IN_DELETE] THEN
    CONV_TAC (ONCE_DEPTH_CONV COND_ELIM_CONV) THEN
    ASM_CASES_TAC (← q r"a:A = x") THEN ASM_SIMP_TAC [] THEN
    ASM_MESON_TAC [LT_REFL, IN_DELETE])

  let INFINITE_ENUMERATE ← prove
   r"!s:num->bool.
       INFINITE s
       ==> ?r:num->num. (!m n. m < n ==> r(m) < r(n)) /\
                        IMAGE r (:num) = s"
   (← do
    let a2 ← ARITH_RULE (← q r"r < p <=> r + 1 <= p")
    let t3 ← TAUT
       (← q r"p /\ (q ==> r) ==> (p <=> q) ==> r")
    let a1 ← ARITH_RULE (← q r"m <= n /\ n + 1 <= p ==> m < p")
    let t2 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    let prfe ← prove_recursive_functions_exist num_RECURSION
     (← q r"(f(0) = next 0) /\ (!n. f(SUC n) = next(f n + 1))")
    let t1 ← TAUT (← q r"p ==> ~(q /\ r) <=> q /\ p ==> ~r")
    pure
      (REPEAT STRIP_TAC THEN
       SUBGOAL_THEN (← q r"!n:num. ?x. n <= x /\ x IN s") MP_TAC THENL
        [ASM_MESON_TAC [INFINITE, num_FINITE, LT_IMP_LE, NOT_LE],
         GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [num_WOP]] THEN
       REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM, FORALL_AND_THM] THEN
       REWRITE_TAC [t1] THEN
       X_GEN_TAC (← q r"next:num->num") THEN STRIP_TAC THEN
       MP_TAC prfe THEN
       MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"r:num->num") THEN STRIP_TAC THEN
       MATCH_MP_TAC t2 THEN CONJ_TAC THENL
        [GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [LT] THEN
         ASM_MESON_TAC [a1, LE_LT],
         DISCH_TAC] THEN
       ASM_REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ, FORALL_IN_IMAGE, SUBSET] THEN
       REWRITE_TAC [IN_IMAGE, IN_UNIV] THEN CONJ_TAC THENL
        [INDUCT_TAC THEN ASM_MESON_TAC [], ALL_TAC] THEN
       MATCH_MP_TAC num_WF THEN X_GEN_TAC (← q r"n:num") THEN REPEAT STRIP_TAC THEN
       ASM_CASES_TAC (← q r"?m:num. m < n /\ m IN s") THENL
        [MP_TAC (← SPEC (← q r"\m:num. m < n /\ m IN s") num_MAX) THEN
         ASM_REWRITE_TAC [] THEN MATCH_MP_TAC t3 THEN
         CONJ_TAC THENL [MESON_TAC [LT_IMP_LE], ALL_TAC] THEN
         DISCH_THEN (X_CHOOSE_THEN (← q r"p:num") STRIP_ASSUME_TAC) THEN
         SUBGOAL_THEN (← q r"?q. p = (r:num->num) q") (CHOOSE_THEN SUBST_ALL_TAC) THENL
          [ASM_MESON_TAC [], EXISTS_TAC (← q r"SUC q")] THEN
         ASM_REWRITE_TAC [← GSYM LE_ANTISYM, ← GSYM NOT_LT] THEN
         ASM_MESON_TAC [NOT_LE, a2],
         EXISTS_TAC (← q r"0") THEN ASM_REWRITE_TAC [← GSYM LE_ANTISYM, ← GSYM NOT_LT] THEN
         ASM_MESON_TAC [LE_0]]))

  let INFINITE_ENUMERATE_EQ ← prove
   r"!s:num->bool.
     INFINITE s <=> ?r. (!m n:num. m < n ==> r m < r n) /\ IMAGE r (:num) = s"
   (GEN_TAC THEN EQ_TAC THEN REWRITE_TAC [INFINITE_ENUMERATE] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"r:num->num") (STRIP_ASSUME_TAC o GSYM)) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC INFINITE_IMAGE THEN
    REWRITE_TAC [num_INFINITE, IN_UNIV] THEN
    MATCH_MP_TAC WLOG_LT THEN ASM_MESON_TAC [LT_REFL])

  let INFINITE_ENUMERATE_SUBSET ← prove
   r"!s. INFINITE s <=>
       ?f:num->A. (!x. f x IN s) /\ (!x y. f x = f y ==> x = y)"
   (GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
     [SUBGOAL_THEN (← q r"?f:num->A. !n. f n IN s /\ !m. m < n ==> ~(f m = f n)")
      MP_TAC THENL
       [MATCH_MP_TAC (← MATCH_MP WF_REC_EXISTS WF_num) THEN SIMP_TAC [] THEN
        MAP_EVERY X_GEN_TAC [← q r"f:num->A", ← q r"n:num"] THEN STRIP_TAC THEN
        FIRST_ASSUM (MP_TAC o SPEC (← q r"IMAGE (f:num->A) {m | m < n}") o
          MATCH_MP (← REWRITE_RULE [IMP_CONJ] INFINITE_DIFF_FINITE)) THEN
        SIMP_TAC [FINITE_IMAGE, FINITE_NUMSEG_LT] THEN
        DISCH_THEN (MP_TAC o MATCH_MP INFINITE_NONEMPTY) THEN SET_TAC [],
        MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
        ASM_REWRITE_TAC [] THEN MATCH_MP_TAC WLOG_LT THEN ASM SET_TAC []],
       MATCH_MP_TAC INFINITE_SUPERSET THEN
       EXISTS_TAC (← q r"IMAGE (f:num->A) (:num)") THEN
       ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
       ASM_MESON_TAC [INFINITE_IMAGE_INJ, num_INFINITE]])

  /- Mapping between finite sets and lists. -/

  let set_of_list ← new_recursive_definition list_RECURSION
   r"(set_of_list ([]:A list) = {}) /\
   (set_of_list (CONS (h:A) t) = h INSERT (set_of_list t))"

  let list_of_set ← new_definition
   r"list_of_set s = @l:A list. set_of_list l = s /\ LENGTH l = CARD s"

  let LIST_OF_SET_PROPERTIES ← prove
   r"!s:A->bool. FINITE(s)
               ==> (set_of_list(list_of_set s) = s) /\
                   (LENGTH(list_of_set s) = CARD s)"
   (REWRITE_TAC [list_of_set] THEN
    CONV_TAC (BINDER_CONV (RAND_CONV SELECT_CONV)) THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REPEAT STRIP_TAC THENL
     [EXISTS_TAC (← q r"[]:A list") THEN REWRITE_TAC [CARD_CLAUSES, LENGTH, set_of_list],
      EXISTS_TAC (← q r"CONS (x:A) l") THEN ASM_REWRITE_TAC [LENGTH] THEN
      ASM_REWRITE_TAC [set_of_list] THEN
      FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC
       [← MATCH_MP (← CONJUNCT2 CARD_CLAUSES) th])) THEN
      ASM_REWRITE_TAC []])

  let SET_OF_LIST_OF_SET ← prove
   r"!s:A->bool. FINITE(s) ==> (set_of_list(list_of_set s) = s)"
   (MESON_TAC [LIST_OF_SET_PROPERTIES])

  let LENGTH_LIST_OF_SET ← prove
   r"!s:A->bool. FINITE(s) ==> (LENGTH(list_of_set s) = CARD s)"
   (MESON_TAC [LIST_OF_SET_PROPERTIES])

  let MEM_LIST_OF_SET ← prove
   r"!s:A->bool. FINITE(s) ==> !x. MEM x (list_of_set s) <=> x IN s"
   (GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP SET_OF_LIST_OF_SET) THEN
    DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC (BINDER_CONV o funpow 2 RAND_CONV)
      [← GSYM th])) THEN
    SPEC_TAC (← q r"list_of_set(s:A->bool)", ← q r"l:A list") THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [MEM, set_of_list, NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC [IN_INSERT])

  let FINITE_SET_OF_LIST ← prove
   r"!l:A list. FINITE(set_of_list l)"
   (LIST_INDUCT_TAC THEN ASM_SIMP_TAC [set_of_list, FINITE_RULES])

  let IN_SET_OF_LIST ← prove
   r"!x l:A list. x IN (set_of_list l) <=> MEM x l"
   (GEN_TAC THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY, MEM, set_of_list] THEN
    ASM_MESON_TAC [])

  let SET_OF_LIST_APPEND ← prove
   r"!l1 l2:A list.
        set_of_list(APPEND l1 l2) = set_of_list(l1) UNION set_of_list(l2)"
   (REWRITE_TAC [EXTENSION, IN_SET_OF_LIST, IN_UNION, MEM_APPEND])

  let SET_OF_LIST_MAP ← prove
   r"!(f:A->B) l. set_of_list(MAP f l) = IMAGE f (set_of_list l)"
   (GEN_TAC THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [set_of_list, MAP, IMAGE_CLAUSES])

  let SET_OF_LIST_EQ_EMPTY ← prove
   r"!l:A list. set_of_list l = {} <=> l = []"
   (LIST_INDUCT_TAC THEN
    REWRITE_TAC [set_of_list, NOT_CONS_NIL, NOT_INSERT_EMPTY])

  let LIST_OF_SET_EMPTY ← prove
   r"list_of_set {}:A list = []"
   (REWRITE_TAC [← GSYM LENGTH_EQ_NIL] THEN
    SIMP_TAC [LENGTH_LIST_OF_SET, FINITE_EMPTY, CARD_CLAUSES])

  let LIST_OF_SET_SING ← prove
   r"!a:A. list_of_set {a} = [a]"
   (GEN_TAC THEN REWRITE_TAC [list_of_set] THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [NOT_CONS_NIL] THEN
    SIMP_TAC [LENGTH, CARD_CLAUSES, FINITE_EMPTY, NOT_IN_EMPTY, NOT_SUC] THEN
    GEN_TAC THEN LIST_INDUCT_TAC THEN DISCH_THEN (K ALL_TAC : thm → tactic) THEN
    SIMP_TAC [LENGTH, set_of_list, CONS_11, SUC_INJ, NOT_CONS_NIL, NOT_SUC] THEN
    SET_TAC [])

  -- mk_setenum (sets.ml 3880-3882): its two constants, parsed once.
  let insert_atm ← q r"(INSERT):A->(A->bool)->(A->bool)"
  let nil_atm ← q r"(EMPTY):A->bool"

  /- Pairwise property over sets and lists. -/

  let pairwise ← new_definition
   r"pairwise r (s:A->bool) <=> !x y. x IN s /\ y IN s /\ ~(x = y) ==> r x y"

  let PAIRWISE_EMPTY ← prove
   r"!r:A->A->bool. pairwise r {} <=> T"
   (REWRITE_TAC [pairwise, NOT_IN_EMPTY] THEN MESON_TAC [])

  let PAIRWISE_SING ← prove
   r"!r x:A. pairwise r {x} <=> T"
   (REWRITE_TAC [pairwise, IN_SING] THEN MESON_TAC [])

  let PAIRWISE_IMP ← prove
   r"!P Q s:A->bool.
        pairwise P s /\
        (!x y. x IN s /\ y IN s /\ P x y /\ ~(x = y) ==> Q x y)
        ==> pairwise Q s"
   (REWRITE_TAC [pairwise] THEN SET_TAC [])

  let PAIRWISE_MONO ← prove
   r"!(r:A->A->bool) s t. pairwise r s /\ t SUBSET s ==> pairwise r t"
   (REWRITE_TAC [pairwise] THEN SET_TAC [])

  let PAIRWISE_AND ← prove
   r"!R R' s. pairwise R s /\ pairwise R' s <=>
            pairwise (\x y:A. R x y /\ R' x y) s"
   (REWRITE_TAC [pairwise] THEN SET_TAC [])

  let PAIRWISE_INSERT ← prove
   r"!r x s.
        pairwise r (x INSERT s) <=>
        (!y:A. y IN s /\ ~(y = x) ==> r x y /\ r y x) /\
        pairwise r s"
   (REWRITE_TAC [pairwise, IN_INSERT] THEN MESON_TAC [])

  let PAIRWISE_INSERT_SYMMETRIC ← prove
   r"!r (x:A) s.
        (!y. y IN s ==> (r x y <=> r y x))
        ==> (pairwise r (x INSERT s) <=>
             (!y. y IN s /\ ~(y = x) ==> r x y) /\ pairwise r s)"
   (REWRITE_TAC [PAIRWISE_INSERT] THEN MESON_TAC [])

  let PAIRWISE_IMAGE ← prove
   r"!r (f:A->B).
        pairwise r (IMAGE f s) <=>
        pairwise (\x y. ~(f x = f y) ==> r (f x) (f y)) s"
   (REWRITE_TAC [pairwise, IN_IMAGE] THEN MESON_TAC [])

  let PAIRWISE_UNION ← prove
   r"!R s t. pairwise R (s UNION t) <=>
           pairwise R s /\ pairwise R t /\
           (!x y:A. x IN s DIFF t /\ y IN t DIFF s ==> R x y /\ R y x)"
   (REWRITE_TAC [pairwise] THEN SET_TAC [])

  let PAIRWISE_CHAIN_UNIONS ← prove
   r"!R:A->A->bool c.
        (!s. s IN c ==> pairwise R s) /\
        (!s t. s IN c /\ t IN c ==> s SUBSET t \/ t SUBSET s)
        ==> pairwise R (UNIONS c)"
   (REWRITE_TAC [pairwise] THEN SET_TAC [])

  let DIFF_UNIONS_PAIRWISE_DISJOINT ← prove
   r"!s t:(A->bool)->bool.
        pairwise DISJOINT s /\ t SUBSET s
        ==> UNIONS s DIFF UNIONS t = UNIONS(s DIFF t)"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (← SET_RULE (← q r"t UNION u = s /\ DISJOINT t u ==> s DIFF t = u")) THEN
    CONJ_TAC THENL
     [REWRITE_TAC [← GSYM UNIONS_UNION] THEN AP_TERM_TAC THEN ASM SET_TAC [],
      REWRITE_TAC [DISJOINT, INTER_UNIONS, EMPTY_UNIONS, FORALL_IN_GSPEC] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [pairwise]) THEN
      REWRITE_TAC [DISJOINT, IN_DIFF] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      REPEAT (CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC]) THEN ASM_MESON_TAC []])

  let INTER_UNIONS_PAIRWISE_DISJOINT ← prove
   r"!s t:(A->bool)->bool.
        pairwise DISJOINT (s UNION t)
        ==> UNIONS s INTER UNIONS t = UNIONS(s INTER t)"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [INTER_UNIONS, SIMPLE_IMAGE, UNIONS_IMAGE] THEN
    GEN_REWRITE_TAC RAND_CONV [EXTENSION] THEN
    REWRITE_TAC [pairwise, IN_UNIONS, IN_INTER, IN_ELIM_THM, IN_UNION] THEN
    DISCH_TAC THEN X_GEN_TAC (← q r"z:A") THEN REWRITE_TAC [RIGHT_AND_EXISTS_THM] THEN
    EQ_TAC THENL [REWRITE_TAC [LEFT_IMP_EXISTS_THM], MESON_TAC []] THEN
    MAP_EVERY X_GEN_TAC [← q r"u:A->bool", ← q r"v:A->bool"] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"u:A->bool", ← q r"v:A->bool"]) THEN
    ASM_CASES_TAC (← q r"u:A->bool = v") THEN ASM_REWRITE_TAC [] THENL
     [ASM_MESON_TAC [], ASM SET_TAC []])

  let PSUBSET_UNIONS_PAIRWISE_DISJOINT ← prove
   r"!u v:(A->bool)->bool.
        pairwise DISJOINT v /\ u PSUBSET (v DELETE {})
        ==> UNIONS u PSUBSET UNIONS v"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (← SET_RULE (← q r"u SUBSET v /\ ~(v DIFF u = {}) ==> u PSUBSET v")) THEN
    CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    W (MP_TAC o PART_MATCH (lhand o rand)
        DIFF_UNIONS_PAIRWISE_DISJOINT o lhand o rand o snd) THEN
    ANTS_TAC THENL [ASM SET_TAC [], DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC [EMPTY_UNIONS] THEN
    FIRST_ASSUM (MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [PSUBSET_ALT]) THEN
    REWRITE_TAC [IN_DELETE, IN_DIFF] THEN MESON_TAC [])

  return {
    insert_atm, nil_atm,
    HAS_SIZE_INDEX, INFINITE_ENUMERATE, INFINITE_ENUMERATE_EQ,
    INFINITE_ENUMERATE_SUBSET, set_of_list, list_of_set,
    LIST_OF_SET_PROPERTIES, SET_OF_LIST_OF_SET, LENGTH_LIST_OF_SET,
    MEM_LIST_OF_SET, FINITE_SET_OF_LIST, IN_SET_OF_LIST, SET_OF_LIST_APPEND,
    SET_OF_LIST_MAP, SET_OF_LIST_EQ_EMPTY, LIST_OF_SET_EMPTY, LIST_OF_SET_SING,
    pairwise, PAIRWISE_EMPTY, PAIRWISE_SING, PAIRWISE_IMP, PAIRWISE_MONO,
    PAIRWISE_AND, PAIRWISE_INSERT, PAIRWISE_INSERT_SYMMETRIC, PAIRWISE_IMAGE,
    PAIRWISE_UNION, PAIRWISE_CHAIN_UNIONS, DIFF_UNIONS_PAIRWISE_DISJOINT,
    INTER_UNIONS_PAIRWISE_DISJOINT, PSUBSET_UNIONS_PAIRWISE_DISJOINT }

/- ---------------------------------------------------------------------- -/
/- UNION_OF and INTERSECTION_OF.  (sets.ml 3998-4364)                      -/
/- ---------------------------------------------------------------------- -/

/-- `parse_as_infix("UNION_OF",(20,"right"))` and
    `parse_as_infix("INTERSECTION_OF",(20,"right"))` (sets.ml 4001-4002).
    Session runs it once, before `setupSetsUnionOf`. -/
def setupSetsUnionOfInfix : IO Unit := do
  HolCore.Printer.parse_as_infix ("UNION_OF", (20, "right"))
  HolCore.Printer.parse_as_infix ("INTERSECTION_OF", (20, "right"))

/-- `UNION_OF` / `INTERSECTION_OF` and the ARBITRARY and FINITE cases
    (sets.ml 3998-4364).  These combinators - "`s` is a union (resp.
    intersection) of `Q`-sets drawn from a `P`-family" - are used heavily by
    the topology library downstream, so faithfulness here has long reach. -/
structure SetsUnionOf where
  /-- `UNION_OF` (sets.ml 4004, `new_definition`): `P UNION_OF Q = \s. ?u. P u
      /\ (!c. c IN u ==> Q c) /\ UNIONS u = s`.  Introduces the `UNION_OF`
      constant; its infix fixity is registered by `setupSetsUnionOfInfix`. -/
  UNION_OF : thm
  /-- `INTERSECTION_OF` (sets.ml 4009, `new_definition`): `P INTERSECTION_OF Q
      = \s. ?u. P u /\ (!c. c IN u ==> Q c) /\ INTERS u = s`.  Introduces the
      `INTERSECTION_OF` constant. -/
  INTERSECTION_OF : thm
  /-- `UNION_OF_INC` (sets.ml 4012): `P {s} /\ Q s ==> (P UNION_OF Q) s`.
      `EXISTS_TAC {s}`, `ASM_SIMP_TAC[UNIONS_1; IN_SING]`. -/
  UNION_OF_INC : thm
  /-- `INTERSECTION_OF_INC` (sets.ml 4017): `P {s} /\ Q s ==>
      (P INTERSECTION_OF Q) s`.  `ASM_SIMP_TAC[INTERS_1; IN_SING]`. -/
  INTERSECTION_OF_INC : thm
  /-- `UNION_OF_MONO` (sets.ml 4022): `REWRITE_TAC[UNION_OF] THEN MESON_TAC`. -/
  UNION_OF_MONO : thm
  /-- `INTERSECTION_OF_MONO` (sets.ml 4027): `REWRITE_TAC[INTERSECTION_OF] THEN
      MESON_TAC`. -/
  INTERSECTION_OF_MONO : thm
  /-- `FORALL_UNION_OF` (sets.ml 4033): `REWRITE_TAC[UNION_OF] THEN
      MESON_TAC`. -/
  FORALL_UNION_OF : thm
  /-- `FORALL_INTERSECTION_OF` (sets.ml 4038): `REWRITE_TAC[INTERSECTION_OF]
      THEN MESON_TAC`. -/
  FORALL_INTERSECTION_OF : thm
  /-- `UNION_OF_EMPTY` (sets.ml 4043): `P {} ==> (P UNION_OF Q) {}`.
      `EXISTS_TAC {}`, `ASM_REWRITE_TAC[UNIONS_0; NOT_IN_EMPTY]`. -/
  UNION_OF_EMPTY : thm
  /-- `INTERSECTION_OF_EMPTY` (sets.ml 4049): `P {} ==>
      (P INTERSECTION_OF Q) UNIV`.  `ASM_REWRITE_TAC[INTERS_0; NOT_IN_EMPTY]`. -/
  INTERSECTION_OF_EMPTY : thm
  /-- `ARBITRARY` (sets.ml 4062, `new_definition`): `ARBITRARY s <=> T`.
      Introduces the `ARBITRARY` constant. -/
  ARBITRARY : thm
  /-- `ARBITRARY_UNION_OF_ALT` (sets.ml 4062): `(ARBITRARY UNION_OF B) s <=>
      !x. x IN s ==> ?u. u IN B /\ x IN u /\ u SUBSET s`.  ONE top-level `THENL`
      (CONJ_TAC, width 2, second branch ALL_TAC), inline `TAUT`, `FORALL_AND_THM`,
      `EXISTS_TAC {u | u IN B /\ u SUBSET s}`, `ASM SET_TAC[]`. -/
  ARBITRARY_UNION_OF_ALT : thm
  /-- `ARBITRARY_UNION_OF_EMPTY` (sets.ml 4074): `SIMP_TAC[UNION_OF_EMPTY;
      ARBITRARY]`. -/
  ARBITRARY_UNION_OF_EMPTY : thm
  /-- `ARBITRARY_INTERSECTION_OF_EMPTY` (sets.ml 4078):
      `SIMP_TAC[INTERSECTION_OF_EMPTY; ARBITRARY]`. -/
  ARBITRARY_INTERSECTION_OF_EMPTY : thm
  /-- `ARBITRARY_UNION_OF_INC` (sets.ml 4082): `SIMP_TAC[UNION_OF_INC;
      ARBITRARY]`. -/
  ARBITRARY_UNION_OF_INC : thm
  /-- `ARBITRARY_INTERSECTION_OF_INC` (sets.ml 4086): `SIMP_TAC[
      INTERSECTION_OF_INC; ARBITRARY]`. -/
  ARBITRARY_INTERSECTION_OF_INC : thm
  /-- `ARBITRARY_UNION_OF_COMPLEMENT` (sets.ml 4090): `(ARBITRARY UNION_OF P) s
      <=> (ARBITRARY INTERSECTION_OF (\s. P((:A) DIFF s))) ((:A) DIFF s)`.  No
      top-level `THENL`; `X_CHOOSE_THEN .. STRIP_ASSUME_TAC`, `EXISTS_TAC IMAGE
      (\c. UNIV DIFF c) u`, `ONCE_REWRITE_TAC[UNIONS_INTERS; INTERS_UNIONS]`,
      an inline `SET_RULE`. -/
  ARBITRARY_UNION_OF_COMPLEMENT : thm
  /-- `ARBITRARY_INTERSECTION_OF_COMPLEMENT` (sets.ml 4102): dual.
      `REWRITE_TAC[ARBITRARY_UNION_OF_COMPLEMENT] THEN REWRITE_TAC[ETA_AX;
      COMPL_COMPL]`. -/
  ARBITRARY_INTERSECTION_OF_COMPLEMENT : thm
  /-- `ARBITRARY_UNION_OF_IDEMPOT` (sets.ml 4108): `ARBITRARY UNION_OF ARBITRARY
      UNION_OF P = ARBITRARY UNION_OF P`.  ONE top-level `THENL` (CONJ_TAC,
      width 2, second branch `REWRITE_TAC[UNIONS_IMAGE]`); `DISCH_THEN(
      CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))` runs `SYM` first, `SKOLEM_THM`,
      `GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)` (depth 2). -/
  ARBITRARY_UNION_OF_IDEMPOT : thm
  /-- `ARBITRARY_INTERSECTION_OF_IDEMPOT` (sets.ml 4127): dual, via
      `REWRITE_RULE[GSYM FUN_EQ_THM; ETA_AX] ARBITRARY_INTERSECTION_OF_COMPLEMENT`
      then `ARBITRARY_UNION_OF_IDEMPOT`. -/
  ARBITRARY_INTERSECTION_OF_IDEMPOT : thm
  /-- `ARBITRARY_UNION_OF_UNIONS` (sets.ml 4135): `(!s. s IN u ==> (ARBITRARY
      UNION_OF P) s) ==> (ARBITRARY UNION_OF P) (UNIONS u)`.  `ONCE_REWRITE_TAC[
      GSYM ARBITRARY_UNION_OF_IDEMPOT]`, `ONCE_REWRITE_TAC[UNION_OF]`. -/
  ARBITRARY_UNION_OF_UNIONS : thm
  /-- `ARBITRARY_UNION_OF_UNION` (sets.ml 4143): `MATCH_MP_TAC
      ARBITRARY_UNION_OF_UNIONS`, `FORALL_IN_INSERT`, `NOT_IN_EMPTY`. -/
  ARBITRARY_UNION_OF_UNION : thm
  /-- `ARBITRARY_INTERSECTION_OF_INTERS` (sets.ml 4152): dual of UNIONS. -/
  ARBITRARY_INTERSECTION_OF_INTERS : thm
  /-- `ARBITRARY_INTERSECTION_OF_INTER` (sets.ml 4161): dual of UNION. -/
  ARBITRARY_INTERSECTION_OF_INTER : thm
  /-- `ARBITRARY_UNION_OF_INTER_EQ` (sets.ml 4170): distributivity-over-INTER
      equivalence.  ONE top-level `THENL` (EQ_TAC, width 2, first branch
      `MESON_TAC[ARBITRARY_UNION_OF_INC]`, second `DISCH_TAC`); `GEN_REWRITE_TAC
      (LAND_CONV o ONCE_DEPTH_CONV) [UNION_OF]` (depth 2), `DISCH_THEN(
      STRIP_ASSUME_TAC o GSYM)` (GSYM first), `REPLICATE_TAC 2`. -/
  ARBITRARY_UNION_OF_INTER_EQ : thm
  /-- `ARBITRARY_UNION_OF_INTER` (sets.ml 4186): `REWRITE_TAC[
      ARBITRARY_UNION_OF_INTER_EQ] THEN MESON_TAC[ARBITRARY_UNION_OF_INC]`. -/
  ARBITRARY_UNION_OF_INTER : thm
  /-- `ARBITRARY_INTERSECTION_OF_UNION_EQ` (sets.ml 4194): dual via COMPLEMENT;
      two `MESON[COMPL_COMPL] (!s. P(UNIV DIFF s)) <=> (!s. P s)` rewrites. -/
  ARBITRARY_INTERSECTION_OF_UNION_EQ : thm
  /-- `ARBITRARY_INTERSECTION_OF_UNION` (sets.ml 4210): `REWRITE_TAC[
      ARBITRARY_INTERSECTION_OF_UNION_EQ] THEN MESON_TAC[
      ARBITRARY_INTERSECTION_OF_INC]`. -/
  ARBITRARY_INTERSECTION_OF_UNION : thm
  /-- `FINITE_UNION_OF_EMPTY` (sets.ml 4219): `SIMP_TAC[UNION_OF_EMPTY;
      FINITE_EMPTY]`. -/
  FINITE_UNION_OF_EMPTY : thm
  /-- `FINITE_INTERSECTION_OF_EMPTY` (sets.ml 4223): `SIMP_TAC[
      INTERSECTION_OF_EMPTY; FINITE_EMPTY]`. -/
  FINITE_INTERSECTION_OF_EMPTY : thm
  /-- `FINITE_UNION_OF_INC` (sets.ml 4227): `SIMP_TAC[UNION_OF_INC;
      FINITE_SING]`. -/
  FINITE_UNION_OF_INC : thm
  /-- `FINITE_INTERSECTION_OF_INC` (sets.ml 4231): `SIMP_TAC[
      INTERSECTION_OF_INC; FINITE_SING]`. -/
  FINITE_INTERSECTION_OF_INC : thm
  /-- `FINITE_UNION_OF_COMPLEMENT` (sets.ml 4235): like the ARBITRARY version
      but `ASM_SIMP_TAC[FINITE_IMAGE; ...]`. -/
  FINITE_UNION_OF_COMPLEMENT : thm
  /-- `FINITE_INTERSECTION_OF_COMPLEMENT` (sets.ml 4247): dual. -/
  FINITE_INTERSECTION_OF_COMPLEMENT : thm
  /-- `FINITE_UNION_OF_IDEMPOT` (sets.ml 4253): like the ARBITRARY version but
      `ASM_SIMP_TAC[FINITE_IMAGE; FINITE_PRODUCT_DEPENDENT]`.  ONE top-level
      `THENL` (CONJ_TAC, width 2). -/
  FINITE_UNION_OF_IDEMPOT : thm
  /-- `FINITE_INTERSECTION_OF_IDEMPOT` (sets.ml 4272): dual. -/
  FINITE_INTERSECTION_OF_IDEMPOT : thm
  /-- `FINITE_UNION_OF_UNIONS` (sets.ml 4280): `FINITE u /\ (!s. s IN u ==>
      (FINITE UNION_OF P) s) ==> (FINITE UNION_OF P) (UNIONS u)`. -/
  FINITE_UNION_OF_UNIONS : thm
  /-- `FINITE_UNION_OF_UNION` (sets.ml 4288): `FINITE_INSERT`, `FORALL_IN_INSERT`,
      `FINITE_EMPTY`, `NOT_IN_EMPTY`. -/
  FINITE_UNION_OF_UNION : thm
  /-- `FINITE_INTERSECTION_OF_INTERS` (sets.ml 4297): dual of UNIONS. -/
  FINITE_INTERSECTION_OF_INTERS : thm
  /-- `FINITE_INTERSECTION_OF_INTER` (sets.ml 4306): dual of UNION. -/
  FINITE_INTERSECTION_OF_INTER : thm
  /-- `FINITE_UNION_OF_INTER_EQ` (sets.ml 4315): ONE top-level `THENL` (EQ_TAC,
      width 2), `REPLICATE_TAC 2`. -/
  FINITE_UNION_OF_INTER_EQ : thm
  /-- `FINITE_UNION_OF_INTER` (sets.ml 4331): `REWRITE_TAC[
      FINITE_UNION_OF_INTER_EQ] THEN MESON_TAC[FINITE_UNION_OF_INC]`. -/
  FINITE_UNION_OF_INTER : thm
  /-- `FINITE_INTERSECTION_OF_UNION_EQ` (sets.ml 4339): dual via COMPLEMENT. -/
  FINITE_INTERSECTION_OF_UNION_EQ : thm
  /-- `FINITE_INTERSECTION_OF_UNION` (sets.ml 4355): `REWRITE_TAC[
      FINITE_INTERSECTION_OF_UNION_EQ] THEN MESON_TAC[
      FINITE_INTERSECTION_OF_INC]`. -/
  FINITE_INTERSECTION_OF_UNION : thm
  deriving Inhabited

@[nospecialize]
def setupSetsUnionOf [HolBase] (S : SetsCore) (P : SetsProps)
    (SOp : SetsOperators) (SUn : SetsUnions) (SIt : SetsInters)
    (SIm : SetsImage) (SMi : SetsMisc) (SFin : SetsFinite) (SCross : SetsCross)
    (ETA_AX : thm)
    (MESON_TAC : List thm → tactic)
    (MESON' : List thm → term → IO (Except String thm))
    (new_definition' : term → IO (Except String thm)) :
    ExceptT String IO SetsUnionOf := do
  let SET_TAC := SET_TAC S P MESON_TAC
  let SET_RULE := SET_RULE S P MESON_TAC
  let MESON (ths : List thm) (t : term) : ExceptT String IO thm := MESON' ths t
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let { NOT_IN_EMPTY, IN_SING, FORALL_IN_INSERT, FORALL_IN_IMAGE,
        FORALL_IN_GSPEC, EXISTS_IN_GSPEC, UNIONS_IMAGE, .. } := P
  let { COMPL_COMPL, .. } := SOp
  let { UNIONS_0, UNIONS_1, UNIONS_2, INTER_UNIONS, .. } := SUn
  let { INTERS_0, INTERS_1, INTERS_2, .. } := SIt
  let { IMAGE_ID, SIMPLE_IMAGE, .. } := SIm
  let { INTERS_UNIONS, UNIONS_INTERS, .. } := SMi
  let { FINITE_EMPTY, FINITE_INSERT, FINITE_SING, FINITE_IMAGE, .. } := SFin
  let { FINITE_PRODUCT_DEPENDENT, .. } := SCross
  let { FORALL_AND_THM, LEFT_IMP_EXISTS_THM, .. } := HolBase.T
  let { FUN_EQ_THM, RIGHT_IMP_EXISTS_THM, SKOLEM_THM, .. } := HolBase.C

  /- Useful idioms for being a suitable union/intersection of somethings. -/

  let UNION_OF ← new_definition
   r"P UNION_OF Q =
   \s:A->bool. ?u. P u /\ (!c. c IN u ==> Q c) /\ UNIONS u = s"

  let INTERSECTION_OF ← new_definition
   r"P INTERSECTION_OF Q =
   \s:A->bool. ?u. P u /\ (!c. c IN u ==> Q c) /\ INTERS u = s"

  let UNION_OF_INC ← prove
   r"!P Q s:A->bool. P {s} /\ Q s ==> (P UNION_OF Q) s"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [UNION_OF] THEN
    EXISTS_TAC (← q r"{s:A->bool}") THEN ASM_SIMP_TAC [UNIONS_1, IN_SING])

  let INTERSECTION_OF_INC ← prove
   r"!P Q s:A->bool. P {s} /\ Q s ==> (P INTERSECTION_OF Q) s"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [INTERSECTION_OF] THEN
    EXISTS_TAC (← q r"{s:A->bool}") THEN ASM_SIMP_TAC [INTERS_1, IN_SING])

  let UNION_OF_MONO ← prove
   r"!P Q Q' s:A->bool.
        (P UNION_OF Q) s /\ (!x. Q x ==> Q' x) ==> (P UNION_OF Q') s"
   (REWRITE_TAC [UNION_OF] THEN MESON_TAC [])

  let INTERSECTION_OF_MONO ← prove
   r"!P Q Q' s:A->bool.
        (P INTERSECTION_OF Q) s /\ (!x. Q x ==> Q' x)
        ==> (P INTERSECTION_OF Q') s"
   (REWRITE_TAC [INTERSECTION_OF] THEN MESON_TAC [])

  let FORALL_UNION_OF ← prove
   r"(!s:A->bool. (P UNION_OF Q) s ==> R s) <=>
   (!t. P t /\ (!c. c IN t ==> Q c) ==> R(UNIONS t))"
   (REWRITE_TAC [UNION_OF] THEN MESON_TAC [])

  let FORALL_INTERSECTION_OF ← prove
   r"(!s:A->bool. (P INTERSECTION_OF Q) s ==> R s) <=>
   (!t. P t /\ (!c. c IN t ==> Q c) ==> R(INTERS t))"
   (REWRITE_TAC [INTERSECTION_OF] THEN MESON_TAC [])

  let UNION_OF_EMPTY ← prove
   r"!P Q:(A->bool)->bool. P {} ==> (P UNION_OF Q) {}"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [UNION_OF] THEN
    EXISTS_TAC (← q r"{}:(A->bool)->bool") THEN
    ASM_REWRITE_TAC [UNIONS_0, NOT_IN_EMPTY])

  let INTERSECTION_OF_EMPTY ← prove
   r"!P Q:(A->bool)->bool. P {} ==> (P INTERSECTION_OF Q) UNIV"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [INTERSECTION_OF] THEN
    EXISTS_TAC (← q r"{}:(A->bool)->bool") THEN
    ASM_REWRITE_TAC [INTERS_0, NOT_IN_EMPTY])

  /- The ARBITRARY and FINITE cases of UNION_OF / INTERSECTION_OF -/

  let ARBITRARY ← new_definition
   r"ARBITRARY (s:(A->bool)->bool) <=> T"

  let ARBITRARY_UNION_OF_ALT ← prove
   r"!B s:A->bool.
        (ARBITRARY UNION_OF B) s <=>
        !x. x IN s ==>  ?u. u IN B /\ x IN u /\ u SUBSET s"
   (GEN_TAC THEN REWRITE_TAC [FORALL_AND_THM, ← TAUT
     (← q r"(p <=> q) <=> (p ==> q) /\ (q ==> p)")] THEN
    REWRITE_TAC [FORALL_UNION_OF, ARBITRARY] THEN
    CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN
    X_GEN_TAC (← q r"s:A->bool") THEN DISCH_TAC THEN
    REWRITE_TAC [ARBITRARY, UNION_OF] THEN
    EXISTS_TAC (← q r"{u:A->bool | u IN B /\ u SUBSET s}") THEN ASM SET_TAC [])

  let ARBITRARY_UNION_OF_EMPTY ← prove
   r"!P:(A->bool)->bool. (ARBITRARY UNION_OF P) {}"
   (SIMP_TAC [UNION_OF_EMPTY, ARBITRARY])

  let ARBITRARY_INTERSECTION_OF_EMPTY ← prove
   r"!P:(A->bool)->bool. (ARBITRARY INTERSECTION_OF P) UNIV"
   (SIMP_TAC [INTERSECTION_OF_EMPTY, ARBITRARY])

  let ARBITRARY_UNION_OF_INC ← prove
   r"!P s:A->bool. P s ==> (ARBITRARY UNION_OF P) s"
   (SIMP_TAC [UNION_OF_INC, ARBITRARY])

  let ARBITRARY_INTERSECTION_OF_INC ← prove
   r"!P s:A->bool. P s ==> (ARBITRARY INTERSECTION_OF P) s"
   (SIMP_TAC [INTERSECTION_OF_INC, ARBITRARY])

  let ARBITRARY_UNION_OF_COMPLEMENT ← prove
   r"!P s. (ARBITRARY UNION_OF P) s <=>
         (ARBITRARY INTERSECTION_OF (\s. P((:A) DIFF s))) ((:A) DIFF s)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [UNION_OF, INTERSECTION_OF] THEN
    EQ_TAC THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"u:(A->bool)->bool") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"IMAGE (\c. (:A) DIFF c) u") THEN
    ASM_SIMP_TAC [ARBITRARY, FORALL_IN_IMAGE, COMPL_COMPL] THEN
    ONCE_REWRITE_TAC [UNIONS_INTERS, INTERS_UNIONS] THEN
    REWRITE_TAC [← SET_RULE (← q r"{f y | y IN IMAGE g s} = IMAGE (\x. f(g x)) s")] THEN
    ASM_REWRITE_TAC [IMAGE_ID, COMPL_COMPL])

  let ARBITRARY_INTERSECTION_OF_COMPLEMENT ← prove
   r"!P s. (ARBITRARY INTERSECTION_OF P) s <=>
         (ARBITRARY UNION_OF (\s. P((:A) DIFF s))) ((:A) DIFF s)"
   (REWRITE_TAC [ARBITRARY_UNION_OF_COMPLEMENT] THEN
    REWRITE_TAC [ETA_AX, COMPL_COMPL])

  let ARBITRARY_UNION_OF_IDEMPOT ← prove
   r"!P:(A->bool)->bool.
        ARBITRARY UNION_OF ARBITRARY UNION_OF P = ARBITRARY UNION_OF P"
   (GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"s:A->bool") THEN
    EQ_TAC THEN REWRITE_TAC [ARBITRARY_UNION_OF_INC] THEN
    REWRITE_TAC [UNION_OF, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"u:(A->bool)->bool") THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM)) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"f:(A->bool)->(A->bool)->bool") THEN DISCH_TAC THEN
    EXISTS_TAC
      (← q r"IMAGE SND {s,t | s IN u /\ t IN (f:(A->bool)->(A->bool)->bool) s}") THEN
    ASM_SIMP_TAC [ARBITRARY] THEN
    REWRITE_TAC [FORALL_IN_IMAGE, FORALL_IN_GSPEC] THEN
    CONJ_TAC THENL [ASM SET_TAC [], REWRITE_TAC [UNIONS_IMAGE]] THEN
    REWRITE_TAC [EXISTS_IN_GSPEC] THEN ASM SET_TAC [])

  let ARBITRARY_INTERSECTION_OF_IDEMPOT ← prove
   r"!P:(A->bool)->bool.
        ARBITRARY INTERSECTION_OF ARBITRARY INTERSECTION_OF P =
        ARBITRARY INTERSECTION_OF P"
   (REWRITE_TAC [COMPL_COMPL, ETA_AX, ← REWRITE_RULE [← GSYM FUN_EQ_THM, ETA_AX]
                 ARBITRARY_INTERSECTION_OF_COMPLEMENT] THEN
    REWRITE_TAC [ARBITRARY_UNION_OF_IDEMPOT])

  let ARBITRARY_UNION_OF_UNIONS ← prove
   r"!P u:(A->bool)->bool.
        (!s. s IN u ==> (ARBITRARY UNION_OF P) s)
        ==> (ARBITRARY UNION_OF P) (UNIONS u)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM ARBITRARY_UNION_OF_IDEMPOT] THEN
    ONCE_REWRITE_TAC [UNION_OF] THEN REWRITE_TAC [] THEN
    EXISTS_TAC (← q r"u:(A->bool)->bool") THEN ASM_REWRITE_TAC [ARBITRARY])

  let ARBITRARY_UNION_OF_UNION ← prove
   r"!P s t:A->bool.
        (ARBITRARY UNION_OF P) s /\ (ARBITRARY UNION_OF P) t
        ==> (ARBITRARY UNION_OF P) (s UNION t)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM UNIONS_2] THEN
    MATCH_MP_TAC ARBITRARY_UNION_OF_UNIONS THEN
    ASM_REWRITE_TAC [ARBITRARY, FORALL_IN_INSERT] THEN
    REWRITE_TAC [ARBITRARY, NOT_IN_EMPTY])

  let ARBITRARY_INTERSECTION_OF_INTERS ← prove
   r"!P u:(A->bool)->bool.
        (!s. s IN u ==> (ARBITRARY INTERSECTION_OF P) s)
        ==> (ARBITRARY INTERSECTION_OF P) (INTERS u)"
   (REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [← GSYM ARBITRARY_INTERSECTION_OF_IDEMPOT] THEN
    ONCE_REWRITE_TAC [INTERSECTION_OF] THEN REWRITE_TAC [] THEN
    EXISTS_TAC (← q r"u:(A->bool)->bool") THEN ASM_REWRITE_TAC [ARBITRARY])

  let ARBITRARY_INTERSECTION_OF_INTER ← prove
   r"!P s t:A->bool.
        (ARBITRARY INTERSECTION_OF P) s /\ (ARBITRARY INTERSECTION_OF P) t
        ==> (ARBITRARY INTERSECTION_OF P) (s INTER t)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM INTERS_2] THEN
    MATCH_MP_TAC ARBITRARY_INTERSECTION_OF_INTERS THEN
    ASM_REWRITE_TAC [ARBITRARY, FORALL_IN_INSERT] THEN
    REWRITE_TAC [ARBITRARY, NOT_IN_EMPTY])

  let ARBITRARY_UNION_OF_INTER_EQ ← prove
   r"!P:(A->bool)->bool.
        (!s t. (ARBITRARY UNION_OF P) s /\ (ARBITRARY UNION_OF P) t
               ==> (ARBITRARY UNION_OF P) (s INTER t)) <=>
        (!s t. P s /\ P t ==> (ARBITRARY UNION_OF P) (s INTER t))"
   (GEN_TAC THEN
    EQ_TAC THENL [MESON_TAC [ARBITRARY_UNION_OF_INC], DISCH_TAC] THEN
    REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [UNION_OF] THEN
    REWRITE_TAC [] THEN DISCH_THEN (STRIP_ASSUME_TAC o GSYM) THEN
    ASM_REWRITE_TAC [INTER_UNIONS] THEN
    REPLICATE_TAC 2
     (MATCH_MP_TAC ARBITRARY_UNION_OF_UNIONS THEN
      ASM_SIMP_TAC [SIMPLE_IMAGE, ARBITRARY, FORALL_IN_IMAGE] THEN
      REPEAT STRIP_TAC))

  let ARBITRARY_UNION_OF_INTER ← prove
   r"!P:(A->bool)->bool.
        (!s t. P s /\ P t ==> P(s INTER t))
        ==> (!s t. (ARBITRARY UNION_OF P) s /\ (ARBITRARY UNION_OF P) t
                   ==> (ARBITRARY UNION_OF P) (s INTER t))"
   (REWRITE_TAC [ARBITRARY_UNION_OF_INTER_EQ] THEN
    MESON_TAC [ARBITRARY_UNION_OF_INC])

  -- The four rules run (and print) right to left, as in OCaml.
  let ARBITRARY_INTERSECTION_OF_UNION_EQ ← prove
   r"!P:(A->bool)->bool.
        (!s t. (ARBITRARY INTERSECTION_OF P) s /\
               (ARBITRARY INTERSECTION_OF P) t
               ==> (ARBITRARY INTERSECTION_OF P) (s UNION t)) <=>
        (!s t. P s /\ P t ==> (ARBITRARY INTERSECTION_OF P) (s UNION t))"
   (← do
    let m2 ← MESON [COMPL_COMPL] (← q r"(!s. P(UNIV DIFF s)) <=> (!s. P s)")
    let r2 ← SET_RULE
     (← q r"s INTER t = UNIV DIFF ((UNIV DIFF s) UNION (UNIV DIFF t))")
    let m1 ← MESON [COMPL_COMPL] (← q r"(!s. P(UNIV DIFF s)) <=> (!s. P s)")
    let r1 ← SET_RULE
     (← q r"UNIV DIFF (s UNION t) = (UNIV DIFF s) INTER (UNIV DIFF t)")
    pure
     (ONCE_REWRITE_TAC [ARBITRARY_INTERSECTION_OF_COMPLEMENT] THEN
      REWRITE_TAC [r1] THEN
      REWRITE_TAC [m1] THEN
      REWRITE_TAC [ARBITRARY_UNION_OF_INTER_EQ] THEN
      REWRITE_TAC [r2] THEN
      REWRITE_TAC [m2] THEN
      REWRITE_TAC [COMPL_COMPL]))

  let ARBITRARY_INTERSECTION_OF_UNION ← prove
   r"!P:(A->bool)->bool.
        (!s t. P s /\ P t ==> P(s UNION t))
        ==> (!s t. (ARBITRARY INTERSECTION_OF P) s /\
                   (ARBITRARY INTERSECTION_OF P) t
                   ==> (ARBITRARY INTERSECTION_OF P) (s UNION t))"
   (REWRITE_TAC [ARBITRARY_INTERSECTION_OF_UNION_EQ] THEN
    MESON_TAC [ARBITRARY_INTERSECTION_OF_INC])

  let FINITE_UNION_OF_EMPTY ← prove
   r"!P:(A->bool)->bool. (FINITE UNION_OF P) {}"
   (SIMP_TAC [UNION_OF_EMPTY, FINITE_EMPTY])

  let FINITE_INTERSECTION_OF_EMPTY ← prove
   r"!P:(A->bool)->bool. (FINITE INTERSECTION_OF P) UNIV"
   (SIMP_TAC [INTERSECTION_OF_EMPTY, FINITE_EMPTY])

  let FINITE_UNION_OF_INC ← prove
   r"!P s:A->bool. P s ==> (FINITE UNION_OF P) s"
   (SIMP_TAC [UNION_OF_INC, FINITE_SING])

  let FINITE_INTERSECTION_OF_INC ← prove
   r"!P s:A->bool. P s ==> (FINITE INTERSECTION_OF P) s"
   (SIMP_TAC [INTERSECTION_OF_INC, FINITE_SING])

  let FINITE_UNION_OF_COMPLEMENT ← prove
   r"!P s. (FINITE UNION_OF P) s <=>
         (FINITE INTERSECTION_OF (\s. P((:A) DIFF s))) ((:A) DIFF s)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [UNION_OF, INTERSECTION_OF] THEN
    EQ_TAC THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"u:(A->bool)->bool") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"IMAGE (\c. (:A) DIFF c) u") THEN
    ASM_SIMP_TAC [FINITE_IMAGE, FORALL_IN_IMAGE, COMPL_COMPL] THEN
    ONCE_REWRITE_TAC [UNIONS_INTERS, INTERS_UNIONS] THEN
    REWRITE_TAC [← SET_RULE (← q r"{f y | y IN IMAGE g s} = IMAGE (\x. f(g x)) s")] THEN
    ASM_REWRITE_TAC [IMAGE_ID, COMPL_COMPL])

  let FINITE_INTERSECTION_OF_COMPLEMENT ← prove
   r"!P s. (FINITE INTERSECTION_OF P) s <=>
         (FINITE UNION_OF (\s. P((:A) DIFF s))) ((:A) DIFF s)"
   (REWRITE_TAC [FINITE_UNION_OF_COMPLEMENT] THEN
    REWRITE_TAC [ETA_AX, COMPL_COMPL])

  let FINITE_UNION_OF_IDEMPOT ← prove
   r"!P:(A->bool)->bool.
        FINITE UNION_OF FINITE UNION_OF P = FINITE UNION_OF P"
   (GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"s:A->bool") THEN
    EQ_TAC THEN REWRITE_TAC [FINITE_UNION_OF_INC] THEN
    REWRITE_TAC [UNION_OF, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"u:(A->bool)->bool") THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM)) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"f:(A->bool)->(A->bool)->bool") THEN DISCH_TAC THEN
    EXISTS_TAC
      (← q r"IMAGE SND {s,t | s IN u /\ t IN (f:(A->bool)->(A->bool)->bool) s}") THEN
    ASM_SIMP_TAC [FINITE_IMAGE, FINITE_PRODUCT_DEPENDENT] THEN
    REWRITE_TAC [FORALL_IN_IMAGE, FORALL_IN_GSPEC] THEN
    CONJ_TAC THENL [ASM SET_TAC [], REWRITE_TAC [UNIONS_IMAGE]] THEN
    REWRITE_TAC [EXISTS_IN_GSPEC] THEN ASM SET_TAC [])

  let FINITE_INTERSECTION_OF_IDEMPOT ← prove
   r"!P:(A->bool)->bool.
        FINITE INTERSECTION_OF FINITE INTERSECTION_OF P =
        FINITE INTERSECTION_OF P"
   (REWRITE_TAC [COMPL_COMPL, ETA_AX, ← REWRITE_RULE [← GSYM FUN_EQ_THM, ETA_AX]
                 FINITE_INTERSECTION_OF_COMPLEMENT] THEN
    REWRITE_TAC [FINITE_UNION_OF_IDEMPOT])

  let FINITE_UNION_OF_UNIONS ← prove
   r"!P u:(A->bool)->bool.
        FINITE u /\ (!s. s IN u ==> (FINITE UNION_OF P) s)
        ==> (FINITE UNION_OF P) (UNIONS u)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM FINITE_UNION_OF_IDEMPOT] THEN
    ONCE_REWRITE_TAC [UNION_OF] THEN REWRITE_TAC [] THEN
    EXISTS_TAC (← q r"u:(A->bool)->bool") THEN ASM_REWRITE_TAC [])

  let FINITE_UNION_OF_UNION ← prove
   r"!P s t:A->bool.
        (FINITE UNION_OF P) s /\ (FINITE UNION_OF P) t
        ==> (FINITE UNION_OF P) (s UNION t)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM UNIONS_2] THEN
    MATCH_MP_TAC FINITE_UNION_OF_UNIONS THEN
    ASM_REWRITE_TAC [FINITE_INSERT, FORALL_IN_INSERT] THEN
    REWRITE_TAC [FINITE_EMPTY, NOT_IN_EMPTY])

  let FINITE_INTERSECTION_OF_INTERS ← prove
   r"!P u:(A->bool)->bool.
        FINITE u /\ (!s. s IN u ==> (FINITE INTERSECTION_OF P) s)
        ==> (FINITE INTERSECTION_OF P) (INTERS u)"
   (REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [← GSYM FINITE_INTERSECTION_OF_IDEMPOT] THEN
    ONCE_REWRITE_TAC [INTERSECTION_OF] THEN REWRITE_TAC [] THEN
    EXISTS_TAC (← q r"u:(A->bool)->bool") THEN ASM_REWRITE_TAC [])

  let FINITE_INTERSECTION_OF_INTER ← prove
   r"!P s t:A->bool.
        (FINITE INTERSECTION_OF P) s /\ (FINITE INTERSECTION_OF P) t
        ==> (FINITE INTERSECTION_OF P) (s INTER t)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM INTERS_2] THEN
    MATCH_MP_TAC FINITE_INTERSECTION_OF_INTERS THEN
    ASM_REWRITE_TAC [FINITE_INSERT, FORALL_IN_INSERT] THEN
    REWRITE_TAC [FINITE_EMPTY, NOT_IN_EMPTY])

  let FINITE_UNION_OF_INTER_EQ ← prove
   r"!P:(A->bool)->bool.
        (!s t. (FINITE UNION_OF P) s /\ (FINITE UNION_OF P) t
                   ==> (FINITE UNION_OF P) (s INTER t)) <=>
        (!s t. P s /\ P t ==> (FINITE UNION_OF P) (s INTER t))"
   (GEN_TAC THEN
    EQ_TAC THENL [MESON_TAC [FINITE_UNION_OF_INC], DISCH_TAC] THEN
    REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [UNION_OF] THEN
    REWRITE_TAC [] THEN DISCH_THEN (STRIP_ASSUME_TAC o GSYM) THEN
    ASM_REWRITE_TAC [INTER_UNIONS] THEN
    REPLICATE_TAC 2
     (MATCH_MP_TAC FINITE_UNION_OF_UNIONS THEN
      ASM_SIMP_TAC [SIMPLE_IMAGE, FINITE_IMAGE, FORALL_IN_IMAGE] THEN
      REPEAT STRIP_TAC))

  let FINITE_UNION_OF_INTER ← prove
   r"!P:(A->bool)->bool.
        (!s t. P s /\ P t ==> P(s INTER t))
        ==> (!s t. (FINITE UNION_OF P) s /\ (FINITE UNION_OF P) t
                   ==> (FINITE UNION_OF P) (s INTER t))"
   (REWRITE_TAC [FINITE_UNION_OF_INTER_EQ] THEN
    MESON_TAC [FINITE_UNION_OF_INC])

  -- The four rules run (and print) right to left, as in OCaml.
  let FINITE_INTERSECTION_OF_UNION_EQ ← prove
   r"!P:(A->bool)->bool.
        (!s t. (FINITE INTERSECTION_OF P) s /\
               (FINITE INTERSECTION_OF P) t
               ==> (FINITE INTERSECTION_OF P) (s UNION t)) <=>
        (!s t. P s /\ P t ==> (FINITE INTERSECTION_OF P) (s UNION t))"
   (← do
    let m2 ← MESON [COMPL_COMPL] (← q r"(!s. P(UNIV DIFF s)) <=> (!s. P s)")
    let r2 ← SET_RULE
     (← q r"s INTER t = UNIV DIFF ((UNIV DIFF s) UNION (UNIV DIFF t))")
    let m1 ← MESON [COMPL_COMPL] (← q r"(!s. P(UNIV DIFF s)) <=> (!s. P s)")
    let r1 ← SET_RULE
     (← q r"UNIV DIFF (s UNION t) = (UNIV DIFF s) INTER (UNIV DIFF t)")
    pure
     (ONCE_REWRITE_TAC [FINITE_INTERSECTION_OF_COMPLEMENT] THEN
      REWRITE_TAC [r1] THEN
      REWRITE_TAC [m1] THEN
      REWRITE_TAC [FINITE_UNION_OF_INTER_EQ] THEN
      REWRITE_TAC [r2] THEN
      REWRITE_TAC [m2] THEN
      REWRITE_TAC [COMPL_COMPL]))

  let FINITE_INTERSECTION_OF_UNION ← prove
   r"!P:(A->bool)->bool.
        (!s t. P s /\ P t ==> P(s UNION t))
        ==> (!s t. (FINITE INTERSECTION_OF P) s /\
                   (FINITE INTERSECTION_OF P) t
                   ==> (FINITE INTERSECTION_OF P) (s UNION t))"
   (REWRITE_TAC [FINITE_INTERSECTION_OF_UNION_EQ] THEN
    MESON_TAC [FINITE_INTERSECTION_OF_INC])

  return {
    UNION_OF, INTERSECTION_OF, UNION_OF_INC, INTERSECTION_OF_INC,
    UNION_OF_MONO, INTERSECTION_OF_MONO, FORALL_UNION_OF,
    FORALL_INTERSECTION_OF, UNION_OF_EMPTY, INTERSECTION_OF_EMPTY, ARBITRARY,
    ARBITRARY_UNION_OF_ALT, ARBITRARY_UNION_OF_EMPTY,
    ARBITRARY_INTERSECTION_OF_EMPTY, ARBITRARY_UNION_OF_INC,
    ARBITRARY_INTERSECTION_OF_INC, ARBITRARY_UNION_OF_COMPLEMENT,
    ARBITRARY_INTERSECTION_OF_COMPLEMENT, ARBITRARY_UNION_OF_IDEMPOT,
    ARBITRARY_INTERSECTION_OF_IDEMPOT, ARBITRARY_UNION_OF_UNIONS,
    ARBITRARY_UNION_OF_UNION, ARBITRARY_INTERSECTION_OF_INTERS,
    ARBITRARY_INTERSECTION_OF_INTER, ARBITRARY_UNION_OF_INTER_EQ,
    ARBITRARY_UNION_OF_INTER, ARBITRARY_INTERSECTION_OF_UNION_EQ,
    ARBITRARY_INTERSECTION_OF_UNION, FINITE_UNION_OF_EMPTY,
    FINITE_INTERSECTION_OF_EMPTY, FINITE_UNION_OF_INC,
    FINITE_INTERSECTION_OF_INC, FINITE_UNION_OF_COMPLEMENT,
    FINITE_INTERSECTION_OF_COMPLEMENT, FINITE_UNION_OF_IDEMPOT,
    FINITE_INTERSECTION_OF_IDEMPOT, FINITE_UNION_OF_UNIONS,
    FINITE_UNION_OF_UNION, FINITE_INTERSECTION_OF_INTERS,
    FINITE_INTERSECTION_OF_INTER, FINITE_UNION_OF_INTER_EQ,
    FINITE_UNION_OF_INTER, FINITE_INTERSECTION_OF_UNION_EQ,
    FINITE_INTERSECTION_OF_UNION }

/- ---------------------------------------------------------------------- -/
/- set_of_list cardinality, injectivity/surjectivity, bijections,          -/
/- wellfoundedness and the cardinal comparisons (sets.ml 4365-4695).        -/
/- ---------------------------------------------------------------------- -/

/-- The finish of the set_of_list section (`CARD_SET_OF_LIST_LE`,
    `HAS_SIZE_SET_OF_LIST`), the classic finite injectivity/surjectivity
    results (`SURJECTIVE_IFF_INJECTIVE_GEN` and friends), the image/preimage
    injectivity/surjectivity rewrites, the finite-set bijection existence
    theorems, `WF_FINITE`/`WF_PSUBSET`, and finally the cardinal-comparison
    definitions `le_c`/`lt_c`/`eq_c`/`ge_c`/`gt_c` with `LE_C`/`GE_C` and the
    `COUNTABLE` definition (sets.ml 4365-4695).

    The five cardinal-comparison infixes `<=_c`, `<_c`, `>=_c`, `>_c`, `=_c`
    were ALREADY registered by `setupSetsInfixes` (sets.ml 28-32, all
    `(12,"right")`); this range introduces NO new `parse_as_infix`, so a term
    like `s <=_c t` parses as an infix application of the `<=_c` constant once
    `le_c` introduces it. -/
structure SetsCardComp where
  /-- `CARD_SET_OF_LIST_LE` (sets.ml 4368):
      `!l:A list. CARD(set_of_list l) <= LENGTH l`. -/
  CARD_SET_OF_LIST_LE : thm
  /-- `HAS_SIZE_SET_OF_LIST` (sets.ml 4374):
      `set_of_list l HAS_SIZE LENGTH l <=> PAIRWISE (\x y. ~(x = y)) l`. -/
  HAS_SIZE_SET_OF_LIST : thm
  /-- `SURJECTIVE_IFF_INJECTIVE_GEN` (sets.ml 4386): on equal-card finite sets
      with `IMAGE f s SUBSET t`, surjectivity onto `t` iff injectivity. -/
  SURJECTIVE_IFF_INJECTIVE_GEN : thm
  /-- `SURJECTIVE_IFF_INJECTIVE` (sets.ml 4406): the `s = t` special case. -/
  SURJECTIVE_IFF_INJECTIVE : thm
  /-- `IMAGE_IMP_INJECTIVE_GEN` (sets.ml 4413): equal card and `IMAGE f s = t`
      force injectivity on `s`. -/
  IMAGE_IMP_INJECTIVE_GEN : thm
  /-- `IMAGE_IMP_INJECTIVE` (sets.ml 4423): the `IMAGE f s = s` special case. -/
  IMAGE_IMP_INJECTIVE : thm
  /-- `HAS_SIZE_IMAGE_INJ_RESTRICT` (sets.ml 4429): transfers a `HAS_SIZE` of a
      predicate-restricted subset across an injective equal-card map. -/
  HAS_SIZE_IMAGE_INJ_RESTRICT : thm
  /-- `CARD_LE_INJ` (sets.ml 4450): `CARD s <= CARD t` on finite sets yields an
      injection of `s` into `t`. -/
  CARD_LE_INJ : thm
  /-- `FORALL_IN_CLAUSES` (sets.ml 4475): the `{}`/`INSERT` clauses of a bounded
      universal. -/
  FORALL_IN_CLAUSES : thm
  /-- `EXISTS_IN_CLAUSES` (sets.ml 4480): the `{}`/`INSERT` clauses of a bounded
      existential. -/
  EXISTS_IN_CLAUSES : thm
  /-- `INJECTIVE_ON_IMAGE` (sets.ml 4489): image-injectivity on subsets of `u`
      iff pointwise injectivity on `u`. -/
  INJECTIVE_ON_IMAGE : thm
  /-- `INJECTIVE_IMAGE` (sets.ml 4498): the `u = (:A)` special case. -/
  INJECTIVE_IMAGE : thm
  /-- `SURJECTIVE_ON_IMAGE` (sets.ml 4504): image-surjectivity onto subsets of
      `v` iff pointwise surjectivity onto `v`. -/
  SURJECTIVE_ON_IMAGE : thm
  /-- `SURJECTIVE_IMAGE` (sets.ml 4514): the `UNIV` special case. -/
  SURJECTIVE_IMAGE : thm
  /-- `INJECTIVE_ON_PREIMAGE` (sets.ml 4520): preimage-injectivity iff
      `u SUBSET IMAGE f s`. -/
  INJECTIVE_ON_PREIMAGE : thm
  /-- `SURJECTIVE_ON_PREIMAGE` (sets.ml 4530): preimage-surjectivity iff image
      subset plus injectivity. -/
  SURJECTIVE_ON_PREIMAGE : thm
  /-- `INJECTIVE_PREIMAGE` (sets.ml 4545): the universal preimage-injectivity
      characterisation, `IMAGE f UNIV = UNIV`. -/
  INJECTIVE_PREIMAGE : thm
  /-- `SURJECTIVE_PREIMAGE` (sets.ml 4554): the universal preimage-surjectivity
      characterisation, pointwise injectivity. -/
  SURJECTIVE_PREIMAGE : thm
  /-- `CARD_EQ_BIJECTION` (sets.ml 4565): equal finite cards give a bijection
      (surjective and injective on `s`). -/
  CARD_EQ_BIJECTION : thm
  /-- `CARD_EQ_BIJECTIONS` (sets.ml 4576): equal finite cards give mutually
      inverse maps `f`/`g`. -/
  CARD_EQ_BIJECTIONS : thm
  /-- `CARD_EQ_BIJECTIONS_SPECIAL` (sets.ml 4585): the bijections may be chosen
      to swap a distinguished pair `a`/`b`. -/
  CARD_EQ_BIJECTIONS_SPECIAL : thm
  /-- `BIJECTIONS_HAS_SIZE` (sets.ml 4600): inverse maps transfer `HAS_SIZE`. -/
  BIJECTIONS_HAS_SIZE : thm
  /-- `BIJECTIONS_HAS_SIZE_EQ` (sets.ml 4610): inverse maps give
      `s HAS_SIZE n <=> t HAS_SIZE n`. -/
  BIJECTIONS_HAS_SIZE_EQ : thm
  /-- `BIJECTIONS_CARD_EQ` (sets.ml 4622): inverse maps with one side finite
      give `CARD s = CARD t`. -/
  BIJECTIONS_CARD_EQ : thm
  /-- `WF_FINITE` (sets.ml 4636): an irreflexive transitive relation with
      finitely many predecessors is wellfounded. -/
  WF_FINITE : thm
  /-- `WF_PSUBSET` (sets.ml 4654): proper-subset descent within a finite set is
      wellfounded. -/
  WF_PSUBSET : thm
  /-- `le_c` (sets.ml 4665): `s <=_c t` iff an injection of `s` into `t`. -/
  le_c : thm
  /-- `lt_c` (sets.ml 4670): `s <_c t <=> s <=_c t /\ ~(t <=_c s)`. -/
  lt_c : thm
  /-- `eq_c` (sets.ml 4673): `s =_c t` iff a bijection witnessed by a unique
      preimage. -/
  eq_c : thm
  /-- `ge_c` (sets.ml 4678): `s >=_c t <=> t <=_c s`. -/
  ge_c : thm
  /-- `gt_c` (sets.ml 4681): `s >_c t <=> t <_c s`. -/
  gt_c : thm
  /-- `LE_C` (sets.ml 4684): `s <=_c t` via a surjection `g` from `t` covering
      `s`. -/
  LE_C : thm
  /-- `GE_C` (sets.ml 4690): `s >=_c t` via a map `f` from `s` covering `t`. -/
  GE_C : thm
  /-- `COUNTABLE` (sets.ml 4694): `COUNTABLE t <=> (:num) >=_c t`. -/
  COUNTABLE : thm
  deriving Inhabited

@[nospecialize]
def setupSetsCardComp [HolBase] (S : SetsCore)
    (P : SetsProps) (SIn : SetsInclusion) (SIm : SetsImage)
    (SInd : SetsInduct) (SFin : SetsFinite) (SCard : SetsCard)
    (SCard2 : SetsCard2) (SFun2 : SetsFunspace2) (SFn : SetsFunctions)
    (SL : SetsList) (SInf : SetsInfinite)
    (Nm : HolMath.Nums.NumsThms)
    (Ar2 : HolMath.Arith.ArithThms2) (Ar3 : HolMath.Arith.ArithThms3)
    (Ar9 : HolMath.Arith.ArithThms9) (Wf : HolMath.Wf.WfThms)
    (MESON_TAC : List thm → tactic) (ASM_MESON_TAC : List thm → tactic)
    (LIST_INDUCT_TAC : tactic) (ASM_ARITH_TAC : tactic)
    (ARITH_RULE' : term → IO (Except String thm))
    (ALL PAIRWISE ALL_MEM LENGTH : thm)
    (new_definition' : term → IO (Except String thm)) :
    ExceptT String IO SetsCardComp := do
  let SET_TAC := SET_TAC S P MESON_TAC
  let ARITH_RULE (t : term) : ExceptT String IO thm := ARITH_RULE' t
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC Nm.num_INDUCTION
  let { SUC_INJ, NOT_SUC, .. } := Nm
  let { LE, LE_SUC, LT_0, .. } := Ar2
  let { LE_REFL, LET_TRANS, LT_CASES, NOT_LE, .. } := Ar3
  let { TRANSITIVE_STEPWISE_LT, .. } := Ar9
  let { WF_DCHAIN, .. } := Wf
  let { EXTENSION, IN_ELIM_THM, SUBSET, INFINITE, .. } := S
  let { NOT_IN_EMPTY, IN_UNIV, IN_INSERT, IN_DELETE, IN_IMAGE, FORALL_IN_IMAGE, .. } := P
  let { MEMBER_NOT_EMPTY, SUBSET_REFL, EMPTY_SUBSET, SUBSET_UNIV, SING_SUBSET, .. } := SIn
  let { IMAGE_CLAUSES, .. } := SIm
  let { FINITE_INDUCT_STRONG, .. } := SInd
  let { FINITE_SUBSET, FINITE_INSERT, FINITE_DELETE, FINITE_IMAGE,
        INFINITE_IMAGE_INJ, .. } := SFin
  let { CARD_CLAUSES, CARD_DELETE, CARD_EQ_0, HAS_SIZE, .. } := SCard
  let { CARD_SUBSET_EQ, CARD_SUBSET, CARD_IMAGE_INJ, HAS_SIZE_IMAGE_INJ,
        CARD_IMAGE_LE, .. } := SCard2
  let { FINITE_POWERSET, .. } := SFun2
  let { SURJECTIVE_ON_RIGHT_INVERSE, INJECTIVE_ON_LEFT_INVERSE, .. } := SFn
  let { set_of_list, FINITE_SET_OF_LIST, IN_SET_OF_LIST, .. } := SL
  let { num_INFINITE, .. } := SInf
  let { CONJ_ASSOC, IMP_CONJ, LEFT_AND_EXISTS_THM, RIGHT_AND_EXISTS_THM,
        RIGHT_FORALL_IMP_THM, LEFT_IMP_EXISTS_THM, MONO_FORALL, MONO_EXISTS, .. } := HolBase.T
  let { RIGHT_IMP_EXISTS_THM, SKOLEM_THM, .. } := HolBase.C

  /- Some additional properties of "set_of_list". -/

  let CARD_SET_OF_LIST_LE ← prove
   r"!l:A list. CARD(set_of_list l) <= LENGTH l"
   (LIST_INDUCT_TAC THEN
    SIMP_TAC [LENGTH, set_of_list, CARD_CLAUSES, FINITE_SET_OF_LIST] THEN
    ASM_ARITH_TAC)

  let HAS_SIZE_SET_OF_LIST ← prove
   r"!l. (set_of_list l) HAS_SIZE (LENGTH l) <=> PAIRWISE (\x y:A. ~(x = y)) l"
   (REWRITE_TAC [HAS_SIZE, FINITE_SET_OF_LIST] THEN LIST_INDUCT_TAC THEN
    ASM_SIMP_TAC [CARD_CLAUSES, LENGTH, set_of_list, PAIRWISE, ALL,
                  FINITE_SET_OF_LIST, ← GSYM ALL_MEM, IN_SET_OF_LIST] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [SUC_INJ] THEN
    ASM_MESON_TAC [CARD_SET_OF_LIST_LE, ← ARITH_RULE (← q r"~(SUC n <= n)")])

  /- Classic result on function of finite set into itself. -/

  let SURJECTIVE_IFF_INJECTIVE_GEN ← prove
   r"!s t f:A->B.
        FINITE s /\ FINITE t /\ (CARD s = CARD t) /\ (IMAGE f s) SUBSET t
        ==> ((!y. y IN t ==> ?x. x IN s /\ (f x = y)) <=>
             (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)))"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
     [ASM_CASES_TAC (← q r"x:A = y") THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"CARD s <= CARD (IMAGE (f:A->B) (s DELETE y))") MP_TAC THENL
       [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC CARD_SUBSET THEN
        ASM_SIMP_TAC [FINITE_IMAGE, FINITE_DELETE] THEN
        REWRITE_TAC [SUBSET, IN_IMAGE, IN_DELETE] THEN ASM_MESON_TAC [],
        REWRITE_TAC [NOT_LE] THEN MATCH_MP_TAC LET_TRANS THEN
        EXISTS_TAC (← q r"CARD(s DELETE (y:A))") THEN
        ASM_SIMP_TAC [CARD_IMAGE_LE, FINITE_DELETE] THEN
        ASM_SIMP_TAC [CARD_DELETE, ← ARITH_RULE (← q r"x - 1 < x <=> ~(x = 0)")] THEN
        ASM_MESON_TAC [CARD_EQ_0, MEMBER_NOT_EMPTY]],
      SUBGOAL_THEN (← q r"IMAGE (f:A->B) s = t") MP_TAC THENL
       [ALL_TAC, ASM_MESON_TAC [EXTENSION, IN_IMAGE]] THEN
      ASM_MESON_TAC [CARD_SUBSET_EQ, CARD_IMAGE_INJ]])

  let SURJECTIVE_IFF_INJECTIVE ← prove
   r"!s f:A->A.
        FINITE s /\ (IMAGE f s) SUBSET s
        ==> ((!y. y IN s ==> ?x. x IN s /\ (f x = y)) <=>
             (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)))"
   (SIMP_TAC [SURJECTIVE_IFF_INJECTIVE_GEN])

  let IMAGE_IMP_INJECTIVE_GEN ← prove
   r"!s t f:A->B.
        FINITE s /\ (CARD s = CARD t) /\ (IMAGE f s = t)
        ==> !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)"
   (REPEAT GEN_TAC THEN DISCH_THEN (ASSUME_TAC o GSYM) THEN
    MP_TAC (← ISPECL [← q r"s:A->bool", ← q r"t:B->bool", ← q r"f:A->B"]
                  SURJECTIVE_IFF_INJECTIVE_GEN) THEN
    ASM_SIMP_TAC [SUBSET_REFL, FINITE_IMAGE] THEN
    ASM_MESON_TAC [EXTENSION, IN_IMAGE])

  let IMAGE_IMP_INJECTIVE ← prove
   r"!s f:A->A.
        FINITE s /\ IMAGE f s = s
        ==> !x y. x IN s /\ y IN s /\ f x = f y ==> x = y"
   (MESON_TAC [IMAGE_IMP_INJECTIVE_GEN])

  let HAS_SIZE_IMAGE_INJ_RESTRICT ← prove
   r"!(f:A->B) s t P n.
      FINITE s /\ FINITE t /\ CARD s = CARD t /\
      IMAGE f s SUBSET t /\
      (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
      {x | x IN s /\ P(f x)} HAS_SIZE n
      ==> {x | x IN t /\ P x} HAS_SIZE n"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"{x | x IN t /\ P x} = IMAGE (f:A->B) {x | x IN s /\ P(f x)}")
    SUBST1_TAC THENL
     [MP_TAC (← ISPECL [← q r"s:A->bool", ← q r"t:B->bool", ← q r"f:A->B"]
          SURJECTIVE_IFF_INJECTIVE_GEN) THEN
      ASM_REWRITE_TAC [] THEN ASM SET_TAC [],
      MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
      ASM_REWRITE_TAC [] THEN ASM SET_TAC []])

  /- Converse relation between cardinality and injection. -/

  let CARD_LE_INJ ← prove
   r"!s t. FINITE s /\ FINITE t /\ CARD s <= CARD t
   ==> ?f:A->B. (IMAGE f s) SUBSET t /\
                !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)"
   (REWRITE_TAC [IMP_CONJ] THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [IMAGE_CLAUSES, EMPTY_SUBSET, NOT_IN_EMPTY] THEN
    SIMP_TAC [CARD_CLAUSES] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"s:A->bool"] THEN STRIP_TAC THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [CARD_CLAUSES, LE, NOT_SUC] THEN
    MAP_EVERY X_GEN_TAC [← q r"y:B", ← q r"t:B->bool"] THEN
    SIMP_TAC [CARD_CLAUSES] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (K ALL_TAC : thm → tactic) STRIP_ASSUME_TAC) THEN
    REWRITE_TAC [LE_SUC] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"t:B->bool")) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"f:A->B") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"\z:A. if z = x then (y:B) else f(z)") THEN
    REWRITE_TAC [IN_INSERT, SUBSET, IN_IMAGE] THEN
    ASM_MESON_TAC [SUBSET, IN_IMAGE])

  /- Occasionally handy rewrites. -/

  let FORALL_IN_CLAUSES ← prove
   r"(!P. (!x:A. x IN {} ==> P x) <=> T) /\
   (!P a s. (!x:A. x IN (a INSERT s) ==> P x) <=> P a /\ (!x. x IN s ==> P x))"
   (REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN MESON_TAC [])

  let EXISTS_IN_CLAUSES ← prove
   r"(!P. (?x:A. x IN {} /\ P x) <=> F) /\
   (!P a s. (?x:A. x IN (a INSERT s) /\ P x) <=> P a \/ (?x. x IN s /\ P x))"
   (REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN MESON_TAC [])

  /- Injectivity and surjectivity of image and preimage under a function. -/

  let INJECTIVE_ON_IMAGE ← prove
   r"!f:A->B u.
    (!s t. s SUBSET u /\ t SUBSET u /\ IMAGE f s = IMAGE f t ==> s = t) <=>
    (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL [DISCH_TAC, SET_TAC []] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"y:A"] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"{x:A}", ← q r"{y:A}"]) THEN
    ASM_REWRITE_TAC [SING_SUBSET, IMAGE_CLAUSES] THEN SET_TAC [])

  let INJECTIVE_IMAGE ← prove
   r"!f:A->B.
    (!s t. IMAGE f s = IMAGE f t ==> s = t) <=> (!x y. f x = f y ==> x = y)"
   (GEN_TAC THEN MP_TAC (← ISPECL [← q r"f:A->B", ← q r"(:A)"] INJECTIVE_ON_IMAGE) THEN
    REWRITE_TAC [IN_UNIV, SUBSET_UNIV])

  let SURJECTIVE_ON_IMAGE ← prove
   r"!f:A->B u v.
        (!t. t SUBSET v ==> ?s. s SUBSET u /\ IMAGE f s = t) <=>
        (!y. y IN v ==> ?x. x IN u /\ f x = y)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"{y:B}")) THEN ASM SET_TAC [],
      DISCH_TAC THEN X_GEN_TAC (← q r"t:B->bool") THEN DISCH_TAC THEN
      EXISTS_TAC (← q r"{x | x IN u /\ (f:A->B) x IN t}") THEN ASM SET_TAC []])

  let SURJECTIVE_IMAGE ← prove
   r"!f:A->B. (!t. ?s. IMAGE f s = t) <=> (!y. ?x. f x = y)"
   (GEN_TAC THEN
    MP_TAC (← ISPECL [← q r"f:A->B", ← q r"(:A)", ← q r"(:B)"] SURJECTIVE_ON_IMAGE) THEN
    REWRITE_TAC [IN_UNIV, SUBSET_UNIV])

  let INJECTIVE_ON_PREIMAGE ← prove
   r"!f:A->B s u.
        (!t t'. t SUBSET u /\ t' SUBSET u /\
                {x | x IN s /\ f x IN t} = {x | x IN s /\ f x IN t'}
                ==> t = t') <=>
        u SUBSET IMAGE f s"
   (REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
    REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"y:B") THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"{y:B}", ← q r"{}:B->bool"]) THEN ASM SET_TAC [])

  let SURJECTIVE_ON_PREIMAGE ← prove
   r"!f:A->B s u.
        (!k. k SUBSET s
             ==> ?t. t SUBSET u /\ {x | x IN s /\ f x IN t} = k) <=>
        IMAGE f s SUBSET u /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"x:A") THEN
        DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q r"{x:A}")) THEN ASM SET_TAC [],
        MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"y:A"] THEN STRIP_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"{x:A}")) THEN ASM SET_TAC []],
      X_GEN_TAC (← q r"k:A->bool") THEN STRIP_TAC THEN
      EXISTS_TAC (← q r"IMAGE (f:A->B) k") THEN ASM SET_TAC []])

  let INJECTIVE_PREIMAGE ← prove
   r"!f:A->B.
        (!t t'. {x | f x IN t} = {x | f x IN t'} ==> t = t') <=>
        IMAGE f UNIV = UNIV"
   (REPEAT GEN_TAC THEN
    MP_TAC (← ISPECL [← q r"f:A->B", ← q r"(:A)", ← q r"(:B)"]
          INJECTIVE_ON_PREIMAGE) THEN
    REWRITE_TAC [IN_UNIV, SUBSET_UNIV] THEN SET_TAC [])

  let SURJECTIVE_PREIMAGE ← prove
   r"!f:A->B. (!k. ?t. {x | f x IN t} = k) <=> (!x y. f x = f y ==> x = y)"
   (REPEAT GEN_TAC THEN
    MP_TAC (← ISPECL [← q r"f:A->B", ← q r"(:A)", ← q r"(:B)"]
          SURJECTIVE_ON_PREIMAGE) THEN
    REWRITE_TAC [IN_UNIV, SUBSET_UNIV] THEN SET_TAC [])

  /- Existence of bijections between two finite sets of same size. -/

  let CARD_EQ_BIJECTION ← prove
   r"!s t. FINITE s /\ FINITE t /\ CARD s = CARD t
   ==> ?f:A->B. (!x. x IN s ==> f(x) IN t) /\
                (!y. y IN t ==> ?x. x IN s /\ f x = y) /\
                !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)"
   (MP_TAC CARD_LE_INJ THEN REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC [LE_REFL] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM_SIMP_TAC [SURJECTIVE_IFF_INJECTIVE_GEN] THEN
    MESON_TAC [SUBSET, IN_IMAGE])

  let CARD_EQ_BIJECTIONS ← prove
   r"!s t. FINITE s /\ FINITE t /\ CARD s = CARD t
   ==> ?f:A->B g. (!x. x IN s ==> f(x) IN t /\ g(f x) = x) /\
                  (!y. y IN t ==> g(y) IN s /\ f(g y) = y)"
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP CARD_EQ_BIJECTION) THEN
    MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC [SURJECTIVE_ON_RIGHT_INVERSE] THEN
    GEN_TAC THEN REWRITE_TAC [LEFT_AND_EXISTS_THM, RIGHT_AND_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC [])

  let CARD_EQ_BIJECTIONS_SPECIAL ← prove
   r"!s t (a:A) (b:B).
         FINITE s /\ FINITE t /\ CARD s = CARD t /\ a IN s /\ b IN t
         ==> ?f g. f a = b /\ g b = a /\
                   (!x. x IN s ==> f x IN t /\ g (f x) = x) /\
                   (!y. y IN t ==> g y IN s /\ f (g y) = y)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"s DELETE (a:A)", ← q r"t DELETE (b:B)"]
          CARD_EQ_BIJECTIONS) THEN
    ASM_SIMP_TAC [FINITE_DELETE, CARD_DELETE, IN_DELETE, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"f:A->B", ← q r"g:B->A"] THEN STRIP_TAC THEN
    EXISTS_TAC (← q r"\x. if x = a then b else (f:A->B) x") THEN
    EXISTS_TAC (← q r"\y. if y = b then a else (g:B->A) y") THEN
    ASM_MESON_TAC [])

  let BIJECTIONS_HAS_SIZE ← prove
   r"!s t f:A->B g.
        (!x. x IN s ==> f(x) IN t /\ g(f x) = x) /\
        (!y. y IN t ==> g(y) IN s /\ f(g y) = y) /\
        s HAS_SIZE n
        ==> t HAS_SIZE n"
   (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"t = IMAGE (f:A->B) s") SUBST_ALL_TAC THENL
     [ASM SET_TAC [],
      MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_MESON_TAC []])

  let BIJECTIONS_HAS_SIZE_EQ ← prove
   r"!s t f:A->B g.
        (!x. x IN s ==> f(x) IN t /\ g(f x) = x) /\
        (!y. y IN t ==> g(y) IN s /\ f(g y) = y)
        ==> !n. s HAS_SIZE n <=> t HAS_SIZE n"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN
    MATCH_MP_TAC (← ONCE_REWRITE_RULE
    [← TAUT (← q r"a /\ b /\ c ==> d <=> a /\ b ==> c ==> d")] BIJECTIONS_HAS_SIZE) THENL
     [MAP_EVERY EXISTS_TAC [← q r"f:A->B", ← q r"g:B->A"],
      MAP_EVERY EXISTS_TAC [← q r"g:B->A", ← q r"f:A->B"]] THEN
    ASM_MESON_TAC [])

  let BIJECTIONS_CARD_EQ ← prove
   r"!s t f:A->B g.
        (FINITE s \/ FINITE t) /\
        (!x. x IN s ==> f(x) IN t /\ g(f x) = x) /\
        (!y. y IN t ==> g(y) IN s /\ f(g y) = y)
        ==> CARD s = CARD t"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2
     MP_TAC (MP_TAC o MATCH_MP BIJECTIONS_HAS_SIZE_EQ)) THEN
    MESON_TAC [HAS_SIZE])

  /- Transitive relation with finitely many predecessors is wellfounded. -/

  let WF_FINITE ← prove
   r"!(<<). (!x. ~(x << x)) /\ (!x y z. x << y /\ y << z ==> x << z) /\
          (!x:A. FINITE {y | y << x})
          ==> WF(<<)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [WF_DCHAIN] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"s:num->A") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"!m n. m < n ==> (s:num->A) n << s m") ASSUME_TAC THENL
     [MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN ASM_MESON_TAC [], ALL_TAC] THEN
    MP_TAC (← ISPEC (← q r"s:num->A") INFINITE_IMAGE_INJ) THEN ANTS_TAC THENL
     [ASM_MESON_TAC [LT_CASES], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"(:num)")) THEN
    REWRITE_TAC [num_INFINITE] THEN REWRITE_TAC [INFINITE] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC (← q r"s(0) INSERT {y:A | y << s(0)}") THEN
    ASM_REWRITE_TAC [FINITE_INSERT] THEN
    REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_UNIV, IN_INSERT] THEN
    INDUCT_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [LT_0])

  let WF_PSUBSET ← prove
   r"!s:A->bool. FINITE s ==> WF (\t1 t2. t1 PSUBSET t2 /\ t2 SUBSET s)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC WF_FINITE THEN SIMP_TAC [CONJ_ASSOC] THEN
    CONJ_TAC THENL [SET_TAC [], X_GEN_TAC (← q r"t:A->bool")] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{t:A->bool | t SUBSET s}") THEN
    ASM_SIMP_TAC [FINITE_POWERSET] THEN SET_TAC [])

  /- Cardinal comparisons (more theory in Library/card.ml) -/

  let le_c ← new_definition
   r"s <=_c t <=>
   ?f:A->B. (!x. x IN s ==> f(x) IN t) /\
            (!x y. x IN s /\ y IN s /\ f(x) = f(y) ==> x = y)"

  let lt_c ← new_definition
   r"(s:A->bool) <_c (t:B->bool) <=> s <=_c t /\ ~(t <=_c s)"

  let eq_c ← new_definition
   r"(s:A->bool) =_c (t:B->bool) <=>
   ?f. (!x. x IN s ==> f(x) IN t) /\
       !y. y IN t ==> ?!x. x IN s /\ (f x = y)"

  let ge_c ← new_definition
   r"(s:A->bool) >=_c (t:B->bool) <=> t <=_c s"

  let gt_c ← new_definition
   r"(s:A->bool) >_c (t:B->bool) <=> t <_c s"

  let LE_C ← prove
   r"!s t. s <=_c t <=> ?g:A->B. !x. x IN s ==> ?y. y IN t /\ g y = x"
   (REWRITE_TAC [le_c, INJECTIVE_ON_LEFT_INVERSE, SURJECTIVE_ON_RIGHT_INVERSE,
                 RIGHT_IMP_EXISTS_THM, SKOLEM_THM, RIGHT_AND_EXISTS_THM] THEN
    MESON_TAC [])

  let GE_C ← prove
   r"!s t. s >=_c t <=> ?f:A->B. !y. y IN t ==> ?x. x IN s /\ (y = f x)"
   (REWRITE_TAC [ge_c, LE_C] THEN MESON_TAC [])

  let COUNTABLE ← new_definition
   r"COUNTABLE (t:A->bool) <=> (:num) >=_c t"

  return {
    CARD_SET_OF_LIST_LE, HAS_SIZE_SET_OF_LIST, SURJECTIVE_IFF_INJECTIVE_GEN,
    SURJECTIVE_IFF_INJECTIVE, IMAGE_IMP_INJECTIVE_GEN, IMAGE_IMP_INJECTIVE,
    HAS_SIZE_IMAGE_INJ_RESTRICT, CARD_LE_INJ, FORALL_IN_CLAUSES,
    EXISTS_IN_CLAUSES, INJECTIVE_ON_IMAGE, INJECTIVE_IMAGE,
    SURJECTIVE_ON_IMAGE, SURJECTIVE_IMAGE, INJECTIVE_ON_PREIMAGE,
    SURJECTIVE_ON_PREIMAGE, INJECTIVE_PREIMAGE, SURJECTIVE_PREIMAGE,
    CARD_EQ_BIJECTION, CARD_EQ_BIJECTIONS, CARD_EQ_BIJECTIONS_SPECIAL,
    BIJECTIONS_HAS_SIZE, BIJECTIONS_HAS_SIZE_EQ, BIJECTIONS_CARD_EQ, WF_FINITE,
    WF_PSUBSET, le_c, lt_c, eq_c, ge_c, gt_c, LE_C, GE_C, COUNTABLE }

/- ---------------------------------------------------------------------- -/
/- Supremum and infimum of a set of reals.               (sets.ml 4698-5027) -/
/- ---------------------------------------------------------------------- -/

/-- The `sup`/`inf` bundle of `sets.ml 4698-5027`: the two `new_definition`s
    `sup`/`inf` and the 49 `prove`s that surround them - the finite-set
    characterisations, the completeness-backed `SUP`/`INF`, uniqueness,
    subset/bounds/union/singleton clauses, `REAL_MAX_SUP`/`REAL_MIN_INF` and
    `REAL_SUP_EQ_INF`.  This section introduces NO new `parse_as_infix`; the
    relational `has_inf`/`has_sup` operators (sets.ml 5030-5031) live in the
    separate `SetsHasInfSup` bundle.  Rests on the real-number layer: `SUP`
    is `REAL_COMPLETE` + `SELECT_CONV`, `INF` reflects it through
    `IMAGE (--)`, and the `_FINITE` clauses run on `REAL_LE_TOTAL`. -/
structure SetsSup where
  sup : thm
  SUP_EQ : thm
  SUP : thm
  SUP_FINITE_LEMMA : thm
  SUP_FINITE : thm
  REAL_LE_SUP_FINITE : thm
  REAL_SUP_LE_FINITE : thm
  REAL_LT_SUP_FINITE : thm
  REAL_SUP_LT_FINITE : thm
  REAL_SUP_UNIQUE : thm
  REAL_SUP_LE : thm
  REAL_SUP_LE_SUBSET : thm
  REAL_SUP_BOUNDS : thm
  REAL_ABS_SUP_LE : thm
  REAL_SUP_ASCLOSE : thm
  SUP_UNIQUE_FINITE : thm
  SUP_INSERT_FINITE : thm
  SUP_SING : thm
  SUP_INSERT_INSERT : thm
  REAL_LE_SUP : thm
  REAL_SUP_LE_EQ : thm
  SUP_UNIQUE : thm
  SUP_UNION : thm
  ELEMENT_LE_SUP : thm
  SUP_APPROACH : thm
  REAL_MAX_SUP : thm
  inf : thm
  INF_EQ : thm
  INF : thm
  INF_FINITE_LEMMA : thm
  INF_FINITE : thm
  REAL_LE_INF_FINITE : thm
  REAL_INF_LE_FINITE : thm
  REAL_LT_INF_FINITE : thm
  REAL_INF_LT_FINITE : thm
  REAL_INF_UNIQUE : thm
  REAL_LE_INF : thm
  REAL_LE_INF_SUBSET : thm
  REAL_INF_BOUNDS : thm
  REAL_ABS_INF_LE : thm
  REAL_INF_ASCLOSE : thm
  INF_UNIQUE_FINITE : thm
  INF_INSERT_FINITE : thm
  INF_SING : thm
  INF_INSERT_INSERT : thm
  REAL_SUP_EQ_INF : thm
  REAL_INF_LE : thm
  REAL_LE_INF_EQ : thm
  INF_UNIQUE : thm
  INF_UNION : thm
  INF_LE_ELEMENT : thm
  INF_APPROACH : thm
  REAL_MIN_INF : thm
  deriving Inhabited

@[nospecialize]
def setupSetsSup [HolBase] (S : SetsCore) (P : SetsProps)
    (MESON_TAC : List thm → tactic) (ASM_MESON_TAC : List thm → tactic)
    (REFUTE_THEN : thm_tactic → tactic)
    (INTRO_TAC : String → tactic)
    (SELECT_CONV' : term → Except String thm)
    (REAL_ARITH' : term → IO (Except String thm))
    (REAL_ARITH_TAC : tactic)
    (IMP_CONJ : thm)
    (MEMBER_NOT_EMPTY IN_IMAGE FINITE_INSERT FINITE_EMPTY NOT_INSERT_EMPTY : thm)
    (NOT_IN_EMPTY IN_INSERT IN_SING FORALL_IN_INSERT FORALL_IN_UNION : thm)
    (FINITE_RULES FINITE_INDUCT_STRONG : thm)
    (REAL_COMPLETE REAL_LE_TOTAL REAL_LE_TRANS REAL_LE_ANTISYM REAL_LE_REFL : thm)
    (REAL_LTE_TRANS REAL_LET_TRANS REAL_NOT_LE REAL_NOT_LT : thm)
    (REAL_LE_NEG2 REAL_NEG_NEG real_max real_min : thm)
    (REAL_MAX_LE REAL_LE_MAX REAL_MIN_LE REAL_LE_MIN : thm)
    (REAL_BOUNDS_LE REAL_ABS_BOUNDS : thm)
    (new_definition' : term → IO (Except String thm)) :
    ExceptT String IO SetsSup := do
  let SET_TAC := SET_TAC S P MESON_TAC
  let SET_RULE := SET_RULE S P MESON_TAC
  let SELECT_CONV : ioconv := fun t => pure (SELECT_CONV' t)
  let REAL_ARITH (t : term) : ExceptT String IO thm := REAL_ARITH' t
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let { SELECT_UNIQUE, NOT_EXISTS_THM, DE_MORGAN_THM, .. } := HolBase.C

  /- Supremum and infimum. -/

  let sup ← new_definition
   r"sup s = @a:real. (!x. x IN s ==> x <= a) /\
                    !b. (!x. x IN s ==> x <= b) ==> a <= b"

  let SUP_EQ ← prove
   r"!s t. (!b. (!x. x IN s ==> x <= b) <=> (!x. x IN t ==> x <= b))
         ==> sup s = sup t"
   (SIMP_TAC [sup])

  let SUP ← prove
   r"!s. ~(s = {}) /\ (?b. !x. x IN s ==> x <= b)
       ==> (!x. x IN s ==> x <= sup s) /\
           !b. (!x. x IN s ==> x <= b) ==> sup s <= b"
   (REWRITE_TAC [sup] THEN CONV_TAC (ONCE_DEPTH_CONV SELECT_CONV) THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_COMPLETE THEN
    ASM_MESON_TAC [MEMBER_NOT_EMPTY])

  let SUP_FINITE_LEMMA ← prove
   r"!s. FINITE s /\ ~(s = {}) ==> ?b:real. b IN s /\ !x. x IN s ==> x <= b"
   (REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [NOT_INSERT_EMPTY, IN_INSERT] THEN
    REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY] THEN
    MESON_TAC [REAL_LE_TOTAL, REAL_LE_TRANS])

  let SUP_FINITE ← prove
   r"!s. FINITE s /\ ~(s = {}) ==> (sup s) IN s /\ !x. x IN s ==> x <= sup s"
   (GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP SUP_FINITE_LEMMA) THEN
    ASM_MESON_TAC [REAL_LE_ANTISYM, REAL_LE_TOTAL, SUP])

  let REAL_LE_SUP_FINITE ← prove
   r"!s a. FINITE s /\ ~(s = {}) ==> (a <= sup s <=> ?x. x IN s /\ a <= x)"
   (MESON_TAC [SUP_FINITE, REAL_LE_TRANS])

  let REAL_SUP_LE_FINITE ← prove
   r"!s a. FINITE s /\ ~(s = {}) ==> (sup s <= a <=> !x. x IN s ==> x <= a)"
   (MESON_TAC [SUP_FINITE, REAL_LE_TRANS])

  let REAL_LT_SUP_FINITE ← prove
   r"!s a. FINITE s /\ ~(s = {}) ==> (a < sup s <=> ?x. x IN s /\ a < x)"
   (MESON_TAC [SUP_FINITE, REAL_LTE_TRANS])

  let REAL_SUP_LT_FINITE ← prove
   r"!s a. FINITE s /\ ~(s = {}) ==> (sup s < a <=> !x. x IN s ==> x < a)"
   (MESON_TAC [SUP_FINITE, REAL_LET_TRANS])

  let REAL_SUP_UNIQUE ← prove
   r"!s b. (!x. x IN s ==> x <= b) /\
         (!b'. b' < b ==> ?x. x IN s /\ b' < x)
         ==> sup s = b"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [sup] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    ASM_MESON_TAC [REAL_NOT_LE, REAL_LE_ANTISYM])

  let REAL_SUP_LE ← prove
   r"!b. ~(s = {}) /\ (!x. x IN s ==> x <= b) ==> sup s <= b"
   (MESON_TAC [SUP])

  let REAL_SUP_LE_SUBSET ← prove
   r"!s t. ~(s = {}) /\ s SUBSET t /\ (?b. !x. x IN t ==> x <= b)
         ==> sup s <= sup t"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SUP_LE THEN
    MP_TAC (← SPEC (← q r"t:real->bool") SUP) THEN ASM SET_TAC [])

  let REAL_SUP_BOUNDS ← prove
   r"!s a b. ~(s = {}) /\ (!x. x IN s ==> a <= x /\ x <= b)
           ==> a <= sup s /\ sup s <= b"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← SPEC (← q r"s:real->bool") SUP) THEN ANTS_TAC THENL
     [ASM_MESON_TAC [], ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY]) THEN
    ASM_MESON_TAC [REAL_LE_TRANS])

  let REAL_ABS_SUP_LE ← prove
   r"!s a. ~(s = {}) /\ (!x. x IN s ==> abs(x) <= a) ==> abs(sup s) <= a"
   (REWRITE_TAC [← GSYM REAL_BOUNDS_LE, REAL_SUP_BOUNDS])

  let REAL_SUP_ASCLOSE ← prove
   r"!s l e. ~(s = {}) /\ (!x. x IN s ==> abs(x - l) <= e)
           ==> abs(sup s - l) <= e"
   (SIMP_TAC [← REAL_ARITH (← q r"abs(x - l):real <= e <=> l - e <= x /\ x <= l + e")] THEN
    REWRITE_TAC [REAL_SUP_BOUNDS])

  let SUP_UNIQUE_FINITE ← prove
   r"!s. FINITE s /\ ~(s = {})
       ==> (sup s = a <=> a IN s /\ !y. y IN s ==> y <= a)"
   (ASM_SIMP_TAC [← GSYM REAL_LE_ANTISYM, REAL_LE_SUP_FINITE, REAL_SUP_LE_FINITE,
                  NOT_INSERT_EMPTY, FINITE_INSERT, FINITE_EMPTY] THEN
    MESON_TAC [REAL_LE_REFL, REAL_LE_TRANS, REAL_LE_ANTISYM])

  let SUP_INSERT_FINITE ← prove
   r"!x s. FINITE s ==> sup(x INSERT s) = if s = {} then x else max x (sup s)"
   (REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [SUP_UNIQUE_FINITE,  FINITE_INSERT, FINITE_EMPTY,
                  NOT_INSERT_EMPTY, FORALL_IN_INSERT, NOT_IN_EMPTY] THEN
    REWRITE_TAC [IN_SING, REAL_LE_REFL] THEN
    REWRITE_TAC [real_max] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [SUP_FINITE, IN_INSERT, REAL_LE_REFL] THEN
    ASM_MESON_TAC [SUP_FINITE, REAL_LE_TOTAL, REAL_LE_TRANS])

  let SUP_SING ← prove
   r"!a. sup {a} = a"
   (SIMP_TAC [SUP_INSERT_FINITE, FINITE_EMPTY])

  let SUP_INSERT_INSERT ← prove
   r"!a b s. sup (b INSERT a INSERT s) = sup (max a b INSERT s)"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC SUP_EQ THEN
    X_GEN_TAC (← q r"c:real") THEN REWRITE_TAC [FORALL_IN_INSERT] THEN
    ASM_CASES_TAC (← q r"!x:real. x IN s ==> x <= c") THEN ASM_REWRITE_TAC [] THEN
    REAL_ARITH_TAC)

  let REAL_LE_SUP ← prove
   r"!s a b y. y IN s /\ a <= y /\ (!x. x IN s ==> x <= b) ==> a <= sup s"
   (MESON_TAC [SUP, MEMBER_NOT_EMPTY, REAL_LE_TRANS])

  let REAL_SUP_LE_EQ ← prove
   r"!s y. ~(s = {}) /\ (?b. !x. x IN s ==> x <= b)
         ==> (sup s <= y <=> !x. x IN s ==> x <= y)"
   (MESON_TAC [SUP, REAL_LE_TRANS])

  let SUP_UNIQUE ← prove
   r"!s b. (!c. (!x. x IN s ==> x <= c) <=> b <= c) ==> sup s = b"
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [← GSYM SUP_SING] THEN
    MATCH_MP_TAC SUP_EQ THEN ASM SET_TAC [])

  let SUP_UNION ← prove
   r"!s t. ~(s = {}) /\ ~(t = {}) /\
         (?b. !x. x IN s ==> x <= b) /\ (?c. !x. x IN t ==> x <= c)
         ==> sup(s UNION t) = max (sup s) (sup t)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUP_UNIQUE THEN
    REWRITE_TAC [FORALL_IN_UNION, REAL_MAX_LE] THEN
    ASM_MESON_TAC [SUP, REAL_LE_TRANS])

  let ELEMENT_LE_SUP ← prove
   r"!s a. (?b. !x. x IN s ==> x <= b) /\ a IN s ==> a <= sup s"
   (MESON_TAC [REAL_LE_SUP, REAL_LE_REFL])

  let SUP_APPROACH ← prove
   r"!s c. ~(s = {}) /\ (?b. !x. x IN s ==> x <= b) /\ c < sup s
         ==> ?x. x IN s /\ c < x"
   (INTRO_TAC "!s c; npty bound lt" THEN
    REFUTE_THEN (LABEL_TAC "hp" o
      REWRITE_RULE [NOT_EXISTS_THM, DE_MORGAN_THM, REAL_NOT_LT]) THEN
    REMOVE_THEN "lt" MP_TAC THEN REWRITE_TAC [REAL_NOT_LT] THEN
    HYP (MP_TAC o MATCH_MP SUP o end_itlist CONJ) "npty bound" [] THEN
    INTRO_TAC "_ sup" THEN REMOVE_THEN "sup" MATCH_MP_TAC THEN
    ASM_MESON_TAC [])

  let REAL_MAX_SUP ← prove
   r"!x y. max x y = sup {x,y}"
   (SIMP_TAC [← GSYM REAL_LE_ANTISYM, REAL_SUP_LE_FINITE, REAL_LE_SUP_FINITE,
              FINITE_RULES, NOT_INSERT_EMPTY, REAL_MAX_LE, REAL_LE_MAX] THEN
    REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN MESON_TAC [REAL_LE_TOTAL])

  let inf ← new_definition
   r"inf s = @a:real. (!x. x IN s ==> a <= x) /\
                    !b. (!x. x IN s ==> b <= x) ==> b <= a"

  let INF_EQ ← prove
   r"!s t. (!a. (!x. x IN s ==> a <= x) <=> (!x. x IN t ==> a <= x))
         ==> inf s = inf t"
   (SIMP_TAC [inf])

  let INF ← prove
   r"!s. ~(s = {}) /\ (?b. !x. x IN s ==> b <= x)
       ==> (!x. x IN s ==> inf s <= x) /\
           !b. (!x. x IN s ==> b <= x) ==> b <= inf s"
   (GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [inf] THEN
    CONV_TAC (ONCE_DEPTH_CONV SELECT_CONV) THEN
    ONCE_REWRITE_TAC [← GSYM REAL_LE_NEG2] THEN
    EXISTS_TAC (← q r"--(sup (IMAGE (--) s))") THEN
    MP_TAC (← SPEC (← q r"IMAGE (--) (s:real->bool)") SUP) THEN
    REWRITE_TAC [REAL_NEG_NEG] THEN
    ABBREV_TAC (← q r"a = sup (IMAGE (--) s)") THEN
    REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_IMAGE] THEN
    ASM_MESON_TAC [REAL_NEG_NEG, MEMBER_NOT_EMPTY, REAL_LE_NEG2])

  let INF_FINITE_LEMMA ← prove
   r"!s. FINITE s /\ ~(s = {}) ==> ?b:real. b IN s /\ !x. x IN s ==> b <= x"
   (REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [NOT_INSERT_EMPTY, IN_INSERT] THEN
    REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY] THEN
    MESON_TAC [REAL_LE_TOTAL, REAL_LE_TRANS])

  let INF_FINITE ← prove
   r"!s. FINITE s /\ ~(s = {}) ==> (inf s) IN s /\ !x. x IN s ==> inf s <= x"
   (GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP INF_FINITE_LEMMA) THEN
    ASM_MESON_TAC [REAL_LE_ANTISYM, REAL_LE_TOTAL, INF])

  let REAL_LE_INF_FINITE ← prove
   r"!s a. FINITE s /\ ~(s = {}) ==> (a <= inf s <=> !x. x IN s ==> a <= x)"
   (MESON_TAC [INF_FINITE, REAL_LE_TRANS])

  let REAL_INF_LE_FINITE ← prove
   r"!s a. FINITE s /\ ~(s = {}) ==> (inf s <= a <=> ?x. x IN s /\ x <= a)"
   (MESON_TAC [INF_FINITE, REAL_LE_TRANS])

  let REAL_LT_INF_FINITE ← prove
   r"!s a. FINITE s /\ ~(s = {}) ==> (a < inf s <=> !x. x IN s ==> a < x)"
   (MESON_TAC [INF_FINITE, REAL_LTE_TRANS])

  let REAL_INF_LT_FINITE ← prove
   r"!s a. FINITE s /\ ~(s = {}) ==> (inf s < a <=> ?x. x IN s /\ x < a)"
   (MESON_TAC [INF_FINITE, REAL_LET_TRANS])

  let REAL_INF_UNIQUE ← prove
   r"!s b. (!x. x IN s ==> b <= x) /\
         (!b'. b < b' ==> ?x. x IN s /\ x < b')
         ==> inf s = b"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [inf] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    ASM_MESON_TAC [REAL_NOT_LE, REAL_LE_ANTISYM])

  let REAL_LE_INF ← prove
   r"!b. ~(s = {}) /\ (!x. x IN s ==> b <= x) ==> b <= inf s"
   (MESON_TAC [INF])

  let REAL_LE_INF_SUBSET ← prove
   r"!s t. ~(t = {}) /\ t SUBSET s /\ (?b. !x. x IN s ==> b <= x)
         ==> inf s <= inf t"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_INF THEN
    MP_TAC (← SPEC (← q r"s:real->bool") INF) THEN ASM SET_TAC [])

  let REAL_INF_BOUNDS ← prove
   r"!s a b. ~(s = {}) /\ (!x. x IN s ==> a <= x /\ x <= b)
           ==> a <= inf s /\ inf s <= b"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← SPEC (← q r"s:real->bool") INF) THEN ANTS_TAC THENL
     [ASM_MESON_TAC [], ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY]) THEN
    ASM_MESON_TAC [REAL_LE_TRANS])

  let REAL_ABS_INF_LE ← prove
   r"!s a. ~(s = {}) /\ (!x. x IN s ==> abs(x) <= a) ==> abs(inf s) <= a"
   (REWRITE_TAC [← GSYM REAL_BOUNDS_LE, REAL_INF_BOUNDS])

  let REAL_INF_ASCLOSE ← prove
   r"!s l e. ~(s = {}) /\ (!x. x IN s ==> abs(x - l) <= e)
           ==> abs(inf s - l) <= e"
   (SIMP_TAC [← REAL_ARITH (← q r"abs(x - l):real <= e <=> l - e <= x /\ x <= l + e")] THEN
    REWRITE_TAC [REAL_INF_BOUNDS])

  let INF_UNIQUE_FINITE ← prove
   r"!s. FINITE s /\ ~(s = {})
       ==> (inf s = a <=> a IN s /\ !y. y IN s ==> a <= y)"
   (ASM_SIMP_TAC [← GSYM REAL_LE_ANTISYM, REAL_LE_INF_FINITE, REAL_INF_LE_FINITE,
                  NOT_INSERT_EMPTY, FINITE_INSERT, FINITE_EMPTY] THEN
    MESON_TAC [REAL_LE_REFL, REAL_LE_TRANS, REAL_LE_ANTISYM])

  let INF_INSERT_FINITE ← prove
   r"!x s. FINITE s ==> inf(x INSERT s) = if s = {} then x else min x (inf s)"
   (REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [INF_UNIQUE_FINITE,  FINITE_INSERT, FINITE_EMPTY,
                  NOT_INSERT_EMPTY, FORALL_IN_INSERT, NOT_IN_EMPTY] THEN
    REWRITE_TAC [IN_SING, REAL_LE_REFL] THEN
    REWRITE_TAC [real_min] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [INF_FINITE, IN_INSERT, REAL_LE_REFL] THEN
    ASM_MESON_TAC [INF_FINITE, REAL_LE_TOTAL, REAL_LE_TRANS])

  let INF_SING ← prove
   r"!a. inf {a} = a"
   (SIMP_TAC [INF_INSERT_FINITE, FINITE_EMPTY])

  let INF_INSERT_INSERT ← prove
   r"!a b s. inf (b INSERT a INSERT s) = inf (min a b INSERT s)"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC INF_EQ THEN
    X_GEN_TAC (← q r"c:real") THEN REWRITE_TAC [FORALL_IN_INSERT] THEN
    ASM_CASES_TAC (← q r"!x:real. x IN s ==> c <= x") THEN ASM_REWRITE_TAC [] THEN
    REAL_ARITH_TAC)

  let REAL_SUP_EQ_INF ← prove
   r"!s. ~(s = {}) /\ (?B. !x. x IN s ==> abs(x) <= B)
       ==> (sup s = inf s <=> ?a. s = {a})"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC (← q r"sup s") THEN MATCH_MP_TAC
       (← SET_RULE (← q r"~(s = {}) /\ (!x. x IN s ==> x = a) ==> s = {a}")) THEN
      ASM_REWRITE_TAC [← GSYM REAL_LE_ANTISYM] THEN
      ASM_MESON_TAC [SUP, REAL_ABS_BOUNDS, INF],
      STRIP_TAC THEN
      ASM_SIMP_TAC [SUP_INSERT_FINITE, INF_INSERT_FINITE, FINITE_EMPTY]])

  let REAL_INF_LE ← prove
   r"!s a b y. y IN s /\ y <= b /\ (!x. x IN s ==> a <= x) ==> inf s <= b"
   (MESON_TAC [INF, MEMBER_NOT_EMPTY, REAL_LE_TRANS])

  let REAL_LE_INF_EQ ← prove
   r"!s y. ~(s = {}) /\ (?b. !x. x IN s ==> b <= x)
         ==> (y <= inf s <=> !x. x IN s ==> y <= x)"
   (MESON_TAC [INF, REAL_LE_TRANS])

  let INF_UNIQUE ← prove
   r"!s b. (!c. (!x. x IN s ==> c <= x) <=> c <= b) ==> inf s = b"
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [← GSYM INF_SING] THEN
    MATCH_MP_TAC INF_EQ THEN ASM SET_TAC [])

  let INF_UNION ← prove
   r"!s t. ~(s = {}) /\ ~(t = {}) /\
         (?b. !x. x IN s ==> b <= x) /\ (?c. !x. x IN t ==> c <= x)
         ==> inf(s UNION t) = min (inf s) (inf t)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC INF_UNIQUE THEN
    REWRITE_TAC [FORALL_IN_UNION, REAL_LE_MIN] THEN
    ASM_MESON_TAC [INF, REAL_LE_TRANS])

  let INF_LE_ELEMENT ← prove
   r"!s a. (?b. !x. x IN s ==> b <= x) /\ a IN s ==> inf s <= a"
   (MESON_TAC [REAL_INF_LE, REAL_LE_REFL])

  let INF_APPROACH ← prove
   r"!s c. ~(s = {}) /\ (?b. !x. x IN s ==> b <= x) /\ inf s < c
         ==> ?x. x IN s /\ x < c"
   (INTRO_TAC "!s c; npty bound lt" THEN
    REFUTE_THEN (LABEL_TAC "hp" o
      REWRITE_RULE [NOT_EXISTS_THM, DE_MORGAN_THM, REAL_NOT_LT]) THEN
    REMOVE_THEN "lt" MP_TAC THEN REWRITE_TAC [REAL_NOT_LT] THEN
    HYP (MP_TAC o MATCH_MP INF o end_itlist CONJ) "npty bound" [] THEN
    INTRO_TAC "_ inf" THEN REMOVE_THEN "inf" MATCH_MP_TAC THEN
    ASM_MESON_TAC [])

  let REAL_MIN_INF ← prove
   r"!x y. min x y = inf {x,y}"
   (SIMP_TAC [← GSYM REAL_LE_ANTISYM, REAL_INF_LE_FINITE, REAL_LE_INF_FINITE,
              FINITE_RULES, NOT_INSERT_EMPTY, REAL_MIN_LE, REAL_LE_MIN] THEN
    REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN MESON_TAC [REAL_LE_TOTAL])

  return {
    sup, SUP_EQ, SUP, SUP_FINITE_LEMMA, SUP_FINITE, REAL_LE_SUP_FINITE,
    REAL_SUP_LE_FINITE, REAL_LT_SUP_FINITE, REAL_SUP_LT_FINITE,
    REAL_SUP_UNIQUE, REAL_SUP_LE, REAL_SUP_LE_SUBSET, REAL_SUP_BOUNDS,
    REAL_ABS_SUP_LE, REAL_SUP_ASCLOSE, SUP_UNIQUE_FINITE, SUP_INSERT_FINITE,
    SUP_SING, SUP_INSERT_INSERT, REAL_LE_SUP, REAL_SUP_LE_EQ, SUP_UNIQUE,
    SUP_UNION, ELEMENT_LE_SUP, SUP_APPROACH, REAL_MAX_SUP, inf, INF_EQ, INF,
    INF_FINITE_LEMMA, INF_FINITE, REAL_LE_INF_FINITE, REAL_INF_LE_FINITE,
    REAL_LT_INF_FINITE, REAL_INF_LT_FINITE, REAL_INF_UNIQUE, REAL_LE_INF,
    REAL_LE_INF_SUBSET, REAL_INF_BOUNDS, REAL_ABS_INF_LE, REAL_INF_ASCLOSE,
    INF_UNIQUE_FINITE, INF_INSERT_FINITE, INF_SING, INF_INSERT_INSERT,
    REAL_SUP_EQ_INF, REAL_INF_LE, REAL_LE_INF_EQ, INF_UNIQUE, INF_UNION,
    INF_LE_ELEMENT, INF_APPROACH, REAL_MIN_INF }

/- ---------------------------------------------------------------------- -/
/- Relational counterparts of sup and inf.               (sets.ml 5028-5182) -/
/- ---------------------------------------------------------------------- -/

/-- `parse_as_infix ("has_inf",(12,"right"))` and
    `parse_as_infix ("has_sup",(12,"right"))` (sets.ml 5030-5031).  Session
    runs it once, before `setupSetsHasInfSup`. -/
def setupSetsHasInfSupInfix : IO Unit := do
  HolCore.Printer.parse_as_infix ("has_inf", (12, "right"))
  HolCore.Printer.parse_as_infix ("has_sup", (12, "right"))

/-- The relational sup/inf bundle of `sets.ml 5033-5182`: the two
    `new_definition`s `has_inf`/`has_sup` and the 14 `prove`s connecting them
    to `inf`/`sup` (`HAS_INF_INF`/`HAS_SUP_SUP`, existence, approach, the
    `HAS_INF`/`HAS_SUP` characterisations and the monotone `HAS_INF_LE`/
    `HAS_SUP_LE`).  The `has_inf`/`has_sup` infix fixities MUST already be
    registered by `setupSetsHasInfSupInfix`; the `SISup` accessor forces it
    first.  Proof-heavy in the `theorems.ml` Part-B DSL - `INTRO_TAC`/
    `HYP_TAC`/`CLAIM_TAC`/`REFUTE_THEN`/`REMOVE_THEN`/`USE_THEN`/`HYP` - so
    those are threaded in alongside the sup/inf bundle and `ASM_REAL_ARITH_TAC`. -/
structure SetsHasInfSup where
  has_inf : thm
  has_sup : thm
  HAS_INF_LBOUND : thm
  HAS_SUP_UBOUND : thm
  HAS_INF_INF : thm
  HAS_SUP_SUP : thm
  INF_EXISTS : thm
  SUP_EXISTS : thm
  HAS_INF_APPROACH : thm
  HAS_SUP_APPROACH : thm
  HAS_INF : thm
  HAS_SUP : thm
  HAS_INF_LE : thm
  HAS_SUP_LE : thm
  deriving Inhabited

/-- `HYP_TAC` takes a rule `thm -> Except String thm`, so Session supplies
    `REWRITE_RULE_PURE` and `MATCH_MP_PURE` for its rule arguments. -/
@[nospecialize]
def setupSetsHasInfSup [HolBase] (SSup : SetsSup)
    (MESON_TAC : List thm → tactic) (ASM_MESON_TAC : List thm → tactic)
    (REFUTE_THEN : thm_tactic → tactic)
    (INTRO_TAC : String → tactic)
    (HYP_TAC : String → (thm → Except String thm) → tactic)
    (CLAIM_TAC : String → term → tactic)
    (REWRITE_RULE_PURE : List thm → thm → Except String thm)
    (MATCH_MP_PURE : thm → thm → Except String thm)
    (REAL_ARITH_TAC ASM_REAL_ARITH_TAC : tactic)
    (NOT_IN_EMPTY NOT_FORALL_THM REAL_LE_REFL REAL_LE_TRANS : thm)
    (REAL_NOT_LT REAL_NOT_LE : thm)
    (new_definition' : term → IO (Except String thm)) :
    ExceptT String IO SetsHasInfSup := do
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let SPEC_PURE (t : term) (th : thm) : Except String thm := HolBase.B.SPEC t th
  let { NOT_EXISTS_THM, .. } := HolBase.C
  let { INF, SUP, INF_UNIQUE, SUP_UNIQUE, INF_APPROACH, SUP_APPROACH, .. } := SSup

  let has_inf ← new_definition
   r"s has_inf b <=> (!c. (!x:real. x IN s ==> c <= x) <=> c <= b)"

  let has_sup ← new_definition
   r"s has_sup b <=> (!c. (!x:real. x IN s ==> x <= c) <=> b <= c)"

  let HAS_INF_LBOUND ← prove
   r"!s b x. s has_inf b /\ x IN s ==> b <= x"
   (REPEAT GEN_TAC THEN REWRITE_TAC [has_inf] THEN MESON_TAC [REAL_LE_REFL])

  let HAS_SUP_UBOUND ← prove
   r"!s b x. s has_sup b /\ x IN s ==> x <= b"
   (REPEAT GEN_TAC THEN REWRITE_TAC [has_sup] THEN MESON_TAC [REAL_LE_REFL])

  let HAS_INF_INF ← prove
   r"!s l. s has_inf l <=>
         ~(s = {}) /\
         (?b. !x. x IN s ==> b <= x) /\
         inf s = l"
   (GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [has_inf] THEN
    EQ_TAC THEN STRIP_TAC THENL
    [CONJ_TAC THENL
     [REFUTE_THEN SUBST_ALL_TAC THEN
      POP_ASSUM MP_TAC THEN REWRITE_TAC [NOT_IN_EMPTY, NOT_FORALL_THM] THEN
      EXISTS_TAC (← q r"l + &1:real") THEN REAL_ARITH_TAC,
      ALL_TAC] THEN
     CONJ_TAC THENL
     [ASM_REWRITE_TAC [] THEN MESON_TAC [REAL_LE_REFL], ALL_TAC] THEN
     MATCH_MP_TAC INF_UNIQUE THEN ASM_REWRITE_TAC [],
     GEN_TAC THEN MP_TAC (← SPEC (← q r"s:real->bool") INF) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN
     POP_ASSUM SUBST_ALL_TAC THEN STRIP_TAC THEN EQ_TAC THEN
     ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
     TRANS_TAC REAL_LE_TRANS (← q r"l:real") THEN ASM_SIMP_TAC []])

  let HAS_SUP_SUP ← prove
   r"!s l. s has_sup l <=>
         ~(s = {}) /\
         (?b. !x. x IN s ==> x <= b) /\
         sup s = l"
   (GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [has_sup] THEN
    EQ_TAC THEN STRIP_TAC THENL
    [CONJ_TAC THENL
     [REFUTE_THEN SUBST_ALL_TAC THEN
      POP_ASSUM MP_TAC THEN REWRITE_TAC [NOT_IN_EMPTY, NOT_FORALL_THM] THEN
      EXISTS_TAC (← q r"l - &1:real") THEN REAL_ARITH_TAC,
      ALL_TAC] THEN
     CONJ_TAC THENL
     [ASM_REWRITE_TAC [] THEN MESON_TAC [REAL_LE_REFL], ALL_TAC] THEN
     MATCH_MP_TAC SUP_UNIQUE THEN ASM_REWRITE_TAC [],
     GEN_TAC THEN MP_TAC (← SPEC (← q r"s:real->bool") SUP) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
     POP_ASSUM SUBST_ALL_TAC THEN STRIP_TAC THEN EQ_TAC THEN
     ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
     TRANS_TAC REAL_LE_TRANS (← q r"l:real") THEN ASM_SIMP_TAC []])

  let INF_EXISTS ← prove
   r"!s. (?l. s has_inf l) <=> ~(s = {}) /\ (?b. !x. x IN s ==> b <= x)"
   (MESON_TAC [HAS_INF_INF])

  let SUP_EXISTS ← prove
   r"!s. (?l. s has_sup l) <=> ~(s = {}) /\ (?b. !x. x IN s ==> x <= b)"
   (MESON_TAC [HAS_SUP_SUP])

  let HAS_INF_APPROACH ← prove
   r"!s l c. s has_inf l /\ l < c ==> ?x. x IN s /\ x < c"
   (REWRITE_TAC [HAS_INF_INF] THEN MESON_TAC [INF_APPROACH])

  let HAS_SUP_APPROACH ← prove
   r"!s l c. s has_sup l /\ c < l ==> ?x. x IN s /\ c < x"
   (REWRITE_TAC [HAS_SUP_SUP] THEN MESON_TAC [SUP_APPROACH])

  let HAS_INF ← prove
   r"!s l. s has_inf l <=>
         ~(s = {}) /\
         (!x. x IN s ==> l <= x) /\
         (!c. l < c ==> ?x. x IN s /\ x < c)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
    [INTRO_TAC "hp" THEN CONJ_TAC THENL
     [HYP_TAC "hp" (REWRITE_RULE_PURE [HAS_INF_INF]) THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
     CONJ_TAC THENL
     [ASM_MESON_TAC [HAS_INF_LBOUND], ASM_MESON_TAC [HAS_INF_APPROACH]],
     ALL_TAC] THEN
    INTRO_TAC "ne bound approach" THEN ASM_REWRITE_TAC [has_inf] THEN
    GEN_TAC THEN EQ_TAC THENL
    [INTRO_TAC "hp" THEN REWRITE_TAC [← GSYM REAL_NOT_LT] THEN INTRO_TAC "lc" THEN
     REMOVE_THEN "approach" (MP_TAC o SPEC (← q r"(l + c) / &2")) THEN
     ANTS_TAC THENL [ASM_REAL_ARITH_TAC, INTRO_TAC "@x0. x0 +"] THEN
     USE_THEN "x0" (HYP_TAC "hp" o C MATCH_MP_PURE) THEN ASM_REAL_ARITH_TAC,
     INTRO_TAC "hp; !x; x" THEN TRANS_TAC REAL_LE_TRANS (← q r"l:real") THEN
     ASM_SIMP_TAC []])

  let HAS_SUP ← prove
   r"!s l. s has_sup l <=>
         ~(s = {}) /\
         (!x. x IN s ==> x <= l) /\
         (!c. c < l ==> ?x. x IN s /\ c < x)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
    [INTRO_TAC "hp" THEN CONJ_TAC THENL
     [HYP_TAC "hp" (REWRITE_RULE_PURE [HAS_SUP_SUP]) THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
     CONJ_TAC THENL
     [ASM_MESON_TAC [HAS_SUP_UBOUND], ASM_MESON_TAC [HAS_SUP_APPROACH]],
     ALL_TAC] THEN
    INTRO_TAC "ne bound approach" THEN ASM_REWRITE_TAC [has_sup] THEN
    GEN_TAC THEN EQ_TAC THENL
    [INTRO_TAC "hp" THEN REWRITE_TAC [← GSYM REAL_NOT_LT] THEN INTRO_TAC "lc" THEN
     REMOVE_THEN "approach" (MP_TAC o SPEC (← q r"(l + c) / &2")) THEN
     ANTS_TAC THENL [ASM_REAL_ARITH_TAC, INTRO_TAC "@x0. x0 +"] THEN
     USE_THEN "x0" (HYP_TAC "hp" o C MATCH_MP_PURE) THEN ASM_REAL_ARITH_TAC,
     INTRO_TAC "hp; !x; x" THEN TRANS_TAC REAL_LE_TRANS (← q r"l:real") THEN
     ASM_SIMP_TAC []])

  let HAS_INF_LE ← prove
   r"!s t l m. s has_inf l /\ t has_inf m /\
             (!y. y IN t ==> ?x. x IN s /\ x <= y)
             ==> l <= m"
   (INTRO_TAC "!s t l m; l m le" THEN
    HYP_TAC "l: s l1 l2" (REWRITE_RULE_PURE [HAS_INF]) THEN
    HYP_TAC "m: t m1 m2" (REWRITE_RULE_PURE [HAS_INF]) THEN
    REFUTE_THEN (LABEL_TAC "lt" o REWRITE_RULE [REAL_NOT_LE]) THEN
    CLAIM_TAC "@c. c1 c2" (← q r"?c:real. m < c /\ c < l") THENL
    [EXISTS_TAC (← q r"(l + m) / &2") THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    HYP_TAC "m2: +" (SPEC_PURE (← q r"c:real")) THEN ASM_REWRITE_TAC [NOT_EXISTS_THM] THEN
    INTRO_TAC "!x; x xc" THEN
    CLAIM_TAC "@y. y yx" (← q r"?y:real. y IN s /\ y <= x") THENL
    [HYP MESON_TAC "le x" [], ALL_TAC] THEN
    HYP_TAC "l1: +" (SPEC_PURE (← q r"y:real")) THEN ASM_REWRITE_TAC [] THEN
    ASM_REAL_ARITH_TAC)

  let HAS_SUP_LE ← prove
   r"!s t l m. s has_sup l /\ t has_sup m /\
             (!y. y IN t ==> ?x. x IN s /\ y <= x)
             ==> m <= l"
   (INTRO_TAC "!s t l m; l m le" THEN
    HYP_TAC "l: s l1 l2" (REWRITE_RULE_PURE [HAS_SUP]) THEN
    HYP_TAC "m: t m1 m2" (REWRITE_RULE_PURE [HAS_SUP]) THEN
    REFUTE_THEN (LABEL_TAC "lt" o REWRITE_RULE [REAL_NOT_LE]) THEN
    CLAIM_TAC "@c. c1 c2" (← q r"?c:real. l < c /\ c < m") THENL
    [EXISTS_TAC (← q r"(l + m) / &2") THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    HYP_TAC "m2: +" (SPEC_PURE (← q r"c:real")) THEN ASM_REWRITE_TAC [NOT_EXISTS_THM] THEN
    INTRO_TAC "!x; x xc" THEN
    CLAIM_TAC "@y. y yx" (← q r"?y:real. y IN s /\ x <= y") THENL
    [HYP MESON_TAC "le x" [], ALL_TAC] THEN
    HYP_TAC "l1: +" (SPEC_PURE (← q r"y:real")) THEN ASM_REWRITE_TAC [] THEN
    ASM_REAL_ARITH_TAC)

  return {
    has_inf, has_sup, HAS_INF_LBOUND, HAS_SUP_UBOUND, HAS_INF_INF, HAS_SUP_SUP,
    INF_EXISTS, SUP_EXISTS, HAS_INF_APPROACH, HAS_SUP_APPROACH, HAS_INF,
    HAS_SUP, HAS_INF_LE, HAS_SUP_LE }

/- ---------------------------------------------------------------------- -/
/- Inductive definition of sets, by reducing them to inductive relations. -/
/- (sets.ml 5183-5217)                                                    -/
/- ---------------------------------------------------------------------- -/

/-- `new_inductive_set` (sets.ml 5186). -/
def new_inductive_set [HolBase] (IN : thm) (and_tm : term)
    (new_inductive_definition : term → IO (Except String (thm × thm × thm)))
    (tm : term) : IO (Except String (thm × thm × thm)) := ExceptT.run do
  let const_of_var (v : term) : ExceptT String IO term :=
    ExceptT.mk (mk_mconst (HolCore.Printer.name_of v) (type_of v))
  let comb_all (tm : term) : Except String term := do
    let rec f (n : Nat) (tm : term) : List hol_type → Except String term
      | [] => pure tm
      | ty :: tys => do
          let v ← variant (← variables tm) (mk_var ("x" ++ toString n) ty)
          f (n + 1) (← mk_comb tm v) tys
    let tys := (splitlist dest_fun_ty (type_of tm)).1
    f 0 tm tys
  let mk_eqin (ptm : term) : ExceptT String IO thm := do
    REWR_CONV (← GSYM IN) (← comb_all ptm)
  let transf (conv : ioconv) (tm : term) : ExceptT String IO term := do
    pure (← rhs (concl (← conv tm)))
  let remove_in_conv (ptm : term) : ExceptT String IO ioconv := do
    let rconv := REWR_CONV (← SYM (← mk_eqin ptm))
    pure (fun tm => ExceptT.run do
      let htm := (strip_comb (← dest_binary "IN" tm).2).1
      if htm == ptm then rconv tm else throw "remove_in_conv")
  let remove_in_transf (ps : List term) (tm : term) : ExceptT String IO term := do
    transf (ONCE_DEPTH_CONV (FIRST_CONV (← ps.mapM remove_in_conv))) tm
  let rule_head (tm : term) : ExceptT String IO term := do
    let tm := (strip_forall tm).2
    let tm := (splitlist (dest_binop (← q r"(==>)")) tm).2
    let tm := (← dest_binary "IN" tm).2
    pure (strip_comb tm).1
  -- `find_pvars = setify o map rule_head o binops `(/\)``: `and_tm` is that
  -- quotation, parsed once when sets.ml loads (sets.ml 5209); `rule_head`'s
  -- `(==>)` is inside the function, so parsed per call.
  let find_pvars (tm : term) : ExceptT String IO (List term) := do
    pure (setify (← (binops and_tm tm).mapM rule_head))
  let pvars ← find_pvars tm
  let dtm ← remove_in_transf pvars tm
  let (th_rules, th_induct, th_cases) ← new_inductive_definition dtm
  let insert_in_rule := REWRITE_RULE (← pvars.mapM (fun p => do mk_eqin (← const_of_var p)))
  -- An OCaml tuple is evaluated right to left.
  let c ← insert_in_rule th_cases
  let i ← insert_in_rule th_induct
  let r ← insert_in_rule th_rules
  pure (r, i, c)

end HolMath.Sets
