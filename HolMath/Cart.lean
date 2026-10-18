/- ---------------------------------------------------------------------- -/
/- File: Cart.lean
Definition of finite Cartesian product types.
Original (c) Copyright, John Harrison 1998-2007
Original (c) Copyright, Andrea Gabrielli, Marco Maggesi 2017-2018
Lean4 translation by Chris Walton 2026

  This file creates new types: five via `new_type_definition` (`finite_image`,
  `cart`, `finite_sum`, `finite_diff`, `finite_prod`) and two via `define_type`
  (`tybit0`, `tybit1`, which make `:2`, `:3`, `:4` ... exist).  These are
  kernel side effects, so they run exactly once and in file order.  The `^`
  type infix is hard-wired into the parser/printer (not declared here) and maps
  to the type operator `cart`; it is inert until `new_type_definition "cart"`
  runs.  Three parser side effects also live here: `parse_as_infix "$"` (vector
  indexing), `parse_as_binder "lambda"`, and `parse_as_infix "PCROSS"`.
-/

import HolMath.Iterate
import HolMath.Base

namespace HolMath.Cart

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms DSLThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax

/-- The `dimindex` definition and the eight theorems about it (cart.ml
    14-48).  `dimindex(s:A->bool)` is the size of the indexing type `:A` -
    `CARD(:A)` when `:A` is finite, else `1` - and EVERYTHING downstream in
    this file (the cart type's dimension, `$` indexing, `lambda`) rests on it.
    `dimindex` (14) is the sole `new_definition`; the other eight are `prove`,
    except `DIMINDEX_1` (48) which is `MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_1`.
    Rests on the Sets/CARD layer's `FINITE`/`CARD`/`UNIV` (all reachable from
    the parser at this point) and, for the cardinality lemmas, `HAS_SIZE`,
    `CARD_EQ_0`, `CARD_CLAUSES`, the `:1` type's `one`, and `NUMSEG_LT` from
    iterate.ml. -/
structure CartDimindex where
  /-- `dimindex` (cart.ml 14): `dimindex(s:A->bool) = if FINITE(:A) then
      CARD(:A) else 1`.  `new_definition`. -/
  dimindex : thm
  /-- `DIMINDEX_NONZERO` (cart.ml 17): `!s:A->bool. ~(dimindex(s) = 0)`.
      `GEN_TAC THEN REWRITE_TAC[dimindex] THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[CARD_EQ_0; ARITH] THEN SET_TAC[]`. -/
  DIMINDEX_NONZERO : thm
  /-- `DIMINDEX_GE_1` (cart.ml 22): `!s:A->bool. 1 <= dimindex(s)`.
      `REWRITE_TAC[ARITH_RULE \`1 <= x <=> ~(x = 0)\`; DIMINDEX_NONZERO]`. -/
  DIMINDEX_GE_1 : thm
  /-- `DIMINDEX_UNIV` (cart.ml 26): `!s. dimindex(s:A->bool) = dimindex(:A)`.
      `REWRITE_TAC[dimindex]`. -/
  DIMINDEX_UNIV : thm
  /-- `DIMINDEX_UNIQUE` (cart.ml 30): `(:A) HAS_SIZE n ==> dimindex(:A) = n`.
      `MESON_TAC[dimindex; HAS_SIZE]`. -/
  DIMINDEX_UNIQUE : thm
  /-- `UNIV_HAS_SIZE_DIMINDEX` (cart.ml 34):
      `(:N) HAS_SIZE dimindex (:N) <=> FINITE(:N)`.
      `MESON_TAC[HAS_SIZE; dimindex]`. -/
  UNIV_HAS_SIZE_DIMINDEX : thm
  /-- `HAS_SIZE_1` (cart.ml 38): `(:1) HAS_SIZE 1`.  `SUBGOAL_THEN \`(:1) =
      {one}\` SUBST1_TAC THENL [b1; b2]` (width 2). -/
  HAS_SIZE_1 : thm
  /-- `NUMSEG_LT_DIMINDEX` (cart.ml 44):
      `{i | i < dimindex(:N)} = 0..dimindex(:N)-1`.
      `REWRITE_TAC[NUMSEG_LT; DIMINDEX_NONZERO]`. -/
  NUMSEG_LT_DIMINDEX : thm
  /-- `DIMINDEX_1` (cart.ml 48): `dimindex(:1) = 1`, via
      `MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_1`. -/
  DIMINDEX_1 : thm
  deriving Inhabited

/-- cart.ml 10-48: association of a number with an indexing type.  `one` is
    the theorem `one` from the `:1` type. -/
@[nospecialize]
def setupCartDimindex [HolBase]
    (new_definition' : term → IO (Except String thm))
    (MESON_TAC : List thm → tactic)
    (SET_TAC : List thm → tactic)
    (ARITH_RULE' : term → IO (Except String thm))
    (one : thm)
    (HAS_SIZE CARD_EQ_0 CARD_CLAUSES FINITE_RULES EXTENSION IN_UNIV IN_SING
     NOT_IN_EMPTY ARITH NUMSEG_LT : thm) :
    ExceptT String IO CartDimindex := do
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let ARITH_RULE (t : term) : ExceptT String IO thm := ARITH_RULE' t

  /- Association of a number with an indexing type. -/

  let dimindex ← new_definition
   r"dimindex(s:A->bool) = if FINITE(:A) then CARD(:A) else 1"

  let DIMINDEX_NONZERO ← prove
   r"!s:A->bool. ~(dimindex(s) = 0)"
   (GEN_TAC THEN REWRITE_TAC [dimindex] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [CARD_EQ_0, ARITH] THEN SET_TAC [])

  let DIMINDEX_GE_1 ← prove
   r"!s:A->bool. 1 <= dimindex(s)"
   (REWRITE_TAC [← ARITH_RULE (← q r"1 <= x <=> ~(x = 0)"), DIMINDEX_NONZERO])

  let DIMINDEX_UNIV ← prove
   r"!s. dimindex(s:A->bool) = dimindex(:A)"
   (REWRITE_TAC [dimindex])

  let DIMINDEX_UNIQUE ← prove
   r"(:A) HAS_SIZE n ==> dimindex(:A) = n"
   (MESON_TAC [dimindex, HAS_SIZE])

  let UNIV_HAS_SIZE_DIMINDEX ← prove
   r"(:N) HAS_SIZE dimindex (:N) <=> FINITE(:N)"
   (MESON_TAC [HAS_SIZE, dimindex])

  let HAS_SIZE_1 ← prove
   r"(:1) HAS_SIZE 1"
   (SUBGOAL_THEN (← q r"(:1) = {one}") SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_UNIV, IN_SING] THEN MESON_TAC [one],
      SIMP_TAC [NOT_IN_EMPTY, HAS_SIZE, FINITE_RULES, CARD_CLAUSES, ARITH]])

  let NUMSEG_LT_DIMINDEX ← prove
   r"{i | i < dimindex(:N)} = 0..dimindex(:N)-1"
   (REWRITE_TAC [NUMSEG_LT, DIMINDEX_NONZERO])

  let DIMINDEX_1 ← MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_1

  return {
    dimindex, DIMINDEX_NONZERO, DIMINDEX_GE_1, DIMINDEX_UNIV, DIMINDEX_UNIQUE,
    UNIV_HAS_SIZE_DIMINDEX, HAS_SIZE_1, NUMSEG_LT_DIMINDEX, DIMINDEX_1 }

/-- The `finite_image` type-bijection layer (cart.ml 54-105).

    `finite_image` is an indexing type of a prescribed size.  Its creation
    (cart.ml 54-55) is the first `new_type_definition` of the development: a
    kernel side effect threaded in from Session as a parameter, so this layer
    stays pure.  The existence proof `?x. x IN 1..dimindex(:A)` is built here
    with `prove`.  `finite_image_tybij` is the conjoined bijection theorem,
    used only through `MESON_TAC` in the downstream proofs. -/
structure CartFiniteImage where
  /-- `finite_image_tybij` (cart.ml 54): the abs/rep bijection for the new type
      `finite_image`, from `new_type_definition` applied to the proof of
      `?x. x IN 1..dimindex(:A)` (`EXISTS_TAC \`1\` THEN REWRITE_TAC[IN_NUMSEG;
      LE_REFL; DIMINDEX_GE_1]`). -/
  finite_image_tybij : thm
  /-- `FINITE_IMAGE_IMAGE` (cart.ml 60):
      `UNIV:(A)finite_image->bool = IMAGE finite_index (1..dimindex(:A))`.
      `REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE] THEN
      MESON_TAC[finite_image_tybij]`. -/
  FINITE_IMAGE_IMAGE : thm
  /-- `HAS_SIZE_FINITE_IMAGE` (cart.ml 69):
      `!s. (UNIV:(A)finite_image->bool) HAS_SIZE dimindex(s:A->bool)`.
      `GEN_TAC THEN SIMP_TAC[FINITE_IMAGE_IMAGE] THEN MATCH_MP_TAC
      HAS_SIZE_IMAGE_INJ THEN ONCE_REWRITE_TAC[DIMINDEX_UNIV] THEN
      REWRITE_TAC[HAS_SIZE_NUMSEG_1] THEN MESON_TAC[finite_image_tybij]`. -/
  HAS_SIZE_FINITE_IMAGE : thm
  /-- `CARD_FINITE_IMAGE` (cart.ml 76):
      `!s. CARD(UNIV:(A)finite_image->bool) = dimindex(s:A->bool)`.
      `MESON_TAC[HAS_SIZE_FINITE_IMAGE; HAS_SIZE]`. -/
  CARD_FINITE_IMAGE : thm
  /-- `FINITE_FINITE_IMAGE` (cart.ml 80): `FINITE(UNIV:(A)finite_image->bool)`.
      `MESON_TAC[HAS_SIZE_FINITE_IMAGE; HAS_SIZE]`. -/
  FINITE_FINITE_IMAGE : thm
  /-- `DIMINDEX_FINITE_IMAGE` (cart.ml 84):
      `!s t. dimindex(s:(A)finite_image->bool) = dimindex(t:A->bool)`.
      `REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [dimindex] THEN
      MP_TAC(ISPEC \`t:A->bool\` HAS_SIZE_FINITE_IMAGE) THEN
      SIMP_TAC[FINITE_FINITE_IMAGE; HAS_SIZE]`. -/
  DIMINDEX_FINITE_IMAGE : thm
  /-- `FINITE_INDEX_WORKS` (cart.ml 90): `!i:(A)finite_image. ?!n. 1 <= n /\
      n <= dimindex(:A) /\ (finite_index n = i)`.  `REWRITE_TAC[CONJ_ASSOC;
      GSYM IN_NUMSEG] THEN MESON_TAC[finite_image_tybij]`. -/
  FINITE_INDEX_WORKS : thm
  /-- `FINITE_INDEX_INJ` (cart.ml 95): `!i j. 1 <= i /\ i <= dimindex(:A) /\
      1 <= j /\ j <= dimindex(:A) ==> ((finite_index i :A finite_image =
      finite_index j) <=> (i = j))`.  `MESON_TAC[FINITE_INDEX_WORKS]`. -/
  FINITE_INDEX_INJ : thm
  /-- `FORALL_FINITE_INDEX` (cart.ml 102): `(!k:(N)finite_image. P k) =
      (!i. 1 <= i /\ i <= dimindex(:N) ==> P(finite_index i))`.
      `MESON_TAC[FINITE_INDEX_WORKS]`. -/
  FORALL_FINITE_INDEX : thm
  deriving Inhabited

/-- cart.ml 50-106: an indexing type with that size, parametrized by base
    type, and its dimension and indexing. -/
@[nospecialize]
def setupCartFiniteImage [HolBase]
    (new_type_definition' : String → String → String → thm → IO (Except String thm))
    (MESON_TAC : List thm → tactic)
    (CDim : CartDimindex)
    (IN_NUMSEG LE_REFL EXTENSION IN_UNIV IN_IMAGE HAS_SIZE HAS_SIZE_IMAGE_INJ
     HAS_SIZE_NUMSEG_1 CONJ_ASSOC : thm) :
    ExceptT String IO CartFiniteImage := do
  let new_type_definition (ty : String) (names : String × String) (th : thm) :
      ExceptT String IO thm :=
    new_type_definition' ty names.1 names.2 th
  let { dimindex, DIMINDEX_GE_1, DIMINDEX_UNIV, .. } := CDim

  /- An indexing type with that size, parametrized by base type. -/

  let finite_image_tybij ←
    new_type_definition "finite_image" ("finite_index", "dest_finite_image")
    (← prove
     r"?x. x IN 1..dimindex(:A)"
     (EXISTS_TAC (← q r"1") THEN REWRITE_TAC [IN_NUMSEG, LE_REFL, DIMINDEX_GE_1]))

  let FINITE_IMAGE_IMAGE ← prove
   r"UNIV:(A)finite_image->bool = IMAGE finite_index (1..dimindex(:A))"
   (REWRITE_TAC [EXTENSION, IN_UNIV, IN_IMAGE] THEN
    MESON_TAC [finite_image_tybij])

  /- Dimension of such a type, and indexing over it. -/

  let HAS_SIZE_FINITE_IMAGE ← prove
   r"!s. (UNIV:(A)finite_image->bool) HAS_SIZE dimindex(s:A->bool)"
   (GEN_TAC THEN SIMP_TAC [FINITE_IMAGE_IMAGE] THEN
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    ONCE_REWRITE_TAC [DIMINDEX_UNIV] THEN REWRITE_TAC [HAS_SIZE_NUMSEG_1] THEN
    MESON_TAC [finite_image_tybij])

  let CARD_FINITE_IMAGE ← prove
   r"!s. CARD(UNIV:(A)finite_image->bool) = dimindex(s:A->bool)"
   (MESON_TAC [HAS_SIZE_FINITE_IMAGE, HAS_SIZE])

  let FINITE_FINITE_IMAGE ← prove
   r"FINITE(UNIV:(A)finite_image->bool)"
   (MESON_TAC [HAS_SIZE_FINITE_IMAGE, HAS_SIZE])

  let DIMINDEX_FINITE_IMAGE ← prove
   r"!s t. dimindex(s:(A)finite_image->bool) = dimindex(t:A->bool)"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [dimindex] THEN
    MP_TAC (← ISPEC (← q r"t:A->bool") HAS_SIZE_FINITE_IMAGE) THEN
    SIMP_TAC [FINITE_FINITE_IMAGE, HAS_SIZE])

  let FINITE_INDEX_WORKS ← prove
   r"!i:(A)finite_image.
        ?!n. 1 <= n /\ n <= dimindex(:A) /\ (finite_index n = i)"
   (REWRITE_TAC [CONJ_ASSOC, ← GSYM IN_NUMSEG] THEN MESON_TAC [finite_image_tybij])

  let FINITE_INDEX_INJ ← prove
   r"!i j. 1 <= i /\ i <= dimindex(:A) /\
         1 <= j /\ j <= dimindex(:A)
         ==> ((finite_index i :A finite_image = finite_index j) <=>
              (i = j))"
   (MESON_TAC [FINITE_INDEX_WORKS])

  let FORALL_FINITE_INDEX ← prove
   r"(!k:(N)finite_image. P k) =
   (!i. 1 <= i /\ i <= dimindex(:N) ==> P(finite_index i))"
   (MESON_TAC [FINITE_INDEX_WORKS])

  return {
    finite_image_tybij, FINITE_IMAGE_IMAGE, HAS_SIZE_FINITE_IMAGE,
    CARD_FINITE_IMAGE, FINITE_FINITE_IMAGE, DIMINDEX_FINITE_IMAGE,
    FINITE_INDEX_WORKS, FINITE_INDEX_INJ, FORALL_FINITE_INDEX }

end

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms DSLThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax



/-- Install the `$` vector-indexing infix (cart.ml 115):
    `parse_as_infix("$",(25,"left"))`.  Must run once, before any term using
    `$` is parsed (the `finite_index` body is the first such term). -/
def setupCartDollarInfix : IO Unit := do
  -- cart.ml 115.
  HolCore.Printer.parse_as_infix ("$", (25, "left"))

/-- Install the `lambda` binder (cart.ml 126): `parse_as_binder "lambda"` (a
    binder, not an infix).  Must run once, before any `lambda i. ...` term is
    parsed (the `lambda` body is the first such term). -/
def setupCartLambdaBinder : IO Unit := do
  -- cart.ml 126.
  HolCore.Printer.parse_as_binder "lambda"


end

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms DSLThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax

/-- The Cartesian-product type `cart` with its indexing (`$`) and abstraction
    (`lambda`), cart.ml 111-168.

    `cart_tybij` (cart.ml 111-112) creates the type operator `cart` that the
    hard-wired `^` type infix maps to, so `:A^B` starts parsing and printing
    once this is forced.  `new_type_definition` is threaded in from Session
    (kernel side effect); the trivial existence proof `?f:(B)finite_image->A. T`
    is built here with `prove`.  The two `new_definition`s `finite_index` (117)
    and `lambda` (128) use the `$` infix and `lambda` binder, so Session
    installs those before forcing this bundle.

    Depends on `CartFiniteImage` (`FORALL_FINITE_INDEX`, `FINITE_INDEX_WORKS`,
    `FINITE_INDEX_INJ`, `DIMINDEX_FINITE_IMAGE`) and on `dimindex`. -/
structure CartCart where
  /-- `cart_tybij` (cart.ml 111): the abs/rep bijection for the new Cartesian
      product type `cart`, from `new_type_definition "cart" ("mk_cart",
      "dest_cart")` applied to the trivial existence proof `?f:(B)finite_image
      ->A. T` (`REWRITE_TAC[]`).  Creating this operator activates the
      parser/printer `^` type infix. -/
  cart_tybij : thm
  /-- `finite_index` (cart.ml 117): `(x:A^N)$i = dest_cart x (finite_index i)`.
      `new_definition`; its body is the FIRST term to use the `$` infix. -/
  finite_index : thm
  /-- `CART_EQ` (cart.ml 120): `!x:A^B y. (x = y) <=> !i. 1 <= i /\ i <=
      dimindex(:B) ==> (x$i = y$i)`.  `REPEAT GEN_TAC THEN REWRITE_TAC
      [finite_index; GSYM FORALL_FINITE_INDEX] THEN REWRITE_TAC[GSYM
      FUN_EQ_THM; ETA_AX] THEN MESON_TAC[cart_tybij]`. -/
  CART_EQ : thm
  /-- `lambda` (cart.ml 128): `(lambda) g = @f:A^B. !i. 1 <= i /\ i <=
      dimindex(:B) ==> (f$i = g i)`.  `new_definition`; parsed AFTER the
      `lambda` binder is installed. -/
  lambda : thm
  /-- `LAMBDA_BETA` (cart.ml 132): `!i. 1 <= i /\ i <= dimindex(:B) ==>
      (((lambda) g:A^B) $i = g i)`.  `REWRITE_TAC[lambda] THEN CONV_TAC
      SELECT_CONV THEN EXISTS_TAC \`mk_cart(\k. g(@i. ...)):A^B\` THEN
      REWRITE_TAC[finite_index; REWRITE_RULE[] cart_tybij] THEN REPEAT
      STRIP_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN GEN_TAC
      THEN REWRITE_TAC[] THEN ASM_MESON_TAC[FINITE_INDEX_INJ;
      DIMINDEX_FINITE_IMAGE]`. -/
  LAMBDA_BETA : thm
  /-- `LAMBDA_UNIQUE` (cart.ml 143): `!f:A^B g. (!i. 1 <= i /\ i <=
      dimindex(:B) ==> (f$i = g i)) <=> ((lambda) g = f)`.  `SIMP_TAC[CART_EQ;
      LAMBDA_BETA] THEN MESON_TAC[]`. -/
  LAMBDA_UNIQUE : thm
  /-- `LAMBDA_ETA` (cart.ml 149): `!g. (lambda i. g$i):A^B = g`.
      `REWRITE_TAC[CART_EQ; LAMBDA_BETA]`. -/
  LAMBDA_ETA : thm
  /- ---------------------------------------------------------------------- -/
  /- For some purposes we can avoid side-conditions on the index.            -/
  /- ---------------------------------------------------------------------- -/
  /-- `FINITE_INDEX_INRANGE` (cart.ml 157): `!i. ?k. 1 <= k /\ k <=
      dimindex(:N) /\ !x:A^N. x$i = x$k`.  `REWRITE_TAC[finite_index] THEN
      MESON_TAC[FINITE_INDEX_WORKS]`. -/
  FINITE_INDEX_INRANGE : thm
  /-- `FINITE_INDEX_INRANGE_2` (cart.ml 161): `!i. ?k. 1 <= k /\ k <=
      dimindex(:N) /\ (!x:A^N. x$i = x$k) /\ (!y:B^N. y$i = y$k)`.
      `REWRITE_TAC[finite_index] THEN MESON_TAC[FINITE_INDEX_WORKS]`. -/
  FINITE_INDEX_INRANGE_2 : thm
  /-- `CART_EQ_FULL` (cart.ml 166): `!x y:A^N. x = y <=> !i. x$i = y$i`.
      `REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN SIMP_TAC[CART_EQ]`. -/
  CART_EQ_FULL : thm
  deriving Inhabited

/-- cart.ml 108-160: finite Cartesian products, with indexing and lambdas.
    The `$` infix and the `lambda` binder are set up by Session before this
    runs. -/
@[nospecialize]
def setupCartCart [HolBase]
    (new_type_definition' : String → String → String → thm → IO (Except String thm))
    (new_definition' : term → IO (Except String thm))
    (MESON_TAC ASM_MESON_TAC : List thm → tactic)
    (SELECT_CONV' : term → Except String thm)
    (CFImg : CartFiniteImage)
    (FUN_EQ_THM ETA_AX SELECT_UNIQUE : thm) :
    ExceptT String IO CartCart := do
  let new_type_definition (ty : String) (names : String × String) (th : thm) :
      ExceptT String IO thm :=
    new_type_definition' ty names.1 names.2 th
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let SELECT_CONV : ioconv := fun t => pure (SELECT_CONV' t)
  let { DIMINDEX_FINITE_IMAGE, FINITE_INDEX_WORKS, FINITE_INDEX_INJ,
        FORALL_FINITE_INDEX, .. } := CFImg

  /- Hence finite Cartesian products, with indexing and lambdas. -/

  let cart_tybij ←
    new_type_definition "cart" ("mk_cart", "dest_cart")
     (← prove r"?f:(B)finite_image->A. T" (REWRITE_TAC []))

  let finite_index ← new_definition
   r"(x:A^N)$i = dest_cart x (finite_index i)"

  let CART_EQ ← prove
   r"!x:A^B y.
    (x = y) <=> !i. 1 <= i /\ i <= dimindex(:B) ==> (x$i = y$i)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [finite_index, ← GSYM FORALL_FINITE_INDEX] THEN
    REWRITE_TAC [← GSYM FUN_EQ_THM, ETA_AX] THEN MESON_TAC [cart_tybij])

  let lambda ← new_definition
   r"(lambda) g =
     @f:A^B. !i. 1 <= i /\ i <= dimindex(:B) ==> (f$i = g i)"

  let LAMBDA_BETA ← prove
   r"!i. 1 <= i /\ i <= dimindex(:B)
       ==> (((lambda) g:A^B) $i = g i)"
   (REWRITE_TAC [lambda] THEN CONV_TAC SELECT_CONV THEN
    EXISTS_TAC (← q r"mk_cart(\k. g(@i. 1 <= i /\  i <= dimindex(:B) /\
                                (finite_index i = k))):A^B") THEN
    REWRITE_TAC [finite_index, ← REWRITE_RULE [] cart_tybij] THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    GEN_TAC THEN REWRITE_TAC [] THEN
    ASM_MESON_TAC [FINITE_INDEX_INJ, DIMINDEX_FINITE_IMAGE])

  let LAMBDA_UNIQUE ← prove
   r"!f:A^B g.
        (!i. 1 <= i /\ i <= dimindex(:B) ==> (f$i = g i)) <=>
        ((lambda) g = f)"
   (SIMP_TAC [CART_EQ, LAMBDA_BETA] THEN MESON_TAC [])

  let LAMBDA_ETA ← prove
   r"!g. (lambda i. g$i):A^B = g"
   (REWRITE_TAC [CART_EQ, LAMBDA_BETA])

  /- For some purposes we can avoid side-conditions on the index. -/

  let FINITE_INDEX_INRANGE ← prove
   r"!i. ?k. 1 <= k /\ k <= dimindex(:N) /\ !x:A^N. x$i = x$k"
   (REWRITE_TAC [finite_index] THEN MESON_TAC [FINITE_INDEX_WORKS])

  let FINITE_INDEX_INRANGE_2 ← prove
   r"!i. ?k. 1 <= k /\ k <= dimindex(:N) /\
           (!x:A^N. x$i = x$k) /\ (!y:B^N. y$i = y$k)"
   (REWRITE_TAC [finite_index] THEN MESON_TAC [FINITE_INDEX_WORKS])

  let CART_EQ_FULL ← prove
   r"!x y:A^N. x = y <=> !i. x$i = y$i"
   (REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC [] THEN SIMP_TAC [CART_EQ])

  return {
    cart_tybij, finite_index, CART_EQ, lambda, LAMBDA_BETA, LAMBDA_UNIQUE,
    LAMBDA_ETA, FINITE_INDEX_INRANGE, FINITE_INDEX_INRANGE_2, CART_EQ_FULL }

/-- The `finite_sum` type-bijection layer and the pasting operators
    `pastecart`/`fstcart`/`sndcart` with their theory (cart.ml 174-273).

    `finite_sum` is a non-standard sum for "pasting" products together.  Its
    `new_type_definition` (cart.ml 179) is applied to a locally proved
    nonemptiness theorem, so that proof is built here first, then handed to the
    Session-threaded `new_type_definition`.  `pastecart`/`fstcart`/`sndcart`
    (181/186/189) are three `new_definition`s whose bodies use the `$` infix
    and `lambda` binder from `CartCart`.

    Depends on `dimindex`/`DIMINDEX_GE_1`/`DIMINDEX_UNIV`, `CartCart`
    (`CART_EQ`, `LAMBDA_BETA`), threaded Sets/Iterate theorems and the
    arithmetic layer. -/
structure CartFiniteSum where
  /-- `finite_sum_tybij` (cart.ml 174): the abs/rep bijection for the new
      binary type `finite_sum`, from `new_type_definition "finite_sum"
      ("mk_finite_sum","dest_finite_sum")` applied to the LOCALLY PROVED
      `?x. x IN 1..(dimindex(:A) + dimindex(:B))` (`EXISTS_TAC \`1\` THEN
      SIMP_TAC[IN_NUMSEG; LE_REFL; DIMINDEX_GE_1; ARITH_RULE \`1 <= a ==>
      1 <= a + b\`]`). -/
  finite_sum_tybij : thm
  /-- `pastecart` (cart.ml 181): `(pastecart:A^M->A^N->A^(M,N)finite_sum) f g =
      lambda i. if i <= dimindex(:M) then f$i else g$(i - dimindex(:M))`.
      `new_definition`. -/
  pastecart : thm
  /-- `fstcart` (cart.ml 186): `(fstcart:A^(M,N)finite_sum->A^M) f =
      lambda i. f$i`.  `new_definition`. -/
  fstcart : thm
  /-- `sndcart` (cart.ml 189): `(sndcart:A^(M,N)finite_sum->A^N) f =
      lambda i. f$(i + dimindex(:M))`.  `new_definition`. -/
  sndcart : thm
  /-- `FINITE_SUM_IMAGE` (cart.ml 193): `UNIV:(A,B)finite_sum->bool =
      IMAGE mk_finite_sum (1..(dimindex(:A)+dimindex(:B)))`.
      `REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE] THEN
      MESON_TAC[finite_sum_tybij]`. -/
  FINITE_SUM_IMAGE : thm
  /-- `DIMINDEX_HAS_SIZE_FINITE_SUM` (cart.ml 199):
      `(UNIV:(M,N)finite_sum->bool) HAS_SIZE (dimindex(:M) + dimindex(:N))`.
      `SIMP_TAC[FINITE_SUM_IMAGE] THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
      ONCE_REWRITE_TAC[DIMINDEX_UNIV] THEN REWRITE_TAC[HAS_SIZE_NUMSEG_1] THEN
      MESON_TAC[finite_sum_tybij]`. -/
  DIMINDEX_HAS_SIZE_FINITE_SUM : thm
  /-- `DIMINDEX_FINITE_SUM` (cart.ml 206): `dimindex(:(M,N)finite_sum) =
      dimindex(:M) + dimindex(:N)`.  `GEN_REWRITE_TAC LAND_CONV [dimindex] THEN
      REWRITE_TAC[REWRITE_RULE[HAS_SIZE] DIMINDEX_HAS_SIZE_FINITE_SUM]`. -/
  DIMINDEX_FINITE_SUM : thm
  /-- `FSTCART_PASTECART` (cart.ml 211): `!x y. fstcart(pastecart (x:A^M)
      (y:A^N)) = x`.  `SIMP_TAC[pastecart; fstcart; CART_EQ; LAMBDA_BETA;
      DIMINDEX_FINITE_SUM; ARITH_RULE \`a <= b ==> a <= b + c\`]`. -/
  FSTCART_PASTECART : thm
  /-- `SNDCART_PASTECART` (cart.ml 216): `!x y. sndcart(pastecart (x:A^M)
      (y:A^N)) = y`.  `SIMP_TAC[pastecart; sndcart; CART_EQ; LAMBDA_BETA] THEN
      REPEAT STRIP_TAC THEN W(fun (_,w) -> MP_TAC (PART_MATCH (lhs o rand)
      LAMBDA_BETA (lhand w))) THEN ANTS_TAC THENL [b1; b2]` (width 2). -/
  SNDCART_PASTECART : thm
  /-- `PASTECART_FST_SND` (cart.ml 227): `!z. pastecart (fstcart z) (sndcart
      z):A^(M,N)finite_sum = z`.  `SIMP_TAC[pastecart; fstcart; sndcart;
      CART_EQ; LAMBDA_BETA] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[DIMINDEX_FINITE_SUM; LAMBDA_BETA;
      three ARITH_RULEs]`. -/
  PASTECART_FST_SND : thm
  /-- `PASTECART_EQ` (cart.ml 236): `!x y:A^(M,N)finite_sum. x = y <=>
      fstcart x = fstcart y /\ sndcart x = sndcart y`.
      `MESON_TAC[PASTECART_FST_SND]`. -/
  PASTECART_EQ : thm
  /-- `FORALL_PASTECART` (cart.ml 241): `(!p:A^(M,N)finite_sum. P p) <=>
      !x y. P (pastecart x y)`.  `MESON_TAC[PASTECART_FST_SND;
      FSTCART_PASTECART; SNDCART_PASTECART]`. -/
  FORALL_PASTECART : thm
  /-- `EXISTS_PASTECART` (cart.ml 245): `(?p:A^(M,N)finite_sum. P p) <=>
      ?x y. P (pastecart x y)`.  `MESON_TAC[PASTECART_FST_SND;
      FSTCART_PASTECART; SNDCART_PASTECART]`. -/
  EXISTS_PASTECART : thm
  /-- `PASTECART_INJ` (cart.ml 249): `!x:A^M y:A^N w z. pastecart x y =
      pastecart w z <=> x = w /\ y = z`.  `REWRITE_TAC[PASTECART_EQ;
      FSTCART_PASTECART; SNDCART_PASTECART]`. -/
  PASTECART_INJ : thm
  /-- `FSTCART_COMPONENT` (cart.ml 253): `!x:A^(M,N)finite_sum i. 1 <= i /\
      i <= dimindex(:M) ==> fstcart x$i = x$i`.
      `SIMP_TAC[fstcart; LAMBDA_BETA]`. -/
  FSTCART_COMPONENT : thm
  /-- `SNDCART_COMPONENT` (cart.ml 258): `!x:A^(M,N)finite_sum i. 1 <= i /\
      i <= dimindex(:N) ==> sndcart x$i = x$(i + dimindex(:M))`.
      `SIMP_TAC[sndcart; LAMBDA_BETA]`. -/
  SNDCART_COMPONENT : thm
  /-- `PASTECART_COMPONENT` (cart.ml 263): the conjoined component clauses.
      `REWRITE_TAC[pastecart] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC
      THENL [b1; b2]` (width 2); `b1` uses `SUBGOAL_THEN ... (fun th ->
      ASM_SIMP_TAC[LAMBDA_BETA; th])`. -/
  PASTECART_COMPONENT : thm
  deriving Inhabited

/-- cart.ml 162-273: a non-standard sum to "paste" together Cartesian
    products. -/
@[nospecialize]
def setupCartFiniteSum [HolBase]
    (new_type_definition' : String → String → String → thm → IO (Except String thm))
    (new_definition' : term → IO (Except String thm))
    (MESON_TAC : List thm → tactic)
    (ARITH_RULE' : term → IO (Except String thm))
    (ASM_ARITH_TAC : tactic)
    (CDim : CartDimindex) (CCart : CartCart)
    (IN_NUMSEG LE_REFL EXTENSION IN_UNIV IN_IMAGE HAS_SIZE HAS_SIZE_IMAGE_INJ
     HAS_SIZE_NUMSEG_1 ADD_SUB : thm) :
    ExceptT String IO CartFiniteSum := do
  let new_type_definition (ty : String) (names : String × String) (th : thm) :
      ExceptT String IO thm :=
    new_type_definition' ty names.1 names.2 th
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let ARITH_RULE (t : term) : ExceptT String IO thm := ARITH_RULE' t
  let { dimindex, DIMINDEX_GE_1, DIMINDEX_UNIV, .. } := CDim
  let { CART_EQ, LAMBDA_BETA, .. } := CCart

  /- We need a non-standard sum to "paste" together Cartesian products. -/

  let finite_sum_tybij ← do
    let th ← prove
     r"?x. x IN 1..(dimindex(:A) + dimindex(:B))"
     (EXISTS_TAC (← q r"1") THEN SIMP_TAC [IN_NUMSEG, LE_REFL, DIMINDEX_GE_1,
        ← ARITH_RULE (← q r"1 <= a ==> 1 <= a + b")])
    new_type_definition "finite_sum" ("mk_finite_sum", "dest_finite_sum") th

  let pastecart ← new_definition
   r"(pastecart:A^M->A^N->A^(M,N)finite_sum) f g =
        lambda i. if i <= dimindex(:M) then f$i
                  else g$(i - dimindex(:M))"

  let fstcart ← new_definition
   r"(fstcart:A^(M,N)finite_sum->A^M) f = lambda i. f$i"

  let sndcart ← new_definition
   r"(sndcart:A^(M,N)finite_sum->A^N) f =
        lambda i. f$(i + dimindex(:M))"

  let FINITE_SUM_IMAGE ← prove
   r"UNIV:(A,B)finite_sum->bool =
       IMAGE mk_finite_sum (1..(dimindex(:A)+dimindex(:B)))"
   (REWRITE_TAC [EXTENSION, IN_UNIV, IN_IMAGE] THEN
    MESON_TAC [finite_sum_tybij])

  let DIMINDEX_HAS_SIZE_FINITE_SUM ← prove
   r"(UNIV:(M,N)finite_sum->bool) HAS_SIZE (dimindex(:M) + dimindex(:N))"
   (SIMP_TAC [FINITE_SUM_IMAGE] THEN
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    ONCE_REWRITE_TAC [DIMINDEX_UNIV] THEN REWRITE_TAC [HAS_SIZE_NUMSEG_1] THEN
    MESON_TAC [finite_sum_tybij])

  let DIMINDEX_FINITE_SUM ← prove
   r"dimindex(:(M,N)finite_sum) = dimindex(:M) + dimindex(:N)"
   (GEN_REWRITE_TAC LAND_CONV [dimindex] THEN
    REWRITE_TAC [← REWRITE_RULE [HAS_SIZE] DIMINDEX_HAS_SIZE_FINITE_SUM])

  let FSTCART_PASTECART ← prove
   r"!x y. fstcart(pastecart (x:A^M) (y:A^N)) = x"
   (SIMP_TAC [pastecart, fstcart, CART_EQ, LAMBDA_BETA, DIMINDEX_FINITE_SUM,
              ← ARITH_RULE (← q r"a <= b ==> a <= b + c")])

  let SNDCART_PASTECART ← prove
   r"!x y. sndcart(pastecart (x:A^M) (y:A^N)) = y"
   (SIMP_TAC [pastecart, sndcart, CART_EQ, LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN
    W (fun g => tactic_of do
      pure (MP_TAC (← PART_MATCH (fun t => do lhs (← rand t)) LAMBDA_BETA
        (← lhand (snd g))))) THEN
    ANTS_TAC THENL
     [REWRITE_TAC [DIMINDEX_FINITE_SUM] THEN MATCH_MP_TAC
       (← ARITH_RULE (← q r"1 <= i /\ i <= b ==> 1 <= i + a /\ i + a <= a + b")) THEN
      ASM_REWRITE_TAC [],
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [] THEN
      ASM_SIMP_TAC [ADD_SUB, ← ARITH_RULE (← q r"1 <= i ==> ~(i + a <= a)")]])

  let PASTECART_FST_SND ← prove
   r"!z. pastecart (fstcart z) (sndcart z):A^(M,N)finite_sum = z"
   (SIMP_TAC [pastecart, fstcart, sndcart, CART_EQ, LAMBDA_BETA] THEN
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_SIMP_TAC [DIMINDEX_FINITE_SUM, LAMBDA_BETA,
       ← ARITH_RULE (← q r"i <= a + b ==> i - a <= b"),
       ← ARITH_RULE (← q r"~(i <= a) ==> 1 <= i - a"),
       ← ARITH_RULE (← q r"~(i <= a) ==> ((i - a) + a = i)")])

  let PASTECART_EQ ← prove
   r"!x y:A^(M,N)finite_sum.
        x = y <=> fstcart x = fstcart y /\ sndcart x = sndcart y"
   (MESON_TAC [PASTECART_FST_SND])

  let FORALL_PASTECART ← prove
   r"(!p:A^(M,N)finite_sum. P p) <=> !x y. P (pastecart x y)"
   (MESON_TAC [PASTECART_FST_SND, FSTCART_PASTECART, SNDCART_PASTECART])

  let EXISTS_PASTECART ← prove
   r"(?p:A^(M,N)finite_sum. P p) <=> ?x y. P (pastecart x y)"
   (MESON_TAC [PASTECART_FST_SND, FSTCART_PASTECART, SNDCART_PASTECART])

  let PASTECART_INJ ← prove
   r"!x:A^M y:A^N w z. pastecart x y = pastecart w z <=> x = w /\ y = z"
   (REWRITE_TAC [PASTECART_EQ, FSTCART_PASTECART, SNDCART_PASTECART])

  let FSTCART_COMPONENT ← prove
   r"!x:A^(M,N)finite_sum i. 1 <= i /\ i <= dimindex(:M)
                           ==> fstcart x$i = x$i"
   (SIMP_TAC [fstcart, LAMBDA_BETA])

  let SNDCART_COMPONENT ← prove
   r"!x:A^(M,N)finite_sum i. 1 <= i /\ i <= dimindex(:N)
                           ==> sndcart x$i = x$(i + dimindex(:M))"
   (SIMP_TAC [sndcart, LAMBDA_BETA])

  let PASTECART_COMPONENT ← prove
   r"(!u:A^M v:A^N i. 1 <= i /\ i <= dimindex(:M) ==> pastecart u v$i = u$i) /\
   (!u:A^M v:A^N i. dimindex(:M) + 1 <= i /\ i <= dimindex(:M) + dimindex(:N)
                    ==> pastecart u v$i = v$(i - dimindex(:M)))"
   (REWRITE_TAC [pastecart] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
     [SUBGOAL_THEN (← q r"i <= dimindex(:(M,N)finite_sum)")
        (fun th => ASM_SIMP_TAC [LAMBDA_BETA, th]) THEN
      REWRITE_TAC [DIMINDEX_FINITE_SUM] THEN ASM_ARITH_TAC,
      ASM_SIMP_TAC [LAMBDA_BETA, DIMINDEX_FINITE_SUM,
                    ← ARITH_RULE (← q r"dimindex(:M) + 1 <= i ==> 1 <= i")] THEN
      COND_CASES_TAC THEN REWRITE_TAC [] THEN ASM_ARITH_TAC])

  return {
    finite_sum_tybij, pastecart, fstcart, sndcart, FINITE_SUM_IMAGE,
    DIMINDEX_HAS_SIZE_FINITE_SUM, DIMINDEX_FINITE_SUM, FSTCART_PASTECART,
    SNDCART_PASTECART, PASTECART_FST_SND, PASTECART_EQ, FORALL_PASTECART,
    EXISTS_PASTECART, PASTECART_INJ, FSTCART_COMPONENT, SNDCART_COMPONENT,
    PASTECART_COMPONENT }

/-- The `finite_diff` type-bijection layer (cart.ml 279-305).

    `finite_diff` is a "subtraction" function on type indices.  Its
    `new_type_definition` (cart.ml 284) is applied to a locally proved
    nonemptiness theorem, built here first.  Its proof closes with `ARITH_TAC`
    and rewrites `[IN_NUMSEG]` only (unlike the near-identical `finite_prod`
    goal below, which closes with `MESON_TAC` and rewrites `[IN_NUMSEG;
    LE_REFL]`).  `new_type_definition` is threaded in from Session. -/
structure CartFiniteDiff where
  /-- `finite_diff_tybij` (cart.ml 279): the abs/rep bijection for the new
      binary type `finite_diff`, from `new_type_definition "finite_diff"
      ("mk_finite_diff","dest_finite_diff")` applied to the LOCALLY PROVED
      `?x. x IN 1..(if dimindex(:B) < dimindex(:A) then dimindex(:A) -
      dimindex(:B) else 1)` (`EXISTS_TAC \`1\` THEN REWRITE_TAC[IN_NUMSEG] THEN
      ARITH_TAC`). -/
  finite_diff_tybij : thm
  /-- `FINITE_DIFF_IMAGE` (cart.ml 286): `UNIV:(A,B)finite_diff->bool =
      IMAGE mk_finite_diff (1..(if dimindex(:B) < dimindex(:A) then
      dimindex(:A) - dimindex(:B) else 1))`.  `REWRITE_TAC[EXTENSION; IN_UNIV;
      IN_IMAGE] THEN MESON_TAC[finite_diff_tybij]`. -/
  FINITE_DIFF_IMAGE : thm
  /-- `DIMINDEX_HAS_SIZE_FINITE_DIFF` (cart.ml 294):
      `(UNIV:(M,N)finite_diff->bool) HAS_SIZE (if dimindex(:N) < dimindex(:M)
      then dimindex(:M) - dimindex(:N) else 1)`.  `SIMP_TAC[FINITE_DIFF_IMAGE]
      THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ONCE_REWRITE_TAC[DIMINDEX_UNIV]
      THEN REWRITE_TAC[HAS_SIZE_NUMSEG_1] THEN MESON_TAC[finite_diff_tybij]`. -/
  DIMINDEX_HAS_SIZE_FINITE_DIFF : thm
  /-- `DIMINDEX_FINITE_DIFF` (cart.ml 302): `dimindex(:(M,N)finite_diff) =
      if dimindex(:N) < dimindex(:M) then dimindex(:M) - dimindex(:N) else 1`.
      `GEN_REWRITE_TAC LAND_CONV [dimindex] THEN REWRITE_TAC[REWRITE_RULE
      [HAS_SIZE] DIMINDEX_HAS_SIZE_FINITE_DIFF]`. -/
  DIMINDEX_FINITE_DIFF : thm
  deriving Inhabited

/-- cart.ml 275-305: likewise a "subtraction" function on type indices. -/
@[nospecialize]
def setupCartFiniteDiff [HolBase]
    (new_type_definition' : String → String → String → thm → IO (Except String thm))
    (MESON_TAC : List thm → tactic)
    (ARITH_TAC : tactic)
    (CDim : CartDimindex)
    (IN_NUMSEG EXTENSION IN_UNIV IN_IMAGE HAS_SIZE HAS_SIZE_IMAGE_INJ
     HAS_SIZE_NUMSEG_1 : thm) :
    ExceptT String IO CartFiniteDiff := do
  let new_type_definition (ty : String) (names : String × String) (th : thm) :
      ExceptT String IO thm :=
    new_type_definition' ty names.1 names.2 th
  let { dimindex, DIMINDEX_UNIV, .. } := CDim

  /- Likewise a "subtraction" function on type indices. -/

  let finite_diff_tybij ← do
    let th ← prove
     r"?x. x IN 1..(if dimindex(:B) < dimindex(:A)
                  then dimindex(:A) - dimindex(:B) else 1)"
     (EXISTS_TAC (← q r"1") THEN REWRITE_TAC [IN_NUMSEG] THEN ARITH_TAC)
    new_type_definition "finite_diff" ("mk_finite_diff", "dest_finite_diff") th

  let FINITE_DIFF_IMAGE ← prove
   r"UNIV:(A,B)finite_diff->bool =
       IMAGE mk_finite_diff
       (1..(if dimindex(:B) < dimindex(:A)
                  then dimindex(:A) - dimindex(:B) else 1))"
   (REWRITE_TAC [EXTENSION, IN_UNIV, IN_IMAGE] THEN
    MESON_TAC [finite_diff_tybij])

  let DIMINDEX_HAS_SIZE_FINITE_DIFF ← prove
   r"(UNIV:(M,N)finite_diff->bool) HAS_SIZE
   (if dimindex(:N) < dimindex(:M) then dimindex(:M) - dimindex(:N) else 1)"
   (SIMP_TAC [FINITE_DIFF_IMAGE] THEN
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    ONCE_REWRITE_TAC [DIMINDEX_UNIV] THEN REWRITE_TAC [HAS_SIZE_NUMSEG_1] THEN
    MESON_TAC [finite_diff_tybij])

  let DIMINDEX_FINITE_DIFF ← prove
   r"dimindex(:(M,N)finite_diff) =
     if dimindex(:N) < dimindex(:M) then dimindex(:M) - dimindex(:N) else 1"
   (GEN_REWRITE_TAC LAND_CONV [dimindex] THEN
    REWRITE_TAC [← REWRITE_RULE [HAS_SIZE] DIMINDEX_HAS_SIZE_FINITE_DIFF])

  return {
    finite_diff_tybij, FINITE_DIFF_IMAGE, DIMINDEX_HAS_SIZE_FINITE_DIFF,
    DIMINDEX_FINITE_DIFF }

/-- The `finite_prod` type-bijection layer (cart.ml 312-335).

    `finite_prod` is a finite-forcing "multiplication" on type indices.  Its
    `new_type_definition` (cart.ml 317) is applied to a locally proved
    nonemptiness theorem, built here first.  Its proof closes with
    `MESON_TAC[LE_1; DIMINDEX_GE_1; MULT_EQ_0]` and rewrites `[IN_NUMSEG;
    LE_REFL]` (unlike the near-identical `finite_diff` goal, which closes with
    `ARITH_TAC` and rewrites `[IN_NUMSEG]` only).  `new_type_definition` is
    threaded in from Session. -/
structure CartFiniteProd where
  /-- `finite_prod_tybij` (cart.ml 312): the abs/rep bijection for the new
      binary type `finite_prod`, from `new_type_definition "finite_prod"
      ("mk_finite_prod","dest_finite_prod")` applied to the LOCALLY PROVED
      `?x. x IN 1..(dimindex(:A) * dimindex(:B))` (`EXISTS_TAC \`1\` THEN
      REWRITE_TAC[IN_NUMSEG; LE_REFL] THEN MESON_TAC[LE_1; DIMINDEX_GE_1;
      MULT_EQ_0]`). -/
  finite_prod_tybij : thm
  /-- `FINITE_PROD_IMAGE` (cart.ml 319): `UNIV:(A,B)finite_prod->bool =
      IMAGE mk_finite_prod (1..(dimindex(:A)*dimindex(:B)))`.
      `REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE] THEN
      MESON_TAC[finite_prod_tybij]`. -/
  FINITE_PROD_IMAGE : thm
  /-- `DIMINDEX_HAS_SIZE_FINITE_PROD` (cart.ml 325):
      `(UNIV:(M,N)finite_prod->bool) HAS_SIZE (dimindex(:M) * dimindex(:N))`.
      `SIMP_TAC[FINITE_PROD_IMAGE] THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
      ONCE_REWRITE_TAC[DIMINDEX_UNIV] THEN REWRITE_TAC[HAS_SIZE_NUMSEG_1] THEN
      MESON_TAC[finite_prod_tybij]`. -/
  DIMINDEX_HAS_SIZE_FINITE_PROD : thm
  /-- `DIMINDEX_FINITE_PROD` (cart.ml 332): `dimindex(:(M,N)finite_prod) =
      dimindex(:M) * dimindex(:N)`.  `GEN_REWRITE_TAC LAND_CONV [dimindex] THEN
      REWRITE_TAC[REWRITE_RULE[HAS_SIZE] DIMINDEX_HAS_SIZE_FINITE_PROD]`. -/
  DIMINDEX_FINITE_PROD : thm
  deriving Inhabited

/-- cart.ml 307-334: and a finite-forcing "multiplication" on type indices. -/
@[nospecialize]
def setupCartFiniteProd [HolBase]
    (new_type_definition' : String → String → String → thm → IO (Except String thm))
    (MESON_TAC : List thm → tactic)
    (CDim : CartDimindex)
    (IN_NUMSEG LE_REFL EXTENSION IN_UNIV IN_IMAGE HAS_SIZE HAS_SIZE_IMAGE_INJ
     HAS_SIZE_NUMSEG_1 LE_1 MULT_EQ_0 : thm) :
    ExceptT String IO CartFiniteProd := do
  let new_type_definition (ty : String) (names : String × String) (th : thm) :
      ExceptT String IO thm :=
    new_type_definition' ty names.1 names.2 th
  let { dimindex, DIMINDEX_GE_1, DIMINDEX_UNIV, .. } := CDim

  /- And a finite-forcing "multiplication" on type indices. -/

  let finite_prod_tybij ← do
    let th ← prove
     r"?x. x IN 1..(dimindex(:A) * dimindex(:B))"
     (EXISTS_TAC (← q r"1") THEN REWRITE_TAC [IN_NUMSEG, LE_REFL] THEN
      MESON_TAC [LE_1, DIMINDEX_GE_1, MULT_EQ_0])
    new_type_definition "finite_prod" ("mk_finite_prod", "dest_finite_prod") th

  let FINITE_PROD_IMAGE ← prove
   r"UNIV:(A,B)finite_prod->bool =
       IMAGE mk_finite_prod (1..(dimindex(:A)*dimindex(:B)))"
   (REWRITE_TAC [EXTENSION, IN_UNIV, IN_IMAGE] THEN
    MESON_TAC [finite_prod_tybij])

  let DIMINDEX_HAS_SIZE_FINITE_PROD ← prove
   r"(UNIV:(M,N)finite_prod->bool) HAS_SIZE (dimindex(:M) * dimindex(:N))"
   (SIMP_TAC [FINITE_PROD_IMAGE] THEN
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    ONCE_REWRITE_TAC [DIMINDEX_UNIV] THEN REWRITE_TAC [HAS_SIZE_NUMSEG_1] THEN
    MESON_TAC [finite_prod_tybij])

  let DIMINDEX_FINITE_PROD ← prove
   r"dimindex(:(M,N)finite_prod) = dimindex(:M) * dimindex(:N)"
   (GEN_REWRITE_TAC LAND_CONV [dimindex] THEN
    REWRITE_TAC [← REWRITE_RULE [HAS_SIZE] DIMINDEX_HAS_SIZE_FINITE_PROD])

  return {
    finite_prod_tybij, FINITE_PROD_IMAGE, DIMINDEX_HAS_SIZE_FINITE_PROD,
    DIMINDEX_FINITE_PROD }

structure CartTybit where
  /-- `tybit0_INDUCT` (cart.ml 341): the induction theorem for `tybit0`, the
      one-constructor inductive type `tybit0 = mktybit0((A,A)finite_sum)`.
      Produced by the FIRST of the two `define_type` calls (threaded from
      Session, which owns the kernel side effect). -/
  tybit0_INDUCT : thm
  /-- `tybit0_RECURSION` (cart.ml 341): the recursion theorem for `tybit0`,
      the second element of the FIRST `define_type` pair. -/
  tybit0_RECURSION : thm
  /-- `tybit1_INDUCT` (cart.ml 344): the induction theorem for `tybit1`, the
      one-constructor inductive type
      `tybit1 = mktybit1(((A,A)finite_sum,1)finite_sum)`.  Produced by the
      SECOND `define_type` call, which MUST run after `tybit0` and after `:1`
      exists (its body mentions the type `1`). -/
  tybit1_INDUCT : thm
  /-- `tybit1_RECURSION` (cart.ml 344): the recursion theorem for `tybit1`,
      the second element of the SECOND `define_type` pair. -/
  tybit1_RECURSION : thm
  /-- `HAS_SIZE_TYBIT0` (cart.ml 347): `(:(A)tybit0) HAS_SIZE 2 * dimindex(:A)`.
      Proof rewrites the universe as `IMAGE mktybit0 (:(A,A)finite_sum)` (via
      `SURJECTIVE_IMAGE_EQ` and `cases "tybit0"`), then `HAS_SIZE_IMAGE_INJ`
      with `injectivity "tybit0"`, matching `DIMINDEX_HAS_SIZE_FINITE_SUM` and
      collapsing `dimindex(:A)+dimindex(:A)` to `2 * dimindex(:A)` via
      `GSYM MULT_2`. -/
  HAS_SIZE_TYBIT0 : thm
  /-- `HAS_SIZE_TYBIT1` (cart.ml 360):
      `(:(A)tybit1) HAS_SIZE 2 * dimindex(:A) + 1`.  Same shape as
      `HAS_SIZE_TYBIT0` but over `((A,A)finite_sum,1)finite_sum`; the extra
      `DIMINDEX_1` in the final rewrite turns the trailing `+ dimindex(:1)`
      into `+ 1`. -/
  HAS_SIZE_TYBIT1 : thm
  /-- `DIMINDEX_TYBIT0` (cart.ml 373): `dimindex(:(A)tybit0) = 2 * dimindex(:A)`.
      `MATCH_MP_TAC DIMINDEX_UNIQUE THEN MATCH_ACCEPT_TAC HAS_SIZE_TYBIT0`. -/
  DIMINDEX_TYBIT0 : thm
  /-- `DIMINDEX_TYBIT1` (cart.ml 377):
      `dimindex(:(A)tybit1) = 2 * dimindex(:A) + 1`.
      `MATCH_MP_TAC DIMINDEX_UNIQUE THEN MATCH_ACCEPT_TAC HAS_SIZE_TYBIT1`. -/
  DIMINDEX_TYBIT1 : thm
  /-- `DIMINDEX_CLAUSES` (cart.ml 381): the three-way conjunction
      `dimindex(:1) = 1 /\ dimindex(:(A)tybit0) = 2 * dimindex(:A) /\
       dimindex(:(A)tybit1) = 2 * dimindex(:A) + 1`. -/
  DIMINDEX_CLAUSES : thm
  /-- `FINITE_1` (cart.ml 389): `FINITE (:1)`.
      `MESON_TAC[HAS_SIZE_1; HAS_SIZE]`. -/
  FINITE_1 : thm
  /-- `FINITE_TYBIT0` (cart.ml 393): `FINITE (:A tybit0)`.
      `MESON_TAC[HAS_SIZE_TYBIT0; HAS_SIZE]`. -/
  FINITE_TYBIT0 : thm
  /-- `FINITE_TYBIT1` (cart.ml 397): `FINITE (:A tybit1)`.
      `MESON_TAC[HAS_SIZE_TYBIT1; HAS_SIZE]`. -/
  FINITE_TYBIT1 : thm
  /-- `FINITE_CLAUSES` (cart.ml 401):
      `FINITE(:1) /\ FINITE(:A tybit0) /\ FINITE(:A tybit1)`. -/
  FINITE_CLAUSES : thm
  deriving Inhabited

/-- cart.ml 336-410: type constructors for finite types indexed by binary
    numbers.  The two `define_type` calls run in Session; their theorems,
    and `cases`/`injectivity` for each, come in as parameters. -/
@[nospecialize]
def setupCartTybit [HolBase]
    (MESON_TAC : List thm → tactic)
    (tybit0_INDUCT tybit0_RECURSION tybit1_INDUCT tybit1_RECURSION : thm)
    (cases0 inj0 cases1 inj1 : thm)
    (DIMINDEX_UNIQUE HAS_SIZE_1 DIMINDEX_1 : thm)
    (DIMINDEX_HAS_SIZE_FINITE_SUM DIMINDEX_FINITE_SUM : thm)
    (SURJECTIVE_IMAGE_EQ HAS_SIZE_IMAGE_INJ IN_UNIV HAS_SIZE MULT_2 : thm) :
    ExceptT String IO CartTybit := do

  let HAS_SIZE_TYBIT0 ← prove
   r"(:(A)tybit0) HAS_SIZE 2 * dimindex(:A)"
   (SUBGOAL_THEN
     (← q r"(:(A)tybit0) = IMAGE mktybit0 (:(A,A)finite_sum)")
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
      REWRITE_TAC [IN_UNIV] THEN MESON_TAC [cases0],
      MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
      REWRITE_TAC [IN_UNIV, inj0] THEN
      W (fun g => tactic_of do
        pure (MP_TAC (← PART_MATCH lhand
          DIMINDEX_HAS_SIZE_FINITE_SUM (← lhand (snd g))))) THEN
      REWRITE_TAC [DIMINDEX_FINITE_SUM, ← GSYM MULT_2]])

  let HAS_SIZE_TYBIT1 ← prove
   r"(:(A)tybit1) HAS_SIZE 2 * dimindex(:A) + 1"
   (SUBGOAL_THEN
     (← q r"(:(A)tybit1) = IMAGE mktybit1 (:((A,A)finite_sum,1)finite_sum)")
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
      REWRITE_TAC [IN_UNIV] THEN MESON_TAC [cases1],
      MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
      REWRITE_TAC [IN_UNIV, inj1] THEN
      W (fun g => tactic_of do
        pure (MP_TAC (← PART_MATCH lhand
          DIMINDEX_HAS_SIZE_FINITE_SUM (← lhand (snd g))))) THEN
      REWRITE_TAC [DIMINDEX_FINITE_SUM, DIMINDEX_1, ← GSYM MULT_2]])

  let DIMINDEX_TYBIT0 ← prove
   r"dimindex(:(A)tybit0) = 2 * dimindex(:A)"
   (MATCH_MP_TAC DIMINDEX_UNIQUE THEN MATCH_ACCEPT_TAC HAS_SIZE_TYBIT0)

  let DIMINDEX_TYBIT1 ← prove
   r"dimindex(:(A)tybit1) = 2 * dimindex(:A) + 1"
   (MATCH_MP_TAC DIMINDEX_UNIQUE THEN MATCH_ACCEPT_TAC HAS_SIZE_TYBIT1)

  let DIMINDEX_CLAUSES ← prove
   r"dimindex(:1) = 1 /\
   dimindex(:(A)tybit0) = 2 * dimindex(:A) /\
   dimindex(:(A)tybit1) = 2 * dimindex(:A) + 1"
   (REWRITE_TAC [DIMINDEX_1] THEN CONJ_TAC THEN
    MATCH_MP_TAC DIMINDEX_UNIQUE THEN
    REWRITE_TAC [HAS_SIZE_TYBIT0, HAS_SIZE_TYBIT1])

  let FINITE_1 ← prove
   r"FINITE (:1)"
   (MESON_TAC [HAS_SIZE_1, HAS_SIZE])

  let FINITE_TYBIT0 ← prove
   r"FINITE (:A tybit0)"
   (MESON_TAC [HAS_SIZE_TYBIT0, HAS_SIZE])

  let FINITE_TYBIT1 ← prove
   r"FINITE (:A tybit1)"
   (MESON_TAC [HAS_SIZE_TYBIT1, HAS_SIZE])

  let FINITE_CLAUSES ← prove
   r"FINITE(:1) /\ FINITE(:A tybit0) /\ FINITE(:A tybit1)"
   (REWRITE_TAC [FINITE_1, FINITE_TYBIT0, FINITE_TYBIT1])

  return {
    tybit0_INDUCT, tybit0_RECURSION, tybit1_INDUCT, tybit1_RECURSION,
    HAS_SIZE_TYBIT0, HAS_SIZE_TYBIT1, DIMINDEX_TYBIT0, DIMINDEX_TYBIT1,
    DIMINDEX_CLAUSES, FINITE_1, FINITE_TYBIT0, FINITE_TYBIT1, FINITE_CLAUSES }

end

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms DSLThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax

/-- `DIMINDEX_CONV`, `HAS_SIZE_DIMINDEX_RULE`, `DIMINDEX_TAC` and the theorems
    proved with them (cart.ml 409-477). -/
structure CartDimindexConv where
  DIMINDEX_CONV : Equal.conv
  HAS_SIZE_DIMINDEX_RULE : hol_type → IO (Except String thm)
  DIMINDEX_TAC : tactic
  pth_num : thm
  pth0 : thm
  pth1 : thm
  pth_one : thm
  DIMINDEX_2 : thm
  DIMINDEX_3 : thm
  DIMINDEX_4 : thm
  HAS_SIZE_2 : thm
  HAS_SIZE_3 : thm
  HAS_SIZE_4 : thm
  deriving Inhabited

/-- The `calc_dimindex` of `DIMINDEX_CONV` (cart.ml 419-430). -/
partial def calc_dimindex (pth0 pth1 pth_one : thm) (nvar : term) :
    hol_type → Except String thm
  | .Tyapp "1" _ => .ok pth_one
  | .Tyapp "tybit0" (ty' :: _) => do
      let th ← calc_dimindex pth0 pth1 pth_one nvar ty'
      let n ← rand (concl th)
      Kernel.EQ_MP (← Kernel.INST [(n, nvar)] (← Kernel.INST_TYPE [(ty', aty)] pth0)) th
  | .Tyapp "tybit1" (ty' :: _) => do
      let th ← calc_dimindex pth0 pth1 pth_one nvar ty'
      let n ← rand (concl th)
      Kernel.EQ_MP (← Kernel.INST [(n, nvar)] (← Kernel.INST_TYPE [(ty', aty)] pth1)) th
  | _ => failwith ""  -- OCaml `fail()`

/-- The `function Comb(Const("dimindex",_),tm) -> ...` of `DIMINDEX_CONV`
    (cart.ml 431-440). -/
def DIMINDEX_CONV (pth_num pth0 pth1 pth_one : thm) (nvar : term) : Equal.conv := fun tm =>
  match tm with
  | .Comb (.Const "dimindex" _) t => do
      let uty := type_of t
      let sty ← match (← dest_type uty).2 with
        | s :: _ => .ok s
        | [] => failwith "DIMINDEX_CONV"
      let th ← calc_dimindex pth0 pth1 pth_one nvar sty
      let svar := mk_var "s" uty
      let ntm ← rand (concl th)
      let pth ← Kernel.INST [(t, svar), (ntm, nvar)] (← Kernel.INST_TYPE [(sty, aty)] pth_num)
      Kernel.EQ_MP pth th
  | _ => failwith "DIMINDEX_CONV"

/-- Build `CartDimindexConv` (cart.ml 409-477). -/
@[nospecialize]
def setupCartDimindexConv [HolBase] (ARITH_TAC : tactic) (MESON_TAC : List thm → tactic)
    (mk_numeral : Rat → Except String term) (BITS_ELIM_CONV : ioconv)
    (NUMERAL dimindex DIMINDEX_CLAUSES UNIV_HAS_SIZE_DIMINDEX HAS_SIZE FINITE_CLAUSES : thm) :
    ExceptT String IO CartDimindexConv := do
  let [pth_num, pth0, pth1, pth_one] := CONJUNCTS (← prove
   r"(dimindex(:A) = n <=> dimindex(s:A->bool) = NUMERAL n) /\
     (dimindex(:A) = n <=> dimindex(:A tybit0) = BIT0 n) /\
     (dimindex(:A) = n <=> dimindex(:A tybit1) = BIT1 n) /\
     dimindex(:1) = BIT1 _0"
   (CONJ_TAC THENL [REWRITE_TAC [NUMERAL, dimindex], ALL_TAC] THEN
    REWRITE_TAC [DIMINDEX_CLAUSES] THEN CONV_TAC BITS_ELIM_CONV THEN
    ARITH_TAC)) | throw "DIMINDEX_CONV"
  let nvar ← q r"n:num"
  let dimindexConv := DIMINDEX_CONV pth_num pth0 pth1 pth_one nvar
  let dimindexIO : ioconv := fun t => pure (dimindexConv t)
  -- HAS_SIZE_DIMINDEX_RULE (cart.ml 442-454).
  let pth ← prove
   r"(:A) HAS_SIZE n <=> FINITE(:A) /\ dimindex(:A) = n"
   (MESON_TAC [UNIV_HAS_SIZE_DIMINDEX, HAS_SIZE])
  let htm ← q r"(HAS_SIZE) (:A)"
  let conv ← GEN_REWRITE_CONV_NET id [pth]
  let finConv ← GEN_REWRITE_CONV_NET id [FINITE_CLAUSES]
  let rule (t : term) : ExceptT String IO thm := do EQT_ELIM (← ExceptT.mk (finConv t))
  let HAS_SIZE_DIMINDEX_RULE (nty : hol_type) : IO (Except String thm) := ExceptT.run do
    let tm ← liftExcept (do mk_comb (inst [(nty, aty)] htm) (← mk_numeral (← dest_finty nty)))
    let th1 ← ExceptT.mk (conv tm)
    let d ← liftExcept (do dimindexConv (← lhand (← rand (← rand (concl th1)))))
    EQ_MP (← SYM th1) (← CONJ (← rule (← liftExcept (do lhand (← rand (concl th1))))) d)
  let DIMINDEX_TAC := CONV_TAC (ONCE_DEPTH_CONV dimindexIO)
  let DIMINDEX_2 ← prove r"dimindex (:2) = 2" (DIMINDEX_TAC THEN REFL_TAC)
  let DIMINDEX_3 ← prove r"dimindex (:3) = 3" (DIMINDEX_TAC THEN REFL_TAC)
  let DIMINDEX_4 ← prove r"dimindex (:4) = 4" (DIMINDEX_TAC THEN REFL_TAC)
  let HAS_SIZE_2 ← ExceptT.mk (HAS_SIZE_DIMINDEX_RULE (← qty r"2"))
  let HAS_SIZE_3 ← ExceptT.mk (HAS_SIZE_DIMINDEX_RULE (← qty r"3"))
  let HAS_SIZE_4 ← ExceptT.mk (HAS_SIZE_DIMINDEX_RULE (← qty r"4"))
  return { DIMINDEX_CONV := dimindexConv, HAS_SIZE_DIMINDEX_RULE, DIMINDEX_TAC,
           pth_num, pth0, pth1, pth_one, DIMINDEX_2, DIMINDEX_3, DIMINDEX_4,
           HAS_SIZE_2, HAS_SIZE_3, HAS_SIZE_4 }

end

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms DSLThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax

/-- The finiteness lemma `FINITE_CART` (cart.ml 483-522) and the three whole-
    universe cardinality results (cart.ml 528-548).

    `FINITE_CART` is a coordinate-wise induction; `HAS_SIZE_CART_UNIV` reduces
    the universe to a funspace `(N)finite_image->A`, and `CARD_CART_UNIV`/
    `FINITE_CART_UNIV` are `MESON_TAC` corollaries of it.

    Depends on `CCart` (`CART_EQ`, `LAMBDA_BETA`, `cart_tybij`), `CFImg`
    (`HAS_SIZE_FINITE_IMAGE`), threaded Sets/Pair/arith theorems, and
    `MESON_TAC`/`ASM_MESON_TAC`/`ARITH_RULE`. -/
structure CartFinite where
  /-- `FINITE_CART` (cart.ml 483): `!P. (!i. 1 <= i /\ i <= dimindex(:N) ==>
      FINITE {x | P i x}) ==> FINITE {v:A^N | !i. 1 <= i /\ i <= dimindex(:N)
      ==> P i (v$i)}`.  Coordinate-wise induction. -/
  FINITE_CART : thm
  /- ---------------------------------------------------------------------- -/
  /- More cardinality results for whole universe.                           -/
  /- ---------------------------------------------------------------------- -/
  /-- `HAS_SIZE_CART_UNIV` (cart.ml 528): `!m. (:A) HAS_SIZE m ==> (:A^N)
      HAS_SIZE m EXP (dimindex(:N))`.  Via the funspace `(N)finite_image->A`,
      `HAS_SIZE_IMAGE_INJ` under `mk_cart`, and `SURJECTIVE_IMAGE_EQ`. -/
  HAS_SIZE_CART_UNIV : thm
  /-- `CARD_CART_UNIV` (cart.ml 542): `FINITE(:A) ==> CARD(:A^N) = CARD(:A)
      EXP dimindex(:N)`.  `MESON_TAC[HAS_SIZE_CART_UNIV; HAS_SIZE]`. -/
  CARD_CART_UNIV : thm
  /-- `FINITE_CART_UNIV` (cart.ml 546): `FINITE(:A) ==> FINITE(:A^N)`.
      `MESON_TAC[HAS_SIZE_CART_UNIV; HAS_SIZE]`. -/
  FINITE_CART_UNIV : thm
  deriving Inhabited

/-- cart.ml 465-552: the finiteness lemma and more cardinality results for
    the whole universe. -/
@[nospecialize]
def setupCartFinite [HolBase]
    (MESON_TAC ASM_MESON_TAC : List thm → tactic)
    (ARITH_RULE' : term → IO (Except String thm))
    (INDUCT_TAC : tactic)
    (CCart : CartCart) (CFImg : CartFiniteImage)
    (LE_REFL LET_ANTISYM LE : thm)
    (FINITE_RULES IN_ELIM_THM EXTENSION SUBSET IN_SING IN_IMAGE IN_UNIV
     IN_ELIM_PAIR_THM EXISTS_PAIR_THM FINITE_SUBSET FINITE_IMAGE FINITE_PRODUCT
     SURJECTIVE_IMAGE_EQ HAS_SIZE_IMAGE_INJ HAS_SIZE_FUNSPACE_UNIV HAS_SIZE
     IMP_CONJ_ALT EQ_IMP : thm) :
    ExceptT String IO CartFinite := do
  let ARITH_RULE (t : term) : ExceptT String IO thm := ARITH_RULE' t
  let { cart_tybij, CART_EQ, LAMBDA_BETA, .. } := CCart
  let { HAS_SIZE_FINITE_IMAGE, .. } := CFImg

  /- Finiteness lemma. -/

  let FINITE_CART ← prove
   r"!P. (!i. 1 <= i /\ i <= dimindex(:N) ==> FINITE {x | P i x})
       ==> FINITE {v:A^N | !i. 1 <= i /\ i <= dimindex(:N) ==> P i (v$i)}"
   (GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN
     (← q r"!n. n <= dimindex(:N)
        ==> FINITE {v:A^N | (!i. 1 <= i /\ i <= dimindex(:N) /\ i <= n
                                 ==> P i (v$i)) /\
                            (!i. 1 <= i /\ i <= dimindex(:N) /\ n < i
                                 ==> v$i = @x. F)}")
     (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"dimindex(:N)") th))) THEN
    REWRITE_TAC [LE_REFL, LET_ANTISYM] THEN
    INDUCT_TAC THENL
     [REWRITE_TAC [← ARITH_RULE (← q r"1 <= i /\ i <= n /\ i <= 0 <=> F")] THEN
      SIMP_TAC [← ARITH_RULE (← q r"1 <= i /\ i <= n /\ 0 < i <=> 1 <= i /\ i <= n")] THEN
      SUBGOAL_THEN
       (← q r"{v | !i. 1 <= i /\ i <= dimindex (:N) ==> v$i = (@x. F)} =
        {(lambda i. @x. F):A^N}")
       (fun th => SIMP_TAC [FINITE_RULES, th]) THEN
      SIMP_TAC [EXTENSION, IN_SING, IN_ELIM_THM, CART_EQ, LAMBDA_BETA],
      ALL_TAC] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
     (← q r"IMAGE (\(x:A,v:A^N). (lambda i. if i = SUC n then x else v$i):A^N)
          {x,v | x IN {x:A | P (SUC n) x} /\
                 v IN {v:A^N | (!i. 1 <= i /\ i <= dimindex(:N) /\ i <= n
                                ==> P i (v$i)) /\
                           (!i. 1 <= i /\ i <= dimindex (:N) /\ n < i
                                ==> v$i = (@x. F))}}") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN
      ASM_SIMP_TAC [FINITE_PRODUCT, ← ARITH_RULE (← q r"1 <= SUC n"),
                    ← ARITH_RULE (← q r"SUC n <= m ==> n <= m")],
      ALL_TAC] THEN
    REWRITE_TAC [SUBSET, IN_IMAGE, IN_ELIM_PAIR_THM, EXISTS_PAIR_THM] THEN
    X_GEN_TAC (← q r"v:A^N") THEN REWRITE_TAC [IN_ELIM_THM] THEN
    STRIP_TAC THEN EXISTS_TAC (← q r"(v:A^N)$(SUC n)") THEN
    EXISTS_TAC (← q r"(lambda i. if i = SUC n then @x. F else (v:A^N)$i):A^N") THEN
    SIMP_TAC [CART_EQ, LAMBDA_BETA, ← ARITH_RULE (← q r"i <= n ==> ~(i = SUC n)")] THEN
    ASM_MESON_TAC [LE, ← ARITH_RULE (← q r"1 <= SUC n"),
                   ← ARITH_RULE (← q r"n < i /\ ~(i = SUC n) ==> SUC n < i")])

  /- More cardinality results for whole universe. -/

  let HAS_SIZE_CART_UNIV ← prove
   r"!m. (:A) HAS_SIZE m ==> (:A^N) HAS_SIZE m EXP (dimindex(:N))"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"(:(N)finite_image->A) HAS_SIZE m EXP (dimindex(:N))")
    MP_TAC THENL
     [ASM_SIMP_TAC [HAS_SIZE_FUNSPACE_UNIV, HAS_SIZE_FINITE_IMAGE],
      DISCH_THEN (fun th => tactic_of do
        pure (MP_TAC (← ISPEC (← q r"mk_cart:((N)finite_image->A)->A^N")
          (← MATCH_MP (← REWRITE_RULE [IMP_CONJ_ALT] HAS_SIZE_IMAGE_INJ) th)))) THEN
      REWRITE_TAC [IN_UNIV] THEN
      ANTS_TAC THENL [MESON_TAC [cart_tybij], MATCH_MP_TAC EQ_IMP] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
      REWRITE_TAC [IN_UNIV] THEN MESON_TAC [cart_tybij]])

  let CARD_CART_UNIV ← prove
   r"FINITE(:A) ==> CARD(:A^N) = CARD(:A) EXP dimindex(:N)"
   (MESON_TAC [HAS_SIZE_CART_UNIV, HAS_SIZE])

  let FINITE_CART_UNIV ← prove
   r"FINITE(:A) ==> FINITE(:A^N)"
   (MESON_TAC [HAS_SIZE_CART_UNIV, HAS_SIZE])

  return {
    FINITE_CART, HAS_SIZE_CART_UNIV, CARD_CART_UNIV, FINITE_CART_UNIV }

/-- cart.ml 551-567: `vector` and `IN_ELIM_PASTECART_THM`.

    `vector` (554) builds a cart from a list: `(vector l):A^N = lambda i.
    EL (i - 1) l`, so the `EL` constant (lists.ml) must already be installed
    when its body parses; Session forces `listDefs` before this bundle.  It is
    a threaded `new_definition`.  `IN_ELIM_PASTECART_THM` (561) is a `prove`. -/
structure CartVector where
  /-- `vector` (cart.ml 554): `(vector l):A^N = lambda i. EL (i - 1) l`.
      `new_definition`.  Bridges cart -> lists (uses `EL`) and cart -> the
      `lambda` binder / `$` indexing installed earlier in the file. -/
  vector : thm
  /-- `IN_ELIM_PASTECART_THM` (cart.ml 561): `!P (a:A^M) (b:A^N). pastecart a b
      IN {pastecart x y | P x y} <=> P a b`.  `REWRITE_TAC[IN_ELIM_THM;
      PASTECART_EQ; FSTCART_PASTECART; SNDCART_PASTECART] THEN MESON_TAC[]`. -/
  IN_ELIM_PASTECART_THM : thm
  deriving Inhabited

/-- cart.ml 554-571: explicit construction of a vector from a list of
    components, and a set membership elimination theorem. -/
@[nospecialize]
def setupCartVector [HolBase]
    (new_definition' : term → IO (Except String thm))
    (MESON_TAC : List thm → tactic)
    (CFSum : CartFiniteSum) (IN_ELIM_THM : thm) :
    ExceptT String IO CartVector := do
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let { FSTCART_PASTECART, SNDCART_PASTECART, PASTECART_EQ, .. } := CFSum

  /- Explicit construction of a vector from a list of components. -/

  let vector ← new_definition
   r"(vector l):A^N = lambda i. EL (i - 1) l"

  /- Convenient set membership elimination theorem. -/

  let IN_ELIM_PASTECART_THM ← prove
   r"!P (a:A^M) (b:A^N). pastecart a b IN {pastecart x y | P x y} <=> P a b"
   (REWRITE_TAC [IN_ELIM_THM, PASTECART_EQ,
                 FSTCART_PASTECART, SNDCART_PASTECART] THEN
    MESON_TAC [])

  return {
    vector, IN_ELIM_PASTECART_THM }

end

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms DSLThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax



/-- Install the `PCROSS` infix (cart.ml 571): `parse_as_infix("PCROSS",(22,
    "right"))`.  Must run once, before the `PCROSS` definition and any term
    using the symbol is parsed. -/
def setupCartPcrossInfix : IO Unit := do
  -- cart.ml 571.
  HolCore.Printer.parse_as_infix ("PCROSS", (22, "right"))


end

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms DSLThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax

/-- The `PCROSS` "pasting" product of two vector sets and its theory
    (cart.ml 573-733).

    `s PCROSS t` is the set of `pastecart x y` for `x IN s`, `y IN t`; it is a
    variant of the set product living in the `finite_sum` cart type.  `PCROSS`
    (573) is the sole `new_definition`; the rest are plain `prove`s plus two
    `CONJ_PAIR o prove` pairs (704/715).  In each pair the first name gets the
    first conjunct (the `f,g` clause) and the second name gets the conjunction
    of the remaining two clauses.

    Depends on `CFSum` (pastecart theory), `CVec` (`IN_ELIM_PASTECART_THM`) and
    threaded Sets/HAS_SIZE theorems. -/
structure CartPcross where
  /-- `PCROSS` (cart.ml 573): `s PCROSS t = {pastecart (x:A^M) (y:A^N) |
      x IN s /\ y IN t}`.  `new_definition`; body uses the `PCROSS` infix
      installed at cart.ml 571. -/
  PCROSS : thm
  /-- `FORALL_IN_PCROSS` (cart.ml 576): `(!z:A^(M,N)finite_sum. z IN s PCROSS t
      ==> P z) <=> (!x y. x IN s /\ y IN t ==> P(pastecart x y))`.
      `REWRITE_TAC[PCROSS; FORALL_IN_GSPEC]`. -/
  FORALL_IN_PCROSS : thm
  /-- `EXISTS_IN_PCROSS` (cart.ml 581): `(?z:A^(M,N)finite_sum. z IN s PCROSS t
      /\ P z) <=> (?x y. x IN s /\ y IN t /\ P(pastecart x y))`.
      `REWRITE_TAC[PCROSS; EXISTS_IN_GSPEC; CONJ_ASSOC]`. -/
  EXISTS_IN_PCROSS : thm
  /-- `PASTECART_IN_PCROSS` (cart.ml 586): `!s t (x:A^M) (y:A^N).
      (pastecart x y) IN (s PCROSS t) <=> x IN s /\ y IN t`.
      `REWRITE_TAC[PCROSS; IN_ELIM_PASTECART_THM]`. -/
  PASTECART_IN_PCROSS : thm
  /-- `PCROSS_EQ_EMPTY` (cart.ml 590): `!(s:A^M->bool) (t:A^N->bool). s PCROSS t
      = {} <=> s = {} \/ t = {}`.  `REWRITE_TAC[PCROSS] THEN SET_TAC[]`. -/
  PCROSS_EQ_EMPTY : thm
  /-- `PCROSS_EMPTY` (cart.ml 594): `(!s. (s PCROSS {}) = {}) /\
      (!t. ({} PCROSS t) = {})`.  `REWRITE_TAC[PCROSS_EQ_EMPTY]`. -/
  PCROSS_EMPTY : thm
  /-- `PCROSS_SING` (cart.ml 599): `!(x:A^M) (y:A^N). {x} PCROSS {y} =
      {pastecart x y}`.  `REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_SING;
      PASTECART_IN_PCROSS; PASTECART_INJ]`. -/
  PCROSS_SING : thm
  /-- `SUBSET_PCROSS` (cart.ml 604): `!(s:A^M->bool) (t:A^N->bool) s' t'.
      s PCROSS t SUBSET s' PCROSS t' <=> s = {} \/ t = {} \/ s SUBSET s' /\
      t SUBSET t'`.  `SIMP_TAC[PCROSS; EXTENSION; IN_ELIM_PASTECART_THM;
      SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; NOT_IN_EMPTY] THEN
      MESON_TAC[]`. -/
  SUBSET_PCROSS : thm
  /-- `PCROSS_MONO` (cart.ml 611): `!(s:A^M->bool) (t:A^N->bool) s' t'.
      s SUBSET s' /\ t SUBSET t' ==> s PCROSS t SUBSET s' PCROSS t'`.
      `SIMP_TAC[SUBSET_PCROSS]`. -/
  PCROSS_MONO : thm
  /-- `PCROSS_EQ` (cart.ml 616): `!s s':real^M->bool t t':real^N->bool.
      s PCROSS t = s' PCROSS t' <=> (s = {} \/ t = {}) /\ (s' = {} \/ t' = {})
      \/ s = s' /\ t = t'`.  `REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ;
      SUBSET_PCROSS] THEN SET_TAC[]`. -/
  PCROSS_EQ : thm
  /-- `UNIV_PCROSS_UNIV` (cart.ml 622): `(:A^M) PCROSS (:A^N) =
      (:A^(M,N)finite_sum)`.  `REWRITE_TAC[EXTENSION; FORALL_PASTECART;
      PASTECART_IN_PCROSS; IN_UNIV]`. -/
  UNIV_PCROSS_UNIV : thm
  /-- `HAS_SIZE_PCROSS` (cart.ml 626): `!(s:A^M->bool) (t:A^N->bool) m n.
      s HAS_SIZE m /\ t HAS_SIZE n ==> (s PCROSS t) HAS_SIZE (m * n)`.
      Structured: `REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(MP_TAC o
      MATCH_MP HAS_SIZE_PRODUCT) THEN MATCH_MP_TAC EQ_IMP THEN SPEC_TAC ...
      THEN MATCH_MP_TAC BIJECTIONS_HAS_SIZE_EQ THEN EXISTS_TAC ... THEN
      EXISTS_TAC ... THEN REWRITE_TAC (three).  `o` at 630: `MP_TAC o
      MATCH_MP`, MATCH_MP first. -/
  HAS_SIZE_PCROSS : thm
  /-- `FINITE_PCROSS` (cart.ml 639): `!(s:A^M->bool) (t:A^N->bool). FINITE s /\
      FINITE t ==> FINITE(s PCROSS t)`.  `MESON_TAC[REWRITE_RULE[HAS_SIZE]
      HAS_SIZE_PCROSS]`. -/
  FINITE_PCROSS : thm
  /-- `FINITE_PCROSS_EQ` (cart.ml 644): `!(s:A^M->bool) (t:A^N->bool).
      FINITE(s PCROSS t) <=> s = {} \/ t = {} \/ FINITE s /\ FINITE t`.
      THENL at 651 (width 2, 2 branches, trailing chain OUTSIDE); closes with
      `ASM SET_TAC[]`. -/
  FINITE_PCROSS_EQ : thm
  /-- `IMAGE_FSTCART_PCROSS` (cart.ml 658): `!s:real^M->bool t:real^N->bool.
      IMAGE fstcart (s PCROSS t) = if t = {} then {} else s`.  `REPEAT GEN_TAC
      THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[PCROSS_EMPTY; IMAGE_CLAUSES] THEN
      REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
      REWRITE_TAC[EXISTS_IN_PCROSS; FSTCART_PASTECART] THEN ASM SET_TAC[]`. -/
  IMAGE_FSTCART_PCROSS : thm
  /-- `IMAGE_SNDCART_PCROSS` (cart.ml 666): `!s:real^M->bool t:real^N->bool.
      IMAGE sndcart (s PCROSS t) = if s = {} then {} else t`.  Same shape as
      `IMAGE_FSTCART_PCROSS` with `SNDCART_PASTECART`. -/
  IMAGE_SNDCART_PCROSS : thm
  /-- `PCROSS_INTER` (cart.ml 674): the conjoined distributivity over `INTER`.
      `REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_INTER; PASTECART_IN_PCROSS]
      THEN REPEAT STRIP_TAC THEN CONV_TAC TAUT`. -/
  PCROSS_INTER : thm
  /-- `PCROSS_UNION` (cart.ml 682): distributivity over `UNION`.
      `REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_UNION; PASTECART_IN_PCROSS]
      THEN REPEAT STRIP_TAC THEN CONV_TAC TAUT`. -/
  PCROSS_UNION : thm
  /-- `PCROSS_DIFF` (cart.ml 690): distributivity over `DIFF`.
      `REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_DIFF; PASTECART_IN_PCROSS]
      THEN REPEAT STRIP_TAC THEN CONV_TAC TAUT`. -/
  PCROSS_DIFF : thm
  /-- `INTER_PCROSS` (cart.ml 698): `!(s:A^M->bool) s' (t:A^N->bool) t'.
      (s PCROSS t) INTER (s' PCROSS t') = (s INTER s') PCROSS (t INTER t')`.
      `REWRITE_TAC[EXTENSION; IN_INTER; FORALL_PASTECART; PASTECART_IN_PCROSS]
      THEN CONV_TAC TAUT`. -/
  INTER_PCROSS : thm
  /-- `PCROSS_UNIONS_UNIONS` (cart.ml 704, FIRST name of the `(CONJ_PAIR o
      prove)` pair): the `f,g` clause `((UNIONS f) PCROSS (UNIONS g)) =
      UNIONS {s PCROSS t | s IN f /\ t IN g}`.  First conjunct of the proved
      theorem. -/
  PCROSS_UNIONS_UNIONS : thm
  /-- `PCROSS_UNIONS` (cart.ml 704, SECOND name): the CONJ of the remaining two
      clauses (`s,f` and `f,t`).  Second component of `CONJ_PAIR`. -/
  PCROSS_UNIONS : thm
  /-- `PCROSS_INTERS_INTERS` (cart.ml 715, FIRST name of the `(CONJ_PAIR o
      prove)` pair): the `f,g` clause with the `if f = {} ... else if g = {}
      ... else ...` body.  First conjunct of the proved theorem. -/
  PCROSS_INTERS_INTERS : thm
  /-- `PCROSS_INTERS` (cart.ml 715, SECOND name): the CONJ of the remaining two
      clauses (`s,f` and `f,t`).  Second component of `CONJ_PAIR`. -/
  PCROSS_INTERS : thm
  /-- `DISJOINT_PCROSS` (cart.ml 729): `!s:A^M->bool t:A^N->bool s' t'.
      DISJOINT (s PCROSS t) (s' PCROSS t') <=> DISJOINT s s' \/ DISJOINT t t'`.
      `REWRITE_TAC[DISJOINT; INTER_PCROSS; PCROSS_EQ_EMPTY]`. -/
  DISJOINT_PCROSS : thm
  deriving Inhabited

/-- cart.ml 573-733: a variant of product types using pasting of vectors.
    The `PCROSS` infix is set up by Session before this runs. -/
@[nospecialize]
def setupCartPcross [HolBase]
    (new_definition' : term → IO (Except String thm))
    (MESON_TAC : List thm → tactic)
    (SET_TAC : List thm → tactic)
    (CFSum : CartFiniteSum) (CVec : CartVector)
    (FORALL_IN_GSPEC EXISTS_IN_GSPEC CONJ_ASSOC IN_ELIM_THM EXTENSION IN_SING
     IN_UNIV IN_INTER IN_UNION IN_DIFF NOT_IN_EMPTY SUBSET DISJOINT
     SUBSET_ANTISYM_EQ IMAGE_CLAUSES CONJ_SYM UNIONS_GSPEC INTERS_GSPEC
     IN_ELIM_PAIR_THM FINITE_EMPTY FINITE_SUBSET FINITE_IMAGE IN_IMAGE HAS_SIZE
     HAS_SIZE_PRODUCT BIJECTIONS_HAS_SIZE_EQ EQ_IMP : thm) :
    ExceptT String IO CartPcross := do
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let TAUT_CONV : ioconv := fun t => (TAUT t).run
  let { FSTCART_PASTECART, SNDCART_PASTECART, PASTECART_FST_SND,
        FORALL_PASTECART, EXISTS_PASTECART, PASTECART_INJ, .. } := CFSum
  let { IN_ELIM_PASTECART_THM, .. } := CVec

  /- Variant of product types using pasting of vectors. -/

  let PCROSS ← new_definition
   r"s PCROSS t = {pastecart (x:A^M) (y:A^N) | x IN s /\ y IN t}"

  let FORALL_IN_PCROSS ← prove
   r"(!z:A^(M,N)finite_sum. z IN s PCROSS t ==> P z) <=>
   (!x y. x IN s /\ y IN t ==> P(pastecart x y))"
   (REWRITE_TAC [PCROSS, FORALL_IN_GSPEC])

  let EXISTS_IN_PCROSS ← prove
   r"(?z:A^(M,N)finite_sum. z IN s PCROSS t /\ P z) <=>
   (?x y. x IN s /\ y IN t /\ P(pastecart x y))"
   (REWRITE_TAC [PCROSS, EXISTS_IN_GSPEC, CONJ_ASSOC])

  let PASTECART_IN_PCROSS ← prove
   r"!s t (x:A^M) (y:A^N). (pastecart x y) IN (s PCROSS t) <=> x IN s /\ y IN t"
   (REWRITE_TAC [PCROSS, IN_ELIM_PASTECART_THM])

  let PCROSS_EQ_EMPTY ← prove
   r"!(s:A^M->bool) (t:A^N->bool). s PCROSS t = {} <=> s = {} \/ t = {}"
   (REWRITE_TAC [PCROSS] THEN SET_TAC [])

  let PCROSS_EMPTY ← prove
   r"(!s. (s PCROSS {}) :A^(M,N)finite_sum->bool = {}) /\
   (!t. ({} PCROSS t) :A^(M,N)finite_sum->bool = {})"
   (REWRITE_TAC [PCROSS_EQ_EMPTY])

  let PCROSS_SING ← prove
   r"!(x:A^M) (y:A^N). {x} PCROSS {y} = {pastecart x y}"
   (REWRITE_TAC [EXTENSION, FORALL_PASTECART, IN_SING, PASTECART_IN_PCROSS,
                 PASTECART_INJ])

  let SUBSET_PCROSS ← prove
   r"!(s:A^M->bool) (t:A^N->bool) s' t'.
        s PCROSS t SUBSET s' PCROSS t' <=>
        s = {} \/ t = {} \/ s SUBSET s' /\ t SUBSET t'"
   (SIMP_TAC [PCROSS, EXTENSION, IN_ELIM_PASTECART_THM, SUBSET,
     FORALL_PASTECART, PASTECART_IN_PCROSS, NOT_IN_EMPTY] THEN MESON_TAC [])

  let PCROSS_MONO ← prove
   r"!(s:A^M->bool) (t:A^N->bool) s' t'.
        s SUBSET s' /\ t SUBSET t' ==> s PCROSS t SUBSET s' PCROSS t'"
   (SIMP_TAC [SUBSET_PCROSS])

  let PCROSS_EQ ← prove
   r"!s s':real^M->bool t t':real^N->bool.
        s PCROSS t = s' PCROSS t' <=>
        (s = {} \/ t = {}) /\ (s' = {} \/ t' = {}) \/ s = s' /\ t = t'"
   (REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ, SUBSET_PCROSS] THEN SET_TAC [])

  let UNIV_PCROSS_UNIV ← prove
   r"(:A^M) PCROSS (:A^N) = (:A^(M,N)finite_sum)"
   (REWRITE_TAC [EXTENSION, FORALL_PASTECART, PASTECART_IN_PCROSS, IN_UNIV])

  let HAS_SIZE_PCROSS ← prove
   r"!(s:A^M->bool) (t:A^N->bool) m n.
        s HAS_SIZE m /\ t HAS_SIZE n ==> (s PCROSS t) HAS_SIZE (m * n)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do pure (MP_TAC (← MATCH_MP HAS_SIZE_PRODUCT th))) THEN
    MATCH_MP_TAC EQ_IMP THEN SPEC_TAC (← q r"m * n:num", ← q r"k:num") THEN
    MATCH_MP_TAC BIJECTIONS_HAS_SIZE_EQ THEN
    EXISTS_TAC (← q r"\(x:A^M,y:A^N). pastecart x y") THEN
    EXISTS_TAC (← q r"\z:A^(M,N)finite_sum. fstcart z,sndcart z") THEN
    REWRITE_TAC [FORALL_IN_GSPEC, PASTECART_IN_PCROSS] THEN
    REWRITE_TAC [IN_ELIM_PAIR_THM, PASTECART_FST_SND] THEN
    REWRITE_TAC [FORALL_IN_PCROSS, FSTCART_PASTECART, SNDCART_PASTECART])

  let FINITE_PCROSS ← prove
   r"!(s:A^M->bool) (t:A^N->bool).
        FINITE s /\ FINITE t ==> FINITE(s PCROSS t)"
   (MESON_TAC [← REWRITE_RULE [HAS_SIZE] HAS_SIZE_PCROSS])

  let FINITE_PCROSS_EQ ← prove
   r"!(s:A^M->bool) (t:A^N->bool).
        FINITE(s PCROSS t) <=> s = {} \/ t = {} \/ FINITE s /\ FINITE t"
   (REPEAT GEN_TAC THEN
    MAP_EVERY ASM_CASES_TAC [← q r"s:A^M->bool = {}", ← q r"t:A^N->bool = {}"] THEN
    ASM_REWRITE_TAC [PCROSS_EMPTY, FINITE_EMPTY] THEN
    EQ_TAC THEN SIMP_TAC [FINITE_PCROSS] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THENL
     [EXISTS_TAC (← q r"IMAGE fstcart ((s PCROSS t):A^(M,N)finite_sum->bool)"),
      EXISTS_TAC (← q r"IMAGE sndcart ((s PCROSS t):A^(M,N)finite_sum->bool)")] THEN
    ASM_SIMP_TAC [FINITE_IMAGE, SUBSET, IN_IMAGE, EXISTS_PASTECART] THEN
    REWRITE_TAC [PASTECART_IN_PCROSS, FSTCART_PASTECART, SNDCART_PASTECART] THEN
    ASM SET_TAC [])

  let IMAGE_FSTCART_PCROSS ← prove
   r"!s:real^M->bool t:real^N->bool.
        IMAGE fstcart (s PCROSS t) = if t = {} then {} else s"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [PCROSS_EMPTY, IMAGE_CLAUSES] THEN
    REWRITE_TAC [EXTENSION, IN_IMAGE] THEN ONCE_REWRITE_TAC [CONJ_SYM] THEN
    REWRITE_TAC [EXISTS_IN_PCROSS, FSTCART_PASTECART] THEN ASM SET_TAC [])

  let IMAGE_SNDCART_PCROSS ← prove
   r"!s:real^M->bool t:real^N->bool.
        IMAGE sndcart (s PCROSS t) = if s = {} then {} else t"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [PCROSS_EMPTY, IMAGE_CLAUSES] THEN
    REWRITE_TAC [EXTENSION, IN_IMAGE] THEN ONCE_REWRITE_TAC [CONJ_SYM] THEN
    REWRITE_TAC [EXISTS_IN_PCROSS, SNDCART_PASTECART] THEN ASM SET_TAC [])

  let PCROSS_INTER ← prove
   r"(!(s:A^M->bool) (t:A^N->bool) u.
        s PCROSS (t INTER u) = (s PCROSS t) INTER (s PCROSS u)) /\
   (!(s:A^M->bool) t (u:A^N->bool).
        (s INTER t) PCROSS u = (s PCROSS u) INTER (t PCROSS u))"
   (REWRITE_TAC [EXTENSION, FORALL_PASTECART, IN_INTER, PASTECART_IN_PCROSS] THEN
    REPEAT STRIP_TAC THEN CONV_TAC TAUT_CONV)

  let PCROSS_UNION ← prove
   r"(!(s:A^M->bool) (t:A^N->bool) u.
        s PCROSS (t UNION u) = (s PCROSS t) UNION (s PCROSS u)) /\
   (!(s:A^M->bool) t (u:A^N->bool).
        (s UNION t) PCROSS u = (s PCROSS u) UNION (t PCROSS u))"
   (REWRITE_TAC [EXTENSION, FORALL_PASTECART, IN_UNION, PASTECART_IN_PCROSS] THEN
    REPEAT STRIP_TAC THEN CONV_TAC TAUT_CONV)

  let PCROSS_DIFF ← prove
   r"(!(s:A^M->bool) (t:A^N->bool) u.
        s PCROSS (t DIFF u) = (s PCROSS t) DIFF (s PCROSS u)) /\
   (!(s:A^M->bool) t (u:A^N->bool).
        (s DIFF t) PCROSS u = (s PCROSS u) DIFF (t PCROSS u))"
   (REWRITE_TAC [EXTENSION, FORALL_PASTECART, IN_DIFF, PASTECART_IN_PCROSS] THEN
    REPEAT STRIP_TAC THEN CONV_TAC TAUT_CONV)

  let INTER_PCROSS ← prove
   r"!(s:A^M->bool) s' (t:A^N->bool) t'.
      (s PCROSS t) INTER (s' PCROSS t') = (s INTER s') PCROSS (t INTER t')"
   (REWRITE_TAC [EXTENSION, IN_INTER, FORALL_PASTECART, PASTECART_IN_PCROSS] THEN
    CONV_TAC TAUT_CONV)

  let (PCROSS_UNIONS_UNIONS, PCROSS_UNIONS) ← CONJ_PAIR (← prove
   r"(!f g. ((UNIONS f) PCROSS (UNIONS g)) :A^(M,N)finite_sum->bool =
          UNIONS {s PCROSS t | s IN f /\ t IN g}) /\
   (!s f. (s PCROSS (UNIONS f)) :A^(M,N)finite_sum->bool =
          UNIONS {s PCROSS t | t IN f}) /\
   (!f t. ((UNIONS f) PCROSS t) :A^(M,N)finite_sum->bool =
          UNIONS {s PCROSS t | s IN f})"
   (REWRITE_TAC [UNIONS_GSPEC, EXTENSION, FORALL_PASTECART, IN_ELIM_THM,
                 PASTECART_IN_PCROSS] THEN
    SET_TAC []))

  let (PCROSS_INTERS_INTERS, PCROSS_INTERS) ← CONJ_PAIR (← prove
   r"(!f g. ((INTERS f) PCROSS (INTERS g)) :A^(M,N)finite_sum->bool =
          if f = {} then INTERS {UNIV PCROSS t | t IN g}
          else if g = {} then INTERS {s PCROSS UNIV | s IN f}
          else INTERS {s PCROSS t | s IN f /\ t IN g}) /\
   (!s f. (s PCROSS (INTERS f)) :A^(M,N)finite_sum->bool =
          if f = {} then s PCROSS UNIV else INTERS {s PCROSS t | t IN f}) /\
   (!f t. ((INTERS f) PCROSS t) :A^(M,N)finite_sum->bool =
          if f = {} then UNIV PCROSS t else INTERS {s PCROSS t | s IN f})"
   (REPEAT STRIP_TAC THEN REPEAT (COND_CASES_TAC THEN REWRITE_TAC []) THEN
    ASM_REWRITE_TAC [INTERS_GSPEC, EXTENSION, FORALL_PASTECART, IN_ELIM_THM,
                     PASTECART_IN_PCROSS, NOT_IN_EMPTY] THEN
    ASM SET_TAC []))

  let DISJOINT_PCROSS ← prove
   r"!s:A^M->bool t:A^N->bool s' t'.
        DISJOINT (s PCROSS t) (s' PCROSS t') <=>
        DISJOINT s s' \/ DISJOINT t t'"
   (REWRITE_TAC [DISJOINT, INTER_PCROSS, PCROSS_EQ_EMPTY])

  return {
    PCROSS, FORALL_IN_PCROSS, EXISTS_IN_PCROSS, PASTECART_IN_PCROSS,
    PCROSS_EQ_EMPTY, PCROSS_EMPTY, PCROSS_SING, SUBSET_PCROSS, PCROSS_MONO,
    PCROSS_EQ, UNIV_PCROSS_UNIV, HAS_SIZE_PCROSS, FINITE_PCROSS,
    FINITE_PCROSS_EQ, IMAGE_FSTCART_PCROSS, IMAGE_SNDCART_PCROSS, PCROSS_INTER,
    PCROSS_UNION, PCROSS_DIFF, INTER_PCROSS, PCROSS_UNIONS_UNIONS,
    PCROSS_UNIONS, PCROSS_INTERS_INTERS, PCROSS_INTERS, DISJOINT_PCROSS }

end

end HolMath.Cart
