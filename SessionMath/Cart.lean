/- File: SessionMath/Cart.lean
cart.ml: finite Cartesian product types, each layer built by `initialize`
when this module is imported, in file order.  Its parser changes each have
their own `initialize` at their file position:

  * `parse_as_infix("$",(25,"left"))`        (cart.ml 115)
  * `parse_as_binder "lambda"`               (cart.ml 126)
  * `parse_as_infix("PCROSS",(22,"right"))`  (cart.ml 571)

`DIMINDEX_CONV`, `HAS_SIZE_DIMINDEX_RULE` and `DIMINDEX_TAC` are conversions,
rules and tactics.
-/
import SessionMath.Iterate
import HolMath.Cart

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Simp HolCore.Theorems HolCore.Classic HolCore.Trivia

namespace Session

/- ====================================================================== -/
/- cart.ml.  Every bundle is forced eagerly by an `initialize`, IN FILE    -/
/- ORDER; the three parser side effects are interleaved at their TRUE      -/
/- positions (cart.ml 115, 126, 571).  iterate.ml has already loaded      -/
/- (cart.ml opens `needs "iterate.ml"`; this module imports it).          -/
/- ====================================================================== -/

/-- `CartDimindex` (cart.ml 14-48): the `dimindex` definition and its eight
    theorems.  `dimindex` is the sole `new_definition` of the range. -/
initialize CDim : HolMath.Cart.CartDimindex ← do
  ioOkI "setupCartDimindex" (HolMath.Cart.setupCartDimindex new_definition
    MESON_TAC SET_TAC ARITH_RULE Tv.one
    HAS_SIZE CARD_EQ_0 CARD_CLAUSES FINITE_RULES EXTENSION
    IN_UNIV IN_SING NOT_IN_EMPTY ARITH NUMSEG_LT).run

/-- `CartFiniteImage` (cart.ml 54-105): the FIRST `new_type_definition` in the
    development - creating `finite_image` and its `finite_index`/
    `dest_finite_image` pair (a KERNEL side effect).  Runs after `CDim` (the
    existence proof needs `DIMINDEX_GE_1`). -/
initialize CFImg : HolMath.Cart.CartFiniteImage ← do
  ioOkI "setupCartFiniteImage" (HolMath.Cart.setupCartFiniteImage new_type_definition
    MESON_TAC CDim
    IN_NUMSEG LE_REFL EXTENSION IN_UNIV IN_IMAGE HAS_SIZE
    HAS_SIZE_IMAGE_INJ HAS_SIZE_NUMSEG_1 CONJ_ASSOC).run

/-- The SECOND parser side effect of cart.ml: `parse_as_infix("$",(25,"left"))`
    (cart.ml 115) - vector indexing.  Its TRUE file position is BETWEEN the
    `cart` type creation (112) and `finite_index` (117); forced here, before
    the `CCart` bundle parses `x$i`. -/
initialize cartDollarInfix : Unit ← HolMath.Cart.setupCartDollarInfix

/-- The THIRD parser side effect of cart.ml: `parse_as_binder "lambda"`
    (cart.ml 126) - vector abstraction.  Its TRUE file position is AFTER
    `$`/`finite_index`/`CART_EQ` and BEFORE the `lambda` definition; forced
    here, before the `CCart` bundle parses `lambda i. ...`. -/
initialize cartLambdaBinder : Unit ← HolMath.Cart.setupCartLambdaBinder

/-- `CartCart` (cart.ml 111-168): the CENTRE of the file.  Creating the `cart`
    type operator (cart.ml 112) ACTIVATES the `^` type infix (a KERNEL side
    effect); runs after `CFImg` (its existence type mentions
    `(B)finite_image`), with the `$` infix (115) and `lambda` binder (126)
    installed FIRST. -/
initialize CCart : HolMath.Cart.CartCart ← do
  ioOkI "setupCartCart" (HolMath.Cart.setupCartCart new_type_definition new_definition
    MESON_TAC ASM_MESON_TAC SELECT_CONV CFImg
    FUN_EQ_THM ETA_AX C.SELECT_UNIQUE).run

/-- `CartFiniteSum` (cart.ml 174-273): the THIRD `new_type_definition`, and the
    FIRST applied to a LOCALLY PROVED nonemptiness theorem - the binary type
    operator `finite_sum` (a KERNEL side effect).  Runs after `CCart`. -/
initialize CFSum : HolMath.Cart.CartFiniteSum ← do
  ioOkI "setupCartFiniteSum" (HolMath.Cart.setupCartFiniteSum new_type_definition
    new_definition MESON_TAC ARITH_RULE IAr.ASM_ARITH_TAC
    CDim CCart
    IN_NUMSEG LE_REFL EXTENSION IN_UNIV IN_IMAGE HAS_SIZE
    HAS_SIZE_IMAGE_INJ HAS_SIZE_NUMSEG_1 ADD_SUB).run

/-- `CartFiniteDiff` (cart.ml 279-305): the FOURTH `new_type_definition` -
    `finite_diff` (a KERNEL side effect).  Runs after `CFSum`. -/
initialize CFDiff : HolMath.Cart.CartFiniteDiff ← do
  ioOkI "setupCartFiniteDiff" (HolMath.Cart.setupCartFiniteDiff new_type_definition
    MESON_TAC IAr.ARITH_TAC CDim
    IN_NUMSEG EXTENSION IN_UNIV IN_IMAGE HAS_SIZE
    HAS_SIZE_IMAGE_INJ HAS_SIZE_NUMSEG_1).run

/-- `CartFiniteProd` (cart.ml 312-335): the FIFTH `new_type_definition` -
    `finite_prod` (a KERNEL side effect).  Runs after `CFDiff`. -/
initialize CFProd : HolMath.Cart.CartFiniteProd ← do
  ioOkI "setupCartFiniteProd" (HolMath.Cart.setupCartFiniteProd new_type_definition
    MESON_TAC CDim
    IN_NUMSEG LE_REFL EXTENSION IN_UNIV IN_IMAGE HAS_SIZE
    HAS_SIZE_IMAGE_INJ HAS_SIZE_NUMSEG_1 LE_1 MULT_EQ_0).run

/-- `CartTybit` (cart.ml 338-405): the two `define_type` calls that create the
    binary "bit" type constructors `tybit0`/`tybit1`, plus their
    size/dimindex/finiteness theory - what makes `:2`, `:3`, `:4`, ... (and
    hence `:real^3`) exist.  Order is load-bearing even between the two
    `define_type` lines: `tybit1`'s body mentions the type `1`, so `tybit0`
    (341) must precede `tybit1` (344).  Runs after `CFProd` (`tybit0`'s body
    mentions `(A,A)finite_sum`). -/
initialize CTybit : HolMath.Cart.CartTybit ← do
  -- `finite_sum` already ran (CFSum's `initialize` precedes this one), as
  -- tybit0's body mentions `(A,A)finite_sum`.
  -- cart.ml 341-342: the FIRST define_type.  MUST run before line 344.
  let ⟨tybit0_INDUCT, tybit0_RECURSION⟩ ←
    (match ← define_type "tybit0 = mktybit0((A,A)finite_sum)" with
     | .ok x => pure x | .error e => throw (IO.userError s!"define_type tybit0: {e}"))
  -- cart.ml 344-345: the SECOND define_type.  Its body mentions the type `1`,
  -- so `1` must already exist; `tybit0` must already be defined.
  let ⟨tybit1_INDUCT, tybit1_RECURSION⟩ ←
    (match ← define_type "tybit1 = mktybit1(((A,A)finite_sum,1)finite_sum)" with
     | .ok x => pure x | .error e => throw (IO.userError s!"define_type tybit1: {e}"))
  -- Read the rectype theorems the two define_type calls populated.
  let cases0 ← (match ← cases "tybit0" with
    | .ok th => pure th | .error e => throw (IO.userError s!"cases tybit0: {e}"))
  let inj0 ← (match ← injectivity "tybit0" with
    | .ok th => pure th | .error e => throw (IO.userError s!"injectivity tybit0: {e}"))
  let cases1 ← (match ← cases "tybit1" with
    | .ok th => pure th | .error e => throw (IO.userError s!"cases tybit1: {e}"))
  let inj1 ← (match ← injectivity "tybit1" with
    | .ok th => pure th | .error e => throw (IO.userError s!"injectivity tybit1: {e}"))
  ioOkI "setupCartTybit" (HolMath.Cart.setupCartTybit MESON_TAC
    tybit0_INDUCT tybit0_RECURSION tybit1_INDUCT tybit1_RECURSION
    cases0 inj0 cases1 inj1
    CDim.DIMINDEX_UNIQUE CDim.HAS_SIZE_1 CDim.DIMINDEX_1
    CFSum.DIMINDEX_HAS_SIZE_FINITE_SUM CFSum.DIMINDEX_FINITE_SUM
    SURJECTIVE_IMAGE_EQ HAS_SIZE_IMAGE_INJ IN_UNIV HAS_SIZE
    MULT_2).run

/-- `CartDimindexConv` (cart.ml 406-479): the `dimindex`-computing conversion
    `DIMINDEX_CONV` (with `HAS_SIZE_DIMINDEX_RULE` and `DIMINDEX_TAC`) and the
    payoff theorems for cases 2, 3, 4.  `BITS_ELIM_CONV` is an `IO`-computed
    conversion, forced once and threaded in.  Runs after `CTybit`. -/
initialize CDConv : HolMath.Cart.CartDimindexConv ← do
  let bitsElim ← (match ← BITS_ELIM_CONV with
    | .ok c => pure c | .error e => throw (IO.userError s!"BITS_ELIM_CONV: {e}"))
  ioOkI "setupCartDimindexConv" (HolMath.Cart.setupCartDimindexConv IAr.ARITH_TAC MESON_TAC mk_numeral
    (fun t => pure (bitsElim t))
    Nm.NUMERAL CDim.dimindex CTybit.DIMINDEX_CLAUSES
    CDim.UNIV_HAS_SIZE_DIMINDEX HAS_SIZE CTybit.FINITE_CLAUSES).run

/-- `DIMINDEX_CONV` (cart.ml 409). -/
def DIMINDEX_CONV : conv := fun tm => CDConv.DIMINDEX_CONV tm
/-- `HAS_SIZE_DIMINDEX_RULE` (cart.ml 442). -/
def HAS_SIZE_DIMINDEX_RULE (ty : hol_type) : IO (Except String thm) :=
  CDConv.HAS_SIZE_DIMINDEX_RULE ty
/-- `DIMINDEX_TAC` (cart.ml 456). -/
def DIMINDEX_TAC : tactic := fun g => CDConv.DIMINDEX_TAC g

/-- `CartFinite` (cart.ml 480-548): the finiteness lemma `FINITE_CART` and the
    three whole-universe cardinality results.  Runs after `CDConv`. -/
initialize CFin : HolMath.Cart.CartFinite ← do
  ioOkI "setupCartFinite" (HolMath.Cart.setupCartFinite MESON_TAC ASM_MESON_TAC
    ARITH_RULE INDUCT_TAC CCart CFImg
    LE_REFL LET_ANTISYM LE
    FINITE_RULES IN_ELIM_THM EXTENSION SUBSET IN_SING IN_IMAGE
    IN_UNIV IN_ELIM_PAIR_THM EXISTS_PAIR_THM FINITE_SUBSET
    FINITE_IMAGE FINITE_PRODUCT SURJECTIVE_IMAGE_EQ
    HAS_SIZE_IMAGE_INJ HAS_SIZE_FUNSPACE_UNIV HAS_SIZE
    IMP_CONJ_ALT T.EQ_IMP).run

/-- `CartVector` (cart.ml 551-567): the `vector` definition and
    `IN_ELIM_PASTECART_THM`.  `vector`'s body `lambda i. EL (i - 1) l` names the
    lists-layer `EL` constant (`listDefs` declares `EL`), built by
    SessionMath/Lists.lean.  Runs after `CFin`. -/
initialize CVec : HolMath.Cart.CartVector ← do
  ioOkI "setupCartVector" (HolMath.Cart.setupCartVector new_definition MESON_TAC
    CFSum IN_ELIM_THM).run

/-- The THIRD and LAST parser side effect of cart.ml:
    `parse_as_infix("PCROSS",(22,"right"))` (cart.ml 571) - the "pasting"
    product infix.  Its TRUE file position is just before the `PCROSS`
    definition; forced here, before the `CPcross` bundle parses `s PCROSS t`. -/
initialize cartPcrossInfix : Unit ← HolMath.Cart.setupCartPcrossInfix

/-- `CartPcross` (cart.ml 573-733): the `PCROSS` "pasting" product and its
    166-line theory - the largest section of cart.ml, which COMPLETES the file.
    The `PCROSS` infix (571) is installed FIRST.  Runs after `CVec`. -/
initialize CPcross : HolMath.Cart.CartPcross ← do
  ioOkI "setupCartPcross" (HolMath.Cart.setupCartPcross new_definition MESON_TAC
    SET_TAC CFSum CVec
    FORALL_IN_GSPEC EXISTS_IN_GSPEC CONJ_ASSOC IN_ELIM_THM EXTENSION
    IN_SING IN_UNIV IN_INTER IN_UNION IN_DIFF NOT_IN_EMPTY SUBSET
    DISJOINT SUBSET_ANTISYM_EQ IMAGE_CLAUSES CONJ_SYM UNIONS_GSPEC
    INTERS_GSPEC IN_ELIM_PAIR_THM FINITE_EMPTY FINITE_SUBSET
    FINITE_IMAGE IN_IMAGE HAS_SIZE HAS_SIZE_PRODUCT
    BIJECTIONS_HAS_SIZE_EQ T.EQ_IMP).run

/-- A no-op: every cart.ml bundle is built at import.  Kept for callers of
    the old `ensureCart`. -/
def ensureCart : IO Unit := pure ()

/- ---------------------------------------------------------------------- -/
/- cart.ml bare theorem re-exports.                                       -/
/- ---------------------------------------------------------------------- -/
-- CartDimindex (cart.ml 14-48)
def dimindex                : thm := CDim.dimindex
def DIMINDEX_NONZERO        : thm := CDim.DIMINDEX_NONZERO
def DIMINDEX_GE_1           : thm := CDim.DIMINDEX_GE_1
def DIMINDEX_UNIV           : thm := CDim.DIMINDEX_UNIV
def DIMINDEX_UNIQUE         : thm := CDim.DIMINDEX_UNIQUE
def UNIV_HAS_SIZE_DIMINDEX  : thm := CDim.UNIV_HAS_SIZE_DIMINDEX
def HAS_SIZE_1              : thm := CDim.HAS_SIZE_1
def NUMSEG_LT_DIMINDEX      : thm := CDim.NUMSEG_LT_DIMINDEX
def DIMINDEX_1              : thm := CDim.DIMINDEX_1

-- CartFiniteImage (cart.ml 54-105)
def finite_image_tybij      : thm := CFImg.finite_image_tybij
def FINITE_IMAGE_IMAGE      : thm := CFImg.FINITE_IMAGE_IMAGE
def HAS_SIZE_FINITE_IMAGE   : thm := CFImg.HAS_SIZE_FINITE_IMAGE
def CARD_FINITE_IMAGE       : thm := CFImg.CARD_FINITE_IMAGE
def FINITE_FINITE_IMAGE     : thm := CFImg.FINITE_FINITE_IMAGE
def DIMINDEX_FINITE_IMAGE   : thm := CFImg.DIMINDEX_FINITE_IMAGE
def FINITE_INDEX_WORKS      : thm := CFImg.FINITE_INDEX_WORKS
def FINITE_INDEX_INJ        : thm := CFImg.FINITE_INDEX_INJ
def FORALL_FINITE_INDEX     : thm := CFImg.FORALL_FINITE_INDEX

-- CartCart (cart.ml 111-168)
def cart_tybij              : thm := CCart.cart_tybij
def finite_index            : thm := CCart.finite_index
def CART_EQ                 : thm := CCart.CART_EQ
def lambda                  : thm := CCart.lambda
def LAMBDA_BETA             : thm := CCart.LAMBDA_BETA
def LAMBDA_UNIQUE           : thm := CCart.LAMBDA_UNIQUE
def LAMBDA_ETA              : thm := CCart.LAMBDA_ETA
def FINITE_INDEX_INRANGE    : thm := CCart.FINITE_INDEX_INRANGE
def FINITE_INDEX_INRANGE_2  : thm := CCart.FINITE_INDEX_INRANGE_2
def CART_EQ_FULL            : thm := CCart.CART_EQ_FULL

-- CartFiniteSum (cart.ml 174-273)
def finite_sum_tybij            : thm := CFSum.finite_sum_tybij
def pastecart                   : thm := CFSum.pastecart
def fstcart                     : thm := CFSum.fstcart
def sndcart                     : thm := CFSum.sndcart
def FINITE_SUM_IMAGE            : thm := CFSum.FINITE_SUM_IMAGE
def DIMINDEX_HAS_SIZE_FINITE_SUM : thm := CFSum.DIMINDEX_HAS_SIZE_FINITE_SUM
def DIMINDEX_FINITE_SUM         : thm := CFSum.DIMINDEX_FINITE_SUM
def FSTCART_PASTECART           : thm := CFSum.FSTCART_PASTECART
def SNDCART_PASTECART           : thm := CFSum.SNDCART_PASTECART
def PASTECART_FST_SND           : thm := CFSum.PASTECART_FST_SND
def PASTECART_EQ                : thm := CFSum.PASTECART_EQ
def FORALL_PASTECART            : thm := CFSum.FORALL_PASTECART
def EXISTS_PASTECART            : thm := CFSum.EXISTS_PASTECART
def PASTECART_INJ               : thm := CFSum.PASTECART_INJ
def FSTCART_COMPONENT           : thm := CFSum.FSTCART_COMPONENT
def SNDCART_COMPONENT           : thm := CFSum.SNDCART_COMPONENT
def PASTECART_COMPONENT         : thm := CFSum.PASTECART_COMPONENT

-- CartFiniteDiff (cart.ml 279-305)
def finite_diff_tybij           : thm := CFDiff.finite_diff_tybij
def FINITE_DIFF_IMAGE           : thm := CFDiff.FINITE_DIFF_IMAGE
def DIMINDEX_HAS_SIZE_FINITE_DIFF : thm := CFDiff.DIMINDEX_HAS_SIZE_FINITE_DIFF
def DIMINDEX_FINITE_DIFF        : thm := CFDiff.DIMINDEX_FINITE_DIFF

-- CartFiniteProd (cart.ml 312-335)
def finite_prod_tybij           : thm := CFProd.finite_prod_tybij
def FINITE_PROD_IMAGE           : thm := CFProd.FINITE_PROD_IMAGE
def DIMINDEX_HAS_SIZE_FINITE_PROD : thm := CFProd.DIMINDEX_HAS_SIZE_FINITE_PROD
def DIMINDEX_FINITE_PROD        : thm := CFProd.DIMINDEX_FINITE_PROD

-- CartTybit (cart.ml 338-405)
def tybit0_INDUCT               : thm := CTybit.tybit0_INDUCT
def tybit0_RECURSION            : thm := CTybit.tybit0_RECURSION
def tybit1_INDUCT               : thm := CTybit.tybit1_INDUCT
def tybit1_RECURSION            : thm := CTybit.tybit1_RECURSION
def HAS_SIZE_TYBIT0             : thm := CTybit.HAS_SIZE_TYBIT0
def HAS_SIZE_TYBIT1             : thm := CTybit.HAS_SIZE_TYBIT1
def DIMINDEX_TYBIT0             : thm := CTybit.DIMINDEX_TYBIT0
def DIMINDEX_TYBIT1             : thm := CTybit.DIMINDEX_TYBIT1
def DIMINDEX_CLAUSES            : thm := CTybit.DIMINDEX_CLAUSES
def FINITE_1                    : thm := CTybit.FINITE_1
def FINITE_TYBIT0               : thm := CTybit.FINITE_TYBIT0
def FINITE_TYBIT1               : thm := CTybit.FINITE_TYBIT1
def FINITE_CLAUSES              : thm := CTybit.FINITE_CLAUSES

-- CartDimindexConv (cart.ml 406-479)
def DIMINDEX_2                  : thm := CDConv.DIMINDEX_2
def DIMINDEX_3                  : thm := CDConv.DIMINDEX_3
def DIMINDEX_4                  : thm := CDConv.DIMINDEX_4
def HAS_SIZE_2                  : thm := CDConv.HAS_SIZE_2
def HAS_SIZE_3                  : thm := CDConv.HAS_SIZE_3
def HAS_SIZE_4                  : thm := CDConv.HAS_SIZE_4

-- CartFinite (cart.ml 480-548)
def FINITE_CART                 : thm := CFin.FINITE_CART
def HAS_SIZE_CART_UNIV          : thm := CFin.HAS_SIZE_CART_UNIV
def CARD_CART_UNIV              : thm := CFin.CARD_CART_UNIV
def FINITE_CART_UNIV            : thm := CFin.FINITE_CART_UNIV

-- CartVector (cart.ml 551-567)
def vector                      : thm := CVec.vector
def IN_ELIM_PASTECART_THM       : thm := CVec.IN_ELIM_PASTECART_THM

-- CartPcross (cart.ml 573-733)
def PCROSS                      : thm := CPcross.PCROSS
def FORALL_IN_PCROSS            : thm := CPcross.FORALL_IN_PCROSS
def EXISTS_IN_PCROSS            : thm := CPcross.EXISTS_IN_PCROSS
def PASTECART_IN_PCROSS         : thm := CPcross.PASTECART_IN_PCROSS
def PCROSS_EQ_EMPTY             : thm := CPcross.PCROSS_EQ_EMPTY
def PCROSS_EMPTY                : thm := CPcross.PCROSS_EMPTY
def PCROSS_SING                 : thm := CPcross.PCROSS_SING
def SUBSET_PCROSS               : thm := CPcross.SUBSET_PCROSS
def PCROSS_MONO                 : thm := CPcross.PCROSS_MONO
def PCROSS_EQ                   : thm := CPcross.PCROSS_EQ
def UNIV_PCROSS_UNIV            : thm := CPcross.UNIV_PCROSS_UNIV
def HAS_SIZE_PCROSS             : thm := CPcross.HAS_SIZE_PCROSS
def FINITE_PCROSS               : thm := CPcross.FINITE_PCROSS
def FINITE_PCROSS_EQ            : thm := CPcross.FINITE_PCROSS_EQ
def IMAGE_FSTCART_PCROSS        : thm := CPcross.IMAGE_FSTCART_PCROSS
def IMAGE_SNDCART_PCROSS        : thm := CPcross.IMAGE_SNDCART_PCROSS
def PCROSS_INTER                : thm := CPcross.PCROSS_INTER
def PCROSS_UNION                : thm := CPcross.PCROSS_UNION
def PCROSS_DIFF                 : thm := CPcross.PCROSS_DIFF
def INTER_PCROSS                : thm := CPcross.INTER_PCROSS
def PCROSS_UNIONS_UNIONS        : thm := CPcross.PCROSS_UNIONS_UNIONS
def PCROSS_UNIONS               : thm := CPcross.PCROSS_UNIONS
def PCROSS_INTERS_INTERS        : thm := CPcross.PCROSS_INTERS_INTERS
def PCROSS_INTERS               : thm := CPcross.PCROSS_INTERS
def DISJOINT_PCROSS             : thm := CPcross.DISJOINT_PCROSS


end Session
