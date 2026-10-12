/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/products.ml.                                -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Products.lean

  The `unsafe` half of the products.ml translation: it supplies
  HolLibrary.Products's dependencies from Session, builds each bundle once,
  in file order, and exports every name under its HOL Light name.
  `ensureProducts` is `needs "Library/products.ml"`.

  The blocks between `@@CORE` and `@@EXPORTS` markers are generated from
  HolLibrary/Products.lean by tools/productsdiff/gen_session.py and scope.py
  (bookkeeping only: field-by-field copies and accessors).
-/

import Session
import HolLibrary.Products

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Products

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

-- @@CORE BEGIN
/-- The core theorems products.ml uses. -/
unsafe def core1 (_ : Unit) : HolLibrary.Products.CoreThms1 where
  ADD_SUB := Session.ADD_SUB
  ARITH := Session.ARITH
  ARITH_EQ := Session.ARITH_EQ
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_NUMSEG := Session.CARD_NUMSEG
  CARD_NUMSEG_1 := Session.CARD_NUMSEG_1
  CARD_SING := Session.CARD_SING
  CART_EQ := Session.CART_EQ
  CONJ_ASSOC := Session.CONJ_ASSOC
  DISJOINT_NUMSEG := Session.DISJOINT_NUMSEG
  EQ_ADD_RCANCEL := Session.EQ_ADD_RCANCEL
  EXISTS_PAIR_THM := Session.EXISTS_PAIR_THM
  EXP := Session.EXP
  EXP_ADD := Session.EXP_ADD
  EXTENSION := Session.EXTENSION
  FACT := Session.FACT
  FINITE_HAS_SIZE := Session.FINITE_HAS_SIZE
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FINITE_RULES := Session.FINITE_RULES
  FINITE_SING := Session.FINITE_SING
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_IMAGE_INJ := Session.HAS_SIZE_IMAGE_INJ
  HAS_SIZE_PRODUCT := Session.HAS_SIZE_PRODUCT
  IMP_CONJ := Session.IMP_CONJ
  IMP_IMP := Session.IMP_IMP
  INT_ABS_MUL := Session.INT_ABS_MUL
  INT_ABS_NUM := Session.INT_ABS_NUM
  INT_ENTIRE := Session.INT_ENTIRE
  INT_LE_MUL := Session.INT_LE_MUL
  INT_LE_MUL2 := Session.INT_LE_MUL2
  INT_LE_REFL := Session.INT_LE_REFL
  INT_LT_01 := Session.INT_LT_01
  INT_LT_MUL := Session.INT_LT_MUL
  INT_MUL_AC := Session.INT_MUL_AC
  INT_MUL_LID := Session.INT_MUL_LID
  INT_MUL_LNEG := Session.INT_MUL_LNEG
  INT_MUL_RID := Session.INT_MUL_RID
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_MUL := Session.INT_OF_NUM_MUL
  INT_POS := Session.INT_POS
/-- The core theorems products.ml uses. -/
unsafe def core2 (_ : Unit) : HolLibrary.Products.CoreThms2 where
  INT_POW := Session.INT_POW
  INT_POW_ADD := Session.INT_POW_ADD
  IN_ELIM_PAIR_THM := Session.IN_ELIM_PAIR_THM
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_NUMSEG := Session.IN_NUMSEG
  IN_SING := Session.IN_SING
  IPRODUCT_CLAUSES := Session.IPRODUCT_CLAUSES
  ITERATE_CLOSED := Session.ITERATE_CLOSED
  ITERATE_CLOSED_NONEMPTY := Session.ITERATE_CLOSED_NONEMPTY
  ITERATE_DELETE := Session.ITERATE_DELETE
  ITERATE_DELTA := Session.ITERATE_DELTA
  ITERATE_EQ := Session.ITERATE_EQ
  ITERATE_EQ_NEUTRAL := Session.ITERATE_EQ_NEUTRAL
  ITERATE_IMAGE := Session.ITERATE_IMAGE
  ITERATE_INJECTION := Session.ITERATE_INJECTION
  ITERATE_OP_GEN := Session.ITERATE_OP_GEN
  ITERATE_PAIR := Session.ITERATE_PAIR
  ITERATE_REFLECT := Session.ITERATE_REFLECT
  ITERATE_RELATED := Session.ITERATE_RELATED
  ITERATE_RELATED_NONEMPTY := Session.ITERATE_RELATED_NONEMPTY
  ITERATE_RESTRICT_SET := Session.ITERATE_RESTRICT_SET
  ITERATE_SUPERSET := Session.ITERATE_SUPERSET
  ITERATE_SUPPORT := Session.ITERATE_SUPPORT
  ITERATE_UNION := Session.ITERATE_UNION
  ITERATE_UNIV := Session.ITERATE_UNIV
  LAMBDA_BETA := Session.LAMBDA_BETA
  LE := Session.LE
  LET_ANTISYM := Session.LET_ANTISYM
  LE_0 := Session.LE_0
  LE_MULT2 := Session.LE_MULT2
  LE_REFL := Session.LE_REFL
  LT_MULT := Session.LT_MULT
  LT_REFL := Session.LT_REFL
  MONOIDAL_INT_MUL := Session.MONOIDAL_INT_MUL
  MONOIDAL_MUL := Session.MONOIDAL_MUL
  MONOIDAL_REAL_MUL := Session.MONOIDAL_REAL_MUL
  MULT_AC := Session.MULT_AC
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EQ_0 := Session.MULT_EQ_0
  MULT_SYM := Session.MULT_SYM
  NEUTRAL_INT_MUL := Session.NEUTRAL_INT_MUL
  NEUTRAL_MUL := Session.NEUTRAL_MUL
/-- The core theorems products.ml uses. -/
unsafe def core3 (_ : Unit) : HolLibrary.Products.CoreThms3 where
  NEUTRAL_REAL_MUL := Session.NEUTRAL_REAL_MUL
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_LT := Session.NOT_LT
  NPRODUCT_CLAUSES := Session.NPRODUCT_CLAUSES
  NSUM_CLAUSES := Session.NSUM_CLAUSES
  NUMSEG_ADD_SPLIT := Session.NUMSEG_ADD_SPLIT
  NUMSEG_CLAUSES := Session.NUMSEG_CLAUSES
  NUMSEG_LREC := Session.NUMSEG_LREC
  NUMSEG_OFFSET_IMAGE := Session.NUMSEG_OFFSET_IMAGE
  NUMSEG_SING := Session.NUMSEG_SING
  PAIR_EQ := Session.PAIR_EQ
  POLYNOMIAL_FUNCTION_CONST := Session.POLYNOMIAL_FUNCTION_CONST
  POLYNOMIAL_FUNCTION_MUL := Session.POLYNOMIAL_FUNCTION_MUL
  PRODUCT_CLAUSES := Session.PRODUCT_CLAUSES
  REAL_ABS_MUL := Session.REAL_ABS_MUL
  REAL_ABS_NUM := Session.REAL_ABS_NUM
  REAL_ENTIRE := Session.REAL_ENTIRE
  REAL_INV_1 := Session.REAL_INV_1
  REAL_INV_MUL := Session.REAL_INV_MUL
  REAL_LE_MUL := Session.REAL_LE_MUL
  REAL_LE_MUL2 := Session.REAL_LE_MUL2
  REAL_LE_REFL := Session.REAL_LE_REFL
  REAL_LT_01 := Session.REAL_LT_01
  REAL_LT_MUL := Session.REAL_LT_MUL
  REAL_MUL_AC := Session.REAL_MUL_AC
  REAL_MUL_LID := Session.REAL_MUL_LID
  REAL_MUL_LNEG := Session.REAL_MUL_LNEG
  REAL_MUL_RID := Session.REAL_MUL_RID
  REAL_OF_NUM_EQ := Session.REAL_OF_NUM_EQ
  REAL_OF_NUM_MUL := Session.REAL_OF_NUM_MUL
  REAL_POS := Session.REAL_POS
  REAL_POW_ADD := Session.REAL_POW_ADD
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM_EQ := Session.SUBSET_ANTISYM_EQ
  SUC_SUB1 := Session.SUC_SUB1
  iproduct := Session.iproduct
  nproduct := Session.nproduct
  o_DEF := Session.o_DEF
  product := Session.product
  real_div := Session.real_div
  real_pow := Session.real_pow
  support := Session.support-- @@CORE END

/-- What products.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.Products.ProductsDeps where
  prioritize_num := do
    match ← HolCore.Kernel.mk_type "num" [] with
    | .ok ty => Session.prioritize_overload ty
    | .error e => throw (IO.userError e)
  prioritize_real := Session.prioritize_real
  extend_basic_congs := Session.extend_basic_congs
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  NUMBER_RULE t := ExceptT.mk (Session.NUMBER_RULE t)
  core1 := core1 ()
  core2 := core2 ()
  core3 := core3 ()

/-- Build a bundle once.  `setup` is a thunk, so that `deps` is not built
    before the bundle is needed.  The whole core library is built first
    (`Session.ensureDefine`, and MATCH_CONV's basic conversions, which HOL
    Light adds loading ind_types.ml). -/
private unsafe def cached {α : Type} [Inhabited α] (r : IO.Ref (Option α)) (name : String)
    (setup : Unit → IO (Except String α)) : α :=
  match unsafeIO (do
    match ← r.get with
    | some d => pure d
    | none => do
      Session.ensureDefine
      let _ ← Session.MATCH_CONV (HolCore.Kernel.mk_var "p" HolCore.Kernel.bool_ty)
      match ← setup () with
      | .ok d => do r.set (some d); pure d
      | .error e => panic! s!"{name} failed: {e}") with
  | .ok d => d | _ => panic! s!"SessionLibrary.Products: {name}"

/- The bundles, in products.ml order.  Each forces the one before it, so
   that any bundle builds every earlier one first, as HOL Light's load does. -/

-- @@BUNDLES BEGIN
initialize theNProduct : IO.Ref (Option HolLibrary.Products.NProduct) ← IO.mkRef none
unsafe def BNProduct : HolLibrary.Products.NProduct :=
  cached theNProduct "setupNProduct" fun _ => do
    (HolLibrary.Products.setupNProduct (deps ())).run

initialize theIProduct : IO.Ref (Option HolLibrary.Products.IProduct) ← IO.mkRef none
unsafe def BIProduct : HolLibrary.Products.IProduct :=
  cached theIProduct "setupIProduct" fun _ => do
    let _ ← IO.mkRef BNProduct.NPRODUCT_SUPPORT
    (HolLibrary.Products.setupIProduct (deps ())).run

initialize theProduct : IO.Ref (Option HolLibrary.Products.Product) ← IO.mkRef none
unsafe def BProduct : HolLibrary.Products.Product :=
  cached theProduct "setupProduct" fun _ => do
    let _ ← IO.mkRef BIProduct.IPRODUCT_SUPPORT
    (HolLibrary.Products.setupProduct (deps ())).run

-- @@BUNDLES END

-- @@EXPORTS BEGIN
-- NProduct
unsafe def NPRODUCT_SUPPORT : thm := BNProduct.NPRODUCT_SUPPORT
unsafe def NPRODUCT_UNION : thm := BNProduct.NPRODUCT_UNION
unsafe def NPRODUCT_IMAGE : thm := BNProduct.NPRODUCT_IMAGE
unsafe def NPRODUCT_INJECTION : thm := BNProduct.NPRODUCT_INJECTION
unsafe def NPRODUCT_ADD_SPLIT : thm := BNProduct.NPRODUCT_ADD_SPLIT
unsafe def NPRODUCT_POS_LT : thm := BNProduct.NPRODUCT_POS_LT
unsafe def NPRODUCT_POS_LT_NUMSEG : thm := BNProduct.NPRODUCT_POS_LT_NUMSEG
unsafe def NPRODUCT_OFFSET : thm := BNProduct.NPRODUCT_OFFSET
unsafe def NPRODUCT_SING : thm := BNProduct.NPRODUCT_SING
unsafe def NPRODUCT_SING_NUMSEG : thm := BNProduct.NPRODUCT_SING_NUMSEG
unsafe def NPRODUCT_CLAUSES_NUMSEG : thm := BNProduct.NPRODUCT_CLAUSES_NUMSEG
unsafe def NPRODUCT_EQ : thm := BNProduct.NPRODUCT_EQ
unsafe def NPRODUCT_EQ_NUMSEG : thm := BNProduct.NPRODUCT_EQ_NUMSEG
unsafe def NPRODUCT_EQ_0 : thm := BNProduct.NPRODUCT_EQ_0
unsafe def NPRODUCT_EQ_0_NUMSEG : thm := BNProduct.NPRODUCT_EQ_0_NUMSEG
unsafe def NPRODUCT_RESTRICT : thm := BNProduct.NPRODUCT_RESTRICT
unsafe def NPRODUCT_RESTRICT_SET : thm := BNProduct.NPRODUCT_RESTRICT_SET
unsafe def NPRODUCT_LE : thm := BNProduct.NPRODUCT_LE
unsafe def NPRODUCT_LE_NUMSEG : thm := BNProduct.NPRODUCT_LE_NUMSEG
unsafe def NPRODUCT_EQ_1 : thm := BNProduct.NPRODUCT_EQ_1
unsafe def NPRODUCT_EQ_1_NUMSEG : thm := BNProduct.NPRODUCT_EQ_1_NUMSEG
unsafe def NPRODUCT_MUL_GEN : thm := BNProduct.NPRODUCT_MUL_GEN
unsafe def NPRODUCT_MUL : thm := BNProduct.NPRODUCT_MUL
unsafe def NPRODUCT_MUL_NUMSEG : thm := BNProduct.NPRODUCT_MUL_NUMSEG
unsafe def NPRODUCT_CONST : thm := BNProduct.NPRODUCT_CONST
unsafe def NPRODUCT_CONST_NUMSEG : thm := BNProduct.NPRODUCT_CONST_NUMSEG
unsafe def NPRODUCT_CONST_NUMSEG_1 : thm := BNProduct.NPRODUCT_CONST_NUMSEG_1
unsafe def NPRODUCT_ONE : thm := BNProduct.NPRODUCT_ONE
unsafe def NPRODUCT_CLOSED : thm := BNProduct.NPRODUCT_CLOSED
unsafe def NPRODUCT_RELATED : thm := BNProduct.NPRODUCT_RELATED
unsafe def NPRODUCT_CLOSED_NONEMPTY : thm := BNProduct.NPRODUCT_CLOSED_NONEMPTY
unsafe def NPRODUCT_RELATED_NONEMPTY : thm := BNProduct.NPRODUCT_RELATED_NONEMPTY
unsafe def CONG_NPRODUCT : thm := BNProduct.CONG_NPRODUCT
unsafe def NPRODUCT_CLAUSES_LEFT : thm := BNProduct.NPRODUCT_CLAUSES_LEFT
unsafe def NPRODUCT_CLAUSES_RIGHT : thm := BNProduct.NPRODUCT_CLAUSES_RIGHT
unsafe def NPRODUCT_SUPERSET : thm := BNProduct.NPRODUCT_SUPERSET
unsafe def NPRODUCT_UNIV : thm := BNProduct.NPRODUCT_UNIV
unsafe def NPRODUCT_PAIR : thm := BNProduct.NPRODUCT_PAIR
unsafe def NPRODUCT_REFLECT : thm := BNProduct.NPRODUCT_REFLECT
unsafe def NPRODUCT_DELETE : thm := BNProduct.NPRODUCT_DELETE
unsafe def NPRODUCT_FACT : thm := BNProduct.NPRODUCT_FACT
unsafe def NPRODUCT_DELTA : thm := BNProduct.NPRODUCT_DELTA
unsafe def EXP_NSUM : thm := BNProduct.EXP_NSUM
unsafe def HAS_SIZE_CART : thm := BNProduct.HAS_SIZE_CART
unsafe def CARD_CART : thm := BNProduct.CARD_CART

-- IProduct
unsafe def IPRODUCT_SUPPORT : thm := BIProduct.IPRODUCT_SUPPORT
unsafe def IPRODUCT_UNION : thm := BIProduct.IPRODUCT_UNION
unsafe def IPRODUCT_IMAGE : thm := BIProduct.IPRODUCT_IMAGE
unsafe def IPRODUCT_INJECTION : thm := BIProduct.IPRODUCT_INJECTION
unsafe def IPRODUCT_ADD_SPLIT : thm := BIProduct.IPRODUCT_ADD_SPLIT
unsafe def IPRODUCT_POS_LE : thm := BIProduct.IPRODUCT_POS_LE
unsafe def IPRODUCT_POS_LE_NUMSEG : thm := BIProduct.IPRODUCT_POS_LE_NUMSEG
unsafe def IPRODUCT_POS_LT : thm := BIProduct.IPRODUCT_POS_LT
unsafe def IPRODUCT_POS_LT_NUMSEG : thm := BIProduct.IPRODUCT_POS_LT_NUMSEG
unsafe def IPRODUCT_OFFSET : thm := BIProduct.IPRODUCT_OFFSET
unsafe def IPRODUCT_SING : thm := BIProduct.IPRODUCT_SING
unsafe def IPRODUCT_SING_NUMSEG : thm := BIProduct.IPRODUCT_SING_NUMSEG
unsafe def IPRODUCT_CLAUSES_NUMSEG : thm := BIProduct.IPRODUCT_CLAUSES_NUMSEG
unsafe def IPRODUCT_EQ : thm := BIProduct.IPRODUCT_EQ
unsafe def IPRODUCT_EQ_NUMSEG : thm := BIProduct.IPRODUCT_EQ_NUMSEG
unsafe def IPRODUCT_EQ_0 : thm := BIProduct.IPRODUCT_EQ_0
unsafe def IPRODUCT_EQ_0_NUMSEG : thm := BIProduct.IPRODUCT_EQ_0_NUMSEG
unsafe def IPRODUCT_RESTRICT : thm := BIProduct.IPRODUCT_RESTRICT
unsafe def IPRODUCT_RESTRICT_SET : thm := BIProduct.IPRODUCT_RESTRICT_SET
unsafe def IPRODUCT_LE : thm := BIProduct.IPRODUCT_LE
unsafe def IPRODUCT_LE_NUMSEG : thm := BIProduct.IPRODUCT_LE_NUMSEG
unsafe def IPRODUCT_EQ_1 : thm := BIProduct.IPRODUCT_EQ_1
unsafe def IPRODUCT_EQ_1_NUMSEG : thm := BIProduct.IPRODUCT_EQ_1_NUMSEG
unsafe def IPRODUCT_MUL_GEN : thm := BIProduct.IPRODUCT_MUL_GEN
unsafe def IPRODUCT_MUL : thm := BIProduct.IPRODUCT_MUL
unsafe def IPRODUCT_MUL_NUMSEG : thm := BIProduct.IPRODUCT_MUL_NUMSEG
unsafe def IPRODUCT_CONST : thm := BIProduct.IPRODUCT_CONST
unsafe def IPRODUCT_CONST_NUMSEG : thm := BIProduct.IPRODUCT_CONST_NUMSEG
unsafe def IPRODUCT_CONST_NUMSEG_1 : thm := BIProduct.IPRODUCT_CONST_NUMSEG_1
unsafe def IPRODUCT_NEG : thm := BIProduct.IPRODUCT_NEG
unsafe def IPRODUCT_NEG_NUMSEG : thm := BIProduct.IPRODUCT_NEG_NUMSEG
unsafe def IPRODUCT_NEG_NUMSEG_1 : thm := BIProduct.IPRODUCT_NEG_NUMSEG_1
unsafe def IPRODUCT_ONE : thm := BIProduct.IPRODUCT_ONE
unsafe def IPRODUCT_LE_1 : thm := BIProduct.IPRODUCT_LE_1
unsafe def IPRODUCT_ABS : thm := BIProduct.IPRODUCT_ABS
unsafe def IPRODUCT_CLOSED : thm := BIProduct.IPRODUCT_CLOSED
unsafe def IPRODUCT_RELATED : thm := BIProduct.IPRODUCT_RELATED
unsafe def IPRODUCT_CLOSED_NONEMPTY : thm := BIProduct.IPRODUCT_CLOSED_NONEMPTY
unsafe def IPRODUCT_RELATED_NONEMPTY : thm := BIProduct.IPRODUCT_RELATED_NONEMPTY
unsafe def IPRODUCT_CLAUSES_LEFT : thm := BIProduct.IPRODUCT_CLAUSES_LEFT
unsafe def IPRODUCT_CLAUSES_RIGHT : thm := BIProduct.IPRODUCT_CLAUSES_RIGHT
unsafe def INT_OF_NUM_NPRODUCT : thm := BIProduct.INT_OF_NUM_NPRODUCT
unsafe def IPRODUCT_SUPERSET : thm := BIProduct.IPRODUCT_SUPERSET
unsafe def IPRODUCT_UNIV : thm := BIProduct.IPRODUCT_UNIV
unsafe def IPRODUCT_PAIR : thm := BIProduct.IPRODUCT_PAIR
unsafe def IPRODUCT_REFLECT : thm := BIProduct.IPRODUCT_REFLECT
unsafe def IPRODUCT_DELETE : thm := BIProduct.IPRODUCT_DELETE
unsafe def IPRODUCT_DELTA : thm := BIProduct.IPRODUCT_DELTA
unsafe def INT_POW_NSUM : thm := BIProduct.INT_POW_NSUM

-- Product
unsafe def PRODUCT_SUPPORT : thm := BProduct.PRODUCT_SUPPORT
unsafe def PRODUCT_UNION : thm := BProduct.PRODUCT_UNION
unsafe def PRODUCT_IMAGE : thm := BProduct.PRODUCT_IMAGE
unsafe def PRODUCT_INJECTION : thm := BProduct.PRODUCT_INJECTION
unsafe def PRODUCT_ADD_SPLIT : thm := BProduct.PRODUCT_ADD_SPLIT
unsafe def PRODUCT_POS_LE : thm := BProduct.PRODUCT_POS_LE
unsafe def PRODUCT_POS_LE_NUMSEG : thm := BProduct.PRODUCT_POS_LE_NUMSEG
unsafe def PRODUCT_POS_LT : thm := BProduct.PRODUCT_POS_LT
unsafe def PRODUCT_POS_LT_NUMSEG : thm := BProduct.PRODUCT_POS_LT_NUMSEG
unsafe def PRODUCT_OFFSET : thm := BProduct.PRODUCT_OFFSET
unsafe def PRODUCT_SING : thm := BProduct.PRODUCT_SING
unsafe def PRODUCT_SING_NUMSEG : thm := BProduct.PRODUCT_SING_NUMSEG
unsafe def PRODUCT_CLAUSES_NUMSEG : thm := BProduct.PRODUCT_CLAUSES_NUMSEG
unsafe def PRODUCT_EQ : thm := BProduct.PRODUCT_EQ
unsafe def PRODUCT_EQ_NUMSEG : thm := BProduct.PRODUCT_EQ_NUMSEG
unsafe def PRODUCT_EQ_0 : thm := BProduct.PRODUCT_EQ_0
unsafe def PRODUCT_EQ_0_NUMSEG : thm := BProduct.PRODUCT_EQ_0_NUMSEG
unsafe def PRODUCT_RESTRICT : thm := BProduct.PRODUCT_RESTRICT
unsafe def PRODUCT_RESTRICT_SET : thm := BProduct.PRODUCT_RESTRICT_SET
unsafe def PRODUCT_LE : thm := BProduct.PRODUCT_LE
unsafe def PRODUCT_LE_NUMSEG : thm := BProduct.PRODUCT_LE_NUMSEG
unsafe def PRODUCT_EQ_1 : thm := BProduct.PRODUCT_EQ_1
unsafe def PRODUCT_EQ_1_NUMSEG : thm := BProduct.PRODUCT_EQ_1_NUMSEG
unsafe def PRODUCT_MUL_GEN : thm := BProduct.PRODUCT_MUL_GEN
unsafe def PRODUCT_MUL : thm := BProduct.PRODUCT_MUL
unsafe def PRODUCT_MUL_NUMSEG : thm := BProduct.PRODUCT_MUL_NUMSEG
unsafe def PRODUCT_CONST : thm := BProduct.PRODUCT_CONST
unsafe def PRODUCT_CONST_NUMSEG : thm := BProduct.PRODUCT_CONST_NUMSEG
unsafe def PRODUCT_CONST_NUMSEG_1 : thm := BProduct.PRODUCT_CONST_NUMSEG_1
unsafe def PRODUCT_NEG : thm := BProduct.PRODUCT_NEG
unsafe def PRODUCT_NEG_NUMSEG : thm := BProduct.PRODUCT_NEG_NUMSEG
unsafe def PRODUCT_NEG_NUMSEG_1 : thm := BProduct.PRODUCT_NEG_NUMSEG_1
unsafe def PRODUCT_INV : thm := BProduct.PRODUCT_INV
unsafe def PRODUCT_DIV : thm := BProduct.PRODUCT_DIV
unsafe def PRODUCT_DIV_NUMSEG : thm := BProduct.PRODUCT_DIV_NUMSEG
unsafe def PRODUCT_ONE : thm := BProduct.PRODUCT_ONE
unsafe def PRODUCT_LE_1 : thm := BProduct.PRODUCT_LE_1
unsafe def PRODUCT_ABS : thm := BProduct.PRODUCT_ABS
unsafe def PRODUCT_CLOSED : thm := BProduct.PRODUCT_CLOSED
unsafe def PRODUCT_RELATED : thm := BProduct.PRODUCT_RELATED
unsafe def PRODUCT_CLOSED_NONEMPTY : thm := BProduct.PRODUCT_CLOSED_NONEMPTY
unsafe def PRODUCT_RELATED_NONEMPTY : thm := BProduct.PRODUCT_RELATED_NONEMPTY
unsafe def PRODUCT_CLAUSES_LEFT : thm := BProduct.PRODUCT_CLAUSES_LEFT
unsafe def PRODUCT_CLAUSES_RIGHT : thm := BProduct.PRODUCT_CLAUSES_RIGHT
unsafe def REAL_OF_NUM_NPRODUCT : thm := BProduct.REAL_OF_NUM_NPRODUCT
unsafe def PRODUCT_SUPERSET : thm := BProduct.PRODUCT_SUPERSET
unsafe def PRODUCT_UNIV : thm := BProduct.PRODUCT_UNIV
unsafe def PRODUCT_PAIR : thm := BProduct.PRODUCT_PAIR
unsafe def PRODUCT_REFLECT : thm := BProduct.PRODUCT_REFLECT
unsafe def PRODUCT_DELETE : thm := BProduct.PRODUCT_DELETE
unsafe def PRODUCT_DELTA : thm := BProduct.PRODUCT_DELTA
unsafe def REAL_POW_NSUM : thm := BProduct.REAL_POW_NSUM
unsafe def POLYNOMIAL_FUNCTION_PRODUCT : thm := BProduct.POLYNOMIAL_FUNCTION_PRODUCT






-- @@EXPORTS END

/-- `needs "Library/products.ml"`: build every bundle, in file order. -/
unsafe def ensureProducts : IO Unit := do
  -- @@ENSURE BEGIN
  let _ ← IO.mkRef BNProduct.NPRODUCT_SUPPORT
  let _ ← IO.mkRef BIProduct.IPRODUCT_SUPPORT
  let _ ← IO.mkRef BProduct.PRODUCT_SUPPORT  -- @@ENSURE END
  pure ()

end SessionLibrary.Products
