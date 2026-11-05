/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/products.ml.                                -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Products.lean

  The session half of the products.ml translation: it supplies
  HolLibrary.Products's dependencies from Session and exports every name
  under its HOL Light name.  Importing this module is
  `needs "Library/products.ml"`: each bundle is built by `initialize` when
  the module is loaded, in file order.
-/

import Session
import HolLibrary.Products

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Products

/-- The core theorems products.ml uses. -/
def core1 : HolLibrary.Products.CoreThms1 where
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
def core2 : HolLibrary.Products.CoreThms2 where
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
def core3 : HolLibrary.Products.CoreThms3 where
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
  support := Session.support

/-- What products.ml uses from Session. -/
def deps : HolLibrary.Products.ProductsDeps where
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
  core1 := core1
  core2 := core2
  core3 := core3

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in products.ml order. -/
initialize BNProduct : HolLibrary.Products.NProduct ←
  ioB "setupNProduct" (HolLibrary.Products.setupNProduct deps).run
initialize BIProduct : HolLibrary.Products.IProduct ←
  ioB "setupIProduct" (HolLibrary.Products.setupIProduct deps).run
initialize BProduct : HolLibrary.Products.Product ←
  ioB "setupProduct" (HolLibrary.Products.setupProduct deps).run

-- NProduct
def NPRODUCT_SUPPORT : thm := BNProduct.NPRODUCT_SUPPORT
def NPRODUCT_UNION : thm := BNProduct.NPRODUCT_UNION
def NPRODUCT_IMAGE : thm := BNProduct.NPRODUCT_IMAGE
def NPRODUCT_INJECTION : thm := BNProduct.NPRODUCT_INJECTION
def NPRODUCT_ADD_SPLIT : thm := BNProduct.NPRODUCT_ADD_SPLIT
def NPRODUCT_POS_LT : thm := BNProduct.NPRODUCT_POS_LT
def NPRODUCT_POS_LT_NUMSEG : thm := BNProduct.NPRODUCT_POS_LT_NUMSEG
def NPRODUCT_OFFSET : thm := BNProduct.NPRODUCT_OFFSET
def NPRODUCT_SING : thm := BNProduct.NPRODUCT_SING
def NPRODUCT_SING_NUMSEG : thm := BNProduct.NPRODUCT_SING_NUMSEG
def NPRODUCT_CLAUSES_NUMSEG : thm := BNProduct.NPRODUCT_CLAUSES_NUMSEG
def NPRODUCT_EQ : thm := BNProduct.NPRODUCT_EQ
def NPRODUCT_EQ_NUMSEG : thm := BNProduct.NPRODUCT_EQ_NUMSEG
def NPRODUCT_EQ_0 : thm := BNProduct.NPRODUCT_EQ_0
def NPRODUCT_EQ_0_NUMSEG : thm := BNProduct.NPRODUCT_EQ_0_NUMSEG
def NPRODUCT_RESTRICT : thm := BNProduct.NPRODUCT_RESTRICT
def NPRODUCT_RESTRICT_SET : thm := BNProduct.NPRODUCT_RESTRICT_SET
def NPRODUCT_LE : thm := BNProduct.NPRODUCT_LE
def NPRODUCT_LE_NUMSEG : thm := BNProduct.NPRODUCT_LE_NUMSEG
def NPRODUCT_EQ_1 : thm := BNProduct.NPRODUCT_EQ_1
def NPRODUCT_EQ_1_NUMSEG : thm := BNProduct.NPRODUCT_EQ_1_NUMSEG
def NPRODUCT_MUL_GEN : thm := BNProduct.NPRODUCT_MUL_GEN
def NPRODUCT_MUL : thm := BNProduct.NPRODUCT_MUL
def NPRODUCT_MUL_NUMSEG : thm := BNProduct.NPRODUCT_MUL_NUMSEG
def NPRODUCT_CONST : thm := BNProduct.NPRODUCT_CONST
def NPRODUCT_CONST_NUMSEG : thm := BNProduct.NPRODUCT_CONST_NUMSEG
def NPRODUCT_CONST_NUMSEG_1 : thm := BNProduct.NPRODUCT_CONST_NUMSEG_1
def NPRODUCT_ONE : thm := BNProduct.NPRODUCT_ONE
def NPRODUCT_CLOSED : thm := BNProduct.NPRODUCT_CLOSED
def NPRODUCT_RELATED : thm := BNProduct.NPRODUCT_RELATED
def NPRODUCT_CLOSED_NONEMPTY : thm := BNProduct.NPRODUCT_CLOSED_NONEMPTY
def NPRODUCT_RELATED_NONEMPTY : thm := BNProduct.NPRODUCT_RELATED_NONEMPTY
def CONG_NPRODUCT : thm := BNProduct.CONG_NPRODUCT
def NPRODUCT_CLAUSES_LEFT : thm := BNProduct.NPRODUCT_CLAUSES_LEFT
def NPRODUCT_CLAUSES_RIGHT : thm := BNProduct.NPRODUCT_CLAUSES_RIGHT
def NPRODUCT_SUPERSET : thm := BNProduct.NPRODUCT_SUPERSET
def NPRODUCT_UNIV : thm := BNProduct.NPRODUCT_UNIV
def NPRODUCT_PAIR : thm := BNProduct.NPRODUCT_PAIR
def NPRODUCT_REFLECT : thm := BNProduct.NPRODUCT_REFLECT
def NPRODUCT_DELETE : thm := BNProduct.NPRODUCT_DELETE
def NPRODUCT_FACT : thm := BNProduct.NPRODUCT_FACT
def NPRODUCT_DELTA : thm := BNProduct.NPRODUCT_DELTA
def EXP_NSUM : thm := BNProduct.EXP_NSUM
def HAS_SIZE_CART : thm := BNProduct.HAS_SIZE_CART
def CARD_CART : thm := BNProduct.CARD_CART

-- IProduct
def IPRODUCT_SUPPORT : thm := BIProduct.IPRODUCT_SUPPORT
def IPRODUCT_UNION : thm := BIProduct.IPRODUCT_UNION
def IPRODUCT_IMAGE : thm := BIProduct.IPRODUCT_IMAGE
def IPRODUCT_INJECTION : thm := BIProduct.IPRODUCT_INJECTION
def IPRODUCT_ADD_SPLIT : thm := BIProduct.IPRODUCT_ADD_SPLIT
def IPRODUCT_POS_LE : thm := BIProduct.IPRODUCT_POS_LE
def IPRODUCT_POS_LE_NUMSEG : thm := BIProduct.IPRODUCT_POS_LE_NUMSEG
def IPRODUCT_POS_LT : thm := BIProduct.IPRODUCT_POS_LT
def IPRODUCT_POS_LT_NUMSEG : thm := BIProduct.IPRODUCT_POS_LT_NUMSEG
def IPRODUCT_OFFSET : thm := BIProduct.IPRODUCT_OFFSET
def IPRODUCT_SING : thm := BIProduct.IPRODUCT_SING
def IPRODUCT_SING_NUMSEG : thm := BIProduct.IPRODUCT_SING_NUMSEG
def IPRODUCT_CLAUSES_NUMSEG : thm := BIProduct.IPRODUCT_CLAUSES_NUMSEG
def IPRODUCT_EQ : thm := BIProduct.IPRODUCT_EQ
def IPRODUCT_EQ_NUMSEG : thm := BIProduct.IPRODUCT_EQ_NUMSEG
def IPRODUCT_EQ_0 : thm := BIProduct.IPRODUCT_EQ_0
def IPRODUCT_EQ_0_NUMSEG : thm := BIProduct.IPRODUCT_EQ_0_NUMSEG
def IPRODUCT_RESTRICT : thm := BIProduct.IPRODUCT_RESTRICT
def IPRODUCT_RESTRICT_SET : thm := BIProduct.IPRODUCT_RESTRICT_SET
def IPRODUCT_LE : thm := BIProduct.IPRODUCT_LE
def IPRODUCT_LE_NUMSEG : thm := BIProduct.IPRODUCT_LE_NUMSEG
def IPRODUCT_EQ_1 : thm := BIProduct.IPRODUCT_EQ_1
def IPRODUCT_EQ_1_NUMSEG : thm := BIProduct.IPRODUCT_EQ_1_NUMSEG
def IPRODUCT_MUL_GEN : thm := BIProduct.IPRODUCT_MUL_GEN
def IPRODUCT_MUL : thm := BIProduct.IPRODUCT_MUL
def IPRODUCT_MUL_NUMSEG : thm := BIProduct.IPRODUCT_MUL_NUMSEG
def IPRODUCT_CONST : thm := BIProduct.IPRODUCT_CONST
def IPRODUCT_CONST_NUMSEG : thm := BIProduct.IPRODUCT_CONST_NUMSEG
def IPRODUCT_CONST_NUMSEG_1 : thm := BIProduct.IPRODUCT_CONST_NUMSEG_1
def IPRODUCT_NEG : thm := BIProduct.IPRODUCT_NEG
def IPRODUCT_NEG_NUMSEG : thm := BIProduct.IPRODUCT_NEG_NUMSEG
def IPRODUCT_NEG_NUMSEG_1 : thm := BIProduct.IPRODUCT_NEG_NUMSEG_1
def IPRODUCT_ONE : thm := BIProduct.IPRODUCT_ONE
def IPRODUCT_LE_1 : thm := BIProduct.IPRODUCT_LE_1
def IPRODUCT_ABS : thm := BIProduct.IPRODUCT_ABS
def IPRODUCT_CLOSED : thm := BIProduct.IPRODUCT_CLOSED
def IPRODUCT_RELATED : thm := BIProduct.IPRODUCT_RELATED
def IPRODUCT_CLOSED_NONEMPTY : thm := BIProduct.IPRODUCT_CLOSED_NONEMPTY
def IPRODUCT_RELATED_NONEMPTY : thm := BIProduct.IPRODUCT_RELATED_NONEMPTY
def IPRODUCT_CLAUSES_LEFT : thm := BIProduct.IPRODUCT_CLAUSES_LEFT
def IPRODUCT_CLAUSES_RIGHT : thm := BIProduct.IPRODUCT_CLAUSES_RIGHT
def INT_OF_NUM_NPRODUCT : thm := BIProduct.INT_OF_NUM_NPRODUCT
def IPRODUCT_SUPERSET : thm := BIProduct.IPRODUCT_SUPERSET
def IPRODUCT_UNIV : thm := BIProduct.IPRODUCT_UNIV
def IPRODUCT_PAIR : thm := BIProduct.IPRODUCT_PAIR
def IPRODUCT_REFLECT : thm := BIProduct.IPRODUCT_REFLECT
def IPRODUCT_DELETE : thm := BIProduct.IPRODUCT_DELETE
def IPRODUCT_DELTA : thm := BIProduct.IPRODUCT_DELTA
def INT_POW_NSUM : thm := BIProduct.INT_POW_NSUM

-- Product
def PRODUCT_SUPPORT : thm := BProduct.PRODUCT_SUPPORT
def PRODUCT_UNION : thm := BProduct.PRODUCT_UNION
def PRODUCT_IMAGE : thm := BProduct.PRODUCT_IMAGE
def PRODUCT_INJECTION : thm := BProduct.PRODUCT_INJECTION
def PRODUCT_ADD_SPLIT : thm := BProduct.PRODUCT_ADD_SPLIT
def PRODUCT_POS_LE : thm := BProduct.PRODUCT_POS_LE
def PRODUCT_POS_LE_NUMSEG : thm := BProduct.PRODUCT_POS_LE_NUMSEG
def PRODUCT_POS_LT : thm := BProduct.PRODUCT_POS_LT
def PRODUCT_POS_LT_NUMSEG : thm := BProduct.PRODUCT_POS_LT_NUMSEG
def PRODUCT_OFFSET : thm := BProduct.PRODUCT_OFFSET
def PRODUCT_SING : thm := BProduct.PRODUCT_SING
def PRODUCT_SING_NUMSEG : thm := BProduct.PRODUCT_SING_NUMSEG
def PRODUCT_CLAUSES_NUMSEG : thm := BProduct.PRODUCT_CLAUSES_NUMSEG
def PRODUCT_EQ : thm := BProduct.PRODUCT_EQ
def PRODUCT_EQ_NUMSEG : thm := BProduct.PRODUCT_EQ_NUMSEG
def PRODUCT_EQ_0 : thm := BProduct.PRODUCT_EQ_0
def PRODUCT_EQ_0_NUMSEG : thm := BProduct.PRODUCT_EQ_0_NUMSEG
def PRODUCT_RESTRICT : thm := BProduct.PRODUCT_RESTRICT
def PRODUCT_RESTRICT_SET : thm := BProduct.PRODUCT_RESTRICT_SET
def PRODUCT_LE : thm := BProduct.PRODUCT_LE
def PRODUCT_LE_NUMSEG : thm := BProduct.PRODUCT_LE_NUMSEG
def PRODUCT_EQ_1 : thm := BProduct.PRODUCT_EQ_1
def PRODUCT_EQ_1_NUMSEG : thm := BProduct.PRODUCT_EQ_1_NUMSEG
def PRODUCT_MUL_GEN : thm := BProduct.PRODUCT_MUL_GEN
def PRODUCT_MUL : thm := BProduct.PRODUCT_MUL
def PRODUCT_MUL_NUMSEG : thm := BProduct.PRODUCT_MUL_NUMSEG
def PRODUCT_CONST : thm := BProduct.PRODUCT_CONST
def PRODUCT_CONST_NUMSEG : thm := BProduct.PRODUCT_CONST_NUMSEG
def PRODUCT_CONST_NUMSEG_1 : thm := BProduct.PRODUCT_CONST_NUMSEG_1
def PRODUCT_NEG : thm := BProduct.PRODUCT_NEG
def PRODUCT_NEG_NUMSEG : thm := BProduct.PRODUCT_NEG_NUMSEG
def PRODUCT_NEG_NUMSEG_1 : thm := BProduct.PRODUCT_NEG_NUMSEG_1
def PRODUCT_INV : thm := BProduct.PRODUCT_INV
def PRODUCT_DIV : thm := BProduct.PRODUCT_DIV
def PRODUCT_DIV_NUMSEG : thm := BProduct.PRODUCT_DIV_NUMSEG
def PRODUCT_ONE : thm := BProduct.PRODUCT_ONE
def PRODUCT_LE_1 : thm := BProduct.PRODUCT_LE_1
def PRODUCT_ABS : thm := BProduct.PRODUCT_ABS
def PRODUCT_CLOSED : thm := BProduct.PRODUCT_CLOSED
def PRODUCT_RELATED : thm := BProduct.PRODUCT_RELATED
def PRODUCT_CLOSED_NONEMPTY : thm := BProduct.PRODUCT_CLOSED_NONEMPTY
def PRODUCT_RELATED_NONEMPTY : thm := BProduct.PRODUCT_RELATED_NONEMPTY
def PRODUCT_CLAUSES_LEFT : thm := BProduct.PRODUCT_CLAUSES_LEFT
def PRODUCT_CLAUSES_RIGHT : thm := BProduct.PRODUCT_CLAUSES_RIGHT
def REAL_OF_NUM_NPRODUCT : thm := BProduct.REAL_OF_NUM_NPRODUCT
def PRODUCT_SUPERSET : thm := BProduct.PRODUCT_SUPERSET
def PRODUCT_UNIV : thm := BProduct.PRODUCT_UNIV
def PRODUCT_PAIR : thm := BProduct.PRODUCT_PAIR
def PRODUCT_REFLECT : thm := BProduct.PRODUCT_REFLECT
def PRODUCT_DELETE : thm := BProduct.PRODUCT_DELETE
def PRODUCT_DELTA : thm := BProduct.PRODUCT_DELTA
def REAL_POW_NSUM : thm := BProduct.REAL_POW_NSUM
def POLYNOMIAL_FUNCTION_PRODUCT : thm := BProduct.POLYNOMIAL_FUNCTION_PRODUCT






/-- `needs "Library/products.ml"`: already done by importing this module. -/
def ensureProducts : IO Unit := pure ()

end SessionLibrary.Products
