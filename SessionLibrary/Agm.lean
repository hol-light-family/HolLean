/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/agm.ml.                                     -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Agm.lean

  The session half of the agm.ml translation: it supplies HolLibrary.Agm's
  dependencies from Session and SessionLibrary.Products, and exports every
  name under its HOL Light name.  Importing this module is
  `needs "Library/agm.ml"`; its `needs "Library/products.ml"` is the import
  of SessionLibrary.Products.
-/

import Session
import HolLibrary.Agm
import SessionLibrary.Products

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Agm

/-- The core theorems agm.ml uses (products.ml's from
    SessionLibrary.Products). -/
def core1 : HolLibrary.Agm.CoreThms1 where
  ADD1 := Session.ADD1
  ADD_SYM := Session.ADD_SYM
  ARITH := Session.ARITH
  EVEN_EXISTS := Session.EVEN_EXISTS
  EXTENSION := Session.EXTENSION
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FINITE_RULES := Session.FINITE_RULES
  IN_INSERT := Session.IN_INSERT
  IN_NUMSEG := Session.IN_NUMSEG
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_EXISTS := Session.LE_EXISTS
  LE_REFL := Session.LE_REFL
  MULT_2 := Session.MULT_2
  NOT_EVEN := Session.NOT_EVEN
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  ODD_EXISTS := Session.ODD_EXISTS
  PRODUCT_ADD_SPLIT := SessionLibrary.Products.«PRODUCT_ADD_SPLIT»
  PRODUCT_CLAUSES := Session.PRODUCT_CLAUSES
  PRODUCT_CLAUSES_NUMSEG := SessionLibrary.Products.«PRODUCT_CLAUSES_NUMSEG»
  PRODUCT_OFFSET := SessionLibrary.Products.«PRODUCT_OFFSET»
  PRODUCT_POS_LE := SessionLibrary.Products.«PRODUCT_POS_LE»
  REAL_ADD_RID := Session.REAL_ADD_RID
  REAL_ENTIRE := Session.REAL_ENTIRE
  REAL_INV_EQ_0 := Session.REAL_INV_EQ_0
  REAL_INV_MUL := Session.REAL_INV_MUL
  REAL_LE_ANTISYM := Session.REAL_LE_ANTISYM
  REAL_LE_DIV := Session.REAL_LE_DIV
  REAL_LE_LMUL_EQ := Session.REAL_LE_LMUL_EQ
  REAL_LE_MUL := Session.REAL_LE_MUL
  REAL_LE_MUL2 := Session.REAL_LE_MUL2
  REAL_LE_REFL := Session.REAL_LE_REFL
  REAL_LE_SQUARE := Session.REAL_LE_SQUARE
  REAL_LE_TRANS := Session.REAL_LE_TRANS
  REAL_MUL_LZERO := Session.REAL_MUL_LZERO
  REAL_MUL_RID := Session.REAL_MUL_RID
  REAL_MUL_RZERO := Session.REAL_MUL_RZERO
  REAL_MUL_SYM := Session.REAL_MUL_SYM
  REAL_NOT_LT := Session.REAL_NOT_LT
  REAL_OF_NUM_EQ := Session.REAL_OF_NUM_EQ
  REAL_OF_NUM_LE := Session.REAL_OF_NUM_LE
  REAL_OF_NUM_MUL := Session.REAL_OF_NUM_MUL
  REAL_OF_NUM_SUC := Session.REAL_OF_NUM_SUC
  REAL_POS := Session.REAL_POS
  REAL_POW_LE2 := Session.REAL_POW_LE2
  REAL_POW_MUL := Session.REAL_POW_MUL
  REAL_POW_POW := Session.REAL_POW_POW
  SUM_ADD_SPLIT := Session.SUM_ADD_SPLIT
  SUM_CLAUSES := Session.SUM_CLAUSES
  SUM_CLAUSES_NUMSEG := Session.SUM_CLAUSES_NUMSEG
  SUM_OFFSET := Session.SUM_OFFSET
  SUM_POS_EQ_0_NUMSEG := Session.SUM_POS_EQ_0_NUMSEG
  SUM_POS_LE := Session.SUM_POS_LE
  num_WF := Session.num_WF
  real_div := Session.real_div
  real_pow := Session.real_pow

/-- What agm.ml uses from Session. -/
def deps : HolLibrary.Agm.AgmDeps where
  prioritize_real := Session.prioritize_real
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  MESON_TAC := Session.MESON_TAC
  REAL_ARITH t := ExceptT.mk (Session.REAL_ARITH3 t)
  REAL_FIELD t := ExceptT.mk (Session.REAL_FIELD t)
  core1 := core1

/-- agm.ml, run when this module is loaded (after products.ml, which agm.ml
    needs: the import of SessionLibrary.Products). -/
initialize BAgm : HolLibrary.Agm.Agm ← do
  if !(← Session.bundlesWanted) then return default
  match ← (HolLibrary.Agm.setupAgm deps).run with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"setupAgm failed: {e}")

-- Agm
def FORALL_2 : thm := BAgm.FORALL_2
def NUMSEG_2 : thm := BAgm.NUMSEG_2
def AGM_2 : thm := BAgm.AGM_2
def SUM_SPLIT_2 : thm := BAgm.SUM_SPLIT_2
def PRODUCT_SPLIT_2 : thm := BAgm.PRODUCT_SPLIT_2
def CAUCHY_INDUCT : thm := BAgm.CAUCHY_INDUCT
def AGM : thm := BAgm.AGM

/-- `needs "Library/agm.ml"`: already done by importing this module. -/
def ensureAgm : IO Unit := pure ()

end SessionLibrary.Agm
