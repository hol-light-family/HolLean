/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/agm.ml.                                     -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Agm.lean

  The `unsafe` half of the agm.ml translation: it supplies HolLibrary.Agm's
  dependencies from Session and SessionLibrary.Products, builds the bundle
  once, and exports every name under its HOL Light name.  `ensureAgm` is
  `needs "Library/agm.ml"` (which first does `needs "Library/products.ml"`).

  The blocks between `@@CORE` and `@@EXPORTS` markers are generated from
  HolLibrary/Agm.lean by tools/agmdiff/gen_session.py and scope.py
  (bookkeeping only: field-by-field copies and accessors).  The products.ml
  theorems agm.ml uses are filled from SessionLibrary.Products.
-/

import Session
import HolLibrary.Agm
import SessionLibrary.Products

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Agm

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

-- @@CORE BEGIN
/-- The core theorems agm.ml uses. -/
unsafe def core1 (_ : Unit) : HolLibrary.Agm.CoreThms1 where
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
  real_pow := Session.real_pow-- @@CORE END

/-- What agm.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.Agm.AgmDeps where
  prioritize_real := Session.prioritize_real
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  MESON_TAC := Session.MESON_TAC
  REAL_ARITH t := ExceptT.mk (Session.REAL_ARITH3 t)
  REAL_FIELD t := ExceptT.mk (Session.REAL_FIELD t)
  core1 := core1 ()

/-- Build a bundle once.  `setup` is a thunk, so that `deps` is not built
    before the bundle is needed.  The whole core library is built first
    (`Session.ensureDefine`, and MATCH_CONV's basic conversions, which HOL
    Light adds loading ind_types.ml), then products.ml, which agm.ml
    needs. -/
private unsafe def cached {α : Type} [Inhabited α] (r : IO.Ref (Option α)) (name : String)
    (setup : Unit → IO (Except String α)) : α :=
  match unsafeIO (do
    match ← r.get with
    | some d => pure d
    | none => do
      Session.ensureDefine
      let _ ← Session.MATCH_CONV (HolCore.Kernel.mk_var "p" HolCore.Kernel.bool_ty)
      SessionLibrary.Products.ensureProducts
      match ← setup () with
      | .ok d => do r.set (some d); pure d
      | .error e => panic! s!"{name} failed: {e}") with
  | .ok d => d | _ => panic! s!"SessionLibrary.Agm: {name}"

/- The single bundle. -/

-- @@BUNDLES BEGIN
initialize theAgm : IO.Ref (Option HolLibrary.Agm.Agm) ← IO.mkRef none
unsafe def BAgm : HolLibrary.Agm.Agm :=
  cached theAgm "setupAgm" fun _ => do
    (HolLibrary.Agm.setupAgm (deps ())).run

-- @@BUNDLES END

-- @@EXPORTS BEGIN
-- Agm
unsafe def FORALL_2 : thm := BAgm.FORALL_2
unsafe def NUMSEG_2 : thm := BAgm.NUMSEG_2
unsafe def AGM_2 : thm := BAgm.AGM_2
unsafe def SUM_SPLIT_2 : thm := BAgm.SUM_SPLIT_2
unsafe def PRODUCT_SPLIT_2 : thm := BAgm.PRODUCT_SPLIT_2
unsafe def CAUCHY_INDUCT : thm := BAgm.CAUCHY_INDUCT
unsafe def AGM : thm := BAgm.AGM



-- @@EXPORTS END

/-- `needs "Library/agm.ml"`: build the bundle. -/
unsafe def ensureAgm : IO Unit := do
  -- @@ENSURE BEGIN
  let _ ← IO.mkRef BAgm.FORALL_2  -- @@ENSURE END
  pure ()

end SessionLibrary.Agm
