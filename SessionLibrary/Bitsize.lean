/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/bitsize.ml.                                 -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Bitsize.lean

  The `unsafe` half of the bitsize.ml translation: it supplies
  HolLibrary.Bitsize's dependencies from Session, builds the bundle once,
  and exports every name under its HOL Light name.  `ensureBitsize` is
  `needs "Library/bitsize.ml"`.

  The blocks between `@@CORE` and `@@EXPORTS` markers are generated from
  HolLibrary/Bitsize.lean by tools/bitsizediff/gen_session.py and scope.py
  (bookkeeping only: field-by-field copies and accessors).
-/

import Session
import HolLibrary.Bitsize

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Bitsize

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

-- @@CORE BEGIN
/-- The core theorems bitsize.ml uses. -/
unsafe def core1 (_ : Unit) : HolLibrary.Bitsize.CoreThms1 where
  ADD_EQ_0 := Session.ADD_EQ_0
  ADD_SUB := Session.ADD_SUB
  ADD_SYM := Session.ADD_SYM
  ARITH := Session.ARITH
  ARITH_EQ := Session.ARITH_EQ
  DISJ_SYM := Session.DISJ_SYM
  EQ_IMP_LE := Session.EQ_IMP_LE
  EXP := Session.EXP
  EXP_ADD := Session.EXP_ADD
  EXP_EQ_0 := Session.EXP_EQ_0
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  LET_TRANS := Session.LET_TRANS
  LE_0 := Session.LE_0
  LE_ANTISYM := Session.LE_ANTISYM
  LE_EXP := Session.LE_EXP
  LE_MULT_LCANCEL := Session.LE_MULT_LCANCEL
  LE_RDIV_EQ := Session.LE_RDIV_EQ
  LE_REFL := Session.LE_REFL
  LE_TRANS := Session.LE_TRANS
  LT := Session.LT
  LTE_TRANS := Session.LTE_TRANS
  LT_ANTISYM := Session.LT_ANTISYM
  LT_CASES := Session.LT_CASES
  LT_EXP := Session.LT_EXP
  LT_MULT2 := Session.LT_MULT2
  LT_MULT_LCANCEL := Session.LT_MULT_LCANCEL
  LT_POW2_REFL := Session.LT_POW2_REFL
  LT_TRANS := Session.LT_TRANS
  MINIMAL_LE := Session.MINIMAL_LE
  MINIMAL_UNIQUE := Session.MINIMAL_UNIQUE
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_SYM := Session.MULT_SYM
  NOT_LE := Session.NOT_LE
  NOT_LT := Session.NOT_LT
  RDIV_LT_EQ := Session.RDIV_LT_EQ-- @@CORE END

/-- What bitsize.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.Bitsize.BitsizeDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  SIMP_TAC := Session.SIMP_TAC
  mk_small_numeral := Session.mk_small_numeral
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  core1 := core1 ()

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
  | .ok d => d | _ => panic! s!"SessionLibrary.Bitsize: {name}"

/- The bundles, in bitsize.ml order. -/

-- @@BUNDLES BEGIN
initialize theBitsize : IO.Ref (Option HolLibrary.Bitsize.Bitsize) ← IO.mkRef none
unsafe def BBitsize : HolLibrary.Bitsize.Bitsize :=
  cached theBitsize "setupBitsize" fun _ => do
    (HolLibrary.Bitsize.setupBitsize (deps ())).run

-- @@BUNDLES END

-- @@EXPORTS BEGIN
-- Bitsize
unsafe def bitsize : thm := BBitsize.bitsize
unsafe def BITSIZE_0 : thm := BBitsize.BITSIZE_0
unsafe def BITSIZE_POW2 : thm := BBitsize.BITSIZE_POW2
unsafe def BITSIZE_1 : thm := BBitsize.BITSIZE_1
unsafe def BITSIZE_2 : thm := BBitsize.BITSIZE_2
unsafe def BITSIZE_LE : thm := BBitsize.BITSIZE_LE
unsafe def BITSIZE : thm := BBitsize.BITSIZE
unsafe def BITSIZE_UNIQUE : thm := BBitsize.BITSIZE_UNIQUE
unsafe def BITSIZE_UNIQUE_ALT : thm := BBitsize.BITSIZE_UNIQUE_ALT
unsafe def BITSIZE_EQ_0 : thm := BBitsize.BITSIZE_EQ_0
unsafe def BITSIZE_MONO : thm := BBitsize.BITSIZE_MONO
unsafe def BITSIZE_MAX : thm := BBitsize.BITSIZE_MAX
unsafe def BITSIZE_MIN : thm := BBitsize.BITSIZE_MIN
unsafe def BITSIZE_MULT_LE : thm := BBitsize.BITSIZE_MULT_LE
unsafe def BITSIZE_REV_EQ : thm := BBitsize.BITSIZE_REV_EQ
unsafe def BITSIZE_REV : thm := BBitsize.BITSIZE_REV
unsafe def BITSIZE_REV_EQ_ALT : thm := BBitsize.BITSIZE_REV_EQ_ALT
unsafe def BITSIZE_REV_ALT : thm := BBitsize.BITSIZE_REV_ALT
unsafe def LE_BITSIZE : thm := BBitsize.LE_BITSIZE
unsafe def LE_BITSIZE_ALT : thm := BBitsize.LE_BITSIZE_ALT
unsafe def BITSIZE_UNIQUE_EQ : thm := BBitsize.BITSIZE_UNIQUE_EQ
unsafe def BITSIZE_MULT : thm := BBitsize.BITSIZE_MULT
unsafe def BITSIZE_MULT_ADD : thm := BBitsize.BITSIZE_MULT_ADD
unsafe def BITSIZE_DIV : thm := BBitsize.BITSIZE_DIV
unsafe def BITSIZE_CONV : term → IO (Except String thm) := fun t => (BBitsize.BITSIZE_CONV t).run


-- @@EXPORTS END

/-- `needs "Library/bitsize.ml"`: build every bundle, in file order. -/
unsafe def ensureBitsize : IO Unit := do
  -- @@ENSURE BEGIN
  let _ ← IO.mkRef BBitsize.bitsize  -- @@ENSURE END
  pure ()

end SessionLibrary.Bitsize
