/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/iter.ml.                                    -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Iter.lean

  The `unsafe` half of the iter.ml translation: it supplies
  HolLibrary.Iter's dependencies from Session, builds the bundle once, and
  exports every name under its HOL Light name.  `ensureIter` is
  `needs "Library/iter.ml"`.

  The blocks between `@@CORE` and `@@EXPORTS` markers are generated from
  HolLibrary/Iter.lean by tools/iterdiff/gen_session.py and scope.py
  (bookkeeping only: field-by-field copies and accessors).
-/

import Session
import HolLibrary.Iter

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Iter

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

-- @@CORE BEGIN
/-- The core theorems iter.ml uses. -/
unsafe def core1 (_ : Unit) : HolLibrary.Iter.CoreThms1 where
  ADD := Session.ADD
  ADD_AC := Session.ADD_AC
  ADD_SYM := Session.ADD_SYM
  CARD_IMAGE_EQ_INJ := Session.CARD_IMAGE_EQ_INJ
  CARD_NUMSEG := Session.CARD_NUMSEG
  CARD_SUBSET := Session.CARD_SUBSET
  DIVIDES_LE := Session.DIVIDES_LE
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FUN_EQ_THM := Session.FUN_EQ_THM
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  IN_NUMSEG := Session.IN_NUMSEG
  I_THM := Session.I_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_1 := Session.LE_1
  LE_REFL := Session.LE_REFL
  MONO_EXISTS := Session.MONO_EXISTS
  MULT := Session.MULT
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NOT_LT := Session.NOT_LT
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  SUB_0 := Session.SUB_0
  SUB_REFL := Session.SUB_REFL
  WLOG_LT := Session.WLOG_LT
  num_WF := Session.num_WF
  num_WOP := Session.num_WOP
  o_THM := Session.o_THM-- @@CORE END

/-- What iter.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.Iter.IterDeps where
  define s := do ExceptT.mk (Session.define (← HolLight.q s))
  num_CONV := Session.num_CONV
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  ASM_SIMP_TAC := Session.ASM_SIMP_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  NUMBER_RULE t := ExceptT.mk (Session.NUMBER_RULE t)
  SET_TAC := Session.SET_TAC
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
  | .ok d => d | _ => panic! s!"SessionLibrary.Iter: {name}"

/- The single bundle. -/

-- @@BUNDLES BEGIN
initialize theIter : IO.Ref (Option HolLibrary.Iter.Iter) ← IO.mkRef none
unsafe def BIter : HolLibrary.Iter.Iter :=
  cached theIter "setupIter" fun _ => do
    (HolLibrary.Iter.setupIter (deps ())).run

-- @@BUNDLES END

-- @@EXPORTS BEGIN
-- Iter
unsafe def ITER : thm := BIter.ITER
unsafe def ITER_POINTLESS : thm := BIter.ITER_POINTLESS
unsafe def ITER_ALT : thm := BIter.ITER_ALT
unsafe def ITER_ALT_POINTLESS : thm := BIter.ITER_ALT_POINTLESS
unsafe def ITER_1 : thm := BIter.ITER_1
unsafe def ITER_ADD : thm := BIter.ITER_ADD
unsafe def ITER_ADD_POINTLESS : thm := BIter.ITER_ADD_POINTLESS
unsafe def ITER_MUL : thm := BIter.ITER_MUL
unsafe def ITER_FIXPOINT : thm := BIter.ITER_FIXPOINT
unsafe def ORDER_EXISTENCE_GEN : thm := BIter.ORDER_EXISTENCE_GEN
unsafe def ORDER_EXISTENCE_ITER : thm := BIter.ORDER_EXISTENCE_ITER
unsafe def ORDER_EXISTENCE_CARD : thm := BIter.ORDER_EXISTENCE_CARD
unsafe def ORDER_EXISTENCE_FINITE : thm := BIter.ORDER_EXISTENCE_FINITE



-- @@EXPORTS END

/-- `needs "Library/iter.ml"`: build the bundle. -/
unsafe def ensureIter : IO Unit := do
  -- @@ENSURE BEGIN
  let _ ← IO.mkRef BIter.ITER  -- @@ENSURE END
  pure ()

end SessionLibrary.Iter
