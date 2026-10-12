/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/frag.ml.                                    -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Frag.lean

  The `unsafe` half of the frag.ml translation: it supplies
  HolLibrary.Frag's dependencies from Session, builds the bundle once, and
  exports every name under its HOL Light name.  `ensureFrag` is
  `needs "Library/frag.ml"`.

  The blocks between `@@CORE` and `@@EXPORTS` markers are generated from
  HolLibrary/Frag.lean by tools/fragdiff/gen_session.py and scope.py
  (bookkeeping only: field-by-field copies and accessors).
-/

import Session
import HolLibrary.Frag

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Frag

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

-- @@CORE BEGIN
/-- The core theorems frag.ml uses. -/
unsafe def core1 (_ : Unit) : HolLibrary.Frag.CoreThms1 where
  AND_FORALL_THM := Session.AND_FORALL_THM
  BETA_THM := Session.BETA_THM
  COND_RAND := Session.COND_RAND
  COND_RATOR := Session.COND_RATOR
  CONJ_ASSOC := Session.CONJ_ASSOC
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  EMPTY_GSPEC := Session.EMPTY_GSPEC
  EMPTY_SUBSET := Session.EMPTY_SUBSET
  ETA_AX := Session.ETA_AX
  EXTENSION := Session.EXTENSION
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_SING := Session.FINITE_SING
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_UNION := Session.FINITE_UNION
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FUN_EQ_THM := Session.FUN_EQ_THM
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  IMAGE_SUBSET := Session.IMAGE_SUBSET
  IMP_CONJ := Session.IMP_CONJ
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  INSERT_SUBSET := Session.INSERT_SUBSET
  INT_ADD_LID := Session.INT_ADD_LID
  INT_ENTIRE := Session.INT_ENTIRE
  INT_FORALL_POS := Session.INT_FORALL_POS
  INT_MUL_LZERO := Session.INT_MUL_LZERO
  INT_MUL_RZERO := Session.INT_MUL_RZERO
  INT_NEG_EQ_0 := Session.INT_NEG_EQ_0
  INT_OF_NUM_SUC := Session.INT_OF_NUM_SUC
  INT_SUB_RZERO := Session.INT_SUB_RZERO
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_INSERT := Session.IN_INSERT
  IN_UNION := Session.IN_UNION
  IN_UNIV := Session.IN_UNIV
/-- The core theorems frag.ml uses. -/
unsafe def core2 (_ : Unit) : HolLibrary.Frag.CoreThms2 where
  ITERATE_CLAUSES := Session.ITERATE_CLAUSES
  ITERATE_EQ := Session.ITERATE_EQ
  ITERATE_EQ_NEUTRAL := Session.ITERATE_EQ_NEUTRAL
  ITERATE_EXPAND_CASES := Session.ITERATE_EXPAND_CASES
  ITERATE_OP_GEN := Session.ITERATE_OP_GEN
  ITERATE_UNIV := Session.ITERATE_UNIV
  I_THM := Session.I_THM
  LEFT_OR_FORALL_THM := Session.LEFT_OR_FORALL_THM
  MONO_FORALL := Session.MONO_FORALL
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RIGHT_OR_FORALL_THM := Session.RIGHT_OR_FORALL_THM
  SIMPLE_IMAGE := Session.SIMPLE_IMAGE
  SING_GSPEC := Session.SING_GSPEC
  SUBSET := Session.SUBSET
  SUBSET_TRANS := Session.SUBSET_TRANS
  SUBSET_UNIONS := Session.SUBSET_UNIONS
  SUBSET_UNIV := Session.SUBSET_UNIV
  SUPPORT_SUBSET := Session.SUPPORT_SUBSET
  SWAP_FORALL_THM := Session.SWAP_FORALL_THM
  UNIONS_MONO_IMAGE := Session.UNIONS_MONO_IMAGE
  UNIONS_SUBSET := Session.UNIONS_SUBSET
  monoidal := Session.monoidal
  neutral := Session.neutral
  o_THM := Session.o_THM
  support := Session.support-- @@CORE END

/-- What frag.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.Frag.FragDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  new_type_definition ty names th :=
    ExceptT.mk (Session.new_type_definition ty names.1 names.2 th)
  INT_ARITH t := ExceptT.mk (Session.INT_ARITH t)
  INT_ARITH_TAC := Session.INT_ARITH_TAC
  INT_RING t := ExceptT.mk (Session.INT_RING t)
  INT_REDUCE_CONV := Session.INT_REDUCE_CONV
  INDUCT_TAC := Session.INDUCT_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  core1 := core1 ()
  core2 := core2 ()

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
  | .ok d => d | _ => panic! s!"SessionLibrary.Frag: {name}"

/- The bundle, in frag.ml order. -/

-- @@BUNDLES BEGIN
initialize theFrag : IO.Ref (Option HolLibrary.Frag.Frag) ← IO.mkRef none
unsafe def BFrag : HolLibrary.Frag.Frag :=
  cached theFrag "setupFrag" fun _ => do
    (HolLibrary.Frag.setupFrag (deps ())).run

-- @@BUNDLES END

-- @@EXPORTS BEGIN
-- Frag
unsafe def frag_tybij : thm := BFrag.frag_tybij
unsafe def frag_support : thm := BFrag.frag_support
unsafe def frag_0 : thm := BFrag.frag_0
unsafe def frag_of : thm := BFrag.frag_of
unsafe def frag_neg : thm := BFrag.frag_neg
unsafe def frag_cmul : thm := BFrag.frag_cmul
unsafe def frag_add : thm := BFrag.frag_add
unsafe def frag_sub : thm := BFrag.frag_sub
unsafe def FRAG_EQ : thm := BFrag.FRAG_EQ
unsafe def DEST_FRAG_0 : thm := BFrag.DEST_FRAG_0
unsafe def DEST_FRAG_OF : thm := BFrag.DEST_FRAG_OF
unsafe def DEST_FRAG_NEG : thm := BFrag.DEST_FRAG_NEG
unsafe def DEST_FRAG_CMUL : thm := BFrag.DEST_FRAG_CMUL
unsafe def DEST_FRAG_ADD : thm := BFrag.DEST_FRAG_ADD
unsafe def DEST_FRAG_SUB : thm := BFrag.DEST_FRAG_SUB
unsafe def FRAG_OF_NONZERO : thm := BFrag.FRAG_OF_NONZERO
unsafe def FRAG_MODULE : term → IO (Except String thm) := fun t => (BFrag.FRAG_MODULE t).run
unsafe def FINITE_FRAG_SUPPORT : thm := BFrag.FINITE_FRAG_SUPPORT
unsafe def FRAG_SUPPORT_0 : thm := BFrag.FRAG_SUPPORT_0
unsafe def FRAG_SUPPORT_OF : thm := BFrag.FRAG_SUPPORT_OF
unsafe def FRAG_SUPPORT_NEG : thm := BFrag.FRAG_SUPPORT_NEG
unsafe def FRAG_SUPPORT_CMUL : thm := BFrag.FRAG_SUPPORT_CMUL
unsafe def FRAG_SUPPORT_ADD : thm := BFrag.FRAG_SUPPORT_ADD
unsafe def FRAG_SUPPORT_SUB : thm := BFrag.FRAG_SUPPORT_SUB
unsafe def FRAG_SUPPORT_EQ_EMPTY : thm := BFrag.FRAG_SUPPORT_EQ_EMPTY
unsafe def FRAG_OF_EQ : thm := BFrag.FRAG_OF_EQ
unsafe def FRAG_ADD_EQ_0 : thm := BFrag.FRAG_ADD_EQ_0
unsafe def NEUTRAL_FRAG_ADD : thm := BFrag.NEUTRAL_FRAG_ADD
unsafe def MONOIDAL_FRAG_ADD : thm := BFrag.MONOIDAL_FRAG_ADD
unsafe def FRAG_CMUL_SUM : thm := BFrag.FRAG_CMUL_SUM
unsafe def FRAG_SUPPORT_SUM : thm := BFrag.FRAG_SUPPORT_SUM
unsafe def frag_extend : thm := BFrag.frag_extend
unsafe def FRAG_EXTEND : thm := BFrag.FRAG_EXTEND
unsafe def FRAG_EXTEND_0 : thm := BFrag.FRAG_EXTEND_0
unsafe def FRAG_EXTEND_OF : thm := BFrag.FRAG_EXTEND_OF
unsafe def FRAG_EXTEND_CMUL : thm := BFrag.FRAG_EXTEND_CMUL
unsafe def FRAG_EXTEND_NEG : thm := BFrag.FRAG_EXTEND_NEG
unsafe def FRAG_EXTEND_ADD : thm := BFrag.FRAG_EXTEND_ADD
unsafe def FRAG_EXTEND_SUB : thm := BFrag.FRAG_EXTEND_SUB
unsafe def FRAG_EXTEND_SUM : thm := BFrag.FRAG_EXTEND_SUM
unsafe def FRAG_EXTEND_EQ : thm := BFrag.FRAG_EXTEND_EQ
unsafe def FRAG_EXTEND_EQ_0 : thm := BFrag.FRAG_EXTEND_EQ_0
unsafe def FRAG_SUPPORT_FRAG_EXTEND : thm := BFrag.FRAG_SUPPORT_FRAG_EXTEND
unsafe def FRAG_EXPANSION : thm := BFrag.FRAG_EXPANSION
unsafe def FRAG_CLOSURE_SUB_CMUL : thm := BFrag.FRAG_CLOSURE_SUB_CMUL
unsafe def FRAG_INDUCTION : thm := BFrag.FRAG_INDUCTION
unsafe def FRAG_EXTEND_COMPOSE : thm := BFrag.FRAG_EXTEND_COMPOSE
unsafe def FRAG_SPLIT : thm := BFrag.FRAG_SPLIT





-- @@EXPORTS END

/-- `needs "Library/frag.ml"`: build every bundle, in file order. -/
unsafe def ensureFrag : IO Unit := do
  -- @@ENSURE BEGIN
  let _ ← IO.mkRef BFrag.frag_tybij  -- @@ENSURE END
  pure ()

end SessionLibrary.Frag
